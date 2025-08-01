open Unix
open Filename
open Compile
open Printf
open OUnit2
open ExtLib
open Lexing
open Exprs
open Pretty
open Phases
open Errors

let result_printer (e : (string, string) result) : string =
  match e with
  | Error v -> sprintf "Error: %s\n" v
  | Ok v -> v
;;

let parse (name : string) lexbuf : sourcespan program =
  try
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname= name};
    Parser.program Lexer.token lexbuf
  with
  | Failure msg as exn ->
      if msg = "lexing: empty token" then
        raise (ParseError (sprintf "Lexical error at %s" (string_of_position lexbuf.lex_curr_p)))
      else
        let bt = Printexc.get_raw_backtrace () in
        Printexc.raise_with_backtrace exn bt (* make sure we throw with the same stack trace *)
  | Parsing.Parse_error ->
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let tok = Lexing.lexeme lexbuf in
      raise (ParseError (sprintf "Parse error at line %d, col %d: token `%s`" line cnum tok))
;;

(* Read a file into a string *)
let string_of_file (file_name : string) : string =
  let inchan = open_in file_name in
  let ans = really_input_string inchan (in_channel_length inchan) in
  close_in inchan; ans
;;

let parse_string (name : string) (s : string) : sourcespan program =
  let lexbuf = Lexing.from_string s in
  parse name lexbuf
;;

let parse_file (name : string) input_file : sourcespan program =
  let lexbuf = Lexing.from_channel input_file in
  parse name lexbuf
;;

let compile_string_to_string
    ?(no_builtins = false)
    ?(no_typechecking = false)
    (alloc_strat : alloc_strategy)
    (name : string)
    (input : string) : string pipeline =
  Ok (input, [])
  |> add_phase source (fun x -> x)
  |> add_err_phase parsed (fun input -> try Ok (parse_string name input) with err -> Error [err])
  |> compile_to_string ~no_builtins ~no_typechecking alloc_strat
;;

let compile_file_to_string
    ?(no_builtins = false)
    ?(no_typechecking = false)
    (alloc_strat : alloc_strategy)
    (name : string)
    (input_file : string) : string pipeline =
  compile_string_to_string ~no_builtins ~no_typechecking alloc_strat name (string_of_file input_file)
;;


let make_tmpfiles (name : string) (std_input : string) =
  let stdin_read, stdin_write = pipe () in
  let stdout_name = temp_file ("stdout_" ^ name) ".out" in
  let stderr_name = temp_file ("stderr_" ^ name) ".err" in
  ignore (Unix.write_substring stdin_write std_input 0 (String.length std_input));
  Unix.close stdin_write;
  ( openfile stdout_name [O_RDWR] 0o600,
    stdout_name,
    openfile stderr_name [O_RDWR] 0o600,
    stderr_name,
    stdin_read )
;;

let run_no_vg (program_name : string) args std_input : (string, string) result =
  let rstdout, rstdout_name, rstderr, rstderr_name, rstdin = make_tmpfiles "run" std_input in
  let ran_pid =
    Unix.create_process (program_name ^ ".run")
      (Array.of_list ([program_name ^ ".run"] @ args))
      rstdin rstdout rstderr
  in
  let _, status = waitpid [] ran_pid in
  let result =
    match status with
    | WEXITED 0 -> Ok (string_of_file rstdout_name)
    | WEXITED n -> Error (sprintf "Error %d: %s" n (string_of_file rstderr_name))
    | WSIGNALED n -> Error (sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n -> Error (sprintf "Stopped with signal %d while running %s." n program_name)
  in
  List.iter close [rstdout; rstderr; rstdin];
  List.iter unlink [rstdout_name; rstderr_name];
  result
;;

let run_vg (program_name : string) args std_input : (string, string) result =
  let rstdout, rstdout_name, rstderr, rstderr_name, rstdin = make_tmpfiles "run" std_input in
  let ran_pid =
    Unix.create_process "valgrind"
      (Array.of_list (["valgrind"; program_name ^ ".run"] @ args))
      rstdin rstdout rstderr
  in
  let _, status = waitpid [] ran_pid in
  let vg_str = string_of_file rstderr_name in
  let vg_ok = String.exists vg_str ~sub:"0 errors from 0 contexts" in
  let result =
    match (status, vg_ok) with
    | WEXITED 0, true -> Ok (string_of_file rstdout_name)
    | WEXITED 0, false ->
        Error ("Stdout: " ^ string_of_file rstdout_name ^ "\n" ^ "Valgrind: \n" ^ vg_str)
    | WEXITED n, _ -> Error (sprintf "Error %d: %s" n vg_str)
    | WSIGNALED n, _ -> Error (sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n, _ -> Error (sprintf "Stopped with signal %d while running %s." n program_name)
  in
  List.iter close [rstdout; rstderr; rstdin];
  List.iter unlink [rstdout_name; rstderr_name];
  result
;;

let run_asm
    (asm_string : string)
    (out : string)
    (runner : string -> string list -> string -> (string, string) result)
    args
    (std_input : string) =
  let outfile = open_out (out ^ ".s") in
  fprintf outfile "%s" asm_string;
  close_out outfile;
  let bstdout, bstdout_name, bstderr, bstderr_name, bstdin = make_tmpfiles "build" "" in
  let built_pid =
    Unix.create_process "make" (Array.of_list ["make"; out ^ ".run"]) bstdin bstdout bstderr
  in
  let _, status = waitpid [] built_pid in
  let try_running =
    match status with
    | WEXITED 0 -> Ok (string_of_file bstdout_name)
    | WEXITED _ ->
        Error
          (sprintf "Finished with error while building %s:\nStderr:\n%s\nStdout:\n%s" out
             (string_of_file bstderr_name) (string_of_file bstdout_name) )
    | WSIGNALED n -> Error (sprintf "Signalled with %d while building %s." n out)
    | WSTOPPED n -> Error (sprintf "Stopped with signal %d while building %s." n out)
  in
  let result =
    match try_running with
    | Error _ -> try_running
    | Ok _ -> runner out args std_input
  in
  List.iter close [bstdout; bstderr; bstdin];
  List.iter unlink [bstdout_name; bstderr_name];
  result
;;

let run p out runner no_builtins no_typechecking args std_input alloc_strat =
  let maybe_asm_string = compile_to_string ~no_builtins ~no_typechecking alloc_strat (Ok (p, [])) in
  match maybe_asm_string with
  | Error (errs, _) -> Error (ExtString.String.join "\n" (print_errors errs))
  | Ok (asm_string, _) -> run_asm asm_string out runner args std_input
;;

let run_anf p out runner args std_input =
  let maybe_asm_string =
    try Ok (compile_prog p) with
    | Failure s -> Error [Failure ("Compile error: " ^ s)]
    | err -> Error [Failure ("Unexpected compile error: " ^ Printexc.to_string err)]
  in
  match maybe_asm_string with
  | Error errs -> Error (ExtString.String.join "\n" (print_errors errs))
  | Ok asm_string -> run_asm asm_string out runner args std_input
;;

type compile_opts =
  { valgrind: bool;
    no_builtins: bool;
    heap_size: int option;
    alloc_strat: alloc_strategy;
    no_typechecking: bool;
    }

let starts_with target src =
  String.length src >= String.length target && String.sub src 0 (String.length target) = target
;;

let chomp str =
  if str = "" then
    str
  else if str.[String.length str - 1] = '\n' then
    String.sub str 0 (String.length str - 1)
  else
    str
;;

let read_options filename : compile_opts =
  let opts =
    if Sys.file_exists filename then
      String.split_on_char '\n' (string_of_file filename)
    else
      []
  in
  let heap_size =
    match List.find_opt (starts_with "heap ") opts with
    | None -> None
    | Some str -> Some (Scanf.sscanf str "heap %d" (fun h -> h))
  in
  let alloc_strat =
    match List.find_opt (starts_with "alloc ") opts with
    | None -> Naive
    | Some "alloc naive" -> Naive
    | Some "alloc register" -> Register
    | Some s ->
        raise
          (InternalCompilerError
             (sprintf "'%s' is not a valid allocation strategy, use naive or register" s) )
  in
  { valgrind= List.mem "valgrind" opts;
    no_builtins= List.mem "no_builtins" opts;
    no_typechecking = List.mem "no_typechecking" opts;
    heap_size;
    alloc_strat }
;;

let parse_args (argsfile : string) (opts : compile_opts) : string list =
  if Sys.file_exists argsfile then
    String.split_on_char '\n' (chomp (string_of_file argsfile))
  else
    match opts.heap_size with
    | Some size -> [string_of_int size]
    | None -> []
;;

let test_run
    ?(no_builtins = false)
    ?(no_typechecking = false)
    ?(args = [])
    ?(std_input = "")
    alloc_strat
    program_str
    outfile
    expected
    ?(cmp = ( = ))
    _ =
  let full_outfile = "output/" ^ outfile in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile run_no_vg no_builtins no_typechecking args std_input alloc_strat
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Ok (expected ^ "\n")) result ~cmp ~printer:result_printer
;;

let test_run_anf ?(args = []) ?(std_input = "") program_anf outfile expected ?(cmp = ( = )) _ =
  let full_outfile = "output/" ^ outfile in
  let result = run_anf program_anf full_outfile run_no_vg args std_input in
  assert_equal (Ok (expected ^ "\n")) result ~cmp ~printer:result_printer
;;

let test_run_valgrind
    ?(no_builtins = false)
    ?(no_typechecking = false)
    ?(args = [])
    ?(std_input = "")
    alloc_strat
    program_str
    outfile
    expected
    ?(cmp = ( = ))
    _ =
  let full_outfile = "output/" ^ outfile in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile run_vg no_builtins no_typechecking args std_input alloc_strat
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Ok (expected ^ "\n")) result ~cmp ~printer:result_printer
;;

let test_err
    ?(no_builtins = false)
    ?(no_typechecking = false)
    ?(args = [])
    ?(std_input = "")
    alloc_strat
    program_str
    outfile
    errmsg
    ?(vg = false)
    _ =
  let full_outfile = "output/" ^ outfile in
  let runner =
    if vg then
      run_vg
    else
      run_no_vg
  in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile runner no_builtins no_typechecking args std_input alloc_strat
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Error errmsg) result ~printer:result_printer ~cmp:(fun check result ->
      match (check, result) with
      | Error expect_msg, Error actual_message -> String.exists actual_message ~sub:expect_msg
      | _ -> false )
;;

let test_run_input filename ?(args = []) ?(std_input = "") alloc_strat expected test_ctxt =
  test_run ~args ~std_input alloc_strat
    (string_of_file ("input/" ^ filename))
    filename expected test_ctxt
;;

let test_err_input filename ?(args = []) alloc_strat expected test_ctxt =
  test_err ~args ~std_input:"" alloc_strat
    (string_of_file ("input/" ^ filename))
    filename expected test_ctxt
;;

let chomp str =
  if str = "" then
    str
  else if str.[String.length str - 1] = '\n' then
    String.sub str 0 (String.length str - 1)
  else
    str
;;

let test_does_run filename test_ctxt =
  let filename = Filename.remove_extension filename in
  let progfile = sprintf "input/do_pass/%s.racer" filename in
  let argsfile = sprintf "input/do_pass/%s.args" filename in
  let outfile = sprintf "input/do_pass/%s.out" filename in
  let infile = sprintf "input/do_pass/%s.in" filename in
  let opts = read_options (sprintf "input/do_pass/%s.options" filename) in
  let prog = string_of_file progfile in
  let args = parse_args argsfile opts in
  let output =
    if Sys.file_exists outfile then
      chomp (string_of_file outfile)
    else
      ""
  in
  let input =
    if Sys.file_exists infile then
      string_of_file infile
    else
      ""
  in
  let runner =
    if opts.valgrind then
      test_run_valgrind
    else
      test_run
  in
  let alloc_strat = opts.alloc_strat in
  runner ~no_builtins:opts.no_builtins ~no_typechecking:opts.no_typechecking ~args ~std_input:input alloc_strat prog
    ("do_pass/" ^ filename) output test_ctxt ~cmp:(fun check result ->
      match (check, result) with
      | Ok expect_msg, Ok actual_message -> String.exists actual_message ~sub:expect_msg
      | _ -> false )
;;

let test_does_err filename test_ctxt =
  let filename = Filename.remove_extension filename in
  let progfile = sprintf "input/do_err/%s.racer" filename in
  let argsfile = sprintf "input/do_err/%s.args" filename in
  let errfile = sprintf "input/do_err/%s.err" filename in
  let infile = sprintf "input/do_err/%s.in" filename in
  let opts = read_options (sprintf "input/do_err/%s.options" filename) in
  let prog = string_of_file progfile in
  let args = parse_args argsfile opts in
  let err =
    if Sys.file_exists errfile then
      chomp (string_of_file errfile)
    else
      ""
  in
  let input =
    if Sys.file_exists infile then
      string_of_file infile
    else
      ""
  in
  let alloc_strat = opts.alloc_strat in
  test_err ~no_builtins:opts.no_builtins ~args ~std_input:input alloc_strat prog
    ("do_err/" ^ filename) err ~vg:opts.valgrind test_ctxt
;;

let test_doesnt_run filename _ =
  let filename = Filename.remove_extension filename in
  let progfile = sprintf "input/dont_pass/%s.racer" filename in
  let argsfile = sprintf "input/dont_pass/%s.args" filename in
  let infile = sprintf "input/dont_pass/%s.in" filename in
  let opts = read_options (sprintf "input/dont_pass/%s.options" filename) in
  let prog = string_of_file progfile in
  let args = parse_args argsfile opts in
  let input =
    if Sys.file_exists infile then
      string_of_file infile
    else
      ""
  in
  let runner =
    if opts.valgrind then
      run_vg
    else
      run_no_vg
  in
  let alloc_strat = opts.alloc_strat in
  let full_outfile = "output/dont_pass" ^ filename in
  let result =
    try
      let program = parse_string filename prog in
      run program full_outfile runner opts.no_builtins opts.no_typechecking args input alloc_strat
    with err -> Error (Printexc.to_string err)
  in
  match result with
  | Ok unexpected ->
      assert_failure (sprintf "Expected program to fail, but it didn't:\nReceived: %s" unexpected)
  | Error _ ->
      assert_bool (sprintf "Program %s currently fails (as expected for now)" filename) true
;;

let test_doesnt_err filename _ =
  let filename = Filename.remove_extension filename in
  let progfile = sprintf "input/dont_err/%s.racer" filename in
  let argsfile = sprintf "input/dont_err/%s.args" filename in
  let infile = sprintf "input/dont_err/%s.in" filename in
  let opts = read_options (sprintf "input/dont_err/%s.options" filename) in
  let prog = string_of_file progfile in
  let args = parse_args argsfile opts in
  let input =
    if Sys.file_exists infile then
      string_of_file infile
    else
      ""
  in
  let runner =
    if opts.valgrind then
      run_vg
    else
      run_no_vg
  in
  let alloc_strat = opts.alloc_strat in
  let full_outfile = "output/dont_err" ^ filename in
  let result =
    try
      let program = parse_string filename prog in
      run program full_outfile runner opts.no_builtins opts.no_typechecking args input alloc_strat
    with err -> Error (Printexc.to_string err)
  in
  match result with
  | Ok _ -> assert_bool (sprintf "Program %s currently runs (as expected for now)" filename) true
  | Error errmsg ->
      assert_failure (sprintf "Expected program to succeed, but it didn't:\nReceived: %s" errmsg)
;;

let input_file_test_suite () =
  let safe_readdir dir ext =
    try List.filter (fun f -> Filename.check_suffix f ext) (Array.to_list (Sys.readdir dir))
    with _ -> []
  in
  "input-file-suite"
  >::: [ "do_pass"
         >::: List.map (fun f -> f >:: test_does_run f) (safe_readdir "input/do_pass" ".racer");
         "do_err"
         >::: List.map (fun f -> f >:: test_does_err f) (safe_readdir "input/do_err" ".racer");
         "dont_pass"
         >::: List.map (fun f -> f >:: test_doesnt_run f) (safe_readdir "input/dont_pass" ".racer");
         "dont_err"
         >::: List.map (fun f -> f >:: test_doesnt_err f) (safe_readdir "input/dont_err" ".racer")
       ]
;;