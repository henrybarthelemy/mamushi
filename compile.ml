open Printf
open Exprs
open Pretty
open Errors
open Phases
open Assembly
open Wellformed
open Typecheck
open Utils
open Desugar
open Rename
open Anf
open Allocation
open Addnative
open Graph

(* Since we merged in our changes out comments here got Got *)
(* Truely a tragedy *)
(* Anyways welcome to this gay compiler *)
(* It's not like the water had anything to do with that *)
(* It's perfectly normal water and totally safe to drink *)

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _, _) as d) :: ds_rest ->
      if name = fname then
        Some d
      else
        find_decl ds_rest name
;;

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] | [_] -> None
  | x :: xs ->
      if find_one xs x then
        Some x
      else
        find_dup xs
;;

(* Produces a uniquely mapped type environment *)
let build_type_env (type_decls: 'a type_decl list) : (int64 * int64) envt =
  let rec t_env_for_typ tp typ_tag  = 
        match tp with
          | TAlgebric(var_l, _) ->
              (List.mapi (fun (var_tag: tag) ((name, _): string * _) ->
                (name, (Int64.of_int (2 * var_tag), Int64.of_int (2 * typ_tag)))
              ) var_l)
          | _ -> [] in
  List.flatten (List.mapi (fun typ_tag td ->
    match td with
      | DType(_, tp, _) -> t_env_for_typ tp typ_tag
  ) type_decls)
;;

(* Builds essentially the same type map as above, just with a different key to make .data gen easier *)
let build_rotated_type_env (type_decls: 'a type_decl list) : (int64 * (int64 * string) list) list =
  let rec t_env_for_typ tp  = 
        match tp with
          | TAlgebric(var_l, _) ->
              (List.mapi (fun (var_tag: tag) ((name, _): string * _) ->
                (Int64.of_int (2 * var_tag), name)
              ) var_l)
          | _ -> [] in
  List.mapi (fun typ_tag td ->
    match td with
      | DType(_, tp, _) -> (Int64.of_int (2 * typ_tag), t_env_for_typ tp)
  ) type_decls
;;

(* Un-aligns the stack, if it's aligned! *)
let unalign_stack_before_call (tag: int): instruction list =
  let label = sprintf "align_done$%d" tag in [
    IInstrComment(ITest(Reg RSP, Const 0xFL), "Checks if stack is aligned");
    IInstrComment(IJnz(Label(label)), "Jumps to end if stack is not aligned");
    IInstrComment(IMov(Reg scratch_reg, Const 0xB0BABABEL), "Bounce 0xB0BABABE into scratch reg");
    IInstrComment(IPush(Sized(QWORD_PTR, Reg scratch_reg)), "Pushed dummy val onto the stack to align");
    IInstrComment(ILabel(label), "Stack is now unaligned (for a function call most likely)");
  ]
;;

(* Returns a list of placement args, and cleanup args *)
let place_args_where_they_go (args: arg list): (instruction list * instruction list) = 
  let (placement, cleanup, _) = 
    (List.fold_left (fun (placement, cleanup, regs) arg -> (
      match regs with
        | [] -> ([
          IInstrComment(IPush(arg), "Pushed external arg onto the stack");
        ] @ placement, cleanup @ [
          IInstrComment(IPop(arg), "Pops external arg off the stack");
        ], [])
        | first::rest -> ([
          IInstrComment(IMov(Reg first, arg), "Puts external arg into register");
        ] @ placement, cleanup, rest)
    )) ([], [], first_six_args_registers) args) 
  in (placement, cleanup)
;;

(* Function call abstraction *)
let rec extern_function_call (name: string) (tag: int) (args: arg list) =
  (* (native_call (Label name) args) *) (* here if we want to use the starter code implementation *)
  let (placement, cleanup) = (place_args_where_they_go args) in
  placement
  @ [ ILineComment((sprintf "Unaligning before calling %s" name))]
  @ (unalign_stack_before_call tag)
  (* @ placement *)
  @ [ IInstrComment(ICall(Label(name)), "calls external function"); ]  
  @ cleanup
and args_help args regs =
  match (args, regs) with
  | arg :: args, reg :: regs -> IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = num_stack_args mod 2 <> 0 in
  let setup =
    ( if padding_needed then
        [IInstrComment (IPush (Sized (QWORD_PTR, Const 0L)), "Padding to 16-byte alignment")]
      else
        [] )
    @ args_help args first_six_args_registers
  in
  let teardown =
    ( if num_stack_args = 0 then
        []
      else
        [ IInstrComment
            ( IAdd (Reg RSP, Const (Int64.of_int (word_size * num_stack_args))),
              sprintf "Popping %d arguments" num_stack_args ) ] )
    @
    if padding_needed then
      [IInstrComment (IAdd (Reg RSP, Const (Int64.of_int word_size)), "Unpadding one word")]
    else
      []
  in
  setup @ [ICall label] @ teardown

(* replicates the value x i number of times *)
let rec replicate x (i: int) =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
;;



(* Arg must be an immediate *)
(* Leaves value in RAX *)
(* Checks the tuple using the mask and tag of some value *)
let check_type (value: arg) (mask: int64) (tag: int64) (err_name: string): instruction list =
  [
    ILineComment((sprintf "Checking for error: %s" err_name));
    IInstrComment(IMov(Reg RAX, value), "Puts value to type check in reg");
    IInstrComment(IAnd(Reg RAX, Const mask), "Ands with the type mask - this means that all remaining in RAX is the tag");
    IInstrComment(IMov (Reg scratch_reg, Const tag), "Puts the correct tag in a reg");
    IInstrComment(IXor (Reg RAX, Reg scratch_reg), "XORs the correct and given tag - if 0 then they match");
    IInstrComment(ICmp (Reg RAX, Const 0L), "Compares result of previous with 0");
    (* This MOV makes it so the error handler can return the SV *)
    IInstrComment(IMov(Reg RAX, value), "Puts value back in RAX so we can return it, or it is passed to the type error");
    IInstrComment(IJnz(Label(err_name)), "Jumps to type error if the check fails");
    ]
;;

(* Checking an overflow is abstracted so we can change this if we ever want to *)
let check_overflow = [
  IInstrComment(IJo(Label("overflow")), "If the previous instr overflowed, jump to error");
  ]
;;

(* 
  -> RAX has the working value in it
  -> R11 has the does_match value in it
  -> Cond is either some other register, or some address on the stack (Some SV)
 *)
(* Evaluates a pattern against some immediate, puts the bool_sv result in RAX *)
(* Also binds any names in the pattern *)
let evaluate_pattern cond p type_env env bailout: instruction list = 
  let val_reg = R11 in
  let result_reg = RAX in
  let tmp_reg = RDX in
  let helpPI cond p : instruction list =
    let comp_p = match p with
      | IPBlank _ -> [ IAnd(Reg result_reg, const_true); ] 
      | IPId (name, _) -> 
        let bind_loc = match find_opt env name with
          | None -> raise (InternalCompilerError "Alloc failed")
          | Some(loc) -> loc in
        [ 
          IInstrComment(IMov(bind_loc, Reg val_reg), "Moves var pattern into bind loc");
        ]
      | IPLBool(true, (t, _, _)) -> 
          let pbool_label_end = sprintf "pattern_bool_true$%d" t in
          [ 
            ILineComment("Check bool true pattern");
            IMov(Reg tmp_reg, const_true);
            ICmp(Reg val_reg, Reg tmp_reg);
            IJe(Label pbool_label_end); 
            IMov(Reg tmp_reg, const_false);
            IAnd(Reg result_reg, Reg tmp_reg); 
            ILabel(pbool_label_end);
          ]
      | IPLBool(false, (t, _, _)) ->
          let pbool_label_end = sprintf "pattern_bool_false$%d" t in
          [ 
            ILineComment("Check bool false pattern");
            IMov(Reg tmp_reg, const_false);
            ICmp(Reg val_reg, Reg tmp_reg);
            IJe(Label pbool_label_end); 
            IAnd(Reg result_reg, Reg tmp_reg); 
            ILabel(pbool_label_end);
          ]
      | IPLInt(i, (t, _, _)) ->
          let pint_label_end = sprintf "pattern_int_%d$%d" (Int64.to_int i) t in
          [ 
            ILineComment(sprintf "Checking int %d pattern" (Int64.to_int i));
            ICmp(Reg val_reg, Const (Int64.mul i 2L));
            IJe(Label pint_label_end); 
            IMov(Reg tmp_reg, const_false);
            IAnd(Reg result_reg, Reg tmp_reg); 
            ILabel(pint_label_end);
          ]
    in [IInstrComment(IMov(Reg val_reg, cond), "Puts expr to check immpattern of in reg")] @ comp_p
  in
  let helpPC cond p =
    let comp_p = match p with
      | CPTup(pl, _) -> 
          List.flatten (List.mapi (fun i x -> 
            [
              IInstrComment(IMov(Reg val_reg, cond), "Puts tuple in reg");
              IInstrComment(ISub(Reg val_reg, Const tup_tag), "Untag tuple");
            ] @ helpPI (RegOffset(i + 1, val_reg)) x
          ) pl)
      | CPConstructor(name, data_opt, (t, _, _)) ->
          let valid_var_label = sprintf "pattern_match_valid_var$%d" t in
          let var_tag = match find_opt type_env name with
            | None -> raise (InternalCompilerError (sprintf "Could not find constructor with name %s" name))
            | Some((var_t, _)) -> var_t in
          let data_matches = 
            match data_opt with
              | None -> [  ]
              | Some(x) -> helpPI (RegOffset(2, val_reg)) x in
          [
            IInstrComment(ISub(Reg val_reg, Const algebraic_tag), "Untag atype");
            (* Gets variant tag *)
            IInstrComment(IMov(Reg val_reg, RegOffset(0, val_reg)), "Gets variant tag for pattern match");
            IMov(Reg tmp_reg, Const var_tag);
            (* Checks variant tag against expected *)
            IInstrComment(ICmp(Reg val_reg, Reg tmp_reg), "Checks variant tag against expected");
            IInstrComment(IJe(Label valid_var_label), "Jumps over flag setting if it passes");
            IMov(Reg tmp_reg, const_false);
            IAnd(Reg result_reg, Reg tmp_reg);
            IJmp(Label bailout);
            IInstrComment(ILabel(valid_var_label), "Jumps here if the variant tag is valid");
            IInstrComment(IMov(Reg val_reg, cond), "Puts the result back in val_reg");
            IInstrComment(ISub(Reg val_reg, Const algebraic_tag), "Untags atype");
            ILineComment("Checking nested data...");
          ] @ data_matches
      | CPImm(imm) -> helpPI cond imm
    in [ IMov(Reg val_reg, cond) ] @ comp_p
  in 
  [IMov(Reg result_reg, const_true);] @ helpPC cond p

(* attempts to reserve size amount of words *)
let reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  let gc_args = [ (* alloc_ptr in C *)
                  Sized (QWORD_PTR, Reg heap_reg);
                  (* bytes_needed in C *)
                  Sized (QWORD_PTR, Const (Int64.of_int size));
                  (* first_frame in C *)
                  Sized (QWORD_PTR, Reg RBP);
                  (* stack_top in C *)
                  Sized (QWORD_PTR, Reg RSP)] in 
  [ 
    ILineComment("Reserving space for a heap allocation");
    IInstrComment(IMov (Reg RAX, RelLabel "?HEAP_END"), sprintf "Reserving %d words" (size / word_size));
    IInstrComment(ISub (Reg RAX, Const (Int64.of_int size)), "Subtracting size needed from end of the heap");
    IInstrComment(ICmp (Reg RAX, Reg heap_reg), "Comparing size needed to size remaining");
    IInstrComment(IJge (Label ok), "If we have space, skip over try_gc call");
    IMov(Reg scratch_reg, HexConst 0xB0BABABEL);
    IPush(Reg scratch_reg);
  ]
  @ (List.map (fun r -> IInstrComment(IPush(Reg r), "Pushing to put reg on stack before gc")) callee_saved)
  @ (extern_function_call "?try_gc" tag gc_args)
  @ [
    IAdd(Reg RSP, Const 8L);
  ]
  @ (List.map (fun r -> IInstrComment(IPop(Reg r), "Popping regs of stack after gc")) (List.rev callee_saved))
  @ [ 
    IInstrComment
        ( IMov (Reg heap_reg, Reg RAX),
          "assume gc success if returning here, so RAX holds the new heap_reg value" );
      ILabel ok ]
;;

(* Allocates elements onto the heap *)
(* For example, for tups, we use [length, elem1, elem2, ...] as the arg *)
let alloc_heap_space elements (tag: int64) (tag_expr: int) =
  let num_elems = List.length elements in
  let space_to_save = (num_elems * word_size) + (if num_elems mod 2 = 0 then 0 else word_size) in
  let reservation_instrs = (reserve space_to_save tag_expr) in
  let add_to_heap = List.flatten (List.mapi (fun i elem -> 
    let m = (
      match elem with
        | RelLabel _ -> ILea(Reg scratch_reg, Sized(QWORD_PTR, elem))
        | _ -> IMov(Reg scratch_reg, Sized(QWORD_PTR, elem))
    ) in
    [
    ILineComment(sprintf "putting {| %s |} on heap" (arg_to_asm elem));
    IInstrComment(m, "Puts the element temporarily in a register");
    IInstrComment(IMov(Sized(QWORD_PTR, RegOffset(i, heap_reg)), Reg scratch_reg), "Moves element into heap memory");
  ]) elements) in
  reservation_instrs
  @ add_to_heap 
  @ [
    ILineComment("cleaning up heap alloc");
    IInstrComment(IMov(Reg RAX, Reg heap_reg), "Saves start location of allocated object in RAX");
    IInstrComment(IAdd(Reg RAX, Const tag), "Tags the object");
    IInstrComment(IAdd(Reg heap_reg, Const (Int64.of_int space_to_save)), "Bumps the free heap pointer");
    ILineComment("end of heap alloc");
  ]
;;

(*  returns a list from [min_inc, max_exc) *)
let rec range min_inc max_exc =
  if min_inc >= max_exc then []
  else max_exc::(range min_inc (max_exc - 1))

(* OMG we use this now and it's kinda the greatest thing ever *)
(* Compiles a function body! *)
let rec compile_fun (fun_name : string) (args : string list) (env : arg name_envt name_envt) (body: (tag * free_vars * live_vars) aexpr) (free_vars: free_vars) (extra_prologue: instruction list) (type_env : (int64 * int64) envt): instruction list =
      let fun_env = (
        match find_opt env fun_name with
          | Some v -> v
          | None -> raise (InternalCompilerError (sprintf "Failed to find evironment for program entrypoint: %s" program_entrypoint))
        ) in
    let num_args = List.length args in
    let (arg_offsets, _) = List.fold_left 
      (fun (acc, i) arg_name ->
        (acc @ [(arg_name, RegOffset((i + arg_offset_from_rbp), RBP))]), (i + 1)) 
      ([], 0) 
      args 
    in
    let new_env = arg_offsets @ fun_env in
    (* For some reason... this happens... some of the times... and we still need this. TODO eventually REMOVE THIS *)
    let local_stack_size = (deepest_stack new_env) in 
    let stack_alignment_label = sprintf "%s$stack$aligned" fun_name in
    let push_callee_saved = List.map (fun r -> 
      IInstrComment(IPush(Reg r), "save callee saved reg @ start of function call")
      ) callee_saved in 
    let pop_callee_saved = List.map (fun r -> 
      IInstrComment(IPop(Reg r), "restore callee saved reg @ end of function call")
      ) (List.rev callee_saved) in 
    [ ILabel (fun_name); ]
    @ [
      ILabel (sprintf "%s$prologue" fun_name);
      (* The stuff that goes at the start of a function! *)
    ]
    @ push_callee_saved
    @ [
      IInstrComment(IPush (Reg RBP), "Saves old RBP for CC");
      IInstrComment(IMov (Reg RBP, Reg RSP), "Moves RBP to new location in new stack frame");
    ]
    @ [  
      ILabel (sprintf "%s$body" fun_name);
    ]
    @ [ILineComment("Tldr: callocs the stack frame")]
    @ [IInstrComment(IMov(Reg scratch_reg, Const 0xDEADCAFEL), "Put stack zeroing val (0xDEADCAFE) into scratch reg");]
    @ (List.map (fun i -> 
      IInstrComment(IMov(RegOffset(~-i, RSP), Reg scratch_reg), sprintf "Zeroing stack frame slot %d" i)
      ) (range 0 local_stack_size))
    @ [
      IInstrComment(IAdd(Reg RSP, Const (Int64.of_int (~-(local_stack_size * word_size)))), "Allocates enough space for all locals in stack frame");
    ] @ [
      (* Make sure the stack is aligned *)
      IInstrComment(ITest(Reg RSP, Const 0xFL), "Checks if stack is aligned");
      IInstrComment(IJz(Label(stack_alignment_label)), "If aligned, jump, otherwise continue");

      IInstrComment(IMov(Reg scratch_reg, Const 0xBEEFCAFEL), "Pushes 0xBEEFCAFE into scratch reg");
      IInstrComment(IPush(Sized(QWORD_PTR, Reg scratch_reg)), "Use dummy val to align at the start of a function call");
      IInstrComment(ILabel(stack_alignment_label), "Stack is now aligned at this point");
    ]
    @ extra_prologue
    (* This is kinda bullshit, but it's how we get away with not stack smashing *)
    @ (compile_aexpr body new_env num_args (fun_name != program_entrypoint) env type_env) 
    @ [ 
      ILabel (sprintf "%s$epilogue" fun_name);
        IInstrComment(IMov (Reg RSP, Reg RBP), "Resets RSP to old location");
        IInstrComment(IPop (Reg RBP), "Restores old RBP"); ]
    @ pop_callee_saved
    @ [ IInstrComment(IRet, "Returns out of the function"); ]

(* Compiles an is_type prim, since they are all the same except for mask and tag *)
(* and compile_is_type type_mask type_tag tag value =
  let not_type_label = sprintf "not_type_%d" tag in
  let done_label = sprintf "done_%d" tag in
  [
  IInstrComment(IMov (Reg RAX, value), "Puts value to check type of in reg");

  (* This is equivalent to the testing we do in C *)
  IInstrComment(IAnd(Reg RAX, Const type_mask), "Ands with type mask (so we just have tag bits left)");
  IInstrComment(IMov (Reg scratch_reg, Const type_tag), "Puts the desired tag into reg");
  IInstrComment(IXor (Reg RAX, Reg scratch_reg), "XORs with desired tag");
  IInstrComment(ICmp (Reg RAX, Const 0L), "Checks if previous XOR is 0, if so, they are the same");

  (* Basically IF code to determine result *)
  IInstrComment(IJnz (Label(not_type_label)), "If not 0, jumps to false case, otherwise continue");
  IInstrComment(IMov (Reg RAX, const_true), "Puts true in RAX");
  IInstrComment(IJmp (Label(done_label)), "Jumps to end - answer has been resolved");
  IInstrComment(ILabel (not_type_label), "Case if type doesn't match");
  IInstrComment(IMov (Reg RAX, const_false), "Puts false in RAX");
  IInstrComment(ILabel (done_label), "Check type prim is over");
  ] *)

(* Compiles an AExpr *)
and compile_aexpr (e : (tag * free_vars * live_vars) aexpr) (env : arg name_envt) (num_args : int) (is_tail : bool) (env_env: arg name_envt name_envt) (type_env: (int64 * int64) envt) : instruction list =
  match e with
  | ALet (name, b_exp, exp, _) ->
  let id_name = match find_opt env name with
    | Some(v) -> v
    | None -> raise (InternalCompilerError(sprintf "compile_aexpr failed to find: %s" name))
    in (
    [ILineComment("Let")]
    @ (compile_cexpr b_exp env num_args false env_env type_env)
    @ [ IMov(id_name, Reg RAX) ]
    @ (compile_aexpr exp env num_args is_tail env_env type_env)
  )
  | ACExpr (exp) -> (compile_cexpr exp env num_args is_tail env_env type_env)
  (* This may be an issue :P *)
  | ASeq (fst, sec, _) -> (compile_cexpr fst env num_args false env_env type_env) @ (compile_aexpr sec env num_args is_tail env_env type_env)
  | ALetRec (binds, body, _) -> 
    (* Compiles the function normally, this will look on the stack for the function closure ptr, but it will be something *else* probably *)
    let compiled_binds = List.flatten (List.map (fun (name, ce) -> 
      let id_name = match find_opt env name with
        | Some(v) -> v
        | None -> raise (InternalCompilerError(sprintf "compile_aexpr failed to find: %s" name))
      in 
      let compiled_ce = (compile_cexpr ce env num_args is_tail env_env type_env) in
      compiled_ce @ [ 
        IInstrComment(IMov(id_name, Reg RAX), sprintf "Puts function %s in it's spot on the stack" name);
      ]
    ) binds) in
    (* This is. literally just going to go through each lambda and put the function closure back where it goes *)
    (* This is the dumbest way to do this. we could be smarter about it as an optimization *)
    let patch_free_vars = List.flatten (List.map (fun (name, ce) ->
      match ce with
        | CLambda(args, body, (t, fvs, _)) -> 
            let free_vars_fr = (StringSet.to_list fvs) in
            let dummy_metadata = (t, StringSet.empty, StringSet.empty) in
            let restore_free_vars =
              [ 
                ILineComment(sprintf "Patching free vars for function <%s> into lambda value" name);
                IInstrComment(IMov(Reg RAX, compile_imm (ImmId(name, dummy_metadata)) env), sprintf "Loading <%s> into memory" name); 
                IInstrComment(ISub(Reg RAX, Const closure_tag), sprintf "Untag closure for <%s>" name);
              ]
              @ (List.flatten (List.mapi (fun i fv -> 
                let fv_location = compile_imm (ImmId(fv, dummy_metadata)) env in
                let fv_dest = RegOffset(i + 4, RAX) in
                (* Puts the free var where it goes on the heap *)
                [
                  IInstrComment(IMov(Reg scratch_reg, fv_location), sprintf "Stashes free var %s in tmp reg" fv);
                  IInstrComment(IMov(fv_dest, Reg scratch_reg), sprintf "Puts free var %s in it's expected stack slot" fv);
                ]
            ) free_vars_fr)) in
          restore_free_vars
        | _ -> raise (InternalCompilerError ("Something incredibly fucked up has occured and we got a non lambda in a let rec"))
    ) binds) in
    compiled_binds
    @ patch_free_vars
    @ (compile_aexpr body env num_args is_tail env_env type_env)

(* Compiles a cexpr! *)
and compile_cexpr (e : (tag * free_vars * live_vars) cexpr) (env : arg envt) (num_args : int) (is_tail : bool) (env_env: arg name_envt name_envt) (type_env: (int64 * int64) envt) =
  match e with
    | CPrim1(op, e, (tag, _, _)) -> (
      let e_reg = compile_imm e env in
      match op with
      | Add1 -> 
          [ILineComment("Add1")]
          @ (check_type e_reg num_tag_mask num_tag "arith_not_num")
          @ [
            IInstrComment(IAdd (Reg RAX, Const 2L), "preforms add1 op");
          ] @ check_overflow
      | Sub1 ->
          [ILineComment("Sub1")]
          @ (check_type e_reg num_tag_mask num_tag "arith_not_num")
          @ [
            IInstrComment(ISub (Reg RAX, Const 2L), "preforms sub1 op");
          ] @ check_overflow
      (* | IsBool -> [ILineComment("IsBool")] @ (compile_is_type bool_tag_mask bool_tag tag e_reg)
      | IsNum -> [ILineComment("IsNum")] @ (compile_is_type num_tag_mask num_tag tag e_reg)
      | IsTuple -> [ILineComment("IsTuple")] @ (compile_is_type tup_tag_mask tup_tag tag e_reg) *)
      | Not -> 
          [ILineComment("Not")]
          @ (check_type e_reg bool_tag_mask bool_tag "logic_not_bool")
          @ [
            IInstrComment(IMov(Reg scratch_reg, bool_mask), "Moves bool mask into reg");
            (* Swap bit (not!) *)
            IInstrComment(IXor(Reg RAX, Reg scratch_reg), "Swaps bool bit for not !");
          ]
      )
    | CPrim2(op, left, right, (tag, _, _)) -> (
    (* left and right expressions be immediates given invariant of ANF *)
    let e1_reg = compile_imm left env in
    let e2_reg = compile_imm right env in
    match op with
    | Plus -> 
        [ILineComment("Plus")]
        @ (check_type e2_reg num_tag_mask num_tag "arith_not_num")
        @ (check_type e1_reg num_tag_mask num_tag "arith_not_num")
        @ [
          IInstrComment(IAdd (Reg RAX, e2_reg), "Adds two numbers from + operator")
        ] @ check_overflow
    | Minus ->
        [ILineComment("Minus")]
        @ (check_type e2_reg num_tag_mask num_tag "arith_not_num")
        @ (check_type e1_reg num_tag_mask num_tag "arith_not_num")
        @ [
          IInstrComment(ISub (Reg RAX, e2_reg), "Subtracts two numbers from - operator");
        ] @ check_overflow
    | Times ->
        [ILineComment("Times")]
        @ (check_type e2_reg num_tag_mask num_tag "arith_not_num")
        @ (check_type e1_reg num_tag_mask num_tag "arith_not_num")
        @ [ 
          IInstrComment(IMul (Reg RAX, e2_reg), "Multiples two numbers from * operator"); 
        ]
        (* We have to check for overflow right after multiplying BC SAR resets the flag I think *)
        @ check_overflow
        @ [ 
          IInstrComment(ISar(Reg RAX, Const 1L), "Accounts for the extra SV power of 2 from multiplication")
        ]
    (* We implement short circuiting as desugaring :P *)
    | And -> raise (InternalCompilerError (sprintf "Did not expect to see an 'and' after desugaring"))
    | Or -> raise (InternalCompilerError (sprintf "Did not expect to see an 'or' after desugaring"))
    (* All of these are the same kinda IF logic, the Jx is different *)
    (* TODO: note to self - get around to these before garter :3 *)
    | Greater -> 
      let is_greater = sprintf "is_greater_%d" tag in
      let done_label = sprintf "done_%d" tag in
      [ILineComment("Greater")]
      @ (check_type e2_reg num_tag_mask num_tag "comp_not_num")
      @ (check_type e1_reg num_tag_mask num_tag "comp_not_num")
      @ [ 
        IMov (Reg RAX, e1_reg);
        ICmp (Reg RAX, e2_reg);
        IJg (Label(is_greater));
        IMov (Reg RAX, const_false);
        IJmp (Label(done_label));
        ILabel (is_greater);
        IMov (Reg RAX, const_true);
        ILabel (done_label);
      ]
    | GreaterEq -> 
      let is_greater_eq = sprintf "is_greater_eq_%d" tag in
      let done_label = sprintf "done_%d" tag in
      [ILineComment("GreaterEq")]
      @ (check_type e2_reg num_tag_mask num_tag "comp_not_num")
      @ (check_type e1_reg num_tag_mask num_tag "comp_not_num")
      @ [ 
        IMov (Reg RAX, e1_reg);
        ICmp (Reg RAX, e2_reg);
        IJge (Label(is_greater_eq));
        IMov (Reg RAX, const_false);
        IJmp (Label(done_label));
        ILabel (is_greater_eq);
        IMov (Reg RAX, const_true);
        ILabel (done_label);
      ]
    | Less -> 
      let is_less = sprintf "is_less_%d" tag in
      let done_label = sprintf "done_%d" tag in
      [ILineComment("Less")]
      @ (check_type e2_reg num_tag_mask num_tag "comp_not_num")
      @ (check_type e1_reg num_tag_mask num_tag "comp_not_num")
      @ [ 
        IMov (Reg RAX, e1_reg);
        ICmp (Reg RAX, e2_reg);
        IJl (Label(is_less));
        IMov (Reg RAX, const_false);
        IJmp (Label(done_label));
        ILabel (is_less);
        IMov (Reg RAX, const_true);
        ILabel (done_label);
      ]
    | LessEq -> 
      let is_less_eq = sprintf "is_less_eq_%d" tag in
      let done_label = sprintf "done_%d" tag in
      [ILineComment("LessEq")]
      @ (check_type e2_reg num_tag_mask num_tag "comp_not_num")
      @ (check_type e1_reg num_tag_mask num_tag "comp_not_num")
      @ [ 
        IMov (Reg RAX, e1_reg);
        ICmp (Reg RAX, e2_reg);
        IJle (Label(is_less_eq));
        IMov (Reg RAX, const_false);
        IJmp (Label(done_label));
        ILabel (is_less_eq);
        IMov (Reg RAX, const_true);
        ILabel (done_label);
      ]

    (* Equality must be total, so we just compare both values *)
    | Eq ->
      let is_eq = sprintf "is_eq_%d" tag in
      let done_label = sprintf "done_%d" tag in
      [ 
        ILineComment ("Eq");
        IInstrComment(IMov (Reg RAX, e2_reg), "Moves right hand side of EQ into reg");
        IInstrComment(IMov(Reg scratch_reg, e1_reg), "Moves left hand side of EQ into reg");
        IInstrComment(ICmp (Reg RAX, Reg scratch_reg), "Checks for equality");
        IInstrComment(IJz (Label(is_eq)), "Jumps based on equality");
        IMov (Reg RAX, const_false);
        IJmp (Label(done_label));
        ILabel (is_eq);
        IMov (Reg RAX, const_true);
        ILabel (done_label);
      ]
  )
    | CIf(cond, thn, els, (tag, _, _)) ->
      (* From ANF definition we know cond should be immediate expr while then and else will be ANF *)
      let cond_reg = compile_imm cond env in
      let thn_instruction_list = compile_aexpr thn env num_args is_tail env_env type_env in
      let els_instruction_list = compile_aexpr els env num_args is_tail env_env type_env in
      let else_label = sprintf "if_false_%d" tag in
      let done_label = sprintf "done_%d" tag in
        [ ILineComment ("If Statement") ]
        @ (check_type cond_reg bool_tag_mask bool_tag "if_not_bool")
        @ [
          IInstrComment(IMov(Reg RAX, cond_reg), "Moves If condition into a reg");
          IInstrComment(ICmp(Reg RAX, const_true), "Checks if the condition is true");
          IInstrComment(IJne(Label(else_label)), "Jumps to else label if not true");
        ]
        @ thn_instruction_list
        @ [ 
          IInstrComment(IJmp(Label(done_label)), "Jumps to the done label to skip over else branch"); 
          ILabel(else_label) 
        ]
        @ els_instruction_list
        @ [ 
          ILabel(done_label) 
        ]
    | CApp(function_obj, args, call_type, (t, _, _)) ->
        let compiled_args = (List.map (fun arg -> compile_imm arg env) args) in
        (match call_type with
          | Prim | Unknown -> raise (InternalCompilerError(sprintf "We will probably have to deal with this in fer-de-lance IG"))
          | Native -> 
            (match function_obj with
              | ImmId(extern_name, _) -> 
                  let new_comp_args = if extern_name = "printStack" then compiled_args @ [Reg RSP; Reg RBP; Const (Int64.mul 2L (Int64.of_int num_args))] else compiled_args in
                  [ ILineComment ("Native Function Call" )] 
                  @ (extern_function_call extern_name t new_comp_args)
              | _ -> failwith "external call borkn")
          | Snake ->
            (* todo : overloading names of different arities would move fname to rename *)
            let comp_fun_obj = compile_imm function_obj env in
            let push_args = List.flatten (List.map (fun reg -> [
              IInstrComment(IMov(Reg scratch_reg, reg), "Move function arg into a tmp reg"); 
              IInstrComment(IPush (Sized(QWORD_PTR, Reg scratch_reg)), "Pushes function arg onto the stack");
              ]) (List.rev compiled_args)) in
            (* Do we need to change out definition of same amount of args? *)
            let setup_args = 
              (* I love my life so much *)
              (match (is_tail && (num_args >= List.length args)) with
                | true -> 
                  push_args 
                  @ [ 
                    ILineComment("Tail recursion reuses the stack frame by over-writing args") ;
                    (* This probably wont work but whatever *)
                    (* I think there could be an issue where we overwrite this? but maybe no? since it's the same place? *)
                    IInstrComment(IMov(Reg scratch_reg, comp_fun_obj), "Move the function object into temp reg for tail rec");
                    IInstrComment(IMov(RegOffset(arg_offset_from_rbp - 1, RBP), Reg scratch_reg), "Move the function object into the new place on the stack");
                  ] 
                  (* then move them into place *)
                  @ (let (_, place_args_instrs) = (List.fold_left (fun (offset, instructions) _ -> (
                    (offset + 1, instructions @ [
                      IInstrComment(IPop(Sized(QWORD_PTR, RegOffset((offset + arg_offset_from_rbp), RBP))), "Pops the instruction off the stack into the correct arg slots");
                  ])
                  )) (0 (* this is the started point after the pre-saved things *), []) compiled_args) in place_args_instrs)
                  @ [
                    (* Sets up the stack as expected when we jump into a function *)
                    IInstrComment(IMov(Reg RSP, Reg RBP), "Resets RSP on the stack so it's as expected at the start of the function call");
                  ]
                | false -> push_args) in
            let stack_cleanup = 
              (* Added +1 to include closure object *)
              let arg_size = ((List.length args) + 1) * 8 in [
                IInstrComment(IAdd(Reg RSP, Const (Int64.of_int arg_size)), "Reclaims stack space from pushed args");
            ] in
            (* Check function obj type *)
            (check_type comp_fun_obj closure_tag_mask closure_tag "call_not_clos") 
            (* Get function object from the thing *)
            @ [ ILineComment("Converting to a function object")]
            @ [ IInstrComment(ISub(Reg RAX, Const closure_tag), "Untag the closure") ]
            (* Check arity *)
            @ [ ILineComment("Checking arity")]
            @ [ 
              IInstrComment(IMov(Reg scratch_reg, RegOffset(0, RAX)), "Get the function's arity (snake_val)"); 
              IInstrComment(ICmp(Reg scratch_reg, Const (Int64.of_int ((List.length args) * 2))), "Check the arity against number of args provided"); 
              IInstrComment(IJnz(Label "call_arity"), "Error if arity is wrong");
            ]
            (* Push args *)
            @ setup_args
            (* Push function obj *)
            @ [ 
              IInstrComment(IMov(Reg scratch_reg, comp_fun_obj), "Push func obj into temp reg");
              IInstrComment(IPush(Sized(QWORD_PTR, Reg scratch_reg)), "Pushed function object onto stack as part of new CC");
            ]
            (* Call function *)
            @ (match (is_tail && (num_args >= List.length args)) with
                | false -> 
                [
                  IInstrComment(IMov(Reg scratch_reg, RegOffset(1, RAX)), "Gets the address of the closure code");
                  IInstrComment(ICall(Reg scratch_reg), "Calls the function");
                  ]
                | true -> [
                      IInstrComment(IMov(Reg scratch_reg, RegOffset(2, RAX)), "Gets the address of the closure code");
                      IInstrComment(IJmp(Reg scratch_reg), "Jumps for tail recursion");
                  ])
            @ [ 
            ]
            @ stack_cleanup)
    | CTuple(elements, (t, _, _)) -> 
        let tuple_size_sv = Int64.of_int ((List.length elements) * 2) in
        [ ILineComment("Create a Tuple ") ]
        @ (alloc_heap_space ([Const tuple_size_sv] @ (List.map (fun (e) -> (compile_imm e env)) elements)) tup_tag t)
    | CGetItem(tup, idx, _) -> 
      let tup_imm = compile_imm tup env in
      let idx_imm = compile_imm idx env in
      [ ILineComment("Get Tuple Item") ]
        @ (check_type tup_imm tup_tag_mask tup_tag "get_not_tup")
        @ [
          (* Untag tuple *)
          IInstrComment(ISub(Reg RAX, Const tup_tag), "Untag tuple");
          
          (* Check for Nil *)
          IInstrComment(ICmp(Reg RAX, Const nil_val), "Compares to nil value");
          IInstrComment(IJz(Label("nil_deref")), "Jumps to error if deref nil");

          (* Check if it's less than 0 *)
          IInstrComment(IMov(Reg scratch_reg, idx_imm), "Moves idx into reg");
          IInstrComment(ICmp(Reg scratch_reg, Const 0L), "Checks that the idx is > 0");
          IInstrComment(IJl(Label("get_low_idx")), "Jumps to error if idx is < 0");

          (* Checks if it's greater than the arity *)
          (* IInstrComment(ISar(Reg scratch_reg, Const 1L), "Converts idx snake val to machine val"); *)
          IInstrComment(ICmp(Reg scratch_reg, RegOffset(0, RAX)), "Checks against size of tuple for out of bounds error");
          IInstrComment(IJge(Label("get_high_idx")), "Jumps to error if idx > tuple arity");

          (* Gets the element! *)
          IInstrComment(ISar(Reg scratch_reg, Const 1L), "Converts idx snake val to machine val");
          IInstrComment(IMov(Reg RAX, RegOffsetReg(RAX, scratch_reg, 8, 8)), "Moves from the nth element of the tuple on the heap to RAX");
        ]
    | CSetItem(tup, idx, value, _) ->
      let tup_imm = compile_imm tup env in
      let idx_imm = compile_imm idx env in
      let val_imm = compile_imm value env in
      [ ILineComment("Set Tuple Item") ]
      @ (check_type tup_imm tup_tag_mask tup_tag "set_not_tup")
      @ [
        (* Untag tuple *)
        IInstrComment(ISub(Reg RAX, Const tup_tag), "Untag tuple");

        (* Check for Nil *)
        IInstrComment(ICmp(Reg RAX, Const nil_val), "Compares to nil value");
        IInstrComment(IJz(Label("nil_deref")), "Jumps to error if deref nil");

        (* Check if it's less than 0 *)
        IInstrComment(IMov(Reg scratch_reg, idx_imm), "Moves idx into reg");
        IInstrComment(ICmp(Reg scratch_reg, Const 0L), "Checks that the idx is > 0");
        IInstrComment(IJl(Label("set_low_idx")), "Jumps to error if idx is < 0");

        (* Checks if it's greater than the arity *)
        IInstrComment(ICmp(Reg scratch_reg, RegOffset(0, RAX)), "Checks against size of tuple for out of bounds error");
        IInstrComment(IJge(Label("set_high_idx")), "Jumps to error if idx > tuple arity");

        (* Preforms the mutation! *)
        IInstrComment(ISar(Reg scratch_reg, Const 1L), "Converts idx snake val to machine val");
        IInstrComment(IMov(Reg RDX, val_imm), "Puts the value to set the tuple to into a tmp reg");
        IInstrComment(IMov(RegOffsetReg(RAX, scratch_reg, 8, 8(* Hi this is julia - this is so we don't modify the arity (0th elem) :3 *)), Reg RDX), "Sets the element in the tuple to the new value");
        IInstrComment(IMov(Reg RAX, Reg RDX), "Puts the new tuple element into rax");
      ]
    | CImmExpr(exp) -> [ ILineComment("CImmExpr"); IMov(Reg RAX, compile_imm exp env) ]
    | CLambda(args, body, (t, fvs, _)) ->
      let name = name_lambda e in
      let tail_name = sprintf "%s$body" name in
      let free_vars = StringSet.to_list fvs in
      let num_free_vars_sv = List.length free_vars * 2 in
      let lambda_env = (match find_opt env_env name with
        | Some v -> v
        | None -> raise (InternalCompilerError (sprintf "Failed to find the env for lambda: %s" name))
      ) in
      (* Adds free vars to lambda compilation env *)
      let restore_free_vars = [
        (* Get the function closure *)
        IInstrComment(IMov(Reg RAX, RegOffset(arg_offset_from_rbp - 1, RBP)), "Gets the function closure from modified calling convention");
        IInstrComment(ISub(Reg RAX, Const closure_tag), "Untag closure so we can access fields");
        ILineComment("Moves all closed over values onto the stack from heap:");
        (* Put the closure values on the stack in a findable place *)
      ] @ (List.flatten (List.mapi (fun i v -> 
        (match find_opt lambda_env v with
          | None -> (raise (InternalCompilerError((sprintf "Lambda failed to find closed over variable in the env in compile_cexpr %s" v))))
          | Some offset -> [
            ILineComment(sprintf "Unpacking closed over variable: %s" v);
            IInstrComment(IMov(Reg scratch_reg, Sized(QWORD_PTR, RegOffset(i + 4, RAX))), sprintf "Gets %s from closure object" v);
            IInstrComment(IMov(offset, Reg scratch_reg), "Puts value onto the stack");
          ])
      ) free_vars)) in
      let compiled_lambda = compile_fun name args env_env body fvs restore_free_vars type_env in
      let end_label = sprintf "lambda_fun_end$%d" t in
      let arity_sv = (List.length args) * 2 in
      [ 
        IInstrComment(IJmp(Label end_label), "Jumps over lambda body"); 
        ILineComment("Lambda body"); ]
      @ compiled_lambda
      @ [ ILabel(end_label); ILineComment("Sets up the lambda object") ]
      (* | arity | code pointer | # vars | var_1 | var_2 | .... | padding ? |*)
      (* we store the number of variables as raw numbers for simpler debugging  *)
      @ alloc_heap_space 
        ([Const (Int64.of_int arity_sv); RelLabel name; RelLabel tail_name; Const (Int64.of_int num_free_vars_sv)] 
        @ (List.map (fun var -> compile_imm (ImmId(var, (t, StringSet.empty, StringSet.empty))) env) free_vars))
        closure_tag
        t
    | CMatch(branches, (t, _, _)) -> 
        let match_start_label branch_num = sprintf "match_branch_%d$%d" branch_num t in
        let match_end_label = sprintf "match_end$%d" t in
        let branches_fail_label = sprintf "match_fail$%d" t in
        let number_of_branches = List.length branches in
        (List.flatten (List.mapi (fun i (ipl, ae) ->
          let bailout_num = i + 1 in
          let bailout_label = if bailout_num = number_of_branches then branches_fail_label else match_start_label bailout_num in
          let curr_branch_label = match_start_label i in
          let check_patterns_and_bind = List.flatten (List.map (fun (im, p) ->
            let cond = compile_imm im env in
            let utag = match im with
              | ImmBool(_, (t, _, _)) 
              | ImmId(_, (t, _, _)) 
              | ImmNil((t, _, _))
              | ImmNum(_, (t, _, _)) -> t in
            (* Bleh - this is so we can get a unique bail out name eww *)
            evaluate_pattern cond p type_env env bailout_label
          ) ipl) in
          (* check_patterns_and_bind *)
          [ ILabel(curr_branch_label); ]
          @ check_patterns_and_bind 
          (* Check if the pattern match was ok *)
          @ [
            IMov(Reg scratch_reg, const_true);
            ICmp(Reg RAX, Reg scratch_reg);
            (* Jump to next branch if it failed *)
            IJne(Label bailout_label);
          ]
          (* Body of the branch *)
          @ (compile_aexpr ae env num_args is_tail env_env type_env)
          @ [ IJmp(Label match_end_label); ]
        ) branches)) @ [
          (* All branches fail! *)
          ILabel(branches_fail_label); 
          IJmp(Label "no_match"); (* TODO make this work *)

          (* End of match! Success! *)
          ILabel(match_end_label);
        ]
    | CConstructor(name, arg_opt, (t, _, _)) -> 
        let associated = match arg_opt with
          | None -> [ Const none_val; ]
          | Some(exp) -> [compile_imm exp env] in
        let (var_tag, typ_tag) = match find_opt type_env name with
          | None -> raise (InternalCompilerError ("Constructor failed to find name in type env [" 
          ^ (List.fold_left (fun a x -> a ^ x) "" (names_in_envt type_env)) ^ "]"))
          | Some(x) -> x in
        (alloc_heap_space ([Const var_tag; Const typ_tag;] @ associated) algebraic_tag t)
and compile_imm (e: (tag * free_vars * live_vars) immexpr) (env : arg envt) =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> (match find_opt env x with
    | Some(v) -> v
    | None -> 
        let e_name = ExtString.String.join ", " (List.map (fun (name, _) -> name) env) in
        raise (InternalCompilerError(sprintf "compile_imm failed to find name in env [%s]: %s" e_name x)))
  | ImmNil _ -> Const 1L (* This is just the tag bit *)
;;

(* It would be cute later to map over a list of errors, which also contain some info about themselves like name and return value *)
(* Generates a label to jump to which handles an error *)
let gen_error_handler (name: string) (value: int64): instruction list =
  [
    ILabel(name);
    IInstrComment(IMov(Reg RSI, Reg RAX), "Moves value into C arg slot");
    IInstrComment(IMov(Reg RDI, Const(value)), "Moves error code into C arg slot");
  ]
  (* Align stack - needs some unique tag *)
  @ [ IInstrComment(ICall(Label("?error")), "Call into runtime error handler"); ]
;;

let compile_prog ((anfed : (tag * free_vars * live_vars) aprogram), (env : arg name_envt name_envt)) : string =
  match anfed with 
  | AProgram (tdecs, expr, _) -> 
    ( 
      let runtime_fun_externs = List.fold_left (fun asm_str (name, _) -> asm_str ^ (sprintf "extern %s\n" name)) "" supported_runtime_functions in
      let type_env = build_type_env tdecs in
      let rotated_typ_env = build_rotated_type_env tdecs in
      let type_lookup_table, type_names = List.fold_right 
        (fun (typ_id, var_name_map) (s, tnames) -> 
          let type_name = sprintf "type_%d" (Int64.to_int typ_id) in
          let var_lookup_table, var_names = List.fold_right (fun (var_id, variant_name) (s, vnames) ->
            let var_name = sprintf "var_%d_%d" (Int64.to_int typ_id) (Int64.to_int var_id) in 
            ((sprintf "%s db \"%s\", 0h\n%s" var_name variant_name s), var_name::vnames)
          ) var_name_map ("", []) in
          let var_names_s = ExtString.String.join ", " var_names in
          (sprintf "%s dq %s\n%s%s" type_name var_names_s var_lookup_table s, type_name::tnames)
        ) rotated_typ_env ("", []) in 
      let type_names_s = ExtString.String.join ", " type_names in
      let data_section = (sprintf "section .data\ntype_lookup dq %s\n%s" type_names_s type_lookup_table) in
      let prelude = (sprintf "%ssection .text\nextern ?error\nextern ?try_gc\nextern ?HEAP_END\nextern ?HEAP\nextern ?set_stack_bottom\n%sglobal type_lookup\nglobal %s\n" data_section runtime_fun_externs program_entrypoint) in
      let postlude =
        [ 
          ILineComment("Error handling labels (none of these return)");
        ]
        @ (List.flatten (List.map (fun (n, v) -> gen_error_handler n v) supported_runtime_errors))
      in
      let extra_entrypoint_prologue = [

      ] 
      @ [
        (* Moves arg into heap Reg*)
        IInstrComment(IMov(Reg R15, Reg RDI), "Moves heap start into the heap reg");
        (* Aligns heap *)
        ILineComment("Aligns Heap");
        IAdd(Reg R15, Const 7L);
        IMov(Reg scratch_reg, HexConst 0xfffffffffffffff8L);
        IAnd(Reg R15, Reg scratch_reg);
      ] 
      @ (extern_function_call "?set_stack_bottom" 0 [Reg RBP;])
      @ (List.map (fun r -> IMov(Reg r, Const 0L)) callee_saved)
      in
      let entrypoint = compile_fun program_entrypoint [] env expr StringSet.empty extra_entrypoint_prologue type_env in
      let as_assembly_string = to_asm (entrypoint @ postlude) in
      sprintf "%s%s\n" prelude as_assembly_string )
;;


let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation
;;

(* Sets up all of the phases in the compiler pipeline and passes the program through *)
let compile_to_string
    ?(no_builtins = false)
    ?(no_typechecking = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_typechecking) (add_err_phase type_checked is_well_typed)
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase free_var_cached free_vars_cache
  |> add_phase live_var_cached live_var_cache
  |> add_phase dead_var_elimed dead_var_elim
  (* todo: add alloc_stratagy to part of naive_stack_allocation *)
  |> add_phase locate_bindings naive_stack_allocation (* (pick_alloc_strategy alloc_strat) *)
  |> add_phase result compile_prog
;;
