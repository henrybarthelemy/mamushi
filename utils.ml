open Exprs
open Assembly
open Lexing

(* Documentation can be found at https://v2.ocaml.org/api/Set.S.html *)
module StringSet = Set.Make (String)

(* Documentation can be found at https://v2.ocaml.org/api/Map.S.html *)
module StringMap = Map.Make (String)

type free_vars = StringSet.t

type live_vars = StringSet.t

(* :3:3:3 *)

type 'a envt = (string * 'a) list

let program_entrypoint = "?our_code_starts_here"

(* Some constants defined *)
let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x000000000000000FL

let bool_tag_mask = 0x000000000000000FL

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let tup_tag = 0x0000000000000001L

let tup_tag_mask = 0x0000000000000007L

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x0000000000000007L

let algebraic_tag = 0x0000000000000007L

let algebraic_tag_mask = 0x000000000000000FL

let nil_val = 0x0000000000000001L

(* This is 0L tagged as an atype *)
let none_val = 0x0000000000000007L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_NIL_DEREF = 9L

(* not used in compilation yet, but still needed to account for the error type in c main *)
let err_INPUT_INVALID = 10L 

let err_OUT_OF_MEMORY = 11L

let err_SET_NOT_TUPLE = 12L

let err_SET_LOW_INDEX = 13L

let err_SET_NOT_NUM = 14L

let err_SET_HIGH_INDEX = 15L

let err_CALL_NOT_CLOSURE = 16L

let err_CALL_ARITY_ERR = 17L

let err_NO_MATCH = 18L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let scratch_reg = R11

let scratch_reg_2 = R10

let heap_reg = R15

let caller_saved = [R9; R8; RCX; RDX; RSI; RDI]

let callee_saved = [RBX; R12; R13; R14] (* RBX meow *)

let arg_offset_from_rbp = 3 + List.length callee_saved

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let supported_runtime_functions = [
  ("print", 1);
  ("println", 1);
  ("printStack", 1);
  ("inputBool", 0);
  ("inputInt", 0);
  ("equal", 2);
]

let rec find_opt ls x =
  match ls with
    | [] -> None
    | (y, v) :: rest ->
        if y = x then Some(v) else find_opt rest x
;;

(* erroring version of the above *)
let rec find ls x =
  match ls with
    | [] -> failwith "UHHHH"
    | (y, v) :: rest ->
        if y = x then v else find rest x
;;

let is_runtime (fname: string) : bool =
  List.fold_left 
    (fun prev (rt_name, _) -> prev || (rt_name = fname)) 
    false 
    supported_runtime_functions
;;

let get_arity (fname: string) : int option = (find_opt supported_runtime_functions fname);;

let supported_runtime_errors = [
  ("comp_not_num", err_COMP_NOT_NUM);
  ("arith_not_num", err_ARITH_NOT_NUM);
  ("logic_not_bool", err_LOGIC_NOT_BOOL);
  ("if_not_bool", err_IF_NOT_BOOL);
  ("overflow", err_OVERFLOW);
  ("get_not_tup", err_GET_NOT_TUPLE);
  ("get_low_idx", err_GET_LOW_INDEX);
  ("get_high_idx", err_GET_HIGH_INDEX);
  ("nil_deref", err_NIL_DEREF);
  ("input_invalid", err_INPUT_INVALID);
  ("out_of_memory", err_OUT_OF_MEMORY);
  ("set_not_tup", err_SET_NOT_TUPLE);
  ("set_low_idx", err_SET_LOW_INDEX);
  ("set_not_num", err_SET_NOT_NUM);
  ("set_high_idx", err_SET_HIGH_INDEX);
  ("call_not_clos", err_CALL_NOT_CLOSURE);
  ("call_arity", err_CALL_ARITY_ERR);
  ("no_match", err_NO_MATCH);
]

(* checks if an item is in the list provided *)
let rec contains (item: 'a) (list: 'a list): bool =
  match list with 
  | [] -> false
  | value :: rol -> value = item || (contains item rol)
;;

(* checks if the list provided has all unique elements, returning the non unique element if it exists *)
let rec unique (lst: 'a list) : 'a option =
  match lst with
  | [] -> None
  | x :: xs -> if (contains x xs) then Some x else unique xs
;;

let rec find_bind_opt ls x =
  match ls with
  | [] -> None
  | BNameTyped (y, _, _, v) :: rest ->
      if y = x then
        Some v
      else
        find_bind_opt rest x
  | BTuple (binds, _) :: rest ->
    let inner_has = (find_bind_opt binds x) in
    (match inner_has with
    | None -> (find_bind_opt rest x)
    | result -> result)
  | _ :: rest -> find_bind_opt rest x
;;

let rec names_in_pattern p =
  match p with
  | PBlank _ | PLiteral _ -> []
  | PId(name, _) -> [name]
  | PTup(pl, _) | PConstructor(_, pl, _) -> List.concat (List.map names_in_pattern pl)
;;

let rec names_in_cpattern p =
  match p with
  | CPTup(ipl, _) -> List.concat (List.map names_in_ipattern ipl)
  | CPConstructor(_, ip_opt, _) -> (match ip_opt with | None -> [] | Some(i) -> names_in_ipattern i)
  | CPImm(i) -> names_in_ipattern i
and names_in_ipattern p =
  match p with
  | IPId(name, _) -> name::[]
  | _ -> []
;;

let names_in_envt (e: 'a envt) =
  List.map (fun (name, _) -> name) e
