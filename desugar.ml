open Exprs
open Errors
open Utils
open Printf
open Pretty

(* Validates if a function is in ANF *)
let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1 (_, e, _) -> is_imm e
  | EPrim2 (_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet (binds, body, _) -> List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
  | EIf (cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | EApp (_, args, _, _) -> List.fold_left (fun a b -> a && (is_imm b)) true args
  | ESeq(a, b, _) -> is_anf a && is_anf b
  | ETuple(elems, _) -> List.for_all (fun e -> is_imm e) elems
  | EGetItem(a, b, _) -> is_imm a && is_imm b
  | ESetItem(a, b, c, _) -> is_imm a && is_imm b && is_imm c
  | _ -> is_imm e
(* Checks if a function is immediate *)
and is_imm e =
  match e with
  | ENumber _ -> true
  | EId _ -> true
  | EBool _ -> true
  | ENil _ -> true
  | _ -> false
;;

(* Desugaring function for lets *)
let rec expand_bindings (b: (string * 'a cexpr) list)(e: 'a aexpr) : 'a aexpr =
  (List.fold_right 
  (fun (name, bind_exp) (exp: 'a aexpr) -> 
    ALet(name, bind_exp, exp, ()))
  b e)
;;

(* Currently this stage ensures 
    -  each let only has one binding 
    -  each and/or statement is turned into an if statement for short circuiting 
    -  declerations are turned into let rec groups 
      *)
let rec desugar (p: sourcespan program) : sourcespan program =
  let rec desugar_expr (e: sourcespan expr) : sourcespan expr =
    match e with
      | ENumber _ | EBool _ | EId _ | ENil _ -> e
      | ETuple (exprs, t) -> ETuple ((List.map desugar_expr exprs), t)
      | EGetItem(a, b, t) -> EGetItem(desugar_expr a, desugar_expr b, t)
      | ESetItem(a, b, c, t) -> ESetItem(desugar_expr a, desugar_expr b, desugar_expr c, t)
      | EPrim1(prim, exp, t) -> EPrim1(prim, (desugar_expr exp), t)
      | EPrim2(prim, l_exp, r_exp, t) -> 
        (match prim with 
        (* to avoid the error being around if we ensure the type checker looks for logical statements by wrapping booleans in a not operator *)
        | Or -> EIf(EPrim1(Not, (desugar_expr l_exp), t), EPrim1(Not, EPrim1(Not, (desugar_expr r_exp), t), t), EBool(true, t), t)
        | And -> EIf(EPrim1(Not, (desugar_expr l_exp), t), EBool(false, t), EPrim1(Not, EPrim1(Not, (desugar_expr r_exp), t), t), t)
        | prim -> EPrim2(prim, (desugar_expr l_exp), (desugar_expr r_exp), t))
      | EIf(pred, then_exp, else_exp, t) -> EIf((desugar_expr pred), (desugar_expr then_exp), (desugar_expr else_exp), t)
      | EApp(fun_expr, args, ct, t) -> 
        let desugared_args = List.map desugar_expr args in
        (match ct with 
        | Native -> EApp((desugar_expr fun_expr), desugared_args, Native, t)
        | _ -> EApp((desugar_expr fun_expr), desugared_args, Snake, t))
      | ELet(bindings, exp, t) -> (List.fold_right
        (fun (name, bind_exp, b_t) (exp_acc) -> 
          (match name with
            | BTuple (binds, t) ->
                let new_tmp_bind = (sprintf "tup_desugaring_%s" (string_of_sourcespan t)) in
                let (nested_tuple_exp, _) =
                (List.fold_right 
                  (fun bind (tup_exp_acc, i) -> 
                    let tup_idx = ((List.length binds) - i - 1) in 
                    (desugar_expr (ELet([(bind, (EGetItem(EId(new_tmp_bind, t), ENumber(Int64.of_int(tup_idx), t), t)), t)], tup_exp_acc, t)), i + 1))
                binds (exp_acc, 0)) in
                (* since we desugar after type env is built this dummy type needs to be changed once thats done *)
                ELet([(BName(new_tmp_bind, TInt dummy_span, false, t), desugar_expr bind_exp, t)], nested_tuple_exp, t)
            | BName _ | BBlank _ -> ELet([(name, (desugar_expr bind_exp), b_t)], 
            exp_acc, t))) 
        bindings (desugar_expr exp))
      | ESeq(a, b, t) -> ELet([(BBlank(t), (desugar_expr a), t)], (desugar_expr b), t)
      | ELambda(binds, typ, body, t) -> ELambda(binds, typ, (desugar_expr body), t)
      | ELetRec(bindings, exp, t) -> 
        let desugared_bindings = (List.map (fun (bind, exp, tag) -> (bind, (desugar_expr exp), tag)) bindings) in
        ELetRec(desugared_bindings, (desugar_expr exp), t)
      | EConstructor(name, args, t) -> 
          (* Desugars args to either none, one, or a tuple containing multiple *)
          let new_args = match args with
            | [] | _::[] -> (List.map desugar_expr args)
            | _ -> ETuple(List.map desugar_expr args, t)::[] in
          EConstructor(name, new_args, t)
      | EMatch(e, pe_l, t) ->
          let des_pe_l = List.map (fun (p, e) -> (desugar_pattern p, desugar_expr e)) pe_l in
          EMatch(desugar_expr e, des_pe_l, t)

  and desugar_pattern (p: 'a pattern) : 'a pattern =
    match p with
      | PConstructor(name, pl, t) ->
          let new_pl = match pl with
            | [] | _::[] -> (List.map desugar_pattern pl)
            | _ -> PTup(List.map desugar_pattern pl, t)::[] in
          PConstructor(name, new_pl, t)
      | PTup(pl, t) -> PTup(List.map desugar_pattern pl, t)
      | _ -> p
          
  (* desugars the bindings of the decls, formatting them to allow for tuple use *)
  and desugar_decl_bindings (decls: 'a decl list list) : ('a decl list list) =
    (List.map 
      (fun decel_list -> 
      (* Lets turn each list into its desugared version *)
        (List.map 
          (fun decel -> 
            match decel with 
              | DFun(name, args, typ, fun_body, tag) -> 
                (* Processing each function arguments to handle tuple bindings *)
                let (new_args, new_fun_body) =
                  List.fold_right (fun arg (new_arg_acc, new_fun_body_acc) -> 
                    match arg with
                    | BTuple(binds, _) -> 
                      (* If the argument is a tuple, introduce a temporary variable *)
                      let tmp_bind_name = sprintf "tup_desugaring$%s" name in
                      let new_var = EId(tmp_bind_name, tag) in
                      (* Desugar the tuple by extracting elements into separate bindings *)
                      let let_body =
                        List.fold_right (fun (bind, i) body_acc ->
                          let indexed_access = EGetItem(new_var, ENumber(Int64.of_int i, tag), tag) in
                          ELet([(bind, indexed_access, tag)], body_acc, tag)
                        ) (List.mapi (fun i bind -> (bind, i)) binds) new_fun_body_acc
                      in
                      (* Add the temporary variable to function arguments *)
                      (* since we desugar after type env is built this dummy span can be changed later *)
                      (BName(tmp_bind_name, TInt dummy_span, false, tag) :: new_arg_acc, desugar_expr let_body)
                    (* If it's a normal variable or blank, keep it as is *)
                    | BName _ | BBlank _ -> (arg :: new_arg_acc, new_fun_body_acc)
                  ) args ([], fun_body)
                in
                DFun(name, new_args, typ, desugar_expr new_fun_body, tag)) 
          decel_list)) 
    decls) 
  (* desugars the declerations by instead wrapping the original body in lambdas *)
  and desugar_decls_to_expr (decls: 'a decl list list) (body: 'a expr) (program_tag : 'a) : ('a expr) =
    List.fold_right
        (fun (decl_list : 'a decl list) (acc : 'a expr) ->
          let bindings : 'a binding list =
            (List.map
              (fun decl ->
                match decl with
                | DFun (name, args, typ, fun_body, tag) -> 
                  let function_typ = 
                    if List.length args = 0 then typ 
                    else 
                      let arg_types = List.map 
                        (fun arg -> 
                          match arg with
                          | BName(_, arg_typ, _, _) -> arg_typ
                          | _ -> failwith "Expected BName with type information")
                          args 
                      in
                      TFunction (
                        (match arg_types with
                        | [t] -> t
                        | typs -> TProduct(typs, tag)),
                        typ,
                        tag)
                  in
                  (BName (name, function_typ, false, tag)), (ELambda (args, function_typ, fun_body, tag)), tag)
              decl_list)
          in
          (* Wrap each letrec in a lambda to prevent external references *)
          (* ELambda ([], ELetRec (bindings, acc, tag), tag)) *)
          (* Or don't to allow later groups to reference earlier ones *)
          (ELetRec (bindings, acc, program_tag)))
        decls
        body
  in
    match p with
      | Program(ty, decls, body, t) ->
        (match decls with 
        | [] -> Program(ty, decls, desugar_expr body, t)
        | _ -> (Program (ty, [], (desugar_expr (desugar_decls_to_expr (desugar_decl_bindings decls) body t)), t)))
;;
  
