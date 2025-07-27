open Exprs
open Errors
open Utils
open Printf
open Pretty

(* Renames all let bindings so that every name is unique *)
(* This is useful for the case where we define a variable x in both sides of a prim2 *)
(* Change to a tag program *)
let rename (p : tag program) : tag program =
  let rec rename_expr (env : (string * string) list) (e : tag expr) =
    match e with
    (* Looks up the new name in out env and renames the binding to this *)
    | EId (x, tag) -> 
        if (is_runtime x) then EId(x, tag) else
        let name = match find_opt env x with
          | Some(v) -> v
          | None -> raise (InternalCompilerError(sprintf "Failed to find name in rename %s" x))
        in EId(name, tag)
    | ELet (binds, body, tag) -> let (new_env, new_bindings) = 
        (* Traverses the bindings, renames them, and renames their exprs *)
        (List.fold_left (fun (env_acc, binding_acc) (bind, b_exp, bind_tag) -> 
          match bind with
            | BNameTyped(b_name, typ, b, t) ->
            (* Generates the new name *)
            (let new_name: string = if (is_runtime b_name) then b_name else (sprintf "%s#%d" b_name t) in
              (* Accumulates env *)
              ((b_name, new_name)::env_acc,
                (* Adds this binding to the previous ones *)
                binding_acc @ [(BNameTyped(new_name, typ, b, t), (rename_expr env b_exp), bind_tag)]))
            | _ -> (env_acc, binding_acc @ [(bind, (rename_expr env b_exp), bind_tag)])
        ) (env, []) binds)
      in ELet (new_bindings, (rename_expr new_env body), tag)
    (* Pretty trivial recursive cases *)
    | EPrim1 (prim, exp, tag) -> EPrim1 (prim, (rename_expr env exp), tag)
    | EPrim2 (prim, l_exp, r_exp, tag) -> EPrim2 (prim, (rename_expr env l_exp), (rename_expr env r_exp), tag)
    | EIf (pred, then_exp, else_exp, tag) -> EIf ((rename_expr env pred), (rename_expr env then_exp), (rename_expr env else_exp), tag)
    (* Base case, just returns a num *)
    | ENumber (num, tag) -> ENumber (num, tag)
    | EBool (value, tag) -> EBool(value, tag)
    | EApp (f_obj, arg_names, call_type, tag) ->
      let renamed_f_obj =  if call_type = Native then f_obj else rename_expr env f_obj in
      let renamed_args = (List.map (fun arg -> (rename_expr env arg)) arg_names)
      in EApp (renamed_f_obj, renamed_args, call_type, tag)
    | ESeq (a, b, t) -> ESeq(rename_expr env a, rename_expr env b, t)
    | ETuple(exprs, t) -> ETuple(List.map (rename_expr env) exprs, t)
    | EGetItem(a, b, t) -> EGetItem(rename_expr env a, rename_expr env b, t)
    | ESetItem(a, b, c, t) -> ESetItem(rename_expr env a, rename_expr env b, rename_expr env c, t)
    | ENil(t) -> ENil(t)
    | ELambda (binds, typ, body, t) -> 
        let (new_env, new_args) = 
          List.fold_left (fun (env_acc, arg_acc) bind -> 
            match bind with
              | BNameTyped(b_name, typ, b, t) ->
                let new_arg_name = sprintf "%s#%d" b_name t in
                ((b_name, new_arg_name)::env_acc, arg_acc @ [BNameTyped(new_arg_name, typ, b, t)])
              | _ -> (env_acc, bind::arg_acc)
          ) (env, []) binds in
        ELambda(new_args, typ, rename_expr new_env body, t)
    | ELetRec (binds, body, tag) -> 
      let (new_env, new_bindings) = 
        (* On the first pass, only rename the binding names and accumulate those.
           This is done since they are allowed to refer back to one another in either direction *)
        let (env_acc, binding_acc) = 
          List.fold_left 
            (fun (env_acc, binding_acc) (bind, b_exp, bind_tag) -> 
              match bind with
              | BNameTyped(b_name, typ, b, t) ->
                  let new_name = if (is_runtime b_name) then b_name else (sprintf "%s#%d" b_name t) in
                  let updated_env = (b_name, new_name) :: env_acc in
                  (* Accumulate the binding with the new name but without renaming exprs yet *)
                  (updated_env, binding_acc @ [(BNameTyped(new_name, typ, b, t), b_exp, bind_tag)])
              (* We shouldn't really get here I think, maybe we throw instead? *)
              | _ -> (env_acc, binding_acc @ [(bind, b_exp, bind_tag)]))
            (env, []) 
            binds
        in
        (* On the second pass rename the expressions for all bindings using environment
           with access to all other binding names *)
        let renamed_bindings = List.map 
          (fun (bind, b_exp, bind_tag) -> (bind, rename_expr env_acc b_exp, bind_tag))
          binding_acc
        in
        (env_acc, renamed_bindings)
      in 
      (* Rename the body of the let rec using the final environment *)
      ELetRec (new_bindings, rename_expr new_env body, tag)
    | EConstructor(name, args, t) -> EConstructor(name, List.map (rename_expr env) args, t)
    | EMatch(e, pe_l, t) -> 
        let renamed_pe_l = List.map (fun (p, e) ->
          let (new_env, renamed_pattern) = rename_pattern env p in
          (renamed_pattern, (rename_expr new_env e))
        ) pe_l in
        EMatch(rename_expr env e, renamed_pe_l, t)
  and rename_pattern (env: (string * string) list) (p: tag pattern): ((string * string) list * tag pattern) =
    match p with
    | PBlank _ | PLiteral _ -> (env, p)
    | PId(name, t) ->
        let new_name = sprintf "%s#%d" name t in
        ((name, new_name)::env, PId(new_name, t))
    | PConstructor(name, args, t) ->
        let (new_env, renamed_args) = List.fold_right (fun p (env_acc, args_acc) -> 
          let (new_env, new_p) = rename_pattern env_acc p in
          (new_env, new_p::args_acc)
        ) args (env, []) in
        (new_env, PConstructor(name, renamed_args, t))
    | PTup(pl, t) ->
        let (new_env, renamed_pl) = List.fold_right (fun p (env_acc, pl_acc) -> 
          let (new_env, new_p) = rename_pattern env_acc p in
          (new_env, new_p::pl_acc)
        ) pl (env, []) in
        (new_env, PTup(renamed_pl, t))
  in
match p with
| Program (tdef, decls, expr, t) -> 
  match decls with 
  | [] -> Program (tdef, decls, (rename_expr [] expr), t)
  | _ -> raise (InternalCompilerError("Desugaring invariant should lead to no decls in renaming"))
;;
