open Exprs
open Errors
open Phases
open Utils

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  (* wf_E checks if a given expersion is well formed, accumulating a list of errors we encounter
    Params:
     e is our expr that we are checking for errors
     env is the environment we are in
     loe is the current errors in our environment, we add errors encountered onto this list
  *)
  let rec wf_E (e : sourcespan expr) (env: sourcespan bind list) (loe : exn list) : exn list =
    let sub_wf_E sub_e = (wf_E sub_e env []) in 
    match e with
    | ETuple (exprs, loc) -> List.fold_left (fun acc_loe cur_expr -> acc_loe @ (sub_wf_E cur_expr)) loe exprs   
    | EGetItem (e, idx_e, _) -> loe @ (sub_wf_E e) @ (sub_wf_E idx_e) 
    | ESetItem (e, idx_e, newval_e, _) -> loe @ (sub_wf_E e) @ (sub_wf_E idx_e) @ (sub_wf_E newval_e)
    | EBool _ -> loe
    | ENil _ -> loe
    | ENumber (n, loc) -> 
      (* we can check if any of the numbers provided are outside [min, max] values *)
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
        loe @ [(Overflow (n, loc))]
      else
        loe
    | EId (x, loc) -> (
      let x_res_opt = (find_bind_opt env x) in 
      match x_res_opt with
      | None -> if (is_runtime x) then loe else loe @ [(UnboundId (x, loc))]
      | Some x_res -> loe)
    | EPrim1 (_, e, _) -> loe @ (sub_wf_E e)
    | EPrim2 (_, l, r, _) -> loe @ (sub_wf_E l) @ (sub_wf_E r)
    | EIf (c, t, f, _) -> loe @ (sub_wf_E c) @ (sub_wf_E t) @ (sub_wf_E f)
    | EApp(exp, args, call_typ, loc) -> 
      (* Application issues are now runtime issues  *)
      loe 
      (* we should check only if its not a runtime application argument *)
      @ (sub_wf_E exp)
      @ (List.flatten (List.map (fun arg -> (sub_wf_E arg)) args))
    | ELet (binds, body, _) -> 
      let env2, _, loe_bindings = List.fold_left
      (fun (scope_env, shadow_env, loe_bindings) (bind, e, _) ->
        match bind with
        | BBlank _ -> (scope_env, shadow_env, loe_bindings)
        | BNameTyped(x, typ, t, loc) ->
          let existing_opt = List.assoc_opt x shadow_env in
          let binding_errrors = 
            (match existing_opt with
            | Some existing -> (loe_bindings
                             @ [(DuplicateId (x, loc, existing))]
                             @ (wf_E e scope_env []))
            | None -> (wf_E e scope_env loe_bindings)) 
          in
          (BNameTyped(x, typ, t, loc) :: scope_env, (x, loc) :: shadow_env, binding_errrors)
        | BTuple (binds, loc) ->
          let rec process_tuple_bindings binds scope_env shadow_env loe_bindings =
            match binds with
            | [] -> (scope_env, shadow_env, loe_bindings)
            | bind :: rest ->
              match bind with
              | BBlank _ -> process_tuple_bindings rest scope_env shadow_env loe_bindings
              | BNameTyped(x, typ, t, loc) ->
                let existing_opt = List.assoc_opt x shadow_env in
                let binding_errors =
                  match existing_opt with
                  | Some existing -> loe_bindings @ [(DuplicateId (x, loc, existing))]
                  | None -> loe_bindings
                in
                process_tuple_bindings rest (BNameTyped(x, typ, t, loc) :: scope_env) ((x, loc) :: shadow_env) binding_errors
              | BTuple (nested_binds, nested_loc) ->
                process_tuple_bindings (nested_binds @ rest) scope_env shadow_env loe_bindings
          in
          process_tuple_bindings binds scope_env shadow_env loe_bindings
      )
      (env, [], loe) 
      binds
      in
      wf_E body env2 loe_bindings
    | ESeq (a, b, _) -> loe @ (wf_E a env []) @ (wf_E b env [])
    | ELambda (bind_list, _, body_expr, tag) -> 
      (* Checks the bindings for duplicates *)
      let rec check_binds (binds : 'a bind list) (shadow_env: 'a bind list) loe_bindings = 
        (match binds with
        | [] -> (shadow_env, loe_bindings)
        | bind :: rest ->
          match bind with
          | BBlank _ -> check_binds rest shadow_env loe_bindings
          | BNameTyped (x, typ, t, loc) ->
            let existing_opt = find_bind_opt shadow_env x in
            let binding_errors =
              match existing_opt with
              | Some existing -> loe_bindings @ [(DuplicateId (x, loc, existing))]
              | None -> loe_bindings
            in
            check_binds rest (bind :: shadow_env) binding_errors
          | BTuple (nested_binds, _) -> check_binds (nested_binds @ rest) shadow_env loe_bindings)
      in
        let (post_bind_env, post_bind_errors) = (check_binds bind_list [] loe) in 
          (wf_E body_expr (post_bind_env @ env) post_bind_errors)
    | ELetRec (binding_list, body, tag) -> 
      let rec check_bindings (bindings: 'a binding list) new_env loe_bindings : exn list =
        (match bindings with
        | [] -> loe_bindings
        | binding :: rest -> 
          (match binding with
          | (BNameTyped (x, typ, t, loc), bind_expr, _) -> 
            (* new well-formedness error for let rec declarations whose right hand sides are not all lambda expressions. *)
            let binding_errors = 
              (match bind_expr with 
                | ELambda (bind_list, typ, body_expr, tag) -> (wf_E bind_expr new_env [])
                | _ -> [(LetRecNonFunction (BNameTyped (x, typ, t, loc), tag))])
            in (check_bindings rest new_env (loe_bindings @ binding_errors))
                    (* let rec expressions is restricted to only permit binding names to values; 
              it does not permit the fancier tuple bindings or underscore bindings tht we allow elsewhere *)
          | _ -> raise (InternalCompilerError "LetRec bindings only support names, parser should not let us get here")))
      (* collect all the bindings and duplicate binding errors along the way *)
      and collect_letrec_bindings (bindings: 'a binding list) : (('a bind list) * (exn list)) =
        (match bindings with
        | [] -> ([], [])
        | binding :: rest -> 
          (match binding with
          | (BNameTyped (x, typ, t, loc), bind_expr, _) -> 
            let rest_bindings, rest_loe_dup = (collect_letrec_bindings rest) in 
            (match (find_bind_opt rest_bindings x) with
            | Some existing -> ((BNameTyped (x, typ, t, loc) :: rest_bindings), (DuplicateId (x, loc, existing)) :: rest_loe_dup)
            | None -> ((BNameTyped (x, typ, t, loc) :: rest_bindings), rest_loe_dup))
          | _ -> raise (InternalCompilerError "LetRec bindings only support names, parser should not let us get here")))
      in 
        let (new_binding_env, loe_dup_binds) = (collect_letrec_bindings binding_list) in
        let binding_errs = (check_bindings binding_list (new_binding_env @ env) loe_dup_binds) in 
        let body_errs = (wf_E body (new_binding_env @ env) []) in
        binding_errs @ body_errs
    | EConstructor (_, sub_exprs, _) -> 
      List.fold_left (fun acc_loe cur_expr -> acc_loe @ (sub_wf_E cur_expr)) loe sub_exprs
    | EMatch (e, branches, tag) ->
      (* accumulate the errors associated through duplicate ids in this pattern and the new bindings we need to add to the env for the sub branch *)
      let rec process_pattern (pat : sourcespan pattern) (env : sourcespan bind list) (loe : exn list) : (sourcespan bind list * exn list) =
        (* god idk why i made this take in an loe ^.___. ^ *)
      match pat with
      | PBlank _ -> (env, loe)
      | PId (x, loc) ->
        (* check if this already exists *)
        let existing_opt = List.assoc_opt x (List.filter_map (function
          | BNameTyped (name, _, _, loc) -> Some (name, loc)
          | _ -> None) env) in
        let binding_errors =
        match existing_opt with
        | Some existing -> loe @ [DuplicateId (x, loc, existing)]
        | None -> loe
        in
        (* and add it to the environment either way *)
        (BNameTyped (x, TInt loc, false, loc) :: env, binding_errors)
      | PTup (patterns, _) ->
        (* to the left now yall *)
        List.fold_left
        (fun (acc_env, acc_loe) sub_pat ->
          let (new_env, new_loe) = process_pattern sub_pat acc_env acc_loe in
          (new_env, acc_loe @ new_loe))
        (env, loe)
        patterns
        (* one hop this time *)
      | PLiteral _ -> (env, loe)
      | PConstructor (_, sub_patterns, _) ->
        (* to the left *again* now yall *)
        List.fold_left
        (fun (acc_env, acc_loe) sub_pat ->
          let (new_env, new_loe) = process_pattern sub_pat acc_env acc_loe in
          (new_env, acc_loe @ new_loe))
        (env, loe)
        sub_patterns
      in
      (* now cris-cross *)
      let process_branch (pat, branch_expr) (acc_loe : exn list) =
        let (new_env, pattern_loe) = process_pattern pat [] [] in
        let branch_loe = wf_E branch_expr (new_env @ env) [] in
        acc_loe @ pattern_loe @ branch_loe
      in
      let match_loe = sub_wf_E e in
      (List.fold_left
      (fun acc_loe (pat, branch_expr) -> process_branch (pat, branch_expr) acc_loe)
      match_loe
      branches) @ loe (* i may be turning loe one too many times im so cooked rn loeloeloeloleoleololololloeloel *)

  (* wf_D checks if a given decleration is well formed, checking that in the given seen declerations, 
    one of the same name has not been seen, and that the declarations don't have arguments of duplicate names
    Params:
     d is our declartion that we are checking for errors
     loe is the current errors in our environment, we add errors encountered onto this list
     seen_decl is a map of previously seen declarations (key is name, value is seen functions with that name)
     in_scope_decls : other declerations in scope (typically those seen before and those mutually recursive with 'and')
     TODO: Clean this up a little, its brutally written  (* perhaps a future assignment :( *)
  *)
  and wf_D d (loe : exn list) (seen_decls : (string * sourcespan decl) list) (in_scope_decls : sourcespan bind list) : exn list =
    let rec find_dup_named_args (arg_name: string) (remaining_args: sourcespan bind list) : sourcespan option =
      match remaining_args with
        | [] -> None
        | BNameTyped(f_name, _, _, f_loc)::rest -> if (String.equal f_name arg_name) then Some f_loc else find_dup_named_args arg_name rest
        (* todo fix other bug here relating to not finding duplicates in nested tuples *)
        | _::rest -> find_dup_named_args arg_name rest
    in let rec find_all_dup_args (args: sourcespan bind list) : (string * sourcespan * sourcespan) list =
      match args with
        | [] -> []
        | BNameTyped(f_name, _, _, f_loc)::rest -> 
          (let dup_opt = find_dup_named_args f_name rest in
            (match dup_opt with
              | None -> []
              | Some x -> [(f_name, f_loc, x)]) 
            @ (find_all_dup_args rest))
            (* same above here for find dup named with looking at tuples *)
        | _::rest -> find_all_dup_args rest
    in match d with
    | DFun (name, args, typ, body, loc) -> 
        let loe' = 
          let duplicates = List.filter (fun (n, _) -> n = name) seen_decls in
          (* for now: if we have a(x): blah, a(y): blah, a(z) blah ... this creates 1 error when reaching a(y) and 2 when reaching a(z) *)
          let new_loe = List.fold_left (fun acc (_, DFun (_, _, _, _, existing_loc)) -> acc @ [DuplicateFun(name, loc, existing_loc)]) loe duplicates in
          let args_loe = List.map (fun (name, l1, l2) -> DuplicateId(name, l1, l2)) (find_all_dup_args args) in
          new_loe @ args_loe
        in
        wf_E body (in_scope_decls @ args) loe'
      in
  match p with
  | Program (_, decls, body, _) ->
    let (decl_loe, seen_decls) =
    List.fold_left
    (fun (cur_decl_loe, seen_decls) sublist ->
      (* so within this subgroup, they can be mutually recursive so lets get all those declerations as names *)
      (* wow this is so horibly done im sorry *)
      let seen_decl_env_values = (List.map (function (a, b) -> b) seen_decls) in
      (* since we don't type check it doesn't matter what our type is here, this might change to pretty print type info in non well formed programs... *)
      let in_scope_decls = (List.map (function DFun (name, _, _, _, loc) -> BNameTyped (name, TInt dummy_span, false, loc)) (sublist @ seen_decl_env_values)) in
      List.fold_left
      (fun (inner_decl_loe, inner_seen_decls) current_decl ->
        let new_decl_loe = wf_D current_decl inner_decl_loe inner_seen_decls in_scope_decls in
        (new_decl_loe, match current_decl with DFun(name, _, _, _, _) -> (name, current_decl) :: inner_seen_decls))
      (cur_decl_loe, seen_decls)
      sublist)
    ([], [])
    decls
  in
    (* repeated code that could be avoided; hardly know her *)
    let seen_decl_env_values = (List.map (function (a, b) -> b) seen_decls) in
    (* all of these will get desugared to let rec lambda applications anyways *)
    let body_scope_decls = (List.map (function DFun (name, _, _, _, loc) -> BNameTyped (name, TInt dummy_span, false, loc)) seen_decl_env_values) in
    let total_loe = wf_E body body_scope_decls decl_loe in 
    if List.length total_loe = 0 then (Ok p) else (Error total_loe)
  ;;
