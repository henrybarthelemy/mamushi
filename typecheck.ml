open Exprs
open Errors
open Phases
open Utils
open Printf
open Pretty


(* Turns an 'a decl into an 'a function type *)
let determine_function_type (d : 'a decl) : 'a typ =
  let convert_single_bind bind = 
    match bind with 
    | BNameTyped (_, typ, _, _) -> typ
  in
  match d with 
  | DFun (str, bl, rt, body, loc) ->
    let in_typ = 
    (match bl with 
    | [] -> TProduct([], loc)
    | [sb] -> (convert_single_bind sb)
    | binds -> TProduct((List.map (fun b -> (convert_single_bind b)) binds), loc))
    in
    TFunction(in_typ, rt, loc)
;;

(* Untags an environment *)
let rec untag_tenv (tenv : 'a typ envt) : unit typ envt =
  match tenv with 
  | [] -> []
  | (str, atyp) :: rest -> (str, untagT atyp) :: (untag_tenv rest)
;;

(* collects the list of decls into a function environment *)
let rec collect_def_type_env (decls : 'a decl list) : sourcespan typ envt =
  match decls with 
  | [] -> []
  | d :: rod -> 
    match d with 
    | DFun (str, _, _, _, _) ->
      (str, (determine_function_type d)) :: (collect_def_type_env rod)
;;

(* Collects bindings from the expression provided recuring if needed *)
let rec collect_bindings (e : sourcespan expr) : sourcespan bind list =
  match e with
  | ELet (bindings, body, _)
  | ELetRec (bindings, body, _) ->
      let current_bindings = List.map (fun (bind, _, _) -> bind) bindings in
      current_bindings @ collect_bindings body
  | ELambda (bind_list, typ, body, _) ->
      bind_list @ collect_bindings body
  | ESeq (e1, e2, _) ->
      collect_bindings e1 @ collect_bindings e2
  | EIf (cond, then_branch, else_branch, _) ->
      collect_bindings cond @ collect_bindings then_branch @ collect_bindings else_branch
  | EMatch (e, branches, _) ->
      let branch_bindings = List.flatten (List.map (fun (_, branch_expr) -> collect_bindings branch_expr) branches) in
      collect_bindings e @ branch_bindings
  | EPrim1 (_, e, _) -> collect_bindings e
  | EPrim2 (_, e1, e2, _) -> collect_bindings e1 @ collect_bindings e2
  | ETuple (exprs, _) -> List.flatten (List.map collect_bindings exprs)
  | EGetItem (e1, e2, _) -> collect_bindings e1 @ collect_bindings e2
  | ESetItem (e1, e2, e3, _) -> collect_bindings e1 @ collect_bindings e2 @ collect_bindings e3
  | EApp (func, args, _, _) -> collect_bindings func @ List.flatten (List.map collect_bindings args)
  | EId _ | EBool _ | ENil _ | ENumber _ -> []
  | EConstructor (_, exprs, _) ->
      List.flatten (List.map collect_bindings exprs)
(* collapses the binds to a type environment *)
and colapse_to_tenv binds : sourcespan typ envt = 
  (match binds with 
  | [] -> []
  | bind :: rob -> 
    (match bind with 
      | BNameTyped (name, typ, _, _) -> [(name, typ)] @ (colapse_to_tenv rob)
      | BTuple (blist, _) -> (colapse_to_tenv binds) @ (colapse_to_tenv rob)
      | _ -> []))
(* collects all the types in the expression making a type environment that results from it *)
and collect_type_env (e : sourcespan expr) : sourcespan typ envt = 
  let expr_bindings = collect_bindings e in 
  (colapse_to_tenv expr_bindings)
;;

(* Collects all the IDs in a typ, useful for well formed type checking *)
let rec collect_type_ids (typ : sourcespan typ) : (string * sourcespan) list =
  match typ with
  | TId (id, loc) -> [(id, loc)]
  | TFunction (tin, tout, _) -> collect_type_ids tin @ collect_type_ids tout
  | TProduct (tlist, _) -> List.flatten (List.map collect_type_ids tlist)
  | TAlgebric (constructors, _) -> List.flatten (List.map (fun (_, t) -> collect_type_ids t) constructors)
  | TInt _ | TBool _ -> [] 
;;

(* Collects all constructor names and maps them to their associated TAlgebric types *)
let rec collect_constructors_env (tdecls : sourcespan type_decl list) : sourcespan typ envt =
  match tdecls with
  | [] -> []
  | DType(_, TAlgebric(constructors, loc), _) :: rest ->
      let constructor_mappings = List.map (fun (cname, _) -> (cname, TAlgebric(constructors, loc))) constructors in
      constructor_mappings @ collect_constructors_env rest
  | _ :: rest -> collect_constructors_env rest
;;

(* Is the program well typed? *)
let is_well_typed (p : sourcespan program) : sourcespan program fallible =
  (* returns none if a tdecl with that name isn't found, otherwise returns that tdecl *)
  let rec get_name_opt (tdecls : sourcespan type_decl list) (name : string) : sourcespan type_decl option = 
    match tdecls with
    | [] -> None
    | tdec :: rest -> 
      match tdec with | DType(id, _, loc) -> if id = name then Some tdec else (get_name_opt rest name)
  in
  (* Get the type from the program (by looking through type decls) declared with the name provided *)
  let get_typ_from_prog (name : string) =
    match p with 
    | Program (tdecls, _, _, _) -> 
      (match (get_name_opt tdecls name) with
      | Some tdec -> (match tdec with | DType (_, typ, _) -> Some typ)
      | None -> None)
  in
  (* Handles checking for duplicate type id naming in the declarations *)
  let rec duplicate_id (tdecls : sourcespan type_decl list) (seen_tdecs : sourcespan type_decl list) : exn list =
  match tdecls with 
  | [] -> []
  | tdec :: rest -> 
    (match tdec with 
    | DType(name, _, loc) -> 
      (match (get_name_opt seen_tdecs name) with
      | Some (DType(name, _, first_loc)) -> (DuplicateTypeId (name, loc, first_loc)) :: (duplicate_id rest (tdec :: seen_tdecs))
      | None -> duplicate_id rest (tdec :: seen_tdecs)))
  in
  (* Handles checking for constructor duplicate constructor names *)
  let rec duplicate_constructor_names (tdecls : sourcespan type_decl list) : exn list =
    match tdecls with 
    | [] -> []
    | tdec :: rest -> 
      let rest_err = duplicate_constructor_names rest in
      (match tdec with 
      | DType(name, typ, loc) -> 
        (* checks a specific type for multiple constructors in a algebric type having the same name *)
        (match typ with 
        | TAlgebric (constructors, t) -> 
          let (names, _) = (List.split constructors) in
          (match (unique names) with 
          | None -> []
          | Some cname -> [DuplicateConstructorNames (cname, loc)])
        | _ -> [])) @ rest_err
  in
  (* Makes sure that every type used in the expression exists as a defined type *)
  let rec undefined_type_check (tdecls : sourcespan type_decl list) (e : sourcespan expr) : exn list =
    let binds = collect_bindings e in
    undefined_types_in_binds_check tdecls binds
  and undefined_types_in_binds_check tdecls binds = 
    match binds with
    | [] -> []
    | bind :: rob -> 
      let rob_errs = (undefined_types_in_binds_check tdecls rob) in
      (match bind with 
      | BNameTyped (_, typ, _, _) -> (check_type_for_undefined typ tdecls)
      | BTuple (blist, _) -> (undefined_types_in_binds_check tdecls blist) 
      | _ -> []) @ rob_errs
  and check_type_for_undefined typ tdecls = 
    let ids = collect_type_ids typ in 
    (List.fold_left (fun acc (id, loc) ->
      (match get_name_opt tdecls id with
      | None -> (UndefinedType (id, loc)) :: acc
      | Some _ -> acc)) 
      [] 
      ids)
  in
  (* Infers the type of the expression provided under the given environment *)
  (* We assume every variable is correctly bounded in this environment *)
  let rec infer_type_with (tenv : 'a typ envt) (e : 'a expr) : 'a typ = 
    match e with 
    | EId (str, loc) -> 
      (match (find_opt tenv str) with 
        | Some typ -> typ
        | None -> (raise (InternalCompilerError (sprintf "Was unable to find %s in the environment during type checking of expression %s" str (string_of_expr e))))) 
    | ENumber (_, loc) -> TInt loc
    | EBool (_, loc) -> TBool loc
    | ELambda (binds, return_typ, body, loc) ->
      let rec gather_tuple_typ (blist:'a Exprs.bind list) =
        TProduct (List.map (fun b -> 
        match b with 
        | BNameTyped (_, typ, _, _) -> typ
        | BTuple (nested_blist, _) -> gather_tuple_typ nested_blist
        (* | BBlank _ -> TBlank () *)
        | _ -> failwith "gotta figure this bs out") blist, loc) 
      in
      TFunction ((gather_tuple_typ binds), return_typ, loc)
    | EIf (_, then_branch, _, _) ->
      (infer_type_with tenv then_branch)
    | EPrim1 (op, e, loc) ->
      (match op with 
      | Not -> (TBool loc)
      | Add1 | Sub1 -> (TInt loc))
    | EPrim2 (op, e1, e2, loc) ->
      (match op with 
      | And | Or | Eq -> (TBool loc)
      | Plus | Minus | Times | Greater | GreaterEq | Less | LessEq -> (TInt loc))
    | ETuple (elist, loc) ->
      let typs = List.map (fun expr -> (infer_type_with tenv expr)) elist in
      TProduct(typs, loc)
    | EConstructor (cname, _, loc) ->
      let algebric = (find_opt tenv cname) in
      (match algebric with
        (* We only really want the overall algebric type not the constructor *)
        | Some TAlgebric (constructors, loc) -> TAlgebric (constructors, loc)
        (* Only run type inference if things are well defined or this blows up *)
        | _ -> raise (InternalCompilerError "No consturctor found"))
    | EMatch (mexp, branches, loc) -> 
      (match branches with  
      | [] -> raise (InternalCompilerError "ParserInvariant: There should be more than one branch in a match expression")
      | (pattern, expr) :: rest -> 
        (infer_type_with ((pattern_to_tenv tenv (infer_type_with tenv mexp) pattern) @ tenv) expr))
    | ELet (bindings, expr, loc) ->
      (* Add each binding to the environment *)
      let rec check_bindings tenv bindings : 'a typ envt = 
      (match bindings with
      | [] -> tenv
      | (bind, b_exp, bind_tag) :: rob -> 
        let rec check_bind tenv bind : 'a typ envt = 
          (match bind with 
          | BNameTyped (name, typ, _, _) -> 
            let new_tenv = ((name, typ) :: tenv) in 
            (check_bindings new_tenv rob) 
          | BTuple (blist, tag) -> 
            let new_tenv = List.fold_right
              (fun b acc_tenv -> check_bind acc_tenv b)
              blist
              tenv
            in
            (check_bindings new_tenv rob)
          | _ -> tenv) in (check_bind tenv bind))
        in 
      let e_tenv = (check_bindings tenv bindings) in 
      (infer_type_with e_tenv expr)
    | ELetRec (bindings, expr, loc) ->
      (* Add each binding to the environment *)
      let rec add_bindings tenv bindings : 'a typ envt = 
      (match bindings with
      | [] -> tenv
      | (bind, b_exp, bind_tag) :: rob -> 
        let rec add_bind tenv bind : 'a typ envt = 
          (match bind with 
          | BNameTyped (name, typ, _, _) -> 
            let new_tenv = ((name, typ) :: tenv) in 
            (add_bindings new_tenv rob) 
          | _ -> tenv) in 
          (add_bind tenv bind))
        in 
      let e_tenv = (add_bindings tenv bindings) in 
      (infer_type_with e_tenv expr)
    | EApp (func, args, rt, loc) ->  
      (match func with
        | ELambda (binds, return_typ, body, loc) -> return_typ
        | EId (name, loc) -> 
          let rec get_func_type from_name = 
            (match (find_opt tenv from_name) with 
              | Some v -> 
                (match v with 
                  | TId (name, _) -> get_func_type name
                  | _ -> v)
              | None -> 
                raise (InternalCompilerError (sprintf "Unable to find function %s in the type environment " name)))
          in
          (match (get_func_type name) with
          | TFunction (_, tout, _) -> tout
          | typ -> typ
          | _ -> raise (InternalCompilerError (sprintf "Unable to find function %s in the type environment " name))))
    | ESeq (_, e2, _) ->
      (infer_type_with tenv e2)
    | EGetItem (tup, idx, a) ->
      let nidx = match idx with 
      | ENumber (num, _) -> num
      | _ -> (raise (InternalCompilerError "Parser Invariant broken : tup idx should be number")) in
      (match (infer_type_with tenv tup) with
      | TProduct (styps, _) -> 
        if Int64.to_int nidx < List.length styps && Int64.to_int nidx >= 0 then
          List.nth styps (Int64.to_int nidx)
        else
          TInt a (* dummy value, this tuple access will error out prior *)
      | _ -> TInt a )
    | ESetItem (_, _, item, _) -> 
      (infer_type_with tenv item)
    | ENil _ -> (raise (InternalCompilerError "Parser Invariant broken: NIL should never exist"))
  (* We need to update the tenv for the pattern given the type of the expression we are matching against *)
  and pattern_to_tenv (tenv : 'a typ envt) (mtyp : 'a typ) (pattern : 'a pattern) : 'a typ envt = 
    (match pattern with 
    | PBlank _ -> 
      (* In this case nothing really gets added to our environment *)
      []
    | PId (x, loc) -> 
      (* In this case whatever the match expression needs to be added as a type *)
      [(x, mtyp)]
    | PTup (patterns, _) ->
      (match mtyp with
      | TProduct (subtypes, _) ->
      if List.length patterns = List.length subtypes then
        List.flatten (List.map2 (fun pattern subtype -> pattern_to_tenv tenv subtype (pattern)) patterns subtypes)
      else
        []
      | _ -> [])
    | PLiteral _ -> []
    | PConstructor (cname, patterns, _) -> 
      (match mtyp with 
      | TAlgebric(constructors, _) -> 
        let typ = (find_opt constructors cname) in 
        (match typ with 
        | Some TProduct(subtypes, _) ->
          if List.length patterns = List.length subtypes then
            List.flatten (List.map2 (fun pattern subtype -> pattern_to_tenv tenv subtype (pattern)) patterns subtypes)
          else 
            []
        | Some subtype -> 
          (match patterns with 
          | [pattern] -> pattern_to_tenv tenv subtype pattern
          | _ -> [])
        | _ -> [])        
      | _ -> [])
    )
  in 
  (* Checkes that the provided expression is the expected_typ in the context of this typing environment *)
  (* Params: 
        @ tenv : maps the identifiers in the expression to their respective types 
        @ e : the expression we are type checking 
        @ expected_typ : the expected type of the expression e *)
  let rec check_type_with (tenv : sourcespan typ envt) (e : sourcespan expr) (expected_typ : unit typ) : exn list = 
    let e_typ = (infer_type_with tenv e) in 
    let rec compare_types (actual_typ: sourcespan typ) (expected_typ : unit typ) : exn list =
      (match (actual_typ, expected_typ) with
      (* Same types, terminal *)
      | (_, TId(dec, loc)) ->
        (match (get_typ_from_prog dec) with
        | Some etyp -> (check_type_with tenv e (untagT etyp))
        | None -> [TypeMismatch (untagT actual_typ, expected_typ, dummy_span)])
      | (TInt l1, TInt ())
      | (TBool l1, TBool ()) -> []
      (* Same types, need to recur *)
      | (TFunction (tin, tout, _)), (TFunction (tin2, tout2, _)) ->
        (compare_types tin tin2) @ (compare_types tout tout2)
      | (TFunction (TProduct ([], _), tout, _)), _ -> 
        (compare_types tout expected_typ)
      | _, (TFunction (TProduct ([], _), tout, _)) -> 
        (compare_types actual_typ tout)
      | TProduct (tlist, loc), TProduct (tlist2, _) ->
        (if ((List.length tlist) == (List.length tlist2)) 
        then List.flatten (List.map2 (fun t1 t2 -> compare_types t1 t2) tlist tlist2)
        else [TypeMismatch (untagT actual_typ, expected_typ, loc)])
      | (TAlgebric (constructors, loc), TAlgebric (constructors2, _)) ->
        if (List.length constructors == List.length constructors2)
        then 
            (if (List.for_all2 (fun (name1, _) (name2, _) -> (name1 = name2)) constructors constructors2)
            then []
            else [TypeMismatch (untagT actual_typ, expected_typ, loc)])
          else []
      | TProduct (st::[], _), _ -> 
        (compare_types st expected_typ)
      | _, TProduct (st::[], _) ->
        (compare_types actual_typ st)
      | (TBool loc, _)
      | (TInt loc, _) 
      | (TFunction (_, _, loc), _)
      | (TProduct (_, loc), _)
      | (TAlgebric (_, loc), _) -> [TypeMismatch (untagT actual_typ, expected_typ, loc)]
      | _ -> [] (* uncomment below to see what were missing *)
      | (x, y) -> raise (InternalCompilerError (sprintf "Reached %s vs %s and didn't have a case for it" 
                        (string_of_type actual_typ) (string_of_type expected_typ))))
    in 
    (compare_types e_typ expected_typ)
  in 
  (* Checks types for tuple accesses *)
  let check_type_tuple_access (tenv : sourcespan typ envt) (idx : sourcespan expr) (tup : sourcespan expr) : exn list = 
    let (num, num_loc) = (match idx with 
    | ENumber(num, loc) -> (num, loc)
    | _ -> raise (InternalCompilerError "Did not expect a non-number to make it past the parser"))
    in 
    (match tup with
      | EId(name, l) -> 
        let rec get_func_type from_name = 
          (match (find_opt tenv from_name) with 
            | Some v -> 
              (match v with 
                | TId (name, _) -> get_func_type name
                | _ -> v)
            | None -> 
              raise (InternalCompilerError "A variable introduced was expected to be in the type environment but it wasn't"))
        in 
        let tup_typ = (get_func_type name) in 
        (match tup_typ with 
        | TProduct (tlist, loc) ->  if ((num < (Int64.of_int (List.length tlist))) && (num > 0L)) then [] else [IndexOutOfBounds(Int64.to_int num, List.length tlist, num_loc)]
        | _ -> [NotATuple num_loc](* expected tuple error *) )
      | ETuple(exprs, l) -> if ((num < (Int64.of_int (List.length exprs))) && (num > 0L)) then [] else [IndexOutOfBounds(Int64.to_int num, List.length exprs, num_loc)]
      | _ -> [NotATuple num_loc])
  in
  let rec type_check_decls (d : sourcespan decl list list) (tenv : sourcespan typ envt) : exn list =
    let rec add_bindings tenv bindings : 'a typ envt = 
      (match bindings with
      | [] -> tenv
      | bind :: rob -> 
        let rec add_bind tenv bind : 'a typ envt = 
          (match bind with 
          | BNameTyped (name, typ, _, _) -> 
            let new_tenv = ((name, typ) :: tenv) in 
            (add_bindings new_tenv rob) 
          | _ -> tenv) in 
          (add_bind tenv bind))
    in 
    match d with
    | [] -> []
    | decl_group :: rest ->
      let rec check_decl_group decl_group new_env =
        let group_tenv = collect_def_type_env decl_group @ tenv in
        List.flatten 
          (List.map 
          (fun decl -> 
            (match decl with
            | DFun (_, binds, rt, body, _) ->
              let fenv = add_bindings group_tenv binds in
              (
                (check_type_with fenv body (untagT rt)) @ 
                (type_check_expr body fenv)
              ))) 
          decl_group), group_tenv
        in
      let group_errors, new_env = (check_decl_group decl_group tenv) in
      group_errors @ type_check_decls rest new_env

  and type_check_expr (e : sourcespan expr) (tenv : sourcespan typ envt) : exn list = 
    let check_type = (check_type_with tenv) in
    match e with 
    | EPrim2 (prim2, e1, e2, _) -> 
      (match prim2 with 
      | Plus | Minus | Times | Greater | GreaterEq | Less | LessEq  -> (check_type e1 (TInt ())) @ (check_type e2 (TInt ()))
      | And | Or -> (check_type e1 (TBool ())) @ (check_type e2 (TBool ()))
      | Eq -> []) @ (type_check_expr e1 tenv) @ (type_check_expr e2 tenv)
    | EPrim1 (prim1, e, _) ->
      (match prim1 with
      | Not -> (check_type e (TBool ()))
      | Add1 | Sub1 -> (check_type e (TInt ()))) @ (type_check_expr e tenv)
    | ENumber _ -> []
    | EBool _ -> []
    | EId _ -> []
    | ELet (bindings, expr, loc) ->
      (* we need to check that every bind is of the correct type *)
      let rec check_bindings tenv bindings : (exn list * sourcespan typ envt) = 
      (match bindings with
      | [] -> ([], tenv)
      | (bind, b_exp, bind_tag) :: rob -> 
        let rec check_bind tenv bind : (exn list * sourcespan typ envt) = 
          (match bind with 
          | BNameTyped (name, typ, _, _) -> 
            let new_tenv = ((name, typ) :: tenv) in 
            let (rest_err, rest_env) = (check_bindings new_tenv rob) in
            (((check_type_with tenv b_exp (untagT typ))
              @ (type_check_expr b_exp tenv)
            @ rest_err), rest_env) 
          | BTuple (blist, _) -> 
            let rec gather_tuple_typ (blist: Exprs.sourcespan Exprs.bind list) =
              TProduct (List.map (fun b -> 
              match b with 
              | BNameTyped (_, typ, _, _) -> typ
              | BTuple (nested_blist, _) -> gather_tuple_typ nested_blist
              (* | BBlank _ -> TBlank () *)
              | _ -> failwith "gotta figure this bs out") blist, dummy_span) 
            in
            let tuple_typ = (untagT (gather_tuple_typ blist)) in
            let bind_errs = (check_type_with tenv b_exp tuple_typ) in
            let (_, new_tenv) = List.fold_right
              (fun b (acc_errs, acc_tenv) ->
                let (errs, new_tenv) = check_bind acc_tenv b in
                (errs @ acc_errs, new_tenv))
              blist
              ([], tenv)
            in
            let (rest_err, rest_env) = (check_bindings new_tenv rob) in
            (bind_errs @ rest_err, rest_env)
          | _ -> ([], tenv)) in (check_bind tenv bind))
        in 
      let (res, e_tenv) = (check_bindings tenv bindings) in 
      res @ (type_check_expr expr e_tenv)
    | ELetRec (bindings, expr, loc) ->
      (* get all the bindings in this let rec to use in the check_bindings portion *)
      let rec add_bindings tenv bindings : 'a typ envt = 
        (match bindings with
        | [] -> tenv
        | (bind, b_exp, bind_tag) :: rob -> 
          let rec add_bind tenv bind : 'a typ envt = 
            (match bind with 
            | BNameTyped (name, typ, _, _) -> 
              let new_tenv = ((name, typ) :: tenv) in 
              (add_bindings new_tenv rob) 
            | _ -> tenv) in 
            (add_bind tenv bind))
      in 
      let e_tenv = (add_bindings tenv bindings) in 
      (* we need to check that every bind is of the correct type *)
      let rec check_bindings bindings : exn list = 
      (match bindings with
      | [] -> []
      | (bind, b_exp, bind_tag) :: rob -> 
        let rec check_bind bind : (exn list) = 
          (match bind with 
          | BNameTyped (name, typ, _, _) -> 
            let rest_err = (check_bindings rob) in
            (check_type_with e_tenv b_exp (untagT typ))
            @ (type_check_expr b_exp e_tenv)
            @ rest_err
          | _ -> raise (InternalCompilerError "Did not expect to encounter non-bname in let rec")) 
        in (check_bind bind))
      in 
      (check_bindings bindings) @ (type_check_expr expr e_tenv)
    | ESeq (e1, e2, _) -> (type_check_expr e1 tenv) @ (type_check_expr e1 tenv)
    | ETuple (exprs, _) -> 
      List.flatten (List.map (fun e -> (type_check_expr e tenv)) exprs)
    | EGetItem(tup_e, idx_e, _) -> 
      (check_type_tuple_access tenv idx_e tup_e)
      @ (type_check_expr tup_e tenv)
    | ESetItem (e, idx, newval, _) ->
      (check_type idx (TInt ()))
      @ (type_check_expr e tenv)
      @ (type_check_expr idx tenv) (* this will change to an enumber for us to check size *)
    | ELambda (bindings, return_typ, body, loc) ->
      (* We need to (1) add the bindings to the type environment *)
      (* (2) Check that the body has the return type given that new environment *)
      (* (3) Recur to type check the body with the new environment *)
      let new_tenv = (colapse_to_tenv bindings) @ tenv in 
      (check_type_with new_tenv body (untagT return_typ)) @ (type_check_expr body new_tenv)
    | EApp (func, args, _, loc) ->
      (* (1) Check that args match the types provided in func *)
      (* (2) Recur to check that func type checks *)
      (* Gets the type of this function through recuring its lambda *)
      let rec gather_func_type func_expr =
        match func_expr with
        | EId (name, loc) -> 
          let rec get_func_type from_name = 
            (match (find_opt tenv from_name) with 
              | Some v -> 
                (match v with 
                  | TId (name, _) -> get_func_type name
                  | _ -> v)
              | None -> 
                raise (InternalCompilerError "A varibale introduced was expected to be in the type environment but it wasn't"))
          in get_func_type name
        | ELambda (binds, return_typ, body, loc) ->
          (* Need to turn binds + return_typ into a function type *)
          let rec gather_tuple_typ (blist: Exprs.sourcespan Exprs.bind list) =
            TProduct (List.map (fun b -> 
            match b with 
            | BNameTyped (_, typ, _, _) -> typ
            | BTuple (nested_blist, _) -> gather_tuple_typ nested_blist
            (* | BBlank _ -> TBlank () *)
            | _ -> failwith "gotta figure this bs out") blist, loc) 
          in
          TFunction ((gather_tuple_typ binds), return_typ, loc)
        | _ -> raise (InternalCompilerError "Expected to see and ID or lambda but didn't")
      in
      let func_type = (gather_func_type func) in
      (match func_type with
        | TFunction (TProduct (arg_types, _), return_type, loc) ->
          let arg_check_errors =
            (if List.length arg_types = List.length args then
                List.flatten (List.map2 (fun arg typ -> check_type arg (untagT typ)) args arg_types)
            else
                [TypeApplicationArityMismatch (List.length arg_types, List.length args, loc)])
          in
          arg_check_errors
          (* given the order of things the below will error out above when gathering the type.. *)
        | TFunction (typ, return_type, loc) ->
          (match args with 
          | arg :: [] -> (check_type arg (untagT typ))
          | _ -> [TypeApplicationArityMismatch (1, List.length args, loc)])
        | rt -> 
          if (List.length args) == 0 then [] else [(LambdaGivenNonFunction (untagT func_type, loc))]) 
      @ (type_check_expr func tenv) (* recur to the lambda *)
      @ List.flatten (List.map (fun e -> (type_check_expr e tenv)) args) 
    | EConstructor (cname, exprs, loc) -> 
      (match (find_opt tenv cname) with
      | Some TAlgebric (constructors, _) ->
        (match List.assoc_opt cname constructors with
        | Some (TProduct (arg_types, _)) ->
          if List.length arg_types = List.length exprs then
        let arg_check_errors =
          List.flatten (List.map2 (fun arg typ -> check_type_with tenv arg (untagT typ)) exprs arg_types)
        in
        arg_check_errors
          else
        [ConstructorArgumentsMismatch (cname, List.length arg_types, List.length exprs, loc)]
        | Some typ ->
          (match exprs with
          | [expr] ->
            check_type_with tenv expr (untagT typ)
          | _ -> [ConstructorArgumentsMismatch (cname, 1, List.length exprs, loc)])
        | None -> [UndefinedConstructor (cname, loc)])
      | _ -> [UndefinedConstructor (cname, loc)])
      @ List.flatten (List.map (fun e -> (type_check_expr e tenv)) exprs)
    | EMatch (mexp, branches, loc) ->
      (* We need to check 
        (1) Each branch has the same expression types
        - Infer first type of branch in the expression, which we need to get the type environment from the match + pattern
        - Check that the type of each of the following branches are the same
        (2) The pattern for each branch type checks from the match expr
        (3) The sub expressions need to type check with the pattern ids added to the type environment
        (4) The match with expression is correctly typed
        *)
      let mexp_typ = (infer_type_with tenv mexp) in
      let rec is_valid_tcheck pattern texp = 
        match texp with 
        | TId(x, _) -> 
          let typ = 
            (match (get_typ_from_prog x) with
            | Some v -> v 
            | None -> raise (InternalCompilerError (sprintf "%s was unable to be found in thy type declerations" x))) in
          (is_valid_tcheck pattern typ)
        | _ -> (match pattern with 
                  | PBlank _ -> []
                  | PId _ -> []
                  | PTup (subpatterns, _) -> 
                    (match texp with 
                    | TProduct(subtypes, _) -> 
                      if (List.length subpatterns = List.length subtypes) then
                      List.flatten (List.map2 (fun subp subt -> (is_valid_tcheck subp subt)) subpatterns subtypes)
                      else [InvalidPattern(loc)]
                    | subt -> 
                      (match subpatterns with 
                      | [subp] -> (is_valid_tcheck subp subt)
                      | _ -> [InvalidPattern(loc)]))
                  | PLiteral(l, _) -> 
                    (match (l, texp) with
                      | (LInt (_, _), TInt(_)) 
                      | (LBool (_, _), TBool(_)) -> []
                      | _ -> [InvalidPattern(loc)] 
                      )
                  | PConstructor (cname, inner_patterns, tag) -> 
                    (match texp with
                    (* theoretically this should always be larger algebric part *)
                    | TAlgebric(constructors, _) ->
                      (* and since we enforce no dups we can just get tenv *)
                      (match (find_opt tenv cname) with
                      | Some TProduct(subtypes, _) ->
                        if (List.length inner_patterns = List.length subtypes) then
                          List.flatten (List.map2 (fun subp subt -> (is_valid_tcheck subp subt)) inner_patterns subtypes)
                        else [InvalidPattern(loc)]
                      | Some subtyp -> 
                        (match inner_patterns with 
                        | [subpattern] -> (is_valid_tcheck subpattern subtyp)
                        | [] -> if (List.length inner_patterns) == 0 then [] else [InvalidPattern(loc)]
                        | single -> (is_valid_tcheck (PTup(single, tag)) subtyp)
                        (* | _ -> raise (InternalCompilerError (sprintf "Unexpected %s" (string_of_expr mexp))) *)
                         )
                      | None -> [InvalidPattern(loc)])
                    | _ -> [InvalidPattern(loc)]))
      in
      let return_typ = (infer_type_with tenv e) in
      let rec has_valid_patterns branches =
        match branches with
        | [] -> []
        | (pattern, _) :: rob ->
          (is_valid_tcheck pattern mexp_typ) @ (has_valid_patterns rob)
      in
      let valid_patterns = (has_valid_patterns branches) in
      (* bail early if the patterns are fucked *)
      if valid_patterns != [] then valid_patterns else
      let rec has_correct_branch_returns branches = 
        match branches with 
        | [] -> []
        | (pattern, exp) :: rob -> 
          (check_type_with ((pattern_to_tenv tenv mexp_typ pattern) @ tenv) exp (untagT return_typ)) @
          (has_correct_branch_returns rob)
      in
      (has_correct_branch_returns branches)
    | EIf (cond, then_branch, else_branch, _) ->
      let type_then = (infer_type_with tenv then_branch) in 
      (check_type else_branch (untagT type_then))
      @ (check_type cond (TBool ()))
      @ (type_check_expr then_branch tenv)
      @ (type_check_expr else_branch tenv)
      @ (type_check_expr cond tenv)
    | _ -> [] (* todo .. *)
    (*
     @
    | ELetRec of 'a binding list * 'a expr * 'a *)
  in 
  match p with
  | Program (tdecls, decls, body, _) -> 
    let duplicate_err = (duplicate_id tdecls []) in
    let duplicate_constructor_errs = (duplicate_constructor_names tdecls) in
    let undefined_type_errs = 
      (undefined_type_check tdecls body) 
      @ (List.flatten (List.map (fun decl -> 
          match decl with 
          | DFun(_, bl, typ, expr, _) -> (undefined_types_in_binds_check tdecls bl) 
                                       @ (undefined_type_check tdecls expr)
                                       @ (check_type_for_undefined typ tdecls))  
        (List.flatten decls))) in
    let errs = duplicate_err @ duplicate_constructor_errs @ undefined_type_errs in
    if (errs != []) then (Error errs) else 
    (* 2nd phase pt 1 : fast fail if the functions aren't type checking *)
    let errs = (type_check_decls decls (collect_constructors_env tdecls)) in
    if (errs != []) then (Error errs) else
    (* 2nd phase pt 2 : check the body *)
    let errs = (type_check_expr body ((collect_def_type_env (List.flatten decls)) @ (collect_constructors_env tdecls))) in
    if (errs = []) then (Ok p) else (Error errs)
      
