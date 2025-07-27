open Exprs
open Errors
open Utils
open Printf
open Pretty

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish
   letrec from let. Essentially, it accumulates just enough information
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
   type 'a anf_bind =
   | BLet of string * 'a cexpr
   | BLetRec of (string * 'a cexpr) list
 
 let anf (p : tag program) : unit aprogram =
   let rec helpP (p : tag program) : unit aprogram =
     match p with
     | Program (dl, [], body, _) -> AProgram (List.map untag_decel dl, helpA body, ())
     | _ -> raise (InternalCompilerError "Top-level declarations should have been desugared away")
   and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
     match e with
     | EPrim1 (op, arg, _) ->
         let arg_imm, arg_setup = helpI arg in
         (CPrim1 (op, arg_imm, ()), arg_setup)
     | EPrim2 (op, left, right, _) ->
         let left_imm, left_setup = helpI left in
         let right_imm, right_setup = helpI right in
         (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
     | EIf (cond, _then, _else, _) ->
         let cond_imm, cond_setup = helpI cond in
         (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
     | ELet ([], body, _) -> helpC body
     | ELet((BBlank _, b_exp, _)::[], exp, _) -> (
          let (_, c_ctx) = helpI b_exp in
          let (c_exp, exp_ctx) = helpC exp in
          (c_exp, c_ctx @ exp_ctx))
     | ELet ((BNameTyped (bind, _, _, _), exp, _) :: rest, body, pos) ->
         let exp_ans, exp_setup = helpC exp in
         let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
         (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
     | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
         raise (InternalCompilerError "Tuple bindings should have been desugared away")
     | ESeq (e1, e2, _) ->
         raise (InternalCompilerError "Sequences should have been desugared away")
      | EApp(fn_obj, args, call_type, _) -> 
       let (imm_fn_obj, fn_obj_ctx) = helpI fn_obj in
       let (imm_list, ctx) = 
       List.fold_left (fun (imm_list, ctx) (exp) -> (
         let (imm_exp, exp_ctx) = helpI exp in
         (imm_list @ [imm_exp], ctx @ exp_ctx)
       )) ([], []) args in
       (CApp(imm_fn_obj, imm_list, call_type, ()), ctx @ fn_obj_ctx)
     | ETuple(exprs, _) -> 
       let (ctx, imms) = List.fold_left (fun (ctx_acc, imms_acc) ex ->
         let (new_imm, new_ctx) = helpI ex in
         (ctx_acc @ new_ctx, imms_acc @ [new_imm])
       ) ([], []) exprs
       in (CTuple(imms, ()), ctx)
     | EGetItem(a, b, _) ->
         let (a_imm, a_ctx) = helpI a in
         let (b_imm, b_ctx) = helpI b in
         (CGetItem(a_imm, b_imm, ()), a_ctx @ b_ctx)
     | ESetItem(a, b, c, _) ->
         let (a_imm, a_ctx) = helpI a in
         let (b_imm, b_ctx) = helpI b in
         let (c_imm, c_ctx) = helpI c in
         (CSetItem(a_imm, b_imm, c_imm, ()), a_ctx @ b_ctx @ c_ctx)
     | ELambda(binds, _, exp, _) -> 
       let arg_names = List.fold_left (fun acc b -> 
         match b with
           | BNameTyped(s, _, _, _) -> acc @ [s]
           | _ -> raise (InternalCompilerError("ANF: Non-name binding in lambda"))
       ) [] binds in
       (CLambda(arg_names, helpA exp, ()), [])
     | ELetRec (binds, body, _) -> 
      let processed_binds = List.map 
        (fun (bind, b_exp, bind_tag) -> 
          let (b_cexp, _) = (helpC b_exp) in
          (match bind with 
          | BNameTyped(s, _, _, _) -> (s, b_cexp)
          | _ -> raise (InternalCompilerError("ANF: Non-name binding in let-rec"))))
        binds
      in
      let (c_exp, exp_ctx) = helpC body in
      (c_exp, BLetRec (processed_binds) :: exp_ctx)
     | EConstructor(name, args, _) ->
         let ctx, arg_opt = match args with
          | [] -> ([], None)
          | x::[] -> 
            let i, ctx = helpI x in
            (ctx, Some(i))
          | _ -> raise (InternalCompilerError "Desugaring invariant for constructors failed") in
         (CConstructor(name, arg_opt, ()), ctx)
     | EMatch(e, pe_l, _) ->
         let (new_e, e_ctx) = helpI e in
         let branches = List.map (fun (p, be) ->
            let ipl = helpPat new_e p in
            (ipl, helpA be)) pe_l in
         (CMatch(branches, ()), e_ctx)
     | _ ->
         let imm, setup = helpI e in
         (CImmExpr imm, setup)
   and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
     match e with
     | ENumber (n, _) -> (ImmNum (n, ()), [])
     | EBool (b, _) -> (ImmBool (b, ()), [])
     | EId (name, _) -> (ImmId (name, ()), [])
     | ENil _ -> (ImmNil (), [])
     | ESeq (e1, e2, _) -> raise (InternalCompilerError "Sequences should have been desugared away")
     | ETuple(exprs, t) ->
         let name = (sprintf "tup#$%d" t) in
         let (ctx, imms) = List.fold_left (fun (ctx_acc, imms_acc) ex ->
           let (new_imm, new_ctx) = helpI ex in
           (ctx_acc @ new_ctx, imms_acc @ [new_imm])
         ) ([], []) exprs
         in 
         (ImmId(name, ()), ctx @ [BLet (name, CTuple(imms, ()))])
     | EGetItem(a, b, t) ->
         let name = (sprintf "tupget#$%d" t) in
         let (a_imm, a_ctx) = helpI a in
         let (b_imm, b_ctx) = helpI b in
         (ImmId(name, ()), a_ctx @ b_ctx @ [BLet (name, CGetItem(a_imm, b_imm, ()))])
     | ESetItem(a, b, c, t) ->
         let name = (sprintf "tupset#$%d" t) in
         let (a_imm, a_ctx) = helpI a in
         let (b_imm, b_ctx) = helpI b in
         let (c_imm, c_ctx) = helpI c in
         (ImmId(name, ()), a_ctx @ b_ctx @ c_ctx @ [BLet (name, CSetItem(a_imm, b_imm, c_imm, ()))])
     | EPrim1 (op, arg, tag) ->
         let tmp = sprintf "unary_$%d" tag in
         let arg_imm, arg_setup = helpI arg in
         (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
     | EPrim2 (op, left, right, tag) ->
         let tmp = sprintf "binop_$%d" tag in
         let left_imm, left_setup = helpI left in
         let right_imm, right_setup = helpI right in
         ( ImmId (tmp, ()),
           left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, ()))] )
     | EIf (cond, _then, _else, tag) ->
         let tmp = sprintf "if_$%d" tag in
         let cond_imm, cond_setup = helpI cond in
         (ImmId (tmp, ()), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
     | EApp(_, _, _, t) -> 
       let (c_exp, ctx) = helpC e in
         let name = (sprintf "fnapp$#%d" t) in
         (ImmId(name, ()), ctx @ [BLet (name, c_exp)])
     | ELet ([], body, _) -> helpI body
     | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
         let exp_ans, exp_setup = helpI exp in
         (* MUST BE helpI, to avoid any missing final steps *)
         let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
         (body_ans, exp_setup @ body_setup)
     | ELambda(binds, _, exp, t) -> 
         let lambda_tmp_name = (sprintf "lambda#$%d" t)
        in
         let arg_names = List.fold_left (fun acc b -> 
           match b with
             | BNameTyped(s, _, _, _) -> acc @ [s]
             | _ -> raise (InternalCompilerError("Well-formed should catch this"))
         ) [] binds in
         (ImmId(lambda_tmp_name, ()), [BLet (lambda_tmp_name, CLambda(arg_names, helpA exp, ()))])
     | ELet ((BNameTyped (bind, _, _, _), exp, _) :: rest, body, pos) ->
         let exp_ans, exp_setup = helpC exp in
         let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
         (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
     | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
         raise (InternalCompilerError "Tuple bindings should have been desugared away")
     | ELetRec (binds, body, tag) ->
      let processed_binds = List.map 
        (fun (bind, b_exp, bind_tag) -> 
          (* we can ignore the context given from the body of the binding since 
             we're only using those bindings locally *)
          let (b_cexp, _) = (helpC b_exp) in
          (match bind with 
  | BNameTyped(s, _, _, _) -> (s, b_cexp)
          | _ -> raise (InternalCompilerError("ANF: Non-name binding in let-rec"))))
        binds
      in
      let (imm_exp, exp_ctx) = helpI body in
      (imm_exp, (BLetRec processed_binds) :: exp_ctx)
     | EConstructor(name, args, t) ->
         let c_name = sprintf "%s-con#%d" name t in
         let ctx, arg_opt = match args with
          | [] -> ([], None)
          | x::[] -> 
            let i, ctx = helpI x in
            (ctx, Some(i))
          | _ -> raise (InternalCompilerError "Desugaring invariant for constructors failed") in
         (ImmId(c_name, ()), ctx @ [BLet(c_name, CConstructor(name, arg_opt, ()))])
     | EMatch(e, pe_l, t) ->
         let m_name = sprintf "match#%d" t in
         let (new_e, e_ctx) = helpI e in
         let branches = List.map (fun (p, be) ->
            let ipl = helpPat new_e p in
            (ipl, helpA be)) pe_l in
         (ImmId(m_name, ()), e_ctx @ [BLet(m_name, CMatch(branches, ()))])

    and helpPat cond p: (unit immexpr * unit cpattern) list =
      helpPPending [(cond, p)]

    and helpPPending pending: (unit immexpr * unit cpattern) list =
      match pending with
        | [] -> []
        | (ie, p)::rest -> 
            let new_pending, cpat = helpPC p in
            (ie, cpat)::(helpPPending (rest @ new_pending))

    and helpPC p: (unit immexpr * tag pattern) list * unit cpattern =
      match p with
        | PConstructor(name, pl, t) ->
            let pending, imm = 
              (match pl with
                | [] -> ([], None)
                | x::[] -> 
                    let pending, ip = helpPI x in (pending, Some(ip))
                | _ -> raise (InternalCompilerError "Should only be one associated datatype")) in
            (pending, CPConstructor(name, imm, ()))
        | PTup(pl, _) ->
            let pending, il = List.fold_right (fun p (pen_acc, il_acc) -> 
              let ppending, pimm = helpPI p in
              (ppending @ pen_acc, pimm::il_acc)
            ) pl ([], []) in
            (pending, CPTup(il, ()))
        | _ ->
            let pending, ip = helpPI p in
            (pending, CPImm(ip))
      
    and helpPI p: (unit immexpr * tag pattern) list * unit immpattern =
      match p with
        | PBlank _ -> ([], IPBlank(()))
        | PId (n, _) -> ([], IPId(n, ()))
        | PLiteral(LInt(i, _), _) -> ([], IPLInt(i, ()))
        | PLiteral(LBool(b, _), _) -> ([], IPLBool(b, ()))
        | PConstructor(name, _, t) ->
            let c_name = sprintf "con-pat#%s#%d" name t in
            ([ImmId(c_name, ()), p], IPId (c_name, ()))
        | PTup(pl, t) ->
            let t_name = sprintf "tup-pat#%d" t in
            ([ImmId(t_name, ()), p], IPId (t_name, ()))

   and helpA e : unit aexpr =
     let ans, ans_setup = helpC e in
     List.fold_right
       (fun bind body ->
         (* Here's where the anf_bind datatype becomes most useful:
             BLet binds get wrapped back into ALet aexprs.
             BLetRec binds get wrapped back into ALetRec aexprs.
           Syntactically it looks like we're just replacing Bwhatever with Awhatever,
           but that's exactly the information needed to know which aexpr to build. *)
         match bind with
         | BLet (name, exp) -> ALet (name, exp, body, ())
         | BLetRec names -> ALetRec (names, body, ()) )
       ans_setup (ACExpr ans)
   in
   helpP p
 ;;
