open Exprs
open Errors
open Utils
open Printf
open Pretty
open Assembly
open Phases
open Graph

let name_lambda l =
  match l with
    | CLambda(_, _, (t, _, _)) -> sprintf "lambda$%d" t
    | _ -> failwith "Tried to get a lambda name for not a lambda"

(* Add a value to the environment *)
(* Returns a triplet of the new environment, updated stack index (if the variable was already in the environment the stack index does not change), 
  and relative stack index of the variable added to the environment. *)
let rec add_env (env: arg envt) (x: string) (si: int) : arg envt * int = 
  match env with
    | [] -> ((x, RegOffset(-(si), RBP))::[], si + 1)
    | (name, v)::rest -> if name = x then ((name, v)::rest, si)
      else 
        let (env, return_si) = (add_env rest x si) in
        ((name, v)::env, return_si)
;;

let rec add_env_overwrite (env: 'a name_envt) (x: string) (target: 'a) : 'a name_envt =
  match env with
    | [] -> []
    | (name, v)::rest -> if name = x then (name, target)::rest
      else
        let new_env = (add_env_overwrite rest x target) in
        (name, v)::new_env
;;
  
(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this environment *)
let deepest_stack (env : (arg envt)) : int =
  List.fold_left 
    (fun cur_max (_, arg) ->
      match arg with
      | RegOffset (offset, RBP) -> max cur_max (-offset)
      | _ -> cur_max)
    0
    env
;;

let rec union_list sets = 
  match sets with
    | [] -> StringSet.empty
    | set::rest -> StringSet.union set (union_list rest)
;;

(*  Take a tagged aprog and produce an aprog augmented with the set of free variables at every single expression position *)
let free_vars_cache (prog : tag aprogram) : (tag * free_vars) aprogram =
  (* there is a cuter way of cleaning this up by making this a let rec and with free vars and having this call into free vars 
    and cashing the sub expressions *)
  (* This is even cuter with live vars - we should,,, get rid of this meow *)
  let rec helpA (env: free_vars) (e: 'a aexpr) : free_vars * ('a * free_vars) aexpr =
    match e with
      | ASeq (fst, sec, t) -> 
          let fst_res, fst = (helpC env fst) in 
          let snd_res, snd = (helpA env sec) in
          let res = (StringSet.union fst_res snd_res) in
          (res, ASeq (fst, snd, (t, res)))
      | ALet (bname, be, ae, t) ->
          let new_env = StringSet.add bname env in
          let (res_be, be) = (helpC new_env be) in
          let (res_ae, ae) = (helpA new_env ae) in
          let res = (StringSet.union res_be res_ae) in
          let modified_fvs = StringSet.remove bname res in
          (modified_fvs, ALet (bname, be, ae, (t, modified_fvs)))
      | ALetRec (binds, ae, t) -> 
          let names = List.map fst binds in
          let new_env = List.fold_left (fun env name -> StringSet.add name env) env names in
          let (bind_results, bind_exps) = List.split (List.map (fun (_, ce) -> helpC new_env ce) binds) in
          let res_ae, ae = helpA new_env ae in
          let res = union_list (res_ae :: bind_results) in
          let binds = (List.combine names bind_exps) in
          let modified_fvs = List.fold_left (fun fvs_acc name -> StringSet.remove name fvs_acc) res names in
          (modified_fvs, ALetRec (binds, ae, (t, modified_fvs)))
      | ACExpr(ce) -> 
          let (res, ce) = (helpC env ce) in
          (res, ACExpr(ce))
  and helpC (env: free_vars) (e: 'a cexpr) : free_vars * ('a * free_vars) cexpr =
    match e with
      | CIf(ie, thn_ae, els_ae, t) -> 
          let res_ie, ie = (helpI env ie) in
          let res_thn_ae, thn_ae = (helpA env thn_ae) in
          let res_els_ae, els_ae = (helpA env els_ae) in
          let res = union_list [res_ie; res_thn_ae; res_els_ae] in
          (res, CIf (ie, thn_ae, els_ae, (t, res)))
      | CPrim1(prim, ie, t) -> 
          let res, ie = helpI env ie in
          (res, CPrim1(prim, ie, (t, res)))
      | CPrim2(prim, l_ie, r_ie, t) -> 
          let res_l, l_ie = (helpI env l_ie) in
          let res_r, r_ie = (helpI env r_ie) in
          let res = union_list [res_l; res_r] in
          (res, CPrim2(prim, l_ie, r_ie, (t, res)))
      | CApp(ie, ie_list, ct, t) ->
          let (res_ie_list, ie_list) = (List.split (List.map (helpI env) ie_list)) in
          let (res_ie, ie) = (helpI env ie) in
          let res = union_list ([res_ie] @ res_ie_list) in
          (res, CApp(ie, ie_list, ct, (t, res)))
      | CImmExpr ie -> 
          let (res_ie, ie) = helpI env ie in
          (res_ie, CImmExpr ie)
      | CTuple(ie_list, t) -> 
          let (res_ie_list, ie_list) = (List.split (List.map (helpI env) ie_list)) in
          let res = union_list (res_ie_list) in 
          (res, CTuple(ie_list, (t, res)))
      | CGetItem(ie, ie_idx, t) -> 
          let res_ie, ie = (helpI env ie) in
          let res_ie_idx, ie_idx = (helpI env ie_idx) in 
          let res = union_list [res_ie; res_ie_idx] in
          (res, CGetItem(ie, ie_idx, (t, res)))
      | CSetItem(ie, ie_idx, ie_val, t) -> 
          let res_ie, ie = (helpI env ie) in
          let res_ie_idx, ie_idx = (helpI env ie_idx) in 
          let res_ie_val, ie_val = (helpI env ie_val) in
          let res = union_list [res_ie; res_ie_idx; res_ie_val] in
          (res, CSetItem(ie, ie_idx, ie_val, (t, res)))
      | CLambda(str_l, ae, t) ->
          let new_lambda_env = List.fold_left (fun env_acc name -> StringSet.add name env_acc) StringSet.empty str_l in
          let (res, ae) = helpA new_lambda_env ae in
          let modified_fvs = List.fold_left (fun fvs_acc name -> StringSet.remove name fvs_acc) res str_l in
          (modified_fvs, CLambda(str_l, ae, (t, modified_fvs)))
      | CConstructor(name, arg_opt, t) ->
          let res_args, res_args_opt = (match arg_opt with
            | None -> (StringSet.empty, None)
            | Some(x) -> let fvs, r_x = helpI env x in
              (fvs, Some(r_x))) in
          (res_args, CConstructor(name, res_args_opt, (t, res_args)))
      | CMatch(bl, t) ->
          let fvs, new_bl = List.fold_right (fun (ipl, ae) (fvs_acc, bl_acc) -> 
            let ipl_fvs, new_ipl, branch_env = List.fold_right (fun (i, p) (fv_acc, ipl_acc, env_acc) ->
              let defined_names = names_in_cpattern p in
              let new_p = helpPC env_acc p in
              let i_fvs, new_i = helpI env_acc i in
              let new_env = StringSet.union env_acc (StringSet.of_list defined_names) in
              let fvs_out = StringSet.union i_fvs fv_acc in
              let fvs = List.fold_right StringSet.remove defined_names fvs_out in
              (fvs, (new_i, new_p)::ipl_acc, new_env)
            ) ipl (StringSet.empty, [], env) in
            
            let ae_fvs, new_ae = helpA branch_env ae in
           
            (union_list [ae_fvs; ipl_fvs; fvs_acc;], (new_ipl, new_ae)::bl_acc) 
          ) bl (StringSet.empty, []) in
          (fvs, CMatch(new_bl, (t, fvs)))
  and helpI (env: free_vars) (e: 'a immexpr) : free_vars * ('a * free_vars) immexpr =
    match e with
      | ImmId(name, t) -> (
        let res = 
          (match StringSet.find_opt name env with
            | None -> StringSet.add name StringSet.empty
            | Some _ -> StringSet.empty) in
        (res, ImmId(name, (t, res))))
      | ImmNum(n, t) -> (StringSet.empty, ImmNum(n, (t, StringSet.empty)))
      | ImmBool(b, t) -> (StringSet.empty, ImmBool(b, (t, StringSet.empty)))
      | ImmNil t -> (StringSet.empty, ImmNil (t, StringSet.empty))
  and helpPC (env: free_vars) (p: 'a cpattern) : ('a * free_vars) cpattern =
    match p with
      | CPTup(il, t) -> CPTup(List.map (helpPI env) il, (t, StringSet.empty))
      | CPConstructor(name, i_opt, t) -> CPConstructor(name, map_opt (helpPI env) i_opt, (t, StringSet.empty))
      | CPImm(i) -> CPImm(helpPI env i)
  and helpPI (env: free_vars) (p: 'a immpattern) : ('a * free_vars) immpattern =
    match p with
      | IPBlank t -> IPBlank((t, StringSet.empty))
      | IPLInt(i, t) -> IPLInt(i, (t, StringSet.empty))
      | IPLBool(b, t) -> IPLBool(b, (t, StringSet.empty))
      | IPId(name, t) -> IPId(name, (t, StringSet.empty))
  and helpTD (td : tag type_decl) : (tag * free_vars) type_decl = 
    match td with
    | DType (str, typ, t) -> DType (str, helpT typ, (t, StringSet.empty))
  and helpT (t : tag typ) : (tag * free_vars) typ =
    match t with
    | TId (id, t) -> TId (id, (t, StringSet.empty))
    | TFunction (tin, tout, t) -> TFunction (helpT tin, helpT tout, (t, StringSet.empty))
    | TProduct (tlist, t) -> TProduct (List.map helpT tlist, (t, StringSet.empty))
    | TAlgebric (constructors, t) -> TAlgebric ((List.map (fun (s, v) -> (s, helpT v)) constructors), (t, StringSet.empty))
    | TInt t -> TInt (t, StringSet.empty)
    | TBool t  -> TBool (t, StringSet.empty)
  in
  match prog with
    | AProgram (tdecls, aexpr, t) -> 
        let (res_env, t_aexpr) = (helpA StringSet.empty aexpr) in AProgram (List.map helpTD tdecls, t_aexpr, (t, res_env))
;;

let live_var_cache (prog : ('a * 'b) aprogram) : ('a * 'b * live_vars * live_vars) aprogram = 
  let rec helpA (e: ('a * 'b) aexpr) (env: live_vars): live_vars * ('a * 'b * live_vars * live_vars) aexpr =
      (match e with
        | ALet(name, be, ae, (t, fvs)) ->
            let (ae_lvs, new_ae) = helpA ae env in
            let (be_lvs, new_be) = helpC be ae_lvs in
            let lvs_in = StringSet.remove name be_lvs in
            (lvs_in, ALet(name, new_be, new_ae, (t, fvs, lvs_in, be_lvs)))
        | ALetRec(bl, ae, (t, fvs))  ->
            let (ae_lvs, new_ae) = helpA ae env in
            (* Creates lvs tagged bind list & merged bind lvs *)
            let (bl_lvs, new_bl) = List.fold_right (fun (name, be) (lvs_acc, bl_acc) -> 
              let (be_lvs, new_be) = helpC be lvs_acc in
              (be_lvs, (name, new_be)::bl_acc)
            ) bl (ae_lvs, []) in
            (* Removes all bind names from result lvs *)
            let lvs_in = List.fold_left (fun (lvs_acc) (name, _) -> StringSet.remove name lvs_acc) bl_lvs bl in
            (lvs_in, ALetRec(new_bl, new_ae, (t, fvs, lvs_in, bl_lvs)))
        | ASeq(ce, ae, (t, fvs)) ->
            let (ae_lvs, new_ae) = helpA ae env in
            let (ce_lvs, new_ce) = helpC ce ae_lvs in
            (ce_lvs, ASeq(new_ce, new_ae, (t, fvs, ce_lvs, ce_lvs)))
        | ACExpr ce ->
            let (ce_lvs, new_ce) = helpC ce env in
            (ce_lvs, ACExpr new_ce)
            )
    and helpC (e: ('a * 'b) cexpr) (env: live_vars) : live_vars * ('a * 'b * live_vars * live_vars) cexpr =
        match e with
          | CIf(cond, thn, els, (t, fvs)) ->
              let (thn_lvs, new_thn) = helpA thn env in
              let (els_lvs, new_els) = helpA els env in
              let alvs = union_list [thn_lvs; els_lvs] in
              let (cond_lvs, new_cond) = helpI cond alvs in
              let lvs = union_list [cond_lvs; alvs] in
              (lvs, CIf(new_cond, new_thn, new_els, (t, fvs, lvs, lvs)))
          | CPrim1(p, ie, (t, fvs)) ->
              let (ie_lvs, new_ie) = helpI ie env in
              (ie_lvs, CPrim1(p, new_ie, (t, fvs, ie_lvs, ie_lvs)))
          | CPrim2(p, le, re, (t, fvs)) ->
              let (le_lvs, new_le) = helpI le env in
              let (re_lvs, new_re) = helpI re env in
              let lvs = StringSet.union le_lvs re_lvs in
              (lvs, CPrim2(p, new_le, new_re, (t, fvs, lvs, lvs)))
          | CApp(fe, args, ct, (t, fvs)) ->
              let (fe_lvs, new_fe) = helpI fe env in
              let (lvs, new_args) = List.fold_right (fun ie (lvs_acc, args_acc) ->
                let (ie_lvs, new_ie) = helpI ie lvs_acc in
                (ie_lvs, new_ie::args_acc)
              ) args (fe_lvs, []) in
              (lvs, CApp(new_fe, new_args, ct, (t, fvs, lvs, lvs)))
          | CImmExpr ie -> 
              let (ie_lvs, new_ie) = helpI ie env in
              (ie_lvs, CImmExpr new_ie)
          | CTuple (el, (t, fvs)) ->
              let (el_lvs, new_el) = List.fold_right (fun e (lvs_acc, el_acc) -> 
                let (e_lvs, new_e) = helpI e env in
                (StringSet.union e_lvs lvs_acc, new_e::el_acc)
              ) el (env, []) in
              (el_lvs, CTuple(new_el, (t, fvs, el_lvs, el_lvs)))
          | CGetItem (te, ie, (t, fvs)) ->
              let (te_lvs, new_te) = helpI te env in
              let (ie_lvs, new_ie) = helpI ie env in
              let lvs = StringSet.union te_lvs ie_lvs in
              (lvs, CGetItem(new_te, new_ie, (t, fvs, lvs, lvs)))
          | CSetItem (te, ie, e, (t, fvs)) ->
              let (te_lvs, new_te) = helpI te env in
              let (ie_lvs, new_ie) = helpI ie env in
              let (e_lvs, new_e) = helpI e env in
              let lvs = union_list [te_lvs; ie_lvs; e_lvs] in
              (lvs, CSetItem(new_te, new_ie, new_e, (t, fvs, lvs, lvs)))
          | CLambda (args, ae, (t, fvs)) ->
              let (ae_lvs, new_ae) = helpA ae env in
              (* this is lvs_out *)
              let lvs = List.fold_left (fun lvs_acc arg -> StringSet.remove arg lvs_acc) ae_lvs args in
              (lvs, CLambda(args, new_ae, (t, fvs, lvs, ae_lvs)))
          | CConstructor(name, arg_opt, (t, fvs)) ->
              let arg_lvs, new_arg_opt = (match arg_opt with
                | None -> (env, None)
                | Some(ie) -> 
                    let (l, ni) = helpI ie env in
                    (l, Some(ni))) in
              (arg_lvs, CConstructor(name, new_arg_opt, (t, fvs, arg_lvs, arg_lvs)))
          | CMatch(bl, (t, fvs)) ->
              let branch_lvs, new_bl = List.fold_right (fun (ipl, ae) (lvs_list, bl_acc) -> 
                (* Find LVS of the ae *)
                let alvs, new_ae = helpA ae env in

                (* Calculate unbound variables from immediate conds, also resolve names from AE *)
                let lvs_b, new_ipl = List.fold_right (fun (cond, p) (lvs_acc, ipl_acc) -> 
                  (* We just need to tag the pattern - this won't produce any live vars *)
                  (* TODO: This is not completely correct since individual pats of patterns will be tagged 
                     incorrectly since the helper can't resolve names_inbut it works for the final - change
                     later if this becomes important *)
                  let new_pattern = helpPC p lvs_acc in
                  (* Then we get all the new names from this pattern *)
                  let introduced_names = names_in_cpattern p in
                  (* Remove them from the live vars of the previous *)
                  let lvs_p = List.fold_right StringSet.remove introduced_names lvs_acc in
                  (* Then get the live vars for the condition *)
                  let lvs, new_i = helpI cond lvs_p in
                  (lvs, (new_i, new_pattern)::ipl_acc)
                ) ipl (alvs, [])  in

                (lvs_b::lvs_list, (new_ipl, new_ae)::bl_acc)
              ) bl ([], []) in
              
              let lvs = union_list branch_lvs in
              (lvs, CMatch(new_bl, (t, fvs, lvs, lvs)))

    and helpI (e: ('a * 'b) immexpr) (env: live_vars) : live_vars * ('a * 'b * live_vars * live_vars) immexpr =
      match e with
        | ImmId(name, (t, fvs)) -> 
            let lvs = StringSet.add name env in
            (lvs, ImmId(name, (t, fvs, lvs, env)))
        | ImmNum(n, (t, fvs)) -> (env, ImmNum(n, (t, fvs, env, env)))
        | ImmBool(b, (t, fvs)) -> (env, ImmBool(b, (t, fvs, env, env)))
        | ImmNil (t, fvs) -> (env, ImmNil (t, fvs, env, env))

    and helpPC (p: ('a * 'b) cpattern) (env: live_vars) : ('a * 'b * live_vars * live_vars) cpattern =
      match p with
        | CPTup (il, (t, f)) -> CPTup(List.map (helpPI env) il, (t, f, env, env))
        | CPConstructor (name, opt_p, (t, f)) -> CPConstructor(name, map_opt (helpPI env) opt_p, (t, f, env, env))
        | CPImm(i) -> CPImm(helpPI env i)

    and helpPI (env: live_vars) (p: ('a * 'b) immpattern) : ('a * 'b * live_vars * live_vars) immpattern =
      match p with
        | IPBlank (t, f) -> IPBlank (t, f, env, env)
        | IPId (name, (t, f)) -> IPId (name, (t, f, env, env))
        | IPLInt (i, (t, f)) -> IPLInt (i, (t, f, env, env))
        | IPLBool (b, (t, f)) -> IPLBool (b, (t, f, env, env))

    and helpTD (td : ('a * 'b) type_decl) : ('a * 'b * live_vars * live_vars) type_decl = 
      match td with
      | DType (str, typ, (a, b)) -> DType (str, helpT typ, (a, b, StringSet.empty, StringSet.empty))
    and helpT (t :  ('a * 'b) typ) :  ('a * 'b * live_vars * live_vars) typ =
      match t with
      | TId (id, (a, b)) -> TId (id, (a, b, StringSet.empty, StringSet.empty))
      | TFunction (tin, tout, (a, b)) -> TFunction (helpT tin, helpT tout, (a, b, StringSet.empty, StringSet.empty))
      | TProduct (tlist, (a, b)) -> TProduct (List.map helpT tlist, (a, b, StringSet.empty, StringSet.empty))
      | TAlgebric (constructors, (a, b)) -> TAlgebric ((List.map (fun (s, v) -> (s, helpT v)) constructors), (a, b, StringSet.empty, StringSet.empty))
      | TInt (a, b) -> TInt (a, b, StringSet.empty, StringSet.empty)
      | TBool (a, b)  -> TBool (a, b, StringSet.empty, StringSet.empty)
    in
    match prog with
      | AProgram(tdecs, body, (tag, fvs)) -> 
          let new_body =
            let (lvs, nb) = helpA body StringSet.empty in
            if lvs = StringSet.empty then nb else raise (InternalCompilerError (sprintf "Somehow had live vars [%s] at the top level of the env" (ExtString.String.join ", " (StringSet.to_list lvs)))) in
          AProgram(List.map helpTD tdecs, new_body, (tag, fvs, StringSet.empty, StringSet.empty))

(* Currently, this ignores self recursive functions *)
let dead_var_elim (prog: (tag * free_vars * live_vars * live_vars) aprogram) : (tag * free_vars * live_vars) aprogram =
  let rec helpA (e: (tag * free_vars * live_vars * live_vars) aexpr): (tag * free_vars * live_vars) aexpr =
    match e with
      | ALet(name, be, ae, (t, fvs, lvs_in, lvs_out)) ->
          (match StringSet.find_opt name lvs_out with
            | Some _ -> ALet(name, helpC be, helpA ae, (t, fvs, lvs_in))
            | None -> ASeq(helpC be, helpA ae, (t, fvs, lvs_in)))
      | ALetRec(bl, ae, (t, fvs, lvs_in, lvs_out)) ->
          let (dead, remaining) = List.fold_left (fun (d_acc, r_acc) (name, be) -> 
            (match StringSet.find_opt name lvs_out with
              | Some _ -> (d_acc, (name, helpC be)::r_acc)
              | None -> ((helpC be)::d_acc, r_acc))
          ) ([], []) bl in
          (* Is it ok here to specify live vars like this? Or do we want them to be real over the ASeq? *)
          (* This will work - it will just create extranious collisions *)
          List.fold_left 
            (fun e_acc de -> ASeq(de, e_acc, (t, fvs, lvs_in)))
            (if remaining = [] then helpA ae else (ALetRec(remaining, helpA ae, (t, fvs, lvs_in))))
          dead
      | ASeq(ce, ae, (t, fvs, lvs_in, _)) -> ASeq(helpC ce, helpA ae, (t, fvs, lvs_in))
      | ACExpr(ce) -> ACExpr(helpC ce)
  and helpC e =
    (match e with
      | CIf(cond, thn, els, (t, fvs, lvs, _)) -> CIf(helpI cond, helpA thn, helpA els, (t, fvs, lvs))
      | CLambda(args, ae, (t, fvs, lvs, _)) -> CLambda(args, helpA ae, (t, fvs, lvs))
      | CPrim1(p, ie, (t, fvs, lvs, _)) -> CPrim1(p, helpI ie, (t, fvs, lvs))
      | CPrim2(p, le, re, (t, fvs, lvs, _)) -> CPrim2(p, helpI le, helpI re, (t, fvs, lvs))
      | CApp(fe, args, ct, (t, fvs, lvs, _)) -> CApp(helpI fe, List.map helpI args, ct, (t, fvs, lvs))
      | CTuple(el, (t, fvs, lvs, _)) -> CTuple(List.map helpI el, (t, fvs, lvs))
      | CGetItem(te, ie, (t, fvs, lvs, _)) -> CGetItem(helpI te, helpI ie, (t, fvs, lvs))
      | CSetItem(te, ie, e, (t, fvs, lvs, _)) -> CSetItem(helpI te, helpI ie, helpI e, (t, fvs, lvs))
      | CMatch(bl, (t, fvs, lvs, _)) -> 
          let el_branches = List.map (fun (ipl, ae) -> 
            let el_ipl = List.map (fun (i, p) -> (helpI i, helpPC p)) ipl in
            (el_ipl, helpA ae)
          ) bl in
        CMatch(el_branches, (t, fvs, lvs))
      | CConstructor(name, arg, (t, fvs, lvs, _)) -> CConstructor(name, map_opt helpI arg, (t, fvs, lvs))
      | CImmExpr(ie) -> CImmExpr(helpI ie)
      )
  and helpI e =
    match e with
      | ImmId(n, (t, fvs, lvs, _)) -> ImmId(n, (t, fvs, lvs))
      | ImmBool(n, (t, fvs, lvs, _)) -> ImmBool(n, (t, fvs, lvs))
      | ImmNum(n, (t, fvs, lvs, _)) -> ImmNum(n, (t, fvs, lvs))
      | ImmNil((t, fvs, lvs, _)) -> ImmNil((t, fvs, lvs))
  and helpPC (p: (tag * free_vars * live_vars * live_vars) cpattern) : (tag * free_vars * live_vars) cpattern =
    match p with
      | CPTup(il, (t, f, l, _)) -> CPTup (List.map helpPI il, (t, f, l))
      | CPConstructor(n, i_opt, (t, f, l, _)) -> CPConstructor(n, map_opt helpPI i_opt, (t, f, l))
      | CPImm(i) -> CPImm(helpPI i)
  and helpPI (p: (tag * free_vars * live_vars * live_vars) immpattern) : (tag * free_vars * live_vars) immpattern =
    match p with
      | IPBlank (t, f, l, _) -> IPBlank (t, f, l)
      | IPId(n, (t, f, l, _)) -> IPId (n, (t, f, l))
      | IPLInt (i, (t, f, l, _)) -> IPLInt (i, (t, f, l))
      | IPLBool (b, (t, f, l, _)) -> IPLBool (b, (t, f, l))
  and helpTD (td : (tag * free_vars * live_vars * live_vars) type_decl) : (tag * free_vars * live_vars) type_decl = 
    match td with
    | DType (str, typ, (a, b, c, _)) -> DType (str, helpT typ, (a, b, c))
  and helpT (t :  (tag * free_vars * live_vars * live_vars) typ) : (tag * free_vars * live_vars) typ =
    match t with
    | TId (id, (a, b, c, _)) -> TId (id, (a, b, c))
    | TFunction (tin, tout, (a, b, c, _)) -> TFunction (helpT tin, helpT tout, (a, b, c))
    | TProduct (tlist, (a, b, c, _)) -> TProduct (List.map helpT tlist, (a, b, c))
    | TAlgebric (constructors, (a, b, c, _)) -> TAlgebric ((List.map (fun (s, v) -> (s, helpT v)) constructors), (a, b, c))
    | TBool (a, b, c, _) -> TBool (a, b, c)
    | TInt (a, b, c, _)  -> TInt (a, b, c)
  in
    match prog with
      | AProgram(tdec, ae, (t, fvs, lvs, _)) -> AProgram(List.map helpTD tdec, helpA ae, (t, fvs, lvs))

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog : (tag * free_vars * live_vars) aprogram) : (tag * free_vars * live_vars) aprogram * arg name_envt name_envt  =
  let rec helpA (e: (tag * free_vars * live_vars) aexpr) (si: int) (env: arg name_envt name_envt) (current_env_name: string): arg name_envt name_envt * int =
    match e with
      | ALet(name, b_exp, exp, _) ->
          let current_env = (
            match find_opt env current_env_name with
              | Some e -> e
              | None -> raise (InternalCompilerError "Failed to find current env in naive stack alloc")
          ) in
          let (new_env, new_si) = (add_env current_env name si) in
          let new_outer_env = (add_env_overwrite env current_env_name new_env) in
          let (b_env, b_si) = (helpC b_exp new_si new_outer_env current_env_name) in
          (helpA exp b_si b_env current_env_name)
      | ACExpr(exp) -> (helpC exp si env current_env_name)
      | ASeq (ce, ae, _) -> 
          let (ce_env, new_si) = helpC ce si env current_env_name in
          helpA ae new_si ce_env current_env_name
      | ALetRec (names, body, _) -> 
          let current_env = (
            match find_opt env current_env_name with
              | Some e -> e
              | None -> raise (InternalCompilerError "Failed to find current env in naive stack alloc")
          ) in
          (* First pass: add all the names to the environment without evaluating their expressions *)
          let (name_only_env, new_si) = List.fold_left 
            (fun (env_acc, si_acc) (name, _) -> 
              add_env env_acc name si_acc) 
            (current_env, si) 
            names 
          in
          let new_outer_env = (add_env_overwrite env current_env_name name_only_env) in
          (* Second pass: Process each binding separately, making sure to env with only names *)
          let (b_env, b_si) = List.fold_left 
            (fun (env_acc, si_acc) (_, b_exp) -> 
              helpC b_exp si_acc env_acc current_env_name)
            (new_outer_env, new_si)
            names
          in
          (* Process the body with only the original names in scope *)
          helpA body b_si b_env current_env_name
  and helpC (e: (tag * free_vars * live_vars) cexpr) (si: int) (env: arg name_envt name_envt) (current_env_name: string): arg name_envt name_envt * int =
    match e with
      | CIf(_, thn, els, _) -> 
          let (thn_env, thn_si) = (helpA thn si env current_env_name) in
          let (els_env, els_si) = (helpA els thn_si thn_env current_env_name) in
          (els_env, els_si)
      | CLambda(_, body, (_, fvs, _)) -> 
        (* modified to work with free vars cached *)
        (* note that because of how we use free vars, this actually isn't much of a change *)
          let lambda_name = name_lambda e in
          let free_vars = (StringSet.to_list fvs) in
          let new_lambda_env = [] in
          let (new_env, new_si) = List.fold_left (fun (env_acc, si_acc) var -> add_env env_acc var si_acc) (new_lambda_env, 1) free_vars in
          let new_outer_env = (lambda_name, new_env)::env in
          let (new_new_env, _) = helpA body new_si new_outer_env lambda_name in
          (new_new_env, si)
      | CMatch(bl, _) ->
          let new_outer_env, new_si = List.fold_left (fun (env_acc, si_acc) (ipl, ae) -> 
            let current_env = match find_opt env_acc current_env_name with 
              | None -> raise (InternalCompilerError "failed to find current env in naive stack alloc")
              | Some (e) -> e in
            let names = List.concat (List.map (fun (_, p) -> names_in_cpattern p) ipl) in
            let new_current_env, new_si = List.fold_left (fun (env_acc, si_acc) var -> add_env env_acc var si_acc) (current_env, si_acc) names in
            let new_outer_env = (add_env_overwrite env current_env_name new_current_env) in
            let new_new_outer_env, new_new_si = helpA ae new_si new_outer_env current_env_name in
            (new_new_outer_env, new_new_si)
          ) (env, si) bl in
          new_outer_env, new_si
      | _ -> (env, si)
  in
    match prog with
    | AProgram (_, aexpr, _) -> 
        let (res_env, _) = (helpA aexpr 1 [(program_entrypoint, [])] program_entrypoint) in (prog, res_env)
;;

let interfere (e : ('a * 'b * live_vars) aexpr) : grapht =
  let merge_graphs gl =
    List.fold_left (fun g_acc g -> graph_merge g g_acc) empty gl
  (* TODO this could be a bit better by not being O(n^2) *)
  in let interfere_lvs lvs g =
    let l_lvs = StringSet.to_list lvs in
    List.fold_left (
      fun g_acc_outer lv_a ->
        List.fold_left (
          fun g_acc_inner lv_b ->
            add_edge g_acc_inner lv_a lv_b
      ) g_acc_outer l_lvs
    ) g l_lvs
  in let rec helpA (e : ('a * 'b * live_vars) aexpr) =
    match e with 
    | ALet(_, be, ae, (_, _, lvs)) | ASeq(be, ae, (_, _, lvs)) -> 
        let b_ig = helpC be in
        let e_ig = helpA ae in
        let old_ig = merge_graphs [b_ig; e_ig] in
        interfere_lvs lvs old_ig
    | ACExpr(exp) -> helpC exp
    | ALetRec (bl, ae, (_, _, lvs)) ->
        let names = List.map (fun (n, _) -> n) bl in
        let e_ig = helpA ae in
        let old_ig = merge_graphs (e_ig::(List.map (fun (_, be) -> (helpC be)) bl)) in
        interfere_lvs (StringSet.union lvs (StringSet.of_list names)) old_ig
  and helpC (e : ('a * 'b * live_vars) cexpr) =
    (match e with
      | CIf(_, thn, els, (_, _, lvs)) ->
          let thn_ig = helpA thn in
          let els_ig = helpA els in
          let old_ig = merge_graphs [ thn_ig; els_ig] in
          interfere_lvs lvs old_ig
      | CMatch(bl, (_, _, lvs)) ->
        let b_ig_l = List.map (fun (ipl, ae) -> 
          let ipl_ig = List.fold_left (fun ig (i, _) ->
            merge_graphs [ig; (helpI i)]
          ) empty ipl in
          let a_ig =  helpA ae in
          let old_ig = merge_graphs [a_ig; ipl_ig] in
          interfere_lvs lvs old_ig
        ) bl in
        let merged = merge_graphs b_ig_l in
        interfere_lvs lvs merged
      | CLambda(_, _, (_, fvs, lvs)) -> interfere_lvs lvs (interfere_lvs fvs empty)
      | CPrim1(_, _, (_, _, lvs))
      | CPrim2(_, _, _, (_, _, lvs))
      | CApp(_, _, _, (_, _, lvs))
      | CTuple(_, (_, _, lvs))
      | CGetItem(_, _, (_, _, lvs))
      | CConstructor(_, _, (_, _, lvs))
      | CSetItem(_, _, _, (_, _, lvs)) -> interfere_lvs lvs empty
      | CImmExpr(ie) -> helpI ie
    )
  and helpI (e: ('a * 'b * live_vars) immexpr) =
    match e with
      | ImmBool(_, (_, _, lvs))
      | ImmId(_, (_, _, lvs))
      | ImmNil((_, _, lvs))
      | ImmNum(_, (_, _, lvs)) -> interfere_lvs lvs empty 
  in helpA e
;;

(* 
  Given the interference graph g and current register alocation enviornment, colors the graph
*)
let color_graph (g : grapht) (init_env : arg name_envt) : arg name_envt =
  let register_colors = [Reg R12; Reg R13; Reg R14;] in
  let color_idx_to_alloc (i : int) : (arg) =
    (* This is bad because it doesn't account for freevars... todo *)
    if (i < (List.length register_colors)) then (List.nth register_colors i) else (RegOffset((~-(i - (List.length register_colors) + 1)), RBP)) in
  (* finds the next color to use given the current being used *)
  let next_color (seen_colors : arg list) : arg =
    let rec next_color_help (i : int) : arg = 
      let color_alloc = (color_idx_to_alloc i) in
      if (List.mem color_alloc seen_colors) then (next_color_help (i + 1)) else color_alloc
    in (next_color_help 0)
  in
  (* producing a worklist of nodes that we’ll process in order *)
  let rec build_worklist (g : grapht) (worklist : string list) : string list =  
    match (smallest_degree_node g) with
    | None -> worklist
    | Some v -> (build_worklist (remove_node g v) (v :: worklist))
  in
  (* colors the worklist hehe *)
  let rec do_coloring (work_list: string list) (env_acc : arg name_envt) : arg name_envt = 
    match work_list with
    | [] -> env_acc
    | v :: row -> 
      let names, _ = (List.split env_acc) in
      if (List.mem v names) then
        (do_coloring row env_acc)
      else
        let edges = (get_neighbors g v) in
        let colors_taken = (List.map snd (List.filter (fun (name, _) -> (List.mem name edges)) env_acc)) in
        let v_color = (next_color colors_taken) in
        (do_coloring row ((v, v_color) :: env_acc))
  in
  (do_coloring (build_worklist g []) init_env)
;;

let register_allocation (prog : (tag * free_vars * live_vars) aprogram) : (tag * free_vars * live_vars) aprogram * arg name_envt name_envt =
  (* Basically we just want to recur into each body and do the interference graph gen/coloring at each stack frame *)
  let rec helpA (e: (tag * free_vars * live_vars) aexpr) (env: arg name_envt name_envt): arg name_envt name_envt =
    match e with
      | ALet(_, be, ae, _) -> 
          let b_env = helpC be env in
          helpA ae b_env
      | ACExpr(be) -> helpC be env
      | ASeq (be, ae, _) -> 
          let be_env = helpC be env in
          helpA ae be_env
      | ALetRec (bl, ae, _) ->
          let b_env = List.fold_left (fun b_env_acc (_, be) -> helpC be b_env_acc) env bl in
          helpA ae b_env
  and helpC (e: (tag * free_vars * live_vars) cexpr) (env: arg name_envt name_envt): arg name_envt name_envt =
    match e with
      | CIf(_, thn, els, _) -> 
          let thn_env = helpA thn env in
          helpA els thn_env
      | CLambda(_, body, _) -> 
          (* TODO free vars meow? *)
          let name = name_lambda e in
          let l_env = color_graph (interfere body) [] in
          let new_env = (name, l_env)::env in
          helpA body new_env
      | CMatch(bl, _) ->
          List.fold_left (fun env_acc (_, ae) -> helpA ae env_acc) env bl
      | _ -> env
  in
    match prog with
    | AProgram (_, ae, _) -> 
        let entry_env = color_graph (interfere ae) [] in
        let env_acc = [(program_entrypoint, entry_env)] in
        (prog, helpA ae env_acc)

;;
