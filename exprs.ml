open Printf

let show_debug_print = ref false

let debug_printf fmt =
  if !show_debug_print then
    printf fmt
  else
    ifprintf stdout fmt
;;

type tag = int

type sourcespan = Lexing.position * Lexing.position

type 'a pattern =
  | PConstructor of string * 'a pattern list * 'a
  | PBlank of 'a
  | PId of string * 'a
  | PTup of 'a pattern list * 'a
  | PLiteral of 'a literal * 'a
and 'a literal =
  | LInt of int64 * 'a
  | LBool of bool * 'a

type 'a cpattern =
  | CPTup of 'a immpattern list * 'a
  | CPConstructor of string * 'a immpattern option * 'a
  | CPImm of 'a immpattern
and 'a immpattern =
  | IPBlank of 'a
  | IPId of string * 'a
  | IPLInt of int64 * 'a
  | IPLBool of bool * 'a

type prim1 =
  | Add1
  | Sub1
  (* | Print *)
  (* | IsBool
  | IsNum
  | IsTuple *)
  | Not
  (* | PrintStack *)


type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq
  (* | CheckSize *)

type 'a bind =
  | BBlank of 'a
  | BNameTyped of string * 'a typ * bool * 'a
  | BNameUntype of string * bool * 'a
  | BTuple of 'a bind list * 'a

and 'a binding = 'a bind * 'a expr * 'a

and call_type =
  | Native
  | Snake
  | Prim
  | Unknown

and 'a expr =
  | ESeq of 'a expr * 'a expr * 'a
  | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * 'a expr * 'a
  | ESetItem of 'a expr * 'a expr * 'a expr * 'a
  | ELet of 'a binding list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | ENil of 'a
  | EId of string * 'a
  | EApp of 'a expr * 'a expr list * call_type * 'a
  | ELambda of 'a bind list * 'a typ * 'a expr * 'a
  | ELetRec of 'a binding list * 'a expr * 'a
  | EConstructor of string * 'a expr list * 'a
  | EMatch of 'a expr * ('a pattern * 'a expr) list * 'a

and 'a typ = 
  | TInt of 'a
  | TBool of 'a 
  | TId of string * 'a
  | TFunction of 'a typ * 'a typ * 'a
  | TProduct of 'a typ list * 'a 
  | TAlgebric of (string * 'a typ) list * 'a 

type 'a type_decl = DType of string * 'a typ * 'a

(* name, binds (including types), return type, body, and tag info *)
type 'a decl = DFun of string * 'a bind list * 'a typ * 'a expr * 'a

type 'a program = Program of 'a type_decl list * 'a decl list list * 'a expr * 'a

type alloc_strategy =
  | Register
  | Naive

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * call_type * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
  | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * 'a immexpr * 'a
  | CSetItem of 'a immexpr * 'a immexpr * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * 'a
  | CConstructor of string * 'a immexpr option * 'a
  | CMatch of (('a immexpr * 'a cpattern) list * 'a aexpr) list * 'a

and 'a aexpr =
  (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a aprogram = AProgram of 'a type_decl list * 'a aexpr * 'a

let map_opt f v =
  match v with
  | None -> None
  | Some v -> Some (f v)
;;

let get_tag_E e =
  match e with
  | ELet (_, _, t) -> t
  | ELetRec (_, _, t) -> t
  | EPrim1 (_, _, t) -> t
  | EPrim2 (_, _, _, t) -> t
  | EIf (_, _, _, t) -> t
  | ENil t -> t
  | ENumber (_, t) -> t
  | EBool (_, t) -> t
  | EId (_, t) -> t
  | EApp (_, _, _, t) -> t
  | ETuple (_, t) -> t
  | EGetItem (_, _, t) -> t
  | ESetItem (_, _, _, t) -> t
  | ESeq (_, _, t) -> t
  | ELambda (_, _, _, t) -> t
  | EConstructor (_, _, t) -> t
  | EMatch (_, _, t) -> t
;;

let get_tag_D d =
  match d with
  | DFun (_, _, _, _, t) -> t
;;

let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | ESeq (e1, e2, a) -> ESeq (map_tag_E f e1, map_tag_E f e2, f a)
  | ETuple (exprs, a) -> ETuple (List.map (map_tag_E f) exprs, f a)
  | EGetItem (e, idx, a) -> EGetItem (map_tag_E f e, map_tag_E f idx, f a)
  | ESetItem (e, idx, newval, a) ->
      ESetItem (map_tag_E f e, map_tag_E f idx, map_tag_E f newval, f a)
  | EId (x, a) -> EId (x, f a)
  | ENumber (n, a) -> ENumber (n, f a)
  | EBool (b, a) -> EBool (b, f a)
  | ENil a -> ENil (f a)
  | EPrim1 (op, e, a) ->
      let tag_prim = f a in
      EPrim1 (op, map_tag_E f e, tag_prim)
  | EPrim2 (op, e1, e2, a) ->
      let tag_prim = f a in
      let tag_e1 = map_tag_E f e1 in
      let tag_e2 = map_tag_E f e2 in
      EPrim2 (op, tag_e1, tag_e2, tag_prim)
  | ELet (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELet (tag_binds, tag_body, tag_let)
  | ELetRec (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELetRec (tag_binds, tag_body, tag_let)
  | EIf (cond, thn, els, a) ->
      let tag_if = f a in
      let tag_cond = map_tag_E f cond in
      let tag_thn = map_tag_E f thn in
      let tag_els = map_tag_E f els in
      EIf (tag_cond, tag_thn, tag_els, tag_if)
  | EApp (func, args, native, a) ->
      let tag_app = f a in
      EApp (map_tag_E f func, List.map (map_tag_E f) args, native, tag_app)
  | ELambda (binds, typ, body, a) ->
      let tag_lam = f a in
      ELambda (List.map (map_tag_B f) binds, map_tag_T f typ, map_tag_E f body, tag_lam)
  | EConstructor(name, args, a) ->
      let tag_con = f a in
      let tag_args = List.map (map_tag_E f) args in
      EConstructor(name, tag_args, tag_con)
  | EMatch(e, p_l, a) ->
      let tag_e = map_tag_E f e in
      let tag_p_l = List.map (fun (p, e) -> ((map_tag_Pattern f p), map_tag_E f e)) p_l in
      EMatch(tag_e, tag_p_l, f a)

and map_tag_B (f : 'a -> 'b) b =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BNameTyped (x, typ, allow_shadow, ax) ->
      let tag_ax = f ax in
      BNameTyped (x, map_tag_T f typ, allow_shadow, tag_ax)
  | BTuple (binds, t) ->
      let tag_tup = f t in
      BTuple (List.map (map_tag_B f) binds, tag_tup)

and map_tag_Pattern (f: 'a -> 'b) p =
  match p with
  | PBlank a -> PBlank(f a)
  | PId (name, a) -> PId(name, f a)
  | PTup (pats, a) ->
      let tag_pats = List.map (map_tag_Pattern f) pats in
      PTup (tag_pats, f a)
  | PLiteral (lit, a) -> PLiteral (map_tag_L f lit, f a)
  | PConstructor (name, pats, a) ->
    let tag_pats = List.map (map_tag_Pattern f) pats in
    PConstructor (name, tag_pats, f a)
and map_tag_L (f: 'a -> 'b) l =
  match l with
  | LInt (v, a) -> LInt (v, f a)
  | LBool (b, a) -> LBool (b, f a)

and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun (name, args, typ, body, a) ->
      let tag_fun = f a in
      let tag_args = List.map (map_tag_B f) args in
      let tag_body = map_tag_E f body in
      DFun (name, tag_args, map_tag_T f typ, tag_body, tag_fun)

and map_tag_T (f : 'a -> 'b) typ =
  match typ with 
  | TInt (t) -> TInt (f t)
  | TBool (t) -> TBool (f t)
  | TId (str, t) -> TId (str, f t)
  | TFunction (fst, snd, t) -> TFunction (map_tag_T f fst, map_tag_T f snd, f t)
  | TProduct (tlist, t) -> TProduct(List.map (map_tag_T f) tlist, f t)
  | TAlgebric (constructors, t) -> 
    let tag_constructors = (List.map (fun (s, typ) -> (s, map_tag_T f typ)) constructors) in
    TAlgebric (tag_constructors, f t)

and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program (typedecls, declgroups, body, a) ->
      let tag_a = f a in
      let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
      let tag_typs = List.map (fun tdec -> match tdec with DType (str, typ, tag) -> DType (str, map_tag_T f typ, f tag)) typedecls in
      let tag_body = map_tag_E f body in
      Program (tag_typs, tag_decls, tag_body, tag_a)
;;

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_P tag p
;;

let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) : ('b * 'c) program =
  map_tag_P (fun a -> (f1 a, f2 a)) p
;;

let tag_and_map (f : 'a -> 'b) (p : 'a program) : ('a * 'b) program =
  map_tag_P (fun a -> (a, f a)) p
;;

let prog_and_tag (p : 'a program) : ('a * tag) program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  tag_and_map tag p
;;

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program (tdec, decls, body, _) ->
    let untagged_types = (List.map (fun x -> match x with DType(str, typ, _) -> DType(str, untagT typ, ())) tdec) in
    Program (untagged_types, List.map (fun group -> List.map untagD group) decls, untagE body, ())
and untagE e =
  match e with
  | ESeq (e1, e2, _) -> ESeq (untagE e1, untagE e2, ())
  | ETuple (exprs, _) -> ETuple (List.map untagE exprs, ())
  | EGetItem (e, idx, _) -> EGetItem (untagE e, untagE idx, ())
  | ESetItem (e, idx, newval, _) -> ESetItem (untagE e, untagE idx, untagE newval, ())
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | ENil _ -> ENil ()
  | EPrim1 (op, e, _) -> EPrim1 (op, untagE e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untagE e1, untagE e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | EIf (cond, thn, els, _) -> EIf (untagE cond, untagE thn, untagE els, ())
  | EApp (func, args, native, _) -> EApp (untagE func, List.map untagE args, native, ())
  | ELetRec (binds, body, _) ->
      ELetRec (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | ELambda (binds, typ, body, _) -> ELambda (List.map untagB binds, untagT typ, untagE body, ())
  | EConstructor(name, args, _) -> EConstructor (name, List.map untagE args, ())
  | EMatch(name, pe_l, _) ->
      let untag_pe_l = List.map (fun (p, e) -> (untagPat p, untagE e)) pe_l in
      EMatch(untagE name, untag_pe_l, ())
and untagPat (p: 'a pattern) =
  match p with
  | PBlank _ -> PBlank(())
  | PId(name, _) -> PId(name, ())
  | PTup(pl, _) -> PTup(List.map untagPat pl, ())
  | PConstructor(name, args, _) -> PConstructor(name, List.map untagPat args, ())
  | PLiteral(l, _) -> PLiteral(untagL l, ())
and untagL l = 
  match l with
  | LInt (v, _) -> LInt (v, ())
  | LBool (b, _) -> LBool (b, ())
and untagB b =
  match b with
  | BBlank _ -> BBlank ()
  | BNameTyped (x, typ, allow_shadow, _) -> BNameTyped (x, untagT typ, allow_shadow, ())
  | BTuple (binds, _) -> BTuple (List.map untagB binds, ())
and untagD d =
  match d with
  | DFun (name, args, typ, body, _) -> DFun (name, List.map untagB args, untagT typ, untagE body, ())
and untagT t =
  match t with
  | TInt (_) -> TInt (())
  | TBool (_) -> TBool (())
  | TId (str, _) -> TId (str, ())
  | TFunction (fst, snd, _) -> TFunction (untagT fst, untagT snd, ())
  | TProduct (tlist, _) -> TProduct(List.map untagT tlist, ())
  | TAlgebric (constructors, _) -> 
    let untagged_constructors = (List.map (fun (s, typ) -> (s, untagT typ)) constructors) in
    TAlgebric (untagged_constructors, ())
;;

let rec untag_decel (d: 'a type_decl): unit type_decl =
  match d with
    | DType(name, t, _) -> DType(name, untag_typ t, ())
and untag_typ (t: 'a typ): unit typ =
  match t with
    | TInt _ -> TInt(())
    | TBool _ -> TBool(())
    | TId(name, _) -> TId(name, ())
    | TFunction(t1, t2, _) -> TFunction(untag_typ t1, untag_typ t2, ())
    | TProduct(tl, _) -> TProduct(List.map untag_typ tl, ())
    | TAlgebric(tenv, _) ->
        let new_tenv = List.fold_right (fun (n, t) tenv_acc -> 
          (n, untag_typ t)::tenv_acc
        ) tenv [] in
        TAlgebric(new_tenv, ())

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ASeq (e1, e2, _) ->
        let seq_tag = tag () in
        ASeq (helpC e1, helpA e2, seq_tag)
    | ALet (x, c, b, _) ->
        let let_tag = tag () in
        ALet (x, helpC c, helpA b, let_tag)
    | ALetRec (xcs, b, _) ->
        let let_tag = tag () in
        ALetRec (List.map (fun (x, c) -> (x, helpC c)) xcs, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1 (op, e, _) ->
        let prim_tag = tag () in
        CPrim1 (op, helpI e, prim_tag)
    | CPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        CPrim2 (op, helpI e1, helpI e2, prim_tag)
    | CIf (cond, thn, els, _) ->
        let if_tag = tag () in
        CIf (helpI cond, helpA thn, helpA els, if_tag)
    | CApp (func, args, native, _) ->
        let app_tag = tag () in
        CApp (helpI func, List.map helpI args, native, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple (es, _) ->
        let tup_tag = tag () in
        CTuple (List.map helpI es, tup_tag)
    | CGetItem (e, idx, _) ->
        let get_tag = tag () in
        CGetItem (helpI e, helpI idx, get_tag)
    | CSetItem (e, idx, newval, _) ->
        let set_tag = tag () in
        CSetItem (helpI e, helpI idx, helpI newval, set_tag)
    | CLambda (args, body, _) ->
        let lam_tag = tag () in
        CLambda (args, helpA body, lam_tag)
    | CConstructor(name, assoc, _) ->
        let con_tag = tag () in
        let assoc_tag = match assoc with
          | None -> None
          | Some(x) -> Some(helpI x) in
        CConstructor(name, assoc_tag, con_tag)
    | CMatch(bl, _) ->
        let match_tag = tag () in
        CMatch(List.map (fun (pl, ae) -> 
        let tagged_pl = List.map (fun (ie, p) -> (helpI ie, helpPC p)) pl in
        (tagged_pl, helpA ae)) bl, match_tag)
  and helpPC (p: 'a cpattern) : tag cpattern =
    match p with
      | CPConstructor(name, p_opt, _) ->
          let c_tag = tag () in
          CPConstructor(name, (match p_opt with
            | None -> None
            | Some(x) -> Some(helpPI x)), c_tag)
      | CPTup(il, _) ->
          let t_tag = tag () in
          CPTup(List.map helpPI il, t_tag)
      | CPImm(i) -> CPImm(helpPI i)
  and helpPI (p : 'a immpattern) : tag immpattern =
    match p with
      | IPBlank _ -> IPBlank (tag ())
      | IPId (n, _) -> IPId (n, tag ())
      | IPLBool(b, _) -> IPLBool (b, tag ())
      | IPLInt(i, _) -> IPLInt (i, tag ())
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmNil _ -> ImmNil (tag ())
    | ImmId (x, _) -> ImmId (x, tag ())
    | ImmNum (n, _) -> ImmNum (n, tag ())
    | ImmBool (b, _) -> ImmBool (b, tag ())
  and helpTypD (typD: 'a type_decl) : tag type_decl =
    match typD with 
    | DType (str, typ, _) -> DType (str, helpTyp typ, tag ())
  and helpTyp (typ: 'a typ) : tag typ =
    match typ with 
    | TInt _ -> TInt(tag ())
    | TBool _ -> TBool(tag ())
    | TId (str, _) -> TId(str, tag ())
    | TFunction (t1, t2, _) -> TFunction(helpTyp t1, helpTyp t2, tag ())
    | TProduct (tlist, _) -> TProduct (List.map helpTyp tlist, tag ())
    | TAlgebric (tclist, _) -> TAlgebric ((List.map (fun (str, ctyp) -> (str, helpTyp ctyp)) tclist), tag())
  and helpP (p: 'a aprogram) : tag aprogram =
    match p with
    | AProgram (d, body, _) -> 
        AProgram (List.map helpTypD d, helpA body, 0)
  in
  helpP p
;;
