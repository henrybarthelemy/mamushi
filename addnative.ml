open Exprs
open Utils
open Printf

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
   let add_native_lambdas (p : sourcespan program) =
    let wrap_native name arity =
      let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
      [ DFun
          ( name,
          (* TODO FIX THIS :/ *)
            List.map (fun name -> BNameTyped (name, TInt dummy_span, false, dummy_span)) argnames,
            (* fix native calls types :/ *)
            TInt dummy_span,
            EApp
              ( EId (name, dummy_span),
                List.map (fun name -> EId (name, dummy_span)) argnames,
                Native,
                dummy_span ),
            dummy_span ) ]
    in
    match p with
    | Program (t, declss, body, tag) ->
        Program
          ( t, List.fold_left
              (fun declss (name, arity) -> wrap_native name arity :: declss)
              declss supported_runtime_functions,
            body,
            tag )
  ;;
  
