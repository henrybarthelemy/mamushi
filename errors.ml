open Printf
open Exprs
open Pretty

(* TODO: Define any additional exceptions you want *)
exception ParseError of string (* parse-error message *)

exception UnboundId of string * sourcespan (* name, where used *)

exception UnboundFun of string * sourcespan (* name of fun, where used *)

exception ShadowId of string * sourcespan * sourcespan (* name, where used, where defined *)

exception DuplicateId of string * sourcespan * sourcespan (* name, where used, where defined *)

exception DuplicateFun of string * sourcespan * sourcespan (* name, where used, where defined *)

exception Overflow of int64 * sourcespan (* value, where used *)

exception Arity of int * int * sourcespan (* intended arity, actual arity, where called *)

exception NotYetImplemented of string (* TODO: Message to show *)

exception Unsupported of string * sourcespan

exception InternalCompilerError of string (* Major failure: message to show *)

exception LetRecNonFunction of sourcespan bind * sourcespan (* name binding, where defined *)

exception ShouldBeFunction of string * sourcespan (* name, where defined, actual typ *)

exception
  DeclArity of string * int * int * sourcespan (* name, num args, num types, where defined *)

exception DuplicateTypeId of string * sourcespan * sourcespan (* name, where first defined, where second defined *)

exception DuplicateConstructorNames of string * sourcespan (* name, where defined *)

exception TypeMismatch of unit typ * unit typ * sourcespan (* type actual, type expected, where *)

(* used when actual type not known but its not correct *)
exception NotOfExpectedType of unit typ * sourcespan (* type expected, where *)

exception UndefinedConstructor of string * sourcespan (* constructor, where *)

exception InvalidPattern of sourcespan (* at what match statement *)

exception ConstructorArgumentsMismatch of string * int * int * sourcespan (* constructor name, expected arity, actual arity, where used *)

exception UndefinedType of string * sourcespan (* type name, where used *)

exception TypeApplicationArityMismatch of int * int * sourcespan (* expected arity, actual arity, where used *)

exception LambdaGivenNonFunction of unit typ * sourcespan (* actual type, where *)

exception IndexOutOfBounds of int * int * sourcespan (* index tried, max index, location *)

exception NotATuple of sourcespan (* action which was expected on a tuple type happened a non tuple at location *)

let known_compiletime_exn exn =
  match exn with
  | ParseError _
  | NotYetImplemented _
  | InternalCompilerError _
  | UnboundId _
  | UnboundFun _
  | ShadowId _
  | DuplicateId _
  | DuplicateFun _
  | Overflow _
  | DeclArity _
  | ShouldBeFunction _
  | LetRecNonFunction _
  | Unsupported _
  | DuplicateTypeId _
  | DuplicateConstructorNames _
  | TypeMismatch _
  | NotOfExpectedType _
  | InvalidPattern _ 
  | UndefinedConstructor _
  | ConstructorArgumentsMismatch _
  | UndefinedType _
  | TypeApplicationArityMismatch _
  | LambdaGivenNonFunction _
  | IndexOutOfBounds _
  | NotATuple _
  | Arity _ -> true
  | _ -> false
;;

let print_error exn =
  match exn with
  | ParseError msg -> msg
  | NotYetImplemented msg -> "Not yet implemented: " ^ msg
  | Unsupported (msg, loc) -> sprintf "Unsupported: %s at <%s>" msg (string_of_sourcespan loc)
  | InternalCompilerError msg -> "Internal Compiler Error: " ^ msg
  | UnboundId (x, loc) ->
      sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | UnboundFun (x, loc) ->
      sprintf "The function name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | ShadowId (x, loc, existing) ->
      sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | DuplicateId (x, loc, existing) ->
      sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | DuplicateFun (x, loc, existing) ->
      sprintf "The function name %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | Overflow (num, loc) ->
      sprintf "The number literal %Ld, used at <%s>, is not supported in this language" num
        (string_of_sourcespan loc)
  | Arity (expected, actual, loc) ->
      sprintf "The function called at <%s> expected an arity of %d, but received %d arguments"
        (string_of_sourcespan loc) expected actual
  | DeclArity (name, num_args, num_types, loc) ->
      sprintf "The function %s, defined at %s, has %d arguments but only %d types provided" name
        (string_of_sourcespan loc) num_args num_types
  | ShouldBeFunction (name, loc) ->
      sprintf "The function %s, at %s, should be function" name (string_of_sourcespan loc)
  | LetRecNonFunction (bind, loc) ->
      sprintf "Binding error at %s: Let-rec expected a name binding to a lambda; got %s"
        (string_of_sourcespan loc) (string_of_bind bind)
  (* type errors within type declerations *)
  | DuplicateTypeId (name, loc1, loc2) ->
    sprintf "The type %s, is both defined at <%s> and <%s>" name
      (string_of_sourcespan loc2) (string_of_sourcespan loc1)
  | DuplicateConstructorNames (name, loc) ->
      sprintf "There are two constructors with name %s, defined at <%s>" name
        (string_of_sourcespan loc)
  (* type errors within expressions *)
  | TypeMismatch (ta, te, loc) ->
      sprintf "Got %s instead of type %s at %s" (string_of_type ta)
        (string_of_type te) (string_of_sourcespan loc)
  | NotOfExpectedType (te, loc) ->
      sprintf "Expected to see %s at %s but didn't" (string_of_type te)
        (string_of_sourcespan loc)
  | UndefinedConstructor (constructor, loc) ->
      sprintf "The constructor named %s, as used at <%s> wasn't found" constructor
        (string_of_sourcespan loc)
  | ConstructorArgumentsMismatch (constructor, expected, actual, loc) ->
      sprintf "The constructor %s, used at <%s>, expected %d arguments but got %d" constructor
        (string_of_sourcespan loc) expected actual
  | UndefinedType (type_name, loc) ->
      sprintf "The type %s, used at <%s>, is not defined" type_name
        (string_of_sourcespan loc)
  | TypeApplicationArityMismatch (expected, actual, loc) ->
      sprintf "The type used at <%s>, expected %d type arguments but got %d"
        (string_of_sourcespan loc) expected actual
  | InvalidPattern (loc) -> 
      sprintf "The match at <%s>, had an invalid pattern" (string_of_sourcespan loc)
  | LambdaGivenNonFunction (typ, loc) ->
      sprintf "The lambda used at <%s>, is expected type function but was provided %s" (string_of_sourcespan loc)
      (string_of_type typ)
  | IndexOutOfBounds (id1, max, loc) ->
      sprintf "The index %s used at <%s> was out of bounds for tuple [0, %s)" (string_of_int id1)
      (string_of_sourcespan loc) (string_of_int max)
  | NotATuple (loc) ->
      sprintf "Attempted to do tuple action on non-tuple at %s" (string_of_sourcespan loc)
  | _ -> sprintf "%s" (Printexc.to_string exn)
;;

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list = List.map print_error exns
