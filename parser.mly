%{
open Exprs

let full_span() = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
let tok_span(start, endtok) = (Parsing.rhs_start_pos start, Parsing.rhs_end_pos endtok)

%}

%token <int64> NUM
%token <string> ID CNAME
%token DEF ANDDEF ADD1 SUB1 LPARENSPACE LPARENNOSPACE RPAREN MATCH WITH LBRACK RBRACK RARROW OF LET IN EQUAL PIPE COMMA PLUS MINUS TIMES IF COLON ELSECOLON EOF INT BOOL TYPE (* PRINT PRINTSTACK *) TRUE FALSE ISBOOL ISNUM ISTUPLE EQEQ LESSSPACE GREATER LESSEQ GREATEREQ AND OR NOT COLONEQ SEMI LAMBDA (* BEGIN END SHADOW *) REC UNDERSCORE

%right SEMI
%left COLON COLONEQ
%left PLUS MINUS TIMES GREATER LESSSPACE GREATEREQ LESSEQ EQEQ AND OR
%left LPARENNOSPACE


%type <(Lexing.position * Lexing.position) Exprs.program> program

%start program

%%

const :
  | NUM { ENumber($1, full_span()) }
  | TRUE { EBool(true, full_span()) }
  | FALSE { EBool(false, full_span()) }


terminal_typ :
  | INT { TInt(full_span()) }
  | BOOL { TBool(full_span()) }
  | ID { TId($1, full_span()) }

typ_list : 
  | terminal_typ { [$1] }
  | terminal_typ TIMES typ_list { $1 :: $3 }

constructor_def:
  | PIPE CNAME { ($2, TProduct([], full_span())) }
  | PIPE CNAME OF typ_list {
    let typ =
      match $4 with
      | [t] -> t
      | ts -> TProduct(ts, full_span())
    in 
    ($2, typ) 
    }

constructors_def:
  | constructor_def { [$1] }
  | constructor_def constructors_def { $1 :: $2 } 

algebric_type :
  | constructors_def { TAlgebric($1, full_span()) }

typ :
  | algebric_type { $1 }
  | typ_list RARROW typ {
    let lhs =
      match $1 with
      | [t] -> t
      | ts -> TProduct(ts, full_span())
    in
    TFunction(lhs, $3, full_span())
  }
  | typ_list {
    match $1 with
    | [t] -> t  
    | ts -> TProduct(ts, full_span())
  }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  (* | PRINT { Print } *)
  (* | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | ISTUPLE { IsTuple } *)
  (* | PRINTSTACK { PrintStack } *)

bindings :
  | bind EQUAL expr { [($1, $3, full_span())] }
  | bind EQUAL expr COMMA bindings { ($1, $3, tok_span(1, 3))::$5 }

namebindings :
  | namebind EQUAL expr { [($1, $3, full_span())] }
  | namebind EQUAL expr COMMA namebindings { ($1, $3, tok_span(1, 3))::$5 }

expr :
  | LET bindings IN expr { ELet($2, $4, full_span()) }
  | LET REC namebindings IN expr { ELetRec($3, $5, full_span()) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, full_span()) }
  (* | BEGIN expr END { $2 } *)
  | binop_expr SEMI expr { ESeq($1, $3, full_span()) }
  | binop_expr { $1 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

(* two or more exprs in a tuple now *)
tuple_expr :
  | LPARENNOSPACE expr COMMA exprs RPAREN { ETuple($2::$4, full_span()) }
  | LPARENSPACE expr COMMA exprs RPAREN { ETuple($2::$4, full_span()) }

id :
  | ID %prec COLON { EId($1, full_span()) }


prim2 :
  | PLUS { Plus }
  | MINUS { Minus }
  | TIMES { Times }
  | AND { And }
  | OR { Or }
  | GREATER { Greater }
  | GREATEREQ { GreaterEq }
  | LESSSPACE { Less }
  | LESSEQ { LessEq }
  | EQEQ { Eq }

binop_expr :
  | binop_expr prim2 binop_operand %prec PLUS { EPrim2($2, $1, $3, full_span()) }
  | binop_operand COLONEQ binop_expr %prec COLONEQ {
      match $1 with
      | EGetItem(lhs, idx, _) -> ESetItem(lhs, idx, $3, full_span())
      | _ -> raise Parsing.Parse_error
    }
  | binop_operand %prec PLUS { $1 } 

binop_operand :
  // Primops
  | prim1 LPARENNOSPACE expr RPAREN { EPrim1($1, $3, full_span()) }
  // Tuples
  | tuple_expr { $1 }
  // enforce that get index _is_ a number index
  | binop_operand LBRACK NUM RBRACK { EGetItem($1, ENumber($3, tok_span(3, 4)), full_span()) }
  // Function calls
  | binop_operand LPARENNOSPACE exprs RPAREN %prec LPARENNOSPACE { EApp($1, $3, Unknown, full_span()) }
  | binop_operand LPARENNOSPACE RPAREN %prec LPARENNOSPACE { EApp($1, [], Unknown, full_span()) }
  // Parentheses
  | LPARENSPACE expr RPAREN { $2 }
  | LPARENNOSPACE expr RPAREN { $2 }
  // Lambdas
  | LPARENNOSPACE LAMBDA LPARENNOSPACE binds RPAREN RARROW typ COLON expr RPAREN { ELambda($4, $7, $9, full_span()) }
  | LPARENNOSPACE LAMBDA LPARENSPACE binds RPAREN RARROW typ COLON expr RPAREN { ELambda($4, $7, $9, full_span()) }
  | LPARENNOSPACE LAMBDA RARROW typ COLON expr RPAREN { ELambda([], $4, $6, full_span()) }
  | LPARENSPACE LAMBDA LPARENNOSPACE binds RPAREN RARROW typ COLON expr RPAREN { ELambda($4, $7, $9, full_span()) }
  | LPARENSPACE LAMBDA LPARENSPACE binds RPAREN RARROW typ COLON expr RPAREN { ELambda($4, $7, $9, full_span()) }
  | LPARENSPACE LAMBDA RARROW typ COLON expr RPAREN { ELambda([], $4, $6, full_span()) }
  // Constructor
  | CNAME LPARENNOSPACE exprs RPAREN { EConstructor ($1, $3, full_span()) }
  | CNAME LPARENSPACE exprs RPAREN { EConstructor ($1, $3, full_span()) }
  | CNAME LPARENSPACE RPAREN { EConstructor ($1, [], full_span()) }
  | CNAME LPARENNOSPACE RPAREN { EConstructor ($1, [], full_span()) }
  | CNAME { EConstructor ($1, [], full_span()) }
  // Match 
  // EMatch of 'a expr * ('a pattern * 'a expr) list * 'a
  | MATCH expr WITH match_branches { EMatch ($2, $4, full_span()) }
  // Simple cases
  | const { $1 }
  | id { $1 }

literal :
  | NUM { LInt($1, full_span()) }
  | TRUE { LBool(true, full_span()) }
  | FALSE { LBool(false, full_span()) }

pattern:
  | UNDERSCORE { PBlank (full_span()) }
  | literal { PLiteral ($1, full_span()) }
  | ID { PId ($1, full_span()) }
  | CNAME { PConstructor($1, [], full_span()) }
  | CNAME LPARENNOSPACE patterns RPAREN { PConstructor($1, $3, full_span()) }
  | CNAME LPARENSPACE patterns RPAREN { PConstructor($1, $3, full_span()) }
  | LPARENSPACE patterns RPAREN { PTup ($2, full_span()) }

patterns:
  | pattern { [$1] }
  | pattern COMMA patterns { $1 :: $3 }

match_branches : 
  | PIPE pattern RARROW expr { [($2, $4)] }
  | PIPE pattern RARROW expr match_branches { [($2, $4)] @ $5 }

type_decl : 
  | TYPE ID EQUAL typ { DType($2, $4, full_span()) }

type_decls:
  | { [] }
  | type_decl type_decls { $1::$2 }

decl :
  | DEF ID LPARENNOSPACE RPAREN RARROW typ COLON expr { DFun($2, [], $6, $8, full_span()) }
  | DEF ID LPARENNOSPACE binds RPAREN RARROW typ COLON expr { DFun($2, $4, $7, $9, full_span()) }

binds :
  | bind { [$1] }
  | bind COMMA binds { $1::$3 }

bind :
  | namebind { $1 }
  | blankbind { $1 }
  | LPARENNOSPACE binds RPAREN { BTuple($2, full_span()) }
  | LPARENSPACE binds RPAREN { BTuple($2, full_span()) }

blankbind :
  | UNDERSCORE %prec SEMI { BBlank(full_span()) }

namebind :
  | ID COLON typ %prec SEMI { BName($1, $3, false, full_span()) }
  (* | SHADOW ID %prec SEMI { BName($2, true, full_span()) } *)

declgroup :
  | decl { [$1] }
  | decl ANDDEF declgroup { $1::$3 }

decls :
  | { [] }
  | declgroup decls { $1::$2 }

program :
  | type_decls decls expr EOF { Program($1, $2, $3, full_span()) }
%%
