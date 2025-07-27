# Design Document for the-water-turned-the-compilers-gay compiler!

## Language

Final!!

![derpy snake eating egg](./egg.png)
isn't he so cute
### Concrete Syntax

```
<program>:
    | <decls> <expr>
    | <expr>
<decl>:
    | <type-decls> <fun-decls>
    | <type-decls>
    | <fun-decls>
<fun-decls>:
    | <fun-decl>
    | <fun-decl> and <fun-decls>
    | <fun-decl> <fun-decls>
<fun-decl>:
    | def IDENTIFIER ( <typed-ids> ) -> <type> : <expr>
    | def IDENTIFIER ( <ids> ) -> <type> : <expr>
    | def IDENTIFIER ( ) (<type>) : <exp>
<typed-ids>:
    | <typed-id>
    | <typed-id> <typed-ids>
<typed-id>:
    | <id> : <type>
<type-decls>:
    | <type-decl> <type-decls>
    | <type-decl>
<type-decl>:
    | type IDENTIFIER = <type>
<type>:
    | <builtin-type>
    | <function-type>
    | <algebric-type>
    | IDENTIFIER
<builtin-type>
    | int
    | bool
    | <types>
<function-type>
    | <types> -> <types>
<algebric-type>
    | CONSTRUCTOR
    | CONSTRUCTOR of <types>
    | CONSTRUCTOR of <types> | <algebric-type>
<types>:
    | <type>
    | <type> * <type>
<binop-expr>:
    | <imm>
    | <expr> <prim2> <expr>
    | <prim1> ( <expr> )
    | IDENTIFIER ( <exprs> )
    | IDENTIFIER ( )
    | ( <expr> )    
<expr>:
   | <tuple>
   | <tuple-get>
   | <tuple-set>
   | <expr> ; <expr>
   | let <bindings> in <expr>
   | let rec <bindings> in <expr>
   | if <expr> : <expr> else: <expr>
   | <binop-expr>
   | match IDENTIFIER with <match-patterns>
   | <construct-expr>
<construct-expr>
   | CONSTRUCTOR
   | CONSTRUCTOR (<exprs>)
<match-patterns>:
   | <match-pattern>
   | <match-pattern> | <match-patterns>
<match-pattern>:
   | <literal>
   | _
   | <IDENTIFIER>
   | <constructor-pattern>
   | (<patterns>)
<patterns>
   | <match-pattern>
   | <match-pattern>, <patterns>
<constructor-pattern>
   | CONSTRUCTOR (<patterns>)
   | CONSTRUCTOR(<patterns>)
   | CONSTRUCTOR 
<literal>
    | int
    | bool
<prim1>:
    | !
    | print
    | printStack
    | add1
    | sub1
<imm>:
    | NUMBER
    | IDENTIFIER
    | BOOL
<prim2>:
    | +
    | -
    | *
    | <
    | >
    | <=
    | >=
    | ==
    | &&
    | ||
<tuple>:
    | (<expr>, <expr>, ..., <expr>)
<tuple-get>:
    | <expr> [ NUMBER ]
<tuple-set>:
    | <tuple-get> := <expr>
<bind>:
    | _
    | IDENTIFIER
    | ( <binds> )
<binds>:
    | <bind>
    | <bind>, <binds>
<bindings>:
    | <bind> : <type> = <expr>
    | <bind> : <type> = <expr>, <bindings>
<exprs>:
    | <expr>
    | <expr>, <exprs>
```

### Where code is:
We decided to split up our code.
Utilitity used in multiple phases is placed in utils.ml

Wellformed is placed inside wellformed.ml
Desugar is in desuger.ml
Rename is in rename.ml
(Tag is in exprs)
ANF is in anf.ml
Locate Bindings is in allocation.ml
Codegen/compilation is in compile.ml 

We also have the runtime split up into:

main.c -> entrypoint code and runtime natives
snake.h/c -> code for working with snake vals specifically
gc.h/c -> garbage collection code

### Semantics

- binops are left to right associated
- If statements are based on numbers, the then-branch is evaluated if the condition is non-zero, and the else-branch gets evaluated if the condition was zero. Thus in Boa, zero behaves as a "false" and non-zero as a "true"
- The non-used branch in an IF statement is not executed
- Let behaves like let*. Some important things to note are that
   - No duplicate bindings in a single let statement
   - Duplicate bindings may exist if they are defined in different lets (shadows)
- Bool AND and OR short circuit

## Compilation Pipeline

### Pre-Parsing

Pre-parsing reads in a file. This step just turns in some input into a String.
```ocaml
File -> String
```

### Tokenizing
This is done through OCamls lexer and parser generators (ocamllex, ocamlyacc). See [https://ocaml.org/manual/5.3/lexyacc.html](https://ocaml.org/manual/5.3/lexyacc.html). It is handled in the parser.mly file which gets compiled to an ml file in the build.
```ocaml
String -> Token List
```

### Parsing

Converts a list of tokens into a s-expression. 

```ocaml
Token List -> Sexp
```

### Lexing

- Converts an sexp into an expr

```ocaml
Sexp -> Expr
```

- We will get a valid Expression, although it may not be well formed
- We will not have identifiers or bindings named "let, add/sub1", or named containing #

### Well formed-ness & scope checking

- All names are valid names in our Language
- Let bindings don't allow duplicates
- keywords aren't variable names

### Desugaring

- Each let will only have one binding
- There will be no AND, OR prim ops (short circuiting)

### Tagging

- Provides a unique tag to each expr
- Introduced so IF statement labels can be uniquely named
- Also used to generate unique names

### Renaming

- Introduces because in some cases, ANF can mess up with let rebinding
- Each variable will have a unique name!

### ANF

- Introduced to make binops work
- Stores intermediate values, parser gives us our order of operations and ANF ensures that result is calculatable
- Each value an operation uses will be immediate

### Tagging 2

- Needed so if statements can actually use tags in ASM

### Naive stack allocation

- allocates dumbly variables on the stack
- handles multiple names bound to different values in different nested environments by mapping an env to a name

### Compilation

- Compilation will produce valid ASM
- Compilation will generally not throw errors?
