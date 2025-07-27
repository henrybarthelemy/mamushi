# To Do List for the-water-turned-the-compilers-gay

## Final Project Scope

- The ability to define ML-like alegbraic types
    - product type: structs
    - sum type: tagged unions (enums with associated data)

## Final Project todo

- Parsing for match expressions
- Parsing for adding type information to preexisting stuff (definitions)
    - this will involve having to change ALL our tests... a bit tedius and brain dead but needs to be done
- Add parsing for nested tests (int * (int * int))
- Add types for well formed (perhaps a difference type checking phase), desugar, and figure out how to get them into a type environment/anfing
    - Good errors for duplicate IDs for types, invalid types
    - Deal with how to introduce types to function definitions lambdas, and maybe applications?
- Deal with tagging/untagging/renaming stuff within types
- Parsing for creating and constructing algebric types
- Think about code gen for match expressions, we can maybe desugar it to a bunch of lambdas and then dispatch the application?????
- so many tests

### Static Typing
- Type annotations in parser
- runtime implications of typing (input, print)
- type checker phase - after well formed
- id->type env builder - before type checking
- propergate aforementioned env through code
- remove is-type fully
- update tests with new annotations
- type arity things???

### Algebric types
- tagged untions Parsing
- constructors all through pipeline
- match statements all through pipeline
    - compile match statements?
    - explore decision tree option
- locally defined type env (for info)
- universal AT layout with variant SV, type SV, associated data
- well defined semantics in a doc somewhere
- update tagging to support AT

### Administrative
- presentation
- cake

## Misc

- the RDX thing in set (tldr we use rdx to cheat) (we will need to fix this by racer)
- arbitrary arity tail calls
- cleanup runtime things like error messages
- Garter feedback
- the nil thing
- _ in lambdas check
- make tuple errors correct (with sets and such)
- desugaring a smaller tuple than the tuple size
- fix the renaming bug with print things!
- moving the code to align stack causes bad segfaults
