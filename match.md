# Compilation Added

- make sure we do the binds
- make sure compilation can keep track of the bail out point - (jump into another compilation step until we run out of cevalpattern)
- build the canonical variant mapping

## Compiling Match
- we should have some immexpr for our value to check
- for each match branch
    - check if the patten matches our immexpr
        - PBlank, PId matches everything
        - PLiteral is just checking for equality, no recursion
        - PCons means we check the constructor, then we recur into the associated pattern
        -> we can turn a tuple into a anf-y list of pattern, where each pattern is either an immediate or a tuple
    - if not, jump to next match (end of this match)
    - if it does, unpack the correct names
    - then compile the body aexpr
    - jump to the end of the match block

## Compiling constructors
- need dtypenv
- just put the things on the heap meow

## TODO

h- typechecking for runtime, function decels, seq
h- _ bindings typed

?- remove runtime type checks

- more complex cases and checks
- fix old tests with type (eww)

- bake a cake
- make the slides
    - redo presentation tomorrow
    - string bullshit
    - hear me out cake
- submit solutions
- play minecraft

