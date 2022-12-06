# Styff
A type checker based on system F-omega with pattern unifiction, implicit parameters, and GADTs.

### Current Features
- function definitions
    - local definitions `let f = ... in ...`
    - recursive functions `let rec`
- type definitions `type t = ...`
    - local type definitions `let type t = ... in ...`
    - type-level lambdas
- rank N polymorphism `forall x y z . t2` written as `{x y z} → t2`
    - optionally-explicit instantiation `e {t}`
- higher kinded quantification
    - kind annotations on type binders
- data declarations
    - GADT syntax
    - shallow pattern matching
        - scoped type variables (without "dot patterns")
        - matching on indexed types
- user-defined infix operator
    - infix type formers

### Future Ideas/TODOs
- builtins
    - int, bool, float
    - plus, minus, times, div (for both ints and floats)
    - and, or, if
    - comparisons

    - builtin declaration (maybe like `{@ BUILTIN nat: Nat, zero, succ @}`)

- datatype parameters
- bring back `∀` syntax sugar

- error reporting
    - from parsing
    - from typechecking
- logging (for debugging and good errors)

- small & super simple module system and stdlib

- backend