# Implifit
A type checker based on system F-omega with pattern unifiction and implicit parameters

### Current Features
- function definitions
    - local definitions `let f = ... in ...`
    - recursive functions `let rec`
- type definitions `type t = ...`
    - local type definitions `let type t = ... in ...`
    - type-level lambdas
- rank N polymorphism `forall x y z . t2` written as `[x y z] → t2`
    - optionally-explicit instantiation `e [t]`
- higher kinded quantification
    - kind annotations on type binders
- data declarations
    - GADT syntax
    - shallow pattern matching
        - scoped type variables
        - matching on indexed types (super scuffed implementation. no coverage checking, no escape checking, no linearity checking, do not trust until rewrite)
- user-defined infix operator
    - infix type formers (but no constructors yet)

### Future Ideas
- allow overloading `*` (collision with kind star)
- bring back `∀` syntax sugar

- error reporting
    - from parsing
    - from typechecking

- annotate core types with kinds
- check with bidi to accept more programs
- small & super simple module system and stdlib

- backend