# Styff
A small functional language based on system Fω with pattern unifiction, implicit parameters, GADTs, and compilation to native.

### Example
```ocaml
data Nat : ∗ where
| zero : Nat
| succ : Nat → Nat

let three = succ (succ (succ zero))

data List : ∗ → ∗ where
| nil  : {a} → List a
| (::) : {a} → a → List a → List a

let nums : List Nat = zero :: succ zero :: succ (succ zero) :: three :: nil

(* pattern matching *)
let rec nat_add (a : Nat) (b : Nat) : Nat =
  match a with
  | zero . b
  | succ a' . succ (nat_add a' b)
  end

let rec list_concat {T : ∗} (xs : List T) (ys : List T) : List T =
  match xs with
  | nil . ys
  | x :: xs' . x :: (list_concat xs' ys)
  end
```

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
- compilation to javascript

### Future Ideas/TODOs
- builtins
    - int, bool, float
    - plus, minus, times, div (for both ints and floats)
    - and, or, if
    - comparisons

- datatype parameters
- bring back `∀` syntax sugar

- error reporting
    - from parsing
    - from typechecking
- logging (for debugging and good errors)

- small & super simple module system and stdlib