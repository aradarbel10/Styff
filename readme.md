# Styff
A small functional language based on system Fω with pattern unifiction, implicit parameters, GADTs, and compilation to native.

### Example
```ocaml
data Nat : ∗ where
| zero : Nat
| succ : Nat → Nat

let three = succ (succ (succ zero))

data List (a : ∗) : ∗ where
| nil  : List a
| (::) : a → List a → List a

let nums : List Nat = zero :: succ zero :: succ (succ zero) :: three :: nil

(* pattern matching *)
let rec (+) (a : Nat) (b : Nat) : Nat =
  match a with
  | zero . b
  | succ a' . succ (a' + b)
  end

let rec (++) {T : ∗} (xs : List T) (ys : List T) : List T =
  match xs with
  | nil . ys
  | x :: xs' . x :: (xs' ++ ys)
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
    - both data parameters and indices
    - GADT syntax
    - shallow pattern matching
        - scoped type variables (without "dot patterns")
        - matching on indexed types
- user-defined infix operator
    - infix type formers
    - infix patterns
- compilation to javascript

### Future Ideas/TODOs
- builtins
    - int, bool, float
    - plus, minus, times, div (for both ints and floats)
    - and, or, if
    - comparisons

- bring back `∀` syntax sugar

- logging (for debugging and good errors)

- small & super simple module system and stdlib