# Pattern Unification
We represent types with DeBruijn levels. Their grammar is
```
τ ::= #n            (var)
    | ?m            (metavar)
    | ∀ x . τ       (binder)
    | τ → σ         (arrow)
```

examples
```
ex1
named       ∀ x y z .  z →  x →  y
unnamed     ∀ _ _ _ . #2 → #0 → #1

ex2
named       ∀ x .  x → (∀ y .  y →  x)
unnamed     ∀ _ . #0 → (∀ _ . #1 → #0)
```

We define an operation on types called *instantiation* by the following
```
($$) : {h : Lvl} → Type → Type → Type
#n $$ x      := x        when h = n
                #(n-1    when h ≠ n
(τ → σ) $$ x := (τ $$ x) → (σ $$ x)
(∀_. τ) $$ x := ∀_. (τ $$ x)
```

for example,
```
h=0;        ex1 $$ int = ∀ y z . z → int → y
```

theorem:
under |Γ|=h, τ $$ #h = τ

## Renaming
Have a type τ which is well-formed under context Γ.
A renaming θ to a new context Δ consists of a map { i ↦ j },
every i is a variable in Γ, and every j is a variable in Δ.

We define substitution application τ[θ] by inductively traversing the type.
In practice, renaming can be combined with an `occurs` check.