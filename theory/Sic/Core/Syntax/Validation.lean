module

import Sic.Core.Syntax

/-!
# Validation of the Syntax

The examples of RFC 24, and two examples of the literature, written as terms of `Sic.Core.Syntax`,
each with its named term.
-/

namespace Sic.Core.Syntax.Validation

open Grade Term

/-!
The constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` and its type
`Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, in the context `A : U₀, B : U₀` of two type variables.
The index of a variable is the number of variables declared after it and in scope where it is used,
those of the context included:

- `A`, the type of `x`, is `var 1`, since `B` is declared after it;
- `B`, the type of `y`, is `var 1`, since `x` is declared after it;
- `x`, the body of the function, is `var 1`, since `y` is declared after it;
- `A`, the type of the body, is `var 3`, since `B`, `x` and `y` are declared after it.
-/

def constant : Term 0 2 := lam 𝟙 (var 1) (lam 𝟘 (var 1) (var 1))

def constantType : Term 0 2 := pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))

/-!
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` and its type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A`, closed, over the level variable `l`, which is `var 0`.
-/

def identity : Term 1 0 := lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 0) (var 0))

def identityType : Term 1 0 := pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1))

/-!
Two examples of the literature, beyond RFC 24, check the definitions on terms whose behavior is
known.
The combinators `K` and `S` are those of combinatory logic, where `S K K` behaves as the identity,
exercise 2.16 of [Hindley and Seldin](https://doi.org/10.1017/CBO9780511809835).
The Church numerals are those of System F, section 11.5.1 of
[Girard, Lafont and Taylor](https://www.paultaylor.eu/stable/prot.pdf), in the variant that takes
the function before the argument, at a level `l`.
All are closed, over the level variable `l`, which is `var 0`, and are terms over any number of
variables, so that they can be used in any context.
`𝟙 + 𝟙` is the grade of any number of uses.
-/

/--
`K = λ_𝟘 (A : U_l). λ_𝟘 (B : U_l). λ_𝟙 (x : A). λ_𝟘 (y : B). x`, polymorphic: its variables have the
indices of those of the constant function.
-/
def combinatorK : Term 1 n :=
  lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 1) (lam 𝟘 (var 1) (var 1))))

/-- `Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, the type of `K`. -/
def combinatorKType : Term 1 n :=
  pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))))

/-!
`S = λ_𝟘 (A : U_l). λ_𝟘 (B : U_l). λ_𝟘 (C : U_l). λ_𝟙 (x : Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C).
λ_𝟘 (y : Π^𝟘_𝟙 (a : A). B). λ_𝟙 (z : A). (x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)`, of the type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^{𝟙 + 𝟙}_𝟘 (B : U_l). Π^{𝟙 + 𝟙}_𝟘 (C : U_l).
Π^𝟘_𝟙 (x : Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C). Π^𝟘_𝟘 (y : Π^𝟘_𝟙 (a : A). B).
Π^𝟘_𝟙 (z : A). C`.
Its grades are ours, those that `S K K` needs: `K` does not use its second argument, so that `x`
takes its own with the grade `𝟘`, and `y`, and the second use of `z`, are erased, so that `z` is
used once at run time, while the untyped `S` duplicates it.
The indices of its variables:

- in the type of `x`, `A`, `B` and `C` are each `var 2`, after `B` and `C`, `C` and `a`, and `a`
  and `b`;
- in the type of `y`, `A` and `B` are each `var 3`, after `B`, `C` and `x`, and `C`, `x` and `a`;
- `A`, the type of `z`, is `var 4`, after `B`, `C`, `x` and `y`, and `C`, the type of the body, is
  `var 3`, after `x`, `y` and `z`;
- in the body, `x`, `y` and `z` are `var 2`, `var 1` and `var 0`.
-/

def combinatorS : Term 1 n :=
  lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0))
    (lam 𝟙 (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2))) (lam 𝟘 (pi 𝟙 𝟘 (var 3) (var 3))
      (lam 𝟙 (var 4) (app 𝟘 (app 𝟙 (var 2) (var 0)) (app 𝟙 (var 1) (var 0))))))))

def combinatorSType : Term 1 n :=
  pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 (𝟙 + 𝟙) (univ (.var 0))
    (pi 𝟙 𝟘 (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2))) (pi 𝟘 𝟘 (pi 𝟙 𝟘 (var 3) (var 3))
      (pi 𝟙 𝟘 (var 4) (var 3))))))

/-!
The numerals have the type `Nat_l = Π^{𝟙 + 𝟙}_𝟘 (X : U_l). Π^𝟘_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X).
Π^𝟘_𝟙 (x : X). X`, and the numeral `n` is `λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X).
λ_𝟙 (x : X). f ∘_𝟙 (… (f ∘_𝟙 x))`, with `n` applications of `f`.
In the bodies, `X`, `f` and `x` are `var 2`, `var 1` and `var 0`.
-/

/-- `Π^𝟘_𝟙 (y : X). X`, the type of `f`, after `X`. -/
def churchFunType : Term 1 (n + 1) := pi 𝟙 𝟘 (var 0) (var 1)

/-- `Nat_l`, where `x : X` is `var 1`, after `f`, and the type of the body is `var 2`. -/
def churchNat : Term 1 n :=
  pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi (𝟙 + 𝟙) 𝟘 churchFunType (pi 𝟙 𝟘 (var 1) (var 2)))

/-- `1 = λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X). f ∘_𝟙 x`. -/
def churchOne : Term 1 n :=
  lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1) (app 𝟙 (var 1) (var 0))))

/-- `2 = λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X). f ∘_𝟙 (f ∘_𝟙 x)`. -/
def churchTwo : Term 1 n :=
  lam 𝟘 (univ (.var 0))
    (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1) (app 𝟙 (var 1) (app 𝟙 (var 1) (var 0)))))

/--
`succ = λ_𝟙 (m : Nat_l). λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X).
f ∘_𝟙 (m ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)`, the `S` of Girard, Lafont and Taylor, where `m` is `var 3` in
the body.
-/
def churchSucc : Term 1 n :=
  lam 𝟙 churchNat (lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1)
    (app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 (var 3) (var 2)) (var 1)) (var 0))))))

/--
Two types of functions that differ only by a grade are different types, as `Π^𝟘_𝟙 (x : A). A` and
`Π^𝟘_{𝟙 + 𝟙} (x : A). A`, in the context `A : U₀`.
-/
example : pi 𝟙 𝟘 (var 0) (var 1) ≠ (pi (𝟙 + 𝟙) 𝟘 (var 0) (var 1) : Term 0 1) := by decide

end Sic.Core.Syntax.Validation
