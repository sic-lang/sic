module

import Sic.Core.Syntax

/-!
# The Church Numerals

The Church numerals of System F, section 11.5.1 of
[Girard, Lafont and Taylor](https://www.paultaylor.eu/stable/prot.pdf), in the variant that takes
the function before the argument, at a level `l`.
They are closed, over the level variable `l`, which is `var 0`, and are terms over any number of
variables, so that they can be used in any context.
`𝟙 + 𝟙` is the grade of any number of uses.
-/

namespace SicTest.ChurchNumerals.Syntax

open Sic.Core Sic.Grade Sic.Core.Term

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

end SicTest.ChurchNumerals.Syntax
