module

import Sic.Core.Substitution
import SicTest.ChurchNumerals.Syntax

/-!
# The Church Numerals: Substitution

The closed `Nat_l` moved under binders, and the step of the successor.
-/

@[expose] public section

namespace SicTest.ChurchNumerals.Substitution

open Sic.Core Sic.Grade Sic.Core.Term SicTest.ChurchNumerals.Syntax

/--
`Nat_l` replaces a type variable under binders:
`(Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A)[Nat_l/A]` is
`Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : Nat_l). Π^𝟘_𝟘 (y : B). Nat_l`, where the closed `Nat_l` moves under the
binders unchanged.
-/
example : (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))) : Term 1 1).instantiate
    churchNat = pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 churchNat (pi 𝟘 𝟘 (var 1) churchNat)) := rfl

/--
The step `succ ∘_𝟙 1` of the Church numerals replaces `m` by `1` under the binders of `X`, `f` and
`x`: the body of `succ` becomes `λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X).
f ∘_𝟙 (1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)`.
-/
example : (lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1)
      (app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 (var 3) (var 2)) (var 1)) (var 0))))) :
      Term 1 1).instantiate churchOne =
    lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1)
      (app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchOne (var 2)) (var 1)) (var 0))))) := rfl

end SicTest.ChurchNumerals.Substitution
