module

import Sic.Core.Injectivity
import all SicTest.TypeVariable.Reducibility.Introductions.Function

/-!
# A Type Variable: Injectivity

`Sic.Core.Typing` does not equate the type `(λ_p (X : U_l). X) ∘_p A`, which is equal to the neutral
type `A`, to a type of functions, and does not equate two types of functions whose grades differ.
-/

namespace SicTest.TypeVariable.Injectivity

open Sic.Core Sic.Grade Sic.Core.Term SicTest.TypeVariable.Reducibility.LogicalRelation
  SicTest.TypeVariable.Reducibility.Introductions.Function

/-- `(λ_p (X : U_l). X) ∘_p A` is equal to `A`, by `(β)`. -/
theorem typeEq_idA : ΓA ⊢ idA p ≡ var 0 :=
  -- `U_l : U_{l + 1}` in `ΓA` and after `X : U_l`, and `X : U_l` after `X`.
  have hU : ΓA ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ wfCon_ΓA
  have hΓ : ⊢ ΓA ∙ univ (.var 0) := .snoc (.univ hU)
  have hU' : ΓA ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ hΓ
  have hPi := HasType.pi (p := p) (q := 𝟘) hU hU'
  .univ (.beta (.univ hPi) (.var (x := 0) hΓ) (.var wfCon_ΓA))

/-- `(λ_p (X : U_l). X) ∘_p A` and `Π^q_p' (x : A). A` are not equal types: `A` is neutral. -/
example : ¬ ΓA ⊢ idA p ≡ pi p' q (var 0) (var 1) := fun h =>
  nomatch (typeEq_idA.symm.trans h).inv_ne .var .pi

/-- `Π^q_𝟘 (x : A). A` and `Π^q_𝟙 (x : A). A` are not equal types: their grades differ. -/
example : ¬ ΓA ⊢ pi 𝟘 q (var 0) (var 1) ≡ pi 𝟙 q (var 0) (var 1) := fun h =>
  absurd h.pi_inj.1 (by decide)

end SicTest.TypeVariable.Injectivity
