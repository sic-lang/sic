module

public import Sic.Core.Reduction

/-!
# A Type Variable: Reduction

A type that reduces as a term of its universe reduces as a type.
-/

@[expose] public section

namespace SicTest.TypeVariable.Reduction

open Sic.Core Sic.Grade Sic.Core.Term

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def ΓA : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_ΓA : ⊢ ΓA := .snoc (.univ (.univ .empty))

/--
The identity of the types of `U_l` applied to `A`, `(λ_𝟘 (X : U_l). X) ∘_𝟘 A`, reduces as a type to
the type variable `A`, by `(β)`.
-/
example : ΓA ⊢ app 𝟘 (lam 𝟘 (univ (.var 0)) (var 0)) (var 0) ⇒* var 0 :=
  -- `U_l : U_{l + 1}` in `ΓA` and after `X : U_l`, and `X : U_l` after `X`.
  have hU : ΓA ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ wfCon_ΓA
  have hΓ : ⊢ ΓA ∙ univ (.var 0) := .snoc (.univ hU)
  have hU' : ΓA ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ hΓ
  have hPi := HasType.pi (p := 𝟘) (q := 𝟘) hU hU'
  have hA : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA
  have hβ : ΓA ⊢ app 𝟘 (lam 𝟘 (univ (.var 0)) (var 0)) (var 0) ⇒ var 0 : univ (.var 0) :=
    .beta (.univ hPi) (.var (x := 0) hΓ) hA
  .step (.univ hβ) (.refl (.univ hA))

end SicTest.TypeVariable.Reduction
