module

import Sic.Core.Reduction
import all SicTest.Identity.Syntax

/-!
# The Polymorphic Identity: Reduction

The polymorphic identity applied to a type reduces to the identity of that type.
-/

namespace SicTest.Identity.Reduction

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def Γ₁ : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_Γ₁ : ⊢ Γ₁ := .snoc (.univ (.univ .empty))

/--
The polymorphic identity applied to a type, `(λ_𝟘 (A : U_l). λ_𝟙 (x : A). x) ∘_𝟘 A`, reduces in one
step to the identity `λ_𝟙 (x : A). x` of `A`, a weak head normal form.
-/
example : Γ₁ ⊢ app 𝟘 identity.wk1 (var 0) ↘ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`, as for the type of
  -- the polymorphic identity, but in `Γ₁`.
  have hU : Γ₁ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ wfCon_Γ₁
  have hA : Γ₁ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ hU))
  have hA' : Γ₁ ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hA))
  have hPi : Γ₁ ∙ univ (.var 0) ⊢ pi 𝟙 𝟘 (var 0) (var 1) : univ (.var 0 ⊔ .var 0) := .pi hA hA'
  have hIdType := HasType.pi (p := 𝟘) (q := 𝟙 + 𝟙) hU hPi
  -- `A : U_l` in `Γ₁`, and `A : U_l` after `x : A`, for the identity of `A`.
  have hB : Γ₁ ⊢ var 0 : univ (.var 0) := .var wfCon_Γ₁
  have hB' : Γ₁ ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hB))
  ⟨.step (.beta (.univ hIdType) (.lam (.univ hPi) (.var (.snoc (.univ hA)))) hB)
    (.refl (.lam (.univ (.pi hB hB')) (.var (.snoc (.univ hB))))), .lam⟩

end SicTest.Identity.Reduction
