module

public import Sic.Core.Typing
public import SicTest.Constant.Syntax

/-!
# The Constant Function: Typing

The type of the constant function of RFC 24, as a derivation.
-/

@[expose] public section

namespace SicTest.Constant.Typing

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Constant.Syntax

/-- The context `A : U₀, B : U₀` of the constant function. -/
def Γ₂ : Con 0 2 := .empty ∙ univ .zero ∙ univ .zero

theorem wfCon_Γ₂ : ⊢ Γ₂ := .snoc (.univ (.univ (.snoc (.univ (.univ .empty)))))

/--
The constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` has the type
`Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`.
-/
theorem hasType_constant : Γ₂ ⊢ constant : constantType :=
  -- `A : U₀` in `Γ₂`, `B : U₀` after `x : A`, and `A : U₀` after `y : B`.
  have hA : Γ₂ ⊢ var 1 : univ .zero := .var wfCon_Γ₂
  have hB : Γ₂ ∙ var 1 ⊢ var 1 : univ .zero := .var (.snoc (.univ hA))
  have hA' : Γ₂ ∙ var 1 ∙ var 1 ⊢ var 3 : univ .zero := .var (.snoc (.univ hB))
  have hPi := HasType.pi hB hA'
  .lam (.univ (.pi hA hPi)) (.lam (.univ hPi) (.var (.snoc (.univ hB))))

end SicTest.Constant.Typing
