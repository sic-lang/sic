module

public import Sic.Core.UsageReduction
import Sic.Core.UsageInference
import SicTest.Common.Usage

/-!
# Usage Reduction

The preservation of the usage by reduction, an admissible property of RFC 24, on a redex that drops
its argument: in the context `A : U₀, y : A`, the term `(λ_ω (x : A). y) ∘_ω y` uses `y` once in the
body of the abstraction and any number of times as the argument, and reduces to `y`, which uses `y`
once.
Every usage of the redex is a usage of its reduct, but not conversely: the reduct is well used with
`y` linear, the redex is not.
-/

@[expose] public section

namespace SicTest.Rfc24.UsageReduction

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Common.Usage

/-- The grade `⟨ω, ω⟩` of an unrestricted parameter. -/
def unrestricted : Grade := ⟨.omega, .omega, by decide⟩

/-- The context `A : U₀, y : A`. -/
def Γ : Con 0 2 := .empty ∙ univ .zero ∙ var 0

/-- `(λ_ω (x : A). y) ∘_ω y`, where `x` is the innermost variable in the body. -/
def redex : Term 0 2 := app unrestricted (lam unrestricted (var 1) (var 1)) (var 0)

theorem wfCon_Γ : ⊢ Γ :=
  have hU : Con.empty ∙ univ .zero ⊢ var 0 : univ .zero := .var (.snoc (.univ (.univ .empty)))
  .snoc (.univ hU)

/-- The redex reduces to `y` by `(β)`, at the type `A`. -/
theorem termRed_redex : Γ ⊢ redex ⇒ var 0 : var 1 :=
  have hA : Γ ⊢ var 1 : univ .zero := .var wfCon_Γ
  have hx : ⊢ Γ ∙ var 1 := .snoc (.univ hA)
  -- `A` after `x`, the type of the body `y`.
  have hB : Γ ∙ var 1 ⊢ var 2 : univ .zero := .var hx
  .beta (q := 𝟘) (.univ (.pi hA hB)) (.var hx) (.var wfCon_Γ)

/-- The redex uses `y` with `𝟙 + ω`, at most, which is `ω`. -/
theorem usage_redex_iff : γ ▶[𝟙𝟙ᵐ] redex ↔ γ ≤ 𝟘ᶜ ∙ 𝟘 ∙ unrestricted :=
  usage_iff_le (by decide)

/-- The reduction keeps the usage of the redex. -/
example : 𝟘ᶜ ∙ 𝟘 ∙ unrestricted ▶[𝟙𝟙ᵐ] (var 0 : Term 0 2) :=
  (usage_redex_iff.2 (le_refl _)).termRed termRed_redex

/-- The reduct is well used with `y` linear, which the redex is not. -/
theorem usage_linear :
    (𝟘ᶜ ∙ 𝟘 ∙ 𝟙 ▶[𝟙𝟙ᵐ] (var 0 : Term 0 2)) ∧ ¬ (𝟘ᶜ ∙ 𝟘 ∙ 𝟙 ▶[𝟙𝟙ᵐ] redex) :=
  ⟨by decide, fun h => absurd (usage_redex_iff.1 h) (by decide)⟩

end SicTest.Rfc24.UsageReduction
