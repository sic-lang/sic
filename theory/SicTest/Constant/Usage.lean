module

import Sic.Core.Usage
import all SicTest.Constant.Syntax
import all SicTest.GradeVector

/-!
# The Constant Function: Usage

The usage of the constant function of RFC 24 and of its type, as derivations, in every mode.
The vectors are over the context `A : U₀, B : U₀`, the grade of `B` last, since it is the innermost
variable.
-/

namespace SicTest.Constant.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Constant.Syntax
  SicTest.GradeVector

/--
The constant function uses neither `A` nor `B`, since the types that its abstractions carry use no
variable: its body uses `x` with the grade `𝟙` of the outer abstraction, and `y` never.
-/
theorem usage_constant : 𝟘ᶜ ▶[m] constant :=
  .lam (.lam (.sub .var (by cases m <;> decide)))

/--
The usage of `usage_constant` is the greatest: the constant function is well used exactly with the
vectors below `𝟘ᶜ`, whatever its mode.
-/
theorem usage_constant_iff : γ ▶[m] constant ↔ γ ≤ 𝟘ᶜ :=
  ⟨fun h =>
    have ⟨_, ht, hγ⟩ := h.inv_lam
    have ⟨_, hx, hδ⟩ := ht.inv_lam
    GradeVector.le_trans hγ <| GradeVector.le_trans (le_tail hδ) <|
      GradeVector.le_trans (tail_mono (le_tail hx.inv_var)) (by cases m <;> decide),
    fun h => .sub usage_constant h⟩

/--
The type of the constant function uses `A` twice, as the domain of `x` and as the type of the
result, and `B` never, as the domain of `y`, whose grade is `𝟘`; it does not use `x` or `y`, whose
grades in the type are `𝟘`.
-/
theorem usage_constantType : 𝟘ᶜ ∙ (⌜m⌝ + ⌜m⌝) ∙ 𝟘 ▶[m] constantType :=
  -- `A`, after `B`, `x` and `y`, then `Π^𝟘_𝟘 (y : B). A`, after `B` and `x`.
  have hA : 𝟘ᶜ ∙ ⌜m⌝ ∙ 𝟘 ∙ 𝟘 ∙ (⌜m⌝ * 𝟘) ▶[m] var 3 := .sub .var (by cases m <;> decide)
  have hB : 𝟘ᶜ ∙ ⌜m⌝ ∙ 𝟘 ∙ (⌜m⌝ * 𝟘) ▶[m] pi 𝟘 𝟘 (var 1) (var 3) :=
    .sub (.pi .var hA) (by cases m <;> decide)
  .sub (.pi .var hB) (by cases m <;> decide)

/--
The usage of `usage_constantType` is the greatest: the type of the constant function is well used
exactly with the vectors below it, so that it uses `A` twice, and `B` never.
-/
theorem usage_constantType_iff : γ ▶[m] constantType ↔ γ ≤ 𝟘ᶜ ∙ (⌜m⌝ + ⌜m⌝) ∙ 𝟘 :=
  ⟨fun h =>
    -- `γ` is below the sum of the bounds of the domain `A` and of the codomain, itself below the
    -- sum of the bounds of its domain `B` and of its codomain `A`.
    have ⟨_, _, hA, hB, hγ⟩ := h.inv_pi
    have ⟨_, _, hB', hA', hη⟩ := hB.inv_pi
    GradeVector.le_trans hγ <| GradeVector.le_trans
      (add_mono (smul_mono (Grade.le_refl _) hA.inv_var)
        (GradeVector.le_trans (le_tail hη)
          (tail_mono (add_mono (smul_mono (Grade.le_refl _) hB'.inv_var) (le_tail hA'.inv_var)))))
      (by cases m <;> decide),
    fun h => .sub usage_constantType h⟩

end SicTest.Constant.Usage
