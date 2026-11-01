module

import Sic.Core.UsageInference
import all SicTest.Common.Usage
import all SicTest.Constant.Syntax

/-!
# The Constant Function: Usage

The usage of the constant function of RFC 24 and of its type, in every mode, which the inferred
usage decides.
The vectors are over the context `A : U₀, B : U₀`, the grade of `B` last, since it is the innermost
variable.
-/

namespace SicTest.Constant.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Common.Usage
  SicTest.Constant.Syntax

/--
The constant function uses neither `A` nor `B`, since the types that its abstractions carry use no
variable: its body uses `x` with the grade `𝟙` of the outer abstraction, and `y` never.
-/
theorem usage_constant : 𝟘ᶜ ▶[m] constant := by
  cases m <;> decide

/--
The usage of `usage_constant` is the greatest: the constant function is well used exactly with the
vectors below `𝟘ᶜ`, whatever its mode.
-/
theorem usage_constant_iff : γ ▶[m] constant ↔ γ ≤ 𝟘ᶜ :=
  usage_iff_le (by cases m <;> decide)

/--
The type of the constant function uses `A` twice, as the domain of `x` and as the type of the
result, and `B` never, as the domain of `y`, whose grade is `𝟘`; it does not use `x` or `y`, whose
grades in the type are `𝟘`.
-/
theorem usage_constantType : 𝟘ᶜ ∙ (⌜m⌝ + ⌜m⌝) ∙ 𝟘 ▶[m] constantType := by
  cases m <;> decide

/--
The usage of `usage_constantType` is the greatest: the type of the constant function is well used
exactly with the vectors below it, so that it uses `A` twice, and `B` never.
-/
theorem usage_constantType_iff : γ ▶[m] constantType ↔ γ ≤ 𝟘ᶜ ∙ (⌜m⌝ + ⌜m⌝) ∙ 𝟘 :=
  usage_iff_le (by cases m <;> decide)

end SicTest.Constant.Usage
