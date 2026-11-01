module

import Sic.Core.Usage
import all SicTest.Identity.Syntax

/-!
# The Polymorphic Identity: Usage

The usage of the polymorphic identity of RFC 24 and of its type, in every mode: the type uses its
type argument twice, which its grade `𝟙 + 𝟙` allows and the grade `𝟙` does not.
-/

namespace SicTest.Identity.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Identity.Syntax

/-- The identity uses no variable: its body uses `x` once, with the grade `𝟙` of its abstraction. -/
theorem usage_identity : 𝟘ᶜ ▶[m] identity :=
  .lam (.lam (.sub .var (by cases m <;> decide)))

/--
The type of the identity uses `A` twice, as the domain of `x` and as the type of the result, which
the grade `𝟙 + 𝟙` of `A` in the type allows.
-/
theorem usage_identityType : 𝟘ᶜ ▶[m] identityType :=
  -- `A`, after `x`, then `Π^𝟘_𝟙 (x : A). A`, after `A`.
  have hA : 𝟘ᶜ ∙ ⌜m⌝ ∙ (⌜m⌝ * 𝟘) ▶[m] (var 1 : Term 1 2) := .sub .var (by cases m <;> decide)
  have hB : 𝟘ᶜ ∙ (⌜m⌝ * (𝟙 + 𝟙)) ▶[m] pi 𝟙 𝟘 (var 0) (var 1) :=
    .sub (.pi .var hA) (by cases m <;> decide)
  .sub (.pi .univ hB) (by cases m <;> decide)

/--
With the grade `𝟙` for `A` in its type, the type of the identity is not well used at run time: the
grade `𝟙` allows one use of `A`, and the type uses it twice.
-/
theorem not_usage_identityType_one :
    ¬ 𝟘ᶜ ▶[𝟙𝟙ᵐ] (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1)) : Term 1 0) := fun h =>
  -- The type uses `A` as the domain of `x`, with a grade `a`, and as the type of the result, with a
  -- grade `b`, both at most `𝟙`, so that it uses `A` at most with `(𝟙 * a) + b`, which `𝟙` is not
  -- below.
  have ⟨_, _, _, hB, _⟩ := h.inv_pi
  have ⟨_, _, hA, hA', hB'⟩ := hB.inv_pi
  have key : ∀ a b : Grade, a ≤ 𝟙 → b ≤ 𝟙 → ¬ 𝟙 ≤ (𝟙 * a) + b := by decide
  key _ _ (hA.inv_var 0) (hA'.inv_var 1) (hB' 0)

end SicTest.Identity.Usage
