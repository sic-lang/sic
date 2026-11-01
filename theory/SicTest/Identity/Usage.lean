module

public import Sic.Core.UsageInference
public import SicTest.Identity.Syntax

/-!
# The Polymorphic Identity: Usage

The usage of the polymorphic identity of RFC 24 and of its type, in every mode, which the inferred
usage decides: the type uses its type argument twice, which its grade `𝟙 + 𝟙` allows and the grade
`𝟙` does not.
-/

@[expose] public section

namespace SicTest.Identity.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Identity.Syntax

/-- The identity uses no variable: its body uses `x` once, with the grade `𝟙` of its abstraction. -/
theorem usage_identity : 𝟘ᶜ ▶[m] identity := by
  cases m <;> decide

/--
The type of the identity uses `A` twice, as the domain of `x` and as the type of the result, which
the grade `𝟙 + 𝟙` of `A` in the type allows.
-/
theorem usage_identityType : 𝟘ᶜ ▶[m] identityType := by
  cases m <;> decide

/--
With the grade `𝟙` for `A` in its type, the type of the identity is not well used at run time: the
grade `𝟙` allows one use of `A`, and the type uses it twice.
-/
theorem not_usage_identityType_one :
    ¬ 𝟘ᶜ ▶[𝟙𝟙ᵐ] (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1)) : Term 1 0) := by
  decide

end SicTest.Identity.Usage
