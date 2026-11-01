module

public import SicTest.Rfc24.Usage
import Sic.Core.UsageSubstitution
import SicTest.Common.Usage

/-!
# Usage Substitution

The instantiation of the usage on the terms of the claims of RFC 24 on the multiplicities: the
reduct of an application of an abstraction counts the argument as many times as the application
does, and the vector that `Sic.Core.Usage.instantiate` gives it is its greatest usage, so the
instantiation loses no precision.
-/

@[expose] public section

namespace SicTest.Rfc24.UsageSubstitution

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Common.Usage
open SicTest.Rfc24.Usage

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-!
## An Argument Used Twice

In the context `f, x`, the body `(f ∘_𝟙 y) ∘_𝟙 y` of an abstraction over `y` uses `y` twice, and
instantiating `y` by `x` gives the term `twice` of RFC 24.
-/

/-- `(f ∘_𝟙 y) ∘_𝟙 y`, in the context `f, x, y`. -/
def twiceBody : Term 0 3 := app 𝟙 (app 𝟙 (var 2) (var 0)) (var 0)

example : twiceBody.instantiate (var 0) = twice := rfl

/-- The argument `x`, of grade `𝟙 + 𝟙`, counts twice in the usage of the reduct. -/
theorem usage_twice :
    (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) + ((𝟙 + 𝟙) • (𝟘ᶜ ∙ 𝟘 ∙ 𝟙)) ▶[𝟙𝟙ᵐ] twice :=
  Usage.instantiate (t := twiceBody) (by decide) (by decide)

/-- That usage is the greatest usage of the reduct. -/
example : γ ▶[𝟙𝟙ᵐ] twice ↔ γ ≤ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) + ((𝟙 + 𝟙) • (𝟘ᶜ ∙ 𝟘 ∙ 𝟙)) :=
  usage_iff_le (by decide)

/-!
## An Erased Argument

In the context `f, x`, the body `f ∘_⟨0, 1⟩ y` of an abstraction over `y` uses `y` once, erased,
and instantiating `y` by `x` gives the second term of `usage_affine`.
-/

/-- `f ∘_⟨0, 1⟩ y`, in the context `f, x, y`. -/
def erasedBody : Term 0 3 := app ⟪.zero, .one⟫ (var 2) (var 0)

/-- `f ∘_⟨0, 1⟩ x`, in the context `f, x`. -/
def erased : Term 0 2 := app ⟪.zero, .one⟫ (var 1) (var 0)

example : erasedBody.instantiate (var 0) = erased := rfl

/--
The argument `x`, of grade `⟨0, 1⟩`, is checked in the mode `𝟘𝟙ᵐ`, and its use stays erased in the
usage of the reduct.
-/
theorem usage_erased :
    (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) + (⟪.zero, .one⟫ • (𝟘ᶜ ∙ 𝟘 ∙ ⟪.zero, .one⟫)) ▶[𝟙𝟙ᵐ] erased :=
  Usage.instantiate (t := erasedBody) (p := ⟪.zero, .one⟫) (by decide) (by decide)

/-- That usage is the greatest usage of the reduct. -/
example : γ ▶[𝟙𝟙ᵐ] erased ↔
    γ ≤ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) + (⟪.zero, .one⟫ • (𝟘ᶜ ∙ 𝟘 ∙ ⟪.zero, .one⟫)) :=
  usage_iff_le (by decide)

end SicTest.Rfc24.UsageSubstitution
