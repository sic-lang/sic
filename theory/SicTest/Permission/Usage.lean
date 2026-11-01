module

public import SicTest.Common.Usage
public import SicTest.Permission.Syntax
import Sic.Core.UsageInference

/-!
# A Permission Used Once: Usage

Of the three functions that receive a permission, all well typed, usage accepts only the one that
passes the permission on once, whatever grades the variables of the context get, as the inferred
usage decides: the vectors are over `Perm`, `B`, `b`, `close` and `commit`, the grade of `commit`
last.
-/

@[expose] public section

namespace SicTest.Permission.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.Common.Usage
  SicTest.Permission.Syntax

/--
The function that passes the permission on once uses `close` once: its body uses `x` with
`⟨0, 1⟩ · ⟨0, 1⟩ = ⟨0, 1⟩`, since the argument of `close` is checked in the mode `𝟘𝟙ᵐ`, where `x`
uses itself with `⟨0, 1⟩`, and this is the grade of the abstraction.
-/
theorem usage_once : 𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟙 ∙ 𝟘 ▶[𝟙𝟙ᵐ] once := by
  decide

/--
The usage of `usage_once` is the greatest: the function that passes the permission on once is well
used exactly with the vectors below it, so that it cannot leave `close` unused, nor use any other
variable.
-/
theorem usage_once_iff : γ ▶[𝟙𝟙ᵐ] once ↔ γ ≤ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟙 ∙ 𝟘 :=
  usage_iff_le (by decide)

/--
The function that passes the permission to both operations is rejected: its body uses `x` with
`⟨0, 1⟩ + ⟨0, 1⟩ = ⟨0, ω⟩` at least, which `⟨0, 1⟩` is not below.
-/
theorem not_usage_twice : ¬ γ ▶[𝟙𝟙ᵐ] twice := fun h =>
  absurd h.usable (by decide)

/-- The function that drops the permission is rejected: its body uses `x` with `𝟘`. -/
theorem not_usage_dropped : ¬ γ ▶[𝟙𝟙ᵐ] dropped := fun h =>
  absurd h.usable (by decide)

end SicTest.Permission.Usage
