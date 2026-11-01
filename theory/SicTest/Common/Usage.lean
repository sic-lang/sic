module

public import Sic.Core.UsageInference

/-!
# Common Usage

The exact usage of a term, which the checks of the themes prove by decision.
-/

@[expose] public section

namespace SicTest.Common.Usage

open Sic Sic.Core

/--
A usable term whose inferred usage is `v` is well used exactly with the vectors below `v`, so that
`v` is its greatest usage: the three premises are closed, and `decide` proves them.
-/
theorem usage_iff_le (h : Usable m t ∧ ⌈t⌉[m] ≤ v ∧ v ≤ ⌈t⌉[m]) : γ ▶[m] t ↔ γ ≤ v :=
  usage_iff.trans
    ⟨fun ⟨_, hγ⟩ => GradeVector.le_trans hγ h.2.1, fun hγ => ⟨h.1, GradeVector.le_trans hγ h.2.2⟩⟩

end SicTest.Common.Usage
