module

import Sic.Core.Reducibility.Validity

/-!
# The Universes: Validity

The universes are valid types at the levels above theirs, since no substitution changes them.
-/

namespace SicTest.Universe.Reducibility.Validity

open Sic.Core Sic.Core.Term Sic.Core.Reducibility

variable [EqualityRelation]

/--
The universe `U_l`, with a level variable `l`, is a valid type at the level `1` in every valid
context: every substitution keeps it, in a well-formed context where it is reducible.
-/
theorem validTypeEq_univ {Γ : Con 1 n} (hΓ : ⊩ᵛ Γ) :
    Γ ⊩ᵛ⟨1⟩ univ (.var 0) ≡ univ (.var 0) := by
  rw [ValidTypeEq.unfold]
  refine ⟨hΓ, fun {_ Δ _ _} hσ => ?_⟩
  have hΔ : ⊢ Δ := hσ.wfCon
  have hU : Δ ⊩⟨1⟩ univ (.var 0) ▸ _ :=
    LogicalRelation.unfold ▸ LogRel.univ (L := .var 0) (by decide) (.refl (.univ (.univ hΔ)))
  exact ⟨_, _, hU, hU, _, .refl (.univ (.univ hΔ)), .refl _⟩

end SicTest.Universe.Reducibility.Validity
