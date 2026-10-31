module

import Sic.Core.Reducibility.Validity

/-!
# The Universes: Validity

The universes are valid types at the levels above theirs, since no substitution changes them, and
only there: the validity does not equate two universes of different levels, and a universe is not a
valid type at the value of its own level.
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

/-- The universes `U_l` and `U_{l + 1}` are not validly equal, at any level. -/
theorem not_validTypeEq_univ_succ :
    ¬ (.empty : Con 1 0) ⊩ᵛ⟨l⟩ univ (.var 0) ≡ univ (.succ (.var 0)) := by
  intro h
  have ⟨_, _, hU, _, hUU⟩ := h.reducible
  have hΓ : ⊢ (.empty : Con 1 0) := .empty
  rw [LogicalRelation.unfold] at hU
  cases hU with
  | univ _ hA =>
    cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩
    have ⟨_, hB, hL⟩ := hUU
    cases TypeRedWhnf.det ⟨hB, .univ⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩
    -- With `l = 0`, the two levels have the values `0` and `1`.
    nomatch hL fun _ => 0
  | ne hA hN => cases TypeRedWhnf.det ⟨hA, .ne hN⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩; nomatch hN
  | pi hA => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩

/--
The universe `U_l` is not a valid type at the level `0`, the value of `l` when it is `0`, so that
`ValidTypeEq.univ` gives the smallest level.
-/
example : ¬ (.empty : Con 1 0) ⊩ᵛ⟨0⟩ univ (.var 0) ≡ univ (.var 0) := by
  intro h
  have ⟨_, _, hU, _⟩ := h.reducible
  have hΓ : ⊢ (.empty : Con 1 0) := .empty
  rw [LogicalRelation.unfold] at hU
  cases hU with
  | univ hL => exact Nat.not_lt_zero _ hL
  | ne hA hN => cases TypeRedWhnf.det ⟨hA, .ne hN⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩; nomatch hN
  | pi hA => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩

end SicTest.Universe.Reducibility.Validity
