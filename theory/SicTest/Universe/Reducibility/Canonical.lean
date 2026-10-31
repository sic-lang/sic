module

import Sic.Core.Reducibility.Canonical

/-!
# The Universes: Canonical Interpretation

The canonical interpretation of a universe equates it to itself at the levels where it is reducible,
and equates nothing at the others, where no interpretation describes it.
-/

namespace SicTest.Universe.Reducibility.Canonical

open Sic.Core Sic.Core.Term Sic.Core.Reducibility

variable [EqualityRelation]

/-- The canonical interpretation of `U₀` at the level `1` equates it to itself. -/
example : (Interpretation.canonical (.empty : Con 0 0) 1 (univ .zero)).eqType (univ .zero) := by
  have hΓ : ⊢ (.empty : Con 0 0) := .empty
  have hU : (.empty : Con 0 0) ⊩⟨1⟩ univ .zero ▸ _ :=
    LogicalRelation.unfold ▸ LogRel.univ (L := .zero) (by decide) (.refl (.univ (.univ hΓ)))
  exact ⟨_, hU, _, .refl (.univ (.univ hΓ)), .refl _⟩

/--
The canonical interpretation of `U₀` at the level `0`, where it is not reducible, does not equate it
to itself.
-/
example : ¬ (Interpretation.canonical (.empty : Con 0 0) 0 (univ .zero)).eqType (univ .zero) := by
  intro ⟨_, hU, _⟩
  have hΓ : ⊢ (.empty : Con 0 0) := .empty
  rw [LogicalRelation.unfold] at hU
  cases hU with
  | univ hL => exact Nat.not_lt_zero _ hL
  | ne hA hN => cases TypeRedWhnf.det ⟨hA, .ne hN⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩; nomatch hN
  | pi hA => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl (.univ (.univ hΓ)), .univ⟩

end SicTest.Universe.Reducibility.Canonical
