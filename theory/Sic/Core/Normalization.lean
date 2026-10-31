module

public import Sic.Core.Reduction
import Sic.Core.Reducibility.Fundamental

/-!
# Normalization

Every type and every term of a type reduce to a weak head normal form, as in the formalizations of
ADE and of Pujet: the fundamental lemma makes them reducible, and the interpretation of a reducible
type reduces it, and each of its terms, to a weak head normal form.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE, in `Definition/Typed/Consequences/Reduction.agda` | Of Pujet, in `Definition/Typed/Consequences/Reduction.agda` |
| --- | --- | --- |
| `IsType.whnf` | `whNorm` | the same |
| `HasType.whnf` | `whNormTerm` | the same |

The theorems hold for every equality relation, and the proofs use the equality of
`Sic.Core.Typing`, which is one.
-/

@[expose] public section

namespace Sic.Core

open Reducibility

/-- A type reduces to a weak head normal form. -/
theorem IsType.whnf (h : Γ ⊢ A) : ∃ B, Γ ⊢ A ↘ B := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, _, _, hP, _⟩ := h.reducible
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hU => exact ⟨_, hU, .univ⟩
  | ne hN hN' => exact ⟨_, hN, .ne hN'⟩
  | pi hA => exact ⟨_, hA, .pi⟩

/--
A term of a type reduces to a weak head normal form.

The interpretation of the type equates the term to itself only when the term reduces to a weak head
normal form, at the weak head normal form of the type, which is equal to the type.
-/
theorem HasType.whnf (h : Γ ⊢ t : A) : ∃ u, Γ ⊢ t ↘ u : A := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, _, hP, ht⟩ := h.reducible
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hU =>
    have ⟨_, _, ht, _⟩ := ht
    exact ⟨_, ht.conv hU.typeEq.symm⟩
  | ne hN _ _ =>
    have ⟨_, _, ht, _, ht', _⟩ := ht
    exact ⟨_, TermRedWhnf.conv ⟨ht, .ne ht'⟩ hN.typeEq.symm⟩
  | pi hA =>
    have ⟨_, _, ht, _⟩ := ht
    exact ⟨_, ht.conv hA.typeEq.symm⟩

end Sic.Core
