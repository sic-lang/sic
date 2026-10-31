module

public import Sic.Core.Reduction
import Sic.Core.Reducibility.Fundamental
import Sic.Core.Reducibility.Introductions.Pi

/-!
# Injectivity

A type equal to a universe, to a type of functions or to a neutral type, and in weak head normal
form, has the same head: a universe of an equivalent level, a type of functions with the same grades
and equal domain and codomain, or a neutral type, as in the formalizations of ADE and of Pujet.
The constructors of the types are thus injective, and distinct ones never make equal types.

## Correspondence with the Formalizations of ADE and of Pujet

ADE and Pujet state the head of the other type and the equalities of its components apart, while
the inversions here state both, from which the injectivity follows, and the inequalities of distinct
heads follow from the inversions, by the head of the other type.

The theorems hold for every equality relation, and the proofs use the equality of
`Sic.Core.Typing`, which is one.
The statements write `Term.univ` and `Term.pi`, since `univ` and `pi` name constructors of
`TypeEq`, in whose namespace the theorems are.
-/

@[expose] public section

namespace Sic.Core

open Reducibility Term

/-!
The two types are reducibly equal, by the fundamental lemma, and the interpretation of the first
one, in weak head normal form, is the one of its head, since it reduces the type to a weak head
normal form, which is the type itself.
The interpretation equates the second type to the first one only when it reduces to a type of the
same head, which is the second type itself, in weak head normal form.
-/

-- ADE: `U≡A`, in `Definition/Typed/Consequences/Equality.agda`, and `U-injectivity`, in
-- `Definition/Typed/Consequences/Injectivity.agda`.
-- Pujet: `U≡A`, in `Definition/Typed/Consequences/Equality.agda`.
/-- A type in weak head normal form equal to a universe is a universe of an equivalent level. -/
theorem TypeEq.inv_univ (h : Γ ⊢ Term.univ l ≡ C) (hC : Whnf C) :
    ∃ l', C = Term.univ l' ∧ l ≈ l' := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, _, _, hP, hQ, hPC⟩ := h.reducible
  have hU := hP.escape
  have hC' := hQ.escape
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hA =>
    cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨.refl hU, .univ⟩
    have ⟨_, hC'', hl⟩ := hPC
    cases TypeRedWhnf.det ⟨hC'', .univ⟩ ⟨.refl hC', hC⟩
    exact ⟨_, rfl, hl⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hU, .univ⟩; nomatch hN'
  | pi hA => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hU, .univ⟩

-- ADE: `Π≡A`, in `Definition/Typed/Consequences/Equality.agda`, and `ΠΣ-injectivity`, in
-- `Definition/Typed/Consequences/Injectivity.agda`.
-- Pujet: `Π≡A`, in `Definition/Typed/Consequences/Equality.agda`, and `injectivity`, in
-- `Definition/Typed/Consequences/Injectivity.agda`.
/--
A type in weak head normal form equal to a type of functions is a type of functions with the same
grades, an equal domain, and an equal codomain in the context extended by the domain.

The codomains are reducibly equal at the variable of a new declaration of the domain, which is a
reducible argument.
-/
theorem TypeEq.inv_pi (h : Γ ⊢ Term.pi p q A B ≡ C) (hC : Whnf C) :
    ∃ A' B', C = Term.pi p q A' B' ∧ (Γ ⊢ A ≡ A') ∧ Γ ∙ A ⊢ B ≡ B' := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, hR⟩ := h.reducible
  have ⟨_, _, hP, hQ, hPC⟩ := hR
  have hPi := hP.escape
  have hC' := hQ.escape
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hU => nomatch TypeRedWhnf.det ⟨hU, .univ⟩ ⟨.refl hPi, .pi⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hPi, .pi⟩; nomatch hN'
  | pi hA =>
    cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hPi, .pi⟩
    have ⟨_, _, hC'', _⟩ := hPC
    cases TypeRedWhnf.det ⟨hC'', .pi⟩ ⟨.refl hC', hC⟩
    have ⟨hF, hG⟩ := hR.inv_pi
    have ⟨_, _, hPA, _, hPA'⟩ := hF .id h.wfCon
    rw [wk_id] at hPA hPA'
    have hΓA : ⊢ Γ ∙ A := .snoc hPA.escape
    have ⟨_, _, hPB, _, hPB'⟩ := hG (.step .id) hΓA (ReducibleTermEq.var hPA hΓA)
    rw [instantiate_wk_lift_step] at hPB hPB'
    exact ⟨_, _, rfl, hPA.escape_eqType hPA', hPB.escape_eqType hPB'⟩

-- ADE: `ne≡A`, in `Definition/Typed/Consequences/Equality.agda`.
-- Pujet: `ne≡A`, in `Definition/Typed/Consequences/Equality.agda`.
/-- A type in weak head normal form equal to a neutral type is neutral. -/
theorem TypeEq.inv_ne (h : Γ ⊢ K ≡ C) (hK : Neutral K) (hC : Whnf C) : Neutral C := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, _, _, hP, hQ, hPC⟩ := h.reducible
  have hK' := hP.escape
  have hC' := hQ.escape
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hA => cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨.refl hK', .ne hK⟩; nomatch hK
  | ne =>
    have ⟨_, hC'', hM, _⟩ := hPC
    cases TypeRedWhnf.det ⟨hC'', .ne hM⟩ ⟨.refl hC', hC⟩
    exact hM
  | pi hA => cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hK', .ne hK⟩; nomatch hK

-- ADE: `ΠΣ-injectivity`, in `Definition/Typed/Consequences/Injectivity.agda`.
-- Pujet: `injectivity`, in `Definition/Typed/Consequences/Injectivity.agda`.
/--
Two equal types of functions have the same grades, equal domains, and equal codomains in the context
extended by the first domain.
-/
theorem TypeEq.pi_inj (h : Γ ⊢ Term.pi p q A B ≡ Term.pi p' q' A' B') :
    p = p' ∧ q = q' ∧ (Γ ⊢ A ≡ A') ∧ Γ ∙ A ⊢ B ≡ B' := by
  have ⟨_, _, e, hA, hB⟩ := h.inv_pi .pi
  cases e
  exact ⟨rfl, rfl, hA, hB⟩

end Sic.Core
