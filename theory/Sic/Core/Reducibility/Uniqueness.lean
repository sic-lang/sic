module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# Uniqueness

The interpretation of a reducible type is unique, whatever the levels of the logical relation that
prove its reducibility.
ADE prove the same property as the irrelevance of the proofs of reducibility: since their relation
computes the interpretation from a proof, they show that two proofs give equivalent equalities,
where a relation that is a predicate of a type and of its interpretation, as here and in the
formalization of Pujet, is a function.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

-- ADE: `irrelevanceEq`, `irrelevanceTerm` and `irrelevanceEqTerm`, in
-- `Definition/LogicalRelation/Irrelevance.agda`.
-- Pujet: `irrelevanceEq`, `irrelevanceTerm` and `irrelevanceEqTerm`, in
-- `Definition/LogicalRelation/Irrelevance.agda`.
/--
Two proofs that a type is reducible, at any two levels, give the same interpretation.

Both proofs reduce the type to the same weak head normal form, since its reduction is deterministic,
so that they end with the same constructor.
The interpretation of a universe or of a neutral type only depends on this weak head normal form,
and the elements of a universe are interpreted by the relation at the level of the universe,
whatever the level of the proof.
For a type of functions, the induction shows that the interpretations of its domain and of its
codomain are the same in every context and at every argument that the interpretation of the type
quantifies over, which `simp` rewrites under the quantifiers that give these hypotheses.
-/
theorem LogicalRelation.unique (h₁ : Γ ⊩⟨l₁⟩ A ▸ P) (h₂ : Γ ⊩⟨l₂⟩ A ▸ Q) : P = Q := by
  rw [LogicalRelation.unfold] at h₁ h₂
  induction h₁ generalizing l₂ with
  | univ _ hA =>
    cases h₂ with
    | univ _ hA' => cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨hA', .univ⟩; rfl
    | ne hA' hN => cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨hA', .ne hN⟩; nomatch hN
    | pi hA' => nomatch TypeRedWhnf.det ⟨hA, .univ⟩ ⟨hA', .pi⟩
  | ne hA hN =>
    cases h₂ with
    | univ _ hA' => cases TypeRedWhnf.det ⟨hA', .univ⟩ ⟨hA, .ne hN⟩; nomatch hN
    | ne hA' hN' => cases TypeRedWhnf.det ⟨hA, .ne hN⟩ ⟨hA', .ne hN'⟩; rfl
    | pi hA' => cases TypeRedWhnf.det ⟨hA', .pi⟩ ⟨hA, .ne hN⟩; nomatch hN
  | pi hA _ PF PG _ _ _ ihF ihG =>
    cases h₂ with
    | univ _ hA' => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨hA', .univ⟩
    | ne hA' hN' => cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨hA', .ne hN'⟩; nomatch hN'
    | pi hA' _ PF' PG' hF' hG' =>
      cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨hA', .pi⟩
      have hPF : ∀ {m} {ρ : Wk m _} {Δ}, ρ ∷ Δ ⊇ _ → ⊢ Δ → PF ρ Δ = PF' ρ Δ :=
        fun hρ hΔ => ihF hρ hΔ (hF' hρ hΔ)
      have hPG : ∀ {m} {ρ : Wk m _} {Δ a}, ρ ∷ Δ ⊇ _ → ⊢ Δ → (PF' ρ Δ).eqTerm a a →
          PG ρ Δ a = PG' ρ Δ a :=
        fun hρ hΔ ha => ihG hρ hΔ (hPF hρ hΔ ▸ ha) (hG' hρ hΔ ha)
      congr 1 <;> funext <;> simp +contextual only [hPF, hPG]

end Sic.Core.Reducibility
