module

public import Sic.Core.Reducibility.Validity

/-!
# Universes

The universes are valid types and valid terms of the universes of the next level, and two terms
validly equal at a universe are validly equal types, at the level of the universe, so that the
fundamental lemma covers the rules `(U)` and `(U_≡)` of `Sic.Core.Typing`, and the rules that make
the terms of a universe its types.

## Correspondence with the Formalizations of ADE and of Pujet

ADE's `⊩ᵛU≡U∷U` equates two universes of equal levels, which may be terms, where the levels here
are those of `Sic.Core.Level`, whose equality `≈` the rule `(U_≡)` reads.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

variable [EqualityRelation]

/-!
The statements of the theorems on `ValidTermEq` write the universes with the namespace `Term`,
since the short name of their constructor would resolve to `ValidTermEq.univ` in the namespace that
Lean opens for them.
-/

/--
Two universes of equal levels are reducibly equal types at every level larger than the value of
the first, in every well-formed context.
-/
private theorem reducibleTypeEq_univ (hΔ : ⊢ Δ) (hL : L₁ ≈ L₂) (hl : L₁.bound < l) :
    Δ ⊩⟨l⟩ univ L₁ ≡ univ L₂ := by
  have hb : L₁.bound = L₂.bound := hL _
  have hU₁ : Δ ⊩⟨l⟩ univ L₁ ▸ _ :=
    LogicalRelation.unfold ▸ LogRel.univ (L := L₁) hl (.refl (.univ (.univ hΔ)))
  have hU₂ : Δ ⊩⟨l⟩ univ L₂ ▸ _ :=
    LogicalRelation.unfold ▸ LogRel.univ (L := L₂) (hb ▸ hl) (.refl (.univ (.univ hΔ)))
  exact ⟨_, _, hU₁, hU₂, _, .refl (.univ (.univ hΔ)), hL⟩

-- ADE: `⊩ᵛU`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
-- Pujet: `Uᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/--
The universe of a level `L` is a valid type at the level that follows the value of `L`, in every
valid context, since every substitution keeps it.
-/
theorem ValidTypeEq.univ (hΓ : ⊩ᵛ Γ) : Γ ⊩ᵛ⟨L.bound + 1⟩ univ L ≡ univ L := by
  rw [ValidTypeEq.unfold]
  exact ⟨hΓ, fun hσ => reducibleTypeEq_univ hσ.wfCon (.refl L) (Nat.lt_succ_self _)⟩

-- ADE: `⊩ᵛU≡U∷U`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
-- Pujet: none, with a single universe, which is not a term.
/--
Two universes of equal levels `L₁` and `L₂` are validly equal terms of the universe of the level
`L₁ + 1`, in every valid context, since every substitution keeps them, and each is a type reducible
at the level of that universe.
-/
theorem ValidTermEq.univ (hΓ : ⊩ᵛ Γ) (hL : L₁ ≈ L₂) :
    Γ ⊩ᵛ⟨L₁.succ.bound + 1⟩ Term.univ L₁ ≡ Term.univ L₂ : Term.univ L₁.succ := by
  refine ⟨ValidTypeEq.univ hΓ, fun {_ Δ _ _} hσ => ?_⟩
  have hΔ := hσ.wfCon
  have hU : Δ ⊩⟨L₁.succ.bound + 1⟩ Term.univ L₁.succ ▸ _ := LogicalRelation.unfold ▸
    LogRel.univ (L := L₁.succ) (Nat.lt_succ_self _) (.refl (.univ (.univ hΔ)))
  have ⟨_, _, hU₁, hU₂, hU₁₂⟩ := reducibleTypeEq_univ hΔ hL (Nat.lt_succ_self _)
  have hU₂U₁ : Δ ⊢ Term.univ L₂.succ ≡ Term.univ L₁.succ := .univ (.univ hΔ hL.symm.succ)
  exact ⟨_, hU, _, _, ⟨.refl (.univ hΔ), .univ⟩, ⟨.refl (.conv (.univ hΔ) hU₂U₁), .univ⟩, .univ,
    .univ, EqualityRelation.univ hΔ hL, _, hU₁, ⟨_, hU₂⟩, hU₁₂⟩

-- ADE: `⊩ᵛ≡∷U→⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
-- Pujet: `univᵛ` and `univEqᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/--
Two terms validly equal at the universe of a level `L` are validly equal types at the value of `L`,
since the interpretation of the universe equates them as two types reducible at that level.
-/
theorem ValidTermEq.toTypeEq (h : Γ ⊩ᵛ⟨l⟩ A ≡ B : Term.univ L) : Γ ⊩ᵛ⟨L.bound⟩ A ≡ B := by
  have hU := h.1
  rw [ValidTypeEq.unfold] at hU ⊢
  refine ⟨hU.1, fun hσ => ?_⟩
  have ⟨_, hU, hAB⟩ := h.2 hσ
  have hΔ := hσ.wfCon
  rw [LogicalRelation.unfold] at hU
  cases hU with
  | univ _ hA =>
    cases TypeRedWhnf.det ⟨hA, .univ⟩ ⟨.refl (.univ (.univ hΔ)), .univ⟩
    have ⟨_, _, _, _, _, _, _, _, hA, ⟨_, hB⟩, hAB⟩ := hAB
    exact ⟨_, _, hA, hB, hAB⟩
  | ne hA hN => cases TypeRedWhnf.det ⟨hA, .ne hN⟩ ⟨.refl (.univ (.univ hΔ)), .univ⟩; nomatch hN
  | pi hA => nomatch TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl (.univ (.univ hΔ)), .univ⟩

end Sic.Core.Reducibility
