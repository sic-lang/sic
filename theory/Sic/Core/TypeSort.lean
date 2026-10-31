module

public import Sic.Core.Typing
import Sic.Core.Injectivity
import Sic.Core.Inversion
import Sic.Core.NeutralType
import Sic.Core.Reducibility.Fundamental
import Sic.Core.Reducibility.Neutral
import Sic.Core.Reducibility.Weakening
import Sic.Core.SubjectReduction
import Sic.Core.WellFormed

/-!
# The Sort of a Type

A type is a term of a single universe, up to the equality of levels, and two equal types are equal
terms of a universe, as the Rationale of RFC 24 requires: the rules of the equality of types then
add no equality to those of the universes, so that the core with them derives the same judgments as
the core where types are only compared in a universe.

The uniqueness of the universe of a type cannot follow from the uniqueness of the type of a term,
which fails, since an abstraction does not carry the grade of the result of its type of functions.
It is proved on the weak head normal form of the type instead, whose universe the inversions of
typing give, and whose domain and codomain, when it is a type of functions, are types again: the
proof is an induction on the reducibility of the type, which contains the reducibility of its domain
and of its codomain, since these are not subterms of the type.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE | Of Pujet |
| --- | --- | --- |
| `HasType.sort_unique`, `TypeEq.sort` | none | none |

The types of ADE are not all terms of a universe, and Pujet's have a single universe.
-/

@[expose] public section

namespace Sic.Core

open Term Reducibility

/-- Two equal universes have equal levels. -/
private theorem TypeEq.univ_level (h : Γ ⊢ Term.univ L₁ ≡ Term.univ L₂) : L₁ ≈ L₂ :=
  have ⟨_, e, hL⟩ := h.inv_univ .univ
  by cases e; exact hL

/--
A reducible type has a single universe, by induction on its reducibility: its weak head normal form
has each of its universes, by subject reduction, and is a universe, whose universe is the one above
it, a neutral type, whose types are equal, or a type of functions, whose universe is the larger of
the universes of its domain and of its codomain, which are unique by induction.
-/
private theorem Reducibility.LogRel.sort_unique [EqualityRelation]
    (h : LogRel l (fun l' _ => LogicalRelation l') Γ A P) :
    Γ ⊢ A : Term.univ L₁ → Γ ⊢ A : Term.univ L₂ → L₁ ≈ L₂ := by
  induction h generalizing L₁ L₂ with
  | univ _ hA =>
    intro h₁ h₂
    exact (h₁.typeRedStar hA).inv_univ.univ_level.trans
      (h₂.typeRedStar hA).inv_univ.univ_level.symm
  | ne hA hN _ =>
    intro h₁ h₂
    exact (hN.typeEq (h₁.typeRedStar hA) (h₂.typeRedStar hA)).univ_level
  | @pi _ Γ _ F G _ _ hA _ PF _ hF _ _ ihF ihG =>
    intro h₁ h₂
    have ⟨a₁, b₁, hF₁, hG₁, hL₁⟩ := (h₁.typeRedStar hA).inv_pi_univ
    have ⟨a₂, b₂, hF₂, hG₂, hL₂⟩ := (h₂.typeRedStar hA).inv_pi_univ
    have hΓ := hF₁.wfCon
    have hΓF : ⊢ Γ ∙ F := .snoc (.univ hF₁)
    have eF := ihF (ρ := .id) .id hΓ (by rw [wk_id]; exact hF₁) (by rw [wk_id]; exact hF₂)
    have hPF : Γ ∙ F ⊩⟨l⟩ F.wk1 ▸ PF (.step .id) (Γ ∙ F) := by
      rw [LogicalRelation.unfold]; exact hF (.step .id) hΓF
    -- The codomain is reducible at the variable of a new declaration of the domain.
    have hx := hPF.neutral_eqTerm .var .var
      (EqualityRelation.var (.var hΓF : Γ ∙ F ⊢ var 0 : F.wk1))
    have eG := ihG (.step .id) hΓF hx (by rw [instantiate_wk_lift_step]; exact hG₁)
      (by rw [instantiate_wk_lift_step]; exact hG₂)
    have hmax : a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := fun ρ => by
      rw [Level.eval_max, Level.eval_max, eF ρ, eG ρ]
    exact hL₁.univ_level.trans (hmax.trans hL₂.univ_level.symm)

/-- A type is a term of a single universe, up to the equality of levels. -/
theorem HasType.sort_unique (h₁ : Γ ⊢ A : Term.univ L₁) (h₂ : Γ ⊢ A : Term.univ L₂) : L₁ ≈ L₂ := by
  letI := EqualityRelation.termEqRelation
  have ⟨_, _, _, hP, _⟩ := (IsType.univ h₁).reducible
  rw [LogicalRelation.unfold] at hP
  exact hP.sort_unique h₁ h₂

/--
Two equal types are equal terms of a universe: the only rule of the equality of types that needs
more than the rules of the equality of terms is the transitivity, whose two equalities are in the
universes of their common type, which are equal.
-/
theorem TypeEq.sort : Γ ⊢ A ≡ B → ∃ L, Γ ⊢ A ≡ B : Term.univ L
  | .univ h => ⟨_, h⟩
  | .refl h => have ⟨_, h⟩ := h.sort; ⟨_, .refl h⟩
  | .symm h => have ⟨_, h⟩ := h.sort; ⟨_, .symm h⟩
  | .trans h₁ h₂ =>
    have ⟨_, h₁⟩ := h₁.sort
    have ⟨_, h₂⟩ := h₂.sort
    have hL := (h₂.wf.1.sort_unique h₁.wf.2.1)
    ⟨_, .trans h₁ (.conv h₂ (.univ (.univ h₁.wfCon hL)))⟩

end Sic.Core
