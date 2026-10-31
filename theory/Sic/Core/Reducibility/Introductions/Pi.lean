module

public import Sic.Core.Reducibility.Validity
import Sic.Core.Reducibility.Canonical
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.WellFormed

/-!
# Types of Functions

The types of functions are valid terms of the universes, so that the fundamental lemma covers the
rules `(Π)` and `(Π_≡)` of `Sic.Core.Typing`, and, through `ValidTermEq.toTypeEq`, the types of
functions as types.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Substitution/Introductions/Pi-Sigma.agda` | Of Pujet, in `Definition/LogicalRelation/Substitution/Introductions/Pi.agda` |
| --- | --- | --- |
| `ValidTermEq.pi` | `ΠΣᵗᵛ`, `ΠΣ-congᵗᵛ` | `Πᵗᵛ`, `Π-congᵗᵛ` |

ADE and Pujet build the interpretations of the domain and of the codomain from the proofs of their
reducibility, which are data, where they are the canonical interpretations of
`Sic.Core.Reducibility.Canonical` here.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

variable [EqualityRelation]

/-!
The statements of the theorems on `ValidTermEq` write `Term.pi` and `Term.univ`, since `pi` and
`univ` name theorems in the namespace that Lean opens for them.
-/

/--
A type of functions is reducible, with an interpretation that equates it to a second type of
functions, when the two are equal by the equality relation, their domains are reducibly equal in
every well-formed context that contains their own, and their codomains are reducibly equal at
reducibly equal arguments: the interpretations of the domain and of the codomain are the canonical
ones, which these equalities describe, as in ADE's `⊩ΠΣ⇔`.
-/
private theorem logicalRelation_pi {F₁ F₂ : Term k n} {G₁ G₂ : Term k (n + 1)}
    (hPi : Δ ⊢ pi p q F₁ G₁ ≅ pi p q F₂ G₂)
    (hF : ∀ {m} {ρ : Wk m n} {Ε : Con k m}, ρ ∷ Ε ⊇ Δ → ⊢ Ε → Ε ⊩⟨l⟩ F₁.wk ρ ≡ F₂.wk ρ)
    (hG : ∀ {m} {ρ : Wk m n} {Ε : Con k m} {a b}, ρ ∷ Ε ⊇ Δ → ⊢ Ε →
      (Ε ⊩⟨l⟩ a ≡ b : F₁.wk ρ) →
      Ε ⊩⟨l⟩ (G₁.wk ρ.lift).instantiate a ≡ (G₂.wk ρ.lift).instantiate b) :
    ∃ P, (Δ ⊩⟨l⟩ pi p q F₁ G₁ ▸ P) ∧ P.eqType (pi p q F₂ G₂) := by
  have hPiPi := EqualityRelation.typeEq hPi
  have h := LogRel.pi (lower := fun l' _ => LogicalRelation l') (.refl hPiPi.wf.1)
    (EqualityRelation.transType hPi (EqualityRelation.symmType hPi))
    (fun ρ Ε => Interpretation.canonical Ε l (F₁.wk ρ))
    (fun ρ Ε a => Interpretation.canonical Ε l ((G₁.wk ρ.lift).instantiate a))
    (fun hρ hΕ =>
      have ⟨_, _, hF₁, _⟩ := hF hρ hΕ
      hF₁.eq_canonical ▸ LogicalRelation.unfold ▸ hF₁)
    (fun hρ hΕ ha =>
      have ⟨_, _, hG₁, _⟩ := hG hρ hΕ ha
      hG₁.eq_canonical ▸ LogicalRelation.unfold ▸ hG₁)
    (fun hρ hΕ _ hb hab =>
      have ⟨_, _, hG₁, _, hG₁₁⟩ := (hG hρ hΕ hab).trans (hG hρ hΕ hb).symm
      ⟨_, hG₁, hG₁₁⟩)
  have h : Δ ⊩⟨l⟩ pi p q F₁ G₁ ▸ _ := LogicalRelation.unfold ▸ h
  refine ⟨_, h, F₂, G₂, .refl hPiPi.wf.2, hPi, fun hρ hΕ => ?_, fun hρ hΕ ha => ?_⟩
  · have ⟨_, _, hF₁, _, hF₁₂⟩ := hF hρ hΕ
    exact ⟨_, hF₁, hF₁₂⟩
  · have ⟨_, _, hG₁, _, hG₁₂⟩ := hG hρ hΕ ha
    exact ⟨_, hG₁, hG₁₂⟩

/--
Two types of functions are reducibly equal when they are equal by the equality relation, their
domains are reducibly equal in every well-formed context that contains their own, and their
codomains are reducibly equal at reducibly equal arguments, as in ADE's `⊩ΠΣ≡ΠΣ⇔`.

The second type is reducible since its domain is reducibly equal to itself, and its codomain at
two reducibly equal arguments of its domain, which are reducibly equal arguments of the first
domain, is reducibly equal to the first codomain at the first argument.
-/
private theorem reducibleTypeEq_pi {F₁ F₂ : Term k n} {G₁ G₂ : Term k (n + 1)}
    (hPi : Δ ⊢ pi p q F₁ G₁ ≅ pi p q F₂ G₂)
    (hF : ∀ {m} {ρ : Wk m n} {Ε : Con k m}, ρ ∷ Ε ⊇ Δ → ⊢ Ε → Ε ⊩⟨l⟩ F₁.wk ρ ≡ F₂.wk ρ)
    (hG : ∀ {m} {ρ : Wk m n} {Ε : Con k m} {a b}, ρ ∷ Ε ⊇ Δ → ⊢ Ε →
      (Ε ⊩⟨l⟩ a ≡ b : F₁.wk ρ) →
      Ε ⊩⟨l⟩ (G₁.wk ρ.lift).instantiate a ≡ (G₂.wk ρ.lift).instantiate b) :
    Δ ⊩⟨l⟩ pi p q F₁ G₁ ≡ pi p q F₂ G₂ := by
  have ⟨_, h₁, h₁₂⟩ := logicalRelation_pi hPi hF hG
  have hG₂ {m} {ρ : Wk m n} {Ε : Con k m} {a b} (hρ : ρ ∷ Ε ⊇ Δ) (hΕ : ⊢ Ε)
      (hab : Ε ⊩⟨l⟩ a ≡ b : F₂.wk ρ) :
      Ε ⊩⟨l⟩ (G₂.wk ρ.lift).instantiate a ≡ (G₂.wk ρ.lift).instantiate b :=
    have hab := hab.conv (hF hρ hΕ).symm
    (hG hρ hΕ (hab.trans hab.symm)).symm.trans (hG hρ hΕ hab)
  have ⟨_, h₂, _⟩ :=
    logicalRelation_pi (EqualityRelation.transType (EqualityRelation.symmType hPi) hPi)
      (fun hρ hΕ => (hF hρ hΕ).symm.trans (hF hρ hΕ)) hG₂
  exact ⟨_, _, h₁, h₂, h₁₂⟩

/--
Two types of functions are validly equal terms of the universe of the larger of the levels of their
domains and of their codomains, when their domains and their codomains are.

Under two reducibly equal substitutions, the domains are reducibly equal types at the value of the
larger level, in every well-formed context that contains the substituted one, and so are the
codomains at reducibly equal arguments, since the substitutions extended by these arguments are
reducibly equal: the substituted types of functions are reducibly equal, and equal by the equality
relation, which the interpretation of the universe asks for.
-/
theorem ValidTermEq.pi (hA : Γ ⊩ᵛ⟨l₁⟩ A₁ ≡ A₂ : Term.univ L₁)
    (hB : Γ ∙ A₁ ⊩ᵛ⟨l₂⟩ B₁ ≡ B₂ : Term.univ L₂) :
    Γ ⊩ᵛ⟨(L₁ ⊔ L₂).bound + 1⟩ Term.pi p q A₁ B₁ ≡ Term.pi p q A₂ B₂ : Term.univ (L₁ ⊔ L₂) := by
  have hA' := hA.toTypeEq
  have hB' := hB.toTypeEq
  have hA₁ := hA'.trans hA'.symm
  have hA₁' := hA₁.emb (Nat.le_max_left L₁.bound L₂.bound)
  have hA'' : Γ ⊩ᵛ⟨(L₁ ⊔ L₂).bound⟩ A₁ ≡ A₂ := hA'.emb (Nat.le_max_left L₁.bound L₂.bound)
  have hB'' : Γ ∙ A₁ ⊩ᵛ⟨(L₁ ⊔ L₂).bound⟩ B₁ ≡ B₂ := hB'.emb (Nat.le_max_right L₁.bound L₂.bound)
  rw [ValidTypeEq.unfold] at hA'' hB''
  refine ⟨ValidTypeEq.univ hA''.1, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  have hΔ := hσ.wfCon
  have ⟨_, hU₁, hA₁₂⟩ := hA.2 hσ
  have ⟨_, hU₂, hB₁₂⟩ := hB.2 (hσ.lift hA₁)
  have hPi := EqualityRelation.pi (p := p) (q := q) (hU₁.escape_eq hA₁₂) (hU₂.escape_eq hB₁₂)
  have ⟨hPi₁, hPi₂, _⟩ := (EqualityRelation.termEq hPi).wf
  have ⟨_, _, h₁, h₂, h₁₂⟩ :=
    reducibleTypeEq_pi (l := (L₁ ⊔ L₂).bound) (EqualityRelation.ofUniv hPi)
      (fun hρ hΕ => by
        rw [wk_subst, wk_subst]
        exact hA''.2 (hσ.wk hρ hΕ))
      (fun hρ hΕ hab => by
        rw [wk_lift_subst_lift, wk_lift_subst_lift, subst_lift_instantiate, subst_lift_instantiate]
        exact hB''.2 ((hσ.wk hρ hΕ).cons hA₁' (wk_subst _ _ A₁ ▸ hab)))
  have hU : Δ ⊩⟨(L₁ ⊔ L₂).bound + 1⟩ Term.univ (L₁ ⊔ L₂) ▸ _ := LogicalRelation.unfold ▸
    LogRel.univ (L := L₁ ⊔ L₂) (Nat.lt_succ_self _) (.refl (.univ (.univ hΔ)))
  exact ⟨_, hU, _, _, ⟨.refl hPi₁, .pi⟩, ⟨.refl hPi₂, .pi⟩, .pi, .pi, hPi, _, h₁, ⟨_, h₂⟩, h₁₂⟩

end Sic.Core.Reducibility
