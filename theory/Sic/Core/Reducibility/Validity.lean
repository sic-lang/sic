module

public import Sic.Core.Reducibility.Hidden
import Sic.Core.Reducibility.Neutral
import Sic.Core.Reducibility.Weakening
import Sic.Core.WellFormed

/-!
# Validity

The validity of the judgments, as in the formalization of ADE: a judgment is valid when it holds
reducibly under every pair of reducibly equal substitutions, so that the fundamental lemma, which
makes every judgment of `Sic.Core.Typing` valid, can substitute its variables.
A context is valid when each of its types is valid in the rest of the context, and two
substitutions are reducibly equal when they replace each variable by two terms reducibly equal at
its type, substituted, which must be valid.
Each judgment is a valid equality, and a type or a term is valid when it is validly equal to itself.
The validities are defined together, by recursion on the context.

## Correspondence with the Formalizations of ADE and of Pujet

| Definition or theorem | Definition or theorem of ADE, in `Definition/LogicalRelation/Substitution.agda` | Of Pujet, in `Definition/LogicalRelation/Substitution.agda` or `Substitution/Properties.agda` |
| --- | --- | --- |
| `ValidCon` | `_»⊩ᵛ_` | `⊩ᵛ_` |
| `ValidTypeEq` | `_⊩ᵛ⟨_⟩_≡_`, and `_⊩ᵛ⟨_⟩_` for a type equal to itself | `_⊩ᵛ⟨_⟩_≡_/_/_`, `_⊩ᵛ⟨_⟩_/_` |
| `ValidTermEq` | `_⊩ᵛ⟨_⟩_≡_∷_`, and `_⊩ᵛ⟨_⟩_∷_` for a term equal to itself | `_⊩ᵛ⟨_⟩_≡_∷_/_/_`, `_⊩ᵛ⟨_⟩_∷_/_/_` |
| `ReducibleSubstEq` | `_⊩ˢ_≡_∷_`, and `_⊩ˢ_∷_` for a substitution equal to itself | `_⊩ˢ_≡_∷_/_/_/_`, `_⊩ˢ_∷_/_/_` |
| `ValidCon.unfold_empty`, `ValidCon.unfold_snoc`, `ValidTypeEq.unfold`, `ReducibleSubstEq.unfold_empty`, `ReducibleSubstEq.unfold_snoc` | the characterization lemmas `⊩ᵛε⇔`, `⊩ᵛ∙⇔`, `⊩ᵛ≡⇔`, `⊩ˢ≡∷ε⇔`, `⊩ˢ≡∷∙⇔` | none |
| `ReducibleSubstEq.wfCon` | the first part of `escape-⊩ˢ≡∷` | none, since `⊢ Δ` is an argument of each validity |
| `ReducibleSubstEq.substEq`, `ReducibleSubstEq.substWf` | the second part of `escape-⊩ˢ≡∷`, and `escape-⊩ˢ∷` | `wellformedSubstEq`, `wellformedSubst` |
| `ReducibleSubstEq.cons` | `⊩ˢ≡∷∙⇔`, which characterizes the substitutions of a longer context | `consSubstSEq` |
| `ReducibleSubstEq.wk` | `⊩ˢ≡∷-•ₛ` | `wkSubstSEq` |
| `ReducibleTermEq.var` | `⊩var`, in `Definition/LogicalRelation/Substitution/Introductions/Var.agda`, for the last variable | none |
| `ReducibleSubstEq.lift` | `⊩ˢ≡∷-liftSubst` | `liftSubstSEq` |
| `ReducibleSubstEq.var` | `⊩ˢ∷-idSubst` | `idSubstS` |
| `ReducibleSubstEq.symm` | `sym-⊩ˢ≡∷` | `symS` |
| `ReducibleSubstEq.left` | `refl-⊩ˢ≡∷` | none, since the equality of two substitutions carries the proofs of their reducibility |
| `ValidTypeEq.symm`, `ValidTermEq.symm` | `sym-⊩ᵛ≡`, `sym-⊩ᵛ≡∷` | none |
| `ValidTypeEq.trans`, `ValidTermEq.trans` | `trans-⊩ᵛ≡`, `trans-⊩ᵛ≡∷` | none |
| `ValidTermEq.conv` | `conv-⊩ᵛ≡∷` | `convᵛ`, `convEqᵛ` |
| `ValidTypeEq.emb`, `ValidTermEq.emb` | `emb-⊩ᵛ≡`, `emb-⊩ᵛ≡∷` | none, with a single universe |
| `ValidTypeEq.wk1`, `ValidTermEq.wk1` | `wk1-⊩ᵛ≡`, `wk1-⊩ᵛ≡∷` | `wk1ᵛ`, `wk1Eqᵛ` for the types |

Pujet's validities carry the proofs of the validity of the context, of the reducibility of the
substitutions and of the substituted types, on which the others depend, which needs
induction-recursion, while those here, as ADE's, are equalities that depend on no proof.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

variable [EqualityRelation]

/-!
The validity of a type reads the reducible substitutions of its context, and the reducible
substitutions of a longer context read the validity of a type of the shorter one: the recursion
decreases the length of the context, and, for a context of the same length, goes from the validity
of a type to the validity of the context and to the reducible substitutions.
-/

mutual

/-- `⊩ᵛ Γ`: each type of the context `Γ` is valid, at some level, in the rest of the context. -/
def ValidCon : Con k n → Prop
  | .empty => True
  | .snoc Γ A => ∃ l, ValidTypeEq Γ l A A
termination_by (n, 0)

/--
`Γ ⊩ᵛ⟨l⟩ A ≡ B`: the context `Γ` is valid, and every two reducibly equal substitutions of `Γ`
replace the variables of the types `A` and `B` by terms that make them reducibly equal at the level
`l`.
-/
def ValidTypeEq (Γ : Con k n) (l : Nat) (A B : Term k n) : Prop :=
  ValidCon Γ ∧ ∀ {m} {Δ : Con k m} {σ₁ σ₂ : Subst k m n}, ReducibleSubstEq Δ σ₁ σ₂ Γ →
    Δ ⊩⟨l⟩ A.subst σ₁ ≡ B.subst σ₂
termination_by (n, 1)

/--
`Δ ⊩ˢ σ₁ ≡ σ₂ : Γ`: the context `Δ` is well formed, and the substitutions `σ₁` and `σ₂` replace each
variable of the context `Γ` by two terms of `Δ` reducibly equal at its type, substituted by `σ₁`,
which is valid in the rest of `Γ`.
-/
def ReducibleSubstEq (Δ : Con k m) : Subst k m n → Subst k m n → Con k n → Prop
  | _, _, .empty => ⊢ Δ
  | σ₁, σ₂, .snoc Γ A =>
    (∃ l, ValidTypeEq Γ l A A ∧ Δ ⊩⟨l⟩ σ₁ 0 ≡ σ₂ 0 : A.subst (σ₁ ·.succ)) ∧
      ReducibleSubstEq Δ (σ₁ ·.succ) (σ₂ ·.succ) Γ
termination_by (n, 0)

end

@[inherit_doc] notation:40 "⊩ᵛ " Γ:41 => ValidCon Γ

@[inherit_doc] notation:40 Γ:41 " ⊩ᵛ⟨" l "⟩ " A:41 " ≡ " B:41 => ValidTypeEq Γ l A B

@[inherit_doc] notation:40 Δ:41 " ⊩ˢ " σ₁:41 " ≡ " σ₂:41 " : " Γ:41 => ReducibleSubstEq Δ σ₁ σ₂ Γ

/--
`Γ ⊩ᵛ⟨l⟩ t ≡ u : A`: the type `A` is valid at the level `l`, and every two reducibly equal
substitutions of the context `Γ` replace the variables of the terms `t` and `u` by terms that make
them reducibly equal at `A`, substituted by the first.
-/
def ValidTermEq (Γ : Con k n) (l : Nat) (t u A : Term k n) : Prop :=
  (Γ ⊩ᵛ⟨l⟩ A ≡ A) ∧ ∀ {m} {Δ : Con k m} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
    Δ ⊩⟨l⟩ t.subst σ₁ ≡ u.subst σ₂ : A.subst σ₁

@[inherit_doc]
notation:40 Γ:41 " ⊩ᵛ⟨" l "⟩ " t:41 " ≡ " u:41 " : " A:41 => ValidTermEq Γ l t u A

/-- The empty context is valid. -/
theorem ValidCon.unfold_empty : (⊩ᵛ (.empty : Con k 0)) = True := by
  rw [ValidCon]

/-- A longer context is valid when its last type is valid, at some level, in the rest of it. -/
theorem ValidCon.unfold_snoc {Γ : Con k n} {A : Term k n} :
    (⊩ᵛ (Γ ∙ A)) = ∃ l, Γ ⊩ᵛ⟨l⟩ A ≡ A := by
  rw [ValidCon]

/-- The validity of the equality of two types, as `ValidTypeEq` defines it. -/
theorem ValidTypeEq.unfold {Γ : Con k n} {A B : Term k n} :
    (Γ ⊩ᵛ⟨l⟩ A ≡ B) = ((⊩ᵛ Γ) ∧ ∀ {m} {Δ : Con k m} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
      Δ ⊩⟨l⟩ A.subst σ₁ ≡ B.subst σ₂) := by
  rw [ValidTypeEq]

/-- Two substitutions of the empty context are reducibly equal when their context is well formed. -/
theorem ReducibleSubstEq.unfold_empty {Δ : Con k m} {σ₁ σ₂ : Subst k m 0} :
    (Δ ⊩ˢ σ₁ ≡ σ₂ : .empty) = (⊢ Δ) := by
  rw [ReducibleSubstEq]

/--
Two substitutions of a longer context are reducibly equal when they replace its last variable by two
terms reducibly equal at its valid type, substituted, and the other variables as two reducibly
equal substitutions.
-/
theorem ReducibleSubstEq.unfold_snoc {Δ : Con k m} {Γ : Con k n} {A : Term k n}
    {σ₁ σ₂ : Subst k m (n + 1)} :
    (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ ∙ A) = ((∃ l, (Γ ⊩ᵛ⟨l⟩ A ≡ A) ∧ Δ ⊩⟨l⟩ σ₁ 0 ≡ σ₂ 0 : A.subst (σ₁ ·.succ)) ∧
      Δ ⊩ˢ (σ₁ ·.succ) ≡ (σ₂ ·.succ) : Γ) := by
  rw [ReducibleSubstEq]

/-- The context of two reducibly equal substitutions is well formed. -/
theorem ReducibleSubstEq.wfCon : ∀ {Γ : Con k n} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) → ⊢ Δ
  | .empty, _, _, hσ => ReducibleSubstEq.unfold_empty ▸ hσ
  | .snoc _ _, _, _, hσ => (ReducibleSubstEq.unfold_snoc ▸ hσ).2.wfCon

/-- Two substitutions extended by two terms reducibly equal at a valid type are reducibly equal. -/
theorem ReducibleSubstEq.cons (hσ : Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) (hA : Γ ⊩ᵛ⟨l⟩ A ≡ A)
    (ha : Δ ⊩⟨l⟩ a₁ ≡ a₂ : A.subst σ₁) : Δ ⊩ˢ σ₁.cons a₁ ≡ σ₂.cons a₂ : Γ ∙ A := by
  rw [ReducibleSubstEq.unfold_snoc]
  exact ⟨⟨l, hA, ha⟩, hσ⟩

/--
Two reducibly equal substitutions stay reducibly equal when their terms move to a well-formed
context that contains their own.
-/
theorem ReducibleSubstEq.wk {Δ : Con k m} {Ε : Con k m'} {ρ : Wk m' m} (hρ : ρ ∷ Ε ⊇ Δ)
    (hΕ : ⊢ Ε) : ∀ {Γ : Con k n} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
      Ε ⊩ˢ (fun x => (σ₁ x).wk ρ) ≡ (fun x => (σ₂ x).wk ρ) : Γ
  | .empty, _, _, _ => ReducibleSubstEq.unfold_empty ▸ hΕ
  | .snoc _ A, _, _, hσ => by
    rw [ReducibleSubstEq.unfold_snoc] at hσ ⊢
    have ⟨⟨l, hA, ha⟩, hσ⟩ := hσ
    exact ⟨⟨l, hA, wk_subst ρ _ A ▸ ha.wk hρ hΕ⟩, ReducibleSubstEq.wk hρ hΕ hσ⟩

/--
Two reducibly equal substitutions are equal substitutions of `Sic.Core.Typing`, since their terms
are equal at the types they substitute.
-/
theorem ReducibleSubstEq.substEq : ∀ {Γ : Con k n} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
    Δ ⊢ˢ σ₁ ≡ σ₂ : Γ
  | .empty, _, _, _ => fun x => x.elim0
  | .snoc _ _, _, _, hσ => by
    rw [ReducibleSubstEq.unfold_snoc] at hσ
    have ⟨⟨_, _, _, hA, ha⟩, hσ⟩ := hσ
    intro
    | ⟨0, _⟩ =>
      show _ ⊢ _ ≡ _ : (Con.get _ 0).subst _
      rw [Con.get_zero, subst_wk]
      exact hA.escape_eqTerm ha
    | ⟨x + 1, hx⟩ =>
      show _ ⊢ _ ≡ _ : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst _
      rw [Con.get_succ, subst_wk]
      exact hσ.substEq ⟨x, Nat.lt_of_succ_lt_succ hx⟩

/-- The first of two reducibly equal substitutions is a substitution of `Sic.Core.Typing`. -/
theorem ReducibleSubstEq.substWf (hσ : Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) : Δ ⊢ˢ σ₁ : Γ :=
  fun x => (hσ.substEq x).wf.1

/--
The variable of a declaration of a type reducible in a well-formed context is a reducible term of
that type, weakened.
-/
theorem ReducibleTermEq.var (hA : Γ ⊩⟨l⟩ A ▸ P) (hΓA : ⊢ Γ ∙ A) :
    Γ ∙ A ⊩⟨l⟩ var 0 ≡ var 0 : A.wk1 :=
  let ⟨_, hA'⟩ := hA.wk (.step .id) hΓA
  ⟨_, hA', hA'.neutral_eqTerm .var .var (EqualityRelation.var (.var hΓA))⟩

/--
Two reducibly equal substitutions, extended under a binder of a valid type, are reducibly equal in
the context extended by that type, substituted, which is well formed since the type is reducible.
-/
theorem ReducibleSubstEq.lift (hσ : Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) (hA : Γ ⊩ᵛ⟨l⟩ A ≡ A) :
    Δ ∙ A.subst σ₁ ⊩ˢ σ₁.lift ≡ σ₂.lift : Γ ∙ A := by
  have hA₁ : Δ ⊩⟨l⟩ A.subst σ₁ ≡ A.subst σ₂ := by rw [ValidTypeEq.unfold] at hA; exact hA.2 hσ
  have ⟨_, _, hA₁, _⟩ := hA₁
  have hΔA : ⊢ Δ ∙ A.subst σ₁ := .snoc hA₁.escape
  refine ReducibleSubstEq.cons (hσ.wk (.step .id) hΔA) hA ?_
  rw [← wk_subst]
  exact ReducibleTermEq.var hA₁ hΔA

/-- The identity substitution of a valid context is reducible. -/
theorem ReducibleSubstEq.var : ∀ {Γ : Con k n}, (⊩ᵛ Γ) → Γ ⊩ˢ .var ≡ .var : Γ
  | .empty, _ => ReducibleSubstEq.unfold_empty ▸ .empty
  | .snoc Γ A, hΓA => by
    rw [ValidCon.unfold_snoc] at hΓA
    have ⟨_, hA⟩ := hΓA
    have hΓ : ⊩ᵛ Γ := by rw [ValidTypeEq.unfold] at hA; exact hA.1
    have h := (ReducibleSubstEq.var hΓ).lift hA
    rw [Subst.lift_var, subst_var] at h
    exact h

/-!
The validities are partial equivalences, as the reducible equalities, and each of them holds at
every level larger than its own: the symmetry of two substitutions converts the terms of the second
to the types it substitutes, and the other properties hold under each pair of substitutions, where
the first substitution is reducibly equal to itself.
-/

/-- Two reducibly equal substitutions are reducibly equal in the other order. -/
theorem ReducibleSubstEq.symm : ∀ {Γ : Con k n} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
    Δ ⊩ˢ σ₂ ≡ σ₁ : Γ
  | .empty, _, _, hσ => ReducibleSubstEq.unfold_empty ▸ ReducibleSubstEq.unfold_empty ▸ hσ
  | .snoc _ _, _, _, hσ => by
    rw [ReducibleSubstEq.unfold_snoc] at hσ ⊢
    have ⟨⟨l, hA, ha⟩, hσ⟩ := hσ
    rw [ValidTypeEq.unfold] at hA
    exact ⟨⟨l, ValidTypeEq.unfold ▸ hA, ha.symm.conv (hA.2 hσ)⟩, hσ.symm⟩

/-- The first of two reducibly equal substitutions is reducibly equal to itself. -/
theorem ReducibleSubstEq.left : ∀ {Γ : Con k n} {σ₁ σ₂ : Subst k m n}, (Δ ⊩ˢ σ₁ ≡ σ₂ : Γ) →
    Δ ⊩ˢ σ₁ ≡ σ₁ : Γ
  | .empty, _, _, hσ => ReducibleSubstEq.unfold_empty ▸ ReducibleSubstEq.unfold_empty ▸ hσ
  | .snoc _ _, _, _, hσ => by
    rw [ReducibleSubstEq.unfold_snoc] at hσ ⊢
    have ⟨⟨l, hA, ha⟩, hσ⟩ := hσ
    exact ⟨⟨l, hA, ha.trans ha.symm⟩, hσ.left⟩

/-- Two validly equal types are validly equal in the other order. -/
theorem ValidTypeEq.symm (h : Γ ⊩ᵛ⟨l⟩ A ≡ B) : Γ ⊩ᵛ⟨l⟩ B ≡ A := by
  rw [ValidTypeEq.unfold] at h ⊢
  exact ⟨h.1, fun hσ => (h.2 hσ.symm).symm⟩

/-- Two types validly equal to the same type are validly equal. -/
theorem ValidTypeEq.trans (hAB : Γ ⊩ᵛ⟨l⟩ A ≡ B) (hBC : Γ ⊩ᵛ⟨l⟩ B ≡ C) : Γ ⊩ᵛ⟨l⟩ A ≡ C := by
  rw [ValidTypeEq.unfold] at hAB hBC ⊢
  exact ⟨hAB.1, fun hσ => (hAB.2 hσ.left).trans (hBC.2 hσ)⟩

/-- Two types validly equal at a level are validly equal at every larger level. -/
theorem ValidTypeEq.emb (hl : l ≤ l') (h : Γ ⊩ᵛ⟨l⟩ A ≡ B) : Γ ⊩ᵛ⟨l'⟩ A ≡ B := by
  rw [ValidTypeEq.unfold] at h ⊢
  exact ⟨h.1, fun hσ => (h.2 hσ).emb hl⟩

/--
Two validly equal types stay validly equal, moved past a new variable, in the context extended by a
valid type.
-/
theorem ValidTypeEq.wk1 (h : Γ ⊩ᵛ⟨l⟩ A ≡ B) (hC : Γ ⊩ᵛ⟨l'⟩ C ≡ C) :
    Γ ∙ C ⊩ᵛ⟨l⟩ A.wk1 ≡ B.wk1 := by
  rw [ValidTypeEq.unfold] at h ⊢
  refine ⟨ValidCon.unfold_snoc ▸ ⟨l', hC⟩, fun hσ => ?_⟩
  rw [ReducibleSubstEq.unfold_snoc] at hσ
  rw [subst_wk, subst_wk]
  exact h.2 hσ.2

/-- Two validly equal terms are validly equal in the other order. -/
theorem ValidTermEq.symm (h : Γ ⊩ᵛ⟨l⟩ t ≡ u : A) : Γ ⊩ᵛ⟨l⟩ u ≡ t : A := by
  have hA := h.1
  rw [ValidTypeEq.unfold] at hA
  exact ⟨h.1, fun hσ => (h.2 hσ.symm).symm.conv (hA.2 hσ.symm)⟩

/-- Two terms validly equal to the same term are validly equal. -/
theorem ValidTermEq.trans (htu : Γ ⊩ᵛ⟨l⟩ t ≡ u : A) (huv : Γ ⊩ᵛ⟨l⟩ u ≡ v : A) :
    Γ ⊩ᵛ⟨l⟩ t ≡ v : A :=
  ⟨htu.1, fun hσ => (htu.2 hσ.left).trans (huv.2 hσ)⟩

/--
Two terms validly equal at a type are validly equal at every type validly equal to it, at the level
of that equality.
-/
theorem ValidTermEq.conv (h : Γ ⊩ᵛ⟨l⟩ t ≡ u : A) (hAB : Γ ⊩ᵛ⟨l'⟩ A ≡ B) :
    Γ ⊩ᵛ⟨l'⟩ t ≡ u : B := by
  refine ⟨hAB.symm.trans hAB, fun hσ => ?_⟩
  rw [ValidTypeEq.unfold] at hAB
  exact (h.2 hσ).conv (hAB.2 hσ.left)

/-- Two terms validly equal at a level are validly equal at every larger level. -/
theorem ValidTermEq.emb (hl : l ≤ l') (h : Γ ⊩ᵛ⟨l⟩ t ≡ u : A) : Γ ⊩ᵛ⟨l'⟩ t ≡ u : A :=
  ⟨h.1.emb hl, fun hσ => (h.2 hσ).emb hl⟩

/--
Two validly equal terms stay validly equal, moved past a new variable, in the context extended by a
valid type.
-/
theorem ValidTermEq.wk1 (h : Γ ⊩ᵛ⟨l⟩ t ≡ u : A) (hC : Γ ⊩ᵛ⟨l'⟩ C ≡ C) :
    Γ ∙ C ⊩ᵛ⟨l⟩ t.wk1 ≡ u.wk1 : A.wk1 := by
  refine ⟨h.1.wk1 hC, fun hσ => ?_⟩
  rw [ReducibleSubstEq.unfold_snoc] at hσ
  rw [subst_wk, subst_wk, subst_wk]
  exact h.2 hσ.2

end Sic.Core.Reducibility
