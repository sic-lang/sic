module

public import Sic.Core.Typing

/-!
# Typed Substitution

The judgments of `Sic.Core.Typing` moved to another context, as in the formalization of ADE: a
judgment holds in every well-formed context that contains its own, by weakening, and with its
variables replaced by terms of their types, by substitution, which instantiates a binder in
particular.
Two equal substitutions give two equal terms, and the type of the last declaration of a context can
be replaced by an equal type.

## Correspondence with the Formalization of ADE

ADE prove the weakening and the substitutions by induction on the size of the derivations, which
their judgments, in `Set`, have, while those of `Sic.Core.Typing` are propositions: each proof here
proves a stronger statement instead, which the module explains.
-/

@[expose] public section

namespace Sic.Core

open Term

set_option hygiene false in
/--
`ρ ∷ Δ ⊇ Γ`: the weakening `ρ` moves the context `Γ` to `Δ`, which contains its declarations in the
same order.
-/
notation:40 ρ:41 " ∷ " Δ:51 " ⊇ " Γ:51 => WkCon ρ Δ Γ

-- ADE: `_∷_⊇_`, in `Definition/Typed/Weakening.agda`.
/--
`ρ ∷ Δ ⊇ Γ`: the weakening `ρ` moves the context `Γ` to `Δ`, which contains its declarations in the
same order.
-/
inductive WkCon {k : Nat} : {m n : Nat} → Wk m n → Con k m → Con k n → Prop where
  /-- The weakening `Sic.Core.Wk.id` keeps the context. -/
  | id : .id ∷ Γ ⊇ Γ
  /-- A step adds a declaration of any type after the context. -/
  | step : ρ ∷ Δ ⊇ Γ → ρ.step ∷ Δ ∙ A ⊇ Γ
  /-- A lift keeps the last declaration, whose type it moves as the rest of the context. -/
  | lift : ρ ∷ Δ ⊇ Γ → ρ.lift ∷ Δ ∙ A.wk ρ ⊇ Γ ∙ A

/-- A variable moved by a weakening has the type of the variable, moved by the weakening. -/
theorem WkCon.get_var : ρ ∷ Δ ⊇ Γ → ∀ x, Δ.get (ρ.var x) = (Γ.get x).wk ρ
  | .id, _ => (wk_id _).symm
  | .step (ρ := ρ) h, x => by
    show Con.get _ (ρ.var x).succ = _
    rw [Con.get_succ, h.get_var x, wk_step]
  | .lift (A := A) h, ⟨0, _⟩ => (wk_lift_wk1 _ A).symm
  | .lift h, ⟨x + 1, hx⟩ => by
    have := h.get_var ⟨x, Nat.lt_of_succ_lt_succ hx⟩
    simp only [Wk.var] at *
    rw [Con.get_succ, this, ← wk_lift_wk1]
    rfl

-- ADE: `_•ₜ_`, in `Definition/Typed/Weakening.agda`.
/-- Two weakenings of contexts in a row are the weakening by their composition. -/
theorem WkCon.comp : ρ₁ ∷ Ε ⊇ Δ → ρ₂ ∷ Δ ⊇ Γ → ρ₁.comp ρ₂ ∷ Ε ⊇ Γ
  | .id, h₂ => h₂
  | .step h₁, h₂ => .step (h₁.comp h₂)
  | .lift h₁, .id => .lift h₁
  | .lift h₁, .step h₂ => .step (h₁.comp h₂)
  | .lift h₁, .lift h₂ => by
    rw [wk_comp]
    exact .lift (h₁.comp h₂)

-- ADE: `_⊢ˢʷ_∷_`, with `⊢ Δ`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/--
`Δ ⊢ˢ σ : Γ`: the substitution `σ` replaces each variable of the context `Γ` by a term of `Δ`, whose
type is the one of the variable, substituted.
-/
def SubstWf (Δ : Con k m) (σ : Subst k m n) (Γ : Con k n) : Prop :=
  ∀ x, Δ ⊢ σ x : (Γ.get x).subst σ

@[inherit_doc] notation:40 Δ:41 " ⊢ˢ " σ:41 " : " Γ:41 => SubstWf Δ σ Γ

/-!
The weakening of the judgments, by induction on their derivations.
Under a binder, the induction moves the judgment to the context `Δ` extended by the type `A` of the
bound variable, moved to `Δ`, which needs that type to be well formed in `Δ`: the rules state that
`A` is well formed in `Γ` in the premise `⊢ Γ ∙ A` of a judgment in `Γ ∙ A`, but deep in its
derivation, where the induction does not reach it.
The induction thus proves a stronger statement, `WkLast`: each judgment, along with its weakening,
weakens the last type of its context, which a judgment in `Γ ∙ A` gives for `A`.
-/

/-- The last type of the context `Γ` is well formed in every well-formed context that contains it. -/
private def WkLast {k n : Nat} (Γ : Con k n) : Prop :=
  match n, Γ with
  | _, .empty => True
  | _, .snoc Γ A => ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ A.wk ρ

mutual

private theorem WfCon.wkLast {Γ : Con k n} : ⊢ Γ → WkLast Γ
  | .empty => trivial
  | .snoc h => fun hρ hΔ => h.wkStrong.2 hρ hΔ

private theorem IsType.wkStrong {Γ : Con k n} {A : Term k n} : Γ ⊢ A →
    WkLast Γ ∧ ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ A.wk ρ
  | .univ h => ⟨h.wkStrong.1, fun hρ hΔ => .univ (h.wkStrong.2 hρ hΔ)⟩

private theorem TypeEq.wkStrong {Γ : Con k n} {A B : Term k n} : Γ ⊢ A ≡ B →
    WkLast Γ ∧ ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ A.wk ρ ≡ B.wk ρ
  | .univ h => ⟨h.wkStrong.1, fun hρ hΔ => .univ (h.wkStrong.2 hρ hΔ)⟩
  | .refl h => ⟨h.wkStrong.1, fun hρ hΔ => .refl (h.wkStrong.2 hρ hΔ)⟩
  | .symm h => ⟨h.wkStrong.1, fun hρ hΔ => .symm (h.wkStrong.2 hρ hΔ)⟩
  | .trans h₁ h₂ =>
    ⟨h₁.wkStrong.1, fun hρ hΔ => .trans (h₁.wkStrong.2 hρ hΔ) (h₂.wkStrong.2 hρ hΔ)⟩

private theorem HasType.wkStrong {Γ : Con k n} {t A : Term k n} : Γ ⊢ t : A →
    WkLast Γ ∧ ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ t.wk ρ : A.wk ρ
  | .var h => ⟨h.wkLast, fun hρ hΔ => by rw [← hρ.get_var]; exact .var hΔ⟩
  | .conv h hA => ⟨h.wkStrong.1, fun hρ hΔ => .conv (h.wkStrong.2 hρ hΔ) (hA.wkStrong.2 hρ hΔ)⟩
  | .univ h => ⟨h.wkLast, fun _ hΔ => .univ hΔ⟩
  | .pi hA hB => ⟨hA.wkStrong.1, fun hρ hΔ =>
      have hA' := hA.wkStrong.2 hρ hΔ
      .pi hA' (hB.wkStrong.2 hρ.lift (.snoc (.univ hA')))⟩
  | .lam hPi ht => ⟨hPi.wkStrong.1, fun hρ hΔ =>
      have hA := ht.wkStrong.1 hρ hΔ
      .lam (hPi.wkStrong.2 hρ hΔ) (ht.wkStrong.2 hρ.lift (.snoc hA))⟩
  | .app ht ha => ⟨ht.wkStrong.1, fun hρ hΔ => by
      rw [wk_instantiate]
      exact .app (ht.wkStrong.2 hρ hΔ) (ha.wkStrong.2 hρ hΔ)⟩

private theorem TermEq.wkStrong {Γ : Con k n} {t u A : Term k n} : Γ ⊢ t ≡ u : A →
    WkLast Γ ∧ ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ t.wk ρ ≡ u.wk ρ : A.wk ρ
  | .refl h => ⟨h.wkStrong.1, fun hρ hΔ => .refl (h.wkStrong.2 hρ hΔ)⟩
  | .symm h => ⟨h.wkStrong.1, fun hρ hΔ => .symm (h.wkStrong.2 hρ hΔ)⟩
  | .trans h₁ h₂ =>
    ⟨h₁.wkStrong.1, fun hρ hΔ => .trans (h₁.wkStrong.2 hρ hΔ) (h₂.wkStrong.2 hρ hΔ)⟩
  | .conv h hA => ⟨h.wkStrong.1, fun hρ hΔ => .conv (h.wkStrong.2 hρ hΔ) (hA.wkStrong.2 hρ hΔ)⟩
  | .univ h hl => ⟨h.wkLast, fun _ hΔ => .univ hΔ hl⟩
  | .pi hA hB => ⟨hA.wkStrong.1, fun hρ hΔ =>
      have hA₁ := hB.wkStrong.1 hρ hΔ
      .pi (hA.wkStrong.2 hρ hΔ) (hB.wkStrong.2 hρ.lift (.snoc hA₁))⟩
  | .lam hPi hA ht => ⟨hPi.wkStrong.1, fun hρ hΔ =>
      have hA₁ := ht.wkStrong.1 hρ hΔ
      .lam (hPi.wkStrong.2 hρ hΔ) (hA.wkStrong.2 hρ hΔ) (ht.wkStrong.2 hρ.lift (.snoc hA₁))⟩
  | .app ht ha => ⟨ht.wkStrong.1, fun hρ hΔ => by
      rw [wk_instantiate]
      exact .app (ht.wkStrong.2 hρ hΔ) (ha.wkStrong.2 hρ hΔ)⟩
  | .beta hPi ht ha => ⟨hPi.wkStrong.1, fun hρ hΔ => by
      have hA := ht.wkStrong.1 hρ hΔ
      rw [wk_instantiate, wk_instantiate]
      exact .beta (hPi.wkStrong.2 hρ hΔ) (ht.wkStrong.2 hρ.lift (.snoc hA)) (ha.wkStrong.2 hρ hΔ)⟩
  | .eta h => ⟨h.wkStrong.1, fun hρ hΔ => by
      have := TermEq.eta (h.wkStrong.2 hρ hΔ)
      simp only [wk, wk_lift_wk1] at this ⊢
      exact this⟩

end

-- ADE: `wk`, in `Definition/Typed/Weakening.agda`.
/-- A type stays a type in every well-formed context that contains its own. -/
theorem IsType.wk (h : Γ ⊢ A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ A.wk ρ :=
  h.wkStrong.2 hρ hΔ

-- ADE: `wkEq`, in `Definition/Typed/Weakening.agda`.
/-- Two types stay equal in every well-formed context that contains their own. -/
theorem TypeEq.wk (h : Γ ⊢ A ≡ B) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ A.wk ρ ≡ B.wk ρ :=
  h.wkStrong.2 hρ hΔ

-- ADE: `wkTerm`, in `Definition/Typed/Weakening.agda`.
/-- A term keeps its type in every well-formed context that contains its own. -/
theorem HasType.wk (h : Γ ⊢ t : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ t.wk ρ : A.wk ρ :=
  h.wkStrong.2 hρ hΔ

-- ADE: `wkEqTerm`, in `Definition/Typed/Weakening.agda`.
/-- Two terms stay equal in every well-formed context that contains their own. -/
theorem TermEq.wk (h : Γ ⊢ t ≡ u : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.wk ρ ≡ u.wk ρ : A.wk ρ :=
  h.wkStrong.2 hρ hΔ

-- ADE: `⊢ˢʷ∷-⇑`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- Under a binder, a substitution replaces the bound variable by the variable of its new binder. -/
theorem SubstWf.lift (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ ∙ A.subst σ) : Δ ∙ A.subst σ ⊢ˢ σ.lift : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ var 0 : A.wk1.subst σ.lift
    rw [subst_lift_wk1]
    exact .var hΔ
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ (σ _).wk1 : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst σ.lift
    rw [Con.get_succ, subst_lift_wk1]
    exact (hσ _).wk (.step .id) hΔ

-- ADE: `⊢ˢʷ∷-sgSubst`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The term `a` of the type `A` replaces the variable of that type, and the other variables stay. -/
theorem SubstWf.instantiate (ha : Γ ⊢ a : A) : Γ ⊢ˢ Subst.cons var a : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ a : A.wk1.subst _
    rw [subst_cons_wk1, subst_var]
    exact ha
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ var _ : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst _
    rw [Con.get_succ, subst_cons_wk1, subst_var]
    exact .var ha.wfCon

/-!
The substitution of the judgments, by induction on their derivations, which proves a stronger
statement, `SubstLast`, for the same reason as their weakening.
-/

/-- The last type of the context `Γ`, substituted, is well formed in every well-formed context. -/
private def SubstLast {k n : Nat} (Γ : Con k n) : Prop :=
  match n, Γ with
  | _, .empty => True
  | _, .snoc Γ A => ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → Δ ⊢ A.subst σ

mutual

private theorem WfCon.substLast {Γ : Con k n} : ⊢ Γ → SubstLast Γ
  | .empty => trivial
  | .snoc h => fun hσ hΔ => h.substStrong.2 hσ hΔ

private theorem IsType.substStrong {Γ : Con k n} {A : Term k n} : Γ ⊢ A →
    SubstLast Γ ∧ ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → Δ ⊢ A.subst σ
  | .univ h => ⟨h.substStrong.1, fun hσ hΔ => .univ (h.substStrong.2 hσ hΔ)⟩

private theorem TypeEq.substStrong {Γ : Con k n} {A B : Term k n} : Γ ⊢ A ≡ B →
    SubstLast Γ ∧ ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → Δ ⊢ A.subst σ ≡ B.subst σ
  | .univ h => ⟨h.substStrong.1, fun hσ hΔ => .univ (h.substStrong.2 hσ hΔ)⟩
  | .refl h => ⟨h.substStrong.1, fun hσ hΔ => .refl (h.substStrong.2 hσ hΔ)⟩
  | .symm h => ⟨h.substStrong.1, fun hσ hΔ => .symm (h.substStrong.2 hσ hΔ)⟩
  | .trans h₁ h₂ =>
    ⟨h₁.substStrong.1, fun hσ hΔ => .trans (h₁.substStrong.2 hσ hΔ) (h₂.substStrong.2 hσ hΔ)⟩

private theorem HasType.substStrong {Γ : Con k n} {t A : Term k n} : Γ ⊢ t : A →
    SubstLast Γ ∧ ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → Δ ⊢ t.subst σ : A.subst σ
  | .var h => ⟨h.substLast, fun hσ _ => hσ _⟩
  | .conv h hA =>
    ⟨h.substStrong.1, fun hσ hΔ => .conv (h.substStrong.2 hσ hΔ) (hA.substStrong.2 hσ hΔ)⟩
  | .univ h => ⟨h.substLast, fun _ hΔ => .univ hΔ⟩
  | .pi hA hB => ⟨hA.substStrong.1, fun hσ hΔ =>
      have hΔ' := WfCon.snoc (.univ (hA.substStrong.2 hσ hΔ))
      .pi (hA.substStrong.2 hσ hΔ) (hB.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .lam hPi ht => ⟨hPi.substStrong.1, fun hσ hΔ =>
      have hΔ' := WfCon.snoc (ht.substStrong.1 hσ hΔ)
      .lam (hPi.substStrong.2 hσ hΔ) (ht.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .app ht ha => ⟨ht.substStrong.1, fun hσ hΔ => by
      rw [subst_instantiate]
      exact .app (ht.substStrong.2 hσ hΔ) (ha.substStrong.2 hσ hΔ)⟩

private theorem TermEq.substStrong {Γ : Con k n} {t u A : Term k n} : Γ ⊢ t ≡ u : A →
    SubstLast Γ ∧ ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ →
      Δ ⊢ t.subst σ ≡ u.subst σ : A.subst σ
  | .refl h => ⟨h.substStrong.1, fun hσ hΔ => .refl (h.substStrong.2 hσ hΔ)⟩
  | .symm h => ⟨h.substStrong.1, fun hσ hΔ => .symm (h.substStrong.2 hσ hΔ)⟩
  | .trans h₁ h₂ =>
    ⟨h₁.substStrong.1, fun hσ hΔ => .trans (h₁.substStrong.2 hσ hΔ) (h₂.substStrong.2 hσ hΔ)⟩
  | .conv h hA =>
    ⟨h.substStrong.1, fun hσ hΔ => .conv (h.substStrong.2 hσ hΔ) (hA.substStrong.2 hσ hΔ)⟩
  | .univ h hl => ⟨h.substLast, fun _ hΔ => .univ hΔ hl⟩
  | .pi hA hB => ⟨hA.substStrong.1, fun hσ hΔ =>
      have hΔ' := WfCon.snoc (hB.substStrong.1 hσ hΔ)
      .pi (hA.substStrong.2 hσ hΔ) (hB.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .lam hPi hA ht => ⟨hPi.substStrong.1, fun hσ hΔ =>
      have hΔ' := WfCon.snoc (ht.substStrong.1 hσ hΔ)
      .lam (hPi.substStrong.2 hσ hΔ) (hA.substStrong.2 hσ hΔ) (ht.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .app ht ha => ⟨ht.substStrong.1, fun hσ hΔ => by
      rw [subst_instantiate]
      exact .app (ht.substStrong.2 hσ hΔ) (ha.substStrong.2 hσ hΔ)⟩
  | .beta hPi ht ha => ⟨hPi.substStrong.1, fun hσ hΔ => by
      have hΔ' := WfCon.snoc (ht.substStrong.1 hσ hΔ)
      rw [subst_instantiate, subst_instantiate]
      exact .beta (hPi.substStrong.2 hσ hΔ) (ht.substStrong.2 (hσ.lift hΔ') hΔ')
        (ha.substStrong.2 hσ hΔ)⟩
  | .eta h => ⟨h.substStrong.1, fun hσ hΔ => by
      have := TermEq.eta (h.substStrong.2 hσ hΔ)
      simp only [Term.subst, subst_lift_wk1] at this ⊢
      exact this⟩

end

-- ADE: `subst-⊢`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- A type whose variables are replaced by terms of their types stays a type. -/
theorem IsType.subst (h : Γ ⊢ A) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) : Δ ⊢ A.subst σ :=
  h.substStrong.2 hσ hΔ

-- ADE: `subst-⊢≡`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- Two equal types whose variables are replaced by terms of their types stay equal. -/
theorem TypeEq.subst (h : Γ ⊢ A ≡ B) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ A.subst σ ≡ B.subst σ :=
  h.substStrong.2 hσ hΔ

-- ADE: `subst-⊢∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- A term whose variables are replaced by terms of their types has the substituted type. -/
theorem HasType.subst (h : Γ ⊢ t : A) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.subst σ : A.subst σ :=
  h.substStrong.2 hσ hΔ

-- ADE: `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- Two equal terms whose variables are replaced by terms of their types stay equal. -/
theorem TermEq.subst (h : Γ ⊢ t ≡ u : A) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.subst σ ≡ u.subst σ : A.subst σ :=
  h.substStrong.2 hσ hΔ

/-- A term whose bound variable is replaced by a term of its type has the instantiated type. -/
theorem HasType.instantiate (ht : Γ ∙ A ⊢ t : B) (ha : Γ ⊢ a : A) :
    Γ ⊢ t.instantiate a : B.instantiate a :=
  ht.subst (.instantiate ha) ha.wfCon

-- ADE: `stability-⊢∷`, for contexts that only differ by their last type, in
-- `Definition/Typed/Stability/Primitive.agda`.
/--
A term keeps its type when the last declaration of its context gets an equal type, through the
substitution of each variable by itself, which converts the type of the last one.
-/
theorem HasType.conv_last (h : Γ ∙ A₁ ⊢ t : B) (hA : Γ ⊢ A₁ ≡ A₂) (hA₂ : Γ ⊢ A₂) :
    Γ ∙ A₂ ⊢ t : B := by
  have hΓ : ⊢ Γ ∙ A₂ := .snoc hA₂
  have hσ : Γ ∙ A₂ ⊢ˢ Term.var : Γ ∙ A₁
    | ⟨0, _⟩ => by
      rw [subst_var]
      exact .conv (.var hΓ) ((TypeEq.symm hA).wk (.step .id) hΓ)
    | ⟨x + 1, hx⟩ => by
      rw [subst_var]
      exact .var (x := ⟨x + 1, hx⟩) hΓ
  have := h.subst hσ hΓ
  rwa [subst_var, subst_var] at this

-- ADE: `_⊢ˢʷ_≡_∷_`, which also types `τ`, with `⊢ Δ` and `Δ ⊢ˢ σ : Γ`, in
-- `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/--
`Δ ⊢ˢ σ ≡ τ : Γ`: the substitutions `σ` and `τ` replace each variable of the context `Γ` by equal
terms of `Δ`, at the type of the variable, substituted by `σ`.
-/
def SubstEq (Δ : Con k m) (σ τ : Subst k m n) (Γ : Con k n) : Prop :=
  ∀ x, Δ ⊢ σ x ≡ τ x : (Γ.get x).subst σ

@[inherit_doc] notation:40 Δ:41 " ⊢ˢ " σ:41 " ≡ " τ:41 " : " Γ:41 => SubstEq Δ σ τ Γ

-- ADE: `⊢ˢʷ≡∷-⇑`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- Under a binder, two equal substitutions replace the bound variable by the same variable. -/
theorem SubstEq.lift (hστ : Δ ⊢ˢ σ ≡ τ : Γ) (hΔ : ⊢ Δ ∙ A.subst σ) :
    Δ ∙ A.subst σ ⊢ˢ σ.lift ≡ τ.lift : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ var 0 ≡ var 0 : A.wk1.subst σ.lift
    rw [subst_lift_wk1]
    exact .refl (.var hΔ)
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ (σ _).wk1 ≡ (τ _).wk1 :
      (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst σ.lift
    rw [Con.get_succ, subst_lift_wk1]
    exact (hστ _).wk (.step .id) hΔ

-- ADE: `⊢ˢʷ≡∷-sgSubst`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The equal terms `a₁` and `a₂` replace the variable of their type, and the others stay. -/
theorem SubstEq.instantiate (ha : Γ ⊢ a₁ ≡ a₂ : A) :
    Γ ⊢ˢ Subst.cons var a₁ ≡ Subst.cons var a₂ : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ a₁ ≡ a₂ : A.wk1.subst _
    rw [subst_cons_wk1, subst_var]
    exact ha
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ var _ ≡ var _ : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst _
    rw [Con.get_succ, subst_cons_wk1, subst_var]
    exact .refl (.var ha.wfCon)

/-!
A term whose variables are replaced by two equal substitutions gives two equal terms, by induction
on its derivation.
Under the abstraction `lam p A t`, the conclusion needs the equality of `A` substituted by both
substitutions, which the rules state nowhere: the induction proves a stronger statement, `EqLast`,
where each judgment, along with the equality of its substitutions, substitutes the last type of its
context by both, which a judgment in `Γ ∙ A`, such as the one of `t`, gives for `A`.
-/

/-- The last type of the context `Γ`, substituted by two equal substitutions, gives equal types. -/
private def EqLast {k n : Nat} (Γ : Con k n) : Prop :=
  match n, Γ with
  | _, .empty => True
  | _, .snoc Γ A => ∀ {m} {Δ : Con k m} {σ τ}, Δ ⊢ˢ σ : Γ → Δ ⊢ˢ σ ≡ τ : Γ → ⊢ Δ →
      ∃ l, Δ ⊢ A.subst σ ≡ A.subst τ : univ l

mutual

private theorem WfCon.eqLast {Γ : Con k n} : ⊢ Γ → EqLast Γ
  | .empty => trivial
  | .snoc (.univ h) => fun hσ hστ hΔ => ⟨_, h.substEqStrong.2 hσ hστ hΔ⟩

private theorem HasType.substEqStrong {Γ : Con k n} {t A : Term k n} : Γ ⊢ t : A →
    EqLast Γ ∧ ∀ {m} {Δ : Con k m} {σ τ}, Δ ⊢ˢ σ : Γ → Δ ⊢ˢ σ ≡ τ : Γ → ⊢ Δ →
      Δ ⊢ t.subst σ ≡ t.subst τ : A.subst σ
  | .var h => ⟨h.eqLast, fun _ hστ _ => hστ _⟩
  | .conv h hA => ⟨h.substEqStrong.1, fun hσ hστ hΔ =>
      .conv (h.substEqStrong.2 hσ hστ hΔ) (hA.subst hσ hΔ)⟩
  | .univ h => ⟨h.eqLast, fun _ _ hΔ => .refl (.univ hΔ)⟩
  | .pi hA hB => ⟨hA.substEqStrong.1, fun hσ hστ hΔ =>
      have hΔ' := WfCon.snoc (.univ (hA.subst hσ hΔ))
      .pi (hA.substEqStrong.2 hσ hστ hΔ) (hB.substEqStrong.2 (hσ.lift hΔ') (hστ.lift hΔ') hΔ')⟩
  | .lam (.univ hPi) ht => ⟨hPi.substEqStrong.1, fun hσ hστ hΔ =>
      have hPi' := (IsType.univ hPi).subst hσ hΔ
      have ⟨⟨_, hA'⟩, _⟩ := hPi'.inv_pi
      have hΔ' := WfCon.snoc (.univ hA')
      have ⟨_, hA⟩ := ht.substEqStrong.1 hσ hστ hΔ
      .lam hPi' hA (ht.substEqStrong.2 (hσ.lift hΔ') (hστ.lift hΔ') hΔ')⟩
  | .app ht ha => ⟨ht.substEqStrong.1, fun hσ hστ hΔ => by
      rw [subst_instantiate]
      exact .app (ht.substEqStrong.2 hσ hστ hΔ) (ha.substEqStrong.2 hσ hστ hΔ)⟩

end

-- ADE: `subst-⊢∷→⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- A term whose variables are replaced by two equal substitutions gives two equal terms. -/
theorem HasType.substEq (h : Γ ⊢ t : A) (hσ : Δ ⊢ˢ σ : Γ) (hστ : Δ ⊢ˢ σ ≡ τ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.subst σ ≡ t.subst τ : A.subst σ :=
  h.substEqStrong.2 hσ hστ hΔ

/-- A term whose bound variable is replaced by two equal terms of its type gives two equal terms. -/
theorem HasType.instantiateEq (h : Γ ∙ A ⊢ t : B) (ha₁ : Γ ⊢ a₁ : A) (ha : Γ ⊢ a₁ ≡ a₂ : A) :
    Γ ⊢ t.instantiate a₁ ≡ t.instantiate a₂ : B.instantiate a₁ :=
  h.substEq (.instantiate ha₁) (.instantiate ha) ha₁.wfCon

end Sic.Core
