module

public import Sic.Core.Typing

/-!
# Typed Substitution

The judgments of `Sic.Core.Typing` moved to another context, as in the formalization of ADE: a
judgment holds in every well-formed context that contains its own, by weakening, and with its
variables replaced by terms of their types, by substitution, which instantiates a binder in
particular.
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

/--
`ρ ∷ Δ ⊇ Γ`: the weakening `ρ` moves the context `Γ` to `Δ`, which contains its declarations in the
same order.
-/
inductive WkCon {k : Nat} : {m n : Nat} → Wk m n → Con k m → Con k n → Prop where
  /-- The weakening `id` keeps the context. -/
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
  | _, .snoc Γ A => ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → ∃ l, Δ ⊢ A.wk ρ : univ l

mutual

private theorem WfCon.wkLast {Γ : Con k n} : ⊢ Γ → WkLast Γ
  | .empty => trivial
  | .snoc h => fun hρ hΔ => ⟨_, (h.wkStrong).2 hρ hΔ⟩

private theorem HasType.wkStrong {Γ : Con k n} {t A : Term k n} : Γ ⊢ t : A →
    WkLast Γ ∧ ∀ {m} {Δ : Con k m} {ρ}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ t.wk ρ : A.wk ρ
  | .var h => ⟨h.wkLast, fun hρ hΔ => by rw [← hρ.get_var]; exact .var hΔ⟩
  | .conv h hA => ⟨h.wkStrong.1, fun hρ hΔ => .conv (h.wkStrong.2 hρ hΔ) (hA.wkStrong.2 hρ hΔ)⟩
  | .univ h => ⟨h.wkLast, fun _ hΔ => .univ hΔ⟩
  | .pi hA hB => ⟨hA.wkStrong.1, fun hρ hΔ =>
      have hA' := hA.wkStrong.2 hρ hΔ
      .pi hA' (hB.wkStrong.2 hρ.lift (.snoc hA'))⟩
  | .lam hPi ht => ⟨hPi.wkStrong.1, fun hρ hΔ =>
      have ⟨_, hA⟩ := ht.wkStrong.1 hρ hΔ
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
      have ⟨_, hA₁⟩ := hB.wkStrong.1 hρ hΔ
      .pi (hA.wkStrong.2 hρ hΔ) (hB.wkStrong.2 hρ.lift (.snoc hA₁))⟩
  | .lam hPi hA ht => ⟨hPi.wkStrong.1, fun hρ hΔ =>
      have ⟨_, hA₁⟩ := ht.wkStrong.1 hρ hΔ
      .lam (hPi.wkStrong.2 hρ hΔ) (hA.wkStrong.2 hρ hΔ) (ht.wkStrong.2 hρ.lift (.snoc hA₁))⟩
  | .app ht ha => ⟨ht.wkStrong.1, fun hρ hΔ => by
      rw [wk_instantiate]
      exact .app (ht.wkStrong.2 hρ hΔ) (ha.wkStrong.2 hρ hΔ)⟩
  | .beta hPi ht ha => ⟨hPi.wkStrong.1, fun hρ hΔ => by
      have ⟨_, hA⟩ := ht.wkStrong.1 hρ hΔ
      rw [wk_instantiate, wk_instantiate]
      exact .beta (hPi.wkStrong.2 hρ hΔ) (ht.wkStrong.2 hρ.lift (.snoc hA)) (ha.wkStrong.2 hρ hΔ)⟩
  | .eta h => ⟨h.wkStrong.1, fun hρ hΔ => by
      have := TermEq.eta (h.wkStrong.2 hρ hΔ)
      simp only [wk, wk_lift_wk1] at this ⊢
      exact this⟩

end

/-- A term keeps its type in every well-formed context that contains its own. -/
theorem HasType.wk (h : Γ ⊢ t : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ t.wk ρ : A.wk ρ :=
  h.wkStrong.2 hρ hΔ

/-- Two terms stay equal in every well-formed context that contains their own. -/
theorem TermEq.wk (h : Γ ⊢ t ≡ u : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.wk ρ ≡ u.wk ρ : A.wk ρ :=
  h.wkStrong.2 hρ hΔ

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
  | _, .snoc Γ A => ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → ∃ l, Δ ⊢ A.subst σ : univ l

mutual

private theorem WfCon.substLast {Γ : Con k n} : ⊢ Γ → SubstLast Γ
  | .empty => trivial
  | .snoc h => fun hσ hΔ => ⟨_, h.substStrong.2 hσ hΔ⟩

private theorem HasType.substStrong {Γ : Con k n} {t A : Term k n} : Γ ⊢ t : A →
    SubstLast Γ ∧ ∀ {m} {Δ : Con k m} {σ}, Δ ⊢ˢ σ : Γ → ⊢ Δ → Δ ⊢ t.subst σ : A.subst σ
  | .var h => ⟨h.substLast, fun hσ _ => hσ _⟩
  | .conv h hA =>
    ⟨h.substStrong.1, fun hσ hΔ => .conv (h.substStrong.2 hσ hΔ) (hA.substStrong.2 hσ hΔ)⟩
  | .univ h => ⟨h.substLast, fun _ hΔ => .univ hΔ⟩
  | .pi hA hB => ⟨hA.substStrong.1, fun hσ hΔ =>
      have hΔ' := WfCon.snoc (hA.substStrong.2 hσ hΔ)
      .pi (hA.substStrong.2 hσ hΔ) (hB.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .lam hPi ht => ⟨hPi.substStrong.1, fun hσ hΔ =>
      have ⟨_, hA⟩ := ht.substStrong.1 hσ hΔ
      have hΔ' := WfCon.snoc hA
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
      have ⟨_, hA₁⟩ := hB.substStrong.1 hσ hΔ
      have hΔ' := WfCon.snoc hA₁
      .pi (hA.substStrong.2 hσ hΔ) (hB.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .lam hPi hA ht => ⟨hPi.substStrong.1, fun hσ hΔ =>
      have ⟨_, hA₁⟩ := ht.substStrong.1 hσ hΔ
      have hΔ' := WfCon.snoc hA₁
      .lam (hPi.substStrong.2 hσ hΔ) (hA.substStrong.2 hσ hΔ) (ht.substStrong.2 (hσ.lift hΔ') hΔ')⟩
  | .app ht ha => ⟨ht.substStrong.1, fun hσ hΔ => by
      rw [subst_instantiate]
      exact .app (ht.substStrong.2 hσ hΔ) (ha.substStrong.2 hσ hΔ)⟩
  | .beta hPi ht ha => ⟨hPi.substStrong.1, fun hσ hΔ => by
      have ⟨_, hA⟩ := ht.substStrong.1 hσ hΔ
      have hΔ' := WfCon.snoc hA
      rw [subst_instantiate, subst_instantiate]
      exact .beta (hPi.substStrong.2 hσ hΔ) (ht.substStrong.2 (hσ.lift hΔ') hΔ')
        (ha.substStrong.2 hσ hΔ)⟩
  | .eta h => ⟨h.substStrong.1, fun hσ hΔ => by
      have := TermEq.eta (h.substStrong.2 hσ hΔ)
      simp only [Term.subst, subst_lift_wk1] at this ⊢
      exact this⟩

end

/-- A term whose variables are replaced by terms of their types has the substituted type. -/
theorem HasType.subst (h : Γ ⊢ t : A) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.subst σ : A.subst σ :=
  h.substStrong.2 hσ hΔ

/-- Two equal terms whose variables are replaced by terms of their types stay equal. -/
theorem TermEq.subst (h : Γ ⊢ t ≡ u : A) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.subst σ ≡ u.subst σ : A.subst σ :=
  h.substStrong.2 hσ hΔ

/-- A term whose bound variable is replaced by a term of its type has the instantiated type. -/
theorem HasType.instantiate (ht : Γ ∙ A ⊢ t : B) (ha : Γ ⊢ a : A) :
    Γ ⊢ t.instantiate a : B.instantiate a :=
  ht.subst (.instantiate ha) ha.wfCon

end Sic.Core
