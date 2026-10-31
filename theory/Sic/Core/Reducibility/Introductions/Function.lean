module

public import Sic.Core.Reducibility.Validity
import Sic.Core.Reducibility.Canonical
import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Reduction
import Sic.Core.WellFormed

/-!
# Functions

The abstractions and the applications are valid, and so are the equalities `(β)` and `(η)`, so that
the fundamental lemma covers the rules `(λ)`, `(∘)`, `(β)` and `(η)` of `Sic.Core.Typing`, and the
congruences of abstraction and of application.

Two terms of a type of functions are reducibly equal when they reduce to weak head normal forms
whose applications to reducibly equal arguments are reducibly equal: the equality of these normal
forms by the equality relation, which the interpretation also asks for, follows from `(η)`, applied
to the variable of a new declaration of the domain.

## Correspondence with the Formalizations of ADE and of Pujet

The abstractions of ADE and of Pujet do not carry the type of their argument, so that their
congruence of abstraction relates two bodies in the same context.
Here, the abstractions of two equal types of arguments are equal, which needs the equality of these
types as terms of a universe, to type the second abstraction: `ValidTermEq.lam` takes it from
`Sic.Core.Typing`, as ADE's `lam-congᵛ` takes the equality of the bodies, since the rule `(λ)`
gives no valid equality of the type of the argument as a term of a universe.
`ValidTermEq.eta` validates `(η)` as `Sic.Core.Typing` states it, where ADE's `η-eqᵛ` validates
their extensionality.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

/--
`(β)` with an abstraction whose type of argument is equal to the domain of the type of functions, as
a term of a universe, to which the body and the argument are converted.
-/
private theorem TermRed.beta_conv (hPi : Γ ⊢ pi p q A₁ B) (hA : Γ ⊢ A₁ ≡ A₂ : univ L)
    (ht : Γ ∙ A₁ ⊢ t : B) (ha : Γ ⊢ a : A₁) :
    Γ ⊢ app p (lam p A₂ t) a ⇒ t.instantiate a : B.instantiate a := by
  have ⟨_, _, hB⟩ := hPi.inv_pi
  have ⟨_, hA₂, _⟩ := hA.wf
  have hA' : Γ ⊢ A₁ ≡ A₂ := .univ hA
  have hA₂' : Γ ⊢ A₂ := .univ hA₂
  exact .beta (q := q) (.univ (.pi hA₂ (hB.conv_last hA' hA₂'))) (ht.conv_last hA' hA₂')
    (.conv ha hA')

variable [EqualityRelation]

/-!
The statements of the theorems on `ValidTermEq` write the types of functions, the abstractions and
the applications with the namespace `Term`, since `lam` and `app` name theorems in the namespace that
Lean opens for them.
-/

/-- A type reducibly equal to another is a type. -/
private theorem ReducibleTypeEq.escape : (Γ ⊩⟨l⟩ A ≡ B) → Γ ⊢ A
  | ⟨_, _, hA, _, _⟩ => hA.escape

/-- Two reducibly equal types are equal. -/
private theorem ReducibleTypeEq.escape_eqType : (Γ ⊩⟨l⟩ A ≡ B) → Γ ⊢ A ≡ B
  | ⟨_, _, hA, _, hAB⟩ => hA.escape_eqType hAB

/-- Two reducibly equal terms are equal by the equality relation. -/
private theorem ReducibleTermEq.escape_eq : (Γ ⊩⟨l⟩ t ≡ u : A) → Γ ⊢ t ≅ u : A
  | ⟨_, hA, htu⟩ => hA.escape_eq htu

/-- Two reducibly equal terms are equal. -/
private theorem ReducibleTermEq.escape_eqTerm : (Γ ⊩⟨l⟩ t ≡ u : A) → Γ ⊢ t ≡ u : A
  | ⟨_, hA, htu⟩ => hA.escape_eqTerm htu

/-- Two terms that reduce to reducibly equal terms are reducibly equal. -/
private theorem ReducibleTermEq.expand : (Γ ⊩⟨l⟩ t' ≡ u' : A) → (Γ ⊢ t ⇒* t' : A) →
    (Γ ⊢ u ⇒* u' : A) → Γ ⊩⟨l⟩ t ≡ u : A
  | ⟨_, hA, htu⟩, ht, hu => ⟨_, hA, hA.expand_eqTerm ht hu htu⟩

/--
Two reducibly equal terms of a type of functions reduce to weak head normal forms whose applications
to reducibly equal arguments, in every well-formed context that contains their own, are reducibly
equal, as in the first direction of ADE's `⊩≡∷Π⇔`.
-/
private theorem ReducibleTermEq.inv_pi {F : Term k n} {G : Term k (n + 1)}
    (h : Δ ⊩⟨l⟩ t₁ ≡ t₂ : pi p q F G) :
    ∃ f₁ f₂, (Δ ⊢ t₁ ↘ f₁ : pi p q F G) ∧ (Δ ⊢ t₂ ↘ f₂ : pi p q F G) ∧
      ∀ {m} {ρ : Wk m n} {Ε : Con k m} {a b}, ρ ∷ Ε ⊇ Δ → ⊢ Ε → (Ε ⊩⟨l⟩ a ≡ b : F.wk ρ) →
        Ε ⊩⟨l⟩ app p (f₁.wk ρ) a ≡ app p (f₂.wk ρ) b : (G.wk ρ.lift).instantiate a := by
  have ⟨_, hPi, htu⟩ := h
  have hPi' := hPi.escape
  rw [LogicalRelation.unfold] at hPi
  cases hPi with
  | univ _ hU => nomatch TypeRedWhnf.det ⟨hU, .univ⟩ ⟨.refl hPi', .pi⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hPi', .pi⟩; nomatch hN'
  | pi hA _ PF PG hF hG =>
    cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hPi', .pi⟩
    have ⟨f₁, f₂, hf₁, hf₂, _, happ⟩ := htu
    refine ⟨f₁, f₂, hf₁, hf₂, fun {_ ρ Ε a b} hρ hΕ hab => ?_⟩
    have hPF : Ε ⊩⟨l⟩ F.wk ρ ▸ PF ρ Ε := LogicalRelation.unfold ▸ hF hρ hΕ
    have hPFab : (PF ρ Ε).eqTerm a b := by rw [hPF.eq_canonical]; exact hab
    have hPFa : (PF ρ Ε).eqTerm a a := by rw [hPF.eq_canonical]; exact hab.trans hab.symm
    have hPFb : (PF ρ Ε).eqTerm b b := by rw [hPF.eq_canonical]; exact hab.symm.trans hab
    exact ⟨_, LogicalRelation.unfold ▸ hG hρ hΕ hPFa, happ hρ hΕ hPFa hPFb hPFab⟩

/--
Two terms of a reducible type of functions are reducibly equal when they reduce to weak head normal
forms whose applications to reducibly equal arguments, in every well-formed context that contains
their own, are reducibly equal, as in the second direction of ADE's `⊩≡∷Π⇔`.

The normal forms are equal by the equality relation, as the interpretation asks: by `(η)`, since
their applications to the variable of a new declaration of the domain, which is a reducible
argument, are reducibly equal.
-/
private theorem reducibleTermEq_pi {F : Term k n} {G : Term k (n + 1)}
    (hPi : Δ ⊩⟨l⟩ pi p q F G ≡ pi p q F G) (h₁ : Δ ⊢ t₁ ↘ f₁ : pi p q F G)
    (h₂ : Δ ⊢ t₂ ↘ f₂ : pi p q F G)
    (happ : ∀ {m} {ρ : Wk m n} {Ε : Con k m} {a b}, ρ ∷ Ε ⊇ Δ → ⊢ Ε →
      (Ε ⊩⟨l⟩ a ≡ b : F.wk ρ) →
      Ε ⊩⟨l⟩ app p (f₁.wk ρ) a ≡ app p (f₂.wk ρ) b : (G.wk ρ.lift).instantiate a) :
    Δ ⊩⟨l⟩ t₁ ≡ t₂ : pi p q F G := by
  have hΔ := h₁.1.termEq.wfCon
  have ⟨_, _, hF, _⟩ := hPi.inv_pi.1 .id hΔ
  rw [wk_id] at hF
  have hΔF : ⊢ Δ ∙ F := .snoc hF.escape
  have hx := happ (.step .id) hΔF (ReducibleTermEq.var hF hΔF)
  rw [instantiate_wk_lift_step] at hx
  have hfg := EqualityRelation.eta h₁.1.termEq.wf.2.1 h₂.1.termEq.wf.2.1 h₁.2 h₂.2 hx.escape_eq
  have ⟨_, _, hP, _⟩ := hPi
  refine ⟨_, hP, ?_⟩
  have hP' := hP.escape
  rw [LogicalRelation.unfold] at hP
  cases hP with
  | univ _ hU => nomatch TypeRedWhnf.det ⟨hU, .univ⟩ ⟨.refl hP', .pi⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hP', .pi⟩; nomatch hN'
  | pi hA _ PF PG hF' hG =>
    cases TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hP', .pi⟩
    refine ⟨f₁, f₂, h₁, h₂, hfg, fun {_ ρ Ε a b} hρ hΕ ha _ hab => ?_⟩
    have hPF : Ε ⊩⟨l⟩ F.wk ρ ▸ PF ρ Ε := LogicalRelation.unfold ▸ hF' hρ hΕ
    have hPG : Ε ⊩⟨l⟩ (G.wk ρ.lift).instantiate a ▸ PG ρ Ε a :=
      LogicalRelation.unfold ▸ hG hρ hΕ ha
    rw [hPF.eq_canonical] at hab
    rw [hPG.eq_canonical]
    exact happ hρ hΕ hab

/--
The codomain of a valid type of functions, instantiated at a valid argument, is valid.

Under two reducibly equal substitutions, the substituted argument is reducibly equal to itself,
substituted by the other, at the domain substituted by the first, at which the codomains of the
substituted types of functions are reducibly equal.
-/
private theorem validTypeEq_instantiate (hPi : Γ ⊩ᵛ⟨l⟩ pi p q A B ≡ pi p q A B)
    (ha : Γ ⊩ᵛ⟨l'⟩ a ≡ a : A) : Γ ⊩ᵛ⟨l⟩ B.instantiate a ≡ B.instantiate a := by
  rw [ValidTypeEq.unfold] at hPi ⊢
  refine ⟨hPi.1, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  have hΔ := hσ.wfCon
  have hA := (hPi.2 hσ.left).inv_pi.1 .id hΔ
  rw [wk_id] at hA
  have h := (hPi.2 hσ).inv_pi.2 .id hΔ (by rw [wk_id]; exact (ha.2 hσ).conv hA)
  rw [wk_lift_id, wk_lift_id] at h
  rw [subst_instantiate, subst_instantiate]
  exact h

-- ADE: `lamᵛ` and `lam-congᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`.
-- Pujet: `lamᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`.
/--
Two abstractions are validly equal at a valid type of functions when their types of arguments are
equal terms of a universe and their bodies are validly equal.

Under two reducibly equal substitutions, the substituted abstractions are their own weak head normal
forms, and their applications to reducibly equal arguments reduce, by `(β)`, to their bodies
substituted by the substitutions extended by the arguments, which are reducibly equal.
-/
theorem ValidTermEq.lam (hPi : Γ ⊩ᵛ⟨l⟩ Term.pi p q A₁ B ≡ Term.pi p q A₁ B)
    (hA : Γ ⊢ A₁ ≡ A₂ : Term.univ L) (ht : Γ ∙ A₁ ⊩ᵛ⟨l'⟩ t₁ ≡ t₂ : B) :
    Γ ⊩ᵛ⟨l⟩ Term.lam p A₁ t₁ ≡ Term.lam p A₂ t₂ : Term.pi p q A₁ B := by
  refine ⟨hPi, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  have hB := ht.1
  rw [ValidTypeEq.unfold] at hPi hB
  have hΓA := hB.1
  rw [ValidCon.unfold_snoc] at hΓA
  have ⟨_, hA₁⟩ := hΓA
  have hA₁' := hA₁
  rw [ValidTypeEq.unfold] at hA₁'
  have hΔ := hσ.wfCon
  have hPiσ := hPi.2 hσ.left
  have hAσ : Δ ⊢ A₁.subst σ₁ ≡ A₂.subst σ₂ : Term.univ L :=
    .trans (hA.subst hσ.substWf hΔ) (hA.wf.2.1.substEq hσ.substWf hσ.substEq hΔ)
  have hlam :=
    (TermEq.lam (p := p) hPiσ.escape hAσ (ht.2 (hσ.lift hA₁)).escape_eqTerm).wf
  refine reducibleTermEq_pi hPiσ ⟨.refl hlam.1, .lam⟩ ⟨.refl hlam.2.1, .lam⟩
    fun {_ ρ Ε a b} hρ hΕ hab => ?_
  have hBₐ := hPiσ.inv_pi.2 hρ hΕ (hab.trans hab.symm)
  have hτ := hσ.wk hρ hΕ
  show Ε ⊩⟨l⟩ Term.app p (Term.lam p ((A₁.subst σ₁).wk ρ) ((t₁.subst σ₁.lift).wk ρ.lift)) a ≡
    Term.app p (Term.lam p ((A₂.subst σ₂).wk ρ) ((t₂.subst σ₂.lift).wk ρ.lift)) b : _
  rw [wk_lift_subst_lift, wk_lift_subst_lift, wk_lift_subst_lift, wk_subst, wk_subst]
  rw [wk_subst] at hab
  rw [wk_lift_subst_lift] at hBₐ
  have hab' := hab.conv (hA₁'.2 hτ.left)
  have hτab := hτ.cons hA₁ hab'
  have h := ht.2 hτab
  have hBab := (hB.2 hτab).escape_eqType
  rw [← subst_lift_instantiate, ← subst_lift_instantiate, ← subst_lift_instantiate] at h
  rw [← subst_lift_instantiate, ← subst_lift_instantiate] at hBab
  have h := h.conv hBₐ
  have ⟨_, hb, _⟩ := hab.escape_eqTerm.wf
  have hb := hb.conv (hA₁'.2 hτ).escape_eqType
  have hβ₁ : Ε ⊢ _ ⇒ _ : _ :=
    .beta (hPi.2 hτ.left).escape (ht.2 (hτ.left.lift hA₁)).escape_eqTerm.wf.1
      hab.escape_eqTerm.wf.1
  have hβ₂ :=
    TermRed.beta_conv (hPi.2 hτ.symm.left).escape (hA.subst hτ.symm.substWf hΕ)
      (ht.2 (hτ.symm.left.lift hA₁)).escape_eqTerm.wf.2.1 hb
  exact h.expand (.step hβ₁ (.refl h.escape_eqTerm.wf.1))
    (.step (.conv hβ₂ hBab.symm) (.refl h.escape_eqTerm.wf.2.1))

-- ADE: `∘ᵛ` and `∘-congᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`.
-- Pujet: `appᵛ` and `app-congᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/Application.agda`.
/--
Two applications are validly equal when their functions are validly equal at a type of functions
and their arguments are validly equal at its domain.

Under two reducibly equal substitutions, the substituted functions reduce to weak head normal forms
whose applications to the substituted arguments are reducibly equal, so that the applications, which
reduce to them, are.
-/
theorem ValidTermEq.app (ht : Γ ⊩ᵛ⟨l⟩ t₁ ≡ t₂ : Term.pi p q A B) (ha : Γ ⊩ᵛ⟨l'⟩ a₁ ≡ a₂ : A) :
    Γ ⊩ᵛ⟨l⟩ Term.app p t₁ a₁ ≡ Term.app p t₂ a₂ : B.instantiate a₁ := by
  have hPi := ht.1
  refine ⟨validTypeEq_instantiate hPi (ha.trans ha.symm), fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  rw [ValidTypeEq.unfold] at hPi
  have hΔ := hσ.wfCon
  have hPi₁ := (hPi.2 hσ.left).inv_pi
  have hA := hPi₁.1 .id hΔ
  rw [wk_id] at hA
  have ha' : Δ ⊩⟨l⟩ a₁.subst σ₁ ≡ a₂.subst σ₂ : A.subst σ₁ := (ha.2 hσ).conv hA
  have ⟨f₁, f₂, hf₁, hf₂, happ⟩ := (ht.2 hσ).inv_pi
  have h := happ .id hΔ (by rw [wk_id]; exact ha')
  have hB := hPi₁.2 .id hΔ (by rw [wk_id]; exact ha')
  rw [wk_id, wk_id, wk_lift_id] at h
  rw [wk_lift_id] at hB
  have ⟨ha₁, ha₂, _⟩ := ha'.escape_eqTerm.wf
  rw [subst_instantiate]
  exact h.expand (hf₁.1.app ha₁) ((hf₂.1.app ha₂).conv hB.escape_eqType.symm)

-- ADE: `β-redᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`.
-- Pujet: none, since `fundamentalTermEq`, in `Definition/LogicalRelation/Fundamental.agda`, proves
-- it in place.
/--
`(β)` is valid: the application of an abstraction to a valid argument is validly equal to its body
instantiated at the argument.

Under two reducibly equal substitutions, the substituted application reduces, by `(β)`, to the body
substituted by the first substitution extended by the first argument, which is reducibly equal to
the body substituted by the second, extended by the second.
-/
theorem ValidTermEq.beta (hPi : Γ ⊩ᵛ⟨l⟩ Term.pi p q A B ≡ Term.pi p q A B)
    (ht : Γ ∙ A ⊩ᵛ⟨l'⟩ t ≡ t : B) (ha : Γ ⊩ᵛ⟨l''⟩ a ≡ a : A) :
    Γ ⊩ᵛ⟨l⟩ Term.app p (Term.lam p A t) a ≡ t.instantiate a : B.instantiate a := by
  have hBₐ := validTypeEq_instantiate hPi ha
  refine ⟨hBₐ, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  have hB := ht.1
  rw [ValidTypeEq.unfold] at hPi hB hBₐ
  have hΓA := hB.1
  rw [ValidCon.unfold_snoc] at hΓA
  have ⟨_, hA⟩ := hΓA
  have hA' := hA
  rw [ValidTypeEq.unfold] at hA'
  have ha' := (ha.2 hσ).conv (hA'.2 hσ.left)
  have h := ht.2 (hσ.cons hA ha')
  rw [← subst_lift_instantiate, ← subst_lift_instantiate, ← subst_lift_instantiate] at h
  have hBₐ := hBₐ.2 hσ.left
  rw [subst_instantiate] at hBₐ
  have h := h.conv hBₐ
  have hβ : Δ ⊢ _ ⇒ _ : _ :=
    .beta (hPi.2 hσ.left).escape (ht.2 (hσ.left.lift hA)).escape_eqTerm.wf.1
      ha'.escape_eqTerm.wf.1
  rw [subst_instantiate, subst_instantiate]
  exact h.expand (.step hβ (.refl h.escape_eqTerm.wf.1)) (.refl h.escape_eqTerm.wf.2.1)

-- ADE: `η-eqᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`.
-- Pujet: `η-eqᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`.
/--
`(η)` is valid: a valid function is validly equal to the abstraction of its application to the
variable it binds.

Under two reducibly equal substitutions, the substituted abstraction is its own weak head normal
form, typed by `(η)`, and its application to an argument reduces, by `(β)`, to the application of
the function substituted by the second substitution, which reduces as the function does.
-/
theorem ValidTermEq.eta (ht : Γ ⊩ᵛ⟨l⟩ t ≡ t : Term.pi p q A B) :
    Γ ⊩ᵛ⟨l⟩ t ≡ Term.lam p A (Term.app p t.wk1 (Term.var 0)) : Term.pi p q A B := by
  have hPi := ht.1
  refine ⟨hPi, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  rw [ValidTypeEq.unfold] at hPi
  have hPi₁₂ := hPi.2 hσ
  have hPi₁ := hPi.2 hσ.left
  have htσ := ht.2 hσ
  have ⟨f₁, f₂, hf₁, hf₂, happ⟩ := htσ.inv_pi
  have ht₂ := htσ.escape_eqTerm.wf.2.1.conv hPi₁₂.escape_eqType
  show Δ ⊩⟨l⟩ _ ≡ Term.lam p (A.subst σ₂) (Term.app p (t.wk1.subst σ₂.lift) (Term.var 0)) : _
  rw [subst_lift_wk1]
  have hlam := (TermEq.eta ht₂).wf.2.1.conv hPi₁₂.escape_eqType.symm
  refine reducibleTermEq_pi hPi₁ hf₁ ⟨.refl hlam, .lam⟩ fun {_ ρ Ε a b} hρ hΕ hab => ?_
  have h := happ hρ hΕ hab
  -- The function substituted by the second substitution, moved to `Ε`, and its type.
  have hs := ht₂.wk hρ hΕ
  have ⟨⟨_, hAρ⟩, _⟩ := hs.wfType.inv_pi
  have hΕA := WfCon.snoc (.univ hAρ)
  have hbody := HasType.app (hs.wk (.step .id) hΕA) (.var (x := 0) hΕA)
  rw [instantiate_wk_lift_step] at hbody
  have hb := hab.escape_eqTerm.wf.2.1
  have hβ := TermRed.beta (p := p) hs.wfType hbody
    (hb.conv (hPi₁₂.inv_pi.1 hρ hΕ).escape_eqType)
  have e : (Term.app p ((t.subst σ₂).wk ρ).wk1 (Term.var 0)).instantiate b =
      Term.app p ((t.subst σ₂).wk ρ) b := by
    show Term.app p (((t.subst σ₂).wk ρ).wk1.instantiate b) b = _
    rw [instantiate_wk1]
  rw [e] at hβ
  have hred := (hf₂.1.wk hρ hΕ).app hb
  simp only [Term.wk]
  rw [wk_lift_wk1]
  exact h.expand (.refl h.escape_eqTerm.wf.1)
    (.step (.conv hβ (hPi₁₂.inv_pi.2 hρ hΕ hab).escape_eqType.symm)
      (hred.conv (hPi₁.inv_pi.2 hρ hΕ hab).escape_eqType.symm))

end Sic.Core.Reducibility
