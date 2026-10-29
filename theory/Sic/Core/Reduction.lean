module

public import Sic.Core.Typing
import Sic.Core.TypedSubstitution

/-!
# Reduction

The weak head reduction of the terms of `Sic.Core.Syntax`, which the decision procedure for equality
of RFC 24 applies to both terms before comparing their heads, as in the formalization of ADE.
RFC 24 defines equality only, so that reduction is a device of the proofs: each step is an equality
of `Sic.Core.Typing`, which ties it to the RFC.
A step only reduces the head of a term: the function of an application, until it is an abstraction
applied to its argument, which `(β)` reduces.
A reduction is typed, as in ADE, so that it keeps the type its terms have.
-/

@[expose] public section

namespace Sic.Core

open Term

/--
A neutral term: a variable, applied to any number of arguments, so that no reduction of its head
can apply until the variable is substituted.
-/
inductive Neutral : Term k n → Prop where
  /-- A variable is neutral. -/
  | var : Neutral (var x)
  /-- The application of a neutral term is neutral. -/
  | app : Neutral t → Neutral (app p t a)

/--
A weak head normal form: a term whose head does not reduce, either a type, an abstraction or a
neutral term.
-/
inductive Whnf : Term k n → Prop where
  /-- A universe is a weak head normal form. -/
  | univ : Whnf (univ l)
  /-- A type of functions is a weak head normal form. -/
  | pi : Whnf (pi p q A B)
  /-- An abstraction is a weak head normal form, whatever its body. -/
  | lam : Whnf (lam p A t)
  /-- A neutral term is a weak head normal form. -/
  | ne : Neutral t → Whnf t

set_option hygiene false in
/-- `Γ ⊢ t ⇒ u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in one step. -/
notation:40 Γ:41 " ⊢ " t:41 " ⇒ " u:41 " : " A:41 => TermRed Γ t u A

/-- `Γ ⊢ t ⇒ u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in one step. -/
inductive TermRed {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop where
  /-- A reduction has any type equal to its own, as `(conv)`. -/
  | conv : Γ ⊢ t ⇒ u : A → Γ ⊢ A ≡ B : univ l → Γ ⊢ t ⇒ u : B
  /-- An application reduces its function, with the premises of `(∘)`. -/
  | app : Γ ⊢ t₁ ⇒ t₂ : pi p q A B → Γ ⊢ a : A →
      Γ ⊢ app p t₁ a ⇒ app p t₂ a : B.instantiate a
  /-- `(β)`: applying an abstraction reduces to its body with the argument substituted. -/
  | beta : Γ ⊢ pi p q A B : univ l → Γ ∙ A ⊢ t : B → Γ ⊢ a : A →
      Γ ⊢ app p (lam p A t) a ⇒ t.instantiate a : B.instantiate a

set_option hygiene false in
/--
`Γ ⊢ t ⇒* u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in any number of steps.
-/
notation:40 Γ:41 " ⊢ " t:41 " ⇒* " u:41 " : " A:41 => TermRedStar Γ t u A

/--
`Γ ⊢ t ⇒* u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in any number of steps.
-/
inductive TermRedStar {k : Nat} :
    {n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop where
  /-- A term of a type reduces to itself in no step. -/
  | refl : Γ ⊢ t : A → Γ ⊢ t ⇒* t : A
  /-- A step followed by any number of steps. -/
  | step : Γ ⊢ t₁ ⇒ t₂ : A → Γ ⊢ t₂ ⇒* t₃ : A → Γ ⊢ t₁ ⇒* t₃ : A

/--
`Γ ⊢ t ↘ u : A`: in the context `Γ`, the term `t` of type `A` reduces to the weak head normal form
`u`.
-/
def TermRedWhnf (Γ : Con k n) (t u A : Term k n) : Prop :=
  (Γ ⊢ t ⇒* u : A) ∧ Whnf u

@[inherit_doc] notation:40 Γ:41 " ⊢ " t:41 " ↘ " u:41 " : " A:41 => TermRedWhnf Γ t u A

/-! The properties of reduction that the decision procedure for equality uses. -/

/-- A reduction is an equality. -/
theorem TermRed.termEq : Γ ⊢ t ⇒ u : A → Γ ⊢ t ≡ u : A
  | .conv h hA => .conv h.termEq hA
  | .app h ha => .app h.termEq (.refl ha)
  | .beta hPi ht ha => .beta hPi ht ha

/-- Any number of reductions is an equality. -/
theorem TermRedStar.termEq : Γ ⊢ t ⇒* u : A → Γ ⊢ t ≡ u : A
  | .refl h => .refl h
  | .step h hs => .trans h.termEq hs.termEq

/-- A term that reduces has the type of its reduction. -/
theorem TermRed.hasType : Γ ⊢ t ⇒ u : A → Γ ⊢ t : A
  | .conv h hA => .conv h.hasType hA
  | .app h ha => .app h.hasType ha
  | .beta hPi ht ha => .app (.lam hPi ht) ha

/-- A term that reduces keeps its type: `(β)` instantiates the body of the abstraction at its type. -/
theorem TermRed.hasType_reduct : Γ ⊢ t ⇒ u : A → Γ ⊢ u : A
  | .conv h hA => .conv h.hasType_reduct hA
  | .app h ha => .app h.hasType_reduct ha
  | .beta _ ht ha => ht.instantiate ha

/-- A neutral term does not reduce: its head is a variable, which no rule reduces. -/
theorem Neutral.not_termRed : Neutral t → ¬ Γ ⊢ t ⇒ u : A
  | h, .conv hr _ => h.not_termRed hr
  | .app h, .app hr _ => h.not_termRed hr
  | .app h, .beta .. => nomatch h

/-- A weak head normal form does not reduce. -/
theorem Whnf.not_termRed : Whnf t → ¬ Γ ⊢ t ⇒ u : A
  | h, .conv hr _ => h.not_termRed hr
  | .ne h, hr => h.not_termRed hr

/-!
Reduction is deterministic.
A step is unique up to the conversions of its type, which each proof skips; an application then
reduces either its function or, when its function is an abstraction, by `(β)`, and both cannot
apply, since an abstraction does not reduce.
-/

/-- A term reduces in one step to the same term at any two of its types. -/
theorem TermRed.det (h₁ : Γ ⊢ t ⇒ u₁ : A₁) (h₂ : Γ ⊢ t ⇒ u₂ : A₂) : u₁ = u₂ := by
  induction h₁ generalizing u₂ A₂ with
  | conv _ _ ih => exact ih h₂
  | app h₁ _ ih =>
    generalize hs : Term.app _ _ _ = s at h₂
    induction h₂ with
    | conv _ _ ih₂ => exact ih₂ hs
    | app h₂ _ => cases hs; rw [ih h₂]
    | beta => cases hs; exact absurd h₁ Whnf.lam.not_termRed
  | beta =>
    generalize hs : Term.app _ _ _ = s at h₂
    induction h₂ with
    | conv _ _ ih₂ => exact ih₂ hs
    | app h₂ _ => cases hs; exact absurd h₂ Whnf.lam.not_termRed
    | beta => cases hs; rfl

/--
A term reduces to at most one weak head normal form, at any two of its types: both reductions take
the same steps, since each is unique, until the first one ends on a weak head normal form, where the
other has to end too, since a weak head normal form does not reduce.
-/
theorem TermRedWhnf.det : Γ ⊢ t ↘ u₁ : A₁ → Γ ⊢ t ↘ u₂ : A₂ → u₁ = u₂ := by
  rintro ⟨h₁, hw₁⟩ ⟨h₂, hw₂⟩
  induction h₁ generalizing u₂ A₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step h => exact absurd h hw₁.not_termRed
  | step h₁ _ ih =>
    cases h₂ with
    | refl => exact absurd h₁ hw₂.not_termRed
    | step h₂ hs₂ => exact ih hw₁ (h₁.det h₂ ▸ hs₂) hw₂

end Sic.Core
