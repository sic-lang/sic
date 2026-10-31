module

public import Sic.Core.TypedSubstitution

/-!
# Reduction

The weak head reduction of the terms of `Sic.Core.Syntax`, which the decision procedure for equality
of RFC 24 applies to both terms before comparing their heads, as in the formalization of ADE.
RFC 24 defines equality only, so that reduction is a device of the proofs: each step is an equality
of `Sic.Core.Typing`, which ties it to the RFC.
A step only reduces the head of a term: the function of an application, until it is an abstraction
applied to its argument, which `(β)` reduces.
A reduction is typed, as in ADE, so that it keeps the type its terms have.

## Correspondence with the Formalization of ADE

A type reduces as a term of a universe, as in ADE, so that the reduction of a type, as its equality,
does not depend on the universe of its terms.
Their `β-red` reduces an abstraction applied with another grade, which their premise `p ≡ p′`
equates, while `TermRed.beta` writes the same grade on both.
-/

@[expose] public section

namespace Sic.Core

open Term

-- ADE: `Neutral`, in `Definition/Untyped/Neutral.agda`.
/--
A neutral term: a variable, applied to any number of arguments, so that no reduction of its head
can apply until the variable is substituted.
-/
inductive Neutral : Term k n → Prop where
  /-- A variable is neutral. -/
  | var : Neutral (var x)
  /-- The application of a neutral term is neutral. -/
  | app : Neutral t → Neutral (app p t a)

-- ADE: `Whnf`, in `Definition/Untyped/Whnf.agda`.
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

-- ADE: `Type`, in `Definition/Untyped/Whnf.agda`.
/--
A type in weak head normal form: a universe, a type of functions, or a neutral term, which a variable
of a universe makes a type.
-/
inductive WhnfType : Term k n → Prop where
  /-- A universe is a type in weak head normal form. -/
  | univ : WhnfType (univ l)
  /-- A type of functions is a type in weak head normal form. -/
  | pi : WhnfType (pi p q A B)
  /-- A neutral term is a type in weak head normal form. -/
  | ne : Neutral t → WhnfType t

set_option hygiene false in
/-- `Γ ⊢ t ⇒ u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in one step. -/
notation:40 Γ:41 " ⊢ " t:41 " ⇒ " u:41 " : " A:41 => TermRed Γ t u A

/-- `Γ ⊢ t ⇒ u : A`: in the context `Γ`, the term `t` of type `A` reduces to `u` in one step. -/
inductive TermRed {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop where
  -- ADE: `conv` of `_⊢_⇒_∷_`, in `Definition/Typed.agda`.
  /-- A reduction has any type equal to its own, as `(conv)`. -/
  | conv : Γ ⊢ t ⇒ u : A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒ u : B
  -- ADE: `app-subst` of `_⊢_⇒_∷_`, in `Definition/Typed.agda`.
  /-- An application reduces its function, with the premises of `(∘)`. -/
  | app : Γ ⊢ t₁ ⇒ t₂ : pi p q A B → Γ ⊢ a : A →
      Γ ⊢ app p t₁ a ⇒ app p t₂ a : B.instantiate a
  -- ADE: `β-red` of `_⊢_⇒_∷_`, in `Definition/Typed.agda`.
  /-- `(β)`: applying an abstraction reduces to its body with the argument substituted. -/
  | beta : Γ ⊢ pi p q A B → Γ ∙ A ⊢ t : B → Γ ⊢ a : A →
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
  -- ADE: `id` of `_⊢_⇒*_∷_`, in `Definition/Typed.agda`.
  /-- A term of a type reduces to itself in no step. -/
  | refl : Γ ⊢ t : A → Γ ⊢ t ⇒* t : A
  -- ADE: `_⇨_` of `_⊢_⇒*_∷_`, in `Definition/Typed.agda`.
  /-- A step followed by any number of steps. -/
  | step : Γ ⊢ t₁ ⇒ t₂ : A → Γ ⊢ t₂ ⇒* t₃ : A → Γ ⊢ t₁ ⇒* t₃ : A

-- ADE: `_⊢_↘_∷_`, in `Definition/Typed.agda`.
/--
`Γ ⊢ t ↘ u : A`: in the context `Γ`, the term `t` of type `A` reduces to the weak head normal form
`u`.
-/
def TermRedWhnf (Γ : Con k n) (t u A : Term k n) : Prop :=
  (Γ ⊢ t ⇒* u : A) ∧ Whnf u

@[inherit_doc] notation:40 Γ:41 " ⊢ " t:41 " ↘ " u:41 " : " A:41 => TermRedWhnf Γ t u A

set_option hygiene false in
/-- `Γ ⊢ A ⇒ B`: in the context `Γ`, the type `A` reduces to `B` in one step. -/
notation:40 Γ:41 " ⊢ " A:41 " ⇒ " B:41 => TypeRed Γ A B

/-- `Γ ⊢ A ⇒ B`: in the context `Γ`, the type `A` reduces to `B` in one step. -/
inductive TypeRed {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Prop where
  -- ADE: `univ` of `_⊢_⇒_`, in `Definition/Typed.agda`.
  /-- A type reduces as a term of a universe. -/
  | univ : Γ ⊢ A ⇒ B : univ l → Γ ⊢ A ⇒ B

set_option hygiene false in
/-- `Γ ⊢ A ⇒* B`: in the context `Γ`, the type `A` reduces to `B` in any number of steps. -/
notation:40 Γ:41 " ⊢ " A:41 " ⇒* " B:41 => TypeRedStar Γ A B

/-- `Γ ⊢ A ⇒* B`: in the context `Γ`, the type `A` reduces to `B` in any number of steps. -/
inductive TypeRedStar {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Prop where
  -- ADE: `id` of `_⊢_⇒*_`, in `Definition/Typed.agda`.
  /-- A type reduces to itself in no step. -/
  | refl : Γ ⊢ A → Γ ⊢ A ⇒* A
  -- ADE: `_⇨_` of `_⊢_⇒*_`, in `Definition/Typed.agda`.
  /-- A step followed by any number of steps. -/
  | step : Γ ⊢ A₁ ⇒ A₂ → Γ ⊢ A₂ ⇒* A₃ → Γ ⊢ A₁ ⇒* A₃

-- ADE: `_⊢_↘_`, in `Definition/Typed.agda`.
/-- `Γ ⊢ A ↘ B`: in the context `Γ`, the type `A` reduces to the weak head normal form `B`. -/
def TypeRedWhnf (Γ : Con k n) (A B : Term k n) : Prop :=
  (Γ ⊢ A ⇒* B) ∧ Whnf B

@[inherit_doc] notation:40 Γ:41 " ⊢ " A:41 " ↘ " B:41 => TypeRedWhnf Γ A B

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

/-- A reduction of a type is an equality of types. -/
theorem TypeRed.typeEq : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
  | .univ h => .univ h.termEq

/-- Any number of reductions of a type is an equality of types. -/
theorem TypeRedStar.typeEq : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
  | .refl h => .refl h
  | .step h hs => .trans h.typeEq hs.typeEq

-- ADE: `conv*`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Any number of reductions has any type equal to its own, as `(conv)`. -/
theorem TermRedStar.conv : Γ ⊢ t ⇒* u : A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u : B
  | .refl h, hA => .refl (.conv h hA)
  | .step h hs, hA => .step (.conv h hA) (hs.conv hA)

-- ADE: `conv↘∷`, in `Definition/Typed/Properties/Reduction.agda`.
/-- A reduction to a weak head normal form has any type equal to its own. -/
theorem TermRedWhnf.conv (h : Γ ⊢ t ↘ u : A) (hA : Γ ⊢ A ≡ B) : Γ ⊢ t ↘ u : B :=
  ⟨h.1.conv hA, h.2⟩

-- ADE: `_⇨∷*_`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Two reductions in sequence are a reduction. -/
theorem TermRedStar.trans (h₁ : Γ ⊢ t₁ ⇒* t₂ : A) (h₂ : Γ ⊢ t₂ ⇒* t₃ : A) :
    Γ ⊢ t₁ ⇒* t₃ : A := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

-- ADE: `_⇨*_`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Two reductions of types in sequence are a reduction of types. -/
theorem TypeRedStar.trans (h₁ : Γ ⊢ A₁ ⇒* A₂) (h₂ : Γ ⊢ A₂ ⇒* A₃) : Γ ⊢ A₁ ⇒* A₃ := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

-- ADE: `univ*`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Any number of reductions of a term of a universe are reductions of a type. -/
theorem TermRedStar.univ (h : Γ ⊢ A ⇒* B : Term.univ l) : Γ ⊢ A ⇒* B := by
  generalize hU : Term.univ l = U at h
  induction h with
  | refl h => exact .refl (.univ (hU ▸ h))
  | step h _ ih => exact .step (.univ (hU ▸ h)) (ih hU)

-- ADE: `app-subst*`, in `Definition/Typed/Properties/Admissible/Pi.agda`.
/-- An application reduces its function, in any number of steps, with the premises of `(∘)`. -/
theorem TermRedStar.app (h : Γ ⊢ t₁ ⇒* t₂ : pi p q A B) (ha : Γ ⊢ a : A) :
    Γ ⊢ app p t₁ a ⇒* app p t₂ a : B.instantiate a := by
  generalize hPi : pi p q A B = C at h
  induction h with
  | refl h => exact .refl (.app (hPi ▸ h) ha)
  | step h _ ih => exact .step (.app (hPi ▸ h) ha) (ih hPi)

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

/-- A type in weak head normal form does not reduce. -/
theorem Whnf.not_typeRed : Whnf A → ¬ Γ ⊢ A ⇒ B
  | h, .univ hr => h.not_termRed hr

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

-- ADE: `whrDet`, in `Definition/Typed/Properties/Reduction.agda`.
/-- A type reduces in one step to the same type, as a term of any two universes. -/
theorem TypeRed.det : Γ ⊢ A ⇒ B₁ → Γ ⊢ A ⇒ B₂ → B₁ = B₂
  | .univ h₁, .univ h₂ => h₁.det h₂

-- ADE: `whrDet*`, in `Definition/Typed/Properties/Reduction.agda`.
/-- A type reduces to at most one weak head normal form, as a term does. -/
theorem TypeRedWhnf.det : Γ ⊢ A ↘ B₁ → Γ ⊢ A ↘ B₂ → B₁ = B₂ := by
  rintro ⟨h₁, hw₁⟩ ⟨h₂, hw₂⟩
  induction h₁ generalizing B₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step h => exact absurd h hw₁.not_typeRed
  | step h₁ _ ih =>
    cases h₂ with
    | refl => exact absurd h₁ hw₂.not_typeRed
    | step h₂ hs₂ => exact ih hw₁ (h₁.det h₂ ▸ hs₂) hw₂

/-!
The weakening of the reductions: a weakening only renames the variables, so that it keeps the shape
of the weak head normal forms and the steps of a reduction, in every well-formed context that
contains its own.
-/

-- ADE: `wkNeutral`, in `Definition/Untyped/Neutral.agda`.
/-- A neutral term stays neutral when weakened. -/
theorem Neutral.wk (ρ : Wk m n) : Neutral t → Neutral (t.wk ρ)
  | .var => .var
  | .app h => .app (h.wk ρ)

-- ADE: `wkWhnf`, in `Definition/Untyped/Whnf.agda`.
/-- A weak head normal form stays one when weakened. -/
theorem Whnf.wk (ρ : Wk m n) : Whnf t → Whnf (t.wk ρ)
  | .univ => .univ
  | .pi => .pi
  | .lam => .lam
  | .ne h => .ne (h.wk ρ)

-- ADE: `wkType`, in `Definition/Untyped/Whnf.agda`.
/-- A type in weak head normal form stays one when weakened. -/
theorem WhnfType.wk (ρ : Wk m n) : WhnfType A → WhnfType (A.wk ρ)
  | .univ => .univ
  | .pi => .pi
  | .ne h => .ne (h.wk ρ)

-- ADE: `wkRedTerm`, in `Definition/Typed/Weakening.agda`.
/-- A step of reduction stays one in every well-formed context that contains its own. -/
theorem TermRed.wk (h : Γ ⊢ t ⇒ u : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.wk ρ ⇒ u.wk ρ : A.wk ρ := by
  induction h with
  | conv _ hA ih => exact .conv ih (hA.wk hρ hΔ)
  | app _ ha ih =>
    rw [wk_instantiate]
    exact .app ih (ha.wk hρ hΔ)
  | beta hPi ht ha =>
    rw [wk_instantiate, wk_instantiate]
    exact match ht.wfCon with
      | .snoc hA => .beta (hPi.wk hρ hΔ) (ht.wk hρ.lift (.snoc (hA.wk hρ hΔ))) (ha.wk hρ hΔ)

-- ADE: `wkRed*Term`, in `Definition/Typed/Weakening.agda`.
/--
Any number of steps of reduction stay steps in every well-formed context that contains their own.
-/
theorem TermRedStar.wk (h : Γ ⊢ t ⇒* u : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.wk ρ ⇒* u.wk ρ : A.wk ρ := by
  induction h with
  | refl ht => exact .refl (ht.wk hρ hΔ)
  | step h _ ih => exact .step (h.wk hρ hΔ) ih

-- ADE: `wkRed↘Term`, in `Definition/Typed/Weakening.agda`.
/--
A reduction to a weak head normal form stays one in every well-formed context that contains its own.
-/
theorem TermRedWhnf.wk (h : Γ ⊢ t ↘ u : A) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ t.wk ρ ↘ u.wk ρ : A.wk ρ :=
  ⟨h.1.wk hρ hΔ, h.2.wk ρ⟩

-- ADE: `wkRed`, in `Definition/Typed/Weakening.agda`.
/-- A step of reduction of a type stays one in every well-formed context that contains its own. -/
theorem TypeRed.wk (h : Γ ⊢ A ⇒ B) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ A.wk ρ ⇒ B.wk ρ :=
  match h with
  | .univ h => .univ (h.wk hρ hΔ)

-- ADE: `wkRed*`, in `Definition/Typed/Weakening.agda`.
/--
Any number of steps of reduction of a type stay steps in every well-formed context that contains
their own.
-/
theorem TypeRedStar.wk (h : Γ ⊢ A ⇒* B) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    Δ ⊢ A.wk ρ ⇒* B.wk ρ := by
  induction h with
  | refl hA => exact .refl (hA.wk hρ hΔ)
  | step h _ ih => exact .step (h.wk hρ hΔ) ih

-- ADE: `wkRed↘`, in `Definition/Typed/Weakening.agda`.
/--
A reduction of a type to a weak head normal form stays one in every well-formed context that
contains its own.
-/
theorem TypeRedWhnf.wk (h : Γ ⊢ A ↘ B) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) : Δ ⊢ A.wk ρ ↘ B.wk ρ :=
  ⟨h.1.wk hρ hΔ, h.2.wk ρ⟩

end Sic.Core
