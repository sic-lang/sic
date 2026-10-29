module

public import Sic.Core.Substitution

/-!
# Typing

The judgments of RFC 24 for the terms of `Sic.Core.Syntax`: a context is well formed, `⊢ Γ`, a term
has a type, `Γ ⊢ t : A`, and two terms are equal at a type, `Γ ⊢ t ≡ u : A`.
They are defined together, since each uses the others, and each rule has the name of the RFC.
A type is a term of a universe, as in the RFC, so that no judgment of its own says that a term is a
type.
Grades are part of the terms, but no rule reads them: the usage of a term is a separate judgment.
-/

@[expose] public section

namespace Sic.Core

/-- A context of `n` declarations over `k` level variables. -/
inductive Con (k : Nat) : Nat → Type where
  /-- The empty context. -/
  | empty : Con k 0
  /-- `Γ ∙ A`: the context `Γ` extended by the type `A` of a new variable, over those of `Γ`. -/
  | snoc (Γ : Con k n) (A : Term k n) : Con k (n + 1)

@[inherit_doc] infixl:67 " ∙ " => Con.snoc

/--
The type of the variable of index `x` in the context `Γ`, moved to the whole context: its
declaration is followed by `x` others, which its type does not use.
-/
def Con.get : Con k n → Fin n → Term k n
  | snoc _ A, ⟨0, _⟩ => A.wk1
  | snoc Γ _, ⟨x + 1, h⟩ => (Γ.get ⟨x, Nat.lt_of_succ_lt_succ h⟩).wk1

/-- The innermost variable has the type of the last declaration. -/
@[simp] theorem Con.get_zero (Γ : Con k n) (A : Term k n) : (Γ ∙ A).get 0 = A.wk1 := rfl

/-- The other variables have the types they have in the rest of the context. -/
@[simp] theorem Con.get_succ (Γ : Con k n) (A : Term k n) (x : Fin n) :
    (Γ ∙ A).get x.succ = (Γ.get x).wk1 := rfl

set_option hygiene false in
/-- `⊢ Γ`: the context `Γ` is well formed. -/
notation:40 "⊢ " Γ:41 => WfCon Γ

set_option hygiene false in
/-- `Γ ⊢ t : A`: in the context `Γ`, the term `t` has the type `A`. -/
notation:40 Γ:41 " ⊢ " t:41 " : " A:41 => HasType Γ t A

set_option hygiene false in
/-- `Γ ⊢ t ≡ u : A`: in the context `Γ`, the terms `t` and `u` are equal at the type `A`. -/
notation:40 Γ:41 " ⊢ " t:41 " ≡ " u:41 " : " A:41 => TermEq Γ t u A

open Term

mutual

/-- `⊢ Γ`: the context `Γ` is well formed. -/
inductive WfCon {k : Nat} : {n : Nat} → Con k n → Prop where
  /-- `(ctx_ε)`: the empty context is well formed. -/
  | empty : ⊢ .empty
  /-- `(ctx_,)`: a context extended by a type of a universe is well formed. -/
  | snoc : Γ ⊢ A : univ l → ⊢ Γ ∙ A

/-- `Γ ⊢ t : A`: in the context `Γ`, the term `t` has the type `A`. -/
inductive HasType {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Prop where
  /-- `(var)`: a variable has the type of its declaration. -/
  | var : ⊢ Γ → Γ ⊢ var x : Γ.get x
  /-- `(conv)`: a term has any type equal to its own. -/
  | conv : Γ ⊢ t : A → Γ ⊢ A ≡ B : univ l → Γ ⊢ t : B
  /-- `(univ)`: a universe is a type of the universe just above it. -/
  | univ : ⊢ Γ → Γ ⊢ univ l : univ l.succ
  /-- `(Π)`: the type of functions lives at the larger level of its domain and its codomain. -/
  | pi : Γ ⊢ A : univ l₁ → Γ ∙ A ⊢ B : univ l₂ → Γ ⊢ pi p q A B : univ (l₁ ⊔ l₂)
  /-- `(λ)`: an abstraction has the type of functions whose body has its type. -/
  | lam : Γ ⊢ pi p q A B : univ l → Γ ∙ A ⊢ t : B → Γ ⊢ lam p A t : pi p q A B
  /-- `(∘)`: an application has the codomain of the function, at the argument. -/
  | app : Γ ⊢ t : pi p q A B → Γ ⊢ a : A → Γ ⊢ app p t a : B.instantiate a

/-- `Γ ⊢ t ≡ u : A`: in the context `Γ`, the terms `t` and `u` are equal at the type `A`. -/
inductive TermEq {k : Nat} : {n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop where
  /-- `(refl)` -/
  | refl : Γ ⊢ t : A → Γ ⊢ t ≡ t : A
  /-- `(sym)` -/
  | symm : Γ ⊢ t ≡ u : A → Γ ⊢ u ≡ t : A
  /-- `(trans)` -/
  | trans : Γ ⊢ t₁ ≡ t₂ : A → Γ ⊢ t₂ ≡ t₃ : A → Γ ⊢ t₁ ≡ t₃ : A
  /-- `(conv_≡)`: two terms are equal at any type equal to their own. -/
  | conv : Γ ⊢ t ≡ u : A → Γ ⊢ A ≡ B : univ l → Γ ⊢ t ≡ u : B
  /-- `(univ_≡)`: two universes are equal when their levels are. -/
  | univ : ⊢ Γ → l₁ ≈ l₂ → Γ ⊢ univ l₁ ≡ univ l₂ : univ l₁.succ
  /-- The congruence of the type of functions, with the premises of `(Π)`. -/
  | pi : Γ ⊢ A₁ ≡ A₂ : univ l₁ → Γ ∙ A₁ ⊢ B₁ ≡ B₂ : univ l₂ →
      Γ ⊢ pi p q A₁ B₁ ≡ pi p q A₂ B₂ : univ (l₁ ⊔ l₂)
  /-- The congruence of abstraction, with the premises of `(λ)`. -/
  | lam : Γ ⊢ pi p q A₁ B : univ l → Γ ⊢ A₁ ≡ A₂ : univ l₁ → Γ ∙ A₁ ⊢ t₁ ≡ t₂ : B →
      Γ ⊢ lam p A₁ t₁ ≡ lam p A₂ t₂ : pi p q A₁ B
  /-- The congruence of application, with the premises of `(∘)`. -/
  | app : Γ ⊢ t₁ ≡ t₂ : pi p q A B → Γ ⊢ a₁ ≡ a₂ : A →
      Γ ⊢ app p t₁ a₁ ≡ app p t₂ a₂ : B.instantiate a₁
  /-- `(β)`: applying an abstraction substitutes the argument in its body. -/
  | beta : Γ ⊢ pi p q A B : univ l → Γ ∙ A ⊢ t : B → Γ ⊢ a : A →
      Γ ⊢ app p (lam p A t) a ≡ t.instantiate a : B.instantiate a
  /-- `(η)`: a function is the abstraction of its application to the variable it binds. -/
  | eta : Γ ⊢ t : pi p q A B → Γ ⊢ t ≡ lam p A (app p t.wk1 (var 0)) : pi p q A B

end

/-!
Every judgment implies that its context is well formed, as RFC 24 states: each rule has a premise
in the same context, down to a rule whose premise is `⊢ Γ`.
-/

mutual

theorem HasType.wfCon : Γ ⊢ t : A → ⊢ Γ
  | .var h | .univ h => h
  | .conv h _ | .pi h _ | .lam h _ | .app h _ => h.wfCon

theorem TermEq.wfCon : Γ ⊢ t ≡ u : A → ⊢ Γ
  | .univ h _ => h
  | .refl h | .eta h | .lam h _ _ | .beta h _ _ => h.wfCon
  | .symm h | .trans h _ | .conv h _ | .pi h _ | .app h _ => h.wfCon

end

/-!
The inversion of the function types: a function type has a type only when its domain and its
codomain have one.
The proof generalizes the term of the judgment to any term equal to `pi p q A B`, since an induction
on a judgment of the mutual types of the judgments cannot fix its term.
-/

private theorem HasType.inv_pi_aux : Γ ⊢ s : C → s = Term.pi p q A B →
    (∃ l, Γ ⊢ A : Term.univ l) ∧ ∃ l, Γ ∙ A ⊢ B : Term.univ l
  | .conv h _, e => h.inv_pi_aux e
  | .pi hA hB, e => by cases e; exact ⟨⟨_, hA⟩, _, hB⟩
  | .var _, e | .univ _, e | .lam .., e | .app .., e => by cases e

/-- The domain and the codomain of a function type that has a type are types. -/
theorem HasType.inv_pi (h : Γ ⊢ Term.pi p q A B : C) :
    (∃ l, Γ ⊢ A : Term.univ l) ∧ ∃ l, Γ ∙ A ⊢ B : Term.univ l :=
  h.inv_pi_aux rfl

end Sic.Core
