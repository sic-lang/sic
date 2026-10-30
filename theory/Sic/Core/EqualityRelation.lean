module

public import Sic.Core.Reduction
public import Sic.Core.TypedSubstitution
import Sic.Core.WellFormed

/-!
# Equality Relations

The equalities over which the logical relation is defined, as in the formalization of ADE: an
equality of types `Γ ⊢ A ≅ B`, an equality of terms `Γ ⊢ t ≅ u : A`, and an equality of neutral
terms `Γ ⊢ t ~ u : A`, with the properties its proofs use.
Its proofs then hold for any of them: for the equality of `Sic.Core.Typing`, the only one so far,
they show that typed terms reduce to weak head normal forms; for the equality that an algorithm
decides, they will show that the algorithm decides the equality of `Sic.Core.Typing`.
The equality of types relates the types as `Sic.Core.Typing` does, whatever universe their terms
are in.

## Correspondence with the Formalization of ADE

| Field | Field of ADE's `Equality-relations`, in `Definition/Typed/EqualityRelation.agda` |
| --- | --- |
| `eqType` | `_⊢_≅_` |
| `eq` | `_⊢_≅_∷_` |
| `eqNeutral` | `_⊢_~_∷_` |
| `ofNeutral` | `~-to-≅ₜ` |
| `typeEq`, `termEq` | `≅-eq`, `≅ₜ-eq` |
| `ofUniv` | `≅-univ` |
| `symmType`, `symm`, `symmNeutral` | `≅-sym`, `≅ₜ-sym`, `~-sym` |
| `transType`, `trans`, `transNeutral` | `≅-trans`, `≅ₜ-trans`, `~-trans` |
| `conv`, `convNeutral` | `≅-conv`, `~-conv` |
| `wkType`, `wk`, `wkNeutral` | `≅-wk`, `≅ₜ-wk`, `~-wk` |
| `redType`, `red` | `≅-red`, `≅ₜ-red` |
| `univ` | `≅ₜ-U-cong` |
| `pi` | `≅ₜ-ΠΣ-cong` |
| `eta` | `≅-η-eq` |
| `var` | `~-var` |
| `app` | `~-app` |

| Definition or theorem | Definition or theorem of ADE |
| --- | --- |
| `EqualityRelation.termEqRelation` | `eqRelInstance`, in `Definition/Typed/EqRelInstance.agda` |

Their `≅ₜ-ΠΣ-cong` relates a domain and a codomain in the same universe, which their `Lift` moves
types to, while `pi` takes the larger of their levels, as `(Π)` does.
Their `≅-η-eq` relates functions that are abstractions or neutral terms, `Function⁺`, while `eta`
relates weak head normal forms, which are the same at a type of functions.
The fields of their other types, of their levels, and of their option `Var-included` are not here.
-/

@[expose] public section

namespace Sic.Core

section

set_option hygiene false in
/-- `Γ ⊢ A ≅ B`: in the context `Γ`, the types `A` and `B` are equal. -/
local notation:40 Γ:41 " ⊢ " A:41 " ≅ " B:41 => eqType Γ A B

set_option hygiene false in
/-- `Γ ⊢ t ≅ u : A`: in the context `Γ`, the terms `t` and `u` are equal at the type `A`. -/
local notation:40 Γ:41 " ⊢ " t:41 " ≅ " u:41 " : " A:41 => eq Γ t u A

set_option hygiene false in
/-- `Γ ⊢ t ~ u : A`: in the context `Γ`, the neutral terms `t` and `u` are equal at the type `A`. -/
local notation:40 Γ:41 " ⊢ " t:41 " ~ " u:41 " : " A:41 => eqNeutral Γ t u A

/--
An equality of types, an equality of terms and an equality of neutral terms, contained in the
equalities of `Sic.Core.Typing`, with the properties of an equivalence, the rules of
`Sic.Core.Typing` that build terms of each kind, and the closure of the equalities of types and of
terms under reduction to weak head normal forms.
-/
class EqualityRelation where
  /-- `Γ ⊢ A ≅ B`: in the context `Γ`, the types `A` and `B` are equal. -/
  eqType : {k n : Nat} → Con k n → Term k n → Term k n → Prop
  /-- `Γ ⊢ t ≅ u : A`: in the context `Γ`, the terms `t` and `u` are equal at the type `A`. -/
  eq : {k n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop
  /-- `Γ ⊢ t ~ u : A`: in the context `Γ`, the neutral terms `t` and `u` are equal at the type `A`. -/
  eqNeutral : {k n : Nat} → Con k n → Term k n → Term k n → Term k n → Prop
  /-- Two equal neutral terms are equal. -/
  ofNeutral : Γ ⊢ t ~ u : A → Γ ⊢ t ≅ u : A
  /-- Two equal types are equal in `Sic.Core.Typing`. -/
  typeEq : Γ ⊢ A ≅ B → Γ ⊢ A ≡ B
  /-- Two equal terms are equal in `Sic.Core.Typing`. -/
  termEq : Γ ⊢ t ≅ u : A → Γ ⊢ t ≡ u : A
  /-- Two equal terms of a universe are equal types. -/
  ofUniv : Γ ⊢ A ≅ B : Term.univ l → Γ ⊢ A ≅ B
  /-- The equality of types is symmetric. -/
  symmType : Γ ⊢ A ≅ B → Γ ⊢ B ≅ A
  /-- The equality is symmetric. -/
  symm : Γ ⊢ t ≅ u : A → Γ ⊢ u ≅ t : A
  /-- The equality of neutral terms is symmetric. -/
  symmNeutral : Γ ⊢ t ~ u : A → Γ ⊢ u ~ t : A
  /-- The equality of types is transitive. -/
  transType : Γ ⊢ A₁ ≅ A₂ → Γ ⊢ A₂ ≅ A₃ → Γ ⊢ A₁ ≅ A₃
  /-- The equality is transitive. -/
  trans : Γ ⊢ t₁ ≅ t₂ : A → Γ ⊢ t₂ ≅ t₃ : A → Γ ⊢ t₁ ≅ t₃ : A
  /-- The equality of neutral terms is transitive. -/
  transNeutral : Γ ⊢ t₁ ~ t₂ : A → Γ ⊢ t₂ ~ t₃ : A → Γ ⊢ t₁ ~ t₃ : A
  /-- Two terms are equal at any type equal to their own. -/
  conv : Γ ⊢ t ≅ u : A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u : B
  /-- Two neutral terms are equal at any type equal to their own. -/
  convNeutral : Γ ⊢ t ~ u : A → Γ ⊢ A ≡ B → Γ ⊢ t ~ u : B
  /-- Two types stay equal in every well-formed context that contains their own. -/
  wkType : Γ ⊢ A ≅ B → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ A.wk ρ ≅ B.wk ρ
  /-- Two terms stay equal in every well-formed context that contains their own. -/
  wk : Γ ⊢ t ≅ u : A → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ t.wk ρ ≅ u.wk ρ : A.wk ρ
  /-- Two neutral terms stay equal in every well-formed context that contains their own. -/
  wkNeutral : Γ ⊢ t ~ u : A → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊢ t.wk ρ ~ u.wk ρ : A.wk ρ
  /-- Two types are equal when their weak head normal forms are. -/
  redType : Γ ⊢ A₁ ↘ B₁ → Γ ⊢ A₂ ↘ B₂ → Γ ⊢ B₁ ≅ B₂ → Γ ⊢ A₁ ≅ A₂
  /--
  Two terms are equal when their weak head normal forms are, at the weak head normal form of their
  type.
  -/
  red : Γ ⊢ A ↘ B → Γ ⊢ t₁ ↘ u₁ : B → Γ ⊢ t₂ ↘ u₂ : B → Γ ⊢ u₁ ≅ u₂ : B → Γ ⊢ t₁ ≅ t₂ : A
  /-- `(U_≡)`: two universes are equal when their levels are. -/
  univ : ⊢ Γ → l₁ ≈ l₂ → Γ ⊢ Term.univ l₁ ≅ Term.univ l₂ : Term.univ l₁.succ
  /-- The congruence of the type of functions. -/
  pi : Γ ⊢ A₁ ≅ A₂ : Term.univ l₁ → Γ ∙ A₁ ⊢ B₁ ≅ B₂ : Term.univ l₂ →
      Γ ⊢ Term.pi p q A₁ B₁ ≅ Term.pi p q A₂ B₂ : Term.univ (l₁ ⊔ l₂)
  /--
  `(η)`: two functions in weak head normal form are equal when their applications to the variable
  of a new declaration are.
  -/
  eta : Γ ⊢ t₁ : Term.pi p q A B → Γ ⊢ t₂ : Term.pi p q A B → Whnf t₁ → Whnf t₂ →
      Γ ∙ A ⊢ Term.app p t₁.wk1 (Term.var 0) ≅ Term.app p t₂.wk1 (Term.var 0) : B →
      Γ ⊢ t₁ ≅ t₂ : Term.pi p q A B
  /-- A variable is a neutral term equal to itself. -/
  var : Γ ⊢ Term.var x : A → Γ ⊢ Term.var x ~ Term.var x : A
  /-- The congruence of the application of a neutral term. -/
  app : Γ ⊢ t₁ ~ t₂ : Term.pi p q A B → Γ ⊢ a₁ ≅ a₂ : A →
      Γ ⊢ Term.app p t₁ a₁ ~ Term.app p t₂ a₂ : B.instantiate a₁

end

@[inherit_doc] notation:40 Γ:41 " ⊢ " A:41 " ≅ " B:41 => EqualityRelation.eqType Γ A B
@[inherit_doc] notation:40 Γ:41 " ⊢ " t:41 " ≅ " u:41 " : " A:41 => EqualityRelation.eq Γ t u A

@[inherit_doc]
notation:40 Γ:41 " ⊢ " t:41 " ~ " u:41 " : " A:41 => EqualityRelation.eqNeutral Γ t u A

/--
`(η)` as an extensionality: two functions are equal when their applications to the variable of a new
declaration are.
-/
theorem TermEq.funext (h₁ : Γ ⊢ t₁ : Term.pi p q A B) (h₂ : Γ ⊢ t₂ : Term.pi p q A B)
    (h : Γ ∙ A ⊢ Term.app p t₁.wk1 (Term.var 0) ≡ Term.app p t₂.wk1 (Term.var 0) : B) :
    Γ ⊢ t₁ ≡ t₂ : Term.pi p q A B :=
  -- Each function is equal to the abstraction of its application, by `(η)`, and both abstractions
  -- are equal by congruence.
  have hPi := h₁.wfType
  have ⟨_, hA⟩ := hPi.inv_pi.1
  .trans (.eta h₁) (.trans (.lam hPi (.refl hA) h) (.symm (.eta h₂)))

/--
The equality of `Sic.Core.Typing`, for both kinds of terms, as an equality relation.
It is not an instance, so that each proof chooses its equality relation.
-/
@[instance_reducible]
def EqualityRelation.termEqRelation : EqualityRelation where
  eqType := TypeEq
  eq := TermEq
  eqNeutral := TermEq
  ofNeutral h := h
  typeEq h := h
  termEq h := h
  ofUniv := .univ
  symmType := .symm
  symm := .symm
  symmNeutral := .symm
  transType := .trans
  trans := .trans
  transNeutral := .trans
  conv := .conv
  convNeutral := .conv
  wkType := TypeEq.wk
  wk := TermEq.wk
  wkNeutral := TermEq.wk
  -- Each type or term is equal to its weak head normal form, and a term is so at the weak head
  -- normal form `B` of its type, which is equal to the type.
  redType h₁ h₂ h := .trans h₁.1.typeEq (.trans h (.symm h₂.1.typeEq))
  red hA h₁ h₂ h := .conv (.trans h₁.1.termEq (.trans h (.symm h₂.1.termEq))) (.symm hA.1.typeEq)
  univ := .univ
  pi := .pi
  eta h₁ h₂ _ _ := .funext h₁ h₂
  var := .refl
  app := .app

end Sic.Core
