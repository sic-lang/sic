module

public import Sic.Core.EqualityRelation
import Sic.Core.WellFormed

/-!
# Logical Relation

The reducibility of the types and of the terms of the core, as in the formalization of ADE: a type
is reducible when it reduces to a weak head normal form whose parts are reducible, and its
interpretation says which types are equal to it and which terms of it are equal.
It is defined over any equality relation of `Sic.Core.EqualityRelation`.

The relation is a predicate of a type and of its interpretation, as in the formalization of Pujet,
since a relation that computes the interpretation from a proof of reducibility needs
induction-recursion, which Lean does not have.
The interpretation of a universe mentions the reducibility of its elements, at a smaller level,
which an inductive predicate cannot mention in its own indices: the relation at a level `l` is
defined from the relations at the smaller levels, as ADE do with their `rec`.

A level `l`, with variables, bounds the universes of a type by the value of `l` when its variables
take the value `0`: each rule of `Sic.Core.Typing` keeps the order of the values of its levels, so
that this value is a bound that holds whatever the variables, while the equality of two universes
still requires their levels to be equal.

## Correspondence with the Formalizations of ADE and of Pujet

Pujet's relation is a predicate of a type and of its interpretation, as here, where ADE's relation
computes the interpretation from a proof of reducibility.
Both have a constructor `emb`, which moves a reducible type to a larger level, while the relation at
a level here interprets each universe at its own level: a reducible type stays reducible at the
larger levels, a lemma instead of a constructor, so that each weak head normal form has one
constructor.
The interpretation of a type reduces it and compares it as a type, as ADE do, so that it does not
depend on the universe that a proof of its reducibility chooses for it.
Their relation also covers their other types, levels and definitions.
`LogRel.escape_eqType` and `LogRel.escape_eqTerm` give the equalities of `Sic.Core.Typing`, which
ADE and Pujet obtain from the equality relation, after their `escapeEq` and `escapeTermEq`.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `↑ᵘ`, which sends the neutral levels to `0`, in `Definition/LogicalRelation.agda`.
-- Pujet: none, with a single universe.
/--
The level of the logical relation that interprets the universe of level `l`: the value of `l` when
its variables take the value `0`.
-/
def Level.bound (l : Level k) : Nat := l.eval fun _ => 0

namespace Reducibility

/-- The interpretation of a reducible type `A`: the types equal to `A`, and its equal terms. -/
structure Interpretation (k n : Nat) where
  -- ADE: `_⊩⟨_⟩_≡_/_`, in `Definition/LogicalRelation.agda`.
  -- Pujet: the second predicate of `_⊩LR_▸_▸_▸_`, in `Definition/LogicalRelation.agda`.
  /-- The types equal to `A`. -/
  eqType : Term k n → Prop
  -- ADE: `_⊩⟨_⟩_≡_∷_/_`, in `Definition/LogicalRelation.agda`.
  -- Pujet: the fourth predicate of `_⊩LR_▸_▸_▸_`, in `Definition/LogicalRelation.agda`.
  /-- The pairs of equal terms of `A`, of which a reducible term of `A` is equal to itself. -/
  eqTerm : Term k n → Term k n → Prop

/-- A relation between the types of each context and their interpretations. -/
abbrev Relation (k : Nat) := ∀ {n : Nat}, Con k n → Term k n → Interpretation k n → Prop

variable [EqualityRelation]

-- ADE: the module `LogRel`, with `rec` for `lower`, in `Definition/LogicalRelation.agda`.
-- Pujet: `_⊩LR_▸_▸_▸_`, with `rec` for `lower`, in `Definition/LogicalRelation.agda`.
/--
The logical relation at the level `l`, from the relations `lower` at the smaller levels, which
interpret the elements of the universes: `LogRel l lower Γ A P` says that the type `A` is reducible,
with the interpretation `P`.
Each constructor is a weak head normal form of types, and its interpretation is written in its
conclusion.
-/
inductive LogRel (l : Nat) (lower : ∀ l' < l, Relation k) : Relation k where
  -- ADE: `Uᵣ`, with `_⊩₁U_`, `_⊩₁U≡_/_` and `_⊩₁U_≡_∷U/_`, in `Definition/LogicalRelation.agda`.
  -- Pujet: `LRU`, in `Definition/LogicalRelation.agda`.
  /--
  A type that reduces to a universe of a smaller level: two types are equal to it when they reduce
  to a universe of an equal level, and two of its terms are equal when they reduce to types that are
  equal by the equality relation, and are reducible at the level of the universe, where the first
  interprets the second as an equal type.
  -/
  | univ {n} {Γ : Con k n} {A : Term k n} {L : Level k} (h : L.bound < l)
      (hA : Γ ⊢ A ⇒* Term.univ L) :
      LogRel l lower Γ A
        { eqType := fun B => ∃ L', (Γ ⊢ B ⇒* Term.univ L') ∧ L ≈ L'
          eqTerm := fun t u => ∃ A' B', (Γ ⊢ t ↘ A' : Term.univ L) ∧
            (Γ ⊢ u ↘ B' : Term.univ L) ∧ WhnfType A' ∧ WhnfType B' ∧
            (Γ ⊢ A' ≅ B' : Term.univ L) ∧
            ∃ P, lower _ h Γ t P ∧ (∃ Q, lower _ h Γ u Q) ∧ P.eqType u }
  -- ADE: `ne`, with `_⊩ne_`, `_⊩ne_≡_/_` and `_⊩neNf_≡_∷_`, in `Definition/LogicalRelation.agda`.
  -- Pujet: `LRne`, in `Definition/LogicalRelation.agda`.
  /--
  A type that reduces to a neutral type: two types are equal to it when they reduce to equal neutral
  types, and two of its terms are equal when they reduce to equal neutral terms.
  -/
  | ne {n} {Γ : Con k n} {A N : Term k n} (hA : Γ ⊢ A ⇒* N) (hN : Neutral N) (hNN : Γ ⊢ N ≅ N) :
      LogRel l lower Γ A
        { eqType := fun B => ∃ M, (Γ ⊢ B ⇒* M) ∧ Neutral M ∧ (Γ ⊢ N ≅ M)
          eqTerm := fun t u => ∃ t' u', (Γ ⊢ t ⇒* t' : N) ∧ (Γ ⊢ u ⇒* u' : N) ∧ Neutral t' ∧
            Neutral u' ∧ (Γ ⊢ t' ~ u' : N) }
  -- ADE: `Bᵣ`, with `_⊩ₗB⟨_⟩_`, `_⊩ₗB⟨_⟩_≡_/_` and `_⊩ₗΠ_≡_∷_/_`, in
  -- `Definition/LogicalRelation.agda`.
  -- Pujet: `LRΠ`, in `Definition/LogicalRelation.agda`.
  /--
  A type that reduces to a type of functions, whose domain `F` is reducible, with the
  interpretation `PF`, in every well-formed context that contains `Γ`, and whose codomain `G` is
  reducible at each reducible argument, with the interpretation `PG`, and equal at equal arguments.
  Two types are equal to it when they reduce to a type of functions whose domain and codomain are
  equal to `F` and `G`, and two of its terms are equal when they reduce to weak head normal forms
  that are equal by the equality relation, and whose applications to equal arguments are equal, in
  every well-formed context that contains `Γ`.
  -/
  | pi {n} {Γ : Con k n} {A F : Term k n} {G : Term k (n + 1)} {p q : Grade}
      (hA : Γ ⊢ A ⇒* Term.pi p q F G) (hPi : Γ ⊢ Term.pi p q F G ≅ Term.pi p q F G)
      (PF : ∀ {m}, Wk m n → Con k m → Interpretation k m)
      (PG : ∀ {m}, Wk m n → Con k m → Term k m → Interpretation k m)
      (hF : ∀ {m} {ρ : Wk m n} {Δ : Con k m}, ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        LogRel l lower Δ (F.wk ρ) (PF ρ Δ))
      (hG : ∀ {m} {ρ : Wk m n} {Δ : Con k m} {a}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → (PF ρ Δ).eqTerm a a →
        LogRel l lower Δ ((G.wk ρ.lift).instantiate a) (PG ρ Δ a))
      (hGext : ∀ {m} {ρ : Wk m n} {Δ : Con k m} {a b}, ρ ∷ Δ ⊇ Γ → ⊢ Δ →
        (PF ρ Δ).eqTerm a a → (PF ρ Δ).eqTerm b b → (PF ρ Δ).eqTerm a b →
        (PG ρ Δ a).eqType ((G.wk ρ.lift).instantiate b)) :
      LogRel l lower Γ A
        { eqType := fun B => ∃ (F' : Term k n) (G' : Term k (n + 1)),
            (Γ ⊢ B ⇒* Term.pi p q F' G') ∧ (Γ ⊢ Term.pi p q F G ≅ Term.pi p q F' G') ∧
            (∀ {m} {ρ : Wk m n} {Δ : Con k m}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → (PF ρ Δ).eqType (F'.wk ρ)) ∧
            (∀ {m} {ρ : Wk m n} {Δ : Con k m} {a}, ρ ∷ Δ ⊇ Γ → ⊢ Δ → (PF ρ Δ).eqTerm a a →
              (PG ρ Δ a).eqType ((G'.wk ρ.lift).instantiate a))
          eqTerm := fun t u => ∃ f g : Term k n, (Γ ⊢ t ↘ f : Term.pi p q F G) ∧
            (Γ ⊢ u ↘ g : Term.pi p q F G) ∧ (Γ ⊢ f ≅ g : Term.pi p q F G) ∧
            ∀ {m} {ρ : Wk m n} {Δ : Con k m} {a b}, ρ ∷ Δ ⊇ Γ → ⊢ Δ →
              (PF ρ Δ).eqTerm a a → (PF ρ Δ).eqTerm b b → (PF ρ Δ).eqTerm a b →
              (PG ρ Δ a).eqTerm (Term.app p (f.wk ρ) a) (Term.app p (g.wk ρ) b) }

-- ADE: `_⊩⟨_⟩_`, with `kit`, in `Definition/LogicalRelation.agda`.
-- Pujet: `_⊩⟨_⟩_`, with `kit`, in `Definition/LogicalRelation.agda`.
/--
`Γ ⊩⟨l⟩ A ▸ P`: in the context `Γ`, the type `A` is reducible at the level `l`, with the
interpretation `P`, each universe being interpreted by the relation at its own level.
-/
def LogicalRelation (l : Nat) : Relation k := LogRel l fun l' _ => LogicalRelation l'
termination_by l

@[inherit_doc]
notation:40 Γ:41 " ⊩⟨" l "⟩ " A:76 " ▸ " P:41 => LogicalRelation l Γ A P

/-- The logical relation at the level `l` is built from the relations at the smaller levels. -/
theorem LogicalRelation.unfold {Γ : Con k n} {A : Term k n} {P : Interpretation k n} :
    (Γ ⊩⟨l⟩ A ▸ P) = LogRel l (fun l' _ => LogicalRelation l') Γ A P := by
  rw [LogicalRelation]

/-!
The escape lemmas, as in ADE: a reducible type is a type, the terms that its interpretation equates
are equal by the equality relation, which is closed under reduction to weak head normal forms, and
the types and the terms that its interpretation equates are equal by `Sic.Core.Typing`, whose
equality contains the reductions and the equality relation.
-/

section Escape

variable {l : Nat} {lower : ∀ l' < l, Relation k}

-- ADE: `escape`, in `Definition/LogicalRelation/Properties/Escape.agda`.
-- Pujet: `escape`, in `Definition/LogicalRelation/Properties/Escape.agda`.
/-- A reducible type is a type. -/
theorem LogRel.escape : LogRel l lower Γ A P → Γ ⊢ A
  | .univ _ hA | .ne hA _ _ | .pi hA .. => hA.typeEq.wf.1

/-- The types that the interpretation of a reducible type equates to it are equal to it. -/
theorem LogRel.escape_eqType : LogRel l lower Γ A P → P.eqType B → Γ ⊢ A ≡ B
  | .univ _ hA, ⟨_, hB, hL⟩ =>
    .trans hA.typeEq (.trans (.univ (.univ hA.typeEq.wfCon hL)) (.symm hB.typeEq))
  | .ne hA _ _, ⟨_, hB, _, hNM⟩ =>
    .trans hA.typeEq (.trans (EqualityRelation.typeEq hNM) (.symm hB.typeEq))
  | .pi hA .., ⟨_, _, hB, hPi, _⟩ =>
    .trans hA.typeEq (.trans (EqualityRelation.typeEq hPi) (.symm hB.typeEq))

-- ADE: `escapeTermEq`, in `Definition/LogicalRelation/Properties/Escape.agda`.
-- Pujet: `escapeTermEq`, in `Definition/LogicalRelation/Properties/Escape.agda`.
/--
The terms that the interpretation of a reducible type equates are equal by the equality relation.
-/
theorem LogRel.escape_eq : LogRel l lower Γ A P → P.eqTerm t u → Γ ⊢ t ≅ u : A
  | .univ _ hA, ⟨_, _, ht, hu, _, _, hAB, _⟩ => EqualityRelation.red ⟨hA, .univ⟩ ht hu hAB
  | .ne hA hN _, ⟨_, _, ht, hu, ht', hu', htu⟩ =>
    EqualityRelation.red ⟨hA, .ne hN⟩ ⟨ht, .ne ht'⟩ ⟨hu, .ne hu'⟩ (EqualityRelation.ofNeutral htu)
  | .pi hA .., ⟨_, _, ht, hu, hfg, _⟩ => EqualityRelation.red ⟨hA, .pi⟩ ht hu hfg

/-- The terms that the interpretation of a reducible type equates are equal at that type. -/
theorem LogRel.escape_eqTerm (h : LogRel l lower Γ A P) (htu : P.eqTerm t u) : Γ ⊢ t ≡ u : A :=
  EqualityRelation.termEq (h.escape_eq htu)

end Escape

/-- A reducible type is a type. -/
theorem LogicalRelation.escape (h : Γ ⊩⟨l⟩ A ▸ P) : Γ ⊢ A :=
  (LogicalRelation.unfold ▸ h).escape

/-- The types that the interpretation of a reducible type equates to it are equal to it. -/
theorem LogicalRelation.escape_eqType (h : Γ ⊩⟨l⟩ A ▸ P) (hB : P.eqType B) : Γ ⊢ A ≡ B :=
  (LogicalRelation.unfold ▸ h).escape_eqType hB

/--
The terms that the interpretation of a reducible type equates are equal by the equality relation.
-/
theorem LogicalRelation.escape_eq (h : Γ ⊩⟨l⟩ A ▸ P) (htu : P.eqTerm t u) : Γ ⊢ t ≅ u : A :=
  (LogicalRelation.unfold ▸ h).escape_eq htu

/-- The terms that the interpretation of a reducible type equates are equal at that type. -/
theorem LogicalRelation.escape_eqTerm (h : Γ ⊩⟨l⟩ A ▸ P) (htu : P.eqTerm t u) :
    Γ ⊢ t ≡ u : A :=
  (LogicalRelation.unfold ▸ h).escape_eqTerm htu

end Reducibility

end Sic.Core
