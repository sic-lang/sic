module

/-!
# Sets

The sets of numbers of uses, or of pairs of numbers of uses, by which annexes 03 and 04 of RFC 36
give a meaning to the multiplicities and to the grades, and the sets of grades whose positions the
erasure of annex 15 replaces.
Lean does not provide sets, and this package depends on no library that does, so a set is the
predicate that tells which elements belong to it.
-/

@[expose] public section

namespace Sic.Math

/-- A set of elements of `α`, given by the predicate that tells which elements belong to it. -/
def Set (α : Type) : Type := α → Prop

namespace Set

instance {α : Type} : Membership α (Set α) where
  mem S a := S a

/-- The set of the elements that satisfy `p`, written `{ a | p a }`. -/
def ofPred {α : Type} (p : α → Prop) : Set α := p

/-- The set of the elements that satisfy a property, as `{ a | a ≤ 3 }`. -/
syntax "{ " ident " | " term " }" : term

macro_rules
  | `({ $a:ident | $p }) => `(Sic.Math.Set.ofPred fun $a => $p)

@[simp] theorem mem_ofPred {α : Type} {p : α → Prop} {a : α} : a ∈ ofPred p ↔ p a := Iff.rfl

instance {α : Type} : HasSubset (Set α) where
  Subset S T := ∀ a, a ∈ S → a ∈ T

@[simp] theorem subset_def {α : Type} {S T : Set α} : S ⊆ T ↔ ∀ a, a ∈ S → a ∈ T := Iff.rfl

instance {α : Type} : Union (Set α) where
  union S T := { a | a ∈ S ∨ a ∈ T }

@[simp] theorem mem_union {α : Type} {S T : Set α} {a : α} : a ∈ S ∪ T ↔ a ∈ S ∨ a ∈ T := Iff.rfl

end Set

end Sic.Math
