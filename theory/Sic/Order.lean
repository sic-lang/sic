module

/-!
# Orders

The laws of the preorders and of the least upper bounds, as records whose fields are the laws, so
that each law is stated once and named, and each relation proves that it satisfies them.
They are stated on a relation, as the record `Equivalence` of Lean, which states the laws of the
equivalences, so that they apply to any relation, whether it is the instance `LE` of its type or
not.
-/

@[expose] public section

namespace Sic

-- ADE: `IsPreorder`, of the standard library of Agda, in `Tools/Relation.agda`.
/-- The relation `r` is a preorder: reflexive and transitive.
RFC: `\mathsf{preorder}_l`, `\mathsf{preorder}_\kappa` -/
structure IsPreorder {α : Type} (r : α → α → Prop) : Prop where
  /-- The relation is reflexive. -/
  refl : ∀ a, r a a
  /-- The relation is transitive. -/
  trans : ∀ {a b c}, r a b → r b c → r a c

-- ADE: none.
/-- `j` is the least upper bound of `a` and `b` for the relation `r`: it is above both, and below
every element above both.
RFC: `{\sqcup}{\le}_s`, `{\sqcup}{\preceq}_\kappa` -/
structure IsLeastUpperBound {α : Type} (r : α → α → Prop) (a b j : α) : Prop where
  /-- `j` is above `a`. -/
  le_left : r a j
  /-- `j` is above `b`. -/
  le_right : r b j
  /-- `j` is below every element above `a` and `b`. -/
  least : ∀ c, r a c → r b c → r j c

end Sic
