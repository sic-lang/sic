module

/-!
# Relations

Properties of the relations that Lean does not provide: an element accessible for a relation is not
above itself by its transitive closure, so that a path down from it never comes back to it.
-/

@[expose] public section

-- ADE: none.
/-- An element accessible for a relation is not above itself by its transitive closure. -/
theorem Acc.not_transGen_self {α : Sort _} {r : α → α → Prop} {a : α} (h : Acc r a) :
    ¬ Relation.TransGen r a a := by
  have h' := h.transGen
  clear h
  induction h' with
  | intro x _ ih => exact fun hx => ih x hx hx
