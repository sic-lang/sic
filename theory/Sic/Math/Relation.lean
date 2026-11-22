module

/-!
# Relations

Properties of the relations that Lean does not provide: an element accessible for a relation is not
above itself by its transitive closure, so that a path down from it never comes back to it.

ADE have no counterpart of this property: the standard library of Agda gives it in two steps, the
accessibility for the transitive closure (`accessible`, in
`Relation/Binary/Construct/Closure/Transitive.agda`) and the asymmetry of the relation at an
accessible element (`acc⇒asym`, in `Induction/WellFounded.agda`, which ADE import), but ADE do not
state it.
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
