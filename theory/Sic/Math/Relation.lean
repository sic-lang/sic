module

/-!
# Relations

Properties of the relations that Lean does not provide: an element accessible for a relation is not
above itself by its transitive closure, so that a path down from it never comes back to it.
A graph, a property of an element and of a relation, gives each element the relation that it holds
of it, which is the relation of the graph when the graph holds of one relation at most, up to the
equivalence of relations, for relations between two or three elements.

ADE have no counterpart of this property: the standard library of Agda gives it in two steps, the
accessibility for the transitive closure (`accessible`, in
`Relation/Binary/Construct/Closure/Transitive.agda`) and the asymmetry of the relation at an
accessible element (`acc⇒asym`, in `Induction/WellFounded.agda`, which ADE import), but ADE do not
state it.
-/

@[expose] public section

/-- An element accessible for a relation is not above itself by its transitive closure. -/
theorem Acc.not_transGen_self {α : Sort _} {r : α → α → Prop} {a : α} (h : Acc r a) :
    ¬ Relation.TransGen r a a := by
  have h' := h.transGen
  clear h
  induction h' with
  | intro x _ ih => exact fun hx => ih x hx hx

namespace Sic.Math

/-- The relation that the graph `P` gives `x`: the elements that some relation `S` of the graph at
`x` relates. -/
def Rel₂.ofGraph {X α β : Type} (P : X → (α → β → Prop) → Prop) : X → α → β → Prop :=
  fun x a b => ∃ S, P x S ∧ S a b

/-- The relation that the graph `P` gives `x` is a relation `S` of the graph at `x`, when the
relations of the graph at `x` are equivalent to `S`. -/
theorem Rel₂.ofGraph_eq {X α β : Type} {P : X → (α → β → Prop) → Prop} {x : X}
    {S : α → β → Prop} (h : P x S) (hP : ∀ S', P x S' → ∀ a b, S' a b ↔ S a b) :
    Rel₂.ofGraph P x = S :=
  funext fun a => funext fun b => propext
    ⟨fun ⟨_, h', hs⟩ => (hP _ h' a b).1 hs, fun hs => ⟨S, h, hs⟩⟩

/-- The relation between three elements that the graph `P` gives `x`: the elements that some
relation `S` of the graph at `x` relates. -/
def Rel₃.ofGraph {X α β γ : Type} (P : X → (α → β → γ → Prop) → Prop) :
    X → α → β → γ → Prop :=
  fun x a b c => ∃ S, P x S ∧ S a b c

/-- The relation between three elements that the graph `P` gives `x` is a relation `S` of the
graph at `x`, when the relations of the graph at `x` are equivalent to `S`. -/
theorem Rel₃.ofGraph_eq {X α β γ : Type} {P : X → (α → β → γ → Prop) → Prop} {x : X}
    {S : α → β → γ → Prop} (h : P x S) (hP : ∀ S', P x S' → ∀ a b c, S' a b c ↔ S a b c) :
    Rel₃.ofGraph P x = S :=
  funext fun a => funext fun b => funext fun c => propext
    ⟨fun ⟨_, h', hs⟩ => (hP _ h' a b c).1 hs, fun hs => ⟨S, h, hs⟩⟩

end Sic.Math
