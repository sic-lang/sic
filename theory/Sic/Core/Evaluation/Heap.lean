module

public import Sic.Core.Evaluation

/-!
# Heap

The extension of the heaps of annex 17 of RFC 36: the evaluation only allocates, at the end of the
heap, and never changes a value, so that a heap at a later point of a run extends the heap at an
earlier point, `H ⊑ H'`, which keeps the value at each address of `H`.
The relation of run time of the erasure relates a term to an address in a heap, and the values that
it reads at the addresses of `H` stay in each heap that extends `H`.

ADE run their target language by reduction, without heap, so that they have no extension.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- `H ⊑ H'`: the heap `H'` extends the heap `H`, with the same value at each address of `H`, as
the list `H` is a prefix of `H'`.
RFC: `\sqsubseteq_H` -/
abbrev Heap.Extends (H H' : Heap) : Prop := H <+: H'

-- ADE: none.
/-- A heap that extends `H` has the value of `H` at each address of `H`.
RFC: `\sqsubseteq_H.\mathsf{get}` -/
theorem Heap.Extends.getElem? {H H' : Heap} {a : Nat} {v : Value} (h : H.Extends H')
    (ha : H[a]? = some v) : H'[a]? = some v := by
  obtain ⟨_, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1, ha]

/-- The resumption of a value extends the heap. -/
theorem EvalResume.extends {H H' : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
    {o : Resumption} {w v : Nat} : EvalResume H n E Ps o w v H' → H.Extends H'
  | .none | .done _ _ => List.prefix_refl _
  | .next _ _ | .erased _ => List.prefix_append _ _

mutual

-- ADE: none.
/-- The evaluation extends the heap: it allocates new values and changes none.
RFC: `\mathsf{ext}_\Downarrow` -/
theorem Eval.extends {P : Program} {n : Nat} {H H' : Heap} {E : List Nat} {M : Target n}
    {a : Nat} : Eval P H E M a H' → H.Extends H'
  | .var _ => List.prefix_refl _
  | .const _ hM => hM.extends
  | .erased => List.prefix_append _ _
  | .ctor hs => hs.extends.trans (List.prefix_append _ _)
  | .recursor h hr => h.extends.trans hr.extends
  | .obs h hs ho => h.extends.trans (hs.extends.trans ho.extends)
  | .corec hs => hs.extends.trans (List.prefix_append _ _)

/-- The evaluation of terms extends the heap. -/
theorem EvalAll.extends {P : Program} {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n}
    {as : List Nat} : EvalAll P H E Ms as H' → H.Extends H'
  | .nil => List.prefix_refl _
  | .cons h hs => h.extends.trans hs.extends

/-- The elimination of a value by a recursor extends the heap. -/
theorem EvalRec.extends {P : Program} {n : Nat} {H H' : Heap} {E : List Nat}
    {Ns : TargetBranches n} {a v : Nat} : EvalRec P H E Ns a v H' → H.Extends H'
  | .iota _ _ _ hr hv => hr.extends.trans hv.extends

/-- The evaluation of the recursive results of a branch extends the heap. -/
theorem EvalResults.extends {P : Program} {n : Nat} {H H' : Heap} {E : List Nat}
    {Ns : TargetBranches n} {as : List Nat} {ks : List (Option Nat)} {rs : List Nat} :
    EvalResults P H E Ns as ks rs H' → H.Extends H'
  | .nil => List.prefix_refl _
  | .erased hs => (List.prefix_append _ _).trans hs.extends
  | .recursor _ h hs => h.extends.trans hs.extends

/-- The observation of a value extends the heap. -/
theorem EvalObs.extends {P : Program} {H H' : Heap} {a i : Nat} {bs : List Nat} {v : Nat} :
    EvalObs P H a i bs v H' → H.Extends H'
  | .beta _ _ _ _ hw hr => hw.extends.trans hr.extends

end

end Sic.Core
