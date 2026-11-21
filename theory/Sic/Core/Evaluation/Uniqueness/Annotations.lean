module

public import Sic.Core.Evaluation.Claims

/-!
# Annotations

The annotations of the heap along a run, for the proof of the invariant of the uniqueness at run
time: the extension of an annotation is a preorder, the annotation of a new closure extends the
annotation of the heap, and an annotation stays valid when the evaluation allocates cells, values
and the closure of a corecursor whose branches have their ownership and their usage.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- An annotation extends itself. -/
theorem Heap.Annotation.Extends.refl (H : Heap) (g : Heap.Annotation) :
    Heap.Annotation.Extends H g g := fun _ _ => ⟨rfl, rfl⟩

/-- The extension of the annotations is transitive along the extension of the heaps. -/
theorem Heap.Annotation.Extends.trans {H H' : Heap} {g₁ g₂ g₃ : Heap.Annotation}
    (hH : H.Extends H') (h₁ : Heap.Annotation.Extends H g₁ g₂)
    (h₂ : Heap.Annotation.Extends H' g₂ g₃) : Heap.Annotation.Extends H g₁ g₃ := fun ℓ hℓ =>
  have hℓ' : ℓ < H'.length := Nat.lt_of_lt_of_le hℓ hH.length_le
  ⟨(h₂ ℓ hℓ').1.trans (h₁ ℓ hℓ).1, (h₂ ℓ hℓ').2.trans (h₁ ℓ hℓ).2⟩

-- ADE: none.
/-- The annotation `g` with the ownership `φ` and the usage `δ` of the scope of `n` variables of
the closure at the address `ℓ`. -/
def Heap.Annotation.set (g : Heap.Annotation) (ℓ n : Nat) (φ δ : MultiplicityVector n) :
    Heap.Annotation where
  ownership ℓ' n' := if h : ℓ' = ℓ ∧ n' = n then h.2 ▸ φ else g.ownership ℓ' n'
  usage ℓ' n' := if h : ℓ' = ℓ ∧ n' = n then h.2 ▸ δ else g.usage ℓ' n'

/-- The annotation of a closure is the one that it is given. -/
theorem Heap.Annotation.set_self (g : Heap.Annotation) (ℓ n : Nat) (φ δ : MultiplicityVector n) :
    (g.set ℓ n φ δ).ownership ℓ n = φ ∧ (g.set ℓ n φ δ).usage ℓ n = δ := by
  simp [Heap.Annotation.set]

/-- The annotation of a new closure extends the annotation of the heap before it. -/
theorem Heap.Annotation.set_extends (H : Heap) (g : Heap.Annotation) (n : Nat)
    (φ δ : MultiplicityVector n) : Heap.Annotation.Extends H g (g.set H.length n φ δ) :=
  fun ℓ hℓ => by
    have hne : ℓ ≠ H.length := Nat.ne_of_lt hℓ
    constructor <;> funext n' <;> simp [Heap.Annotation.set, hne]

/-- An annotation valid for a heap is valid for the heap with a new value that is not a closure. -/
theorem Heap.Annotation.Valid.concat {Ω : Name → Multiplicity} {H : Heap} {g : Heap.Annotation}
    (hg : g.Valid Ω H) {v : Value} (hv : ∀ n E Ps πs ϱs as, v ≠ .corec n E Ps πs ϱs as) :
    g.Valid Ω (H ++ [v]) := fun ℓ n E Ps πs ϱs as h => by
  by_cases hℓ : ℓ < H.length
  · rw [List.getElem?_append_left hℓ] at h
    exact hg ℓ n E Ps πs ϱs as h
  · have hlt := (List.getElem?_eq_some_iff.1 h).1
    obtain rfl : ℓ = H.length := by simp at hlt; omega
    rw [List.getElem?_concat_length] at h
    exact absurd (Option.some.inj h) (hv n E Ps πs ϱs as)

/-- An annotation valid for a heap, with the ownership and the usage of the branches of a new
closure, is valid for the heap with the closure. -/
theorem Heap.Annotation.Valid.concat_corec {Ω : Name → Multiplicity} {H : Heap}
    {g : Heap.Annotation} (hg : g.Valid Ω H) {n : Nat} {E : List Nat}
    {Ps : TargetCorecBranches n}
    {πs ϱs : List Multiplicity} {as : List Nat} {φ δ : MultiplicityVector n}
    (hφ : TargetCorecBranches.Ownership Ω φ Ps) (hδ : TargetCorecBranches.Usage δ Ps) :
    (g.set H.length n φ δ).Valid Ω (H ++ [.corec n E Ps πs ϱs as]) :=
  fun ℓ n' E' Ps' πs' ϱs' as' h => by
    by_cases hℓ : ℓ < H.length
    · rw [List.getElem?_append_left hℓ] at h
      rw [((Heap.Annotation.set_extends H g n φ δ) ℓ hℓ).1,
        ((Heap.Annotation.set_extends H g n φ δ) ℓ hℓ).2]
      exact hg ℓ n' E' Ps' πs' ϱs' as' h
    · have hlt := (List.getElem?_eq_some_iff.1 h).1
      obtain rfl : ℓ = H.length := by simp at hlt; omega
      rw [List.getElem?_concat_length] at h
      cases h
      rw [(Heap.Annotation.set_self g H.length n φ δ).1,
        (Heap.Annotation.set_self g H.length n φ δ).2]
      exact ⟨hφ, hδ⟩

/-- An annotation valid for a heap is valid for the heap with the cells of a binder. -/
theorem Heap.Annotation.Valid.bind {Ω : Name → Multiplicity} {H : Heap} {g : Heap.Annotation}
    (hg : g.Valid Ω H) (πs : List Multiplicity) (as : List Nat) : g.Valid Ω (H.bind πs as) :=
  fun ℓ n E Ps πs' ϱs as' h => by
    by_cases hℓ : ℓ < H.length
    · rw [Heap.bind, List.getElem?_append_left hℓ] at h
      exact hg ℓ n E Ps πs' ϱs as' h
    · rw [Heap.bind, List.getElem?_append_right (Nat.le_of_not_lt hℓ), List.getElem?_zipWith] at h
      revert h
      cases πs[ℓ - H.length]? <;> cases as[ℓ - H.length]? <;> simp

end Sic.Core
