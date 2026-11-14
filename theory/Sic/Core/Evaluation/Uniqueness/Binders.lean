module

public import Sic.Core.Evaluation.Claims
public import Sic.Core.Evaluation.Conservation.Positions
import Sic.Core.Evaluation.Conservation.Demands
import Sic.Core.Evaluation.Uniqueness.Positions

/-!
# Binders

The reach and the claims of the binders of a branch, for the proof of the invariant of the
uniqueness at run time: what the unpacking of a value gives of its reach and of its claims, and
what a term claims through the cells that the evaluation binds for a branch.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The value that packs a state refers to what its entries refer to, each as the references of the
multiplicity at which the pack stores it. -/
theorem Unpack.reach {g : Heap.Annotation} : {H : Heap} → {k x : Nat} →
    {πs ϱs : List Multiplicity} → {ss : List Nat} → Unpack H k x πs ϱs ss → {U : Demand} →
      Heap.ValueReach H g x U → ∃ Ss Z, List.Pointwise (Heap.ValueReach H g) ss Ss ∧
        U = Demand.positions (πs.map Multiplicity.references) Ss +ᶜ Z
  | _, _, _, _, _, _, .zero _, U, _ => ⟨[], U, .nil, (Demand.zero_add U).symm⟩
  | _, _, _, _, _, _, .pair (x := x) (π' := π') (πs := πs) h hs, _, hU => by
    obtain ⟨Us, hUs, rfl, -⟩ := hU.ctor_inv h
    obtain _ | ⟨hy, hUs⟩ := hUs
    obtain _ | ⟨hz, hUs⟩ := hUs
    cases hUs
    obtain ⟨Ss, Z, hSs, rfl⟩ := hs.reach hz
    refine ⟨_ :: Ss, Demand.unit x +ᶜ π'.references ·ᶜ Z, .cons hy hSs, ?_⟩
    simp only [List.map_cons, List.map_nil, Demand.positions, Multiplicity.map_references_mul,
      Demand.positions_map_mul, Demand.add_zero, Demand.smul_add]
    ac_rfl

/-- The value that packs a state claims what each entry that the pack stores at the requirement `1`
and at a multiplicity other than `0` claims. -/
theorem Unpack.claims {g : Heap.Annotation} {b : Nat} : {H : Heap} → {k x : Nat} →
    {πs ϱs : List Multiplicity} → {ss : List Nat} → Unpack H k x πs ϱs ss → {j s : Nat} →
      {π : Multiplicity} → ss[j]? = some s → πs[j]? = some π → π ≠ .zero →
      ϱs[j]? = some Multiplicity.one → Heap.Claims H g s b → Heap.Claims H g x b
  | _, _, _, _, _, _, .zero _, _, _, _, hs, _, _, _, _ => by simp at hs
  | _, _, _, _, _, _, .pair h _, 0, _, _, hs, hπ, hπ₀, hϱ, hb => by
    cases hs
    cases hπ
    exact .ctor h (k := 0) rfl rfl hπ₀ (by simpa using hϱ) hb
  | _, _, _, _, _, _, .pair (π' := π') (ϱ' := ϱ') h hu, j + 1, _, _, hs, hπ, hπ₀, hϱ, hb => by
    simp only [List.getElem?_cons_succ, List.getElem?_map] at hs hπ hϱ
    obtain ⟨π₃, hπ₃, rfl⟩ := Option.map_eq_some_iff.1 hπ
    obtain ⟨ϱ₃, hϱ₃, hϱe⟩ := Option.map_eq_some_iff.1 hϱ
    obtain ⟨rfl, rfl⟩ := (by decide : ∀ x y : Multiplicity, x * y = .one →
      x = .one ∧ y = .one) _ _ hϱe
    exact .ctor h (k := 1) rfl rfl
      ((by decide : ∀ x y : Multiplicity, x * y ≠ .zero → x ≠ .zero) _ _ hπ₀) rfl
      (hu.claims hs hπ₃
        ((by decide : ∀ x y : Multiplicity, x * y ≠ .zero → y ≠ .zero) _ _ hπ₀) hϱ₃ hb)

/-- What a branch claims through its environment, the cells of its `a + b` variables from the
address `c` and its scope: what the cell of a variable of a field or of a result that it owns alone
and reads claims, or what it claims through its scope. -/
theorem Heap.EnvClaims.bind_cases {H : Heap} {g : Heap.Annotation} {n a b : Nat} {E : List Nat}
    {c : Nat} {φ ν : MultiplicityVector n} {φs πs : Fin a → Multiplicity}
    {φs' πs' : Fin b → Multiplicity} {b' : Nat}
    (h : Heap.EnvClaims H g ((List.range' c (a + b)).reverse ++ E) (φ.extendBinders φs φs')
      (ν.extendBinders πs πs') b') :
    (∃ l : Fin a, φs l = .one ∧ πs l ≠ .zero ∧ Heap.Claims H g (c + l) b') ∨
      (∃ j : Fin b, φs' j = .one ∧ πs' j ≠ .zero ∧ Heap.Claims H g (c + (a + j)) b') ∨
      Heap.EnvClaims H g E φ ν b' := by
  obtain ⟨x, cx, hx, hφ, hν, hcl⟩ := h
  by_cases h₁ : (x : Nat) < b
  · simp only [MultiplicityVector.extendBinders, h₁, ↓reduceDIte] at hφ hν
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by simp; omega),
      List.getElem?_range' (by simp; omega)] at hx
    cases hx
    refine .inr (.inl ⟨⟨b - 1 - x, by omega⟩, hφ, hν, ?_⟩)
    have e : c + (a + (b - 1 - (x : Nat))) = c + 1 * ((List.range' c (a + b)).length - 1 - x) := by
      simp; omega
    rw [e]
    exact hcl
  · by_cases h₂ : (x : Nat) < a + b
    · simp only [MultiplicityVector.extendBinders, h₁, h₂, ↓reduceDIte] at hφ hν
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by simp; omega),
        List.getElem?_range' (by simp; omega)] at hx
      cases hx
      refine .inl ⟨⟨a - 1 - (x - b), by omega⟩, hφ, hν, ?_⟩
      have e : c + (a - 1 - ((x : Nat) - b)) =
          c + 1 * ((List.range' c (a + b)).length - 1 - x) := by
        simp; omega
      rw [e]
      exact hcl
    · simp only [MultiplicityVector.extendBinders, h₁, h₂, ↓reduceDIte] at hφ hν
      rw [List.getElem?_append_right (by simp; omega)] at hx
      simp only [List.length_reverse, List.length_range'] at hx
      exact .inr (.inr ⟨⟨x - (a + b), by omega⟩, cx, hx, hφ, hν, hcl⟩)

end Sic.Core
