module

public import Sic.Core.Evaluation.Demand

/-!
# Demands

The order and the operations of the demands, for the proof of the invariant of the conservation of
the bindings: the order is a preorder that the operations preserve, the sums are rearranged up to
associativity and commutativity, the cells that successive runs allocate add up, and the uses of a
trace count its reads.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

namespace Demand

/-- The order of the demands is reflexive. -/
theorem le_refl (D : Demand) : D ≤ᶜ D := fun c => Multiplicity.le_refl' (D c)

/-- The order of the demands is transitive. -/
theorem le_trans {D₁ D₂ D₃ : Demand} (h₁ : D₁ ≤ᶜ D₂) (h₂ : D₂ ≤ᶜ D₃) : D₁ ≤ᶜ D₃ :=
  fun c => Multiplicity.le_trans' _ _ _ (h₁ c) (h₂ c)

/-- Two equal demands are in order. -/
theorem le_of_eq {D₁ D₂ : Demand} (h : D₁ = D₂) : D₁ ≤ᶜ D₂ := h ▸ le_refl D₁

/-- The addition of the demands is monotone. -/
theorem add_le_add {D₁ D₂ D₃ D₄ : Demand} (h₁ : D₁ ≤ᶜ D₂) (h₂ : D₃ ≤ᶜ D₄) :
    D₁ +ᶜ D₃ ≤ᶜ D₂ +ᶜ D₄ :=
  Sic.Math.Vector.add_le_add Multiplicity.modality h₁ h₂

/-- The multiplication of a demand by a multiplicity is monotone. -/
theorem smul_le_smul (π : Multiplicity) {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) : π ·ᶜ D₁ ≤ᶜ π ·ᶜ D₂ :=
  Sic.Math.Vector.smul_le_smul Multiplicity.modality π h

/-- The addition of the demands is associative. -/
theorem add_assoc (D₁ D₂ D₃ : Demand) : D₁ +ᶜ D₂ +ᶜ D₃ = D₁ +ᶜ (D₂ +ᶜ D₃) :=
  (Sic.Math.Vector.module Multiplicity.modality).add_assoc D₁ D₂ D₃

/-- The addition of the demands is commutative. -/
theorem add_comm (D₁ D₂ : Demand) : D₁ +ᶜ D₂ = D₂ +ᶜ D₁ :=
  (Sic.Math.Vector.module Multiplicity.modality).add_comm D₁ D₂

/-- `0` is a unit of the addition of the demands. -/
theorem zero_add (D : Demand) : 𝟘ᵛ +ᶜ D = D :=
  (Sic.Math.Vector.module Multiplicity.modality).zero_add D

/-- `0` is a unit of the addition of the demands, on the right. -/
theorem add_zero (D : Demand) : D +ᶜ 𝟘ᵛ = D := by
  rw [add_comm, zero_add]

/-- The multiplication of a demand distributes over their addition. -/
theorem smul_add (π : Multiplicity) (D₁ D₂ : Demand) : π ·ᶜ (D₁ +ᶜ D₂) = π ·ᶜ D₁ +ᶜ π ·ᶜ D₂ :=
  (Sic.Math.Vector.module Multiplicity.modality).smul_add π D₁ D₂

/-- The multiplication of a demand is associative. -/
theorem mul_smul (π₁ π₂ : Multiplicity) (D : Demand) : (π₁ * π₂) ·ᶜ D = π₁ ·ᶜ (π₂ ·ᶜ D) :=
  (Sic.Math.Vector.module Multiplicity.modality).mul_smul π₁ π₂ D

/-- `0` times a demand is `0`. -/
theorem zero_smul (D : Demand) : Multiplicity.zero ·ᶜ D = 𝟘ᵛ :=
  (Sic.Math.Vector.module Multiplicity.modality).zero_smul D

/-- A multiplicity times `0` is `0`. -/
theorem smul_zero (π : Multiplicity) : π ·ᶜ (𝟘ᵛ : Demand) = 𝟘ᵛ :=
  (Sic.Math.Vector.module Multiplicity.modality).smul_zero π

/-- The demand of one read is below itself at a weight other than `0`. -/
theorem smul_unit_le {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero) (c : Nat) : ϖ ·ᶜ unit c ≤ᶜ unit c :=
  fun _ => Multiplicity.mul_le_self ϖ _ hϖ

end Demand

/-- A run that allocates nothing allocates no cell. -/
theorem Demand.allocated_self (H : Heap) : Demand.allocated H H = 𝟘ᵛ := by
  funext c
  simp only [Demand.allocated]
  split
  · rename_i h
    rw [List.getElem?_eq_none h]
    rfl
  · rfl

/-- The cells that two runs one after the other allocate are those of each. -/
theorem Demand.allocated_trans {H₁ H₂ H₃ : Heap} (h₁ : H₁.Extends H₂) (h₂ : H₂.Extends H₃) :
    Demand.allocated H₁ H₃ = Demand.allocated H₁ H₂ +ᶜ Demand.allocated H₂ H₃ := by
  funext c
  have hl₁ := h₁.length_le
  show _ = Demand.allocated H₁ H₂ c + Demand.allocated H₂ H₃ c
  simp only [Demand.allocated]
  by_cases hc₁ : H₁.length ≤ c
  · by_cases hc₂ : H₂.length ≤ c
    · rw [List.getElem?_eq_none hc₂]
      simp only [hc₁, hc₂, ↓reduceIte]
      exact (Multiplicity.modality.semiring.zero_add _).symm
    · have hc₂' : c < H₂.length := Nat.lt_of_not_le hc₂
      obtain ⟨v, hv⟩ : ∃ v, H₂[c]? = some v := ⟨_, List.getElem?_eq_getElem hc₂'⟩
      rw [h₂.getElem? hv, hv]
      simp only [hc₁, hc₂, ↓reduceIte]
      exact (Multiplicity.modality.semiring.add_comm _ _).trans
        (Multiplicity.modality.semiring.zero_add _) |>.symm
  · have hc₂ : ¬ H₂.length ≤ c := fun h => hc₁ (Nat.le_trans hl₁ h)
    simp only [hc₁, hc₂, ↓reduceIte]
    rfl

/-- A value other than a cell, allocated, allocates no cell. -/
theorem Demand.allocated_append {H : Heap} {v : Value} (hv : ∀ π a, v ≠ .cell π a) :
    Demand.allocated H (H ++ [v]) = 𝟘ᵛ := by
  funext c
  simp only [Demand.allocated]
  split
  · rename_i h
    rcases Nat.lt_or_ge c (H.length + 1) with hc | hc
    · have hc' : c = H.length := by omega
      subst hc'
      rw [List.getElem?_concat_length]
      split
      · rename_i π a h'
        cases h'
        exact (hv π a rfl).elim
      · rfl
    · rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  · rfl

instance : Std.Associative (α := Demand) (· +ᶜ ·) := ⟨Demand.add_assoc⟩

instance : Std.Commutative (α := Demand) (· +ᶜ ·) := ⟨Demand.add_comm⟩

/-- A trace without read reads no cell. -/
theorem Demand.uses_nil : Demand.uses [] = 𝟘ᵛ := rfl

/-- The weight times a sum is the sum of the weighted demands. -/
theorem Demand.smul_add₃ (ϖ : Multiplicity) (D₁ D₂ D₃ : Demand) :
    ϖ ·ᶜ (D₁ +ᶜ D₂ +ᶜ D₃) = ϖ ·ᶜ D₁ +ᶜ ϖ ·ᶜ D₂ +ᶜ ϖ ·ᶜ D₃ := by
  rw [Demand.smul_add, Demand.smul_add]

/-- A demand below another stays below it with the same demand added. -/
theorem Demand.add_le_add_right {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) (D : Demand) :
    D₁ +ᶜ D ≤ᶜ D₂ +ᶜ D :=
  Demand.add_le_add h (Demand.le_refl D)

/-- A demand below another stays below it with the same demand added on the left. -/
theorem Demand.add_le_add_left (D : Demand) {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) :
    D +ᶜ D₁ ≤ᶜ D +ᶜ D₂ :=
  Demand.add_le_add (Demand.le_refl D) h

/-- A demand below `0` at a weight stays below `0`. -/
theorem Demand.smul_le_zero {ϖ : Multiplicity} {D : Demand} (h : D ≤ᶜ 𝟘ᵛ) : ϖ ·ᶜ D ≤ᶜ 𝟘ᵛ := by
  have h' := Demand.smul_le_smul ϖ h
  rwa [Demand.smul_zero] at h'

/-- Anything plus a demand below `0` is below the thing. -/
theorem Demand.add_le_of_le_zero {D₁ D₂ : Demand} (h : D₁ ≤ᶜ 𝟘ᵛ) : D₁ +ᶜ D₂ ≤ᶜ D₂ := by
  have h' := Demand.add_le_add_right h D₂
  rwa [Demand.zero_add] at h'

/-- The order of the demands chains in a calculation. -/
instance : Trans (α := Demand) (β := Demand) (γ := Demand) (· ≤ᶜ ·) (· ≤ᶜ ·) (· ≤ᶜ ·) :=
  ⟨Demand.le_trans⟩

/-- The uses of a trace are `1` exactly when the trace reads the cell once. -/
theorem Demand.uses_eq_one {R : List Nat} {c : Nat} : Demand.uses R c = .one ↔ R.count c = 1 := by
  simp only [Demand.uses]
  split <;> simp_all

/-- The uses of a trace are `0` exactly when the trace never reads the cell. -/
theorem Demand.uses_eq_zero {R : List Nat} {c : Nat} : Demand.uses R c = .zero ↔ R.count c = 0 := by
  simp only [Demand.uses]
  split <;> simp_all

end Sic.Core
