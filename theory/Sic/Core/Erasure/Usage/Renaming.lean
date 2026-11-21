module

public import Sic.Core.Erasure.Renaming
public import Sic.Core.Erasure.Usage

/-!
# Usage of the Renamed Terms of the Target Language

The usage of the target language of `Sic/Core/Erasure/Usage.lean` is kept by the renamings of its
variables: a term renamed by `α` reads each of its new variables as the variables that `α` sends to
it read, `α_* ν`, the sum of their multiplicities, which the representation of the variables by de
Bruijn indices needs, since the RFC names its variables.

ADE prove that the usage is kept by the weakenings, `wkUsage`, in `Graded/Usage/Weakening.agda`, for
the terms of their type theory, whose target language has no usage.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `wkConₘ`, in `Graded/Context/Weakening.agda`.
/-- `α_* ν`: the multiplicities of the variables renamed by `α`, each variable reading as the sum
of the multiplicities of the variables that `α` sends to it, `0` for none. -/
def _root_.Sic.Grading.MultiplicityVector.rename {n m : Nat} (α : TargetRen n m)
    (ν : MultiplicityVector m) : MultiplicityVector n :=
  fun y => Multiplicity.sum fun x => if α x = y then ν x else .zero

namespace MultiplicityVector

-- ADE: `wk-𝟘ᶜ`, in `Graded/Context/Weakening.agda`.
/-- The zero vector renamed is the zero vector. -/
theorem rename_zero {n m : Nat} (α : TargetRen n m) :
    MultiplicityVector.rename α (𝟘ᵛ : MultiplicityVector m) = 𝟘ᵛ :=
  funext fun _ => by
    simp only [MultiplicityVector.rename, Sic.Math.Vector.zero, ite_self]
    exact Multiplicity.sum_zero

-- ADE: `wk-+ᶜ`, in `Graded/Context/Weakening.agda`.
/-- The sum of two vectors renamed is the sum of their renamings. -/
theorem rename_add {n m : Nat} (α : TargetRen n m) (ν₁ ν₂ : MultiplicityVector m) :
    MultiplicityVector.rename α (ν₁ +ᶜ ν₂) =
      MultiplicityVector.rename α ν₁ +ᶜ MultiplicityVector.rename α ν₂ :=
  funext fun y => by
    simp only [MultiplicityVector.rename, Sic.Math.Vector.add]
    rw [← Multiplicity.sum_add]
    congr 1
    funext x
    split
    · rfl
    · rfl

-- ADE: `wk-·ᶜ`, in `Graded/Context/Weakening.agda`.
/-- A vector multiplied by `π` renamed is its renaming multiplied by `π`. -/
theorem rename_smul {n m : Nat} (α : TargetRen n m) (π : Multiplicity) (ν : MultiplicityVector m) :
    MultiplicityVector.rename α (π ·ᶜ ν) = π ·ᶜ MultiplicityVector.rename α ν :=
  funext fun y => by
    simp only [MultiplicityVector.rename, Sic.Math.Vector.smul]
    rw [← Multiplicity.sum_mul]
    congr 1
    funext x
    split
    · rfl
    · cases π <;> rfl

-- ADE: `wk-≤ᶜ`, in `Graded/Context/Weakening.agda`.
/-- The renaming keeps the order. -/
theorem rename_le {n m : Nat} (α : TargetRen n m) {ν₁ ν₂ : MultiplicityVector m} (h : ν₁ ≤ᶜ ν₂) :
    MultiplicityVector.rename α ν₁ ≤ᶜ MultiplicityVector.rename α ν₂ := fun _ =>
  Multiplicity.sum_le fun x => by
    split
    · exact h x
    · exact Multiplicity.le_refl' _

-- ADE: `wk-,≔`, in `Graded/Context/Weakening.agda`.
/-- The vector of one read of `x` renamed is the vector of one read of `α x`. -/
theorem rename_update {n m : Nat} (α : TargetRen n m) (x : Fin m) :
    MultiplicityVector.rename α (MultiplicityVector.update 𝟘ᵛ x .one) =
      MultiplicityVector.update 𝟘ᵛ (α x) .one :=
  funext fun y => by
    simp only [MultiplicityVector.rename]
    rw [Multiplicity.sum_single _ x fun j hj => by
      simp only [Sic.Math.Vector.update, Sic.Math.Vector.zero, hj, ↓reduceIte, ite_self]]
    simp only [Sic.Math.Vector.update, Sic.Math.Vector.zero, ↓reduceIte]
    by_cases h : α x = y
    · simp [h]
    · simp [h, Ne.symm h]

-- ADE: none.
/-- The vector of a branch at a variable of the scope, shifted under the binders of the branch, is
the vector of the scope at this variable. -/
theorem extendBinders_shift {m a b : Nat} (φ : MultiplicityVector m) (πs : Fin a → Multiplicity)
    (πs' : Fin b → Multiplicity) (x : Fin m) :
    φ.extendBinders πs πs' (TargetRen.shift m (a + b) x) = φ x := by
  have h₁ : ¬ ((x : Nat) + (a + b) < b) := by omega
  have h₂ : ¬ ((x : Nat) + (a + b) < a + b) := by omega
  simp only [MultiplicityVector.extendBinders, TargetRen.shift, h₁, h₂, ↓reduceDIte,
    Nat.add_sub_cancel, Fin.eta]

-- ADE: none.
/-- The vector of a branch renamed under its new variables is the vector of the scope renamed,
extended by the multiplicities of the new variables. -/
theorem rename_extendBinders {n m a b : Nat} (α : TargetRen n m) (δ : MultiplicityVector m)
    (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity) :
    MultiplicityVector.rename (α.lift (a + b)) (δ.extendBinders πs πs') =
      (MultiplicityVector.rename α δ).extendBinders πs πs' :=
  funext fun i => by
    by_cases hi : (i : Nat) < a + b
    · -- A new variable is the image of itself only.
      have hR : (MultiplicityVector.rename α δ).extendBinders πs πs' i =
          δ.extendBinders πs πs' ⟨i, by omega⟩ := by
        simp only [MultiplicityVector.extendBinders, hi]
        by_cases hb : (i : Nat) < b <;> simp [hb]
      rw [hR, MultiplicityVector.rename, Multiplicity.sum_single _ ⟨i, by omega⟩ fun j hj => by
        have : TargetRen.lift α (a + b) j ≠ i := by
          intro e
          apply hj
          apply Fin.ext
          have := congrArg Fin.val e
          rw [TargetRen.lift_val] at this
          show (j : Nat) = i
          split at this <;> omega
        simp only [this, ↓reduceIte]]
      have hl : TargetRen.lift α (a + b) ⟨i, by omega⟩ = i := by
        apply Fin.ext
        rw [TargetRen.lift_val]
        simp [hi]
      simp only [hl, ↓reduceIte]
    · -- A variable of the scope is the image of the variables of the scope that `α` sends to it.
      have hR : (MultiplicityVector.rename α δ).extendBinders πs πs' i =
          MultiplicityVector.rename α δ ⟨i - (a + b), by omega⟩ := by
        simp only [MultiplicityVector.extendBinders, show ¬ (i : Nat) < b by omega, hi,
          ↓reduceDIte]
      rw [hR, MultiplicityVector.rename, MultiplicityVector.rename,
        Multiplicity.sum_addNat (a + b) _ fun j hj => by
          have : TargetRen.lift α (a + b) j ≠ i := by
            intro e
            have := congrArg Fin.val e
            rw [TargetRen.lift_val] at this
            simp only [hj, ↓reduceDIte] at this
            omega
          simp only [this, ↓reduceIte]]
      congr 1
      funext x
      have hx : δ.extendBinders πs πs' (x.addNat (a + b)) = δ x := by
        simp only [MultiplicityVector.extendBinders, Fin.val_addNat,
          show ¬ ((x : Nat) + (a + b) < b) by omega, show ¬ ((x : Nat) + (a + b) < a + b) by omega,
          ↓reduceDIte, Nat.add_sub_cancel]
      have hl : (TargetRen.lift α (a + b) (x.addNat (a + b)) : Nat) = (α x : Nat) + (a + b) := by
        rw [TargetRen.lift_val]
        simp only [Fin.val_addNat, show ¬ ((x : Nat) + (a + b) < a + b) by omega, ↓reduceDIte,
          Nat.add_sub_cancel]
      rw [hx]
      by_cases h : α x = ⟨(i : Nat) - (a + b), by omega⟩
      · have : TargetRen.lift α (a + b) (x.addNat (a + b)) = i := by
          apply Fin.ext
          rw [hl, h]
          simp only
          omega
        simp [h, this]
      · have : TargetRen.lift α (a + b) (x.addNat (a + b)) ≠ i := by
          intro e
          apply h
          apply Fin.ext
          have := congrArg Fin.val e
          rw [hl] at this
          simp only
          omega
        simp [h, this]

end MultiplicityVector

/-! ## Renaming -/

mutual

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/-- A term renamed by `α` reads its variables as `α_* ν`. -/
theorem Target.Usage.rename {n m : Nat} (α : TargetRen n m) :
    {ν : MultiplicityVector m} → {M : Target m} → Target.Usage ν M →
      Target.Usage (MultiplicityVector.rename α ν) (M.rename α)
  | _, _, .var x => by
    rw [MultiplicityVector.rename_update]
    exact .var _
  | _, _, .const .. => by
    rw [MultiplicityVector.rename_zero]
    exact .const ..
  | _, _, .erased => by
    rw [MultiplicityVector.rename_zero]
    exact .erased
  | _, _, .ctor hMs => .ctor (hMs.rename α)
  | _, _, .recursor hM hz hNs => by
    rw [MultiplicityVector.rename_add, MultiplicityVector.rename_smul]
    exact .recursor (hM.rename α) (fun h => (hz h).rename α) (hNs.rename α)
  | _, _, .obs hM hMs => by
    rw [MultiplicityVector.rename_add]
    exact .obs (hM.rename α) (hMs.rename α)
  | _, _, .corec hMs hPs => by
    rw [MultiplicityVector.rename_add]
    exact .corec (hMs.rename α) (hPs.rename α)
  | _, _, .sub h hle => .sub (h.rename α) (MultiplicityVector.rename_le α hle)

-- ADE: none.
/-- Terms renamed by `α` read their variables as `α_* ν`. -/
theorem Targets.Usage.rename {n m : Nat} (α : TargetRen n m) :
    {ν : MultiplicityVector m} → {Ms : Targets m} → Targets.Usage ν Ms →
      Targets.Usage (MultiplicityVector.rename α ν) (Ms.rename α)
  | _, _, .nil => by
    rw [MultiplicityVector.rename_zero]
    exact .nil
  | _, _, .cons hM hz hMs => by
    rw [MultiplicityVector.rename_add, MultiplicityVector.rename_smul]
    exact .cons (hM.rename α) (fun h => (hz h).rename α) (hMs.rename α)

-- ADE: none.
/-- The branches of a recursor renamed by `α` read the variables of the scope as `α_* χ`. -/
theorem TargetBranches.Usage.rename {n m : Nat} (α : TargetRen n m) :
    {ρ : Multiplicity} → {χ : MultiplicityVector m} → {Ns : TargetBranches m} →
      TargetBranches.Usage ρ χ Ns →
        TargetBranches.Usage ρ (MultiplicityVector.rename α χ) (Ns.rename α)
  | _, _, _, .nil => .nil
  | _, _, _, .cons (δ := δ) (πs := πs) (πs' := πs') hN hχ hk hσ hNs => by
    have hN' := hN.rename (α.lift _)
    rw [MultiplicityVector.rename_extendBinders] at hN'
    refine .cons hN' ?_ hk hσ (hNs.rename α)
    have h := MultiplicityVector.rename_le α hχ
    rwa [MultiplicityVector.rename_add, MultiplicityVector.rename_smul] at h

-- ADE: none.
/-- The branches of a corecursor renamed by `α` read the variables of the scope as `α_* δ`. -/
theorem TargetDestructorBranches.Usage.rename {n m : Nat} (α : TargetRen n m) :
    {δ : MultiplicityVector m} → {Ps : TargetDestructorBranches m} →
    TargetDestructorBranches.Usage δ Ps →
      TargetDestructorBranches.Usage (MultiplicityVector.rename α δ) (Ps.rename α)
  | _, _, .nil => .nil
  | _, _, .cons hP hδ hr hPs => by
    have hP' := hP.rename (α.lift _)
    rw [MultiplicityVector.rename_extendBinders] at hP'
    refine .cons hP' (MultiplicityVector.rename_le α hδ) (fun ho => ?_) (hPs.rename α)
    have h := MultiplicityVector.rename_le α (hr ho)
    rwa [MultiplicityVector.rename_add] at h

end

end Sic.Core
