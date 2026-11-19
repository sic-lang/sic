module

public import Sic.Core.Evaluation.Demand
import Sic.Core.Evaluation.Conservation.Demands

/-!
# Skeletons

The runs of the data, for the proof of the invariant of the conservation of the bindings: data
reads no cell, allocates none, and its value has the demand `0`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

mutual

-- ADE: none.
/-- Data reads no cell, allocates none, and its value has the demand `0`. -/
theorem Target.IsData.conserve {P : Program} {ϖ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {M : Target n} {a : Nat} {R : List Nat} :
    M.IsData → Eval P ϖ H E M a H' R →
      R = [] ∧ Demand.allocated H H' = 𝟘ᵛ ∧ Heap.ValueDemand H' a 𝟘ᵛ
  | .erased, h => by
    cases h
    exact ⟨rfl, Demand.allocated_append (fun _ _ h => Value.noConfusion h),
      .erased List.getElem?_concat_length⟩
  | .ctor hs, h => by
    cases h with
    | ctor hev =>
    obtain ⟨rfl, hal, hD⟩ := Targets.IsData.conserve hs hev
    refine ⟨rfl, ?_, .ctor List.getElem?_concat_length (hD.mono (List.prefix_append _ _))⟩
    rw [Demand.allocated_trans hev.extends (List.prefix_append _ _), hal,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.zero_add]

-- ADE: none.
/-- Terms that are data read no cell, allocate none, and their values have the demand `0`. -/
theorem Targets.IsData.conserve {P : Program} {ϖ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {Ms : Targets n} {as : List Nat} {R : List Nat} :
    Ms.IsData → EvalAll P ϖ H E Ms as H' R →
      R = [] ∧ Demand.allocated H H' = 𝟘ᵛ ∧ Heap.PositionsDemand H' Ms.multiplicities as 𝟘ᵛ
  | .nil, h => by
    cases h
    exact ⟨rfl, Demand.allocated_self _, .nil⟩
  | .cons (π := π) hM hMs, h => by
    cases h with
    | cons hev hevs =>
    obtain ⟨rfl, hal₁, hD₁⟩ := Target.IsData.conserve hM hev
    obtain ⟨rfl, hal₂, hD₂⟩ := Targets.IsData.conserve hMs hevs
    refine ⟨rfl, ?_, ?_⟩
    · rw [Demand.allocated_trans hev.extends hevs.extends, hal₁, hal₂, Demand.zero_add]
    · have h := Heap.PositionsDemand.cons (π := π) (hD₁.mono hevs.extends) hD₂
      rwa [Demand.smul_zero, Demand.zero_add] at h

end

end Sic.Core
