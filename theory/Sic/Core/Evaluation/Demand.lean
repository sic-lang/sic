module

public import Sic.Core.Erasure.Usage
public import Sic.Core.Evaluation.Heap

/-!
# Demand

The demands of annex 17 of RFC 36: a demand `D` gives each address of a heap a multiplicity, the
reads of the cell at this address that remain to be done, and the uses of a trace `#R` the reads that
a run did, so that the conservation of the bindings compares them.
The demand of a value, `H ⊢ ℓ ▶ D`, bounds the reads that a use of the value can still do: `↯` and
a constructor do none of their own, a constructor passes on those of its fields, each as many times
as the multiplicity of its field, and a closure does those of its branches, which read the variables
of its scope as some `δ` of the usage allows, each read of a variable reading its cell and using its
value, and passes on those of its state, each as many times as the multiplicity of its entry.
The demand of an environment, `H ⊢ E ▶_ν D`, bounds the reads of a term that reads its variables as
`ν` allows: `ν(x)` reads of the cell of `x`, each using its value.
A value may have several demands, one for each `δ` of each closure that it reaches, so that the
properties split the demand of an environment rather than add two of them, whose choices may differ.

The demands are the functions from the addresses to the multiplicities, with the operations and the
order of the vectors of `Sic/Math/Vector.lean` at each address.
ADE have no demands: their machine updates the grades of its heap at each read, in
`Graded/Heap/Reduction.agda`, where the evaluation here records the reads and keeps its heap
immutable.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- `D`: a demand, which gives each address a multiplicity, the reads of the cell at this address
that remain to be done, the first address at `0`.
RFC: `\mathsf{demand}_D` -/
abbrev Demand : Type := Nat → Multiplicity

-- ADE: none.
/-- `[c]`: the demand of one read of the cell at the address `c`.
RFC: `\mathsf{unit}_D` -/
def Demand.unit (c : Nat) : Demand := fun c' => if c' = c then .one else .zero

-- ADE: none.
/-- `#R`: the uses of the trace `R`, which gives each address the multiplicity of the number of its
reads in `R`, `0`, `1`, or `ω` for more than one.
RFC: `\mathsf{uses}_R` -/
def Demand.uses (R : List Nat) : Demand := fun c =>
  match R.count c with
  | 0 => .zero
  | 1 => .one
  | _ => .omega

mutual

-- ADE: none.
/-- `H ⊢ ℓ ▶ D`: a use of the value at the address `ℓ` of the heap `H` reads the cells as `D`
allows. -/
inductive Heap.ValueDemand (H : Heap) : Nat → Demand → Prop where
  /-- `↯` reads no cell.
  RFC: `\mathsf{demand}_\ell.\text{↯}` -/
  | erased {ℓ : Nat} (h : H[ℓ]? = some .erased) : Heap.ValueDemand H ℓ 𝟘ᵛ
  /-- A constructor reads the cells as its fields allow, each as many times as its multiplicity.
  RFC: `\mathsf{demand}_\ell.c` -/
  | ctor {ℓ i : Nat} {πs ϱs : List Multiplicity} {as : List Nat} {D : Demand}
      (h : H[ℓ]? = some (.ctor i πs ϱs as)) (hs : Heap.PositionsDemand H πs as D) :
      Heap.ValueDemand H ℓ D
  /-- A closure reads the cells as its branches allow, which read the variables of its scope as
  `δ` allows, and as its state allows, each entry as many times as its multiplicity.
  RFC: `\mathsf{demand}_\ell.\mathsf{corec}` -/
  | corec {ℓ n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {πs ϱs : List Multiplicity}
      {as : List Nat} {δ : MultiplicityVector n} {D₁ D₂ : Demand}
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (hPs : TargetCorecBranches.Usage δ Ps)
      (hE : Heap.EnvDemand H E δ D₁) (hs : Heap.PositionsDemand H πs as D₂) :
      Heap.ValueDemand H ℓ (D₁ +ᶜ D₂)

-- ADE: none.
/-- `H ⊢ ℓ̄ ▶ π̄ ▶ D`: the values at the addresses `ℓ̄`, each used as many times as its multiplicity
in `π̄`, read the cells as `D` allows. -/
inductive Heap.PositionsDemand (H : Heap) : List Multiplicity → List Nat → Demand → Prop where
  /-- No position reads no cell.
  RFC: `\mathsf{demand}_{\bar\ell}.\varepsilon` -/
  | nil : Heap.PositionsDemand H [] [] 𝟘ᵛ
  /-- The first position, as many times as its multiplicity, and the others.
  RFC: `\mathsf{demand}_{\bar\ell}.{,}` -/
  | cons {π : Multiplicity} {πs : List Multiplicity} {ℓ : Nat} {as : List Nat} {D₁ D₂ : Demand}
      (h : Heap.ValueDemand H ℓ D₁) (hs : Heap.PositionsDemand H πs as D₂) :
      Heap.PositionsDemand H (π :: πs) (ℓ :: as) ((π ·ᶜ D₁) +ᶜ D₂)

-- ADE: none.
/-- `H ⊢ E ▶_ν D`: a term that reads the variables of the environment `E`, the last one first, as
`ν` allows, reads the cells as `D` allows: `ν(x)` reads of the cell of `x`, each using its value. -/
inductive Heap.EnvDemand (H : Heap) : {n : Nat} → List Nat → MultiplicityVector n → Demand → Prop
    where
  /-- The empty environment reads no cell.
  RFC: `\mathsf{demand}_E.\varepsilon` -/
  | nil {ν : MultiplicityVector 0} : Heap.EnvDemand H [] ν 𝟘ᵛ
  /-- The last variable, a cell of the address `c` bound to the address `ℓ`, read `ν(x)` times,
  and the others.
  RFC: `\mathsf{demand}_E.{,}` -/
  | cons {n : Nat} {c : Nat} {π : Multiplicity} {ℓ : Nat} {E : List Nat}
      {ν : MultiplicityVector (n + 1)} {D₁ D₂ : Demand} (hc : H[c]? = some (.cell π ℓ))
      (h : Heap.ValueDemand H ℓ D₁) (hE : Heap.EnvDemand H E (fun x => ν x.succ) D₂) :
      Heap.EnvDemand H (c :: E) ν ((ν 0 ·ᶜ (Demand.unit c +ᶜ D₁)) +ᶜ D₂)

end

/-! ## Properties -/

-- ADE: none.
/-- The uses of two traces joined are the sum of their uses.
RFC: `\mathsf{uses}_R.{\cdot}` -/
theorem Demand.uses_append (R₁ R₂ : List Nat) :
    Demand.uses (R₁ ++ R₂) = Demand.uses R₁ +ᶜ Demand.uses R₂ := by
  funext c
  simp only [Demand.uses, List.count_append, Sic.Math.Vector.add]
  generalize R₁.count c = k₁
  generalize R₂.count c = k₂
  rcases k₁ with _ | _ | k₁ <;> rcases k₂ with _ | _ | k₂ <;> rfl

-- ADE: none.
/-- The uses of a trace of one read are the demand of this read.
RFC: `\mathsf{uses}_R.\mathsf{unit}` -/
theorem Demand.uses_singleton (c : Nat) : Demand.uses [c] = Demand.unit c := by
  funext c'
  simp only [Demand.uses, Demand.unit, List.count_singleton, beq_iff_eq]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h, Ne.symm h]

mutual

-- ADE: none.
/-- The demand of a value holds in each heap that extends its heap.
RFC: `\mathsf{demand}_\ell.{\sqsubseteq}` -/
theorem Heap.ValueDemand.mono {H H' : Heap} (hH : H.Extends H') {ℓ : Nat} {D : Demand} :
    Heap.ValueDemand H ℓ D → Heap.ValueDemand H' ℓ D
  | .erased h => .erased (hH.getElem? h)
  | .ctor h hs => .ctor (hH.getElem? h) (hs.mono hH)
  | .corec h hPs hE hs => .corec (hH.getElem? h) hPs (hE.mono hH) (hs.mono hH)

-- ADE: none.
/-- The demand of positions holds in each heap that extends their heap. -/
theorem Heap.PositionsDemand.mono {H H' : Heap} (hH : H.Extends H') {πs : List Multiplicity}
    {as : List Nat} {D : Demand} : Heap.PositionsDemand H πs as D → Heap.PositionsDemand H' πs as D
  | .nil => .nil
  | .cons h hs => .cons (h.mono hH) (hs.mono hH)

-- ADE: none.
/-- The demand of an environment holds in each heap that extends its heap.
RFC: `\mathsf{demand}_E.{\sqsubseteq}` -/
theorem Heap.EnvDemand.mono {H H' : Heap} (hH : H.Extends H') {n : Nat} {E : List Nat}
    {ν : MultiplicityVector n} {D : Demand} : Heap.EnvDemand H E ν D → Heap.EnvDemand H' E ν D
  | .nil => .nil
  | .cons hc h hE => .cons (hH.getElem? hc) (h.mono hH) (hE.mono hH)

end

-- ADE: none.
/-- An environment that has a demand for a vector has the demand `0` for the vector `0`, whose term
reads no variable.
RFC: `\mathsf{demand}_E.0` -/
theorem Heap.EnvDemand.zero {H : Heap} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {D : Demand} : Heap.EnvDemand H E ν D →
      Heap.EnvDemand H E (𝟘ᵛ : MultiplicityVector n) (𝟘ᵛ : Demand)
  | .nil => .nil
  | .cons (c := c) (D₁ := D₁) hc h hE => by
    have h' := Heap.EnvDemand.cons (ν := 𝟘ᵛ) hc h hE.zero
    rwa [show ((𝟘ᵛ : MultiplicityVector (_ + 1)) 0 ·ᶜ (Demand.unit c +ᶜ D₁)) +ᶜ
        (𝟘ᵛ : Demand) = 𝟘ᵛ from funext fun _ => rfl] at h'

-- ADE: none.
/-- The demand of an environment for a sum of vectors splits into a demand for each, with the same
demands of the values.
RFC: `\mathsf{demand}_E.{+}` -/
theorem Heap.EnvDemand.split {H : Heap} {n : Nat} {E : List Nat} {ν₁ ν₂ : MultiplicityVector n}
    {D : Demand} : Heap.EnvDemand H E (ν₁ +ᶜ ν₂) D →
      ∃ D₁ D₂, D = D₁ +ᶜ D₂ ∧ Heap.EnvDemand H E ν₁ D₁ ∧ Heap.EnvDemand H E ν₂ D₂
  | .nil => ⟨_, _, funext fun _ => rfl, .nil, .nil⟩
  | .cons (c := c) (D₁ := D') hc h hE => by
    obtain ⟨D₁, D₂, rfl, hE₁, hE₂⟩ := Heap.EnvDemand.split (ν₁ := fun x => ν₁ x.succ)
      (ν₂ := fun x => ν₂ x.succ) hE
    refine ⟨_, _, ?_, .cons hc h hE₁, .cons hc h hE₂⟩
    funext a
    simp only [Sic.Math.Vector.add, Sic.Math.Vector.smul]
    rw [Multiplicity.modality.mul_add.right]
    generalize ν₁ 0 * (Demand.unit c a + D' a) = x₁
    generalize ν₂ 0 * (Demand.unit c a + D' a) = x₂
    have hs := Multiplicity.modality.semiring
    rw [hs.add_assoc, hs.add_assoc, ← hs.add_assoc x₂, hs.add_comm x₂ (D₁ a), hs.add_assoc]

-- ADE: none.
/-- The demand of an environment for a vector multiplied by `π` is `π` times a demand for the
vector, with the same demands of the values.
RFC: `\mathsf{demand}_E.{\cdot}` -/
theorem Heap.EnvDemand.unsmul {H : Heap} {n : Nat} {E : List Nat} {π : Multiplicity}
    {ν : MultiplicityVector n} {D : Demand} : Heap.EnvDemand H E (π ·ᶜ ν) D →
      ∃ D', D = π ·ᶜ D' ∧ Heap.EnvDemand H E ν D'
  | .nil => ⟨_, funext fun _ => (Multiplicity.modality.semiring.mul_zero π).symm, .nil⟩
  | .cons (c := c) (D₁ := D₁) hc h hE => by
    obtain ⟨D₂, rfl, hE'⟩ := Heap.EnvDemand.unsmul (ν := fun x => ν x.succ) hE
    refine ⟨_, ?_, .cons hc h hE'⟩
    funext a
    simp only [Sic.Math.Vector.add, Sic.Math.Vector.smul]
    rw [Multiplicity.modality.semiring.mul_assoc, ← Multiplicity.modality.mul_add.left]

-- ADE: none.
/-- The demand of an environment for a vector lower than another is lower than a demand for the
other, with the same demands of the values: a term given lower multiplicities than its reads is
given a lower demand than they make.
RFC: `\mathsf{demand}_E.{\le}` -/
theorem Heap.EnvDemand.le {H : Heap} : {n : Nat} → {E : List Nat} →
    {μ ν : MultiplicityVector n} → {D : Demand} → Heap.EnvDemand H E μ D → μ ≤ᶜ ν →
      ∃ D', D ≤ᶜ D' ∧ Heap.EnvDemand H E ν D'
  | _, _, _, _, _, .nil, _ => ⟨_, (Sic.Math.Vector.preorder Multiplicity.modality).refl _, .nil⟩
  | _, _, μ, ν, _, .cons (c := c) (D₁ := D₁) hc h hE, hle => by
    obtain ⟨D₂, hD, hE'⟩ := Heap.EnvDemand.le (μ := fun x => μ x.succ) (ν := fun x => ν x.succ)
      hE (fun x => hle x.succ)
    refine ⟨_, Sic.Math.Vector.add_le_add Multiplicity.modality (fun a => ?_) hD, .cons hc h hE'⟩
    show μ 0 * _ = μ 0 * _ ⊓ ν 0 * _
    rw [← Multiplicity.modality.mul_meet.right, ← hle 0]

end Sic.Core
