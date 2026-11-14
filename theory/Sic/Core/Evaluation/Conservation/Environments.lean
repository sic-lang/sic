module

public import Sic.Core.Evaluation.Demand
import Sic.Core.Evaluation.Conservation.Demands

/-!
# Environments

The demand of an environment, for the proof of the invariant of the conservation of the bindings:
the demand for a usage without read, and the demand of the variable that a term reads.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The sum over an environment for a vector of `0`s is `0`. -/
theorem Heap.EnvSum.eq_zero {H : Heap} {R : Nat → Demand → Prop} : {n : Nat} → {E : List Nat} →
    {ν : MultiplicityVector n} → {D : Demand} → Heap.EnvSum H R E ν D → (∀ x, ν x = .zero) →
      D = 𝟘ᵛ
  | _, _, _, _, .nil, _ => rfl
  | _, _, ν, _, .cons _ _ hE, hν => by
    rw [Heap.EnvSum.eq_zero hE fun x => hν x.succ, hν 0, Demand.zero_smul, Demand.zero_add]

/-- The sum over an environment for the vector of one read of the variable `x` is one read of its
cell, and what `R` gives its value. -/
theorem Heap.EnvSum.var_inv {H : Heap} {R : Nat → Demand → Prop} : {n : Nat} → {E : List Nat} →
    {ν : MultiplicityVector n} → {D : Demand} → Heap.EnvSum H R E ν D → (x : Fin n) →
      ν x = .one → (∀ y, y ≠ x → ν y = .zero) →
      ∃ c π ℓ Dx, E[(x : Nat)]? = some c ∧ H[c]? = some (.cell π ℓ) ∧
        R ℓ Dx ∧ D = Demand.unit c +ᶜ Dx
  | _, _, _, _, .nil, x, _, _ => x.elim0
  | _, c :: E, ν, _, .cons (D₁ := D₁) hc hv hE, x, hx, hy => by
    cases x using Fin.cases with
    | zero =>
      refine ⟨c, _, _, D₁, rfl, hc, hv, ?_⟩
      rw [Heap.EnvSum.eq_zero hE fun y => hy y.succ (Fin.succ_ne_zero y), hx,
        Demand.add_zero]
      exact (Sic.Math.Vector.module Multiplicity.modality).one_smul _
    | succ x =>
      obtain ⟨c', π, ℓ, Dx, hx', hc', hv', rfl⟩ := Heap.EnvSum.var_inv hE x hx
        fun y hyx => hy y.succ fun h => hyx (Fin.succ_inj.1 h)
      refine ⟨c', π, ℓ, Dx, hx', hc', hv', ?_⟩
      rw [hy 0 (Fin.succ_ne_zero x).symm, Demand.zero_smul, Demand.zero_add]

-- ADE: none.
/-- The demand of an environment for a vector of `0`s is `0`. -/
theorem Heap.EnvDemand.eq_zero {H : Heap} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {D : Demand} (h : Heap.EnvDemand H E ν D) (hν : ∀ x, ν x = .zero) : D = 𝟘ᵛ :=
  h.toEnvSum.eq_zero hν

-- ADE: none.
/-- The demand of an environment for the vector of one read of the variable `x` is that of one read
of its cell, and of a use of its value. -/
theorem Heap.EnvDemand.var_inv {H : Heap} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {D : Demand} (h : Heap.EnvDemand H E ν D) (x : Fin n) (hx : ν x = .one)
    (hy : ∀ y, y ≠ x → ν y = .zero) :
    ∃ c π ℓ Dx, E[(x : Nat)]? = some c ∧ H[c]? = some (.cell π ℓ) ∧
      Heap.ValueDemand H ℓ Dx ∧ D = Demand.unit c +ᶜ Dx :=
  h.toEnvSum.var_inv x hx hy

/-- A variable read at a weight other than `0` pays its demand. -/
theorem Multiplicity.var_le : ∀ ϖ e u d : Multiplicity, ϖ ≠ .zero → e ≤ u + d →
    ϖ * e + .zero ≤ u + ϖ * d := by decide

end Sic.Core
