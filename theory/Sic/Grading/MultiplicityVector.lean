module

public import Sic.Grading.GradeVector

/-!
# Vectors of Multiplicities

The vectors of multiplicities of annex 10 of RFC 36, one multiplicity for each variable of a term of
the target language: the vectors of `Sic/Math/Vector.lean` whose elements are multiplicities, whose
operations, order and laws are those of the vectors at the modality of the multiplicities,
`Multiplicity.modality`, and the projection of a vector of grades on its multiplicities at run time.
ADE have no such projection, since their erasure keeps no count of the uses.
-/

@[expose] public section

namespace Sic.Grading

-- ADE: none.
/-- A vector of multiplicities over `n` variables, which gives each variable its multiplicity.
RFC: `\mathsf{vector}_\nu` -/
abbrev MultiplicityVector (n : Nat) : Type := Sic.Math.Vector Multiplicity n

-- ADE: none.
/-- `0^ν`, the zero vector of multiplicities, whose components are all the multiplicity `0`.
RFC: `\mathsf{zero}_\nu` -/
notation "𝟘ᵛ" => Sic.Math.Vector.zero Multiplicity.zero

/-! The operations and the laws of the vectors that the target language names, under the name of
the vectors of multiplicities, so that only this module names the vectors. -/
namespace MultiplicityVector

export Sic.Math.Vector (add add_le_add extend module smul update zero)

/-! ## Properties -/

/-- The zero vector is a unit of the addition. -/
theorem zero_add {n : Nat} (ν : MultiplicityVector n) : 𝟘ᵛ +ᶜ ν = ν :=
  (MultiplicityVector.module Multiplicity.modality).zero_add ν

/-- The order is reflexive. -/
theorem le_refl {n : Nat} (ν : MultiplicityVector n) : ν ≤ᶜ ν :=
  (Sic.Math.Vector.preorder Multiplicity.modality).refl ν

/-- Two equal vectors are ordered. -/
theorem le_of_eq {n : Nat} {ν₁ ν₂ : MultiplicityVector n} (h : ν₁ = ν₂) : ν₁ ≤ᶜ ν₂ :=
  h ▸ le_refl ν₁

/-- The order is transitive. -/
theorem le_trans {n : Nat} {ν₁ ν₂ ν₃ : MultiplicityVector n} (h₁ : ν₁ ≤ᶜ ν₂) (h₂ : ν₂ ≤ᶜ ν₃) :
    ν₁ ≤ᶜ ν₃ :=
  (Sic.Math.Vector.preorder Multiplicity.modality).trans h₁ h₂

/-- The addition is monotone. -/
theorem add_le_add' {n : Nat} {ν₁ ν₂ μ₁ μ₂ : MultiplicityVector n} (hν : ν₁ ≤ᶜ ν₂)
    (hμ : μ₁ ≤ᶜ μ₂) : ν₁ +ᶜ μ₁ ≤ᶜ ν₂ +ᶜ μ₂ :=
  Sic.Math.Vector.add_le_add Multiplicity.modality hν hμ

/-- A vector transported along an equality of sizes gives each index the element of its
transported index. -/
theorem cast_apply {n n' : Nat} (h : n = n') (ν : MultiplicityVector n) (i : Fin n') :
    (h ▸ ν) i = ν (i.cast h.symm) := by
  subst h
  rfl

end MultiplicityVector

namespace GradeVector

-- ADE: none.
/-- `run(γ)`: the vector of the run-time multiplicities of the grades of `γ`.
RFC: `\mathsf{run}_\gamma` -/
def run {n : Nat} (γ : GradeVector n) : MultiplicityVector n := fun x => (γ x).run

-- ADE: none.
/-- The projection of the vectors on their multiplicities at run time commutes with their operations
and keeps their order, as the projection of the grades does. -/
structure RunCommutes : Prop where
  /-- The zero vector of grades has the zero vector of multiplicities.
  RFC: `\mathsf{run}_\gamma.{00}` -/
  run_zero : ∀ n, run (𝟘ᶜ : GradeVector n) = 𝟘ᵛ
  /-- The projection of a sum is the sum of the projections.
  RFC: `\mathsf{run}_\gamma.{+}` -/
  run_add : ∀ {n} (γ δ : GradeVector n), run (γ +ᶜ δ) = γ.run +ᶜ δ.run
  /-- The projection of a vector multiplied by a grade is the projection multiplied by its
  multiplicity at run time.
  RFC: `\mathsf{run}_\gamma.{\cdot}` -/
  run_smul : ∀ {n} (p : Grade) (γ : GradeVector n), run (p ·ᶜ γ) = p.run ·ᶜ γ.run
  /-- The projection keeps the order.
  RFC: `\mathsf{run}_\gamma.{\le}` -/
  run_le : ∀ {n} {γ δ : GradeVector n}, γ ≤ᶜ δ → γ.run ≤ᶜ δ.run
  /-- The projection of an update is the update of the projection.
  RFC: `\mathsf{run}_\gamma.\mathsf{update}` -/
  run_update : ∀ {n} (γ : GradeVector n) (x : Fin n) (p : Grade),
    run (update γ x p) = update γ.run x p.run
  /-- The projection of an extension is the extension of the projection.
  RFC: `\mathsf{run}_\gamma.{\bullet}` -/
  run_extend : ∀ {n} (γ : GradeVector n) (p : Grade), run (γ ∙ p) = γ.run ∙ p.run

-- ADE: none.
/-- The projection of the vectors on their multiplicities at run time commutes with their operations
and keeps their order.
RFC: `\mathsf{run}_\gamma.{00}`
RFC: `\mathsf{run}_\gamma.{+}`
RFC: `\mathsf{run}_\gamma.{\cdot}`
RFC: `\mathsf{run}_\gamma.{\le}`
RFC: `\mathsf{run}_\gamma.\mathsf{update}`
RFC: `\mathsf{run}_\gamma.{\bullet}` -/
theorem run_commutes : RunCommutes where
  run_zero _ := rfl
  run_add _ _ := rfl
  run_smul _ _ := rfl
  run_le h x := (Grade.le_iff _ _).1 (h x) |>.1
  run_update γ x p := funext fun y => by
    simp only [run, update]
    split <;> rfl
  run_extend γ p := funext fun y => by
    cases y using Fin.cases <;> rfl

end GradeVector

end Sic.Grading
