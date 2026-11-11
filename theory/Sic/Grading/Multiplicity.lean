module

public import Sic.Math.Modality

/-!
# Multiplicities

The multiplicities of annex 03 of RFC 36: a multiplicity counts the uses of a variable, and is `0`,
`1` or `ω`.
They are the linear modality of ADE, whose laws are proved here, with the cases of the RFC as the
definitions of the operations; their meaning, the numbers of uses, is in `Sic/Grading/Meaning/`.
The meet is written `⊓`, since `∧` is the conjunction of Lean.
-/

@[expose] public section

namespace Sic.Grading

open Sic.Math

-- ADE: `Linearity`, in `Graded/Modality/Instances/Linearity.agda`.
/-- A multiplicity, which counts the uses of a variable.
RFC: `\mathsf{syntax}_\pi` -/
inductive Multiplicity where
  /-- `0`: no use. -/
  | zero
  /-- `1`: one use. -/
  | one
  /-- `ω`: any number of uses, none included. -/
  | omega
  deriving DecidableEq

namespace Multiplicity

/-- The addition of the multiplicities.
RFC: `\mathsf{op}_\pi.{+}` -/
def add : Multiplicity → Multiplicity → Multiplicity
  | zero, π | π, zero => π
  | _, _ => omega

/-- The multiplication of the multiplicities.
RFC: `\mathsf{op}_\pi.{\cdot}` -/
def mul : Multiplicity → Multiplicity → Multiplicity
  | zero, _ | _, zero => zero
  | one, π | π, one => π
  | omega, omega => omega

instance : Add Multiplicity := ⟨add⟩

instance : Mul Multiplicity := ⟨mul⟩

theorem add_def (π₁ π₂ : Multiplicity) : π₁ + π₂ = add π₁ π₂ := rfl

theorem mul_def (π₁ π₂ : Multiplicity) : π₁ * π₂ = mul π₁ π₂ := rfl

/-- The meet of two multiplicities.
RFC: `\mathsf{op}_\pi.{\wedge}` -/
def meet : Multiplicity → Multiplicity → Multiplicity
  | zero, zero => zero
  | one, one => one
  | _, _ => omega

instance : Min Multiplicity := ⟨meet⟩

theorem meet_def (π₁ π₂ : Multiplicity) : π₁ ⊓ π₂ = meet π₁ π₂ := rfl

/-- The order of the multiplicities, `π₁ ≤ π₂` when `π₁ = π₁ ⊓ π₂`, as in ADE. -/
instance : LE Multiplicity where
  le := order

instance (π₁ π₂ : Multiplicity) : Decidable (π₁ ≤ π₂) :=
  inferInstanceAs (Decidable (π₁ = π₁ ⊓ π₂))

/-- Decides a statement on all the multiplicities by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∀ π, P π) :=
  decidable_of_iff (P zero ∧ P one ∧ P omega)
    ⟨fun ⟨h₀, h₁, h₂⟩ π => by cases π <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-- Decides a statement on some multiplicity by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∃ π, P π) :=
  decidable_of_iff (P zero ∨ P one ∨ P omega)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
      fun ⟨π, h⟩ => by cases π <;> simp_all⟩

/-! The tables of the RFC, row by row, in the order `0`, `1`, `ω`. -/

/-- The table of the addition, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{+}` -/
theorem add_table :
    [[zero + zero, zero + one, zero + omega],
    [one + zero, one + one, one + omega],
    [omega + zero, omega + one, omega + omega]] =
    [[zero, one, omega], [one, omega, omega], [omega, omega, omega]] := by
  decide

/-- The table of the multiplication, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{\cdot}` -/
theorem mul_table :
    [[zero * zero, zero * one, zero * omega],
    [one * zero, one * one, one * omega],
    [omega * zero, omega * one, omega * omega]] =
    [[zero, zero, zero], [zero, one, omega], [zero, omega, omega]] := by
  decide

/-- The table of the meet, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{\wedge}` -/
theorem meet_table :
    [[zero ⊓ zero, zero ⊓ one, zero ⊓ omega],
    [one ⊓ zero, one ⊓ one, one ⊓ omega],
    [omega ⊓ zero, omega ⊓ one, omega ⊓ omega]] =
    [[zero, omega, omega], [omega, one, omega], [omega, omega, omega]] := by
  decide

/-- `ω` is below `0` and below `1`, while `0` and `1` are not comparable.
RFC: `\mathsf{compare}_\pi` -/
theorem order_table :
    omega ≤ zero ∧ omega ≤ one ∧ ¬ zero ≤ one ∧ ¬ one ≤ zero := by
  decide


/-! ## Properties

The multiplicities form a modality of ADE: a semiring whose addition and multiplication distribute
over its meet, ordered by its meet, with a well-behaved zero. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
/-- The multiplicities form a modality.
RFC: `\mathsf{modality}_\pi` -/
theorem modality : IsModality Multiplicity zero one where
  semiring := {
    add_assoc := by decide
    add_comm := by decide
    zero_add := by decide
    mul_assoc := by decide
    one_mul := by decide
    mul_one := by decide
    zero_mul := by decide
    mul_zero := by decide }
  meet := {
    meet_assoc := by decide
    meet_comm := by decide
    meet_idem := by decide }
  mul_add := { left := by decide, right := by decide }
  mul_meet := { left := by decide, right := by decide }
  add_meet := { left := by decide, right := by decide }
  zero := {
    zero_ne_one := by decide
    add_eq_zero := by decide
    meet_eq_zero := by decide
    mul_eq_zero := by decide }

theorem le_antisymm : ∀ π₁ π₂ : Multiplicity, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁ = π₂ := by decide

end Multiplicity

end Sic.Grading
