module

/-!
# Multiplicities

The multiplicities of RFC 24, the components of the grades: a multiplicity counts the uses of a
variable, as the linear modality of ADE, whose laws are proved here.
-/

@[expose] public section

namespace Sic

/-- The meet, written as in Mathlib, on which this package does not depend. -/
infixl:69 " ⊓ " => min

/-- A number of uses. -/
inductive Multiplicity where
  /-- `0`: no use. -/
  | zero
  /-- `1`: exactly one use. -/
  | one
  /-- `ω`: any number of uses, none included. -/
  | omega
  deriving DecidableEq

namespace Multiplicity

instance : Add Multiplicity where
  add
    | zero, u | u, zero => u
    | _, _ => omega

instance : Mul Multiplicity where
  mul
    | zero, _ | _, zero => zero
    | one, u | u, one => u
    | omega, omega => omega

instance : Min Multiplicity where
  min u v := if u = v then u else omega

/--
The order of ADE: a variable of multiplicity `u` may be used where the multiplicity `v` is expected.
-/
instance : LE Multiplicity where
  le u v := u = u ⊓ v

instance (u v : Multiplicity) : Decidable (u ≤ v) := inferInstanceAs (Decidable (u = u ⊓ v))

/--
Decides a statement on every multiplicity by checking each one, so that `decide` proves the laws.
-/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∀ u, P u) :=
  decidable_of_iff (P zero ∧ P one ∧ P omega)
    ⟨fun ⟨h₀, h₁, h₂⟩ u => by cases u <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-! The laws of a modality, on each multiplicity. -/

theorem add_assoc : ∀ u v w : Multiplicity, (u + v) + w = u + (v + w) := by decide
theorem add_comm : ∀ u v : Multiplicity, u + v = v + u := by decide
theorem zero_add : ∀ u : Multiplicity, zero + u = u := by decide
theorem add_zero : ∀ u : Multiplicity, u + zero = u := by decide
theorem mul_assoc : ∀ u v w : Multiplicity, (u * v) * w = u * (v * w) := by decide
theorem one_mul : ∀ u : Multiplicity, one * u = u := by decide
theorem mul_one : ∀ u : Multiplicity, u * one = u := by decide
theorem zero_mul : ∀ u : Multiplicity, zero * u = zero := by decide
theorem mul_zero : ∀ u : Multiplicity, u * zero = zero := by decide
theorem mul_add : ∀ u v w : Multiplicity, u * (v + w) = (u * v) + (u * w) := by decide
theorem add_mul : ∀ u v w : Multiplicity, (u + v) * w = (u * w) + (v * w) := by decide
theorem min_assoc : ∀ u v w : Multiplicity, (u ⊓ v) ⊓ w = u ⊓ (v ⊓ w) := by decide
theorem min_comm : ∀ u v : Multiplicity, u ⊓ v = v ⊓ u := by decide
theorem min_self : ∀ u : Multiplicity, u ⊓ u = u := by decide
theorem mul_min : ∀ u v w : Multiplicity, u * (v ⊓ w) = (u * v) ⊓ (u * w) := by decide
theorem min_mul : ∀ u v w : Multiplicity, (u ⊓ v) * w = (u * w) ⊓ (v * w) := by decide
theorem add_min : ∀ u v w : Multiplicity, u + (v ⊓ w) = (u + v) ⊓ (u + w) := by decide
theorem min_add : ∀ u v w : Multiplicity, (u ⊓ v) + w = (u + w) ⊓ (v + w) := by decide

/-!
The order: a partial order whose meet is `⊓` and whose least element is `ω`, under which the
operations are monotone.
-/

theorem le_refl : ∀ u : Multiplicity, u ≤ u := by decide
theorem le_trans : ∀ u v w : Multiplicity, u ≤ v → v ≤ w → u ≤ w := by decide
theorem le_antisymm : ∀ u v : Multiplicity, u ≤ v → v ≤ u → u = v := by decide
theorem min_le_left : ∀ u v : Multiplicity, u ⊓ v ≤ u := by decide
theorem min_le_right : ∀ u v : Multiplicity, u ⊓ v ≤ v := by decide
theorem le_min : ∀ u v w : Multiplicity, w ≤ u → w ≤ v → w ≤ u ⊓ v := by decide
theorem omega_le : ∀ u : Multiplicity, omega ≤ u := by decide
theorem add_le_add : ∀ u u' v v' : Multiplicity, u ≤ u' → v ≤ v' → u + v ≤ u' + v' := by decide
theorem mul_le_mul : ∀ u u' v v' : Multiplicity, u ≤ u' → v ≤ v' → u * v ≤ u' * v' := by decide
theorem min_le_min : ∀ u u' v v' : Multiplicity, u ≤ u' → v ≤ v' → u ⊓ v ≤ u' ⊓ v' := by decide

/-! The zero is well behaved. -/

theorem add_eq_zero : ∀ {u v : Multiplicity}, u + v = zero → u = zero ∧ v = zero := by decide
theorem mul_eq_zero : ∀ {u v : Multiplicity}, u * v = zero → u = zero ∨ v = zero := by decide
theorem min_eq_zero : ∀ {u v : Multiplicity}, u ⊓ v = zero → u = zero ∧ v = zero := by decide

end Multiplicity

end Sic
