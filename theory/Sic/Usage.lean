module

/-!
# Usages

The usages of RFC 24, the components of the grades: a usage counts the uses of a variable, as the
linear modality of ADE, whose laws are proved here.
-/

@[expose] public section

namespace Sic

/-- The meet, written as in Mathlib, on which this package does not depend. -/
infixl:69 " ⊓ " => min

/-- A number of uses: none, exactly one, or any number, none included. -/
inductive Usage where
  | zero
  | one
  | omega
  deriving DecidableEq

namespace Usage

instance : Add Usage where
  add
    | zero, u | u, zero => u
    | _, _ => omega

instance : Mul Usage where
  mul
    | zero, _ | _, zero => zero
    | one, u | u, one => u
    | omega, omega => omega

instance : Min Usage where
  min u v := if u = v then u else omega

/-- The order of ADE: a variable of usage `u` may be used where the usage `v` is expected. -/
instance : LE Usage where
  le u v := u = u ⊓ v

instance (u v : Usage) : Decidable (u ≤ v) := inferInstanceAs (Decidable (u = u ⊓ v))

/-- Decides a statement on every usage by checking each one, so that `decide` proves the laws. -/
instance {P : Usage → Prop} [DecidablePred P] : Decidable (∀ u, P u) :=
  decidable_of_iff (P zero ∧ P one ∧ P omega)
    ⟨fun ⟨h₀, h₁, h₂⟩ u => by cases u <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-! The laws of a modality, on each usage. -/

theorem add_assoc : ∀ u v w : Usage, (u + v) + w = u + (v + w) := by decide
theorem add_comm : ∀ u v : Usage, u + v = v + u := by decide
theorem zero_add : ∀ u : Usage, zero + u = u := by decide
theorem add_zero : ∀ u : Usage, u + zero = u := by decide
theorem mul_assoc : ∀ u v w : Usage, (u * v) * w = u * (v * w) := by decide
theorem one_mul : ∀ u : Usage, one * u = u := by decide
theorem mul_one : ∀ u : Usage, u * one = u := by decide
theorem zero_mul : ∀ u : Usage, zero * u = zero := by decide
theorem mul_zero : ∀ u : Usage, u * zero = zero := by decide
theorem mul_add : ∀ u v w : Usage, u * (v + w) = (u * v) + (u * w) := by decide
theorem add_mul : ∀ u v w : Usage, (u + v) * w = (u * w) + (v * w) := by decide
theorem min_assoc : ∀ u v w : Usage, (u ⊓ v) ⊓ w = u ⊓ (v ⊓ w) := by decide
theorem min_comm : ∀ u v : Usage, u ⊓ v = v ⊓ u := by decide
theorem min_self : ∀ u : Usage, u ⊓ u = u := by decide
theorem mul_min : ∀ u v w : Usage, u * (v ⊓ w) = (u * v) ⊓ (u * w) := by decide
theorem min_mul : ∀ u v w : Usage, (u ⊓ v) * w = (u * w) ⊓ (v * w) := by decide
theorem add_min : ∀ u v w : Usage, u + (v ⊓ w) = (u + v) ⊓ (u + w) := by decide
theorem min_add : ∀ u v w : Usage, (u ⊓ v) + w = (u + w) ⊓ (v + w) := by decide

/-!
The order: a partial order whose meet is `⊓` and whose least element is `ω`, under which the
operations are monotone.
-/

theorem le_refl : ∀ u : Usage, u ≤ u := by decide
theorem le_trans : ∀ u v w : Usage, u ≤ v → v ≤ w → u ≤ w := by decide
theorem le_antisymm : ∀ u v : Usage, u ≤ v → v ≤ u → u = v := by decide
theorem min_le_left : ∀ u v : Usage, u ⊓ v ≤ u := by decide
theorem min_le_right : ∀ u v : Usage, u ⊓ v ≤ v := by decide
theorem le_min : ∀ u v w : Usage, w ≤ u → w ≤ v → w ≤ u ⊓ v := by decide
theorem omega_le : ∀ u : Usage, omega ≤ u := by decide
theorem add_le_add : ∀ u u' v v' : Usage, u ≤ u' → v ≤ v' → u + v ≤ u' + v' := by decide
theorem mul_le_mul : ∀ u u' v v' : Usage, u ≤ u' → v ≤ v' → u * v ≤ u' * v' := by decide
theorem min_le_min : ∀ u u' v v' : Usage, u ≤ u' → v ≤ v' → u ⊓ v ≤ u' ⊓ v' := by decide

/-! The zero is well behaved. -/

theorem add_eq_zero : ∀ {u v : Usage}, u + v = zero → u = zero ∧ v = zero := by decide
theorem mul_eq_zero : ∀ {u v : Usage}, u * v = zero → u = zero ∨ v = zero := by decide
theorem min_eq_zero : ∀ {u v : Usage}, u ⊓ v = zero → u = zero ∧ v = zero := by decide

end Usage

end Sic
