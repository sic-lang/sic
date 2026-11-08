module

/-!
# Modalities

The laws of a modality, which the multiplicities and the grades satisfy alike, and those of the
modules over them, which the vectors of grades satisfy, as records whose fields are the laws, so
that each law is stated once and named, and each kind of objects proves that it satisfies them; the
laws that follow from those of a modality are theorems on its record, which every modality gets.
ADE state the laws of the modalities as the fields of their record `Modality`, in
`Graded/Modality.agda`.
-/

@[expose] public section

namespace Sic

/-- The meet, written as in Mathlib, on which this package does not depend. -/
infixl:69 " ⊓ " => min

-- ADE: the field `+-·-Semiring` of `Modality`, in `Graded/Modality.agda`.
/-- The addition and the multiplication of `α` form a semiring, whose zero is `zero` and whose unit
is `one`. -/
structure IsSemiring (α : Type) [Add α] [Mul α] (zero one : α) : Prop where
  /-- The addition is associative. -/
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  /-- The addition is commutative. -/
  add_comm : ∀ a b : α, a + b = b + a
  /-- The zero is neutral for the addition. -/
  zero_add : ∀ a : α, zero + a = a
  /-- The multiplication is associative. -/
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  /-- The unit is neutral on the left of the multiplication. -/
  one_mul : ∀ a : α, one * a = a
  /-- The unit is neutral on the right of the multiplication. -/
  mul_one : ∀ a : α, a * one = a
  /-- The zero is absorbing on the left of the multiplication. -/
  zero_mul : ∀ a : α, zero * a = zero
  /-- The zero is absorbing on the right of the multiplication. -/
  mul_zero : ∀ a : α, a * zero = zero

-- ADE: the field `∧-Semilattice` of `Modality`, in `Graded/Modality.agda`.
/-- The meet of `α` is associative, commutative and idempotent. -/
structure IsMeetSemilattice (α : Type) [Min α] : Prop where
  /-- The meet is associative. -/
  meet_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  /-- The meet is commutative. -/
  meet_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  /-- The meet is idempotent. -/
  meet_idem : ∀ a : α, a ⊓ a = a

-- ADE: `_DistributesOver_`, of the standard library of Agda, in `Tools/Algebra.agda`, which the
-- fields `·-distrib-∧` and `+-distrib-∧` of `Modality` use, in `Graded/Modality.agda`.
/-- The operation `mul` of `α` distributes over its operation `add`, on both sides. -/
structure DistributesOver {α : Type} (mul add : α → α → α) : Prop where
  /-- `mul` distributes on the left. -/
  left : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  /-- `mul` distributes on the right. -/
  right : ∀ a b c : α, mul (add b c) a = add (mul b a) (mul c a)

-- ADE: `IsLeftSemimodule`, of the standard library of Agda, in `Tools/Algebra.agda`.
/-- The addition `addV` and the multiplication `smulV` by the elements of `R` make `V` a module over
the semiring `R`, whose zero is `zero` and whose unit is `one`, the zero of `V` being `zeroV`.
The operations of `V` are parameters, as the relation of `IsPreorder`, so that the record applies to
operations that are not the instances of `V`. -/
structure IsModule (R V : Type) [Add R] [Mul R] (zero one : R)
    (zeroV : V) (addV : V → V → V) (smulV : R → V → V) : Prop where
  /-- The addition is associative.
  RFC: `\mathsf{module}_\gamma.\mathsf{assoc}_{+}` -/
  add_assoc : ∀ a b c : V, addV (addV a b) c = addV a (addV b c)
  /-- The addition is commutative.
  RFC: `\mathsf{module}_\gamma.\mathsf{comm}_{+}` -/
  add_comm : ∀ a b : V, addV a b = addV b a
  /-- The zero is neutral for the addition.
  RFC: `\mathsf{module}_\gamma.\mathsf{unit}_{+}` -/
  zero_add : ∀ a : V, addV zeroV a = a
  /-- The multiplication distributes over the addition of `V`.
  RFC: `\mathsf{module}_\gamma.\mathsf{distrib}_{+^{\gamma}}` -/
  smul_add : ∀ (p : R) (a b : V), smulV p (addV a b) = addV (smulV p a) (smulV p b)
  /-- The multiplication distributes over the addition of `R`.
  RFC: `\mathsf{module}_\gamma.\mathsf{distrib}_{+}` -/
  add_smul : ∀ (p q : R) (a : V), smulV (p + q) a = addV (smulV p a) (smulV q a)
  /-- The multiplication by a product is the multiplication by each of its factors.
  RFC: `\mathsf{module}_\gamma.\mathsf{assoc}_{\cdot}` -/
  mul_smul : ∀ (p q : R) (a : V), smulV (p * q) a = smulV p (smulV q a)
  /-- The unit of `R` is neutral for the multiplication.
  RFC: `\mathsf{module}_\gamma.\mathsf{unit}_{\cdot}` -/
  one_smul : ∀ a : V, smulV one a = a
  /-- The zero of `R` multiplies every element into the zero of `V`.
  RFC: `\mathsf{module}_\gamma.\mathsf{lzero}_{\cdot}` -/
  zero_smul : ∀ a : V, smulV zero a = zeroV
  /-- Every element of `R` multiplies the zero of `V` into itself.
  RFC: `\mathsf{module}_\gamma.\mathsf{rzero}_{\cdot}` -/
  smul_zero : ∀ p : R, smulV p zeroV = zeroV

-- ADE: `Has-well-behaved-zero`, in `Graded/Modality.agda`.
/-- The zero of `α` is well behaved: it differs from the unit `one`, and a sum, a meet or a product
is zero only when its operands are. -/
structure HasWellBehavedZero (α : Type) [Add α] [Mul α] [Min α] (zero one : α) : Prop where
  /-- The zero is not the unit. -/
  zero_ne_one : zero ≠ one
  /-- A sum is zero only when its operands are. -/
  add_eq_zero : ∀ a b : α, a + b = zero → a = zero ∧ b = zero
  /-- A meet is zero only when its operands are. -/
  meet_eq_zero : ∀ a b : α, a ⊓ b = zero → a = zero ∧ b = zero
  /-- A product is zero only when one of its operands is. -/
  mul_eq_zero : ∀ a b : α, a * b = zero → a = zero ∨ b = zero

/-- The order of a meet, `a ≤ b` when `a = a ⊓ b`, as in ADE, which the multiplicities and the grades
take as their order. -/
def order {α : Type} [Min α] (a b : α) : Prop :=
  a = a ⊓ b

-- ADE: `Modality`, in `Graded/Modality.agda`.
/-- `α` is a modality, whose zero is `zero` and whose unit is `one`: a semiring whose addition and
multiplication distribute over its meet, with a well-behaved zero. -/
structure IsModality (α : Type) [Add α] [Mul α] [Min α] (zero one : α) : Prop where
  /-- The addition and the multiplication form a semiring. -/
  semiring : IsSemiring α zero one
  /-- The meet is associative, commutative and idempotent. -/
  meet : IsMeetSemilattice α
  /-- The multiplication distributes over the addition. -/
  mul_add : DistributesOver (α := α) (· * ·) (· + ·)
  /-- The multiplication distributes over the meet. -/
  mul_meet : DistributesOver (α := α) (· * ·) (· ⊓ ·)
  /-- The addition distributes over the meet. -/
  add_meet : DistributesOver (α := α) (· + ·) (· ⊓ ·)
  /-- The zero is well behaved. -/
  zero : HasWellBehavedZero α zero one

namespace IsModality

variable {α : Type} [Add α] [Mul α] [Min α] {zero one : α}

/-- The addition is monotone. -/
theorem add_le (h : IsModality α zero one) (a b c : α) (hab : order a b) :
    order (a + c) (b + c) := by
  unfold order at *
  rw [← h.add_meet.right c a b, ← hab]

/-- The meet is the greatest lower bound of two elements. -/
theorem le_meet_iff (h : IsModality α zero one) (a b c : α) :
    order c a ∧ order c b ↔ order c (a ⊓ b) := by
  unfold order
  constructor
  · intro ⟨ha, hb⟩
    rw [← h.meet.meet_assoc, ← ha, ← hb]
  · intro hab
    constructor
    · rw [hab, h.meet.meet_assoc, h.meet.meet_comm a b, h.meet.meet_assoc, h.meet.meet_idem]
    · rw [hab, h.meet.meet_assoc, h.meet.meet_assoc, h.meet.meet_idem]

end IsModality

end Sic
