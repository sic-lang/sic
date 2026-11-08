module

/-!
# Modalities

The laws that the multiplicities and the grades satisfy alike, and those of the modules over them,
which the vectors of grades satisfy, as records whose fields are the laws, so that each law is
stated once and named, and each kind of objects proves that it satisfies them.
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
  /-- The addition is associative.
  RFC: `\mathsf{semiring}_\pi.\mathsf{assoc}_{+}`, `\mathsf{semiring}_p.\mathsf{assoc}_{+}` -/
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  /-- The addition is commutative.
  RFC: `\mathsf{semiring}_\pi.\mathsf{comm}_{+}`, `\mathsf{semiring}_p.\mathsf{comm}_{+}` -/
  add_comm : ∀ a b : α, a + b = b + a
  /-- The zero is neutral for the addition.
  RFC: `\mathsf{semiring}_\pi.\mathsf{unit}_{+}`, `\mathsf{semiring}_p.\mathsf{unit}_{+}` -/
  zero_add : ∀ a : α, zero + a = a
  /-- The multiplication is associative.
  RFC: `\mathsf{semiring}_\pi.\mathsf{assoc}_{\cdot}`
  RFC: `\mathsf{semiring}_p.\mathsf{assoc}_{\cdot}` -/
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  /-- The unit is neutral on the left of the multiplication.
  RFC: `\mathsf{semiring}_\pi.\mathsf{lunit}_{\cdot}`
  RFC: `\mathsf{semiring}_p.\mathsf{lunit}_{\cdot}` -/
  one_mul : ∀ a : α, one * a = a
  /-- The unit is neutral on the right of the multiplication.
  RFC: `\mathsf{semiring}_\pi.\mathsf{runit}_{\cdot}`
  RFC: `\mathsf{semiring}_p.\mathsf{runit}_{\cdot}` -/
  mul_one : ∀ a : α, a * one = a
  /-- The zero is absorbing on the left of the multiplication.
  RFC: `\mathsf{semiring}_\pi.\mathsf{lzero}_{\cdot}`
  RFC: `\mathsf{semiring}_p.\mathsf{lzero}_{\cdot}` -/
  zero_mul : ∀ a : α, zero * a = zero
  /-- The zero is absorbing on the right of the multiplication.
  RFC: `\mathsf{semiring}_\pi.\mathsf{rzero}_{\cdot}`
  RFC: `\mathsf{semiring}_p.\mathsf{rzero}_{\cdot}` -/
  mul_zero : ∀ a : α, a * zero = zero

-- ADE: the field `∧-Semilattice` of `Modality`, in `Graded/Modality.agda`.
/-- The meet of `α` is associative, commutative and idempotent. -/
structure IsMeetSemilattice (α : Type) [Min α] : Prop where
  /-- The meet is associative.
  RFC: `\mathsf{meet}_\pi.\mathsf{assoc}`, `\mathsf{meet}_p.\mathsf{assoc}` -/
  meet_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  /-- The meet is commutative.
  RFC: `\mathsf{meet}_\pi.\mathsf{comm}`, `\mathsf{meet}_p.\mathsf{comm}` -/
  meet_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  /-- The meet is idempotent.
  RFC: `\mathsf{meet}_\pi.\mathsf{idem}`, `\mathsf{meet}_p.\mathsf{idem}` -/
  meet_idem : ∀ a : α, a ⊓ a = a

-- ADE: `_DistributesOver_`, of the standard library of Agda, in `Tools/Algebra.agda`, which the
-- fields `·-distrib-∧` and `+-distrib-∧` of `Modality` use, in `Graded/Modality.agda`.
/-- The operation `mul` of `α` distributes over its operation `add`, on both sides. -/
structure DistributesOver {α : Type} (mul add : α → α → α) : Prop where
  /-- `mul` distributes on the left.
  RFC: `{\cdot}{+}_\pi.\mathsf{left}`, `{\cdot}{\wedge}_\pi.\mathsf{left}`
  RFC: `{+}{\wedge}_\pi.\mathsf{left}`, `{\cdot}{+}_p.\mathsf{left}`
  RFC: `{\cdot}{\wedge}_p.\mathsf{left}`, `{+}{\wedge}_p.\mathsf{left}` -/
  left : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  /-- `mul` distributes on the right.
  RFC: `{\cdot}{+}_\pi.\mathsf{right}`, `{\cdot}{\wedge}_\pi.\mathsf{right}`
  RFC: `{+}{\wedge}_\pi.\mathsf{right}`, `{\cdot}{+}_p.\mathsf{right}`
  RFC: `{\cdot}{\wedge}_p.\mathsf{right}`, `{+}{\wedge}_p.\mathsf{right}` -/
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
  /-- The zero is not the unit.
  RFC: `0_\pi.1`, `0_p.1` -/
  zero_ne_one : zero ≠ one
  /-- A sum is zero only when its operands are.
  RFC: `0_\pi.{+}`, `0_p.{+}` -/
  add_eq_zero : ∀ a b : α, a + b = zero → a = zero ∧ b = zero
  /-- A meet is zero only when its operands are.
  RFC: `0_\pi.{\wedge}`, `0_p.{\wedge}` -/
  meet_eq_zero : ∀ a b : α, a ⊓ b = zero → a = zero ∧ b = zero
  /-- A product is zero only when one of its operands is.
  RFC: `0_\pi.{\cdot}`, `0_p.{\cdot}` -/
  mul_eq_zero : ∀ a b : α, a * b = zero → a = zero ∨ b = zero

end Sic
