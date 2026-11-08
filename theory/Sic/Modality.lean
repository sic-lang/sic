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
is `one`.
RFC: `\mathsf{semiring}_\pi`, `\mathsf{semiring}_p` -/
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
/-- The meet of `α` is associative, commutative and idempotent.
RFC: `\mathsf{meet}_\pi`, `\mathsf{meet}_p` -/
structure IsMeetSemilattice (α : Type) [Min α] : Prop where
  /-- The meet is associative. -/
  meet_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  /-- The meet is commutative. -/
  meet_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  /-- The meet is idempotent. -/
  meet_idem : ∀ a : α, a ⊓ a = a

-- ADE: `IsLeftSemimodule`, of the standard library of Agda, in `Tools/Algebra.agda`.
/-- The addition `addV` and the multiplication `smulV` by the elements of `R` make `V` a module over
the semiring `R`, whose zero is `zero` and whose unit is `one`, the zero of `V` being `zeroV`.
The operations of `V` are parameters, as the relation of `IsPreorder`, so that the record applies to
operations that are not the instances of `V`.
RFC: `\mathsf{module}_\gamma` -/
structure IsModule (R V : Type) [Add R] [Mul R] (zero one : R)
    (zeroV : V) (addV : V → V → V) (smulV : R → V → V) : Prop where
  /-- The addition is associative. -/
  add_assoc : ∀ a b c : V, addV (addV a b) c = addV a (addV b c)
  /-- The addition is commutative. -/
  add_comm : ∀ a b : V, addV a b = addV b a
  /-- The zero is neutral for the addition. -/
  zero_add : ∀ a : V, addV zeroV a = a
  /-- The multiplication distributes over the addition of `V`. -/
  smul_add : ∀ (p : R) (a b : V), smulV p (addV a b) = addV (smulV p a) (smulV p b)
  /-- The multiplication distributes over the addition of `R`. -/
  add_smul : ∀ (p q : R) (a : V), smulV (p + q) a = addV (smulV p a) (smulV q a)
  /-- The multiplication by a product is the multiplication by each of its factors. -/
  mul_smul : ∀ (p q : R) (a : V), smulV (p * q) a = smulV p (smulV q a)
  /-- The unit of `R` is neutral for the multiplication. -/
  one_smul : ∀ a : V, smulV one a = a
  /-- The zero of `R` multiplies every element into the zero of `V`. -/
  zero_smul : ∀ a : V, smulV zero a = zeroV
  /-- Every element of `R` multiplies the zero of `V` into itself. -/
  smul_zero : ∀ p : R, smulV p zeroV = zeroV

-- ADE: `Has-well-behaved-zero`, in `Graded/Modality.agda`.
/-- The zero of `α` is well behaved: it differs from the unit `one`, and a sum, a meet or a product
is zero only when its operands are.
RFC: `0_\pi`, `0_p` -/
structure HasWellBehavedZero (α : Type) [Add α] [Mul α] [Min α] (zero one : α) : Prop where
  /-- The zero is not the unit. -/
  zero_ne_one : zero ≠ one
  /-- A sum is zero only when its operands are. -/
  add_eq_zero : ∀ a b : α, a + b = zero → a = zero ∧ b = zero
  /-- A meet is zero only when its operands are. -/
  meet_eq_zero : ∀ a b : α, a ⊓ b = zero → a = zero ∧ b = zero
  /-- A product is zero only when one of its operands is. -/
  mul_eq_zero : ∀ a b : α, a * b = zero → a = zero ∨ b = zero

end Sic
