module

public import Sic.Grade

/-!
# Modes

The modes of RFC 24, the settings in which the usage of a term is checked, each named after its
grade, with which a variable checked in the mode uses itself.
They form a mode structure of ADE, whose laws are proved at the end.

ADE defines its modes abstractly, as any type with the structure `IsMode`, and instantiates them
with its two modes `𝟘ᵐ` and `𝟙ᵐ`; the modes here are concrete, three, and the laws that ADE adds
for its natural numbers are absent, since the core has none.
-/

@[expose] public section

namespace Sic

-- ADE: `Mode`, in `Graded/Mode.agda`.
/-- A mode, named after its grade. -/
inductive Mode where
  /-- `𝟘𝟘ᵐ`: no use is counted. -/
  | zeroZero
  /-- `𝟘𝟙ᵐ`: all the uses are counted, none at run time. -/
  | zeroOne
  /-- `𝟙𝟙ᵐ`: all the uses are counted, and the uses at run time. -/
  | oneOne
  deriving DecidableEq

namespace Mode

@[inherit_doc] scoped notation "𝟘𝟘ᵐ" => Mode.zeroZero
@[inherit_doc] scoped notation "𝟘𝟙ᵐ" => Mode.zeroOne
@[inherit_doc] scoped notation "𝟙𝟙ᵐ" => Mode.oneOne

-- ADE: `⌜_⌝`, in `Graded/Mode.agda`.
/-- `⌜m⌝`: the grade with which a variable checked in the mode `m` uses itself. -/
def grade : Mode → Grade
  | zeroZero => .zero
  | zeroOne => ⟨.zero, .one, fun h => nomatch h⟩
  | oneOne => .one

@[inherit_doc] scoped notation "⌜" m "⌝" => Mode.grade m

end Mode

open Grade Mode

-- ADE: `⌞_⌟`, in `Graded/Mode.agda`.
/--
`⌞p⌟`: the mode in which a term used with the grade `p` is checked: `𝟘𝟘ᵐ` for `𝟘`, `𝟘𝟙ᵐ` for the
other grades without use at run time, and `𝟙𝟙ᵐ` for the grades used at run time.
-/
def Grade.mode (p : Grade) : Mode :=
  if p = 𝟘 then 𝟘𝟘ᵐ else if p.run = .zero then 𝟘𝟙ᵐ else 𝟙𝟙ᵐ

namespace Mode

@[inherit_doc] scoped notation "⌞" p "⌟" => Grade.mode p

-- ADE: `_·ᵐ_`, in `Graded/Mode.agda`.
/-- The product of two modes, the mode of the product of their grades: the more erased of the two. -/
instance : Mul Mode where
  mul m₁ m₂ := ⌞⌜m₁⌝ * ⌜m₂⌝⌟

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/--
`m ⊙ p`: the mode in which a subterm used with the grade `p` is checked, inside a term checked in
the mode `m`, written as in the paper of ADE.
-/
def scale (m : Mode) (p : Grade) : Mode := m * ⌞p⌟

@[inherit_doc] scoped infixl:70 " ⊙ " => Mode.scale

/-- Decides a statement on every mode by checking each one, so that `decide` proves the laws. -/
instance {P : Mode → Prop} [DecidablePred P] : Decidable (∀ m, P m) :=
  decidable_of_iff (P zeroZero ∧ P zeroOne ∧ P oneOne)
    ⟨fun ⟨h₀, h₁, h₂⟩ m => by cases m <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-!
The laws of the structure `IsMode` of ADE, in its order, on each mode and each grade. ADE orders the
modes by `m ≤ᵐ m′` when `m′ = m′ ·ᵐ m`, the more erased being the greater, which the last two laws
unfold.
-/

-- ADE: `·ᵐ-IdempotentCommutativeMonoid`, in `Graded/Mode.agda`.
theorem mul_assoc : ∀ m₁ m₂ m₃ : Mode, (m₁ * m₂) * m₃ = m₁ * (m₂ * m₃) := by decide
-- ADE: `·ᵐ-IdempotentCommutativeMonoid`, in `Graded/Mode.agda`.
theorem mul_comm : ∀ m₁ m₂ : Mode, m₁ * m₂ = m₂ * m₁ := by decide
-- ADE: `·ᵐ-IdempotentCommutativeMonoid`, in `Graded/Mode.agda`.
theorem mul_self : ∀ m : Mode, m * m = m := by decide
-- ADE: `·ᵐ-IdempotentCommutativeMonoid`, in `Graded/Mode.agda`.
theorem one_mul : ∀ m : Mode, 𝟙𝟙ᵐ * m = m := by decide
-- ADE: `·ᵐ-IdempotentCommutativeMonoid`, in `Graded/Mode.agda`.
theorem mul_one : ∀ m : Mode, m * 𝟙𝟙ᵐ = m := by decide
-- ADE: `·ᵐ-zero`, in `Graded/Mode.agda`.
theorem zero_mul : ∀ m : Mode, 𝟘𝟘ᵐ * m = 𝟘𝟘ᵐ := by decide
-- ADE: `·ᵐ-zero`, in `Graded/Mode.agda`.
theorem mul_zero : ∀ m : Mode, m * 𝟘𝟘ᵐ = 𝟘𝟘ᵐ := by decide
-- ADE: `⌞⌜⌝⌟`, in `Graded/Mode.agda`.
theorem mode_grade : ∀ m : Mode, ⌞⌜m⌝⌟ = m := by decide
-- ADE: `⌜·ᵐ⌝`, in `Graded/Mode.agda`.
theorem grade_mul : ∀ m₁ m₂ : Mode, ⌜m₁ * m₂⌝ = ⌜m₁⌝ * ⌜m₂⌝ := by decide
-- ADE: `⌞⌟·ᵐ`, in `Graded/Mode.agda`.
theorem mode_mul : ∀ p q : Grade, ⌞p⌟ * ⌞q⌟ = ⌞p * q⌟ := by decide
-- ADE: `·⌜⌞⌟⌝`, in `Graded/Mode.agda`.
theorem mul_grade_mode : ∀ p : Grade, p * ⌜⌞p⌟⌝ = p := by decide
-- ADE: `⌜⌞⌟⌝·`, in `Graded/Mode.agda`.
theorem grade_mode_mul : ∀ p : Grade, ⌜⌞p⌟⌝ * p = p := by decide
-- ADE: `≤⌜⌝·`, in `Graded/Mode.agda`.
theorem le_grade_mul : ∀ (m : Mode) (p q : Grade), p ≤ q → q ≤ ⌜m⌝ * q → p ≤ ⌜m⌝ * p := by
  decide
-- ADE: `⌜𝟘ᵐ⌝`, in `Graded/Mode.agda`.
theorem grade_zeroZero : ⌜𝟘𝟘ᵐ⌝ = 𝟘 := rfl
-- ADE: `⌞+⌟-decreasingˡ`, in `Graded/Mode.agda`.
theorem mode_add_left : ∀ p q : Grade, ⌞p⌟ = ⌞p⌟ * ⌞p + q⌟ := by decide
-- ADE: `⌞∧⌟-decreasingˡ`, in `Graded/Mode.agda`.
theorem mode_min_left : ∀ p q : Grade, ⌞p⌟ = ⌞p⌟ * ⌞p ⊓ q⌟ := by decide

/-! The laws that the substitution of the usage uses to move a usage from a mode to another. -/

-- ADE: `·-idem-⌜⌝`, in `Graded/Mode.agda`.
theorem grade_mul_self : ∀ m : Mode, ⌜m⌝ * ⌜m⌝ = ⌜m⌝ := by decide
-- ADE: `⌜⌝-·-comm`, in `Graded/Mode.agda`.
theorem grade_mul_comm : ∀ (m : Mode) (p : Grade), ⌜m⌝ * p = p * ⌜m⌝ := by decide
-- ADE: `·⌜ᵐ·⌝`, in `Graded/Mode.agda`.
theorem mul_grade_scale : ∀ (m : Mode) (p : Grade), p * ⌜m ⊙ p⌝ = p * ⌜m⌝ := by decide
-- ADE: `⌞⌜⌝·⌟`, in `Graded/Mode.agda`.
theorem mode_grade_mul : ∀ (m : Mode) (p : Grade), ⌞⌜m⌝ * p⌟ = m ⊙ p := by decide
-- ADE: `⌞⌟-monotone`, in `Graded/Mode.agda`.
theorem mode_le : ∀ p q : Grade, p ≤ q → ⌞q⌟ = ⌞q⌟ * ⌞p⌟ := by decide
-- ADE: `⌞+⌟-decreasingʳ`, in `Graded/Mode.agda`.
theorem mode_add_right : ∀ p q : Grade, ⌞q⌟ = ⌞q⌟ * ⌞p + q⌟ := by decide

end Mode

end Sic
