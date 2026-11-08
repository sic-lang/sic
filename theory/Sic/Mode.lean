module

public import Sic.Grade

/-!
# Modes

The modes of annex 05 of RFC 36: a mode is the setting in which the usage of a term is checked,
named after the grade with which a variable checked in this mode uses itself.
ADE have the two modes `𝟘ᵐ` and `𝟙ᵐ`, which are `00ᵐ` and `11ᵐ` here: the mode `01ᵐ` is added so that
an erased term still counts all its uses.
-/

@[expose] public section

namespace Sic

-- ADE: `Mode`, in `Graded/Mode.agda`, which has the modes `𝟘ᵐ` and `𝟙ᵐ` only.
/--
A mode of the core.
The mode `00ᵐ` counts no use, `01ᵐ` counts all the uses, none at run time, and `11ᵐ` counts all the
uses and the uses at run time.
RFC: `\mathsf{syntax}_m`
-/
inductive Mode where
  /-- `00ᵐ`: no use. -/
  | zeroZero
  /-- `01ᵐ`: all the uses, none at run time. -/
  | zeroOne
  /-- `11ᵐ`: all the uses and the uses at run time. -/
  | oneOne
  deriving DecidableEq

-- ADE: `Mode`, in `Graded/Mode.agda`.
/--
A mode of ADE, which has two: `𝟘ᵐ` and `𝟙ᵐ`, over a modality that here is the multiplicities.
The modes of Sic project on them.
-/
inductive Multiplicity.Mode where
  /-- `𝟘ᵐ`. -/
  | zero
  /-- `𝟙ᵐ`. -/
  | one
  deriving DecidableEq

namespace Mode

/-- Decides a statement on all the modes by checking each of the three. -/
instance {P : Mode → Prop} [DecidablePred P] : Decidable (∀ m, P m) :=
  decidable_of_iff (P zeroZero ∧ P zeroOne ∧ P oneOne)
    ⟨fun ⟨h₁, h₂, h₃⟩ m => by cases m <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

-- ADE: `⌜_⌝`, in `Graded/Mode.agda`.
/-- The grade `⌜m⌝` with which a variable checked in the mode `m` uses itself.
RFC: `\mathsf{grade}_m` -/
def grade : Mode → Grade
  | zeroZero => .zero
  | zeroOne => .noneLinear
  | oneOne => .one

end Mode

namespace Grade

-- ADE: `⌞_⌟`, in `Graded/Mode.agda`.
/-- The mode `⌞p⌟` in which a term used with the grade `p` is checked: `00ᵐ` for `00ᵖ`, `01ᵐ` for the
other grades whose run-time multiplicity is `0`, those of proofs, specifications and permissions,
and `11ᵐ` for the grades used at run time.
RFC: `\mathsf{mode}_p` -/
def mode (p : Grade) : Mode :=
  match p.run, p.total with
  | .zero, .zero => .zeroZero
  | .zero, _ => .zeroOne
  | _, _ => .oneOne

end Grade

namespace Mode

-- ADE: `_·ᵐ_`, in `Graded/Mode.agda`.
/-- The product of two modes, `m₁ ·ᵐ m₂`, the mode of the product of their grades.
RFC: `\mathsf{product}_m.{\cdot}` -/
def mul (m₁ m₂ : Mode) : Mode :=
  (m₁.grade * m₂.grade).mode

@[inherit_doc] infixr:70 " ·ᵐ " => mul

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/-- The mode `m ⊙ p`, in which a subterm used with the grade `p` is checked inside a term checked in
the mode `m`, so that a subterm, once erased, stays erased.
RFC: `\mathsf{product}_m.{\odot}` -/
def odot (m : Mode) (p : Grade) : Mode :=
  m ·ᵐ p.mode

@[inherit_doc] infixr:70 " ⊙ " => odot

/-! The modes with their grades, and the product of two modes. -/

theorem grades :
    [zeroZero, zeroOne, oneOne].map grade = [Grade.zero, Grade.noneLinear, Grade.one] := rfl

/-- The product of two modes is the more erased of the two.
RFC: `\mathsf{erased}_m` -/
theorem mul_more_erased : ∀ m₁ m₂ : Mode,
    (m₁ = zeroZero ∨ m₂ = zeroZero → m₁ ·ᵐ m₂ = zeroZero) ∧
      (m₁ ≠ zeroZero ∧ m₂ ≠ zeroZero ∧ (m₁ = zeroOne ∨ m₂ = zeroOne) → m₁ ·ᵐ m₂ = zeroOne) ∧
      (m₁ = oneOne ∧ m₂ = oneOne → m₁ ·ᵐ m₂ = oneOne) := by
  decide

end Mode

/-! ### Modes of ADE

The two modes of ADE have on the multiplicities the structure that the three modes have on the
grades. -/

namespace Multiplicity.Mode

/-- Decides a statement on both modes of ADE. -/
instance {P : Mode → Prop} [DecidablePred P] : Decidable (∀ m, P m) :=
  decidable_of_iff (P .zero ∧ P .one)
    ⟨fun ⟨h₁, h₂⟩ m => by cases m <;> assumption, fun h => ⟨h _, h _⟩⟩

-- ADE: `⌜_⌝`, in `Graded/Mode.agda`.
/-- The multiplicity `⌜m⌝` with which a variable checked in the mode `m` uses itself. -/
def multiplicity : Mode → Multiplicity
  | .zero => .zero
  | .one => .one

end Multiplicity.Mode

namespace Multiplicity

-- ADE: `⌞_⌟`, in `Graded/Mode.agda`.
/-- The mode `⌞π⌟` in which a term used with the multiplicity `π` is checked: `𝟘ᵐ` for `0` and `𝟙ᵐ`
for the multiplicities that are used. -/
def mode : Multiplicity → Mode
  | .zero => .zero
  | _ => .one

end Multiplicity

namespace Multiplicity.Mode

-- ADE: `_·ᵐ_`, in `Graded/Mode.agda`.
/-- The product of two modes of ADE, `m₁ ·ᵐ m₂`, the mode of the product of their multiplicities. -/
def mul (m₁ m₂ : Mode) : Mode :=
  (m₁.multiplicity * m₂.multiplicity).mode

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/-- The mode `m ⊙ π`, in which a subterm used with the multiplicity `π` is checked inside a term
checked in the mode `m`. -/
def odot (m : Mode) (π : Multiplicity) : Mode :=
  mul m π.mode

/-! The modes of ADE with their multiplicities, and the product of two modes. -/

theorem multiplicities : [zero, one].map multiplicity = [Multiplicity.zero, Multiplicity.one] := rfl

/-- The multiplicities `0` and `1` are closed under multiplication, so that
`⌜m₁ ·ᵐ m₂⌝ = ⌜m₁⌝ · ⌜m₂⌝`. -/
theorem multiplicity_mul : ∀ m₁ m₂ : Mode,
    (mul m₁ m₂).multiplicity = m₁.multiplicity * m₂.multiplicity := by
  decide

end Multiplicity.Mode

namespace Mode

/-- The modes project on those of ADE as the grades project on their run-time
multiplicity, the two erased modes on `𝟘ᵐ` and the mode of run time on `𝟙ᵐ`. -/
def run : Mode → Multiplicity.Mode
  | zeroZero => .zero
  | zeroOne => .zero
  | oneOne => .one

/-! ## Properties

The three modes form a mode structure of ADE over the grades. -/

end Mode

-- ADE: `IsMode`, in `Graded/Mode.agda`.
/-- The laws of a mode structure of ADE, which the modes satisfy over the grades. -/
structure IsModeStructure : Prop where
  /-- The product of modes is associative.
  RFC: `\mathsf{structure}_m.\mathsf{assoc}` -/
  mul_assoc : ∀ m₁ m₂ m₃ : Mode, (m₁ ·ᵐ m₂) ·ᵐ m₃ = m₁ ·ᵐ (m₂ ·ᵐ m₃)
  /-- The product of modes is commutative.
  RFC: `\mathsf{structure}_m.\mathsf{comm}` -/
  mul_comm : ∀ m₁ m₂ : Mode, m₁ ·ᵐ m₂ = m₂ ·ᵐ m₁
  /-- The product of modes is idempotent.
  RFC: `\mathsf{structure}_m.\mathsf{idem}` -/
  mul_idem : ∀ m : Mode, m ·ᵐ m = m
  /-- The mode `11ᵐ` is neutral for the product.
  RFC: `\mathsf{structure}_m.\mathsf{unit}` -/
  oneOne_mul : ∀ m : Mode, .oneOne ·ᵐ m = m
  /-- The mode `00ᵐ` is absorbing for the product.
  RFC: `\mathsf{structure}_m.\mathsf{zero}` -/
  zeroZero_mul : ∀ m : Mode, .zeroZero ·ᵐ m = .zeroZero
  /-- The grade of `00ᵐ` is `00ᵖ`.
  RFC: `\mathsf{structure}_m.\mathsf{grade}_{00}` -/
  grade_zeroZero : Mode.zeroZero.grade = Grade.zero
  /-- The mode of the grade of a mode is this mode.
  RFC: `\mathsf{structure}_m.\mathsf{section}` -/
  mode_grade : ∀ m : Mode, m.grade.mode = m
  /-- The grade of a product of modes is the product of their grades.
  RFC: `\mathsf{structure}_m.\mathsf{grade}_{\cdot}` -/
  grade_mul : ∀ m₁ m₂ : Mode, (m₁ ·ᵐ m₂).grade = m₁.grade * m₂.grade
  /-- The product of the modes of two grades is the mode of their product.
  RFC: `\mathsf{structure}_m.\mathsf{mode}_{\cdot}` -/
  mode_mul : ∀ p q : Grade, p.mode ·ᵐ q.mode = (p * q).mode
  /-- A grade times the grade of its mode is this grade.
  RFC: `\mathsf{structure}_m.\mathsf{runit}` -/
  mul_grade_mode : ∀ p : Grade, p * p.mode.grade = p
  /-- The grade of the mode of a grade, times this grade, is this grade.
  RFC: `\mathsf{structure}_m.\mathsf{lunit}` -/
  grade_mode_mul : ∀ p : Grade, p.mode.grade * p = p
  /-- If `p ≤ q` and `q ≤ ⌜m⌝ · q`, then `p ≤ ⌜m⌝ · p`.
  RFC: `\mathsf{structure}_m.\mathsf{order}` -/
  le_grade_mul : ∀ (m : Mode) (p q : Grade), p ≤ q → q ≤ m.grade * q → p ≤ m.grade * p
  /-- The mode of a sum of grades is no more erased than the mode of its first operand.
  RFC: `\mathsf{structure}_m.\mathsf{mode}_{+}` -/
  mode_add : ∀ p q : Grade, p.mode ·ᵐ (p + q).mode = p.mode
  /-- The mode of a meet of grades is no more erased than the mode of its first operand.
  RFC: `\mathsf{structure}_m.\mathsf{mode}_{\wedge}` -/
  mode_meet : ∀ p q : Grade, p.mode ·ᵐ (p ⊓ q).mode = p.mode

namespace Mode

-- ADE: `Zero-one-isMode`, in `Graded/Mode/Instances/Zero-one.agda`.
/-- The modes form a mode structure over the grades.
RFC: `\mathsf{structure}_m.\mathsf{assoc}`, `\mathsf{structure}_m.\mathsf{comm}`
RFC: `\mathsf{structure}_m.\mathsf{idem}`, `\mathsf{structure}_m.\mathsf{unit}`
RFC: `\mathsf{structure}_m.\mathsf{zero}`, `\mathsf{structure}_m.\mathsf{grade}_{00}`
RFC: `\mathsf{structure}_m.\mathsf{section}`, `\mathsf{structure}_m.\mathsf{grade}_{\cdot}`
RFC: `\mathsf{structure}_m.\mathsf{mode}_{\cdot}`, `\mathsf{structure}_m.\mathsf{runit}`
RFC: `\mathsf{structure}_m.\mathsf{lunit}`, `\mathsf{structure}_m.\mathsf{order}`
RFC: `\mathsf{structure}_m.\mathsf{mode}_{+}`, `\mathsf{structure}_m.\mathsf{mode}_{\wedge}` -/
theorem modeStructure : IsModeStructure where
  mul_assoc := by decide
  mul_comm := by decide
  mul_idem := by decide
  oneOne_mul := by decide
  zeroZero_mul := by decide
  grade_zeroZero := by decide
  mode_grade := by decide
  grade_mul := by decide
  mode_mul := by decide
  mul_grade_mode := by decide
  grade_mode_mul := by decide
  le_grade_mul := by decide
  mode_add := by decide
  mode_meet := by decide

/-- The projection commutes with the mode of a grade, with the grade of a mode and with the
product of a mode by a grade. -/
theorem run_odot :
    (∀ p : Grade, p.mode.run = p.run.mode) ∧
      (∀ m : Mode, m.run.multiplicity = m.grade.run) ∧
      ∀ (m : Mode) (p : Grade), (m ⊙ p).run = m.run.odot p.run := by
  decide

end Mode

end Sic
