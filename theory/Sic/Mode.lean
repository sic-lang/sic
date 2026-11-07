module

public import Sic.Grade

/-!
# Modes

The modes of RFC 36: a mode is the setting in which the usage of a term is checked, named after the
grade with which a variable checked in this mode uses itself.
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
RFC: `\mathsf{product}_m` -/
def mul (m₁ m₂ : Mode) : Mode :=
  (m₁.grade * m₂.grade).mode

@[inherit_doc] infixr:70 " ·ᵐ " => mul

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/-- The mode `m ⊙ p`, in which a subterm used with the grade `p` is checked inside a term checked in
the mode `m`, so that a subterm, once erased, stays erased.
RFC: `\mathsf{product}_m` -/
def odot (m : Mode) (p : Grade) : Mode :=
  m ·ᵐ p.mode

@[inherit_doc] infixr:70 " ⊙ " => odot

/-! The modes with their grades, and the product of two modes. -/

theorem grades :
    [zeroZero, zeroOne, oneOne].map grade = [Grade.zero, Grade.noneLinear, Grade.one] := rfl

/-- The grades of the three modes are closed under multiplication, so that the grade of a product is
the product of the grades.
RFC: `\mathsf{closed}_m` -/
theorem grade_mul : ∀ m₁ m₂ : Mode, (m₁ ·ᵐ m₂).grade = m₁.grade * m₂.grade := by decide

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

-- ADE: `IsMode`, in `Graded/Mode.agda`.
/-- The modes form a mode structure over the grades.
RFC: `\mathsf{structure}_m` -/
theorem isMode : ∀ (m m₁ m₂ m₃ : Mode) (p q : Grade),
    (m₁ ·ᵐ m₂) ·ᵐ m₃ = m₁ ·ᵐ (m₂ ·ᵐ m₃) ∧
      m₁ ·ᵐ m₂ = m₂ ·ᵐ m₁ ∧
      m ·ᵐ m = m ∧
      oneOne ·ᵐ m = m ∧
      zeroZero ·ᵐ m = zeroZero ∧
      zeroZero.grade = Grade.zero ∧
      m.grade.mode = m ∧
      p.mode ·ᵐ q.mode = (p * q).mode ∧
      (p * p.mode.grade = p ∧ p.mode.grade * p = p) ∧
      (p ≤ q → q ≤ m.grade * q → p ≤ m.grade * p) := by
  intro m m₁ m₂ m₃
  cases m <;> cases m₁ <;> cases m₂ <;> cases m₃ <;> decide

/-- The projection commutes with the mode of a grade, with the grade of a mode and with the
product of a mode by a grade. -/
theorem run_odot :
    (∀ p : Grade, p.mode.run = p.run.mode) ∧
      (∀ m : Mode, m.run.multiplicity = m.grade.run) ∧
      ∀ (m : Mode) (p : Grade), (m ⊙ p).run = m.run.odot p.run := by
  decide

end Mode

end Sic
