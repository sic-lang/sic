module

public import Sic.Grade

/-!
# Modes

The modes of RFC 33: a mode is the setting in which the usage of a term is checked, named after the
grade with which a variable checked in this mode uses itself.
ADE have the two modes `𝟘ᵐ` and `𝟙ᵐ`, which are `𝟘𝟘ᵐ` and `𝟙𝟙ᵐ` here: the mode `𝟘𝟙ᵐ` is added so that
an erased term still counts all its uses.
-/

@[expose] public section

namespace Sic

-- ADE: `Mode`, in `Graded/Mode.agda`, which has the modes `𝟘ᵐ` and `𝟙ᵐ` only.
/--
A mode of the core.
The mode `𝟘𝟘ᵐ` counts no use, `𝟘𝟙ᵐ` counts all the uses, none at run time, and `𝟙𝟙ᵐ` counts all the
uses and the uses at run time.
-/
inductive Mode where
  /-- `𝟘𝟘ᵐ`: no use. -/
  | zeroZero
  /-- `𝟘𝟙ᵐ`: all the uses, none at run time. -/
  | zeroOne
  /-- `𝟙𝟙ᵐ`: all the uses and the uses at run time. -/
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
/-- The grade `⌜m⌝` with which a variable checked in the mode `m` uses itself. -/
def grade : Mode → Grade
  | zeroZero => .zero
  | zeroOne => .noneLinear
  | oneOne => .one

end Mode

namespace Grade

-- ADE: `⌞_⌟`, in `Graded/Mode.agda`.
/-- The mode `⌞p⌟` in which a term used with the grade `p` is checked: `𝟘𝟘ᵐ` for `𝟘`, `𝟘𝟙ᵐ` for the
other grades whose run-time multiplicity is `0`, those of proofs, specifications and permissions,
and `𝟙𝟙ᵐ` for the grades used at run time. -/
def mode (p : Grade) : Mode :=
  if p.run ≠ .zero then .oneOne else if p.total = .zero then .zeroZero else .zeroOne

/-- The three clauses of RFC 33 for `⌞p⌟`. -/
theorem mode_clauses :
    mode zero = .zeroZero ∧ (∀ v, v ≠ .zero → ∀ h, mode ⟨.zero, v, h⟩ = .zeroOne) ∧
      ∀ u v, u ≠ .zero → ∀ h, mode ⟨u, v, h⟩ = .oneOne := by
  refine ⟨rfl, ?_, ?_⟩
  · intro v hv h
    simp [mode, hv]
  · intro u v hu h
    simp [mode, hu]

end Grade

namespace Mode

-- ADE: `_·ᵐ_`, in `Graded/Mode.agda`.
/-- The product of two modes, `m₁ ·ᵐ m₂`, the mode of the product of their grades. -/
def mul (m₁ m₂ : Mode) : Mode :=
  (m₁.grade * m₂.grade).mode

@[inherit_doc] infixr:70 " ·ᵐ " => mul

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/-- The mode `m ⊙ p`, in which a subterm used with the grade `p` is checked inside a term checked in
the mode `m`, so that a subterm, once erased, stays erased. -/
def odot (m : Mode) (p : Grade) : Mode :=
  m ·ᵐ p.mode

@[inherit_doc] infixr:70 " ⊙ " => odot

/-! The modes with their grades, and the product of two modes. -/

theorem grades :
    [zeroZero, zeroOne, oneOne].map grade = [Grade.zero, Grade.noneLinear, Grade.one] := rfl

/-- The grades of the three modes are closed under multiplication, so that `⌜m₁ ·ᵐ m₂⌝ = ⌜m₁⌝ · ⌜m₂⌝`,
and the product of two modes is the more erased of the two. -/
theorem grade_mul : ∀ m₁ m₂ : Mode, (m₁ ·ᵐ m₂).grade = m₁.grade * m₂.grade := by decide

theorem mul_more_erased : ∀ m₁ m₂ : Mode,
    m₁ ·ᵐ m₂ = if m₁ = zeroZero ∨ m₂ = zeroZero then zeroZero
      else if m₁ = zeroOne ∨ m₂ = zeroOne then zeroOne else oneOne := by
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
/-- The mode `⌞u⌟` in which a term used with the multiplicity `u` is checked: `𝟘ᵐ` for `0` and `𝟙ᵐ`
for the multiplicities that are used. -/
def mode (u : Multiplicity) : Mode :=
  if u = .zero then .zero else .one

/-- The two clauses of RFC 33 for `⌞u⌟`. -/
theorem mode_clauses : mode .zero = .zero ∧ ∀ u, u ≠ .zero → mode u = .one := by
  refine ⟨rfl, ?_⟩
  intro u hu
  simp [mode, hu]

end Multiplicity

namespace Multiplicity.Mode

-- ADE: `_·ᵐ_`, in `Graded/Mode.agda`.
/-- The product of two modes of ADE, `m₁ ·ᵐ m₂`, the mode of the product of their multiplicities. -/
def mul (m₁ m₂ : Mode) : Mode :=
  (m₁.multiplicity * m₂.multiplicity).mode

-- ADE: `_ᵐ·_`, in `Graded/Mode.agda`.
/-- The mode `m ⊙ u`, in which a subterm used with the multiplicity `u` is checked inside a term
checked in the mode `m`. -/
def odot (m : Mode) (u : Multiplicity) : Mode :=
  mul m u.mode

/-! The modes of ADE with their multiplicities, and the product of two modes. -/

theorem multiplicities : [zero, one].map multiplicity = [Multiplicity.zero, Multiplicity.one] := rfl

/-- The multiplicities `0` and `1` are closed under multiplication, so that
`⌜m₁ ·ᵐ m₂⌝ = ⌜m₁⌝ · ⌜m₂⌝`. -/
theorem multiplicity_mul : ∀ m₁ m₂ : Mode,
    (mul m₁ m₂).multiplicity = m₁.multiplicity * m₂.multiplicity := by
  decide

end Multiplicity.Mode

namespace Mode

/-- `(run_m)`: the modes project on those of ADE as the grades project on their run-time
multiplicity, the two erased modes on `𝟘ᵐ` and the mode of run time on `𝟙ᵐ`. -/
def run : Mode → Multiplicity.Mode
  | zeroZero => .zero
  | zeroOne => .zero
  | oneOne => .one

/-! ## Properties

The three modes form a mode structure of ADE. -/

-- ADE: `IsMode`, in `Graded/Mode.agda`.
theorem mul_assoc : ∀ m₁ m₂ m₃ : Mode, (m₁ ·ᵐ m₂) ·ᵐ m₃ = m₁ ·ᵐ (m₂ ·ᵐ m₃) := by decide

theorem mul_comm : ∀ m₁ m₂ : Mode, m₁ ·ᵐ m₂ = m₂ ·ᵐ m₁ := by decide

theorem mul_idem : ∀ m : Mode, m ·ᵐ m = m := by decide

theorem oneOne_mul : ∀ m : Mode, oneOne ·ᵐ m = m := by decide

theorem zeroZero_mul : ∀ m : Mode, zeroZero ·ᵐ m = zeroZero := by decide

theorem mode_grade : ∀ m : Mode, m.grade.mode = m := by decide

theorem mode_mul : ∀ p q : Grade, p.mode ·ᵐ q.mode = (p * q).mode := by decide

theorem mul_grade_mode : ∀ p : Grade, p * p.mode.grade = p ∧ p.mode.grade * p = p := by decide

theorem le_grade_mul : ∀ (m : Mode) (p q : Grade), p ≤ q → q ≤ m.grade * q → p ≤ m.grade * p := by
  decide

theorem grade_zeroZero : zeroZero.grade = Grade.zero := rfl

/-- `(run_⊙)`: the projection commutes with the mode of a grade, with the grade of a mode and with the
product of a mode by a grade. -/
theorem run_odot :
    (∀ p : Grade, p.mode.run = p.run.mode) ∧
      (∀ m : Mode, m.run.multiplicity = m.grade.run) ∧
      ∀ (m : Mode) (p : Grade), (m ⊙ p).run = m.run.odot p.run := by
  decide

end Mode

end Sic
