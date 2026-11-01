module

public import Sic.Mode

/-!
# Modes

The definitions of `Sic.Mode` checked against RFC 24, entry by entry, and against their meaning.
-/

@[expose] public section

namespace SicTest.Mode

open Sic Sic.Grade Sic.Mode

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-! The table of RFC 24: the grade of each mode. -/

example : ⌜𝟘𝟘ᵐ⌝ = 𝟘 := rfl
example : ⌜𝟘𝟙ᵐ⌝ = ⟪.zero, .one⟫ := rfl
example : ⌜𝟙𝟙ᵐ⌝ = 𝟙 := rfl

/-!
The mode of each grade, entry by entry: `𝟘𝟘ᵐ` for `𝟘`, `𝟘𝟙ᵐ` for the other grades whose run-time
multiplicity is `0`, and `𝟙𝟙ᵐ` for the grades used at run time.
-/

example : ⌞⟪.zero, .zero⟫⌟ = 𝟘𝟘ᵐ := rfl
example : ⌞⟪.zero, .one⟫⌟ = 𝟘𝟙ᵐ := rfl
example : ⌞⟪.zero, .omega⟫⌟ = 𝟘𝟙ᵐ := rfl
example : ⌞⟪.one, .one⟫⌟ = 𝟙𝟙ᵐ := rfl
example : ⌞⟪.one, .omega⟫⌟ = 𝟙𝟙ᵐ := rfl
example : ⌞⟪.omega, .one⟫⌟ = 𝟙𝟙ᵐ := rfl
example : ⌞⟪.omega, .omega⟫⌟ = 𝟙𝟙ᵐ := rfl

/-! The product of two modes, entry by entry: the more erased of the two. -/

example : 𝟘𝟘ᵐ * 𝟘𝟘ᵐ = 𝟘𝟘ᵐ := rfl
example : 𝟘𝟘ᵐ * 𝟘𝟙ᵐ = 𝟘𝟘ᵐ := rfl
example : 𝟘𝟘ᵐ * 𝟙𝟙ᵐ = 𝟘𝟘ᵐ := rfl
example : 𝟘𝟙ᵐ * 𝟘𝟘ᵐ = 𝟘𝟘ᵐ := rfl
example : 𝟘𝟙ᵐ * 𝟘𝟙ᵐ = 𝟘𝟙ᵐ := rfl
example : 𝟘𝟙ᵐ * 𝟙𝟙ᵐ = 𝟘𝟙ᵐ := rfl
example : 𝟙𝟙ᵐ * 𝟘𝟘ᵐ = 𝟘𝟘ᵐ := rfl
example : 𝟙𝟙ᵐ * 𝟘𝟙ᵐ = 𝟘𝟙ᵐ := rfl
example : 𝟙𝟙ᵐ * 𝟙𝟙ᵐ = 𝟙𝟙ᵐ := rfl

/-! The other claims of RFC 24. -/

/-- The grades of the three modes are closed under multiplication. -/
example : ∀ m₁ m₂ : Mode, ∃ m : Mode, ⌜m₁⌝ * ⌜m₂⌝ = ⌜m⌝ := fun m₁ m₂ =>
  ⟨m₁ * m₂, (grade_mul m₁ m₂).symm⟩

/-- A subterm, once erased, stays erased. -/
example : ∀ (m : Mode) (p : Grade), m ≠ 𝟙𝟙ᵐ → m ⊙ p ≠ 𝟙𝟙ᵐ := by decide
example : ∀ p : Grade, 𝟘𝟘ᵐ ⊙ p = 𝟘𝟘ᵐ := by decide

/--
A variable of grade `none / linear` may be used once in `𝟘𝟙ᵐ`, where it may be neither dropped nor
used twice, since its grade is not at most the uses counted then, while `𝟘𝟘ᵐ`, the mode `𝟘ᵐ` of
ADE, counts no use, once or twice, as none.
-/
example : ⟪.zero, .one⟫ ≤ ⌜𝟘𝟙ᵐ⌝ := by decide
example : ¬(⟪.zero, .one⟫ ≤ 𝟘) := by decide
example : ¬(⟪.zero, .one⟫ ≤ ⌜𝟘𝟙ᵐ⌝ + ⌜𝟘𝟙ᵐ⌝) := by decide
example : ⌜𝟘𝟘ᵐ⌝ = 𝟘 ∧ ⌜𝟘𝟘ᵐ⌝ + ⌜𝟘𝟘ᵐ⌝ = 𝟘 := by decide

/-!
The meaning of the modes, the column "Counts" of RFC 24: a use with the grade `p`, checked in the
mode `m`, counts as `⌜m⌝ * p`, which keeps the uses at run time of `p` only in `𝟙𝟙ᵐ`, and all its
uses everywhere but in `𝟘𝟘ᵐ`.
-/

/-- `𝟘𝟘ᵐ` counts no use. -/
theorem counts_zeroZero : ∀ p : Grade, (⌜𝟘𝟘ᵐ⌝ * p).run = .zero ∧ (⌜𝟘𝟘ᵐ⌝ * p).total = .zero := by decide
/-- `𝟘𝟙ᵐ` counts all the uses, none at run time. -/
theorem counts_zeroOne : ∀ p : Grade, (⌜𝟘𝟙ᵐ⌝ * p).run = .zero ∧ (⌜𝟘𝟙ᵐ⌝ * p).total = p.total := by decide
/-- `𝟙𝟙ᵐ` counts all the uses, and the uses at run time. -/
theorem counts_oneOne : ∀ p : Grade, (⌜𝟙𝟙ᵐ⌝ * p).run = p.run ∧ (⌜𝟙𝟙ᵐ⌝ * p).total = p.total := by decide

end SicTest.Mode
