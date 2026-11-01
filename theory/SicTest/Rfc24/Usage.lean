module

import Sic.Core.Usage
import all SicTest.GradeVector

/-!
# Usage

The claims of RFC 24 on the usage of the terms: the meaning of the multiplicities, which `(sub)`
gives the grades; the permission used once of its examples has its own theme,
`SicTest/Permission/`.
-/

namespace SicTest.Rfc24.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.GradeVector

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-!
## Multiplicities

In a context of two variables `f` and `x`, the terms `f`, `f ∘_𝟙 x` and `(f ∘_𝟙 x) ∘_𝟙 x` use `x`
never, once and twice, at run time.
Usage reads the terms alone, so the types of `f` and `x` need not be given.
The vectors give `f` the grade `𝟙`, and `x` the grade under check, whose two multiplicities are
the same, last, since `x` is the innermost variable.
-/

def never : Term 0 2 := var 1

def once : Term 0 2 := app 𝟙 (var 1) (var 0)

def twice : Term 0 2 := app 𝟙 (app 𝟙 (var 1) (var 0)) (var 0)

/-!
Each term is well used exactly with the vectors below the uses that it counts, `x` included,
whatever the uses of `(sub)`: the inversions bound the vectors, and the rules reach the bounds.
-/

theorem usage_never_iff : γ ▶[𝟙𝟙ᵐ] never ↔ γ ≤ 𝟘ᶜ ∙ 𝟙 ∙ 𝟘 :=
  ⟨fun h => GradeVector.le_trans h.inv_var (by decide),
    fun h => .sub .var (GradeVector.le_trans h (by decide))⟩

theorem usage_once_iff : γ ▶[𝟙𝟙ᵐ] once ↔ γ ≤ 𝟘ᶜ ∙ 𝟙 ∙ 𝟙 :=
  ⟨fun h =>
    have ⟨_, _, hf, hx, hγ⟩ := h.inv_app
    GradeVector.le_trans hγ <|
      GradeVector.le_trans (add_mono hf.inv_var (smul_mono (Grade.le_refl _) hx.inv_var))
        (by decide),
    fun h => .sub (.app .var .var) (GradeVector.le_trans h (by decide))⟩

theorem usage_twice_iff : γ ▶[𝟙𝟙ᵐ] twice ↔ γ ≤ 𝟘ᶜ ∙ 𝟙 ∙ (𝟙 + 𝟙) :=
  ⟨fun h =>
    have ⟨_, _, ht, hx, hγ⟩ := h.inv_app
    have ⟨_, _, hf, hx', hδ⟩ := ht.inv_app
    GradeVector.le_trans hγ <| GradeVector.le_trans
      (add_mono
        (GradeVector.le_trans hδ (add_mono hf.inv_var (smul_mono (Grade.le_refl _) hx'.inv_var)))
        (smul_mono (Grade.le_refl _) hx.inv_var))
      (by decide),
    fun h => .sub (.app (.app .var .var) .var) (GradeVector.le_trans h (by decide))⟩

/-- A variable of multiplicity `ω` may be used any number of times, none included. -/
theorem usage_omega :
    (𝟘ᶜ ∙ 𝟙 ∙ ⟪.omega, .omega⟫ ▶[𝟙𝟙ᵐ] never) ∧ (𝟘ᶜ ∙ 𝟙 ∙ ⟪.omega, .omega⟫ ▶[𝟙𝟙ᵐ] once) ∧
      (𝟘ᶜ ∙ 𝟙 ∙ ⟪.omega, .omega⟫ ▶[𝟙𝟙ᵐ] twice) :=
  ⟨usage_never_iff.2 (by decide), usage_once_iff.2 (by decide), usage_twice_iff.2 (by decide)⟩

/-- A variable of multiplicity `1` is used exactly once. -/
theorem usage_one :
    ¬ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙 ▶[𝟙𝟙ᵐ] never) ∧ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙 ▶[𝟙𝟙ᵐ] once) ∧
      ¬ (𝟘ᶜ ∙ 𝟙 ∙ 𝟙 ▶[𝟙𝟙ᵐ] twice) :=
  ⟨fun h => absurd (usage_never_iff.1 h) (by decide), usage_once_iff.2 (by decide),
    fun h => absurd (usage_twice_iff.1 h) (by decide)⟩

/-- A variable of multiplicity `0` is never used. -/
theorem usage_zero :
    (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ▶[𝟙𝟙ᵐ] never) ∧ ¬ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ▶[𝟙𝟙ᵐ] once) ∧ ¬ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ▶[𝟙𝟙ᵐ] twice) :=
  ⟨usage_never_iff.2 (by decide), fun h => absurd (usage_once_iff.1 h) (by decide),
    fun h => absurd (usage_twice_iff.1 h) (by decide)⟩

/-!
## Usage

The rule `(sub)` lets an unrestricted variable be used once or not at all, as `usage_omega` shows,
and a variable of grade `⟨ω, 1⟩` be used once, at run time or not: once at run time when the
variable is checked in the mode `𝟙𝟙ᵐ`, and once erased when it is the argument of an erased
parameter, of grade `⟨0, 1⟩`, which checks it in the mode `𝟘𝟙ᵐ`.
-/

theorem usage_affine :
    (𝟘ᶜ ∙ ⟪.omega, .one⟫ ▶[𝟙𝟙ᵐ] (var 0 : Term 0 1)) ∧
      (𝟘ᶜ ∙ 𝟙 ∙ ⟪.omega, .one⟫ ▶[𝟙𝟙ᵐ] (app ⟪.zero, .one⟫ (var 1) (var 0) : Term 0 2)) :=
  ⟨.sub .var (by decide), .sub (.app .var .var) (by decide)⟩

end SicTest.Rfc24.Usage
