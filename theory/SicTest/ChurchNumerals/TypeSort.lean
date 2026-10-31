module

import Sic.Core.TypeSort
import all SicTest.ChurchNumerals.Syntax
import all SicTest.ChurchNumerals.Typing

/-!
# The Church Numerals: The Sort of a Type

The universe of a type is unique only up to the equality of levels: the type
`Π^𝟘_𝟙 (y : X). X` of the function that a numeral iterates is a term of `U_{l ⊔ l}`, by `(Π)`, and of
`U_l`, by `(conv)`, whose levels are equal, but not the same level.
-/

namespace SicTest.ChurchNumerals.TypeSort

open Sic.Core Sic.Core.Term SicTest.ChurchNumerals.Syntax SicTest.ChurchNumerals.Typing

/-- The context `X : U_l`, in which `Π^𝟘_𝟙 (y : X). X` is a type. -/
abbrev ΓX : Con 1 1 := .empty ∙ univ (.var 0)

theorem hasType_churchFunType_l : ΓX ⊢ churchFunType : univ (.var 0) :=
  have h := hasType_churchFunType .empty
  .conv h (.univ (.univ h.wfCon fun _ => Nat.max_self _))

/-- The two universes of `Π^𝟘_𝟙 (y : X). X` have equal levels. -/
example : (.var 0 ⊔ .var 0 : Level 1) ≈ .var 0 :=
  (hasType_churchFunType .empty).sort_unique hasType_churchFunType_l

/-- These levels are not the same level. -/
example : (.var 0 ⊔ .var 0 : Level 1) ≠ .var 0 := by decide

end SicTest.ChurchNumerals.TypeSort
