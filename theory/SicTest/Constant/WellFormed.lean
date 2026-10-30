module

import Sic.Core.WellFormed
import all SicTest.Constant.Syntax
import all SicTest.Constant.Typing

/-!
# The Constant Function: Well-Formedness

The type of the constant function is a type.
-/

namespace SicTest.Constant.WellFormed

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Constant.Syntax SicTest.Constant.Typing

/-- The type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of the constant function is a type. -/
example : ∃ l, Γ₂ ⊢ constantType : Term.univ l := hasType_constant.wfType

end SicTest.Constant.WellFormed
