module

import Sic.Core.WellFormed
import SicTest.Constant.Syntax
import SicTest.Constant.Typing

/-!
# The Constant Function: Well-Formedness

The type of the constant function is a type.
-/

@[expose] public section

namespace SicTest.Constant.WellFormed

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Constant.Syntax SicTest.Constant.Typing

/-- The type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of the constant function is a type. -/
example : Γ₂ ⊢ constantType := hasType_constant.wfType

end SicTest.Constant.WellFormed
