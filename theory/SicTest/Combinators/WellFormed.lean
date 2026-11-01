module

import Sic.Core.WellFormed
import SicTest.Combinators.Syntax
import SicTest.Combinators.Typing

/-!
# The Combinators K and S: Well-Formedness

The type of `S` is a type.
-/

@[expose] public section

namespace SicTest.Combinators.WellFormed

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Combinators.Syntax SicTest.Combinators.Typing

/-- The type of `S` is a type. -/
example : (.empty : Con 1 0) ⊢ combinatorSType :=
  (hasType_combinatorS .empty).wfType

end SicTest.Combinators.WellFormed
