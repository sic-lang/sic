module

import Sic.Core.WellFormed
import SicTest.ChurchNumerals.Syntax
import SicTest.ChurchNumerals.Typing

/-!
# The Church Numerals: Well-Formedness

The type of `succ` is a type.
-/

@[expose] public section

namespace SicTest.ChurchNumerals.WellFormed

open Sic.Core Sic.Grade Sic.Core.Term SicTest.ChurchNumerals.Syntax SicTest.ChurchNumerals.Typing

/-- The type of `succ` is a type, in every well-formed context. -/
example (h : ⊢ Γ) : Γ ⊢ pi 𝟙 𝟘 churchNat churchNat :=
  (hasType_churchSucc h).wfType

end SicTest.ChurchNumerals.WellFormed
