module

import Sic.Core.Reduction

/-!
# Meaning of the Reduction

A neutral term does not reduce.
-/

namespace SicTest.Meaning.Reduction

open Sic.Core Sic.Grade Sic.Core.Term

/-- A variable applied to an argument, `x ∘_𝟙 y`, is neutral, so that it does not reduce. -/
example {Γ : Con 0 2} : ¬ Γ ⊢ app 𝟙 (var 0) (var 1) ⇒ u : A := Neutral.not_termRed (.app .var)

end SicTest.Meaning.Reduction
