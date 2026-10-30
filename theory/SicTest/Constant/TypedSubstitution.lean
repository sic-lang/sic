module

import Sic.Core.TypedSubstitution
import all SicTest.Constant.Syntax
import all SicTest.Constant.Typing

/-!
# The Constant Function: Typed Substitution

The constant function moved to a larger context.
-/

namespace SicTest.Constant.TypedSubstitution

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Constant.Syntax SicTest.Constant.Typing

/--
The constant function keeps its type after a new declaration `x : A`, where `A` is `var 1`, at the
end of its context `A : U₀, B : U₀`: each variable of the function and of its type moves past `x`,
to the next index.
-/
example : Γ₂ ∙ var 1 ⊢ constant.wk1 : constantType.wk1 :=
  hasType_constant.wk (.step .id) (.snoc (.univ (.var wfCon_Γ₂)))

end SicTest.Constant.TypedSubstitution
