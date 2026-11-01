module

import Sic.Core.Substitution

/-!
# The Constant Function: Substitution

The substitution that `(β)` performs when it applies the constant function.
-/

@[expose] public section

namespace SicTest.Constant.Substitution

open Sic.Core Sic.Grade Sic.Core.Term

/--
The rule `(β)` applies the constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` to `a`:
`(λ_𝟘 (y : B). x)[a/x]` is `λ_𝟘 (y : B). a`, where `a` is moved under the binder of `y`.
-/
example (a : Term 0 2) : (lam 𝟘 (var 1) (var 1)).instantiate a = lam 𝟘 (var 0) a.wk1 := rfl

end SicTest.Constant.Substitution
