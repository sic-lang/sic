module

import Sic.Core.Substitution

/-!
# RFC 24: Substitution

The claims of RFC 24 on its substitution.
-/

@[expose] public section

namespace SicTest.Rfc24.Substitution

open Sic.Core Sic.Grade Sic.Core.Term

/--
`B[a/x]` renames the bound variables of `B` that `a` would capture: in the context `x : U₀`,
`(Π^𝟘_𝟙 (x : A). A)[x/A]` is `Π^𝟘_𝟙 (y : x). x`, whose bound variable `var 0` differs from the
free `x`, which is `var 1` under the binder.
-/
example : (pi 𝟙 𝟘 (var 0) (var 1) : Term 0 2).instantiate (var 0) = pi 𝟙 𝟘 (var 0) (var 1) := rfl

end SicTest.Rfc24.Substitution
