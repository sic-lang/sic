module

import Sic.Core.Syntax

/-!
# RFC 24: Syntax

The claims of RFC 24 on its terms.
-/

namespace SicTest.Rfc24.Syntax

open Sic.Core Sic.Grade Sic.Core.Term

/--
Two types of functions that differ only by a grade are different types, as `Π^𝟘_𝟙 (x : A). A` and
`Π^𝟘_{𝟙 + 𝟙} (x : A). A`, in the context `A : U₀`.
-/
example : pi 𝟙 𝟘 (var 0) (var 1) ≠ (pi (𝟙 + 𝟙) 𝟘 (var 0) (var 1) : Term 0 1) := by decide

end SicTest.Rfc24.Syntax
