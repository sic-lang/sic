module

import Sic.Core.Injectivity

/-!
# RFC 24: Injectivity

The claims of RFC 24 on the equality of types.
-/

@[expose] public section

namespace SicTest.Rfc24.Injectivity

open Sic.Core Sic.Grade Sic.Core.Term

/--
Two types of functions that differ only by a grade are different types, as the section Conversion
of RFC 24 states: `Π^𝟘_𝟙 (x : A). A` and `Π^𝟘_{𝟙 + 𝟙} (x : A). A` are not equal, in the context
`A : U_0`.
-/
example :
    ¬ (.empty ∙ univ .zero : Con 0 1) ⊢ pi 𝟙 𝟘 (var 0) (var 1) ≡ pi (𝟙 + 𝟙) 𝟘 (var 0) (var 1) :=
  fun h => absurd h.pi_inj.1 (by decide)

end SicTest.Rfc24.Injectivity
