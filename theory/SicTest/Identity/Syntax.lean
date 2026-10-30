module

import Sic.Core.Syntax

/-!
# The Polymorphic Identity

The polymorphic identity of RFC 24, written as a term of `Sic.Core.Syntax`.
-/

namespace SicTest.Identity.Syntax

open Sic.Core Sic.Grade Sic.Core.Term

/-!
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` and its type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A`, closed, over the level variable `l`, which is `var 0`.
-/

def identity : Term 1 0 := lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 0) (var 0))

def identityType : Term 1 0 := pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1))

end SicTest.Identity.Syntax
