module

import Sic.Core.Typing
import all SicTest.Identity.Syntax

/-!
# The Polymorphic Identity: Typing

The type of the polymorphic identity of RFC 24, as a derivation.
-/

namespace SicTest.Identity.Typing

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax

/--
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` has the type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A` in the empty context, with its level variable `l`.
-/
theorem hasType_identity : .empty ⊢ identity : identityType :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`.
  have hU : (.empty : Con 1 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ .empty
  have hA : .empty ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ hU))
  have hA' : .empty ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hA))
  have hPi := HasType.pi hA hA'
  .lam (.univ (.pi hU hPi)) (.lam (.univ hPi) (.var (.snoc (.univ hA))))

end SicTest.Identity.Typing
