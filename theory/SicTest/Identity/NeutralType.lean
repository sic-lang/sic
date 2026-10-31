module

import Sic.Core.Injectivity
import all SicTest.Identity.Syntax
import all SicTest.Identity.Typing

/-!
# The Polymorphic Identity: Neutral Types

`Neutral.typeEq` needs its term to be neutral: the polymorphic identity, an abstraction, has two
types that are not equal, since `Sic.Core.Typing` does not read the grade of the result of a type of
functions.
-/

namespace SicTest.Identity.NeutralType

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax SicTest.Identity.Typing

/-- The polymorphic identity also has the type `Π^𝟘_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A`. -/
theorem hasType_identity_zero :
    .empty ⊢ identity : pi 𝟘 𝟘 (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1)) :=
  -- The derivation of `hasType_identity`, with the grade `𝟘` of the result.
  have hU : (.empty : Con 1 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ .empty
  have hA : .empty ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ hU))
  have hA' : .empty ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hA))
  have hPi := HasType.pi hA hA'
  .lam (.univ (.pi hU hPi)) (.lam (.univ hPi) (.var (.snoc (.univ hA))))

/--
The polymorphic identity has two types that are not equal, `hasType_identity` and
`hasType_identity_zero`, whose results have different grades, so that `Neutral.typeEq` does not hold
for it.
-/
example : ¬ ∀ A B, (.empty ⊢ identity : A) → (.empty ⊢ identity : B) → .empty ⊢ A ≡ B := fun h =>
  absurd (h _ _ hasType_identity hasType_identity_zero).pi_inj.2.1 (by decide)

end SicTest.Identity.NeutralType
