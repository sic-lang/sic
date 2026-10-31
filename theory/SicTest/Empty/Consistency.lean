module

import Sic.Core.Consistency
import all SicTest.Identity.Syntax
import all SicTest.Identity.Typing

/-!
# The Empty Type: Consistency

`not_hasType_forall` states exactly what makes `Π^q_p (X : U_l). X` empty: its codomain is the
variable `X` itself, since the type `Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A` of the polymorphic
identity, whose codomain is a type of functions, has a closed term, and its term must be closed,
since a variable of the type is a term of it.
-/

namespace SicTest.Empty.Consistency

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax SicTest.Identity.Typing

/-- The type of the polymorphic identity, of the form `Π^q_p (X : U_l). B`, has a closed term. -/
example : ∃ t, .empty ⊢ t : identityType := ⟨_, hasType_identity⟩

/-- In a context that declares a variable of the type `Π^𝟘_𝟘 (X : U_l). X`, the variable has it. -/
example : (.empty : Con 1 0) ∙ pi 𝟘 𝟘 (univ (.var 0)) (var 0) ⊢
    var 0 : pi 𝟘 𝟘 (univ (.var 0)) (var 0) :=
  -- `U_l : U_{l + 1}`, and `X : U_l` after `X`.
  have hU : (.empty : Con 1 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ .empty
  have hX : .empty ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ hU))
  .var (.snoc (.univ (.pi hU hX)))

end SicTest.Empty.Consistency
