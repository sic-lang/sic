module

import Sic.Core.Typing

/-!
# The Universes: Typing

The universes are types, and two universes whose levels are equal are equal types.
-/

@[expose] public section

namespace SicTest.Universe.Typing

open Sic.Core Sic.Core.Term

/-- The universe `U_l` is a type, in the empty context, with its level variable `l`. -/
example : (.empty : Con 1 0) ⊢ univ (.var 0) := .univ (.univ .empty)

/-- `U_{l ⊔ l}` and `U_l` are equal types, since `l ⊔ l` equals `l` whatever the value of `l`. -/
example : (.empty : Con 1 0) ⊢ univ (.var 0 ⊔ .var 0) ≡ univ (.var 0) :=
  .univ (.univ .empty fun _ => Nat.max_self _)

end SicTest.Universe.Typing
