module

import Sic.Core.Injectivity

/-!
# The Universes: Injectivity

`Sic.Core.Typing` equates two universes exactly when their levels are equivalent: the universes
`U_l` and `U_{l + 1}` are not equal, while `U_{l ⊔ l}` and `U_l` are, so that `TypeEq.inv_univ` can
only conclude the equivalence of the levels, not their equality.
-/

@[expose] public section

namespace SicTest.Universe.Injectivity

open Sic.Core Sic.Core.Term

/-- The universes `U_l` and `U_{l + 1}` are not equal types: `l` and `l + 1` differ when `l` is `0`. -/
example : ¬ (.empty : Con 1 0) ⊢ univ (.var 0) ≡ univ (.succ (.var 0)) := fun h =>
  have ⟨_, e, hl⟩ := h.inv_univ .univ
  by cases e; exact nomatch hl fun _ => 0

/-- The universes `U_{l ⊔ l}` and `U_l` are equal types, while `l ⊔ l` and `l` are distinct levels. -/
example : (.empty : Con 1 0) ⊢ univ (.var 0 ⊔ .var 0) ≡ univ (.var 0) :=
  .univ (.univ .empty fun _ => Nat.max_self _)

end SicTest.Universe.Injectivity
