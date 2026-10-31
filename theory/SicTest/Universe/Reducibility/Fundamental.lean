module

import Sic.Core.Reducibility.Fundamental
import all SicTest.Universe.Reducibility.Validity

/-!
# The Universes: Fundamental Lemma

`Sic.Core.Typing` does not equate two universes of different levels: the equality would be valid,
by the fundamental lemma, while the validity does not equate them.
Any equality relation gives the contradiction, and the equality of `Sic.Core.Typing` is one.
-/

namespace SicTest.Universe.Reducibility.Fundamental

open Sic.Core Sic.Core.Term Sic.Core.Reducibility SicTest.Universe.Reducibility.Validity

/-- The universes `U_l` and `U_{l + 1}` are not equal types. -/
example : ¬ (.empty : Con 1 0) ⊢ univ (.var 0) ≡ univ (.succ (.var 0)) := fun h =>
  letI := EqualityRelation.termEqRelation
  have ⟨_, h⟩ := h.valid
  not_validTypeEq_univ_succ h

end SicTest.Universe.Reducibility.Fundamental
