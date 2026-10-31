module

import Sic.Core.Reducibility.Fundamental
import all SicTest.TypeVariable.Reducibility.Introductions.Function
import all SicTest.TypeVariable.Reducibility.LogicalRelation

/-!
# A Type Variable: Fundamental Lemma

`Sic.Core.Typing` does not equate the type `(λ_p (X : U_l). X) ∘_p A`, which is equal to the type
variable `A`, to the type of functions `Π^p'_q' (x : A). A`: the equality would be valid, by the
fundamental lemma, while the validity does not equate them.
Any equality relation gives the contradiction, and the equality of `Sic.Core.Typing` is one.
-/

namespace SicTest.TypeVariable.Reducibility.Fundamental

open Sic.Core Sic.Core.Term Sic.Core.Reducibility SicTest.TypeVariable.Reducibility.LogicalRelation
  SicTest.TypeVariable.Reducibility.Introductions.Function

/-- `(λ_p (X : U_l). X) ∘_p A` and `Π^p'_q' (x : A). A` are not equal types. -/
example : ¬ ΓA ⊢ idA p ≡ pi p' q' (var 0) (var 1) := fun h =>
  letI := EqualityRelation.termEqRelation
  have ⟨_, h⟩ := h.valid
  not_validTypeEq_idA_pi h

end SicTest.TypeVariable.Reducibility.Fundamental
