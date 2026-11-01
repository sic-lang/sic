module

public import SicTest.Omega.Reduction
import Sic.Core.Normalization

/-!
# The Divergent Term Ω: Normalization

`Ω` has no type, whatever the type of the variable of `ω` and the grade of its applications, as in
the simply typed lambda calculus of section 12.1 of [Pierce](https://www.cis.upenn.edu/~bcpierce/tapl/):
a term of a type reduces to a weak head normal form, while `Ω` reduces only to itself.
-/

@[expose] public section

namespace SicTest.Omega.Normalization

open Sic.Core SicTest.Omega.Syntax SicTest.Omega.Reduction

/-- `Ω` has no type. -/
theorem not_hasType_omega : ¬ Γ ⊢ omega p A : B := fun h =>
  have ⟨_, h⟩ := h.whnf
  not_termRedWhnf_omega h

end SicTest.Omega.Normalization
