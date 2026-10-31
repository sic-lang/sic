module

import Sic.Core.Syntax

/-!
# The Divergent Term Ω

The term `Ω = (λx. x x) (λx. x x)` of the untyped lambda calculus, which reduces to itself, so that
it has no normal form, `omega` of section 5.2 of [Pierce](https://www.cis.upenn.edu/~bcpierce/tapl/).
Its abstractions declare their variable of any type `A`, and their applications have any grade `p`.
-/

namespace SicTest.Omega.Syntax

open Sic Sic.Core Sic.Core.Term

/-- `ω = λ_p (x : A). x ∘_p x`, which applies its argument to itself. -/
def omegaHalf (p : Grade) (A : Term k n) : Term k n := lam p A (app p (var 0) (var 0))

/-- `Ω = ω ∘_p ω`, which applies `ω` to itself. -/
def omega (p : Grade) (A : Term k n) : Term k n := app p (omegaHalf p A) (omegaHalf p A)

end SicTest.Omega.Syntax
