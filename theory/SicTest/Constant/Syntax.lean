module

import Sic.Core.Syntax

/-!
# The Constant Function

The constant function of RFC 24, written as a term of `Sic.Core.Syntax`.
-/

namespace SicTest.Constant.Syntax

open Sic.Core Sic.Grade Sic.Core.Term

/-!
The constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` and its type
`Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, in the context `A : U₀, B : U₀` of two type variables.
The index of a variable is the number of variables declared after it and in scope where it is used,
those of the context included:

- `A`, the type of `x`, is `var 1`, since `B` is declared after it;
- `B`, the type of `y`, is `var 1`, since `x` is declared after it;
- `x`, the body of the function, is `var 1`, since `y` is declared after it;
- `A`, the type of the body, is `var 3`, since `B`, `x` and `y` are declared after it.
-/

def constant : Term 0 2 := lam 𝟙 (var 1) (lam 𝟘 (var 1) (var 1))

def constantType : Term 0 2 := pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))

end SicTest.Constant.Syntax
