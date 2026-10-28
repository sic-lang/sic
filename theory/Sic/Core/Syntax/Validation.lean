module

import Sic.Core.Syntax

/-!
# Validation of the Syntax

The examples of RFC 24 written as terms of `Sic.Core.Syntax`, each with the named term of the RFC.
-/

namespace Sic.Core.Syntax.Validation

open Grade Term

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

/-!
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` and its type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A`, closed, over the level variable `l`, which is `var 0`.
-/

def identity : Term 1 0 := lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 0) (var 0))

def identityType : Term 1 0 := pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟙 𝟘 (var 0) (var 1))

/--
Two types of functions that differ only by a grade are different types, as `Π^𝟘_𝟙 (x : A). A` and
`Π^𝟘_{𝟙 + 𝟙} (x : A). A`, in the context `A : U₀`.
-/
example : pi 𝟙 𝟘 (var 0) (var 1) ≠ (pi (𝟙 + 𝟙) 𝟘 (var 0) (var 1) : Term 0 1) := by decide

end Sic.Core.Syntax.Validation
