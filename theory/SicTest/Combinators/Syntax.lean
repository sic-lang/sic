module

public import Sic.Core.Syntax

/-!
# The Combinators K and S

The combinators `K` and `S` of combinatory logic, where `S K K` behaves as the identity, exercise
2.16 of [Hindley and Seldin](https://doi.org/10.1017/CBO9780511809835).
Both are closed, over the level variable `l`, which is `var 0`, and are terms over any number of
variables, so that they can be used in any context.
`𝟙 + 𝟙` is the grade of any number of uses.
-/

@[expose] public section

namespace SicTest.Combinators.Syntax

open Sic.Core Sic.Grade Sic.Core.Term

/--
`K = λ_𝟘 (A : U_l). λ_𝟘 (B : U_l). λ_𝟙 (x : A). λ_𝟘 (y : B). x`, polymorphic: its variables have the
indices of those of the constant function.
-/
def combinatorK : Term 1 n :=
  lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 1) (lam 𝟘 (var 1) (var 1))))

/-- `Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, the type of `K`. -/
def combinatorKType : Term 1 n :=
  pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))))

/-!
`S = λ_𝟘 (A : U_l). λ_𝟘 (B : U_l). λ_𝟘 (C : U_l). λ_𝟙 (x : Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C).
λ_𝟘 (y : Π^𝟘_𝟙 (a : A). B). λ_𝟙 (z : A). (x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)`, of the type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^{𝟙 + 𝟙}_𝟘 (B : U_l). Π^{𝟙 + 𝟙}_𝟘 (C : U_l).
Π^𝟘_𝟙 (x : Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C). Π^𝟘_𝟘 (y : Π^𝟘_𝟙 (a : A). B).
Π^𝟘_𝟙 (z : A). C`.
Its grades are ours, those that `S K K` needs: `K` does not use its second argument, so that `x`
takes its own with the grade `𝟘`, and `y`, and the second use of `z`, are erased, so that `z` is
used once at run time, while the untyped `S` duplicates it.
The indices of its variables:

- in the type of `x`, `A`, `B` and `C` are each `var 2`, after `B` and `C`, `C` and `a`, and `a`
  and `b`;
- in the type of `y`, `A` and `B` are each `var 3`, after `B`, `C` and `x`, and `C`, `x` and `a`;
- `A`, the type of `z`, is `var 4`, after `B`, `C`, `x` and `y`, and `C`, the type of the body, is
  `var 3`, after `x`, `y` and `z`;
- in the body, `x`, `y` and `z` are `var 2`, `var 1` and `var 0`.
-/

/-- `S`, with the grades and the indices above. -/
def combinatorS : Term 1 n :=
  lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0)) (lam 𝟘 (univ (.var 0))
    (lam 𝟙 (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2))) (lam 𝟘 (pi 𝟙 𝟘 (var 3) (var 3))
      (lam 𝟙 (var 4) (app 𝟘 (app 𝟙 (var 2) (var 0)) (app 𝟙 (var 1) (var 0))))))))

/-- The type of `S` above. -/
def combinatorSType : Term 1 n :=
  pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 (𝟙 + 𝟙) (univ (.var 0)) (pi 𝟘 (𝟙 + 𝟙) (univ (.var 0))
    (pi 𝟙 𝟘 (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2))) (pi 𝟘 𝟘 (pi 𝟙 𝟘 (var 3) (var 3))
      (pi 𝟙 𝟘 (var 4) (var 3))))))

end SicTest.Combinators.Syntax
