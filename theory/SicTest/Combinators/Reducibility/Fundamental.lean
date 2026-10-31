module

import Sic.Core.Reducibility.Fundamental
import all SicTest.Combinators.Reduction
import all SicTest.Combinators.Syntax
import all SicTest.Combinators.Typing

/-!
# The Combinators K and S: Fundamental Lemma

The equality of `S K K` and of the identity `λ_𝟙 (z : A). z` of `Sic.Core.Typing` is valid, and so
holds reducibly, for every equality relation, as the fundamental lemma says of every judgment.
-/

namespace SicTest.Combinators.Reducibility.Fundamental

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility SicTest.Combinators.Reduction
  SicTest.Combinators.Syntax SicTest.Combinators.Typing

variable [EqualityRelation]

/-- `S K K` and `λ_𝟙 (z : A). z` are validly equal terms of `Π^𝟘_𝟙 (z : A). A`. -/
example : ∃ l, ΓA ⊩ᵛ⟨l⟩ skk ≡ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  skk_termEq.valid

/-- `S K K` and `λ_𝟙 (z : A). z` are reducibly equal terms of `Π^𝟘_𝟙 (z : A). A`. -/
example : ∃ l, ΓA ⊩⟨l⟩ skk ≡ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  skk_termEq.reducible

end SicTest.Combinators.Reducibility.Fundamental
