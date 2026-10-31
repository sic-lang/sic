module

import Sic.Core.Reducibility.Fundamental
import all SicTest.ChurchNumerals.Reduction
import all SicTest.ChurchNumerals.Syntax

/-!
# The Church Numerals: Fundamental Lemma

The equality `succ ∘_𝟙 1 ≡ 2 : Nat_l` of `Sic.Core.Typing` is valid, and so holds reducibly, for
every equality relation, as the fundamental lemma says of every judgment.
-/

namespace SicTest.ChurchNumerals.Reducibility.Fundamental

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility SicTest.ChurchNumerals.Reduction
  SicTest.ChurchNumerals.Syntax

variable [EqualityRelation]

/-- `succ ∘_𝟙 1` and `2` are validly equal terms of `Nat_l`. -/
example : ∃ l, (.empty : Con 1 0) ⊩ᵛ⟨l⟩ app 𝟙 churchSucc churchOne ≡ churchTwo : churchNat :=
  churchSucc_one_termEq.valid

/-- `succ ∘_𝟙 1` and `2` are reducibly equal terms of `Nat_l`. -/
example : ∃ l, (.empty : Con 1 0) ⊩⟨l⟩ app 𝟙 churchSucc churchOne ≡ churchTwo : churchNat :=
  churchSucc_one_termEq.reducible

end SicTest.ChurchNumerals.Reducibility.Fundamental
