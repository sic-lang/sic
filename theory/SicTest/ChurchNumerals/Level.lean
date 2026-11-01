module

import Sic.Core.Level

/-!
# The Church Numerals: Levels

The level of the type of the Church numerals.
-/

@[expose] public section

namespace SicTest.ChurchNumerals.Level

open Sic.Core Sic.Core.Level

/--
The type `Nat_l` of the Church numerals, which `(Π)` puts at the level
`(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))`, lives at the level `l + 1`, above the types its numerals iterate
over, where the numerals of System F iterate over every type, their own included.
-/
example : (succ (var 0) ⊔ ((var 0 ⊔ var 0) ⊔ (var 0 ⊔ var 0)) : Level 1) ≈ succ (var 0) :=
  fun ρ => by simp only [eval_max, eval]; omega

end SicTest.ChurchNumerals.Level
