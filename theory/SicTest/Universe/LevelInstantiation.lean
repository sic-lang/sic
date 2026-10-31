module

import Sic.Core.Injectivity
import Sic.Core.LevelInstantiation

/-!
# The Universes: Level Instantiation

Instantiating the level variables keeps a judgment, but the converse fails: a judgment may hold at
some levels only, so that a definition checked with its level variables holds at more levels than
one checked at a given level.
With two level variables `l₁` and `l₂`, `U_{l₁ ⊔ l₂}` equals `U_{l₁}` once `l₂` is `0`, but not
before.
-/

namespace SicTest.Universe.LevelInstantiation

open Sic.Core Sic.Core.Term

/-- The instantiation of `l₂` by `0`, which keeps `l₁`. -/
def secondToZero : Fin 2 → Level 2 := fun i => if i = 0 then .var 0 else .zero

/-- Once `l₂` is `0`, the universes `U_{l₁ ⊔ l₂}` and `U_{l₁}` are equal types. -/
example : (.empty : Con 2 0) ⊢ (univ (.var 0 ⊔ .var 1)).substLevels secondToZero ≡
    (univ (.var 0)).substLevels secondToZero :=
  .univ (.univ .empty fun _ => Nat.max_zero _)

/-- Before, they are not: `l₁ ⊔ l₂` and `l₁` differ when `l₁` is `0` and `l₂` is `1`. -/
example : ¬ (.empty : Con 2 0) ⊢ univ (.var 0 ⊔ .var 1) ≡ univ (.var 0) := fun h =>
  have ⟨_, e, hl⟩ := h.inv_univ .univ
  by cases e; exact absurd (hl fun i => i.val) (by decide)

end SicTest.Universe.LevelInstantiation
