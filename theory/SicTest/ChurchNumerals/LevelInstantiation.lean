module

public import SicTest.ChurchNumerals.Typing
import Sic.Core.LevelInstantiation
import SicTest.ChurchNumerals.Syntax

/-!
# The Church Numerals: Level Instantiation

The numerals of level `l + 1`, which iterate over the types of `U_{l + 1}`, `Nat_l` among them, are
those of level `l` instantiated: their derivations are those of level `l`, instantiated.
-/

@[expose] public section

namespace SicTest.ChurchNumerals.LevelInstantiation

open Sic.Core Sic.Grade Sic.Core.Term SicTest.ChurchNumerals.Syntax SicTest.ChurchNumerals.Typing

/-- The instantiation of `l` by `l + 1`. -/
def toSucc : Fin 1 → Level 1 := fun _ => .succ (.var 0)

/-- Instantiated, `Nat_l` is `Nat_{l + 1}`, whose type argument ranges over `U_{l + 1}`. -/
example : (churchNat : Term 1 0).substLevels toSucc =
    pi 𝟘 (𝟙 + 𝟙) (univ (.succ (.var 0))) (pi (𝟙 + 𝟙) 𝟘 churchFunType (pi 𝟙 𝟘 (var 1) (var 2))) :=
  rfl

/-- `Nat_{l + 1}` is a type of the level `(l + 2) ⊔ ((l + 1 ⊔ l + 1) ⊔ (l + 1 ⊔ l + 1))`. -/
example : (.empty : Con 1 0) ⊢ churchNat.substLevels toSucc :
    univ (.succ (.succ (.var 0)) ⊔ ((.succ (.var 0) ⊔ .succ (.var 0)) ⊔
      (.succ (.var 0) ⊔ .succ (.var 0)))) :=
  (hasType_churchNat .empty).substLevels toSucc

/-- `2` of level `l + 1` has the type `Nat_{l + 1}`. -/
example : (.empty : Con 1 0) ⊢ churchTwo.substLevels toSucc : churchNat.substLevels toSucc :=
  (hasType_churchTwo .empty).substLevels toSucc

end SicTest.ChurchNumerals.LevelInstantiation
