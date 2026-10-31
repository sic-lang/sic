module

import Sic.Core.LevelInstantiation
import all SicTest.Identity.Syntax
import all SicTest.Identity.Typing

/-!
# The Polymorphic Identity: Level Instantiation

The polymorphic identity, checked once over its level variable `l`, is the identity of the types of
every level: its derivation instantiated gives the identity of `U_0`, with no derivation of its own.
-/

namespace SicTest.Identity.LevelInstantiation

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax SicTest.Identity.Typing

/-- The instantiation of `l` by `0`, over no level variable. -/
def toZero : Fin 1 → Level 0 := fun _ => .zero

/-- Instantiated at `0`, the identity is `λ_𝟘 (A : U_0). λ_𝟙 (x : A). x`. -/
example : identity.substLevels toZero = lam 𝟘 (univ .zero) (lam 𝟙 (var 0) (var 0)) := rfl

/-- The identity of `U_0` has the type `Π^{𝟙 + 𝟙}_𝟘 (A : U_0). Π^𝟘_𝟙 (x : A). A`. -/
example : (.empty : Con 0 0) ⊢ lam 𝟘 (univ .zero) (lam 𝟙 (var 0) (var 0)) :
    pi 𝟘 (𝟙 + 𝟙) (univ .zero) (pi 𝟙 𝟘 (var 0) (var 1)) :=
  hasType_identity.substLevels toZero

end SicTest.Identity.LevelInstantiation
