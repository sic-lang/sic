module

import Sic.Core.Substitution
import all SicTest.Identity.Syntax

/-!
# The Polymorphic Identity: Substitution

The polymorphic identity instantiated at a level.
-/

namespace SicTest.Identity.Substitution

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Identity.Syntax

/-- The polymorphic identity, over the level variable `l`, instantiated at the level `0`. -/
example : identityType.substLevels (fun _ => (.zero : Level 0)) =
    pi 𝟘 (𝟙 + 𝟙) (univ .zero) (pi 𝟙 𝟘 (var 0) (var 1)) := rfl

end SicTest.Identity.Substitution
