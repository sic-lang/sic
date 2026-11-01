module

import Sic.Core.TypeSort

/-!
# RFC 24: The Sort of a Type

The claim of the Rationale of RFC 24 on the equality of types.
-/

@[expose] public section

namespace SicTest.Rfc24.TypeSort

open Sic.Core

/--
The rules of the equality of types add no equality to those of the universes: two types are equal
exactly when they are equal terms of a universe.
-/
example : (Γ ⊢ A ≡ B) ↔ ∃ L, Γ ⊢ A ≡ B : Term.univ L :=
  ⟨TypeEq.sort, fun ⟨_, h⟩ => .univ h⟩

end SicTest.Rfc24.TypeSort
