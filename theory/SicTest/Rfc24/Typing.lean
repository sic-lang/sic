module

public import Sic.Core.Typing

/-!
# RFC 24: Typing

The claims of RFC 24 on its judgments.
-/

@[expose] public section

namespace SicTest.Rfc24.Typing

open Sic.Core

/--
The symmetry of the equality of types follows from the other rules, as the Rationale of RFC 24
states: the proof never uses `TypeEq.symm`, which its case only unfolds, and turns each equality of
terms of a universe around with the symmetry of the equality of terms.
-/
theorem typeEq_symm : Γ ⊢ A ≡ B → Γ ⊢ B ≡ A
  | .univ h => .univ (.symm h)
  | .refl h => .refl h
  | .symm h => h
  | .trans h₁ h₂ => .trans (typeEq_symm h₂) (typeEq_symm h₁)

end SicTest.Rfc24.Typing
