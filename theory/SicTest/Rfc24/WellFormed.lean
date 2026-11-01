module

import Sic.Core.WellFormed

/-!
# RFC 24: Well-Formedness

The claims of RFC 24 on the well-formedness of its judgments.
-/

@[expose] public section

namespace SicTest.Rfc24.WellFormed

open Sic.Core

/--
The reflexivity of the equality of types follows from the other rules, as the Rationale of RFC 24
states: a type is a term of a universe, equal to itself there, which `(U_type≡)` makes an equality
of types, without `TypeEq.refl`.
-/
example (h : Γ ⊢ A) : Γ ⊢ A ≡ A :=
  have ⟨_, hA⟩ := h.sort
  .univ (.refl hA)

end SicTest.Rfc24.WellFormed
