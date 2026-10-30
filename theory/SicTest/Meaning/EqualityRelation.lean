module

import Sic.Core.EqualityRelation

/-!
# Meaning of the Equality Relations

The equality relation of `Sic.Core.Typing` is its equality.
-/

namespace SicTest.Meaning.EqualityRelation

open Sic.Core

/-- The equality relation of `Sic.Core.Typing` is its equality. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ≅ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

/-- Its equality of neutral terms is its equality too. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ~ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

end SicTest.Meaning.EqualityRelation
