module

import Sic.Core.EqualityRelation

/-!
# Meaning of the Equality Relations

The equality relation of `Sic.Core.Typing` is its equality, for types and for terms.
-/

namespace SicTest.Meaning.EqualityRelation

open Sic.Core

/-- The equality of types of the equality relation of `Sic.Core.Typing` is its equality of types. -/
example (Γ : Con k n) (A B : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ A ≅ B) ↔ Γ ⊢ A ≡ B :=
  Iff.rfl

/-- Its equality of terms is its equality of terms. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ≅ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

/-- Its equality of neutral terms is its equality too. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ~ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

end SicTest.Meaning.EqualityRelation
