module

import Sic.Core.EqualityRelation

/-!
# Validation of the Equality Relations

The equality relations of `Sic.Core.EqualityRelation` checked against the formalization of ADE, and
the equality of `Sic.Core.Typing` as one of them.

| Field | Field of ADE's `Equality-relations`, in `Definition/Typed/EqualityRelation.agda` |
| --- | --- |
| `eq` | `_⊢_≅_∷_` |
| `eqNeutral` | `_⊢_~_∷_` |
| `ofNeutral` | `~-to-≅ₜ` |
| `termEq` | `≅ₜ-eq` |
| `symm`, `symmNeutral` | `≅ₜ-sym`, `~-sym` |
| `trans`, `transNeutral` | `≅ₜ-trans`, `~-trans` |
| `conv`, `convNeutral` | `≅-conv`, `~-conv` |
| `wk`, `wkNeutral` | `≅ₜ-wk`, `~-wk` |
| `red` | `≅ₜ-red` |
| `univ` | `≅ₜ-U-cong` |
| `pi` | `≅ₜ-ΠΣ-cong` |
| `eta` | `≅-η-eq` |
| `var` | `~-var` |
| `app` | `~-app` |

| Definition or theorem | Definition or theorem of ADE |
| --- | --- |
| `EqualityRelation.termEqRelation` | `eqRelInstance`, in `Definition/Typed/EqRelInstance.agda` |

ADE also have an equality of types `_⊢_≅_`, with the fields that relate it to the equality of terms,
which the equality of terms at a universe replaces here, as the equality of types does in
`Sic.Core.Typing`.
Their `≅ₜ-ΠΣ-cong` relates a domain and a codomain in the same universe, which their `Lift` moves
types to, while `pi` takes the larger of their levels, as `(Π)` does.
Their `≅-η-eq` relates functions that are abstractions or neutral terms, `Function⁺`, while `eta`
relates weak head normal forms, which are the same at a type of functions.
The fields of their other types, of their levels, and of their option `Var-included` are not here.
-/

namespace Sic.Core.EqualityRelation.Validation

/-- The equality relation of `Sic.Core.Typing` is its equality. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ≅ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

/-- Its equality of neutral terms is its equality too. -/
example (Γ : Con k n) (t u A : Term k n) :
    (letI := EqualityRelation.termEqRelation; Γ ⊢ t ~ u : A) ↔ Γ ⊢ t ≡ u : A :=
  Iff.rfl

end Sic.Core.EqualityRelation.Validation
