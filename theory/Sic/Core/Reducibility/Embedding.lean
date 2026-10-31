module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# Embedding

The logical relation is cumulative: a type reducible at a level is reducible at every larger level,
with the same interpretation.

## Correspondence with the Formalization of ADE

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Properties/Embedding.agda` |
| --- | --- |
| `LogicalRelation.emb` | `emb-≤-⊩` |

The interpretation of a universe reads the relation at the level of the universe, whatever the
level of the relation that interprets it, so that the embedded type keeps its interpretation, where
ADE build a new proof of reducibility and transport the equalities to it, in their `emb-≤-⊩≡` and
`emb-≤-⊩≡∷`.
Pujet's relation has a single universe, and no such lemma.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/--
A type reducible at a level is reducible at every larger level, with the same interpretation.

A universe of a level smaller than the first level is smaller than the second, and the domain and
the codomain of a type of functions are embedded by the induction.
-/
theorem LogicalRelation.emb (hl : l ≤ l') (h : Γ ⊩⟨l⟩ A ▸ P) : Γ ⊩⟨l'⟩ A ▸ P := by
  rw [LogicalRelation.unfold] at h ⊢
  induction h with
  | univ hL hA => exact .univ (Nat.lt_of_lt_of_le hL hl) hA
  | ne hA hN hNN => exact .ne hA hN hNN
  | pi hA hPi PF PG _ _ hGext ihF ihG =>
    exact .pi hA hPi PF PG (fun hρ hΔ => ihF hρ hΔ) (fun hρ hΔ ha => ihG hρ hΔ ha) hGext

end Sic.Core.Reducibility
