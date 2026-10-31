module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Weakening

/-!
# Hidden Interpretations

The equalities of the logical relation that do not name the interpretation of their type, as in the
formalization of ADE: two types are reducibly equal when both are reducible and the interpretation
of the first equates them, and two terms are reducibly equal at a type when the interpretation of
that type equates them.
A type is reducible when it is reducibly equal to itself, and a term is reducible when it is
reducibly equal to itself.
The interpretation of a reducible type is unique, so that the choice of the interpretation that
these equalities hide does not matter.

## Correspondence with the Formalization of ADE

| Definition or theorem | Definition or theorem of ADE, in `Definition/LogicalRelation/Hidden.agda` |
| --- | --- |
| `ReducibleTypeEq` | `_⊩⟨_⟩_≡_`, and `_⊩⟨_⟩_` for a type equal to itself |
| `ReducibleTermEq` | `_⊩⟨_⟩_≡_∷_`, and `_⊩⟨_⟩_∷_` for a term equal to itself |
| `ReducibleTermEq.wk` | `wk-⊩≡∷` |

ADE hide a proof of reducibility, which computes the interpretation, while the equalities here hide
the interpretation, which a proof of reducibility only describes.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/--
`Γ ⊩⟨l⟩ A ≡ B`: in the context `Γ`, the types `A` and `B` are reducible at the level `l`, and the
interpretation of `A` equates them.
-/
def ReducibleTypeEq (Γ : Con k n) (l : Nat) (A B : Term k n) : Prop :=
  ∃ P Q, (Γ ⊩⟨l⟩ A ▸ P) ∧ (Γ ⊩⟨l⟩ B ▸ Q) ∧ P.eqType B

/--
`Γ ⊩⟨l⟩ t ≡ u : A`: in the context `Γ`, the type `A` is reducible at the level `l`, and its
interpretation equates the terms `t` and `u`.
-/
def ReducibleTermEq (Γ : Con k n) (l : Nat) (t u A : Term k n) : Prop :=
  ∃ P, (Γ ⊩⟨l⟩ A ▸ P) ∧ P.eqTerm t u

@[inherit_doc] notation:40 Γ:41 " ⊩⟨" l "⟩ " A:41 " ≡ " B:41 => ReducibleTypeEq Γ l A B

@[inherit_doc]
notation:40 Γ:41 " ⊩⟨" l "⟩ " t:41 " ≡ " u:41 " : " A:41 => ReducibleTermEq Γ l t u A

/--
Two reducibly equal terms stay reducibly equal in every well-formed context that contains their own.
-/
theorem ReducibleTermEq.wk : (Γ ⊩⟨l⟩ t ≡ u : A) → ρ ∷ Δ ⊇ Γ → ⊢ Δ →
    Δ ⊩⟨l⟩ t.wk ρ ≡ u.wk ρ : A.wk ρ
  | ⟨_, hA, htu⟩, hρ, hΔ =>
    let ⟨_, hA'⟩ := hA.wk hρ hΔ
    ⟨_, hA', hA.wk_eqTerm hA' hρ hΔ htu⟩

end Sic.Core.Reducibility
