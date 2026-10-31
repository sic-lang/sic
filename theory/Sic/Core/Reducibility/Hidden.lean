module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Conversion
import Sic.Core.Reducibility.Embedding
import Sic.Core.Reducibility.Symmetry
import Sic.Core.Reducibility.Transitivity
import Sic.Core.Reducibility.Uniqueness
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

ADE hide a proof of reducibility, which computes the interpretation, while the equalities here hide
the interpretation, which a proof of reducibility only describes.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

-- ADE: `_⊩⟨_⟩_≡_`, in `Definition/LogicalRelation/Hidden.agda`, and `_⊩⟨_⟩_` for a type equal to
-- itself, in `Definition/LogicalRelation.agda`.
/--
`Γ ⊩⟨l⟩ A ≡ B`: in the context `Γ`, the types `A` and `B` are reducible at the level `l`, and the
interpretation of `A` equates them.
-/
def ReducibleTypeEq (Γ : Con k n) (l : Nat) (A B : Term k n) : Prop :=
  ∃ P Q, (Γ ⊩⟨l⟩ A ▸ P) ∧ (Γ ⊩⟨l⟩ B ▸ Q) ∧ P.eqType B

-- ADE: `_⊩⟨_⟩_≡_∷_`, and `_⊩⟨_⟩_∷_` for a term equal to itself, in
-- `Definition/LogicalRelation/Hidden.agda`.
/--
`Γ ⊩⟨l⟩ t ≡ u : A`: in the context `Γ`, the type `A` is reducible at the level `l`, and its
interpretation equates the terms `t` and `u`.
-/
def ReducibleTermEq (Γ : Con k n) (l : Nat) (t u A : Term k n) : Prop :=
  ∃ P, (Γ ⊩⟨l⟩ A ▸ P) ∧ P.eqTerm t u

@[inherit_doc] notation:40 Γ:41 " ⊩⟨" l "⟩ " A:41 " ≡ " B:41 => ReducibleTypeEq Γ l A B

@[inherit_doc]
notation:40 Γ:41 " ⊩⟨" l "⟩ " t:41 " ≡ " u:41 " : " A:41 => ReducibleTermEq Γ l t u A

-- ADE: `sym-⊩≡`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two reducibly equal types are reducibly equal in the other order. -/
theorem ReducibleTypeEq.symm : (Γ ⊩⟨l⟩ A ≡ B) → Γ ⊩⟨l⟩ B ≡ A
  | ⟨_, _, hA, hB, hAB⟩ => ⟨_, _, hB, hA, hA.symm_eqType hB hAB⟩

-- ADE: `trans-⊩≡`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two types reducibly equal to the same type are reducibly equal. -/
theorem ReducibleTypeEq.trans : (Γ ⊩⟨l⟩ A ≡ B) → (Γ ⊩⟨l⟩ B ≡ C) → Γ ⊩⟨l⟩ A ≡ C
  | ⟨_, _, hA, hB, hAB⟩, ⟨_, _, hB', hC, hBC⟩ =>
    ⟨_, _, hA, hC, hA.trans_eqType hB hAB (hB'.unique hB ▸ hBC)⟩

-- ADE: `emb-⊩≡`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two types reducibly equal at a level are reducibly equal at every larger level. -/
theorem ReducibleTypeEq.emb (hl : l ≤ l') : (Γ ⊩⟨l⟩ A ≡ B) → Γ ⊩⟨l'⟩ A ≡ B
  | ⟨_, _, hA, hB, hAB⟩ => ⟨_, _, hA.emb hl, hB.emb hl, hAB⟩

-- ADE: `sym-⊩≡∷`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two reducibly equal terms are reducibly equal in the other order. -/
theorem ReducibleTermEq.symm : (Γ ⊩⟨l⟩ t ≡ u : A) → Γ ⊩⟨l⟩ u ≡ t : A
  | ⟨_, hA, htu⟩ => ⟨_, hA, hA.symm_eqTerm htu⟩

-- ADE: `trans-⊩≡∷`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two terms reducibly equal to the same term are reducibly equal. -/
theorem ReducibleTermEq.trans : (Γ ⊩⟨l⟩ t ≡ u : A) → (Γ ⊩⟨l⟩ u ≡ v : A) → Γ ⊩⟨l⟩ t ≡ v : A
  | ⟨_, hA, htu⟩, ⟨_, hA', huv⟩ => ⟨_, hA, hA.trans_eqTerm htu (hA'.unique hA ▸ huv)⟩

-- ADE: `conv-⊩≡∷`, in `Definition/LogicalRelation/Hidden.agda`.
/--
Two terms reducibly equal at a type are reducibly equal at every type reducibly equal to it, at the
level of that equality.
-/
theorem ReducibleTermEq.conv : (Γ ⊩⟨l⟩ t ≡ u : A) → (Γ ⊩⟨l'⟩ A ≡ B) → Γ ⊩⟨l'⟩ t ≡ u : B
  | ⟨_, hA, htu⟩, ⟨_, _, hA', hB, hAB⟩ =>
    ⟨_, hB, (hA'.conv_eqTerm hB hAB).mp (hA.unique hA' ▸ htu)⟩

-- ADE: `emb-⊩≡∷`, in `Definition/LogicalRelation/Hidden.agda`.
/-- Two terms reducibly equal at a level are reducibly equal at every larger level. -/
theorem ReducibleTermEq.emb (hl : l ≤ l') : (Γ ⊩⟨l⟩ t ≡ u : A) → Γ ⊩⟨l'⟩ t ≡ u : A
  | ⟨_, hA, htu⟩ => ⟨_, hA.emb hl, htu⟩

-- ADE: `wk-⊩≡∷`, in `Definition/LogicalRelation/Hidden.agda`.
/--
Two reducibly equal terms stay reducibly equal in every well-formed context that contains their own.
-/
theorem ReducibleTermEq.wk : (Γ ⊩⟨l⟩ t ≡ u : A) → ρ ∷ Δ ⊇ Γ → ⊢ Δ →
    Δ ⊩⟨l⟩ t.wk ρ ≡ u.wk ρ : A.wk ρ
  | ⟨_, hA, htu⟩, hρ, hΔ =>
    let ⟨_, hA'⟩ := hA.wk hρ hΔ
    ⟨_, hA', hA.wk_eqTerm hA' hρ hΔ htu⟩

end Sic.Core.Reducibility
