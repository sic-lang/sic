module

public import Sic.Core.Reducibility.Validity
import Sic.Core.Reducibility.Introductions.Function
import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable

/-!
# Fundamental Lemma

Every judgment of `Sic.Core.Typing` is valid, as in the formalization of ADE: a well-formed context
is valid, and each other judgment is a valid equality at some level, so that it holds reducibly in its
own context.
The proof is one induction on the five judgments, whose rules each follow from a theorem of
`Sic.Core.Reducibility.Validity` or of `Sic.Core.Reducibility.Introductions`.

## Correspondence with the Formalization of ADE

ADE name each theorem by the lemma, while those here are named by what they conclude, as the other
properties of the judgments, such as `HasType.wfCon`.
-/

@[expose] public section

namespace Sic.Core

open Reducibility

variable [EqualityRelation]

/-!
The validities of a judgment may be at different levels in its premises, while `ValidTypeEq.trans`
and `ValidTermEq.trans` take them at the same level: they move to the larger one, which
`ValidTypeEq.emb` and `ValidTermEq.emb` allow.
The rule `(λ)` gives no equality of the type of the argument as a term of a universe, which
`ValidTermEq.lam` takes from `Sic.Core.Typing`: the inversion of the type of functions gives it.
-/

mutual

-- ADE: `valid`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- A well-formed context is valid. -/
theorem WfCon.valid : ⊢ Γ → ⊩ᵛ Γ
  | .empty => ValidCon.unfold_empty ▸ trivial
  | .snoc hA => ValidCon.unfold_snoc ▸ hA.valid

-- ADE: `fundamental-⊩ᵛ`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- A type is valid, at some level. -/
theorem IsType.valid : Γ ⊢ A → ∃ l, Γ ⊩ᵛ⟨l⟩ A ≡ A
  | .univ hA => have ⟨_, hA⟩ := hA.valid; ⟨_, hA.toTypeEq⟩

-- ADE: `fundamental-⊩ᵛ≡`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- Two equal types are validly equal, at some level. -/
theorem TypeEq.valid : Γ ⊢ A ≡ B → ∃ l, Γ ⊩ᵛ⟨l⟩ A ≡ B
  | .univ hAB => have ⟨_, hAB⟩ := hAB.valid; ⟨_, hAB.toTypeEq⟩
  | .refl hA => hA.valid
  | .symm hAB => have ⟨_, hAB⟩ := hAB.valid; ⟨_, hAB.symm⟩
  | .trans h₁₂ h₂₃ =>
    have ⟨_, h₁₂⟩ := h₁₂.valid
    have ⟨_, h₂₃⟩ := h₂₃.valid
    ⟨_, (h₁₂.emb (Nat.le_max_left _ _)).trans (h₂₃.emb (Nat.le_max_right _ _))⟩

-- ADE: `fundamental-⊩ᵛ∷`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- A term of a type is valid, at some level. -/
theorem HasType.valid : Γ ⊢ t : A → ∃ l, Γ ⊩ᵛ⟨l⟩ t ≡ t : A
  | .var hΓ => ValidTermEq.var hΓ.valid _
  | .conv ht hAB =>
    have ⟨_, ht⟩ := ht.valid
    have ⟨_, hAB⟩ := hAB.valid
    ⟨_, ht.conv hAB⟩
  | .univ hΓ => ⟨_, ValidTermEq.univ hΓ.valid (.refl _)⟩
  | .pi hA hB =>
    have ⟨_, hA⟩ := hA.valid
    have ⟨_, hB⟩ := hB.valid
    ⟨_, ValidTermEq.pi hA hB⟩
  | .lam hPi ht =>
    have ⟨⟨_, hA⟩, _⟩ := hPi.inv_pi
    have ⟨_, hPi⟩ := hPi.valid
    have ⟨_, ht⟩ := ht.valid
    ⟨_, ValidTermEq.lam hPi (.refl hA) ht⟩
  | .app ht ha =>
    have ⟨_, ht⟩ := ht.valid
    have ⟨_, ha⟩ := ha.valid
    ⟨_, ValidTermEq.app ht ha⟩

-- ADE: `fundamental-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- Two equal terms of a type are validly equal, at some level. -/
theorem TermEq.valid : Γ ⊢ t ≡ u : A → ∃ l, Γ ⊩ᵛ⟨l⟩ t ≡ u : A
  | .refl ht => ht.valid
  | .symm htu => have ⟨_, htu⟩ := htu.valid; ⟨_, htu.symm⟩
  | .trans h₁₂ h₂₃ =>
    have ⟨_, h₁₂⟩ := h₁₂.valid
    have ⟨_, h₂₃⟩ := h₂₃.valid
    ⟨_, (h₁₂.emb (Nat.le_max_left _ _)).trans (h₂₃.emb (Nat.le_max_right _ _))⟩
  | .conv htu hAB =>
    have ⟨_, htu⟩ := htu.valid
    have ⟨_, hAB⟩ := hAB.valid
    ⟨_, htu.conv hAB⟩
  | .univ hΓ hL => ⟨_, ValidTermEq.univ hΓ.valid hL⟩
  | .pi hA hB =>
    have ⟨_, hA⟩ := hA.valid
    have ⟨_, hB⟩ := hB.valid
    ⟨_, ValidTermEq.pi hA hB⟩
  | .lam hPi hA ht =>
    have ⟨_, hPi⟩ := hPi.valid
    have ⟨_, ht⟩ := ht.valid
    ⟨_, ValidTermEq.lam hPi hA ht⟩
  | .app ht ha =>
    have ⟨_, ht⟩ := ht.valid
    have ⟨_, ha⟩ := ha.valid
    ⟨_, ValidTermEq.app ht ha⟩
  | .beta hPi ht ha =>
    have ⟨_, hPi⟩ := hPi.valid
    have ⟨_, ht⟩ := ht.valid
    have ⟨_, ha⟩ := ha.valid
    ⟨_, ValidTermEq.beta hPi ht ha⟩
  | .eta ht => have ⟨_, ht⟩ := ht.valid; ⟨_, ValidTermEq.eta ht⟩

end

/-!
Every judgment holds reducibly in its own context, since it is valid, and a valid judgment holds
reducibly under the identity substitution.
-/

-- ADE: `reducible-⊩`, in `Definition/LogicalRelation/Fundamental/Reducibility.agda`.
/-- A type is reducible, at some level. -/
theorem IsType.reducible (h : Γ ⊢ A) : ∃ l, Γ ⊩⟨l⟩ A ≡ A :=
  have ⟨_, h⟩ := h.valid; ⟨_, h.reducible⟩

-- ADE: `reducible-⊩≡`, in `Definition/LogicalRelation/Fundamental/Reducibility.agda`.
/-- Two equal types are reducibly equal, at some level. -/
theorem TypeEq.reducible (h : Γ ⊢ A ≡ B) : ∃ l, Γ ⊩⟨l⟩ A ≡ B :=
  have ⟨_, h⟩ := h.valid; ⟨_, h.reducible⟩

-- ADE: `reducible-⊩∷`, in `Definition/LogicalRelation/Fundamental/Reducibility.agda`.
/-- A term of a type is reducible, at some level. -/
theorem HasType.reducible (h : Γ ⊢ t : A) : ∃ l, Γ ⊩⟨l⟩ t ≡ t : A :=
  have ⟨_, h⟩ := h.valid; ⟨_, h.reducible⟩

-- ADE: `reducible-⊩≡∷`, in `Definition/LogicalRelation/Fundamental/Reducibility.agda`.
/-- Two equal terms of a type are reducibly equal, at some level. -/
theorem TermEq.reducible (h : Γ ⊢ t ≡ u : A) : ∃ l, Γ ⊩⟨l⟩ t ≡ u : A :=
  have ⟨_, h⟩ := h.valid; ⟨_, h.reducible⟩

end Sic.Core
