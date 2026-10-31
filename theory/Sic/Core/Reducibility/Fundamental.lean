module

public import Sic.Core.Reducibility.Validity
import Sic.Core.Reducibility.Introductions.Function
import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable

/-!
# Fundamental Lemma

Every judgment of `Sic.Core.Typing` is valid, as in the formalization of ADE: a well-formed context
is valid, and each other judgment is a valid equality at some level.
The proof is one induction on the five judgments, whose rules each follow from a theorem of
`Sic.Core.Reducibility.Validity` or of `Sic.Core.Reducibility.Introductions`.

## Correspondence with the Formalization of ADE

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Fundamental.agda` |
| --- | --- |
| `WfCon.valid` | `valid` |
| `IsType.valid` | `fundamental-⊩ᵛ` |
| `TypeEq.valid` | `fundamental-⊩ᵛ≡` |
| `HasType.valid` | `fundamental-⊩ᵛ∷` |
| `TermEq.valid` | `fundamental-⊩ᵛ≡∷` |

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

/-- A well-formed context is valid. -/
theorem WfCon.valid : ⊢ Γ → ⊩ᵛ Γ
  | .empty => ValidCon.unfold_empty ▸ trivial
  | .snoc hA => ValidCon.unfold_snoc ▸ hA.valid

/-- A type is valid, at some level. -/
theorem IsType.valid : Γ ⊢ A → ∃ l, Γ ⊩ᵛ⟨l⟩ A ≡ A
  | .univ hA => have ⟨_, hA⟩ := hA.valid; ⟨_, hA.toTypeEq⟩

/-- Two equal types are validly equal, at some level. -/
theorem TypeEq.valid : Γ ⊢ A ≡ B → ∃ l, Γ ⊩ᵛ⟨l⟩ A ≡ B
  | .univ hAB => have ⟨_, hAB⟩ := hAB.valid; ⟨_, hAB.toTypeEq⟩
  | .refl hA => hA.valid
  | .symm hAB => have ⟨_, hAB⟩ := hAB.valid; ⟨_, hAB.symm⟩
  | .trans h₁₂ h₂₃ =>
    have ⟨_, h₁₂⟩ := h₁₂.valid
    have ⟨_, h₂₃⟩ := h₂₃.valid
    ⟨_, (h₁₂.emb (Nat.le_max_left _ _)).trans (h₂₃.emb (Nat.le_max_right _ _))⟩

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

end Sic.Core
