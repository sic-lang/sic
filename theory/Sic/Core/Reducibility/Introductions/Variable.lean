module

public import Sic.Core.Reducibility.Validity

/-!
# Variables

The variables of a valid context are valid terms of their types, so that the fundamental lemma
covers the rule `(var)` of `Sic.Core.Typing`.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Substitution/Introductions/Var.agda` | Of Pujet, in `Definition/LogicalRelation/Fundamental.agda` |
| --- | --- | --- |
| `ValidTermEq.var` | `varᵛ` | `fundamentalVar` |
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

variable [EqualityRelation]

/--
Each variable of a valid context is a valid term of its type, at some level.

Two reducibly equal substitutions replace the last variable by two terms reducibly equal at its
type, at the level of the validity of that type in the context, and the other variables are the
variables of the rest of the context, moved past the last one.
-/
theorem ValidTermEq.var : ∀ {Γ : Con k n}, (⊩ᵛ Γ) → ∀ x, ∃ l, Γ ⊩ᵛ⟨l⟩ var x ≡ var x : Γ.get x
  | .snoc _ A, hΓA, ⟨0, _⟩ => by
    rw [ValidCon.unfold_snoc] at hΓA
    have ⟨l, hA⟩ := hΓA
    refine ⟨l, hA.wk1 hA, fun hσ => ?_⟩
    rw [ReducibleSubstEq.unfold_snoc] at hσ
    have ⟨⟨_, _, ha⟩, hσ⟩ := hσ
    rw [ValidTypeEq.unfold] at hA
    show _ ⊩⟨l⟩ _ ≡ _ : A.wk1.subst _
    rw [subst_wk]
    exact ha.conv (hA.2 hσ.left)
  | .snoc Γ _, hΓA, ⟨x + 1, h⟩ => by
    rw [ValidCon.unfold_snoc] at hΓA
    have ⟨_, hA⟩ := hΓA
    have hΓ : ⊩ᵛ Γ := by rw [ValidTypeEq.unfold] at hA; exact hA.1
    have ⟨l, hx⟩ := ValidTermEq.var hΓ ⟨x, Nat.lt_of_succ_lt_succ h⟩
    exact ⟨l, hx.wk1 hA⟩

end Sic.Core.Reducibility
