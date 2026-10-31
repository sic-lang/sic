module

public import Sic.Core.Reduction
import Sic.Core.Injectivity
import Sic.Core.Inversion

/-!
# Neutral Types

The types of a neutral term are all equal, as in the formalizations of ADE and of Pujet: a variable
has the type of its declaration, and the application of a neutral term has the codomain of the
types of functions of the neutral term, which are equal, at the argument.

## Correspondence with the Formalizations of ADE and of Pujet

ADE and Pujet proceed by induction on the neutral term and on the two typings, while the proof here
inverts the typings, by `Sic.Core.Inversion`.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `neTypeEq`, in `Definition/Typed/Consequences/NeTypeEq.agda`.
-- Pujet: `neTypeEq`, in `Definition/Typed/Consequences/NeTypeEq.agda`.
/-- A neutral term has only equal types. -/
theorem Neutral.typeEq (hN : Neutral t) (h₁ : Γ ⊢ t : A) (h₂ : Γ ⊢ t : B) : Γ ⊢ A ≡ B := by
  induction hN generalizing A B with
  | var => exact h₁.inv_var.trans h₂.inv_var.symm
  | app _ ih =>
    have ⟨_, _, _, ht₁, ha, hA⟩ := h₁.inv_app
    have ⟨_, _, _, ht₂, _, hB⟩ := h₂.inv_app
    have ⟨_, _, _, hC⟩ := (ih ht₁ ht₂).pi_inj
    exact hA.trans ((hC.subst (.instantiate ha) ha.wfCon).trans hB.symm)

end Sic.Core
