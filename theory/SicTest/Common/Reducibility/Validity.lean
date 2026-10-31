module

import Sic.Core.Reducibility.Validity

/-!
# Common Consequences of the Validity

The consequences of `Sic.Core.Reducibility.Validity` that the checks of the precision of the
validity use.
-/

namespace SicTest.Common.Reducibility.Validity

open Sic.Core Sic.Core.Reducibility

variable [EqualityRelation]

/--
A valid equality of two types holds reducibly in their context, under the identity substitution,
which is reducible since the context is valid.
-/
theorem reducibleTypeEq_of_validTypeEq (h : Γ ⊩ᵛ⟨l⟩ A ≡ B) : Γ ⊩⟨l⟩ A ≡ B := by
  rw [ValidTypeEq.unfold] at h
  have h := h.2 (ReducibleSubstEq.var h.1)
  rwa [Term.subst_var, Term.subst_var] at h

end SicTest.Common.Reducibility.Validity
