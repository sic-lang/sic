module

public import Sic.Core.WellFormed

/-!
# Common Consequences of the Well-Formedness

The consequences of `Sic.Core.WellFormed` that the reductions of the examples use.
-/

@[expose] public section

namespace SicTest.Common.WellFormed

open Sic.Core

/-- The last type of a well-formed context is a term of a universe. -/
theorem wfCon_snoc_inv : ⊢ Γ ∙ A → ∃ l, Γ ⊢ A : Term.univ l
  | .snoc h => h.sort

/--
An abstraction has the type of functions whose body has its type, whatever the grade `q` of the
type: by syntactic validity, the domain and the codomain are types, which `(λ)` needs.
-/
theorem hasType_lam (ht : Γ ∙ A ⊢ t : B) : Γ ⊢ Term.lam p A t : Term.pi p q A B :=
  have ⟨_, hA⟩ := wfCon_snoc_inv ht.wfCon
  have ⟨_, hB⟩ := ht.wfType.sort
  .lam (.univ (.pi hA hB)) ht

end SicTest.Common.WellFormed
