module

import Sic.Core.WellFormed
import all Sic.Core.Typing.Validation

/-!
# Validation of the Well-Formedness

The syntactic validity of `Sic.Core.WellFormed` checked against the formalization of ADE, and on
the constant function of RFC 24.

| Theorem | Theorem of ADE, in `Definition/Typed/Well-formed.agda` |
| --- | --- |
| `HasType.wfType` | `wf-⊢∷` |
| `TermEq.wf` | `wf-⊢≡∷` |
-/

namespace Sic.Core.WellFormed.Validation

open Syntax.Validation Typing.Validation

/-- The type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of the constant function is a type. -/
example : ∃ l, Γ₂ ⊢ constantType : Term.univ l := hasType_constant.wfType

end Sic.Core.WellFormed.Validation
