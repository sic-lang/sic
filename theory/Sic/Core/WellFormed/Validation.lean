module

import Sic.Core.WellFormed
import all Sic.Core.Typing.Validation

/-!
# Validation of the Well-Formedness

The syntactic validity of `Sic.Core.WellFormed` checked against the formalization of ADE, on the
constant function of RFC 24, and on the examples of the literature.

| Theorem | Theorem of ADE, in `Definition/Typed/Well-formed.agda` |
| --- | --- |
| `HasType.wfType` | `wf-⊢∷` |
| `TermEq.wf` | `wf-⊢≡∷` |
-/

namespace Sic.Core.WellFormed.Validation

open Grade Syntax.Validation Term Typing.Validation

/-- The type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of the constant function is a type. -/
example : ∃ l, Γ₂ ⊢ constantType : Term.univ l := hasType_constant.wfType

/-- The type of `S` is a type. -/
example : ∃ l, (.empty : Con 1 0) ⊢ combinatorSType : Term.univ l :=
  (hasType_combinatorS .empty).wfType

/-- The type of `succ` is a type, in every well-formed context. -/
example (h : ⊢ Γ) : ∃ l, Γ ⊢ pi 𝟙 𝟘 churchNat churchNat : Term.univ l :=
  (hasType_churchSucc h).wfType

/-- The last type of a well-formed context is a type. -/
theorem wfCon_snoc_inv : ⊢ Γ ∙ A → ∃ l, Γ ⊢ A : Term.univ l
  | .snoc h => ⟨_, h⟩

/--
An abstraction has the type of functions whose body has its type, whatever the grade `q` of the
type: by syntactic validity, the domain and the codomain are types, which `(λ)` needs.
-/
theorem hasType_lam (ht : Γ ∙ A ⊢ t : B) : Γ ⊢ Term.lam p A t : Term.pi p q A B :=
  have ⟨_, hA⟩ := wfCon_snoc_inv ht.wfCon
  have ⟨_, hB⟩ := ht.wfType
  .lam (.pi hA hB) ht

end Sic.Core.WellFormed.Validation
