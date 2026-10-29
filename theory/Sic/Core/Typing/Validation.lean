module

import Sic.Core.Typing
import all Sic.Core.Syntax.Validation

/-!
# Validation of the Typing

The judgments of `Sic.Core.Typing` checked against RFC 24 and against the formalization of ADE.

| Rule of RFC 24 | Constructor | Rule of ADE, in `Definition/Typed.agda` |
| --- | --- | --- |
| `(ctx_ε)`, `(ctx_,)` | `WfCon.empty`, `WfCon.snoc` | `ε`, `∙_` of `_»⊢_` |
| `(var)` | `HasType.var` | `var`, with `_∷_∈_` |
| `(conv)` | `HasType.conv` | `conv` of `_⊢_∷_` |
| `(univ)` | `HasType.univ` | `Uⱼ` |
| `(Π)` | `HasType.pi` | `ΠΣⱼ` of `_⊢_∷_` |
| `(λ)` | `HasType.lam` | `lamⱼ` |
| `(∘)` | `HasType.app` | `_∘ⱼ_` |
| `(refl)`, `(sym)`, `(trans)` | `TermEq.refl`, `TermEq.symm`, `TermEq.trans` | `refl`, `sym`, `trans` of `_⊢_≡_∷_` |
| `(conv_≡)` | `TermEq.conv` | `conv` of `_⊢_≡_∷_` |
| `(univ_≡)` | `TermEq.univ` | `U-cong` |
| Congruences | `TermEq.pi`, `TermEq.lam`, `TermEq.app` | `ΠΣ-cong`, none, `app-cong` |
| `(β)` | `TermEq.beta` | `β-red` |
| `(η)` | `TermEq.eta` | `η-eq` |

ADE have five judgments, with two for the types, `Γ ⊢ A` and `Γ ⊢ A ≡ B`, which RFC 24 replaces by
the typing and the equality of a term in a universe.
Their abstraction does not carry the type of its argument, so that they have no congruence of
abstraction, and state `η` as the equality of two functions whose applications to a variable are
equal.
-/

namespace Sic.Core.Typing.Validation

open Grade Syntax.Validation Term

/-! The examples of RFC 24, as derivations. -/

/-- The context `A : U₀, B : U₀` of the constant function. -/
def Γ₂ : Con 0 2 := .empty ∙ univ .zero ∙ univ .zero

theorem wfCon_Γ₂ : ⊢ Γ₂ := .snoc (.univ (.snoc (.univ .empty)))

/--
The constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` has the type
`Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`.
-/
theorem hasType_constant : Γ₂ ⊢ constant : constantType :=
  -- `A : U₀` in `Γ₂`, `B : U₀` after `x : A`, and `A : U₀` after `y : B`.
  have hA : Γ₂ ⊢ var 1 : univ .zero := .var wfCon_Γ₂
  have hB : Γ₂ ∙ var 1 ⊢ var 1 : univ .zero := .var (.snoc hA)
  have hA' : Γ₂ ∙ var 1 ∙ var 1 ⊢ var 3 : univ .zero := .var (.snoc hB)
  have hPi := HasType.pi hB hA'
  .lam (.pi hA hPi) (.lam hPi (.var (.snoc hB)))

/--
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` has the type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A` in the empty context, with its level variable `l`.
-/
theorem hasType_identity : .empty ⊢ identity : identityType :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`.
  have hU : (.empty : Con 1 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ .empty
  have hA : .empty ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc hU)
  have hA' : .empty ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hPi := HasType.pi hA hA'
  .lam (.pi hU hPi) (.lam hPi (.var (.snoc hA)))

end Sic.Core.Typing.Validation
