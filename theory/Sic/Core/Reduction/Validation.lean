module

import Sic.Core.Reduction
import all Sic.Core.Syntax.Validation

/-!
# Validation of the Reduction

The reduction of `Sic.Core.Reduction` checked against the formalization of ADE, and on the
polymorphic identity of RFC 24.

| Definition | Definition of ADE |
| --- | --- |
| `Neutral` | `Neutral`, in `Definition/Untyped/Neutral.agda` |
| `Whnf` | `Whnf`, in `Definition/Untyped/Whnf.agda` |
| `TermRed.conv`, `TermRed.app`, `TermRed.beta` | `conv`, `app-subst`, `β-red` of `_⊢_⇒_∷_`, in `Definition/Typed.agda` |
| `TermRedStar.refl`, `TermRedStar.step` | `id`, `_⇨_` of `_⊢_⇒*_∷_`, in `Definition/Typed.agda` |
| `TermRedWhnf` | `_⊢_↘_∷_`, in `Definition/Typed.agda` |

ADE also reduce types, with `_⊢_⇒_`, which a reduction of a term in a universe replaces here, as the
equality of types does in `Sic.Core.Typing`.
Their `β-red` reduces an abstraction applied with another grade, which their premise `p ≡ p′`
equates, while `TermRed.beta` writes the same grade on both.
-/

namespace Sic.Core.Reduction.Validation

open Grade Syntax.Validation Term

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def Γ₁ : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_Γ₁ : ⊢ Γ₁ := .snoc (.univ .empty)

/--
The polymorphic identity applied to a type, `(λ_𝟘 (A : U_l). λ_𝟙 (x : A). x) ∘_𝟘 A`, reduces in one
step to the identity `λ_𝟙 (x : A). x` of `A`, a weak head normal form.
-/
example : Γ₁ ⊢ app 𝟘 identity.wk1 (var 0) ↘ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`, as for the type of
  -- the polymorphic identity, but in `Γ₁`.
  have hU : Γ₁ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ wfCon_Γ₁
  have hA : Γ₁ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc hU)
  have hA' : Γ₁ ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hPi : Γ₁ ∙ univ (.var 0) ⊢ pi 𝟙 𝟘 (var 0) (var 1) : univ (.var 0 ⊔ .var 0) := .pi hA hA'
  have hIdType := HasType.pi (p := 𝟘) (q := 𝟙 + 𝟙) hU hPi
  -- `A : U_l` in `Γ₁`, and `A : U_l` after `x : A`, for the identity of `A`.
  have hB : Γ₁ ⊢ var 0 : univ (.var 0) := .var wfCon_Γ₁
  have hB' : Γ₁ ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hB)
  ⟨.step (.beta hIdType (.lam hPi (.var (.snoc hA))) hB)
    (.refl (.lam (.pi hB hB') (.var (.snoc hB)))), .lam⟩

/-- A variable applied to an argument, `x ∘_𝟙 y`, is neutral, so that it does not reduce. -/
example {Γ : Con 0 2} : ¬ Γ ⊢ app 𝟙 (var 0) (var 1) ⇒ u : A := Neutral.not_termRed (.app .var)

end Sic.Core.Reduction.Validation
