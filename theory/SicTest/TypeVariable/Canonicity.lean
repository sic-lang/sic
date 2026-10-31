module

import Sic.Core.Canonicity
import all SicTest.TypeVariable.Reduction

/-!
# A Type Variable: Canonicity

`HasType.canonical_univ` and `HasType.canonical_pi` need their term to be closed: in the context of
a type variable `A : U_l`, the variable `A` reduces neither to a universe nor to a type of functions,
and a variable `f : Π^𝟘_𝟙 (x : A). A` does not reduce to an abstraction, since a variable is a weak
head normal form, which reduces only to itself.
-/

namespace SicTest.TypeVariable.Canonicity

open Sic.Core Sic.Grade Sic.Core.Term SicTest.TypeVariable.Reduction

/-- A weak head normal form reduces only to itself. -/
theorem eq_of_whnf (ht : Whnf t) (h : Γ ⊢ t ⇒* u : A) : u = t := by
  cases h with
  | refl => rfl
  | step h => nomatch ht.not_termRed h

/--
The variable `A : U_l` is a term of `U_l` that reduces neither to a universe nor to a type of
functions.
-/
example : (ΓA ⊢ var 0 : univ (.var 0)) ∧ ¬ ((∃ l', ΓA ⊢ var 0 ↘ univ l' : univ (.var 0)) ∨
    ∃ p q A B, ΓA ⊢ var 0 ↘ pi p q A B : univ (.var 0)) := by
  refine ⟨.var wfCon_ΓA, ?_⟩
  rintro (⟨_, h, _⟩ | ⟨_, _, _, _, h, _⟩) <;> nomatch eq_of_whnf (.ne .var) h

/-- The context `A : U_l, f : Π^𝟘_𝟙 (x : A). A`. -/
def ΓAf : Con 1 2 := ΓA ∙ pi 𝟙 𝟘 (var 0) (var 1)

/--
The variable `f : Π^𝟘_𝟙 (x : A). A` is a term of its type that does not reduce to an abstraction.
-/
example : (ΓAf ⊢ var 0 : pi 𝟙 𝟘 (var 1) (var 2)) ∧
    ¬ ∃ A' u, ΓAf ⊢ var 0 ↘ lam 𝟙 A' u : pi 𝟙 𝟘 (var 1) (var 2) := by
  -- `A : U_l` after `A`, and `A : U_l` after `x : A`.
  have hA : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA
  have hA' : ΓA ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hA))
  refine ⟨.var (.snoc (.univ (.pi hA hA'))), ?_⟩
  rintro ⟨_, _, h, _⟩
  nomatch eq_of_whnf (.ne .var) h

end SicTest.TypeVariable.Canonicity
