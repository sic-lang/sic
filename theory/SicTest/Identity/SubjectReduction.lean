module

public import Sic.Core.SubjectReduction
import Sic.Core.Injectivity

/-!
# The Polymorphic Identity: Subject Reduction

The polymorphic identity applied to a type reduces to the identity of that type, at a type that
`(β)` derives, and `HasType.termRed` gives the reduct another type, which is not equal to it: the
identity also has a type whose result of the inner type of functions has another grade, which the
typing does not read.
In the context `A : U_l`, where `A` is `var 0`.
-/

@[expose] public section

namespace SicTest.Identity.SubjectReduction

open Sic.Core Sic.Grade Sic.Core.Term

/-- The context `A : U_l`. -/
def Γ : Con 1 1 := .empty ∙ univ (.var 0)

/-- `λ_𝟘 (B : U_l). λ_𝟙 (x : B). x`, the polymorphic identity, in the context `A : U_l`. -/
def identity : Term 1 1 := lam 𝟘 (univ (.var 0)) (lam 𝟙 (var 0) (var 0))

theorem wfCon_Γ : ⊢ Γ := .snoc (.univ (.univ .empty))

/-- `B : U_l` and `B : U_l` after `x : B`, in the context `A : U_l, B : U_l`. -/
theorem hasType_B : Γ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ (.univ wfCon_Γ)))

theorem hasType_B' : Γ ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) :=
  .var (.snoc (.univ hasType_B))

/-- The identity has the type `Π^𝟘_𝟘 (B : U_l). Π^q_𝟙 (x : B). B`, whatever the grade `q`. -/
theorem hasType_identity (q : Sic.Grade) :
    Γ ⊢ identity : pi 𝟘 𝟘 (univ (.var 0)) (pi 𝟙 q (var 0) (var 1)) :=
  have hPi := HasType.pi (p := 𝟙) (q := q) hasType_B hasType_B'
  .lam (.univ (.pi (.univ wfCon_Γ) hPi)) (.lam (.univ hPi) (.var (.snoc (.univ hasType_B))))

/-- `A : U_l`, the argument. -/
theorem hasType_A : Γ ⊢ var 0 : univ (.var 0) := .var wfCon_Γ

/-- The identity applied to `A` reduces to `λ_𝟙 (x : A). x`, at `Π^𝟘_𝟙 (x : A). A`, by `(β)`. -/
theorem termRed :
    Γ ⊢ app 𝟘 identity (var 0) ⇒ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  have hPi := HasType.pi (p := 𝟙) (q := 𝟘) hasType_B hasType_B'
  .beta (q := 𝟘) (.univ (.pi (.univ wfCon_Γ) hPi)) (.lam (.univ hPi) (.var (.snoc (.univ hasType_B))))
    hasType_A

/-- The reduct also has the type `Π^𝟙_𝟙 (x : A). A`, which the application has. -/
example : Γ ⊢ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟙 (var 0) (var 1) :=
  (HasType.app (hasType_identity 𝟙) hasType_A).termRed termRed

/-- The two types of the reduct are not equal. -/
example : ¬ Γ ⊢ pi 𝟙 𝟘 (var 0) (var 1) ≡ pi 𝟙 𝟙 (var 0) (var 1) := fun h =>
  absurd h.pi_inj.2.1 (by decide)

end SicTest.Identity.SubjectReduction
