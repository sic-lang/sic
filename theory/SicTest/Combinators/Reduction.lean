module

import Sic.Core.Reduction
import Sic.Core.WellFormed
import all SicTest.Common.Reduction
import all SicTest.Common.TypedSubstitution
import all SicTest.Common.WellFormed
import all SicTest.Combinators.Syntax
import all SicTest.Combinators.Typing

/-!
# The Combinators K and S: Reduction

`S K K` reduces as the identity, which proves that it is equal to the identity.
-/

namespace SicTest.Combinators.Reduction

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Common.Reduction SicTest.Common.TypedSubstitution
  SicTest.Common.WellFormed
  SicTest.Combinators.Syntax SicTest.Combinators.Typing

/-! The bodies of `K` and `S`, under the binders that `S K K` applies. -/

theorem hasType_combinatorK_4 :
    contextAt combinatorKType 4 ⊢ bodyAt 4 combinatorK : codomainAt 4 combinatorKType :=
  have hA : .empty ∙ univ (.var 0) ∙ univ (.var 0) ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (.univ (.snoc (.univ .empty))))
  .var (.snoc (.var (.snoc hA) : .empty ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ⊢ var 1 : _))

theorem hasType_combinatorK_3 :
    contextAt combinatorKType 3 ⊢ bodyAt 3 combinatorK : codomainAt 3 combinatorKType :=
  hasType_lam hasType_combinatorK_4

theorem hasType_combinatorK_2 :
    contextAt combinatorKType 2 ⊢ bodyAt 2 combinatorK : codomainAt 2 combinatorKType :=
  hasType_lam hasType_combinatorK_3

theorem hasType_combinatorK_1 :
    contextAt combinatorKType 1 ⊢ bodyAt 1 combinatorK : codomainAt 1 combinatorKType :=
  hasType_lam hasType_combinatorK_2

theorem hasType_combinatorS_5 :
    contextAt combinatorSType 5 ⊢ bodyAt 5 combinatorS : codomainAt 5 combinatorSType :=
  hasType_lam (hasType_combinatorS_body .empty)

theorem hasType_combinatorS_4 :
    contextAt combinatorSType 4 ⊢ bodyAt 4 combinatorS : codomainAt 4 combinatorSType :=
  hasType_lam hasType_combinatorS_5

theorem hasType_combinatorS_3 :
    contextAt combinatorSType 3 ⊢ bodyAt 3 combinatorS : codomainAt 3 combinatorSType :=
  hasType_lam hasType_combinatorS_4

theorem hasType_combinatorS_2 :
    contextAt combinatorSType 2 ⊢ bodyAt 2 combinatorS : codomainAt 2 combinatorSType :=
  hasType_lam hasType_combinatorS_3

theorem hasType_combinatorS_1 :
    contextAt combinatorSType 1 ⊢ bodyAt 1 combinatorS : codomainAt 1 combinatorSType :=
  hasType_lam hasType_combinatorS_2

/-! `S K K` is the identity. -/

/--
`S K K` reduces, by `(β)` on each of its five arguments, to
`λ_𝟙 (z : A). (x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)`, where `x` and `y` are the two `K`.
-/
theorem skk_termRedStar :
    ΓA ⊢ skk ⇒* lam 𝟙 (var 0) (app 𝟘 (app 𝟙 skkX.wk1 (var 0)) (app 𝟙 skkY.wk1 (var 0))) :
      pi 𝟙 𝟘 (var 0) (var 1) :=
  have hσ₀ : ΓA ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_1 hσ₀ wfCon_ΓA hasType_ΓA_var
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hasType_ΓA_var
  have β₂ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_2 hσ₁ wfCon_ΓA hasType_skkB
  have hσ₂ := substWf_cons (A := (univ (.var 0) : Term 1 1)) hσ₁ hasType_skkB
  have β₃ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_3 hσ₂ wfCon_ΓA hasType_ΓA_var
  have hσ₃ := substWf_cons (A := (univ (.var 0) : Term 1 2)) hσ₂ hasType_ΓA_var
  have β₄ := termRed_beta_subst (p := 𝟙) hasType_combinatorS_4 hσ₃ wfCon_ΓA hasType_skkX
  have hσ₄ := substWf_cons (A := (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) : Term 1 3)) hσ₃
    hasType_skkX
  have β₅ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_5 hσ₄ wfCon_ΓA hasType_skkY
  .step (.app (.app (.app (.app β₁ hasType_skkB) hasType_ΓA_var) hasType_skkX) hasType_skkY)
    (.step (.app (.app (.app β₂ hasType_ΓA_var) hasType_skkX) hasType_skkY)
      (.step (.app (.app β₃ hasType_skkX) hasType_skkY)
        (.step (.app β₄ hasType_skkY)
          (.step β₅ (.refl β₅.hasType_reduct)))))

/--
The body `K ∘_𝟘 A ∘_𝟘 B ∘_𝟙 z ∘_𝟘 (K ∘_𝟘 A ∘_𝟘 A ∘_𝟙 z)` reduces to `z`, as `K` discards its
second argument.
-/
theorem skk_body_termRedStar :
    ΓA ∙ var 0 ⊢ app 𝟘 (app 𝟙 skkX.wk1 (var 0)) (app 𝟙 skkY.wk1 (var 0)) ⇒* var 0 : var 1 :=
  have h : ⊢ ΓA ∙ var 0 := .snoc hasType_ΓA_var
  have hA : ΓA ∙ var 0 ⊢ var 1 : univ (.var 0) := .var h
  have hB := hasType_skkB.wk (.step .id) h
  have hz : ΓA ∙ var 0 ⊢ var 0 : var 1 := .var h
  have hw := HasType.app (hasType_skkY.wk (.step .id) h) hz
  have hσ₀ : ΓA ∙ var 0 ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_1 hσ₀ h hA
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hA
  have β₂ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_2 hσ₁ h hB
  have hσ₂ := substWf_cons (A := (univ (.var 0) : Term 1 1)) hσ₁ hB
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_combinatorK_3 hσ₂ h hz
  have hσ₃ := substWf_cons (A := (var 1 : Term 1 2)) hσ₂ hz
  have β₄ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_4 hσ₃ h hw
  .step (.app (.app (.app β₁ hB) hz) hw)
    (.step (.app (.app β₂ hz) hw)
      (.step (.app β₃ hw)
        (.step β₄ (.refl β₄.hasType_reduct))))

/--
`S K K` is the identity `λ_𝟙 (z : A). z` of `A`: it reduces to an abstraction whose body reduces to
its variable, as `S K K X` reduces to `X` in exercise 2.16 of Hindley and Seldin.
-/
theorem skk_termEq : ΓA ⊢ skk ≡ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  .trans skk_termRedStar.termEq
    (.lam (.pi hasType_ΓA_var (.var (.snoc hasType_ΓA_var))) (.refl hasType_ΓA_var)
      skk_body_termRedStar.termEq)

end SicTest.Combinators.Reduction
