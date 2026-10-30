module

import Sic.Core.Reduction
import Sic.Core.WellFormed
import all SicTest.Common.Reduction
import all SicTest.Common.TypedSubstitution
import all SicTest.Common.WellFormed
import all SicTest.ChurchNumerals.Syntax
import all SicTest.ChurchNumerals.Typing

/-!
# The Church Numerals: Reduction

The numerals reduce as Girard, Lafont and Taylor say, which proves that `succ ∘_𝟙 1` is `2`.
-/

namespace SicTest.ChurchNumerals.Reduction

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Common.Reduction SicTest.Common.TypedSubstitution
  SicTest.Common.WellFormed
  SicTest.ChurchNumerals.Syntax SicTest.ChurchNumerals.Typing

/-! The bodies of `1`, `2` and `succ`, under the binders that the examples apply. -/

theorem hasType_churchOne_3 :
    contextAt churchNat 3 ⊢ bodyAt 3 churchOne : codomainAt 3 churchNat :=
  .app (hasType_ΓNat_f .empty) (hasType_ΓNat_x .empty)

theorem hasType_churchOne_2 :
    contextAt churchNat 2 ⊢ bodyAt 2 churchOne : codomainAt 2 churchNat :=
  hasType_lam hasType_churchOne_3

theorem hasType_churchOne_1 :
    contextAt churchNat 1 ⊢ bodyAt 1 churchOne : codomainAt 1 churchNat :=
  hasType_lam hasType_churchOne_2

theorem hasType_churchTwo_3 :
    contextAt churchNat 3 ⊢ bodyAt 3 churchTwo : codomainAt 3 churchNat :=
  .app (hasType_ΓNat_f .empty) (.app (hasType_ΓNat_f .empty) (hasType_ΓNat_x .empty))

theorem hasType_churchTwo_2 :
    contextAt churchNat 2 ⊢ bodyAt 2 churchTwo : codomainAt 2 churchNat :=
  hasType_lam hasType_churchTwo_3

theorem hasType_churchTwo_1 :
    contextAt churchNat 1 ⊢ bodyAt 1 churchTwo : codomainAt 1 churchNat :=
  hasType_lam hasType_churchTwo_2

theorem hasType_churchSucc_1 :
    contextAt (pi 𝟙 𝟘 churchNat churchNat) 1 ⊢ bodyAt 1 churchSucc :
      codomainAt 1 (pi 𝟙 𝟘 churchNat churchNat) :=
  hasType_numeral (.snoc (hasType_churchNat .empty)) (hasType_churchSucc_body .empty)

/-! The successor of `1` is `2`. -/

/-- `2 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x` reduces to `f ∘_𝟙 (f ∘_𝟙 x)`: `2` applies `f` twice. -/
theorem churchTwo_termRedStar :
    ΓNat .empty ⊢ app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchTwo (var 2)) (var 1)) (var 0) ⇒*
      app 𝟙 (var 1) (app 𝟙 (var 1) (var 0)) : var 2 :=
  have h := wfCon_ΓNat (Γ := (.empty : Con 1 0)) .empty
  have hX : ΓNat .empty ⊢ var 2 : univ (.var 0) := .var h
  have hσ₀ : ΓNat .empty ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_churchTwo_1 hσ₀ h hX
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hX
  have β₂ := termRed_beta_subst (p := 𝟙 + 𝟙) hasType_churchTwo_2 hσ₁ h (hasType_ΓNat_f .empty)
  have hσ₂ := substWf_cons (A := (churchFunType : Term 1 1)) hσ₁ (hasType_ΓNat_f .empty)
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_churchTwo_3 hσ₂ h (hasType_ΓNat_x .empty)
  .step (.app (.app β₁ (hasType_ΓNat_f .empty)) (hasType_ΓNat_x .empty))
    (.step (.app β₂ (hasType_ΓNat_x .empty)) (.step β₃ (.refl β₃.hasType_reduct)))

/-- `1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x` reduces to `f ∘_𝟙 x`. -/
theorem churchOne_termRedStar :
    ΓNat .empty ⊢ app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchOne (var 2)) (var 1)) (var 0) ⇒*
      app 𝟙 (var 1) (var 0) : var 2 :=
  have h := wfCon_ΓNat (Γ := (.empty : Con 1 0)) .empty
  have hX : ΓNat .empty ⊢ var 2 : univ (.var 0) := .var h
  have hσ₀ : ΓNat .empty ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_churchOne_1 hσ₀ h hX
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hX
  have β₂ := termRed_beta_subst (p := 𝟙 + 𝟙) hasType_churchOne_2 hσ₁ h (hasType_ΓNat_f .empty)
  have hσ₂ := substWf_cons (A := (churchFunType : Term 1 1)) hσ₁ (hasType_ΓNat_f .empty)
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_churchOne_3 hσ₂ h (hasType_ΓNat_x .empty)
  .step (.app (.app β₁ (hasType_ΓNat_f .empty)) (hasType_ΓNat_x .empty))
    (.step (.app β₂ (hasType_ΓNat_x .empty)) (.step β₃ (.refl β₃.hasType_reduct)))

/--
`succ ∘_𝟙 1` is `2`, as `S n` is `n + 1` in Girard, Lafont and Taylor: `succ ∘_𝟙 1` reduces to
`λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X). f ∘_𝟙 (1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)`,
whose body is equal to the body of `2`, under the three binders, by the congruences.
-/
theorem churchSucc_one_termEq :
    (.empty : Con 1 0) ⊢ app 𝟙 churchSucc churchOne ≡ churchTwo : churchNat :=
  have β := termRed_beta_subst (p := 𝟙) hasType_churchSucc_1 (σ := Fin.elim0) substWf_empty .empty
    (hasType_churchOne .empty)
  have hNat := hasType_churchNat (Γ := (.empty : Con 1 0)) .empty
  have ⟨⟨_, hU⟩, _, hNat₂⟩ := hNat.inv_pi
  have ⟨⟨_, hf⟩, _, hNat₃⟩ := hNat₂.inv_pi
  have ⟨⟨_, hx⟩, _⟩ := hNat₃.inv_pi
  .trans β.termEq (.lam hNat (.refl hU) (.lam hNat₂ (.refl hf) (.lam hNat₃ (.refl hx)
    (.app (.refl (hasType_ΓNat_f .empty)) churchOne_termRedStar.termEq))))

end SicTest.ChurchNumerals.Reduction
