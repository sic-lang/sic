module

import Sic.Core.Typing
import all SicTest.ChurchNumerals.Syntax

/-!
# The Church Numerals: Typing

The types of `Nat_l`, `1`, `2` and `succ`, as derivations.
-/

namespace SicTest.ChurchNumerals.Typing

open Sic.Core Sic.Grade Sic.Core.Term SicTest.ChurchNumerals.Syntax

/-- The context `X : U_l, f : Π^𝟘_𝟙 (y : X). X, x : X` of the bodies of the numerals, after `Γ`. -/
def ΓNat (Γ : Con 1 n) : Con 1 (n + 3) := Γ ∙ univ (.var 0) ∙ churchFunType ∙ var 1

/-- The type `Π^𝟘_𝟙 (y : X). X` of `f`, at the level `l ⊔ l`. -/
theorem hasType_churchFunType (h : ⊢ Γ) :
    Γ ∙ univ (.var 0) ⊢ churchFunType : univ (.var 0 ⊔ .var 0) :=
  have hX : Γ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ (.univ h)))
  .pi hX (.var (.snoc (.univ hX)))

theorem wfCon_ΓNat (h : ⊢ Γ) : ⊢ ΓNat Γ :=
  .snoc (.univ ((.var (.snoc (.univ (hasType_churchFunType h))) :
    Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : _)))

/-- `Nat_l` is a type, of the level `(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))`, which is `l + 1`. -/
theorem hasType_churchNat (h : ⊢ Γ) :
    Γ ⊢ churchNat : univ (.succ (.var 0) ⊔ ((.var 0 ⊔ .var 0) ⊔ (.var 0 ⊔ .var 0))) :=
  have hx : Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (.univ (hasType_churchFunType h)))
  .pi (.univ h) (.pi (hasType_churchFunType h) (.pi hx (.var (wfCon_ΓNat h))))

/-- A numeral has the type `Nat_l` when its body has the type `X`. -/
theorem hasType_numeral (h : ⊢ Γ) (hb : ΓNat Γ ⊢ b : var 2) :
    Γ ⊢ lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1) b)) : churchNat :=
  have hx : Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (.univ (hasType_churchFunType h)))
  have hx' := HasType.pi hx (.var (wfCon_ΓNat h) : ΓNat Γ ⊢ var 2 : univ (.var 0))
  have hf := HasType.pi (hasType_churchFunType h) hx'
  .lam (.univ (.pi (.univ h) hf)) (.lam (.univ hf) (.lam (.univ hx') hb))

/-- `f`, in the bodies of the numerals. -/
theorem hasType_ΓNat_f (h : ⊢ Γ) : ΓNat Γ ⊢ var 1 : pi 𝟙 𝟘 (var 2) (var 3) := .var (wfCon_ΓNat h)

/-- `x`, in the bodies of the numerals. -/
theorem hasType_ΓNat_x (h : ⊢ Γ) : ΓNat Γ ⊢ var 0 : var 2 := .var (wfCon_ΓNat h)

theorem hasType_churchOne (h : ⊢ Γ) : Γ ⊢ churchOne : churchNat :=
  hasType_numeral h (.app (hasType_ΓNat_f h) (hasType_ΓNat_x h))

theorem hasType_churchTwo (h : ⊢ Γ) : Γ ⊢ churchTwo : churchNat :=
  hasType_numeral h (.app (hasType_ΓNat_f h) (.app (hasType_ΓNat_f h) (hasType_ΓNat_x h)))

/-- The body `f ∘_𝟙 (m ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)` of `succ`, after `m : Nat_l`. -/
theorem hasType_churchSucc_body (h : ⊢ Γ) :
    ΓNat (Γ ∙ churchNat) ⊢
      app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 (var 3) (var 2)) (var 1)) (var 0)) : var 2 :=
  have h' : ⊢ Γ ∙ churchNat := .snoc (.univ (hasType_churchNat h))
  have hm : ΓNat (Γ ∙ churchNat) ⊢ var 3 : churchNat := .var (wfCon_ΓNat h')
  have hX : ΓNat (Γ ∙ churchNat) ⊢ var 2 : univ (.var 0) := .var (wfCon_ΓNat h')
  .app (hasType_ΓNat_f h') (.app (.app (.app hm hX) (hasType_ΓNat_f h')) (hasType_ΓNat_x h'))

/-- `succ` has the type `Π^𝟘_𝟙 (m : Nat_l). Nat_l`. -/
theorem hasType_churchSucc (h : ⊢ Γ) : Γ ⊢ churchSucc : pi 𝟙 𝟘 churchNat churchNat :=
  have h' : ⊢ Γ ∙ churchNat := .snoc (.univ (hasType_churchNat h))
  .lam (.univ (.pi (hasType_churchNat h) (hasType_churchNat h')))
    (hasType_numeral h' (hasType_churchSucc_body h))

end SicTest.ChurchNumerals.Typing
