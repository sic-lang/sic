module

import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable
import all SicTest.ChurchNumerals.Syntax

/-!
# The Church Numerals: Validity of the Types of Functions

The type `Nat_l` of the Church numerals is a valid term of the universe of the level that its typing
gives it, `(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))`, at the level `2`, which follows the value `1` of that
level when `l` is `0`, for every equality relation: each of its three types of functions is valid
in the context of the domains before it.
-/

namespace SicTest.ChurchNumerals.Reducibility.Introductions.Pi

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility SicTest.ChurchNumerals.Syntax

variable [EqualityRelation]

/-- `Nat_l` is a valid term of `U_{(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))}`, at the level `2`. -/
example : (.empty : Con 1 0) ⊩ᵛ⟨2⟩ churchNat ≡ churchNat :
    univ (.succ (.var 0) ⊔ ((.var 0 ⊔ .var 0) ⊔ (.var 0 ⊔ .var 0))) := by
  have hε : ⊩ᵛ (.empty : Con 1 0) := by rw [ValidCon.unfold_empty]; trivial
  -- The domain `U_l` of `X`, and the context `X : U_l`.
  have hU := ValidTermEq.univ hε (.refl (.var 0))
  have hX : ⊩ᵛ (.empty ∙ univ (.var 0) : Con 1 1) := by
    rw [ValidCon.unfold_snoc]
    exact ⟨_, hU.toTypeEq⟩
  -- The domain `Π^𝟘_𝟙 (y : X). X` of `f`, and the context `X : U_l, f : Π^𝟘_𝟙 (y : X). X`.
  have ⟨_, hX₀⟩ := ValidTermEq.var hX 0
  have hXy : ⊩ᵛ (.empty ∙ univ (.var 0) ∙ var 0 : Con 1 2) := by
    rw [ValidCon.unfold_snoc]
    exact ⟨_, ValidTermEq.toTypeEq (L := .var 0) hX₀⟩
  have ⟨_, hX₁⟩ := ValidTermEq.var hXy 1
  have hF := ValidTermEq.pi (L₁ := .var 0) (L₂ := .var 0) (p := 𝟙) (q := 𝟘) hX₀ hX₁
  have hXf : ⊩ᵛ (.empty ∙ univ (.var 0) ∙ churchFunType : Con 1 2) := by
    rw [ValidCon.unfold_snoc]
    exact ⟨_, hF.toTypeEq⟩
  -- The domain `X` of `x`, and the context `X : U_l, f : Π^𝟘_𝟙 (y : X). X, x : X`.
  have ⟨_, hXf₁⟩ := ValidTermEq.var hXf 1
  have hXfx : ⊩ᵛ (.empty ∙ univ (.var 0) ∙ churchFunType ∙ var 1 : Con 1 3) := by
    rw [ValidCon.unfold_snoc]
    exact ⟨_, ValidTermEq.toTypeEq (L := .var 0) hXf₁⟩
  have ⟨_, hXfx₂⟩ := ValidTermEq.var hXfx 2
  -- The three types of functions, from the innermost.
  have hx := ValidTermEq.pi (L₁ := .var 0) (L₂ := .var 0) (p := 𝟙) (q := 𝟘) hXf₁ hXfx₂
  have hf := ValidTermEq.pi (p := 𝟙 + 𝟙) (q := 𝟘) hF hx
  exact ValidTermEq.pi (p := 𝟘) (q := 𝟙 + 𝟙) hU hf

end SicTest.ChurchNumerals.Reducibility.Introductions.Pi
