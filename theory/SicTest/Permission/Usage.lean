module

import Sic.Core.Usage
import all SicTest.GradeVector
import all SicTest.Permission.Syntax

/-!
# A Permission Used Once: Usage

Of the three functions that receive a permission, all well typed, usage accepts only the one that
passes the permission on once, whatever grades the variables of the context get: the vectors are
over `Perm`, `B`, `b`, `close` and `commit`, the grade of `commit` last.
-/

namespace SicTest.Permission.Usage

open Sic Sic.Core Sic.Grade Sic.GradeVector Sic.Mode Sic.Core.Term SicTest.GradeVector
  SicTest.Permission.Syntax

/--
The function that passes the permission on once uses `close` once: its body uses `x` with
`⟨0, 1⟩ · ⟨0, 1⟩ = ⟨0, 1⟩`, since the argument of `close` is checked in the mode `𝟘𝟙ᵐ`, where `x`
uses itself with `⟨0, 1⟩`, and this is the grade of the abstraction.
-/
theorem usage_once : 𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟙 ∙ 𝟘 ▶[𝟙𝟙ᵐ] once :=
  .lam (.sub (.app .var .var) (by decide))

/--
The usage of `usage_once` is the greatest: the function that passes the permission on once is well
used exactly with the vectors below it, so that it cannot leave `close` unused, nor use any other
variable.
-/
theorem usage_once_iff : γ ▶[𝟙𝟙ᵐ] once ↔ γ ≤ 𝟘ᶜ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟙 ∙ 𝟘 :=
  ⟨fun h =>
    have ⟨_, hb, hγ⟩ := h.inv_lam
    have ⟨_, _, hf, hx, hδ⟩ := hb.inv_app
    GradeVector.le_trans hγ <| GradeVector.le_trans (le_tail hδ) <|
      GradeVector.le_trans
        (tail_mono (add_mono hf.inv_var (smul_mono (Grade.le_refl _) hx.inv_var))) (by decide),
    fun h => .sub usage_once h⟩

/--
The function that passes the permission to both operations is rejected: its body uses `x` with
`⟨0, 1⟩ + ⟨0, 1⟩ = ⟨0, ω⟩` at least, which `⟨0, 1⟩` is not below.
-/
theorem not_usage_twice : ¬ γ ▶[𝟙𝟙ᵐ] twice := fun h =>
  -- The body uses `x` at most with `(a + (⟨0, 1⟩ * b)) + (𝟙 * (c + (⟨0, 1⟩ * d)))`, where `a`
  -- and `c` are the grades of `x` in `commit` and `close`, at most `𝟘`, and `b` and `d` its grades
  -- as their argument, at most `⟨0, 1⟩`.
  have ⟨_, hb, _⟩ := h.inv_lam
  have ⟨_, _, hgx, hfx, hγ⟩ := hb.inv_app
  have ⟨_, _, hg, hx, hδ⟩ := hgx.inv_app
  have ⟨_, _, hf, hx', hη⟩ := hfx.inv_app
  have key : ∀ a b c d : Grade, a ≤ 𝟘 → b ≤ permission → c ≤ 𝟘 → d ≤ permission →
      ¬ permission ≤ (a + (permission * b)) + (𝟙 * (c + (permission * d))) := by
    decide
  key _ _ _ _ (hg.inv_var 0) (hx.inv_var 0) (hf.inv_var 0) (hx'.inv_var 0)
    (Grade.le_trans (hγ 0) (add_le_add (hδ 0) (mul_le_mul (le_refl _) (hη 0))))

/-- The function that drops the permission is rejected: its body uses `x` with `𝟘`. -/
theorem not_usage_dropped : ¬ γ ▶[𝟙𝟙ᵐ] dropped := fun h =>
  have ⟨_, hb, _⟩ := h.inv_lam
  absurd (hb.inv_var 0) (by decide : ¬ (⌜𝟙𝟙ᵐ⌝ * permission) ≤ 𝟘)

end SicTest.Permission.Usage
