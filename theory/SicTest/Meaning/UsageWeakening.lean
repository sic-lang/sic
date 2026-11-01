module

public import Sic.Core.UsageWeakening

/-!
# Meaning of the Usage Weakening

The weakening of the vectors against its meaning: the vector moved by a weakening gives each
variable of the smaller context its grade, at the index to which the weakening moves it, and the
grade `𝟘` to the variables that the weakening adds.
-/

@[expose] public section

namespace SicTest.Meaning.UsageWeakening

open Sic Sic.Core Sic.Grade Sic.GradeVector

/-- A variable moved by the weakening keeps its grade. -/
theorem wk_var : ∀ (ρ : Wk m n) (γ : GradeVector n) (x : Fin n), γ.wk ρ (ρ.var x) = γ x
  | .id, _, _ => rfl
  | .step ρ, γ, x => wk_var ρ γ x
  | .lift _, _, ⟨0, _⟩ => rfl
  | .lift ρ, γ, ⟨x + 1, hx⟩ => wk_var ρ (tail γ) ⟨x, Nat.lt_of_succ_lt_succ hx⟩

/-- A variable that the weakening adds has the grade `𝟘`. -/
theorem wk_added : ∀ (ρ : Wk m n) (γ : GradeVector n) (y : Fin m),
    (∀ x, ρ.var x ≠ y) → γ.wk ρ y = 𝟘
  | .id, _, y, h => absurd rfl (h y)
  | .step _, _, ⟨0, _⟩, _ => rfl
  | .step ρ, γ, ⟨y + 1, hy⟩, h =>
    wk_added ρ γ ⟨y, Nat.lt_of_succ_lt_succ hy⟩ fun x e => h x (congrArg Fin.succ e)
  | .lift _, _, ⟨0, _⟩, h => absurd rfl (h ⟨0, Nat.succ_pos _⟩)
  | .lift ρ, γ, ⟨y + 1, hy⟩, h =>
    wk_added ρ (tail γ) ⟨y, Nat.lt_of_succ_lt_succ hy⟩ fun x e => h x.succ (congrArg Fin.succ e)

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-- Inserting a variable between the two variables of a context gives it the grade `𝟘`. -/
example : ((𝟘ᶜ : GradeVector 0) ∙ 𝟙 ∙ ⟪.zero, .one⟫).wk (Wk.step .id).lift =
    𝟘ᶜ ∙ 𝟙 ∙ 𝟘 ∙ ⟪.zero, .one⟫ := by
  funext x; match x with | 0 | 1 | 2 => rfl

end SicTest.Meaning.UsageWeakening
