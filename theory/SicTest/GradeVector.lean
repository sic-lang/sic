module

import Sic.GradeVector

/-!
# Grade Vectors

The definitions of `Sic.GradeVector` checked against RFC 24 and against their meaning.
-/

namespace SicTest.GradeVector

open Sic Sic.Grade Sic.GradeVector

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-! The claims of RFC 24: the zero vector, the extension and the replacement of a grade. -/

/-- The components of the zero vector are all the grade `𝟘`, whatever its length. -/
example (x : Fin n) : (𝟘ᶜ : GradeVector n) x = 𝟘 := rfl

/-- The extension gives its grade to the new innermost variable, and keeps the other grades. -/
example (γ : GradeVector n) (p : Grade) : (γ ∙ p) 0 = p := rfl
example (γ : GradeVector n) (p : Grade) (x : Fin n) : (γ ∙ p) x.succ = γ x := rfl

/-- The replacement gives its grade to its variable, and keeps the grades of the other variables. -/
example (γ : GradeVector n) (x : Fin n) (p : Grade) : (γ, x ≔ p) x = p := ite_eq_left rfl
example (γ : GradeVector n) (x y : Fin n) (p : Grade) (h : y ≠ x) : (γ, x ≔ p) y = γ y :=
  ite_eq_right h

/-- The vector of the rule of the variables, for the variable `1` of a context of three, in the mode `𝟘𝟙ᵐ`. -/
example : (𝟘ᶜ, 1 ≔ ⟪.zero, .one⟫) = (𝟘ᶜ : GradeVector 1) ∙ ⟪.zero, .one⟫ ∙ 𝟘 := by
  funext x; match x with | 0 | 1 | 2 => rfl

/-- The operations act on each component, as in the example of two variables. -/
example : ((𝟘ᶜ : GradeVector 0) ∙ 𝟙 ∙ 𝟘) + (𝟘ᶜ ∙ 𝟙 ∙ ⟪.zero, .one⟫) =
    𝟘ᶜ ∙ ⟪.omega, .omega⟫ ∙ ⟪.zero, .one⟫ := by
  funext x; match x with | 0 | 1 => rfl
example : ⟪.zero, .one⟫ • ((𝟘ᶜ : GradeVector 0) ∙ 𝟙 ∙ ⟪.omega, .omega⟫) =
    𝟘ᶜ ∙ ⟪.zero, .one⟫ ∙ ⟪.zero, .omega⟫ := by
  funext x; match x with | 0 | 1 => rfl
example : ((𝟘ᶜ : GradeVector 0) ∙ 𝟙 ∙ 𝟘) ⊓ (𝟘ᶜ ∙ ⟪.zero, .one⟫ ∙ 𝟘) =
    𝟘ᶜ ∙ ⟪.omega, .one⟫ ∙ 𝟘 := by
  funext x; match x with | 0 | 1 => rfl

/-!
The meaning of the vectors: they inherit the laws of the grades, component by component, and form a
module over the grades with a meet semilattice over which the operations distribute, as ADE proves
in `Graded/Context/Properties/`.
-/

section Laws

variable (γ δ η : GradeVector n) (p q : Grade)

example : 𝟙 • γ = γ := funext fun _ => one_mul _

example : (γ ⊓ δ) ⊓ η = γ ⊓ (δ ⊓ η) := funext fun _ => min_assoc ..
example : γ ⊓ δ = δ ⊓ γ := funext fun _ => min_comm ..
example : γ ⊓ γ = γ := funext fun _ => min_self _
example : p • (γ ⊓ δ) = (p • γ) ⊓ (p • δ) := funext fun _ => mul_min ..
example : (p ⊓ q) • γ = (p • γ) ⊓ (q • γ) := funext fun _ => min_mul ..
example : γ + (δ ⊓ η) = (γ + δ) ⊓ (γ + η) := funext fun _ => add_min ..
example : (γ ⊓ δ) + η = (γ + η) ⊓ (δ + η) := funext fun _ => min_add ..

/-- The order component by component is the order of ADE, `γ ≤ᶜ δ` when `γ` is the meet `γ ∧ᶜ δ`. -/
example : γ ≤ δ ↔ γ = γ ⊓ δ :=
  ⟨fun h => funext h, fun h x => congrFun h x⟩

example {γ δ : GradeVector n} (h₁ : γ ≤ δ) (h₂ : δ ≤ γ) : γ = δ :=
  funext fun x => le_antisymm (h₁ x) (h₂ x)
example : γ ⊓ δ ≤ γ := fun _ => min_le_left ..
example : γ ⊓ δ ≤ δ := fun _ => min_le_right ..
example {γ δ η : GradeVector n} (h₁ : η ≤ γ) (h₂ : η ≤ δ) : η ≤ γ ⊓ δ :=
  fun x => le_min (h₁ x) (h₂ x)
example {γ γ' δ δ' : GradeVector n} (h₁ : γ ≤ γ') (h₂ : δ ≤ δ') : γ ⊓ δ ≤ γ' ⊓ δ' :=
  fun x => min_le_min (h₁ x) (h₂ x)

end Laws

end SicTest.GradeVector
