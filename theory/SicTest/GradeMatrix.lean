module

import Sic.GradeMatrix

/-!
# Grade Matrices

The definitions of `Sic.GradeMatrix` checked against their meaning, the product of a row vector by
a matrix, and on examples.
-/

namespace SicTest.GradeMatrix

open Sic Sic.Grade Sic.GradeVector

/-- The grade of the multiplicities `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-- The sum of the grades `f x`, for the `n` variables `x` of a context. -/
def sum : {n : Nat} → (Fin n → Grade) → Grade
  | 0, _ => 𝟘
  | _ + 1, f => f 0 + sum fun x => f x.succ

/--
The meaning of the multiplication by a matrix: each component of `γ <* Ψ` is the sum, over the
variables `x`, of the grade of `x` multiplied by the component of its row, as in the product of a
row vector by a matrix.
-/
theorem subst_apply : ∀ {n : Nat} (γ : GradeVector n) (Ψ : GradeMatrix m n) (y : Fin m),
    (γ <* Ψ) y = sum fun x => γ x * Ψ x y
  | 0, _, _, _ => rfl
  | _ + 1, γ, Ψ, y => congrArg (γ 0 * Ψ 0 y + ·) (subst_apply (tail γ) Ψ.tail y)

/-- The rows of the identity are the vectors of the rule of the variables, with the grade `𝟙`. -/
example (x : Fin n) : GradeMatrix.id x = (𝟘ᶜ, x ≔ 𝟙) := rfl

/-- Under a binder, the identity stays the identity, as the substitutions do. -/
example : (GradeMatrix.id : GradeMatrix 2 2).lift = GradeMatrix.id := by
  funext x y; match x, y with | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 => rfl

/--
A term that uses its only variable `y` with the grade `⟪0, 1⟫`, in which `f x x` is substituted
for `y`, over the context `f, x`: the product scales the row of `f x x`, which uses `f` once and `x`
without bound, by the grade of `y`.
-/
example :
    ((𝟘ᶜ : GradeVector 0) ∙ ⟪.zero, .one⟫) <*
        (GradeMatrix.cons (fun x => x.elim0) (𝟘ᶜ ∙ 𝟙 ∙ ⟪.omega, .omega⟫) : GradeMatrix 2 1) =
      𝟘ᶜ ∙ ⟪.zero, .one⟫ ∙ ⟪.zero, .omega⟫ := by
  funext x; match x with | 0 | 1 => rfl

end SicTest.GradeMatrix
