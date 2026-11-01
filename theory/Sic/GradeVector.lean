module

public import Sic.Grade

/-!
# Grade Vectors

The vectors of grades of RFC 24, one grade for each variable of a context, with the operations that
act on each component.

ADE defines its vectors as lists extended at the end, `Conₘ`, and its operations by recursion on
these lists; the vectors here are functions from the variables, as the substitutions of
`Sic.Core.Subst` are, so that each operation is defined on a component at once.
Lean writes `p • γ` for the multiplication of a vector by a grade, which RFC 24 writes `p ·ᶜ γ`, so
the extension of a vector by a grade, which RFC 24 writes with the same symbol, is written `γ ∙ p`,
as in ADE.
-/

@[expose] public section

namespace Sic

open Grade

-- ADE: `Conₘ`, in `Graded/Context.agda`.
/-- A vector of grades, one grade for each of the `n` variables of a context. -/
def GradeVector (n : Nat) := Fin n → Grade

namespace GradeVector

-- ADE: `𝟘ᶜ`, in `Graded/Context.agda`.
/-- `𝟘ᶜ`: the vector whose components are all the grade `𝟘`. -/
def zero : GradeVector n := fun _ => 𝟘

@[inherit_doc] scoped notation "𝟘ᶜ" => GradeVector.zero

-- ADE: `_+ᶜ_`, in `Graded/Context.agda`.
/-- The sum of two vectors, component by component. -/
instance : Add (GradeVector n) where
  add γ δ := fun x => γ x + δ x

-- ADE: `_·ᶜ_`, in `Graded/Context.agda`.
/-- The product of a grade and a vector, which multiplies each component by the grade. -/
instance : HSMul Grade (GradeVector n) (GradeVector n) where
  hSMul p γ := fun x => p * γ x

-- ADE: `_∧ᶜ_`, in `Graded/Context.agda`.
/-- The meet of two vectors, component by component. -/
instance : Min (GradeVector n) where
  min γ δ := fun x => γ x ⊓ δ x

-- ADE: `_≤ᶜ_`, in `Graded/Context.agda`.
/--
The order of the vectors, component by component: a vector `γ` may be used where the vector `δ` is
expected.
-/
instance : LE (GradeVector n) where
  le γ δ := ∀ x, γ x ≤ δ x

-- ADE: `_∙_`, in `Graded/Context.agda`.
/-- `γ ∙ p`: the vector `γ` extended by the grade `p` for a new innermost variable. -/
def cons (γ : GradeVector n) (p : Grade) : GradeVector (n + 1)
  | ⟨0, _⟩ => p
  | ⟨x + 1, h⟩ => γ ⟨x, Nat.lt_of_succ_lt_succ h⟩

@[inherit_doc] scoped infixl:60 " ∙ " => GradeVector.cons

-- ADE: `_,_≔_`, in `Graded/Context.agda`.
/-- `(γ, x ≔ p)`: the vector `γ` in which the grade of the variable `x` is replaced by `p`. -/
def update (γ : GradeVector n) (x : Fin n) (p : Grade) : GradeVector n :=
  fun y => if y = x then p else γ y

@[inherit_doc] scoped notation:max "(" γ ", " x " ≔ " p ")" => GradeVector.update γ x p

end GradeVector

end Sic
