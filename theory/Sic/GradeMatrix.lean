module

public import Sic.GradeVector

/-!
# Grade Matrices

The matrices of grades that act on the vectors of grades as the substitutions act on the terms: the
row of a variable is the usage of the term that a substitution puts for it, and a vector multiplied
by the matrix, `γ <* Ψ`, sums these rows, each scaled by the grade that `γ` gives its variable.

ADE defines its matrices as lists of rows extended at the end, `Substₘ`, and its operations by
recursion on these lists; the matrices here are functions from the variables to their rows, as the
substitutions of `Sic.Core.Subst` are, and the identity is defined row by row, rather than by
recursion through `lift`.
-/

@[expose] public section

namespace Sic

open Grade GradeVector

-- ADE: `Substₘ`, in `Graded/Substitution.agda`.
/--
A matrix of grades, one row for each of the `n` variables of a context, whose components are over
the `m` variables of another one.
-/
def GradeMatrix (m n : Nat) := Fin n → GradeVector m

namespace GradeMatrix

-- ADE: `idSubstₘ`, in `Graded/Substitution.agda`.
/-- The identity matrix, whose row of a variable uses that variable once and no other. -/
def id : GradeMatrix n n := fun x => (𝟘ᶜ, x ≔ 𝟙)

-- ADE: `_⊙_`, in `Graded/Substitution.agda`.
/-- The matrix `Ψ` extended by the row `δ` for a new innermost variable. -/
def cons (Ψ : GradeMatrix m n) (δ : GradeVector m) : GradeMatrix m (n + 1)
  | ⟨0, _⟩ => δ
  | ⟨x + 1, h⟩ => Ψ ⟨x, Nat.lt_of_succ_lt_succ h⟩

/-- The matrix `Ψ` without the row of its innermost variable, which undoes `Ψ.cons δ`. -/
def tail (Ψ : GradeMatrix m (n + 1)) : GradeMatrix m n := fun x => Ψ x.succ

-- ADE: `liftSubstₘ`, in `Graded/Substitution.agda`.
/--
The matrix `Ψ` extended under a binder, as `Sic.Core.Subst.lift`: its rows do not use the bound
variable, whose row uses it once.
-/
def lift (Ψ : GradeMatrix m n) : GradeMatrix (m + 1) (n + 1) :=
  cons (fun x => Ψ x ∙ 𝟘) (𝟘ᶜ ∙ 𝟙)

end GradeMatrix

namespace GradeVector

-- ADE: `_<*_`, in `Graded/Substitution.agda`.
/--
`γ <* Ψ`: the vector `γ` multiplied by the matrix `Ψ`, the sum of the rows of `Ψ`, each scaled by
the grade that `γ` gives its variable.
-/
def subst : {n : Nat} → GradeVector n → GradeMatrix m n → GradeVector m
  | 0, _, _ => 𝟘ᶜ
  | _ + 1, γ, Ψ => (head γ • Ψ 0) + subst (tail γ) Ψ.tail

@[inherit_doc] scoped infixl:70 (priority := high) " <* " => GradeVector.subst

/-!
The multiplication by a matrix is linear and monotone, the identity leaves the vectors unchanged,
and the extensions of a matrix act as the extensions of a substitution, which the substitution of
the usage uses rule by rule.
-/

-- ADE: `<*-zeroˡ`, in `Graded/Substitution/Properties.agda`.
theorem zero_subst : ∀ {n : Nat} (Ψ : GradeMatrix m n), (𝟘ᶜ : GradeVector n) <* Ψ = 𝟘ᶜ
  | 0, _ => rfl
  | _ + 1, Ψ => by
    rw [subst, show tail (𝟘ᶜ : GradeVector (_ + 1)) = 𝟘ᶜ from rfl, zero_subst,
      show head (𝟘ᶜ : GradeVector (_ + 1)) = 𝟘 from rfl, zero_smul, add_zero]

/-- Two sums in a row add their first terms and their second terms. -/
private theorem add_add_add_comm (γ δ η θ : GradeVector m) :
    (γ + δ) + (η + θ) = (γ + η) + (δ + θ) := by
  rw [add_assoc, ← add_assoc δ, add_comm δ η, add_assoc, ← add_assoc]

-- ADE: `<*-distrib-+ᶜ`, in `Graded/Substitution/Properties.agda`.
theorem add_subst : ∀ {n : Nat} (γ δ : GradeVector n) (Ψ : GradeMatrix m n),
    (γ + δ) <* Ψ = (γ <* Ψ) + (δ <* Ψ)
  | 0, _, _, _ => (add_zero _).symm
  | _ + 1, γ, δ, Ψ => by
    rw [subst, subst, subst, show tail (γ + δ) = tail γ + tail δ from rfl, add_subst,
      show head (γ + δ) = head γ + head δ from rfl, add_smul, add_add_add_comm]

-- ADE: `<*-distrib-·ᶜ`, in `Graded/Substitution/Properties.agda`.
theorem smul_subst : ∀ {n : Nat} (p : Grade) (γ : GradeVector n) (Ψ : GradeMatrix m n),
    (p • γ) <* Ψ = p • (γ <* Ψ)
  | 0, p, _, _ => (smul_zero p).symm
  | _ + 1, p, γ, Ψ => by
    rw [subst, subst, show tail (p • γ) = p • tail γ from rfl, smul_subst,
      show head (p • γ) = p * head γ from rfl, mul_smul, smul_add]

-- ADE: `<*-monotone`, in `Graded/Substitution/Properties.agda`.
theorem subst_mono : ∀ {n : Nat} {γ δ : GradeVector n} (Ψ : GradeMatrix m n),
    γ ≤ δ → γ <* Ψ ≤ δ <* Ψ
  | 0, _, _, _, _ => le_refl _
  | _ + 1, _, _, Ψ, h =>
    add_mono (smul_mono (h 0) (le_refl _)) (subst_mono Ψ.tail (tail_mono h))

-- ADE: `wk1Substₘ-app`, in `Graded/Substitution/Properties.agda`.
/-- Rows that do not use a new variable sum to a vector that does not use it. -/
theorem subst_cons_zero : ∀ {n : Nat} (γ : GradeVector n) (Ψ : GradeMatrix m n),
    (γ <* fun x => Ψ x ∙ 𝟘) = (γ <* Ψ) ∙ 𝟘
  | 0, _, _ => funext fun | ⟨0, _⟩ | ⟨_ + 1, _⟩ => rfl
  | _ + 1, γ, Ψ => by
    show (head γ • (Ψ 0 ∙ 𝟘)) + (tail γ <* fun x => Ψ.tail x ∙ 𝟘) =
      ((head γ • Ψ 0) + (tail γ <* Ψ.tail)) ∙ 𝟘
    rw [subst_cons_zero]
    funext x
    match x with
    | ⟨0, _⟩ => show head γ * 𝟘 + 𝟘 = 𝟘; rw [Grade.mul_zero, Grade.add_zero]
    | ⟨_ + 1, _⟩ => rfl

-- ADE: `liftSubstₘ-app`, in `Graded/Substitution/Properties.agda`.
theorem cons_subst_lift (γ : GradeVector n) (p : Grade) (Ψ : GradeMatrix m n) :
    (γ ∙ p) <* Ψ.lift = (γ <* Ψ) ∙ p := by
  show (p • (𝟘ᶜ ∙ 𝟙)) + (γ <* fun x => Ψ x ∙ 𝟘) = _
  rw [subst_cons_zero]
  funext x
  match x with
  | ⟨0, _⟩ => show p * 𝟙 + 𝟘 = p; rw [Grade.mul_one, Grade.add_zero]
  | ⟨_ + 1, _⟩ => show p * 𝟘 + _ = _; rw [Grade.mul_zero, Grade.zero_add]; rfl

-- ADE: `consSubstₘ` and `_<*_`, in `Graded/Substitution.agda`.
theorem cons_subst_cons (γ : GradeVector n) (p : Grade) (Ψ : GradeMatrix m n)
    (δ : GradeVector m) : (γ ∙ p) <* Ψ.cons δ = (p • δ) + (γ <* Ψ) :=
  rfl

/-- Without the row of its innermost variable, the identity has the rows of a smaller identity. -/
private theorem tail_id : (GradeMatrix.id : GradeMatrix (n + 1) (n + 1)).tail =
    fun x => GradeMatrix.id x ∙ 𝟘 :=
  funext fun x => update_succ_zero x 𝟙

-- ADE: `<*-identityˡ`, in `Graded/Substitution/Properties.agda`.
theorem subst_id : ∀ {n : Nat} (γ : GradeVector n), γ <* GradeMatrix.id = γ
  | 0, _ => funext (·.elim0)
  | _ + 1, γ => by
    show (head γ • (𝟘ᶜ, 0 ≔ 𝟙)) + (tail γ <* (GradeMatrix.id.tail : GradeMatrix _ _)) = γ
    rw [update_zero_zero, tail_id, subst_cons_zero, subst_id]
    funext x
    match x with
    | ⟨0, _⟩ => show head γ * 𝟙 + 𝟘 = γ 0; rw [Grade.mul_one, Grade.add_zero]; rfl
    | ⟨_ + 1, _⟩ => show head γ * 𝟘 + _ = _; rw [Grade.mul_zero, Grade.zero_add]; rfl

-- ADE: `·ᶜ-<*-𝟘ᶜ,≔𝟙`, in `Graded/Substitution/Properties.agda`.
/-- A vector that uses only the variable `x` takes the row of `x`, scaled by its grade. -/
theorem update_zero_subst : ∀ {n : Nat} (x : Fin n) (p : Grade) (Ψ : GradeMatrix m n),
    (𝟘ᶜ, x ≔ p) <* Ψ = p • Ψ x
  | _ + 1, ⟨0, _⟩, p, Ψ => by
    show (𝟘ᶜ, 0 ≔ p) <* Ψ = p • Ψ 0
    rw [update_zero_zero]
    show (p • Ψ 0) + (𝟘ᶜ <* Ψ.tail) = _
    rw [zero_subst, add_zero]
  | _ + 1, ⟨x + 1, hx⟩, p, Ψ => by
    show (𝟘ᶜ, Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩ ≔ p) <* Ψ = _
    rw [update_succ_zero]
    show (𝟘 • Ψ 0) + ((𝟘ᶜ, _ ≔ p) <* Ψ.tail) = _
    rw [zero_smul, zero_add, update_zero_subst]
    rfl

end GradeVector

end Sic
