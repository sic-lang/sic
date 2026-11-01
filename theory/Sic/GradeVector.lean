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

-- ADE: `≤ᶜ-decidable`, in `Graded/Context/Properties/PartialOrder.agda`.
/--
The order of two vectors is decided on each component, with the components given explicitly, since
the search of instances does not unfold `GradeVector` to see the functions that it holds.
-/
instance (γ δ : GradeVector n) : Decidable (γ ≤ δ) :=
  @Nat.decidableForallFin n (fun x => γ x ≤ δ x) fun _ => inferInstance

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

-- ADE: `headₘ`, in `Graded/Context.agda`.
/-- The grade of the innermost variable of `δ`, which `δ ∙ p` gives. -/
def head (δ : GradeVector (n + 1)) : Grade := δ 0

-- ADE: `tailₘ`, in `Graded/Context.agda`.
/-- The vector `δ` without the grade of its innermost variable, which undoes `δ ∙ p`. -/
def tail (δ : GradeVector (n + 1)) : GradeVector n := fun x => δ x.succ

/-! The order is a preorder, which the inversions of the usage use to compose its bounds. -/

-- ADE: `≤ᶜ-refl`, in `Graded/Context/Properties/PartialOrder.agda`.
theorem le_refl (γ : GradeVector n) : γ ≤ γ := fun _ => Grade.le_refl _
-- ADE: `≤ᶜ-trans`, in `Graded/Context/Properties/PartialOrder.agda`.
theorem le_trans {γ δ η : GradeVector n} (h₁ : γ ≤ δ) (h₂ : δ ≤ η) : γ ≤ η :=
  fun x => Grade.le_trans (h₁ x) (h₂ x)

/-!
The vectors inherit the laws of the grades, component by component, which the multiplication of the
vectors by the matrices of `Sic.GradeMatrix` uses to distribute over their operations.
-/

-- ADE: `+ᶜ-assoc`, in `Graded/Context/Properties/Addition.agda`.
theorem add_assoc (γ δ η : GradeVector n) : (γ + δ) + η = γ + (δ + η) :=
  funext fun _ => Grade.add_assoc ..
-- ADE: `+ᶜ-comm`, in `Graded/Context/Properties/Addition.agda`.
theorem add_comm (γ δ : GradeVector n) : γ + δ = δ + γ := funext fun _ => Grade.add_comm ..
-- ADE: `+ᶜ-identityˡ`, in `Graded/Context/Properties/Addition.agda`.
theorem zero_add (γ : GradeVector n) : 𝟘ᶜ + γ = γ := funext fun _ => Grade.zero_add ..
-- ADE: `+ᶜ-identityʳ`, in `Graded/Context/Properties/Addition.agda`.
theorem add_zero (γ : GradeVector n) : γ + 𝟘ᶜ = γ := funext fun _ => Grade.add_zero ..

-- ADE: `·ᶜ-assoc`, in `Graded/Context/Properties/Multiplication.agda`.
theorem mul_smul (p q : Grade) (γ : GradeVector n) : (p * q) • γ = p • (q • γ) :=
  funext fun _ => Grade.mul_assoc ..
-- ADE: `·ᶜ-zeroˡ`, in `Graded/Context/Properties/Multiplication.agda`.
theorem zero_smul (γ : GradeVector n) : 𝟘 • γ = 𝟘ᶜ := funext fun _ => Grade.zero_mul ..
-- ADE: `·ᶜ-zeroʳ`, in `Graded/Context/Properties/Multiplication.agda`.
theorem smul_zero (p : Grade) : p • (𝟘ᶜ : GradeVector n) = 𝟘ᶜ := funext fun _ => Grade.mul_zero ..
-- ADE: `·ᶜ-distribˡ-+ᶜ`, in `Graded/Context/Properties/Multiplication.agda`.
theorem smul_add (p : Grade) (γ δ : GradeVector n) : p • (γ + δ) = (p • γ) + (p • δ) :=
  funext fun _ => Grade.mul_add ..
-- ADE: `·ᶜ-distribʳ-+ᶜ`, in `Graded/Context/Properties/Multiplication.agda`.
theorem add_smul (p q : Grade) (γ : GradeVector n) : (p + q) • γ = (p • γ) + (q • γ) :=
  funext fun _ => Grade.add_mul ..

/-!
The replacement and the extension of the grades, which the weakening and the substitution of the
usage use to follow the variables under a binder: the zero vector with the grade of one variable
replaced, as the rule of the variables gives it, extends a smaller one.
-/

-- ADE: none.
/-- The zero vector whose innermost variable has the grade `p` extends the zero vector by `p`. -/
theorem update_zero_zero (p : Grade) : (𝟘ᶜ, (0 : Fin (n + 1)) ≔ p) = 𝟘ᶜ ∙ p :=
  funext fun
    | ⟨0, _⟩ => ite_eq_left rfl
    | ⟨y + 1, _⟩ => ite_eq_right (Fin.succ_ne_zero ⟨y, by omega⟩)

-- ADE: none.
/-- The zero vector whose outer variable `x.succ` has the grade `p` extends one with `x` by `𝟘`. -/
theorem update_succ_zero (x : Fin n) (p : Grade) : (𝟘ᶜ, x.succ ≔ p) = (𝟘ᶜ, x ≔ p) ∙ 𝟘 :=
  funext fun
    | ⟨0, _⟩ => ite_eq_right (Fin.succ_ne_zero x).symm
    | ⟨y + 1, hy⟩ => by
      show (if Fin.succ ⟨y, Nat.lt_of_succ_lt_succ hy⟩ = x.succ then p else 𝟘) =
        if ⟨y, Nat.lt_of_succ_lt_succ hy⟩ = x then p else 𝟘
      by_cases h : (⟨y, Nat.lt_of_succ_lt_succ hy⟩ : Fin n) = x
      · rw [ite_eq_left (congrArg Fin.succ h), ite_eq_left h]
      · rw [ite_eq_right fun e => h (Fin.succ_inj.1 e), ite_eq_right h]

/-!
The operations are monotone, which the inference of the usage uses to bound every usage by the one
that it infers.
-/

-- ADE: `+ᶜ-monotone`, in `Graded/Context/Properties/Addition.agda`.
theorem add_mono {γ γ' δ δ' : GradeVector n} (h₁ : γ ≤ γ') (h₂ : δ ≤ δ') : γ + δ ≤ γ' + δ' :=
  fun x => add_le_add (h₁ x) (h₂ x)

-- ADE: `·ᶜ-monotone`, in `Graded/Context/Properties/Multiplication.agda`.
theorem smul_mono {p p' : Grade} {γ γ' : GradeVector n} (h₁ : p ≤ p') (h₂ : γ ≤ γ') :
    p • γ ≤ p' • γ' :=
  fun x => mul_le_mul h₁ (h₂ x)

-- ADE: `tailₘ-monotone`, in `Graded/Context/Properties.agda`.
theorem tail_mono {γ δ : GradeVector (n + 1)} (h : γ ≤ δ) : tail γ ≤ tail δ := fun x => h x.succ

-- ADE: none.
/--
A vector is above its tail extended by a grade below its head, which `(sub)` uses to give a binder
a grade lower than the uses of its variable.
-/
theorem cons_tail_le {δ : GradeVector (n + 1)} (h : p ≤ head δ) : tail δ ∙ p ≤ δ
  | ⟨0, _⟩ => h
  | ⟨_ + 1, _⟩ => Grade.le_refl _

end GradeVector

end Sic
