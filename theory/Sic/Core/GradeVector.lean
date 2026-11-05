module

public import Sic.Grade

/-!
# Vectors of Grades

The vectors of grades of RFC 24, one grade for each entry of a context, on which the operations of
the grades act component by component.
The entries are numbered by de Bruijn indices, the last entry of the context being `0`.

ADE define their vectors as sequences, extended one grade at a time; here a vector is the function
that gives each entry its grade, so that the laws of the operations follow from those of the grades
at each entry.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `Conₘ`, in `Graded/Context.agda`.
/-- A vector of grades over `n` entries, which gives each entry its grade. -/
abbrev GradeVector (n : Nat) : Type := Fin n → Grade

namespace GradeVector

variable {n : Nat}

theorem ext {γ δ : GradeVector n} (h : ∀ x, γ x = δ x) : γ = δ := funext h

instance : DecidableEq (GradeVector n) := fun γ δ =>
  decidable_of_iff (∀ x, γ x = δ x) ⟨ext, fun h _ => h ▸ rfl⟩

-- ADE: `𝟘ᶜ`, in `Graded/Context.agda`.
/-- `𝟘ᶜ`, the zero vector, whose components are all the grade `𝟘`. -/
def zero : GradeVector n := fun _ => Grade.zero

@[inherit_doc] notation "𝟘ᶜ" => zero

-- ADE: `_+ᶜ_`, in `Graded/Context.agda`.
/-- `γ +ᶜ δ`, the addition of each component. -/
def add (γ δ : GradeVector n) : GradeVector n := fun x => γ x + δ x

@[inherit_doc] infixl:65 " +ᶜ " => add

-- ADE: `_·ᶜ_`, in `Graded/Context.agda`.
/-- `p ·ᶜ γ`, the multiplication of each component by the grade `p`. -/
def smul (p : Grade) (γ : GradeVector n) : GradeVector n := fun x => p * γ x

@[inherit_doc] infixr:70 " ·ᶜ " => smul

-- ADE: `_∧ᶜ_`, in `Graded/Context.agda`.
/-- `γ ∧ᶜ δ`, the meet of each component, written `⊓ᶜ` since `∧` is the conjunction of Lean. -/
def meet (γ δ : GradeVector n) : GradeVector n := fun x => γ x ⊓ δ x

@[inherit_doc] infixl:69 " ⊓ᶜ " => meet

-- ADE: `_≤ᶜ_`, in `Graded/Context.agda`.
/-- `δ ≤ᶜ γ`, the order of each component. -/
def Le (δ γ : GradeVector n) : Prop := ∀ x, δ x ≤ γ x

@[inherit_doc] infix:50 " ≤ᶜ " => Le

instance (δ γ : GradeVector n) : Decidable (δ ≤ᶜ γ) := inferInstanceAs (Decidable (∀ _, _))

-- ADE: `_∙_`, in `Graded/Context.agda`.
/--
`γ ∙ p`, the vector `γ` extended by the grade `p` of a new entry, the last of the context, whose
de Bruijn index is `0`; the RFC writes it `γ • p`, which is the scalar multiplication of Lean.
-/
def extend (γ : GradeVector n) (p : Grade) : GradeVector (n + 1) := Fin.cases p γ

@[inherit_doc] infixl:75 " ∙ " => extend

-- ADE: `_,_≔_`, in `Graded/Context.agda`.
/-- `(γ, x ≔ p)`, the vector `γ` in which the grade of the entry `x` is replaced by `p`. -/
def update (γ : GradeVector n) (x : Fin n) (p : Grade) : GradeVector n :=
  fun y => if y = x then p else γ y

/-! ## Properties

The operations satisfy at each component the laws of the grades, as the module of ADE over their
modality does. -/

theorem add_assoc (γ δ η : GradeVector n) : (γ +ᶜ δ) +ᶜ η = γ +ᶜ (δ +ᶜ η) :=
  ext fun x => Grade.add_assoc (γ x) (δ x) (η x)

theorem add_comm (γ δ : GradeVector n) : γ +ᶜ δ = δ +ᶜ γ :=
  ext fun x => Grade.add_comm (γ x) (δ x)

theorem zero_add (γ : GradeVector n) : 𝟘ᶜ +ᶜ γ = γ :=
  ext fun x => Grade.zero_add (γ x)

theorem smul_add (p : Grade) (γ δ : GradeVector n) : p ·ᶜ (γ +ᶜ δ) = (p ·ᶜ γ) +ᶜ (p ·ᶜ δ) :=
  ext fun x => (Grade.mul_add p (γ x) (δ x)).1

theorem add_smul (p q : Grade) (γ : GradeVector n) : (p + q) ·ᶜ γ = (p ·ᶜ γ) +ᶜ (q ·ᶜ γ) :=
  ext fun x => (Grade.mul_add (γ x) p q).2

theorem mul_smul (p q : Grade) (γ : GradeVector n) : (p * q) ·ᶜ γ = p ·ᶜ (q ·ᶜ γ) :=
  ext fun x => Grade.mul_assoc p q (γ x)

theorem one_smul (γ : GradeVector n) : Grade.one ·ᶜ γ = γ :=
  ext fun x => Grade.one_mul (γ x)

theorem zero_smul (γ : GradeVector n) : Grade.zero ·ᶜ γ = 𝟘ᶜ :=
  ext fun x => Grade.zero_mul (γ x)

theorem smul_zero (p : Grade) : p ·ᶜ (𝟘ᶜ : GradeVector n) = 𝟘ᶜ :=
  ext fun _ => Grade.mul_zero p

theorem meet_comm (γ δ : GradeVector n) : γ ⊓ᶜ δ = δ ⊓ᶜ γ :=
  ext fun x => Grade.meet_comm (γ x) (δ x)

theorem le_refl (γ : GradeVector n) : γ ≤ᶜ γ := fun x => Grade.le_refl (γ x)

theorem le_trans {γ δ η : GradeVector n} (h₁ : γ ≤ᶜ δ) (h₂ : δ ≤ᶜ η) : γ ≤ᶜ η :=
  fun x => Grade.le_trans _ _ _ (h₁ x) (h₂ x)

theorem le_antisymm {γ δ : GradeVector n} (h₁ : γ ≤ᶜ δ) (h₂ : δ ≤ᶜ γ) : γ = δ :=
  ext fun x => Grade.le_antisymm _ _ (h₁ x) (h₂ x)

theorem add_le_add {γ₁ γ₂ δ₁ δ₂ : GradeVector n} (hγ : γ₁ ≤ᶜ γ₂) (hδ : δ₁ ≤ᶜ δ₂) :
    γ₁ +ᶜ δ₁ ≤ᶜ γ₂ +ᶜ δ₂ :=
  fun x => Grade.add_le_add _ _ _ _ (hγ x) (hδ x)

theorem smul_le_smul {γ δ : GradeVector n} (p : Grade) (h : γ ≤ᶜ δ) : p ·ᶜ γ ≤ᶜ p ·ᶜ δ :=
  fun x => Grade.mul_le_mul_left p _ _ (h x)

theorem le_meet_iff (γ δ η : GradeVector n) : η ≤ᶜ γ ∧ η ≤ᶜ δ ↔ η ≤ᶜ γ ⊓ᶜ δ :=
  ⟨fun ⟨h₁, h₂⟩ x => (Grade.le_meet_iff _ _ _).mp ⟨h₁ x, h₂ x⟩,
    fun h => ⟨fun x => ((Grade.le_meet_iff _ _ _).mpr (h x)).1,
      fun x => ((Grade.le_meet_iff _ _ _).mpr (h x)).2⟩⟩

/-! The extension and the update give the grade of each entry. -/

theorem extend_zero (γ : GradeVector n) (p : Grade) : (γ ∙ p) 0 = p := rfl

theorem extend_succ (γ : GradeVector n) (p : Grade) (x : Fin n) : (γ ∙ p) x.succ = γ x := rfl

theorem update_self (γ : GradeVector n) (x : Fin n) (p : Grade) : update γ x p x = p := by
  simp [update]

theorem update_other (γ : GradeVector n) {x y : Fin n} (p : Grade) (h : y ≠ x) :
    update γ x p y = γ y := by
  simp [update, h]

theorem zero_extend : (𝟘ᶜ : GradeVector n) ∙ Grade.zero = 𝟘ᶜ :=
  ext fun x => by cases x using Fin.cases <;> rfl

theorem add_extend (γ δ : GradeVector n) (p q : Grade) : (γ ∙ p) +ᶜ (δ ∙ q) = (γ +ᶜ δ) ∙ (p + q) :=
  ext fun x => by cases x using Fin.cases <;> rfl

theorem smul_extend (r : Grade) (γ : GradeVector n) (p : Grade) : r ·ᶜ (γ ∙ p) = (r ·ᶜ γ) ∙ (r * p) :=
  ext fun x => by cases x using Fin.cases <;> rfl

/-! ## Examples

The usage of the variables of the RFC: a variable `x` checked in the mode `m` uses itself with the
grade of the mode, `(𝟘ᶜ, x ≔ ⌜m⌝)`, and nothing else. -/

example : update (𝟘ᶜ : GradeVector 2) 0 Grade.one = 𝟘ᶜ ∙ Grade.one := by decide

example : (Grade.noneLinear ·ᶜ (𝟘ᶜ ∙ Grade.one : GradeVector 1)) = 𝟘ᶜ ∙ Grade.noneLinear := by
  decide

/-! The examples of the rule `(sub)`: a variable used once, with the grade `𝟙`, may be given the
grade `⟨ω, 1⟩` or `⟨ω, ω⟩`, and a variable not used, with the grade `𝟘`, the grade `⟨ω, ω⟩`. -/

example : (𝟘ᶜ ∙ Grade.unrestrictedUnrestricted : GradeVector 1) ≤ᶜ 𝟘ᶜ ∙ Grade.one := by decide

example : (𝟘ᶜ ∙ Grade.unrestrictedUnrestricted : GradeVector 1) ≤ᶜ 𝟘ᶜ := by decide

example : (𝟘ᶜ ∙ Grade.affineLinear : GradeVector 1) ≤ᶜ 𝟘ᶜ ∙ Grade.one := by decide

example : ¬ (𝟘ᶜ ∙ Grade.one : GradeVector 1) ≤ᶜ 𝟘ᶜ ∙ Grade.affineLinear := by decide

end GradeVector

end Sic.Core
