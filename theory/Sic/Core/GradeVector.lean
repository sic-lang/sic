module

public import Sic.Grade
public import Sic.Order

/-!
# Vectors of Grades

The vectors of grades of annex 09 of RFC 36, one grade for each entry of a context, on which the
operations of the grades act component by component.
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

-- ADE: `_≈ᶜ_`, in `Graded/Context.agda`.
/-- Two vectors are equal when they give each entry the same grade.
RFC: `\mathsf{equal}_\gamma` -/
theorem eq_iff {γ₁ γ₂ : GradeVector n} : γ₁ = γ₂ ↔ ∀ x, γ₁ x = γ₂ x :=
  ⟨fun h _ => h ▸ rfl, funext⟩

-- ADE: `𝟘ᶜ`, in `Graded/Context.agda`.
/-- `𝟘ᶜ`, the zero vector, whose components are all the grade `𝟘`.
RFC: `\mathsf{op}_\gamma.{00}` -/
def zero : GradeVector n := fun _ => Grade.zero

@[inherit_doc] notation "𝟘ᶜ" => zero

-- ADE: `_+ᶜ_`, in `Graded/Context.agda`.
/-- `γ₁ +ᶜ γ₂`, the addition of each component.
RFC: `\mathsf{op}_\gamma.{+}` -/
def add (γ₁ γ₂ : GradeVector n) : GradeVector n := fun x => γ₁ x + γ₂ x

@[inherit_doc] infixl:65 " +ᶜ " => add

-- ADE: `_·ᶜ_`, in `Graded/Context.agda`.
/-- `p ·ᶜ γ`, the multiplication of each component by the grade `p`.
RFC: `\mathsf{op}_\gamma.{\cdot}` -/
def smul (p : Grade) (γ : GradeVector n) : GradeVector n := fun x => p * γ x

@[inherit_doc] infixr:70 " ·ᶜ " => smul

-- ADE: `_∧ᶜ_`, in `Graded/Context.agda`.
/-- `γ₁ ∧ᶜ γ₂`, the meet of each component, written `⊓ᶜ` since `∧` is the conjunction of Lean.
RFC: `\mathsf{op}_\gamma.{\wedge}` -/
def meet (γ₁ γ₂ : GradeVector n) : GradeVector n := fun x => γ₁ x ⊓ γ₂ x

@[inherit_doc] infixl:69 " ⊓ᶜ " => meet

-- ADE: `_≤ᶜ_`, in `Graded/Context.agda`.
/-- `γ₁ ≤ᶜ γ₂`, the order of each component.
RFC: `\mathsf{order}_\gamma` -/
def Le (γ₁ γ₂ : GradeVector n) : Prop := ∀ x, γ₁ x ≤ γ₂ x

@[inherit_doc] infix:50 " ≤ᶜ " => Le

-- ADE: `_∙_`, in `Graded/Context.agda`.
/--
`γ ∙ p`, the vector `γ` extended by the grade `p` of a new entry, the last of the context, whose
de Bruijn index is `0`; the RFC writes it `γ • p`, which is the scalar multiplication of Lean.
RFC: `\bullet_\gamma`
-/
def extend (γ : GradeVector n) (p : Grade) : GradeVector (n + 1) := Fin.cases p γ

@[inherit_doc] infixl:75 " ∙ " => extend

-- ADE: `_,_≔_`, in `Graded/Context.agda`.
/-- `(γ, x ≔ p)`, the vector `γ` in which the grade of the entry `x` is replaced by `p`.
RFC: `\mathsf{update}_\gamma` -/
def update (γ : GradeVector n) (x : Fin n) (p : Grade) : GradeVector n :=
  fun y => if y = x then p else γ y

/-! ## Properties

The operations satisfy at each component the laws of the grades, as the module of ADE over their
modality does. -/

-- ADE: `Conₘ-semimodule`, in `Graded/Context/Properties.agda`.
/-- The addition and the multiplication by a grade make the vectors a module over the grades.
RFC: `\mathsf{module}_\gamma.\mathsf{assoc}_{+}`, `\mathsf{module}_\gamma.\mathsf{comm}_{+}`
RFC: `\mathsf{module}_\gamma.\mathsf{unit}_{+}`
RFC: `\mathsf{module}_\gamma.\mathsf{distrib}_{+^{\gamma}}`
RFC: `\mathsf{module}_\gamma.\mathsf{distrib}_{+}`
RFC: `\mathsf{module}_\gamma.\mathsf{assoc}_{\cdot}`
RFC: `\mathsf{module}_\gamma.\mathsf{unit}_{\cdot}`
RFC: `\mathsf{module}_\gamma.\mathsf{lzero}_{\cdot}`
RFC: `\mathsf{module}_\gamma.\mathsf{rzero}_{\cdot}` -/
theorem module : IsModule Grade (GradeVector n) Grade.zero Grade.one 𝟘ᶜ add smul where
  add_assoc γ₁ γ₂ γ₃ := funext fun x => Grade.modality.semiring.add_assoc (γ₁ x) (γ₂ x) (γ₃ x)
  add_comm γ₁ γ₂ := funext fun x => Grade.modality.semiring.add_comm (γ₁ x) (γ₂ x)
  zero_add γ := funext fun x => Grade.modality.semiring.zero_add (γ x)
  smul_add p γ₁ γ₂ := funext fun x => Grade.modality.mul_add.left p (γ₁ x) (γ₂ x)
  add_smul p q γ := funext fun x => Grade.modality.mul_add.right (γ x) p q
  mul_smul p q γ := funext fun x => Grade.modality.semiring.mul_assoc p q (γ x)
  one_smul γ := funext fun x => Grade.modality.semiring.one_mul (γ x)
  zero_smul γ := funext fun x => Grade.modality.semiring.zero_mul (γ x)
  smul_zero p := funext fun _ => Grade.modality.semiring.mul_zero p

-- ADE: `∧ᶜ-comm`, in `Graded/Context/Properties/Meet.agda`.
/-- The meet is commutative.
RFC: `\mathsf{meet}_\gamma` -/
theorem meet_comm (γ₁ γ₂ : GradeVector n) : γ₁ ⊓ᶜ γ₂ = γ₂ ⊓ᶜ γ₁ :=
  funext fun x => Grade.modality.meet.meet_comm (γ₁ x) (γ₂ x)

-- ADE: `≤ᶜ-preorder`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order is a preorder.
RFC: `\mathsf{preorder}_\gamma.\mathsf{refl}`, `\mathsf{preorder}_\gamma.\mathsf{trans}` -/
theorem preorder : IsPreorder (α := GradeVector n) (· ≤ᶜ ·) where
  refl γ x := Grade.le_refl (γ x)
  trans h₁ h₂ x := Grade.le_trans _ _ _ (h₁ x) (h₂ x)

-- ADE: `≤ᶜ-antisym`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order is antisymmetric.
RFC: `\mathsf{antisymmetry}_\gamma` -/
theorem le_antisymm {γ₁ γ₂ : GradeVector n} (h₁ : γ₁ ≤ᶜ γ₂) (h₂ : γ₂ ≤ᶜ γ₁) : γ₁ = γ₂ :=
  funext fun x => Grade.le_antisymm _ _ (h₁ x) (h₂ x)

-- ADE: `+ᶜ-monotone`, in `Graded/Context/Properties/Addition.agda`.
/-- The addition is monotone.
RFC: `{+}{\le}_\gamma` -/
theorem add_le_add {γ₁ γ₂ δ₁ δ₂ : GradeVector n} (hγ : γ₁ ≤ᶜ γ₂) (hδ : δ₁ ≤ᶜ δ₂) :
    γ₁ +ᶜ δ₁ ≤ᶜ γ₂ +ᶜ δ₂ :=
  fun x => Grade.add_le_add _ _ _ _ (hγ x) (hδ x)

-- ADE: `·ᶜ-monotoneʳ`, in `Graded/Context/Properties/Multiplication.agda`.
/-- The multiplication by a grade is monotone.
RFC: `{\cdot}{\le}_\gamma` -/
theorem smul_le_smul {γ₁ γ₂ : GradeVector n} (p : Grade) (h : γ₁ ≤ᶜ γ₂) : p ·ᶜ γ₁ ≤ᶜ p ·ᶜ γ₂ :=
  fun x => Grade.mul_le_mul_left p _ _ (h x)

-- ADE: `∧ᶜ-greatest-lower-bound`, `∧ᶜ-decreasingˡ` and `∧ᶜ-decreasingʳ`, in
-- `Graded/Context/Properties/Meet.agda`.
/-- The meet is the greatest lower bound of two vectors.
RFC: `{\wedge}{\le}_\gamma` -/
theorem le_meet_iff (γ₁ γ₂ γ₃ : GradeVector n) : γ₃ ≤ᶜ γ₁ ∧ γ₃ ≤ᶜ γ₂ ↔ γ₃ ≤ᶜ γ₁ ⊓ᶜ γ₂ :=
  ⟨fun ⟨h₁, h₂⟩ x => (Grade.modality.le_meet_iff _ _ _).mp ⟨h₁ x, h₂ x⟩,
    fun h => ⟨fun x => ((Grade.modality.le_meet_iff _ _ _).mpr (h x)).1,
      fun x => ((Grade.modality.le_meet_iff _ _ _).mpr (h x)).2⟩⟩

-- ADE: none, since their operations are defined by these cases, in `Graded/Context.agda`.
/-- The extension commutes with the operations. -/
structure ExtendCommutes : Prop where
  /-- The extension of the zero vector by the zero grade is the zero vector.
  RFC: `\mathsf{op}{\bullet}_\gamma.{00}` -/
  zero_extend : ∀ n, (𝟘ᶜ : GradeVector n) ∙ Grade.zero = 𝟘ᶜ
  /-- The sum of two extensions is the extension of the sums.
  RFC: `\mathsf{op}{\bullet}_\gamma.{+}` -/
  add_extend : ∀ {n} (γ₁ γ₂ : GradeVector n) (p q : Grade),
    (γ₁ ∙ p) +ᶜ (γ₂ ∙ q) = (γ₁ +ᶜ γ₂) ∙ (p + q)
  /-- The multiplication of an extension is the extension of the multiplications.
  RFC: `\mathsf{op}{\bullet}_\gamma.{\cdot}` -/
  smul_extend : ∀ {n} (r : Grade) (γ : GradeVector n) (p : Grade),
    r ·ᶜ (γ ∙ p) = (r ·ᶜ γ) ∙ (r * p)

-- ADE: none, since their operations are defined by these cases, in `Graded/Context.agda`.
/-- The extension commutes with the operations.
RFC: `\mathsf{op}{\bullet}_\gamma.{00}`, `\mathsf{op}{\bullet}_\gamma.{+}`
RFC: `\mathsf{op}{\bullet}_\gamma.{\cdot}` -/
theorem extend_commutes : ExtendCommutes where
  zero_extend _ := funext fun x => by cases x using Fin.cases <;> rfl
  add_extend _ _ _ _ := funext fun x => by cases x using Fin.cases <;> rfl
  smul_extend _ _ _ := funext fun x => by cases x using Fin.cases <;> rfl

-- ADE: `≈ᶜ-decidable`, in `Graded/Context/Properties/Equivalence.agda`.
/-- The equality of two vectors is decidable.
RFC: `\mathsf{decidable}_\gamma.{=}` -/
instance : DecidableEq (GradeVector n) := fun _ _ => decidable_of_iff _ eq_iff.symm

-- ADE: `≤ᶜ-decidable`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order of two vectors is decidable.
RFC: `\mathsf{decidable}_\gamma.{\le}` -/
instance (γ₁ γ₂ : GradeVector n) : Decidable (γ₁ ≤ᶜ γ₂) := inferInstanceAs (Decidable (∀ _, _))

end GradeVector

end Sic.Core
