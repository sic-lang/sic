module

public import Sic.Math.Modality
public import Sic.Math.Order

/-!
# Vectors

The vectors of annex 10 of RFC 36, one element of a modality for each index of a finite set, on
which the operations of the modality act index by index.
The indices of a vector of `n` elements are the numbers below `n`, the index `0` being the one that
extends a vector, as the de Bruijn indices number the entries of a context, the last one first.

ADE define their vectors as sequences, extended one element at a time; here a vector is the function
that gives each index its element, so that the laws of the operations follow from those of the
modality at each index.
The operations and their laws hold whatever the set of the indices, finite or not, so that they are
stated on the functions from any type of indices, of which the vectors are those from the numbers
below `n`: the demands of annex 17, which give each address of a heap a multiplicity, use them.
The core of Lean declares at its root a `Vector`, an array of a fixed size ordered
lexicographically, so that this one is always written with its full name, `Sic.Math.Vector`, outside
its namespace.
-/

@[expose] public section

namespace Sic.Math

-- ADE: `Conₘ`, in `Graded/Context.agda`.
/-- A vector of `n` elements of `α`, which gives each index its element.
RFC: `\mathsf{vector}_\mu` -/
abbrev Vector (α : Type) (n : Nat) : Type := Fin n → α

namespace Vector

variable {α ι : Type} {n : Nat}

-- ADE: `_≈ᶜ_`, in `Graded/Context.agda`.
/-- Two vectors are equal when they give each index the same element.
RFC: `\mathsf{equal}_\mu` -/
theorem eq_iff {μ₁ μ₂ : ι → α} : μ₁ = μ₂ ↔ ∀ i, μ₁ i = μ₂ i :=
  ⟨fun h _ => h ▸ rfl, funext⟩

-- ADE: `𝟘ᶜ`, in `Graded/Context.agda`.
/-- The zero vector, which gives each index the element `zero`, the zero of the modality.
RFC: `\mathsf{op}_\mu.0` -/
def zero (zero : α) : ι → α := fun _ => zero

-- ADE: `_+ᶜ_`, in `Graded/Context.agda`.
/-- `μ₁ +ᶜ μ₂`, the addition at each index.
RFC: `\mathsf{op}_\mu.{+}` -/
def add [Add α] (μ₁ μ₂ : ι → α) : ι → α := fun i => μ₁ i + μ₂ i

@[inherit_doc] infixl:65 " +ᶜ " => add

-- ADE: `_·ᶜ_`, in `Graded/Context.agda`.
/-- `ξ ·ᶜ μ`, the multiplication of the element at each index by the element `ξ`.
RFC: `\mathsf{op}_\mu.{\cdot}` -/
def smul [Mul α] (ξ : α) (μ : ι → α) : ι → α := fun i => ξ * μ i

@[inherit_doc] infixr:70 " ·ᶜ " => smul

-- ADE: `_∧ᶜ_`, in `Graded/Context.agda`.
/-- `μ₁ ⊓ᶜ μ₂`, the meet at each index, written `⊓ᶜ` since `∧` is the conjunction of Lean.
RFC: `\mathsf{op}_\mu.{\wedge}` -/
def meet [Min α] (μ₁ μ₂ : ι → α) : ι → α := fun i => μ₁ i ⊓ μ₂ i

@[inherit_doc] infixl:69 " ⊓ᶜ " => meet

-- ADE: `_≤ᶜ_`, in `Graded/Context.agda`.
/-- `μ₁ ≤ᶜ μ₂`, the order of the modality at each index.
RFC: `\mathsf{order}_\mu` -/
def Le [Min α] (μ₁ μ₂ : ι → α) : Prop := ∀ i, order (μ₁ i) (μ₂ i)

@[inherit_doc] infix:50 " ≤ᶜ " => Le

-- ADE: `_∙_`, in `Graded/Context.agda`.
/--
`μ ∙ ξ`, the vector `μ` extended by the element `ξ` at a new index, `0`, the other indices being
shifted; the RFC writes it `μ • ξ`, which is the scalar multiplication of Lean.
RFC: `\bullet_\mu`
-/
def extend (μ : Vector α n) (ξ : α) : Vector α (n + 1) := Fin.cases ξ μ

@[inherit_doc] infixl:75 " ∙ " => extend

-- ADE: `_,_≔_`, in `Graded/Context.agda`.
/-- `(μ, i ≔ ξ)`, the vector `μ` in which the element at the index `i` is replaced by `ξ`.
RFC: `\mathsf{update}_\mu` -/
def update (μ : Vector α n) (i : Fin n) (ξ : α) : Vector α n :=
  fun j => if j = i then ξ else μ j

/-! ## Properties

The operations satisfy at each index the laws of a modality, as the module of ADE over a modality
does. -/

variable [Add α] [Mul α] [Min α] {zero one : α}

-- ADE: `Conₘ-semimodule`, in `Graded/Context/Properties.agda`.
/-- The addition and the multiplication by an element make the vectors a module over the modality.
RFC: `\mathsf{module}_\mu.\mathsf{assoc}_{+}`
RFC: `\mathsf{module}_\mu.\mathsf{comm}_{+}`
RFC: `\mathsf{module}_\mu.\mathsf{unit}_{+}`
RFC: `\mathsf{module}_\mu.\mathsf{distrib}_{+^{\mu}}`
RFC: `\mathsf{module}_\mu.\mathsf{distrib}_{+}`
RFC: `\mathsf{module}_\mu.\mathsf{assoc}_{\cdot}`
RFC: `\mathsf{module}_\mu.\mathsf{unit}_{\cdot}`
RFC: `\mathsf{module}_\mu.\mathsf{lzero}_{\cdot}`
RFC: `\mathsf{module}_\mu.\mathsf{rzero}_{\cdot}` -/
theorem module (h : IsModality α zero one) :
    IsModule α (ι → α) zero one (Vector.zero zero) add smul where
  add_assoc μ₁ μ₂ μ₃ := funext fun i => h.semiring.add_assoc (μ₁ i) (μ₂ i) (μ₃ i)
  add_comm μ₁ μ₂ := funext fun i => h.semiring.add_comm (μ₁ i) (μ₂ i)
  zero_add μ := funext fun i => h.semiring.zero_add (μ i)
  smul_add ξ μ₁ μ₂ := funext fun i => h.mul_add.left ξ (μ₁ i) (μ₂ i)
  add_smul ξ₁ ξ₂ μ := funext fun i => h.mul_add.right (μ i) ξ₁ ξ₂
  mul_smul ξ₁ ξ₂ μ := funext fun i => h.semiring.mul_assoc ξ₁ ξ₂ (μ i)
  one_smul μ := funext fun i => h.semiring.one_mul (μ i)
  zero_smul μ := funext fun i => h.semiring.zero_mul (μ i)
  smul_zero ξ := funext fun _ => h.semiring.mul_zero ξ

-- ADE: `∧ᶜ-comm`, in `Graded/Context/Properties/Meet.agda`.
/-- The meet is commutative.
RFC: `\mathsf{meet}_\mu` -/
theorem meet_comm (h : IsModality α zero one) (μ₁ μ₂ : ι → α) : μ₁ ⊓ᶜ μ₂ = μ₂ ⊓ᶜ μ₁ :=
  funext fun i => h.meet.meet_comm (μ₁ i) (μ₂ i)

-- ADE: `≤ᶜ-preorder`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order is a preorder.
RFC: `\mathsf{preorder}_\mu.\mathsf{refl}`
RFC: `\mathsf{preorder}_\mu.\mathsf{trans}` -/
theorem preorder (h : IsModality α zero one) : IsPreorder (α := ι → α) (· ≤ᶜ ·) where
  refl μ i := (h.meet.meet_idem (μ i)).symm
  trans h₁ h₂ i := by
    unfold order
    rw [h₁ i, h.meet.meet_assoc, ← h₂ i]

-- ADE: `≤ᶜ-antisym`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order is antisymmetric.
RFC: `\mathsf{antisymmetry}_\mu` -/
theorem le_antisymm (h : IsModality α zero one) {μ₁ μ₂ : ι → α} (h₁ : μ₁ ≤ᶜ μ₂)
    (h₂ : μ₂ ≤ᶜ μ₁) : μ₁ = μ₂ :=
  funext fun i => (h₁ i).trans ((h.meet.meet_comm _ _).trans (h₂ i).symm)

-- ADE: `+ᶜ-monotone`, in `Graded/Context/Properties/Addition.agda`.
/-- The addition is monotone.
RFC: `{+}{\le}_\mu` -/
theorem add_le_add (h : IsModality α zero one) {μ₁ μ₂ ν₁ ν₂ : ι → α} (hμ : μ₁ ≤ᶜ μ₂)
    (hν : ν₁ ≤ᶜ ν₂) : μ₁ +ᶜ ν₁ ≤ᶜ μ₂ +ᶜ ν₂ :=
  (preorder h).trans (b := μ₂ +ᶜ ν₁) (fun i => h.add_le _ _ _ (hμ i)) fun i => by
    show order (μ₂ i + ν₁ i) (μ₂ i + ν₂ i)
    rw [h.semiring.add_comm (μ₂ i) (ν₁ i), h.semiring.add_comm (μ₂ i) (ν₂ i)]
    exact h.add_le _ _ _ (hν i)

-- ADE: `·ᶜ-monotoneʳ`, in `Graded/Context/Properties/Multiplication.agda`.
/-- The multiplication by an element is monotone.
RFC: `{\cdot}{\le}_\mu` -/
theorem smul_le_smul (h : IsModality α zero one) {μ₁ μ₂ : ι → α} (ξ : α) (hμ : μ₁ ≤ᶜ μ₂) :
    ξ ·ᶜ μ₁ ≤ᶜ ξ ·ᶜ μ₂ :=
  fun i => by
    show ξ * μ₁ i = ξ * μ₁ i ⊓ ξ * μ₂ i
    rw [← h.mul_meet.left, ← hμ i]

-- ADE: `∧ᶜ-greatest-lower-bound`, `∧ᶜ-decreasingˡ` and `∧ᶜ-decreasingʳ`, in
-- `Graded/Context/Properties/Meet.agda`.
/-- The meet is the greatest lower bound of two vectors.
RFC: `{\wedge}{\le}_\mu` -/
theorem le_meet_iff (h : IsModality α zero one) (μ₁ μ₂ μ₃ : ι → α) :
    μ₃ ≤ᶜ μ₁ ∧ μ₃ ≤ᶜ μ₂ ↔ μ₃ ≤ᶜ μ₁ ⊓ᶜ μ₂ :=
  ⟨fun ⟨h₁, h₂⟩ i => (h.le_meet_iff _ _ _).mp ⟨h₁ i, h₂ i⟩,
    fun h' => ⟨fun i => ((h.le_meet_iff _ _ _).mpr (h' i)).1,
      fun i => ((h.le_meet_iff _ _ _).mpr (h' i)).2⟩⟩

-- ADE: none, since their operations are defined by these cases, in `Graded/Context.agda`.
/-- The extension commutes with the operations. -/
structure ExtendCommutes (α : Type) [Add α] [Mul α] (zero : α) : Prop where
  /-- The extension of the zero vector by the zero is the zero vector.
  RFC: `\mathsf{op}{\bullet}_\mu.0` -/
  zero_extend : ∀ n, (Vector.zero zero : Vector α n) ∙ zero = Vector.zero zero
  /-- The sum of two extensions is the extension of the sums.
  RFC: `\mathsf{op}{\bullet}_\mu.{+}` -/
  add_extend : ∀ {n} (μ₁ μ₂ : Vector α n) (ξ₁ ξ₂ : α),
    (μ₁ ∙ ξ₁) +ᶜ (μ₂ ∙ ξ₂) = (μ₁ +ᶜ μ₂) ∙ (ξ₁ + ξ₂)
  /-- The multiplication of an extension is the extension of the multiplications.
  RFC: `\mathsf{op}{\bullet}_\mu.{\cdot}` -/
  smul_extend : ∀ {n} (ξ₁ : α) (μ : Vector α n) (ξ₂ : α),
    ξ₁ ·ᶜ (μ ∙ ξ₂) = (ξ₁ ·ᶜ μ) ∙ (ξ₁ * ξ₂)

omit [Min α] in
-- ADE: none, since their operations are defined by these cases, in `Graded/Context.agda`.
/-- The extension commutes with the operations, whatever the laws of `α`.
RFC: `\mathsf{op}{\bullet}_\mu.0`
RFC: `\mathsf{op}{\bullet}_\mu.{+}`
RFC: `\mathsf{op}{\bullet}_\mu.{\cdot}` -/
theorem extend_commutes : ExtendCommutes α zero where
  zero_extend _ := funext fun i => by cases i using Fin.cases <;> rfl
  add_extend _ _ _ _ := funext fun i => by cases i using Fin.cases <;> rfl
  smul_extend _ _ _ := funext fun i => by cases i using Fin.cases <;> rfl

-- ADE: `≈ᶜ-decidable`, in `Graded/Context/Properties/Equivalence.agda`.
/-- The equality of two vectors is decidable when that of their elements is.
RFC: `\mathsf{decidable}_\mu.{=}` -/
instance [DecidableEq α] : DecidableEq (Vector α n) := fun _ _ => decidable_of_iff _ eq_iff.symm

-- ADE: `≤ᶜ-decidable`, in `Graded/Context/Properties/PartialOrder.agda`.
/-- The order of two vectors is decidable when the equality of their elements is.
RFC: `\mathsf{decidable}_\mu.{\le}` -/
instance [DecidableEq α] (μ₁ μ₂ : Vector α n) : Decidable (μ₁ ≤ᶜ μ₂) :=
  inferInstanceAs (Decidable (∀ _, _))

end Vector

end Sic.Math
