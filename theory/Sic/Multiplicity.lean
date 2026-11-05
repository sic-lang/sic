module

public import Sic.Set

/-!
# Multiplicities

The multiplicities of RFC 33: a multiplicity counts the uses of a variable, and is `0`, `1` or `ω`.
They are the linear modality of ADE, whose laws are proved here, with the tables of the RFC as the
definitions of the operations and the meaning of the RFC as theorems about them.
The meet is written `⊓`, since `∧` is the conjunction of Lean.
-/

@[expose] public section

namespace Sic

-- ADE: `Linearity`, in `Graded/Modality/Instances/Linearity.agda`.
/-- A multiplicity, which counts the uses of a variable. -/
inductive Multiplicity where
  /-- `0`: no use. -/
  | zero
  /-- `1`: one use. -/
  | one
  /-- `ω`: any number of uses, none included. -/
  | omega
  deriving DecidableEq

namespace Multiplicity

/-- The addition of the multiplicities, by the first table of RFC 33. -/
def add : Multiplicity → Multiplicity → Multiplicity
  | zero, u | u, zero => u
  | _, _ => omega

/-- The multiplication of the multiplicities, by the second table of RFC 33. -/
def mul : Multiplicity → Multiplicity → Multiplicity
  | zero, _ | _, zero => zero
  | one, u | u, one => u
  | omega, omega => omega

instance : Add Multiplicity := ⟨add⟩

instance : Mul Multiplicity := ⟨mul⟩

theorem add_def (u v : Multiplicity) : u + v = add u v := rfl

theorem mul_def (u v : Multiplicity) : u * v = mul u v := rfl

/-- The meet of two multiplicities, by the third table of RFC 33. -/
def meet : Multiplicity → Multiplicity → Multiplicity
  | zero, zero => zero
  | one, one => one
  | _, _ => omega

instance : Min Multiplicity := ⟨meet⟩

/-- The meet, written as in Mathlib, on which this package does not depend. -/
infixl:69 " ⊓ " => min

theorem meet_def (u v : Multiplicity) : u ⊓ v = meet u v := rfl

/-- The order of the multiplicities, `u ≤ v` when `u = u ⊓ v`, as in ADE. -/
instance : LE Multiplicity where
  le u v := u = u ⊓ v

instance (u v : Multiplicity) : Decidable (u ≤ v) := inferInstanceAs (Decidable (u = u ⊓ v))

/-- Decides a statement on all the multiplicities by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∀ u, P u) :=
  decidable_of_iff (P zero ∧ P one ∧ P omega)
    ⟨fun ⟨h₀, h₁, h₂⟩ u => by cases u <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-- Decides a statement on some multiplicity by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∃ u, P u) :=
  decidable_of_iff (P zero ∨ P one ∨ P omega)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
      fun ⟨u, h⟩ => by cases u <;> simp_all⟩

/-! The tables of RFC 33, row by row, in the order `0`, `1`, `ω`. -/

theorem add_table :
    [[zero + zero, zero + one, zero + omega],
    [one + zero, one + one, one + omega],
    [omega + zero, omega + one, omega + omega]] =
    [[zero, one, omega], [one, omega, omega], [omega, omega, omega]] := by
  decide

theorem mul_table :
    [[zero * zero, zero * one, zero * omega],
    [one * zero, one * one, one * omega],
    [omega * zero, omega * one, omega * omega]] =
    [[zero, zero, zero], [zero, one, omega], [zero, omega, omega]] := by
  decide

theorem meet_table :
    [[zero ⊓ zero, zero ⊓ one, zero ⊓ omega],
    [one ⊓ zero, one ⊓ one, one ⊓ omega],
    [omega ⊓ zero, omega ⊓ one, omega ⊓ omega]] =
    [[zero, omega, omega], [omega, one, omega], [omega, omega, omega]] := by
  decide

/-- `ω` is below `0` and below `1`, while `0` and `1` are not comparable. -/
theorem order_table :
    omega ≤ zero ∧ omega ≤ one ∧ ¬ zero ≤ one ∧ ¬ one ≤ zero := by
  decide


/-! ## Meaning -/

/-- The numbers of uses that a multiplicity allows, `(uses_u)`. -/
def uses : Multiplicity → Set Nat
  | zero => { a | a = 0 }
  | one => { a | a = 1 }
  | omega => { _a | True }

@[simp] theorem mem_uses_zero {a : Nat} : a ∈ uses zero ↔ a = 0 := Iff.rfl
@[simp] theorem mem_uses_one {a : Nat} : a ∈ uses one ↔ a = 1 := Iff.rfl
@[simp] theorem mem_uses_omega {a : Nat} : a ∈ uses omega ↔ True := by simp only [uses, Set.mem_ofPred]

instance (a : Nat) (u : Multiplicity) : Decidable (a ∈ uses u) :=
  match u with
  | zero => inferInstanceAs (Decidable (a = 0))
  | one => inferInstanceAs (Decidable (a = 1))
  | omega => isTrue trivial

/--
`IsBest S u` says that `u` is the best multiplicity for the set `S` of numbers of uses, `best(S) = u`
in RFC 33: it allows all the numbers of `S`, and allows the fewest among the multiplicities that do.
-/
def IsBest (S : Set Nat) (u : Multiplicity) : Prop :=
  S ⊆ uses u ∧ ∀ w, S ⊆ uses w → uses u ⊆ uses w

theorem le_antisymm : ∀ u v : Multiplicity, u ≤ v → v ≤ u → u = v := by decide

/-- The order of the multiplicities is the reverse inclusion of the numbers of uses they allow,
`(≤_u)`: a lower multiplicity allows more numbers of uses. -/
theorem le_iff_uses (u v : Multiplicity) : u ≤ v ↔ uses v ⊆ uses u := by
  constructor
  · intro h
    cases u <;> cases v <;>
      first
        | exact absurd h (by decide)
        | exact fun a ha => ha
        | exact fun a _ => trivial
  · intro h
    cases u <;> cases v <;>
      first
        | decide
        | exact absurd (h 1 (by decide)) (by decide)
        | exact absurd (h 0 (by decide)) (by decide)

/-- The best multiplicity is unique, so that `best(S)` is well defined. -/
theorem IsBest.unique {S : Set Nat} {u v : Multiplicity} (hu : IsBest S u) (hv : IsBest S v) :
    u = v := by
  have h₁ := hu.2 v hv.1
  have h₂ := hv.2 u hu.1
  rw [← le_iff_uses] at h₁ h₂
  exact le_antisymm u v h₂ h₁

/-- The addition is the best abstraction of the addition of numbers, `(+_u)`. -/
theorem add_isBest (u v : Multiplicity) :
    IsBest { c | ∃ a b, a ∈ uses u ∧ b ∈ uses v ∧ c = a + b } (u + v) := by
  refine ⟨?_, ?_⟩
  · intro c ⟨a, b, ha, hb, hc⟩
    cases u <;> cases v <;> simp_all [add_def, add]
  · intro w H
    have H' : ∀ a b, a ∈ uses u → b ∈ uses v → a + b ∈ uses w :=
      fun a b ha hb => H (a + b) ⟨a, b, ha, hb, rfl⟩
    cases u <;> cases v <;> cases w <;>
      simp only [Set.subset_def, mem_uses_zero, mem_uses_one, mem_uses_omega, true_implies,
        add_def, add] at H' ⊢ <;>
    first
      | (intros; assumption)
      | (intros; trivial)
      | exfalso
        have h00 := H' 0 0
        have h01 := H' 0 1
        have h10 := H' 1 0
        have h11 := H' 1 1
        have h02 := H' 0 2
        have h20 := H' 2 0
        have h12 := H' 1 2
        have h21 := H' 2 1
        have h22 := H' 2 2
        simp at h00 h01 h10 h11 h02 h20 h12 h21 h22

/-- The multiplication is the best abstraction of the multiplication of numbers, `(·_u)`. -/
theorem mul_isBest (u v : Multiplicity) :
    IsBest { c | ∃ a b, a ∈ uses u ∧ b ∈ uses v ∧ c = a * b } (u * v) := by
  refine ⟨?_, ?_⟩
  · intro c ⟨a, b, ha, hb, hc⟩
    cases u <;> cases v <;> simp_all [mul_def, mul]
  · intro w H
    have H' : ∀ a b, a ∈ uses u → b ∈ uses v → a * b ∈ uses w :=
      fun a b ha hb => H (a * b) ⟨a, b, ha, hb, rfl⟩
    cases u <;> cases v <;> cases w <;>
      simp only [Set.subset_def, mem_uses_zero, mem_uses_one, mem_uses_omega, true_implies,
        mul_def, mul] at H' ⊢ <;>
    first
      | (intros; assumption)
      | (intros; trivial)
      | exfalso
        have h00 := H' 0 0
        have h01 := H' 0 1
        have h10 := H' 1 0
        have h11 := H' 1 1
        have h02 := H' 0 2
        have h20 := H' 2 0
        have h12 := H' 1 2
        have h21 := H' 2 1
        have h22 := H' 2 2
        simp at h00 h01 h10 h11 h02 h20 h12 h21 h22

/-- The meet is the best abstraction of the union, `(∧_u)`. -/
theorem meet_isBest (u v : Multiplicity) : IsBest (uses u ∪ uses v) (u ⊓ v) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    cases u <;> cases v <;> simp_all [meet_def, meet]
  · intro w H
    have H' : ∀ a, a ∈ uses u ∨ a ∈ uses v → a ∈ uses w := fun a ha => H a ha
    cases u <;> cases v <;> cases w <;>
      simp only [Set.subset_def, mem_uses_zero, mem_uses_one, mem_uses_omega,
        true_implies, meet_def, meet] at H' ⊢ <;>
    first
      | (intros; assumption)
      | (intros; trivial)
      | exfalso
        have h0 := H' 0
        have h1 := H' 1
        have h2 := H' 2
        simp at h0 h1 h2

/-! ## Properties

The multiplicities satisfy the properties that RFC 33 states for the grades, from which they are
those of a modality of ADE: a semiring ordered by its meet, whose zero is well behaved. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
theorem add_assoc : ∀ u v w : Multiplicity, (u + v) + w = u + (v + w) := by decide

theorem add_comm : ∀ u v : Multiplicity, u + v = v + u := by decide

theorem zero_add : ∀ u : Multiplicity, zero + u = u := by decide

theorem mul_assoc : ∀ u v w : Multiplicity, (u * v) * w = u * (v * w) := by decide

theorem one_mul : ∀ u : Multiplicity, one * u = u := by decide

theorem mul_one : ∀ u : Multiplicity, u * one = u := by decide

theorem zero_mul : ∀ u : Multiplicity, zero * u = zero := by decide

theorem mul_zero : ∀ u : Multiplicity, u * zero = zero := by decide

theorem meet_assoc : ∀ u v w : Multiplicity, (u ⊓ v) ⊓ w = u ⊓ (v ⊓ w) := by decide

theorem meet_comm : ∀ u v : Multiplicity, u ⊓ v = v ⊓ u := by decide

theorem meet_idem : ∀ u : Multiplicity, u ⊓ u = u := by decide

/-- `(·₊)`: the multiplication distributes over the addition. -/
theorem mul_add : ∀ u v w : Multiplicity,
    u * (v + w) = (u * v) + (u * w) ∧ (v + w) * u = (v * u) + (w * u) := by
  decide

/-- `(·∧)`: the multiplication distributes over the meet. -/
theorem mul_meet : ∀ u v w : Multiplicity,
    u * (v ⊓ w) = (u * v) ⊓ (u * w) ∧ (v ⊓ w) * u = (v * u) ⊓ (w * u) := by
  decide

theorem add_meet : ∀ u v w : Multiplicity,
    u + (v ⊓ w) = (u + v) ⊓ (u + w) ∧ (v ⊓ w) + u = (v + u) ⊓ (w + u) := by
  decide

/-- `(+≤)`: the addition is monotone. -/
theorem add_le_add_right : ∀ u v w : Multiplicity, u ≤ v → u + w ≤ v + w := by decide

/-- `(∧≤)`: the meet is the greatest lower bound of two multiplicities. -/
theorem le_meet_iff : ∀ u v w : Multiplicity, w ≤ u ∧ w ≤ v ↔ w ≤ u ⊓ v := by decide

/-- `(𝟘ₚ)`: the zero is well behaved. -/
theorem zero_well_behaved :
    zero ≠ one ∧ (∀ u v : Multiplicity, u + v = zero → u = zero ∧ v = zero) ∧
      (∀ u v : Multiplicity, u ⊓ v = zero → u = zero ∧ v = zero) ∧
      ∀ u v : Multiplicity, u * v = zero → u = zero ∨ v = zero := by
  decide

theorem add_eq_zero : ∀ u v : Multiplicity, u + v = zero ↔ u = zero ∧ v = zero := by decide

theorem meet_eq_zero : ∀ u v : Multiplicity, u ⊓ v = zero ↔ u = zero ∧ v = zero := by decide

theorem mul_eq_zero : ∀ u v : Multiplicity, u * v = zero ↔ u = zero ∨ v = zero := by decide

end Multiplicity

end Sic
