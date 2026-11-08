module

public import Sic.Modality
public import Sic.Set

/-!
# Multiplicities

The multiplicities of annex 03 of RFC 36: a multiplicity counts the uses of a variable, and is `0`,
`1` or `ω`.
They are the linear modality of ADE, whose laws are proved here, with the cases of the RFC as the
definitions of the operations and the meaning of the RFC as theorems about them.
The meet is written `⊓`, since `∧` is the conjunction of Lean.
-/

@[expose] public section

namespace Sic

-- ADE: `Linearity`, in `Graded/Modality/Instances/Linearity.agda`.
/-- A multiplicity, which counts the uses of a variable.
RFC: `\mathsf{syntax}_\pi` -/
inductive Multiplicity where
  /-- `0`: no use. -/
  | zero
  /-- `1`: one use. -/
  | one
  /-- `ω`: any number of uses, none included. -/
  | omega
  deriving DecidableEq

namespace Multiplicity

/-- The addition of the multiplicities.
RFC: `\mathsf{op}_\pi.{+}` -/
def add : Multiplicity → Multiplicity → Multiplicity
  | zero, π | π, zero => π
  | _, _ => omega

/-- The multiplication of the multiplicities.
RFC: `\mathsf{op}_\pi.{\cdot}` -/
def mul : Multiplicity → Multiplicity → Multiplicity
  | zero, _ | _, zero => zero
  | one, π | π, one => π
  | omega, omega => omega

instance : Add Multiplicity := ⟨add⟩

instance : Mul Multiplicity := ⟨mul⟩

theorem add_def (π₁ π₂ : Multiplicity) : π₁ + π₂ = add π₁ π₂ := rfl

theorem mul_def (π₁ π₂ : Multiplicity) : π₁ * π₂ = mul π₁ π₂ := rfl

/-- The meet of two multiplicities.
RFC: `\mathsf{op}_\pi.{\wedge}` -/
def meet : Multiplicity → Multiplicity → Multiplicity
  | zero, zero => zero
  | one, one => one
  | _, _ => omega

instance : Min Multiplicity := ⟨meet⟩

theorem meet_def (π₁ π₂ : Multiplicity) : π₁ ⊓ π₂ = meet π₁ π₂ := rfl

/-- The order of the multiplicities, `π₁ ≤ π₂` when `π₁ = π₁ ⊓ π₂`, as in ADE. -/
instance : LE Multiplicity where
  le := order

instance (π₁ π₂ : Multiplicity) : Decidable (π₁ ≤ π₂) :=
  inferInstanceAs (Decidable (π₁ = π₁ ⊓ π₂))

/-- Decides a statement on all the multiplicities by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∀ π, P π) :=
  decidable_of_iff (P zero ∧ P one ∧ P omega)
    ⟨fun ⟨h₀, h₁, h₂⟩ π => by cases π <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-- Decides a statement on some multiplicity by checking each of the three. -/
instance {P : Multiplicity → Prop} [DecidablePred P] : Decidable (∃ π, P π) :=
  decidable_of_iff (P zero ∨ P one ∨ P omega)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
      fun ⟨π, h⟩ => by cases π <;> simp_all⟩

/-! The tables of the RFC, row by row, in the order `0`, `1`, `ω`. -/

/-- The table of the addition, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{+}` -/
theorem add_table :
    [[zero + zero, zero + one, zero + omega],
    [one + zero, one + one, one + omega],
    [omega + zero, omega + one, omega + omega]] =
    [[zero, one, omega], [one, omega, omega], [omega, omega, omega]] := by
  decide

/-- The table of the multiplication, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{\cdot}` -/
theorem mul_table :
    [[zero * zero, zero * one, zero * omega],
    [one * zero, one * one, one * omega],
    [omega * zero, omega * one, omega * omega]] =
    [[zero, zero, zero], [zero, one, omega], [zero, omega, omega]] := by
  decide

/-- The table of the meet, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{\wedge}` -/
theorem meet_table :
    [[zero ⊓ zero, zero ⊓ one, zero ⊓ omega],
    [one ⊓ zero, one ⊓ one, one ⊓ omega],
    [omega ⊓ zero, omega ⊓ one, omega ⊓ omega]] =
    [[zero, omega, omega], [omega, one, omega], [omega, omega, omega]] := by
  decide

/-- `ω` is below `0` and below `1`, while `0` and `1` are not comparable.
RFC: `\mathsf{compare}_\pi` -/
theorem order_table :
    omega ≤ zero ∧ omega ≤ one ∧ ¬ zero ≤ one ∧ ¬ one ≤ zero := by
  decide


/-! ## Meaning -/

/-- The numbers of uses that a multiplicity allows.
RFC: `\mathsf{uses}_\pi` -/
def uses : Multiplicity → Set Nat
  | zero => { n | n = 0 }
  | one => { n | n = 1 }
  | omega => { _n | True }

@[simp] theorem mem_uses_zero {n : Nat} : n ∈ uses zero ↔ n = 0 := Iff.rfl
@[simp] theorem mem_uses_one {n : Nat} : n ∈ uses one ↔ n = 1 := Iff.rfl
@[simp] theorem mem_uses_omega {n : Nat} : n ∈ uses omega ↔ True := by simp only [uses, Set.mem_ofPred]

instance (n : Nat) (π : Multiplicity) : Decidable (n ∈ uses π) :=
  match π with
  | zero => inferInstanceAs (Decidable (n = 0))
  | one => inferInstanceAs (Decidable (n = 1))
  | omega => isTrue trivial

/--
`IsBest S π₁` says that `π₁` is the best multiplicity for the set `S` of numbers of uses,
`best(S) = π₁` in the RFC: it allows all the numbers of `S`, and allows the fewest among the
multiplicities that do.
RFC: `\mathsf{best}_\pi`
-/
def IsBest (S : Set Nat) (π₁ : Multiplicity) : Prop :=
  S ⊆ uses π₁ ∧ ∀ π₂, S ⊆ uses π₂ → uses π₁ ⊆ uses π₂

theorem le_antisymm : ∀ π₁ π₂ : Multiplicity, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁ = π₂ := by decide

/-- The order of the multiplicities is the reverse inclusion of the numbers of uses they allow: a
lower multiplicity allows more numbers of uses.
RFC: `\le_\pi` -/
theorem le_iff_uses (π₁ π₂ : Multiplicity) : π₁ ≤ π₂ ↔ uses π₂ ⊆ uses π₁ := by
  constructor
  · intro h
    cases π₁ <;> cases π₂ <;>
      first
        | exact absurd h (by decide)
        | exact fun a ha => ha
        | exact fun a _ => trivial
  · intro h
    cases π₁ <;> cases π₂ <;>
      first
        | decide
        | exact absurd (h 1 (by decide)) (by decide)
        | exact absurd (h 0 (by decide)) (by decide)

/-- The best multiplicity is unique, so that `best(S)` is well defined.
RFC: `\mathsf{unique}_\pi` -/
theorem IsBest.unique {S : Set Nat} {π₁ π₂ : Multiplicity} (h₁ : IsBest S π₁)
    (h₂ : IsBest S π₂) : π₁ = π₂ := by
  have h₁₂ := h₁.2 π₂ h₂.1
  have h₂₁ := h₂.2 π₁ h₁.1
  rw [← le_iff_uses] at h₁₂ h₂₁
  exact le_antisymm π₁ π₂ h₂₁ h₁₂

/-- The addition is the best abstraction of the addition of numbers.
RFC: `+_\pi` -/
theorem add_isBest (π₁ π₂ : Multiplicity) :
    IsBest { n | ∃ n₁ n₂, n₁ ∈ uses π₁ ∧ n₂ ∈ uses π₂ ∧ n = n₁ + n₂ } (π₁ + π₂) := by
  refine ⟨?_, ?_⟩
  · intro c ⟨a, b, ha, hb, hc⟩
    cases π₁ <;> cases π₂ <;> simp_all [add_def, add]
  · intro π₃ H
    have H' : ∀ a b, a ∈ uses π₁ → b ∈ uses π₂ → a + b ∈ uses π₃ :=
      fun a b ha hb => H (a + b) ⟨a, b, ha, hb, rfl⟩
    cases π₁ <;> cases π₂ <;> cases π₃ <;>
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

/-- The multiplication is the best abstraction of the multiplication of numbers.
RFC: `\cdot_\pi` -/
theorem mul_isBest (π₁ π₂ : Multiplicity) :
    IsBest { n | ∃ n₁ n₂, n₁ ∈ uses π₁ ∧ n₂ ∈ uses π₂ ∧ n = n₁ * n₂ } (π₁ * π₂) := by
  refine ⟨?_, ?_⟩
  · intro c ⟨a, b, ha, hb, hc⟩
    cases π₁ <;> cases π₂ <;> simp_all [mul_def, mul]
  · intro π₃ H
    have H' : ∀ a b, a ∈ uses π₁ → b ∈ uses π₂ → a * b ∈ uses π₃ :=
      fun a b ha hb => H (a * b) ⟨a, b, ha, hb, rfl⟩
    cases π₁ <;> cases π₂ <;> cases π₃ <;>
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

/-- The meet is the best abstraction of the union.
RFC: `\wedge_\pi` -/
theorem meet_isBest (π₁ π₂ : Multiplicity) : IsBest (uses π₁ ∪ uses π₂) (π₁ ⊓ π₂) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    cases π₁ <;> cases π₂ <;> simp_all [meet_def, meet]
  · intro π₃ H
    have H' : ∀ a, a ∈ uses π₁ ∨ a ∈ uses π₂ → a ∈ uses π₃ := fun a ha => H a ha
    cases π₁ <;> cases π₂ <;> cases π₃ <;>
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

The multiplicities form a modality of ADE: a semiring whose addition and multiplication distribute
over its meet, ordered by its meet, with a well-behaved zero. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
/-- The multiplicities form a modality.
RFC: `\mathsf{modality}_\pi` -/
theorem modality : IsModality Multiplicity zero one where
  semiring := {
    add_assoc := by decide
    add_comm := by decide
    zero_add := by decide
    mul_assoc := by decide
    one_mul := by decide
    mul_one := by decide
    zero_mul := by decide
    mul_zero := by decide }
  meet := {
    meet_assoc := by decide
    meet_comm := by decide
    meet_idem := by decide }
  mul_add := { left := by decide, right := by decide }
  mul_meet := { left := by decide, right := by decide }
  add_meet := { left := by decide, right := by decide }
  zero := {
    zero_ne_one := by decide
    add_eq_zero := by decide
    meet_eq_zero := by decide
    mul_eq_zero := by decide }

end Multiplicity

end Sic
