module

public import Sic.Math.Modality

/-!
# Multiplicities

The multiplicities of annex 03 of RFC 36: a multiplicity counts the uses of a variable, and is `0`,
`1` or `ω`.
They are the linear modality of ADE, whose laws are proved here, with the cases of the RFC as the
definitions of the operations; their meaning, the numbers of uses, is in `Sic/Grading/Meaning/`.
The meet is written `⊓`, since `∧` is the conjunction of Lean.
-/

@[expose] public section

namespace Sic.Grading

open Sic.Math

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

-- ADE: `_-_≡_`, in `Graded/Modality/Properties/Subtraction.agda`, a relation, with the cases of
-- `supports-subtraction`, in `Graded/Modality/Instances/Zero-one-many.agda`.
/-- The subtraction of the multiplicities: `π₁ - π₂` counts the uses left of `π₁` uses once `π₂` of
them are taken, none when they are all taken, `0` being absorbing on the left and neutral on the
right.
RFC: `\mathsf{op}_\pi.{-}` -/
def sub : Multiplicity → Multiplicity → Multiplicity
  | zero, _ => zero
  | π, zero => π
  | one, one => zero
  | _, _ => omega

instance : Sub Multiplicity := ⟨sub⟩

theorem sub_def (π₁ π₂ : Multiplicity) : π₁ - π₂ = sub π₁ π₂ := rfl

theorem meet_def (π₁ π₂ : Multiplicity) : π₁ ⊓ π₂ = meet π₁ π₂ := rfl

/-- `Σπ̄`: the sum of the multiplicities `πs`, the first one first, `0` for none.
RFC: `\mathsf{op}_\pi.\Sigma` -/
def sum : {n : Nat} → (Fin n → Multiplicity) → Multiplicity
  | 0, _ => zero
  | _ + 1, πs => πs 0 + sum fun j => πs j.succ

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

/-- The table of the subtraction, whose rows give the left operand.
RFC: `\mathsf{table}_\pi.{-}` -/
theorem sub_table :
    [[zero - zero, zero - one, zero - omega],
    [one - zero, one - one, one - omega],
    [omega - zero, omega - one, omega - omega]] =
    [[zero, zero, zero], [one, zero, omega], [omega, omega, omega]] := by
  decide

/-- `ω` is below `0` and below `1`, while `0` and `1` are not comparable.
RFC: `\mathsf{compare}_\pi` -/
theorem order_table :
    omega ≤ zero ∧ omega ≤ one ∧ ¬ zero ≤ one ∧ ¬ one ≤ zero := by
  decide

/-! ## Properties

The multiplicities form a modality of ADE: a semiring whose addition and multiplication distribute
over its meet, ordered by its meet, with a well-behaved zero. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
/-- The multiplicities form a modality.
RFC: `\mathsf{modality}_\pi` -/
theorem modality : IsModality Multiplicity zero one := by decide_laws

-- ADE: `-≡-monotoneˡ` and `supports-subtraction`, in
-- `Graded/Modality/Properties/Subtraction.agda` and `Graded/Modality/Instances/Zero-one-many.agda`.
/-- The subtraction leaves the least multiplicity `π` such that `π₁ ≤ π + π₂`, when one does: below
each of them, and one of them itself.
RFC: `\mathsf{least}_\pi.{-}` -/
theorem sub_best :
    (∀ π₁ π₂ π : Multiplicity, π₁ ≤ π + π₂ → π₁ - π₂ ≤ π) ∧
      ∀ π₁ π₂ π : Multiplicity, π₁ ≤ π + π₂ → π₁ ≤ (π₁ - π₂) + π₂ := by
  decide

theorem le_antisymm : ∀ π₁ π₂ : Multiplicity, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁ = π₂ := by decide

/-- The order of the multiplicities is reflexive. -/
theorem le_refl' : ∀ π : Multiplicity, π ≤ π := by decide

/-- The order of the multiplicities is transitive. -/
theorem le_trans' : ∀ π₁ π₂ π₃ : Multiplicity, π₁ ≤ π₂ → π₂ ≤ π₃ → π₁ ≤ π₃ := by decide

/-- The addition of the multiplicities is monotone. -/
theorem add_le_add' :
    ∀ π₁ π₂ π₃ π₄ : Multiplicity, π₁ ≤ π₂ → π₃ ≤ π₄ → π₁ + π₃ ≤ π₂ + π₄ := by
  decide

/-- The multiplication of the multiplicities is monotone in its first factor. -/
theorem mul_le_mul_right' :
    ∀ π₁ π₂ π : Multiplicity, π₁ ≤ π₂ → π₁ * π ≤ π₂ * π := by
  decide

/-- A multiplicity other than `0` times another is below it: the uses of a value at a weight other
than `0` include those of the value. -/
theorem mul_le_self : ∀ ϖ π : Multiplicity, ϖ ≠ .zero → ϖ * π ≤ π := by decide

/-- A product of multiplicities other than `0` is other than `0`. -/
theorem mul_ne_zero : ∀ ϖ π : Multiplicity, ϖ ≠ .zero → π ≠ .zero → ϖ * π ≠ .zero := by decide

/-- A multiplicity times itself is itself: the product is idempotent. -/
theorem mul_idem : ∀ π : Multiplicity, π * π = π := by decide

/-- A sum whose first operand is not `0` is not `0`. -/
theorem add_ne_zero_left : ∀ x y : Multiplicity, x ≠ .zero → x + y ≠ .zero := by decide

/-- A sum whose second operand is not `0` is not `0`. -/
theorem add_ne_zero_right : ∀ x y : Multiplicity, y ≠ .zero → x + y ≠ .zero := by
  decide

/-- A sum that is `0` has its first operand `0`. -/
theorem add_eq_zero_left : ∀ x y : Multiplicity, x + y = .zero → x = .zero := by decide

/-- A sum that is `0` has its second operand `0`. -/
theorem add_eq_zero_right : ∀ x y : Multiplicity, x + y = .zero → y = .zero := by decide

/-- A multiplicity at least `1` is `1`, the order being that of the precision. -/
theorem eq_one_of_one_le : ∀ π : Multiplicity, .one ≤ π → π = .one := by decide

/-- A product that is `1` has both its operands `1`. -/
theorem mul_eq_one : ∀ x y : Multiplicity, x * y = .one → x = .one ∧ y = .one := by decide

/-- A multiplicity above `0` is `0`: `0` is not below the others in the order of the precision. -/
theorem eq_zero_of_le_of_eq_zero : ∀ x y : Multiplicity, x ≤ y → x = .zero → y = .zero := by
  decide

/-! ## Sums -/

/-- The sum of multiplicities that are all `0` is `0`. -/
theorem sum_zero : {n : Nat} → sum (n := n) (fun _ => zero) = zero
  | 0 => rfl
  | _ + 1 => by
    simp only [sum]
    rw [sum_zero]
    rfl

/-- The sum of the sums of multiplicities, index by index, is the sum of their sums. -/
theorem sum_add : {n : Nat} → (f g : Fin n → Multiplicity) →
    sum (fun i => f i + g i) = sum f + sum g
  | 0, _, _ => rfl
  | _ + 1, f, g => by
    simp only [sum]
    rw [sum_add (fun j => f j.succ) (fun j => g j.succ)]
    exact (by decide : ∀ a b c d : Multiplicity, (a + b) + (c + d) = (a + c) + (b + d)) _ _ _ _

/-- The sum of multiplicities each multiplied by `π` is `π` times their sum. -/
theorem sum_mul (π : Multiplicity) : {n : Nat} → (f : Fin n → Multiplicity) →
    sum (fun i => π * f i) = π * sum f
  | 0, _ => by cases π <;> rfl
  | _ + 1, f => by
    simp only [sum]
    rw [sum_mul π (fun j => f j.succ)]
    exact (by decide : ∀ p a b : Multiplicity, p * a + p * b = p * (a + b)) _ _ _

/-- The sum is monotone, index by index. -/
theorem sum_le : {n : Nat} → {f g : Fin n → Multiplicity} → (∀ i, f i ≤ g i) → sum f ≤ sum g
  | 0, _, _, _ => le_refl' _
  | _ + 1, _, _, h => add_le_add' _ _ _ _ (h 0) (sum_le fun j => h j.succ)

/-- A sum whose multiplicities are `0` but at the index `i` is the multiplicity at `i`. -/
theorem sum_single : {n : Nat} → (f : Fin n → Multiplicity) → (i : Fin n) →
    (∀ j, j ≠ i → f j = zero) → sum f = f i
  | _ + 1, f, i, h => by
    simp only [sum]
    cases i using Fin.cases with
    | zero =>
      rw [show (fun j : Fin _ => f j.succ) = fun _ => zero from
        funext fun j => h j.succ (Fin.succ_ne_zero j), sum_zero]
      exact (by decide : ∀ a : Multiplicity, a + zero = a) _
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, sum_single (fun j => f j.succ) i
        (fun j hj => h j.succ fun e => hj (Fin.succ_inj.mp e))]
      exact Multiplicity.modality.semiring.zero_add _

/-- A sum over `m + k` indices whose `k` first multiplicities are `0` is the sum of the others. -/
theorem sum_addNat {m : Nat} : (k : Nat) → (f : Fin (m + k) → Multiplicity) →
    (∀ j : Fin (m + k), (j : Nat) < k → f j = zero) → sum f = sum fun x : Fin m => f (x.addNat k)
  | 0, _, _ => rfl
  | k + 1, f, h => by
    have ih := sum_addNat k (fun j : Fin (m + k) => f j.succ)
      (fun j hj => h j.succ (by simp only [Fin.val_succ]; omega))
    show f 0 + sum (fun j : Fin (m + k) => f j.succ) = _
    rw [h 0 (Nat.succ_pos k), ih]
    exact Multiplicity.modality.semiring.zero_add _

end Multiplicity

end Sic.Grading
