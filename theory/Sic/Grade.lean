import Sic.Usage

/-!
# Grades

The grades of RFC 24: a grade counts the uses of a variable at run time and in total, each count
being a usage.
The seven grades form a modality of ADE whose zero is well behaved, proved at the end.
-/

namespace Sic

open Usage

/--
A grade: the usages of a variable at run time and in total.
The run-time uses are among all the uses, which excludes two of the nine pairs.
-/
@[ext]
structure Grade where
  run : Usage
  total : Usage
  run_zero : total = zero → run = zero
  deriving DecidableEq

namespace Grade

/-- `𝟘`: no use. -/
def zero : Grade := ⟨.zero, .zero, fun _ => rfl⟩

/-- `𝟙`: one use, at run time. -/
def one : Grade := ⟨.one, .one, fun h => nomatch h⟩

@[inherit_doc] scoped notation "𝟘" => Grade.zero
@[inherit_doc] scoped notation "𝟙" => Grade.one

/-! The operations act on each usage, and the grades are closed under them. -/

instance : Add Grade where
  add p q := ⟨p.run + q.run, p.total + q.total, fun h =>
    have ⟨hp, hq⟩ := add_eq_zero h
    by rw [p.run_zero hp, q.run_zero hq]; rfl⟩

instance : Mul Grade where
  mul p q := ⟨p.run * q.run, p.total * q.total, fun h =>
    match mul_eq_zero h with
    | .inl hp => by rw [p.run_zero hp]; cases q.run <;> rfl
    | .inr hq => by rw [q.run_zero hq]; cases p.run <;> rfl⟩

instance : Min Grade where
  min p q := ⟨p.run ⊓ q.run, p.total ⊓ q.total, fun h =>
    have ⟨hp, hq⟩ := min_eq_zero h
    by rw [p.run_zero hp, q.run_zero hq]; rfl⟩

/-- The order of ADE: a variable of grade `p` may be used where the grade `q` is expected. -/
instance : LE Grade where
  le p q := p = p ⊓ q

/-! The modality of ADE: a semiring with a meet semilattice over which the operations distribute. -/

section Modality

variable (p q r : Grade)

theorem add_assoc : (p + q) + r = p + (q + r) := by
  ext <;> apply Usage.add_assoc
theorem add_comm : p + q = q + p := by
  ext <;> apply Usage.add_comm
theorem zero_add : 𝟘 + p = p := by
  ext <;> apply Usage.zero_add
theorem add_zero : p + 𝟘 = p := by
  ext <;> apply Usage.add_zero
theorem mul_assoc : (p * q) * r = p * (q * r) := by
  ext <;> apply Usage.mul_assoc
theorem one_mul : 𝟙 * p = p := by
  ext <;> apply Usage.one_mul
theorem mul_one : p * 𝟙 = p := by
  ext <;> apply Usage.mul_one
theorem zero_mul : 𝟘 * p = 𝟘 := by
  ext <;> apply Usage.zero_mul
theorem mul_zero : p * 𝟘 = 𝟘 := by
  ext <;> apply Usage.mul_zero
theorem mul_add : p * (q + r) = (p * q) + (p * r) := by
  ext <;> apply Usage.mul_add
theorem add_mul : (p + q) * r = (p * r) + (q * r) := by
  ext <;> apply Usage.add_mul
theorem min_assoc : (p ⊓ q) ⊓ r = p ⊓ (q ⊓ r) := by
  ext <;> apply Usage.min_assoc
theorem min_comm : p ⊓ q = q ⊓ p := by
  ext <;> apply Usage.min_comm
theorem min_self : p ⊓ p = p := by
  ext <;> apply Usage.min_self
theorem mul_min : p * (q ⊓ r) = (p * q) ⊓ (p * r) := by
  ext <;> apply Usage.mul_min
theorem min_mul : (p ⊓ q) * r = (p * r) ⊓ (q * r) := by
  ext <;> apply Usage.min_mul
theorem add_min : p + (q ⊓ r) = (p + q) ⊓ (p + r) := by
  ext <;> apply Usage.add_min
theorem min_add : (p ⊓ q) + r = (p + r) ⊓ (q + r) := by
  ext <;> apply Usage.min_add

end Modality

/-!
The order, on each usage: a partial order whose meet is `⊓`, under which the operations are
monotone.
-/

theorem le_iff {p q : Grade} : p ≤ q ↔ p.run ≤ q.run ∧ p.total ≤ q.total :=
  ⟨fun h => ⟨congrArg run h, congrArg total h⟩, fun ⟨hr, ht⟩ => Grade.ext hr ht⟩

section Order

variable {p p' q q' r : Grade}

theorem le_refl (p : Grade) : p ≤ p :=
  le_iff.2 ⟨Usage.le_refl _, Usage.le_refl _⟩
theorem le_trans (h₁ : p ≤ q) (h₂ : q ≤ r) : p ≤ r :=
  le_iff.2 ⟨Usage.le_trans _ _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1,
    Usage.le_trans _ _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2⟩
theorem le_antisymm (h₁ : p ≤ q) (h₂ : q ≤ p) : p = q :=
  Grade.ext (Usage.le_antisymm _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1)
    (Usage.le_antisymm _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2)
theorem min_le_left (p q : Grade) : p ⊓ q ≤ p :=
  le_iff.2 ⟨Usage.min_le_left _ _, Usage.min_le_left _ _⟩
theorem min_le_right (p q : Grade) : p ⊓ q ≤ q :=
  le_iff.2 ⟨Usage.min_le_right _ _, Usage.min_le_right _ _⟩
theorem le_min (h₁ : r ≤ p) (h₂ : r ≤ q) : r ≤ p ⊓ q :=
  le_iff.2 ⟨Usage.le_min _ _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1,
    Usage.le_min _ _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2⟩
theorem add_le_add (h₁ : p ≤ p') (h₂ : q ≤ q') : p + q ≤ p' + q' :=
  le_iff.2 ⟨Usage.add_le_add _ _ _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1,
    Usage.add_le_add _ _ _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2⟩
theorem mul_le_mul (h₁ : p ≤ p') (h₂ : q ≤ q') : p * q ≤ p' * q' :=
  le_iff.2 ⟨Usage.mul_le_mul _ _ _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1,
    Usage.mul_le_mul _ _ _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2⟩
theorem min_le_min (h₁ : p ≤ p') (h₂ : q ≤ q') : p ⊓ q ≤ p' ⊓ q' :=
  le_iff.2 ⟨Usage.min_le_min _ _ _ _ (le_iff.1 h₁).1 (le_iff.1 h₂).1,
    Usage.min_le_min _ _ _ _ (le_iff.1 h₁).2 (le_iff.1 h₂).2⟩

end Order

/-! The zero is well behaved, as the modes require. -/

theorem zero_ne_one : 𝟘 ≠ 𝟙 := fun h => nomatch congrArg run h

theorem eq_zero {p : Grade} : p.total = .zero → p = 𝟘 := fun h => Grade.ext (p.run_zero h) h

theorem add_eq_zero {p q : Grade} : p + q = 𝟘 → p = 𝟘 ∧ q = 𝟘 := fun h =>
  have ⟨hp, hq⟩ := Usage.add_eq_zero (congrArg total h)
  ⟨eq_zero hp, eq_zero hq⟩

theorem mul_eq_zero {p q : Grade} : p * q = 𝟘 → p = 𝟘 ∨ q = 𝟘 := fun h =>
  (Usage.mul_eq_zero (congrArg total h)).imp eq_zero eq_zero

theorem min_eq_zero {p q : Grade} : p ⊓ q = 𝟘 → p = 𝟘 ∧ q = 𝟘 := fun h =>
  have ⟨hp, hq⟩ := Usage.min_eq_zero (congrArg total h)
  ⟨eq_zero hp, eq_zero hq⟩

end Grade

end Sic
