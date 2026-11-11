module

public import Sic.Grading.Grade
public import Sic.Grading.Meaning.Multiplicity

/-!
# Meaning of the Grades

The meaning of the grades of annex 04 of RFC 36: a grade stands for the pairs of numbers of uses
it allows, at run time and in total, and its operations and its order are the best abstractions of
those of the pairs.
-/

@[expose] public section

namespace Sic.Grading

open Sic.Math

namespace Grade

/-- The pairs of numbers of uses that the pair of multiplicities `⟨π₁, π₂⟩` allows, the uses at run
time being among all the uses.
RFC: `\mathsf{uses}_p` -/
def usesPair (π₁ π₂ : Multiplicity) : Set (Nat × Nat) :=
  { x | x.1 ∈ Multiplicity.uses π₁ ∧ x.2 ∈ Multiplicity.uses π₂ ∧ x.1 ≤ x.2 }

/-- The pairs of numbers of uses that a grade allows, those of its pair of multiplicities. -/
def uses (p : Grade) : Set (Nat × Nat) :=
  usesPair p.run p.total

theorem mem_uses {p : Grade} {x : Nat × Nat} :
    x ∈ uses p ↔ x.1 ∈ Multiplicity.uses p.run ∧ x.2 ∈ Multiplicity.uses p.total ∧ x.1 ≤ x.2 :=
  Iff.rfl

instance (x : Nat × Nat) (p : Grade) : Decidable (x ∈ uses p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
`IsBest S p` says that `p` is the best grade for the set `S` of pairs of numbers of uses,
`best(S) = p` in the RFC: it allows all the pairs of `S`, and allows the fewest among the grades
that do.
RFC: `\mathsf{best}_p`
-/
def IsBest (S : Set (Nat × Nat)) (p : Grade) : Prop :=
  S ⊆ uses p ∧ ∀ q, S ⊆ uses q → uses p ⊆ uses q

/-- The pairs with numbers up to `2`, which tell the grades apart. -/
def grid : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- A grade is below another when it allows more pairs.
RFC: `\le_p` -/
theorem le_iff_uses (p q : Grade) : p ≤ q ↔ uses q ⊆ uses p := by
  constructor
  · intro h x hx
    obtain ⟨hr, ht⟩ := (le_iff p q).1 h
    rw [Multiplicity.le_iff_uses] at hr ht
    exact ⟨hr _ hx.1, ht _ hx.2.1, hx.2.2⟩
  · intro h
    have key : ∀ p q : Grade, (∀ x ∈ grid, x ∈ uses q → x ∈ uses p) → p ≤ q := by decide
    exact key p q fun x _ hx => h x hx

/-- The best grade is unique, so that `best(S)` is well defined.
RFC: `\mathsf{unique}_p` -/
theorem IsBest.unique {S : Set (Nat × Nat)} {p q : Grade} (hp : IsBest S p) (hq : IsBest S q) :
    p = q :=
  le_antisymm p q ((le_iff_uses p q).2 (hq.2 p hp.1)) ((le_iff_uses q p).2 (hp.2 q hq.1))

/-- The addition is the best abstraction of the addition of pairs of numbers.
RFC: `+_p` -/
theorem add_isBest (p q : Grade) :
    IsBest { x | ∃ n₁ n₂ n₃ n₄, (n₁, n₂) ∈ uses p ∧ (n₃, n₄) ∈ uses q ∧
      x = (n₁ + n₃, n₂ + n₄) } (p + q) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨n₁, n₂, n₃, n₄, ⟨h₁, h₂, h₃⟩, ⟨h₄, h₅, h₆⟩, rfl⟩
    refine ⟨(Multiplicity.add_isBest p.run q.run).1 _ ⟨n₁, n₃, h₁, h₄, rfl⟩,
      (Multiplicity.add_isBest p.total q.total).1 _ ⟨n₂, n₄, h₂, h₅, rfl⟩, ?_⟩
    exact Nat.add_le_add h₃ h₆
  · intro w H
    have key : ∀ p q w : Grade, (∀ y ∈ grid, ∀ z ∈ grid, y ∈ uses p → z ∈ uses q →
        (y.1 + z.1, y.2 + z.2) ∈ uses w) → w ≤ p + q := by
      decide +kernel
    exact (le_iff_uses w (p + q)).1 (key p q w fun y _ z _ hy hz =>
      H _ ⟨y.1, y.2, z.1, z.2, hy, hz, rfl⟩)

/-- The multiplication is the best abstraction of the multiplication of pairs of numbers.
RFC: `\cdot_p` -/
theorem mul_isBest (p q : Grade) :
    IsBest { x | ∃ n₁ n₂ n₃ n₄, (n₁, n₂) ∈ uses p ∧ (n₃, n₄) ∈ uses q ∧
      x = (n₁ * n₃, n₂ * n₄) } (p * q) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨n₁, n₂, n₃, n₄, ⟨h₁, h₂, h₃⟩, ⟨h₄, h₅, h₆⟩, rfl⟩
    refine ⟨(Multiplicity.mul_isBest p.run q.run).1 _ ⟨n₁, n₃, h₁, h₄, rfl⟩,
      (Multiplicity.mul_isBest p.total q.total).1 _ ⟨n₂, n₄, h₂, h₅, rfl⟩, ?_⟩
    exact Nat.mul_le_mul h₃ h₆
  · intro w H
    have key : ∀ p q w : Grade, (∀ y ∈ grid, ∀ z ∈ grid, y ∈ uses p → z ∈ uses q →
        (y.1 * z.1, y.2 * z.2) ∈ uses w) → w ≤ p * q := by
      decide +kernel
    exact (le_iff_uses w (p * q)).1 (key p q w fun y _ z _ hy hz =>
      H _ ⟨y.1, y.2, z.1, z.2, hy, hz, rfl⟩)

/-- The meet is the best abstraction of the union.
RFC: `\wedge_p` -/
theorem meet_isBest (p q : Grade) : IsBest (uses p ∪ uses q) (p ⊓ q) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have key : ∀ p q : Grade, p ⊓ q ≤ p ∧ p ⊓ q ≤ q := by decide
    rcases hx with hx | hx
    · exact (le_iff_uses _ _).1 (key p q).1 x hx
    · exact (le_iff_uses _ _).1 (key p q).2 x hx
  · intro w H
    have key : ∀ p q w : Grade, (∀ y ∈ grid, y ∈ uses p ∨ y ∈ uses q → y ∈ uses w) →
        w ≤ p ⊓ q := by
      decide +kernel
    exact (le_iff_uses w (p ⊓ q)).1 (key p q w fun y _ hy => H y hy)

/-- The pair `⟨1, 0⟩` allows no pair of numbers of uses, since a use at run time is a use, and the
pair `⟨ω, 0⟩` allows only `(0, 0)`, as `00ᵖ` does.
RFC: `\mathsf{excluded}_p` -/
theorem excluded :
    (∀ x, x ∉ usesPair .one .zero) ∧
      (usesPair .omega .zero ⊆ uses zero ∧ uses zero ⊆ usesPair .omega .zero) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n₁, n₂⟩ ⟨h₁, h₂, h₃⟩
    simp at h₁ h₂
    omega
  all_goals
    rintro ⟨n₁, n₂⟩ ⟨h₁, h₂, h₃⟩
    simp_all [zero, noneNone, uses, usesPair] <;> omega

/-- The seven grades allow non-empty sets of pairs, all different.
RFC: `\mathsf{distinct}_p` -/
theorem uses_nonempty_injective :
    (∀ p : Grade, ∃ x, x ∈ uses p) ∧ ∀ p q : Grade, uses p ⊆ uses q → uses q ⊆ uses p → p = q := by
  refine ⟨?_, fun p q h₁ h₂ => le_antisymm p q ((le_iff_uses p q).2 h₂) ((le_iff_uses q p).2 h₁)⟩
  have key : ∀ p : Grade, ∃ x ∈ grid, x ∈ uses p := by decide
  intro p
  obtain ⟨x, _, hx⟩ := key p
  exact ⟨x, hx⟩

/-- The projection on the run-time multiplicity is sound for the first components of the pairs.
RFC: `\mathsf{sound}_{\mathsf{run}}` -/
theorem sound_run (p : Grade) :
    { n₁ | ∃ n₂, (n₁, n₂) ∈ uses p } ⊆ Multiplicity.uses p.run := by
  rintro n₁ ⟨n₂, h, _, _⟩
  exact h

/-- The projection is not exact: `ω1ᵖ` allows `0` and `1` uses at run time, which only `ω` allows
among the multiplicities, and `ω` allows `2`.
RFC: `\mathsf{inexact}_{\mathsf{run}}` -/
theorem inexact_run :
    2 ∈ Multiplicity.uses affineLinear.run ∧
      2 ∉ { n₁ | ∃ n₂, (n₁, n₂) ∈ uses affineLinear } := by
  refine ⟨trivial, ?_⟩
  rintro ⟨n₂, _, h, h'⟩
  simp [affineLinear] at h h'
  omega

end Grade

end Sic.Grading
