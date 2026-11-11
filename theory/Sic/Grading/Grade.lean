module

public import Sic.Grading.Multiplicity

/-!
# Grades

The grades of annex 04 of RFC 36: a grade counts the uses of a variable along two axes, its uses at
run time and all its uses, as a pair of multiplicities.
ADE have no such modality, and prove the laws of a modality for each of their instances; the grades
are proved here to satisfy them, for the multiplications that the RFC states.
Their meaning, the pairs of numbers of uses, is in `Sic/Grading/Meaning/`.
-/

@[expose] public section

namespace Sic.Grading

open Sic.Math

-- ADE: none.
/--
A grade, a pair of multiplicities whose first counts the uses at run time and whose second counts
all the uses.
The uses at run time are among all the uses, so a pair whose second multiplicity is `0` has `0` as
its first multiplicity too: of the nine pairs, the seven others are the grades.
RFC: `\mathsf{syntax}_p`
-/
structure Grade where
  /-- The multiplicity of the uses at run time. -/
  run : Multiplicity
  /-- The multiplicity of all the uses, erased or not. -/
  total : Multiplicity
  /-- No use at all means no use at run time. -/
  run_zero : total = .zero → run = .zero
  deriving DecidableEq

namespace Grade

/-! The seven grades, named in Sic after their two multiplicities, `none`, `linear` and
`unrestricted` for `0`, `1` and `ω`, except a run-time multiplicity `ω` under a total multiplicity
`1`, named `affine` since it counts at most one use. -/

/-- `none / none`, the grade `00ᵖ`. -/
def noneNone : Grade := ⟨.zero, .zero, by decide⟩

/-- `none / linear`, the grade `01ᵖ`. -/
def noneLinear : Grade := ⟨.zero, .one, by decide⟩

/-- `none / unrestricted`, the grade `0ωᵖ`. -/
def noneUnrestricted : Grade := ⟨.zero, .omega, by decide⟩

/-- `linear / linear`, the grade `11ᵖ`. -/
def linearLinear : Grade := ⟨.one, .one, by decide⟩

/-- `linear / unrestricted`, the grade `1ωᵖ`. -/
def linearUnrestricted : Grade := ⟨.one, .omega, by decide⟩

/-- `affine / linear`, the grade `ω1ᵖ`. -/
def affineLinear : Grade := ⟨.omega, .one, by decide⟩

/-- `unrestricted / unrestricted`, the grade `ωωᵖ`. -/
def unrestrictedUnrestricted : Grade := ⟨.omega, .omega, by decide⟩

/-- The grade `00ᵖ`, which `none / none` names. -/
abbrev zero : Grade := noneNone

/-- The grade `11ᵖ`, which `linear / linear` names. -/
abbrev one : Grade := linearLinear

/-- Every grade is one of the seven. -/
theorem cases (p : Grade) :
    p = noneNone ∨ p = noneLinear ∨ p = noneUnrestricted ∨ p = linearLinear ∨
      p = linearUnrestricted ∨ p = affineLinear ∨ p = unrestrictedUnrestricted := by
  obtain ⟨π₁, π₂, h⟩ := p
  cases π₁ <;> cases π₂ <;> simp_all [noneNone, noneLinear, noneUnrestricted, linearLinear,
    linearUnrestricted, affineLinear, unrestrictedUnrestricted]

/-- Decides a statement on all the grades by checking each of the seven. -/
instance {P : Grade → Prop} [DecidablePred P] : Decidable (∀ p, P p) :=
  decidable_of_iff (P noneNone ∧ P noneLinear ∧ P noneUnrestricted ∧ P linearLinear ∧
      P linearUnrestricted ∧ P affineLinear ∧ P unrestrictedUnrestricted)
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ p => by
      rcases cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption,
      fun h => ⟨h _, h _, h _, h _, h _, h _, h _⟩⟩

/-- Decides a statement on some grade by checking each of the seven. -/
instance {P : Grade → Prop} [DecidablePred P] : Decidable (∃ p, P p) :=
  decidable_of_iff (P noneNone ∨ P noneLinear ∨ P noneUnrestricted ∨ P linearLinear ∨
      P linearUnrestricted ∨ P affineLinear ∨ P unrestrictedUnrestricted)
    ⟨fun h => by rcases h with h | h | h | h | h | h | h <;> exact ⟨_, h⟩,
      fun ⟨p, h⟩ => by rcases cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all⟩

theorem ext {p q : Grade} (hr : p.run = q.run) (ht : p.total = q.total) : p = q := by
  obtain ⟨_, _, _⟩ := p
  obtain ⟨_, _, _⟩ := q
  simp_all

/-! ## Operations

The operations act on each multiplicity, and the seven grades are closed under them. -/

/-- The addition of the grades, `⟨π₁, π₂⟩ + ⟨π₃, π₄⟩ = ⟨π₁ + π₃, π₂ + π₄⟩`.
RFC: `\mathsf{op}_p.{+}` -/
def add (p q : Grade) : Grade where
  run := p.run + q.run
  total := p.total + q.total
  run_zero h := by
    obtain ⟨hp, hq⟩ := Multiplicity.modality.zero.add_eq_zero _ _ h
    rw [p.run_zero hp, q.run_zero hq]
    rfl

/-- The multiplication of the grades, `⟨π₁, π₂⟩ · ⟨π₃, π₄⟩ = ⟨π₁ · π₃, π₂ · π₄⟩`.
RFC: `\mathsf{op}_p.{\cdot}` -/
def mul (p q : Grade) : Grade where
  run := p.run * q.run
  total := p.total * q.total
  run_zero h := by
    rcases Multiplicity.modality.zero.mul_eq_zero _ _ h with hp | hq
    · rw [p.run_zero hp]
      rfl
    · rw [q.run_zero hq, Multiplicity.modality.semiring.mul_zero]

/-- The meet of the grades, `⟨π₁, π₂⟩ ∧ ⟨π₃, π₄⟩ = ⟨π₁ ∧ π₃, π₂ ∧ π₄⟩`.
RFC: `\mathsf{op}_p.{\wedge}` -/
def meet (p q : Grade) : Grade where
  run := p.run ⊓ q.run
  total := p.total ⊓ q.total
  run_zero h := by
    obtain ⟨hp, hq⟩ := Multiplicity.modality.zero.meet_eq_zero _ _ h
    rw [p.run_zero hp, q.run_zero hq]
    rfl

instance : Add Grade := ⟨add⟩

instance : Mul Grade := ⟨mul⟩

instance : Min Grade := ⟨meet⟩

theorem add_def (p q : Grade) : p + q = add p q := rfl

theorem mul_def (p q : Grade) : p * q = mul p q := rfl

theorem meet_def (p q : Grade) : p ⊓ q = meet p q := rfl

/-- The order of the grades, `p ≤ q` when `p = p ∧ q`, as in ADE. -/
instance : LE Grade where
  le := order

instance (p q : Grade) : Decidable (p ≤ q) := inferInstanceAs (Decidable (p = p ⊓ q))

/-- The order of the grades is the order of the multiplicities on each component.
RFC: `\mathsf{componentwise}_p` -/
theorem le_iff (p q : Grade) : p ≤ q ↔ p.run ≤ q.run ∧ p.total ≤ q.total := by
  constructor
  · intro h
    exact ⟨congrArg run h, congrArg total h⟩
  · intro ⟨hr, ht⟩
    exact ext hr ht

/-! The table of the RFC, row by row, in the order of the multiplicities. -/

/-- The table of the names of the grades, whose rows give a grade, named after its two
multiplicities, as `noneLinear` is `none / linear`, with its components.
RFC: `\mathsf{names}_p` -/
theorem names_table :
    [(noneNone.run, noneNone.total),
    (noneLinear.run, noneLinear.total),
    (noneUnrestricted.run, noneUnrestricted.total),
    (linearLinear.run, linearLinear.total),
    (linearUnrestricted.run, linearUnrestricted.total),
    (affineLinear.run, affineLinear.total),
    (unrestrictedUnrestricted.run, unrestrictedUnrestricted.total)] =
    [(.zero, .zero),
    (.zero, .one),
    (.zero, .omega),
    (.one, .one),
    (.one, .omega),
    (.omega, .one),
    (.omega, .omega)] := by
  decide

/-- The grades that allow discarding a variable, `p ≤ 00ᵖ`, are exactly those that allow duplicating
it, `p ≤ p + p`: `00ᵖ`, `0ωᵖ` and `ωωᵖ`.
RFC: `\mathsf{discard}_p` -/
theorem discard_iff_duplicate :
    ∀ p : Grade, (p ≤ zero ↔ p ≤ p + p) ∧
      (p ≤ zero ↔ p = zero ∨ p = noneUnrestricted ∨ p = unrestrictedUnrestricted) := by
  decide

/-! ## Properties

The seven grades form a modality of ADE: a semiring whose addition and multiplication distribute
over its meet, ordered by its meet, with a well-behaved zero. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
/-- The grades form a modality.
RFC: `\mathsf{modality}_p` -/
theorem modality : IsModality Grade zero one where
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

theorem le_antisymm : ∀ p q : Grade, p ≤ q → q ≤ p → p = q := by decide

theorem le_trans : ∀ p q r : Grade, p ≤ q → q ≤ r → p ≤ r := by decide

theorem le_refl : ∀ p : Grade, p ≤ p := by decide

theorem add_le_add : ∀ p q r s : Grade, p ≤ q → r ≤ s → p + r ≤ q + s := by decide

theorem mul_le_mul_left : ∀ r p q : Grade, p ≤ q → r * p ≤ r * q := by decide

/-! ### Projection

The projection on the run-time multiplicity is a homomorphism of modalities. -/

/-- The run-time multiplicity of a grade is its projection.
RFC: `\mathsf{run}_p` -/
theorem run_mk (π₁ π₂ : Multiplicity) (h : π₂ = .zero → π₁ = .zero) : run ⟨π₁, π₂, h⟩ = π₁ := rfl

/-- The projection preserves the operations and the units. -/
theorem run_op : ∀ p q : Grade, (p + q).run = p.run + q.run ∧ (p * q).run = p.run * q.run ∧
    (p ⊓ q).run = p.run ⊓ q.run ∧ zero.run = .zero ∧ one.run = .one :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The projection preserves the order. -/
theorem run_le {p q : Grade} (h : p ≤ q) : p.run ≤ q.run :=
  ((le_iff p q).1 h).1

end Grade

end Sic.Grading
