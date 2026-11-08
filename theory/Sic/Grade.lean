module

public import Sic.Multiplicity

/-!
# Grades

The grades of annex 03 of RFC 36: a grade counts the uses of a variable along two axes, its uses at
run time and all its uses, as a pair of multiplicities.
ADE have no such modality, and prove the laws of a modality for each of their instances; the grades
are proved here to satisfy them, for the multiplications and the greatest lower bounds that the RFC
states.
-/

@[expose] public section

namespace Sic

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
    obtain ⟨hp, hq⟩ := Multiplicity.zero_well_behaved.add_eq_zero _ _ h
    rw [p.run_zero hp, q.run_zero hq]
    rfl

/-- The multiplication of the grades, `⟨π₁, π₂⟩ · ⟨π₃, π₄⟩ = ⟨π₁ · π₃, π₂ · π₄⟩`.
RFC: `\mathsf{op}_p.{\cdot}` -/
def mul (p q : Grade) : Grade where
  run := p.run * q.run
  total := p.total * q.total
  run_zero h := by
    rcases Multiplicity.zero_well_behaved.mul_eq_zero _ _ h with hp | hq
    · rw [p.run_zero hp]
      rfl
    · rw [q.run_zero hq, (Multiplicity.semiring).mul_zero]

/-- The meet of the grades, `⟨π₁, π₂⟩ ∧ ⟨π₃, π₄⟩ = ⟨π₁ ∧ π₃, π₂ ∧ π₄⟩`.
RFC: `\mathsf{op}_p.{\wedge}` -/
def meet (p q : Grade) : Grade where
  run := p.run ⊓ q.run
  total := p.total ⊓ q.total
  run_zero h := by
    obtain ⟨hp, hq⟩ := Multiplicity.zero_well_behaved.meet_eq_zero _ _ h
    rw [p.run_zero hp, q.run_zero hq]
    rfl

instance : Add Grade := ⟨add⟩

instance : Mul Grade := ⟨mul⟩

instance : Min Grade := ⟨meet⟩

theorem add_def (p q : Grade) : p + q = add p q := rfl

theorem mul_def (p q : Grade) : p * q = mul p q := rfl

theorem meet_def (p q : Grade) : p ⊓ q = meet p q := rfl

/-- The order of the grades, `p ≤ q` when `p = p ∧ q`, as in ADE.
RFC: `\mathsf{order}_p` -/
instance : LE Grade where
  le p q := p = p ⊓ q

instance (p q : Grade) : Decidable (p ≤ q) := inferInstanceAs (Decidable (p = p ⊓ q))

/-- The order of the grades is the order of the multiplicities on each component.
RFC: `\mathsf{componentwise}_p` -/
theorem le_iff (p q : Grade) : p ≤ q ↔ p.run ≤ q.run ∧ p.total ≤ q.total := by
  constructor
  · intro h
    exact ⟨congrArg run h, congrArg total h⟩
  · intro ⟨hr, ht⟩
    exact ext hr ht

/-! The tables of the RFC follow from those of the multiplicities, and the names of the grades
match their components. -/

theorem names :
    [noneNone, noneLinear, noneUnrestricted, linearLinear, linearUnrestricted, affineLinear,
      unrestrictedUnrestricted].map (fun p => (p.run, p.total)) =
    [(.zero, .zero), (.zero, .one), (.zero, .omega), (.one, .one), (.one, .omega), (.omega, .one),
      (.omega, .omega)] := rfl

/-- Passing a permission of grade `none / linear` to a parameter of the same grade uses it once, and
never at run time: `01ᵖ · 11ᵖ = 01ᵖ`. -/
example : noneLinear * one = noneLinear := by decide

/-- A variable used once in total, erased in one branch and at run time in another, is used once in
total and at most once at run time: `01ᵖ ∧ 11ᵖ = ω1ᵖ`. -/
example : noneLinear ⊓ one = affineLinear := by decide

/-- Without `ω1ᵖ`, the meet of `01ᵖ` and `11ᵖ` would be `ωωᵖ`, and the multiplication would not
distribute over the meet: `01ᵖ · ωωᵖ` is `0ωᵖ`, while `01ᵖ · 01ᵖ ∧ 01ᵖ · 11ᵖ` is `01ᵖ`. -/
example :
    (noneLinear.run * Multiplicity.omega, noneLinear.total * Multiplicity.omega) =
      (.zero, .omega) ∧
    (noneLinear * noneLinear ⊓ noneLinear * one) = noneLinear := by
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
/-- The addition and the multiplication form a semiring.
RFC: `\mathsf{semiring}_p.\mathsf{assoc}_{+}`, `\mathsf{semiring}_p.\mathsf{comm}_{+}`
RFC: `\mathsf{semiring}_p.\mathsf{unit}_{+}`, `\mathsf{semiring}_p.\mathsf{assoc}_{\cdot}`
RFC: `\mathsf{semiring}_p.\mathsf{lunit}_{\cdot}`, `\mathsf{semiring}_p.\mathsf{runit}_{\cdot}`
RFC: `\mathsf{semiring}_p.\mathsf{lzero}_{\cdot}`, `\mathsf{semiring}_p.\mathsf{rzero}_{\cdot}` -/
theorem semiring : IsSemiring Grade zero one where
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide

/-- The meet is associative, commutative and idempotent.
RFC: `\mathsf{meet}_p.\mathsf{assoc}`, `\mathsf{meet}_p.\mathsf{comm}`
RFC: `\mathsf{meet}_p.\mathsf{idem}` -/
theorem meet_semilattice : IsMeetSemilattice Grade where
  meet_assoc := by decide
  meet_comm := by decide
  meet_idem := by decide

/-- The multiplication distributes over the addition.
RFC: `{\cdot}{+}_p.\mathsf{left}`, `{\cdot}{+}_p.\mathsf{right}` -/
theorem mul_add : DistributesOver (α := Grade) (· * ·) (· + ·) where
  left := by decide
  right := by decide

/-- The multiplication distributes over the meet.
RFC: `{\cdot}{\wedge}_p.\mathsf{left}`, `{\cdot}{\wedge}_p.\mathsf{right}` -/
theorem mul_meet : DistributesOver (α := Grade) (· * ·) (· ⊓ ·) where
  left := by decide
  right := by decide

/-- The addition distributes over the meet.
RFC: `{+}{\wedge}_p.\mathsf{left}`, `{+}{\wedge}_p.\mathsf{right}` -/
theorem add_meet : DistributesOver (α := Grade) (· + ·) (· ⊓ ·) where
  left := by decide
  right := by decide

/-- The addition is monotone.
RFC: `{+}{\le}_p` -/
theorem add_le_add_right : ∀ p q r : Grade, p ≤ q → p + r ≤ q + r := by decide

/-- The meet is the greatest lower bound of two grades.
RFC: `{\wedge}{\le}_p` -/
theorem le_meet_iff : ∀ p q r : Grade, r ≤ p ∧ r ≤ q ↔ r ≤ p ⊓ q := by decide

/-- The zero is well behaved.
RFC: `0_p.1`, `0_p.{+}`, `0_p.{\wedge}`, `0_p.{\cdot}` -/
theorem zero_well_behaved : HasWellBehavedZero Grade zero one where
  zero_ne_one := by decide
  add_eq_zero := by decide
  meet_eq_zero := by decide
  mul_eq_zero := by decide

/-! ## Meaning

A grade stands for the pairs of numbers of uses it allows, at run time and in total. -/

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

theorem le_antisymm : ∀ p q : Grade, p ≤ q → q ≤ p → p = q := by decide

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

/-! ### Greatest lower bounds

Every non-empty set of grades has a greatest lower bound, its meet, which the usage of the recursion
of the data and codata types takes over all the shapes of a term. -/

-- ADE: `Greatest-lower-bound`, in `Graded/Modality.agda`.
/-- `g` is the greatest lower bound of the set `S` of grades, written `⋀ S`.
RFC: `\textstyle\bigwedge_p` -/
def IsGLB (S : Set Grade) (g : Grade) : Prop :=
  (∀ p, p ∈ S → g ≤ p) ∧ ∀ r, (∀ p, p ∈ S → r ≤ p) → r ≤ g

theorem le_trans : ∀ p q r : Grade, p ≤ q → q ≤ r → p ≤ r := by decide

/-- The seven grades, in a list. -/
def all : List Grade :=
  [noneNone, noneLinear, noneUnrestricted, linearLinear, linearUnrestricted, affineLinear,
    unrestrictedUnrestricted]

theorem mem_all (p : Grade) : p ∈ all := by
  rcases cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [all]

theorem le_refl : ∀ p : Grade, p ≤ p := by decide

/-- The meet of `g` and of the grades of a list is their greatest lower bound. -/
theorem isGLB_foldl (L : List Grade) : ∀ g : Grade,
    IsGLB { p | p = g ∨ p ∈ L } (L.foldl (· ⊓ ·) g) := by
  have meet_le : ∀ g x : Grade, g ⊓ x ≤ g ∧ g ⊓ x ≤ x := by decide
  induction L with
  | nil =>
    intro g
    refine ⟨?_, fun r h => h g (Or.inl rfl)⟩
    intro p hp
    rcases hp with hp | hp
    · rw [hp]
      exact le_refl g
    · cases hp
  | cons x xs ih =>
    intro g
    obtain ⟨h₁, h₂⟩ := ih (g ⊓ x)
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases hp with hp | hp
      · rw [hp]
        exact le_trans _ _ _ (h₁ (g ⊓ x) (Or.inl rfl)) (meet_le g x).1
      · rcases List.mem_cons.1 hp with hp | hp
        · rw [hp]
          exact le_trans _ _ _ (h₁ (g ⊓ x) (Or.inl rfl)) (meet_le g x).2
        · exact h₁ p (Or.inr hp)
    · intro r h
      apply h₂
      intro p hp
      rcases hp with hp | hp
      · rw [hp]
        exact (le_meet_iff g x r).1 ⟨h g (Or.inl rfl), h x (Or.inr List.mem_cons_self)⟩
      · exact h p (Or.inr (List.mem_cons_of_mem _ hp))

/-- Every non-empty set of grades has a greatest lower bound.
RFC: `\textstyle\bigwedge_p`
The set is decidable, which the proof needs to compute the bound without the axiom of choice; the
sets of grades that a rule computes are. -/
theorem exists_isGLB (S : Set Grade) [DecidablePred (· ∈ S)] (h : ∃ p, p ∈ S) :
    ∃ g, IsGLB S g := by
  obtain ⟨p₀, h₀⟩ := h
  let L := all.filter (fun p => decide (p ∈ S))
  have mem : ∀ p, p ∈ S ↔ p ∈ L := by
    intro p
    simp only [L, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => ⟨mem_all p, h⟩, fun h => h.2⟩
  have hL : p₀ ∈ L := (mem p₀).1 h₀
  refine ⟨L.foldl (· ⊓ ·) p₀, ?_, ?_⟩
  · intro p hp
    exact (isGLB_foldl L p₀).1 p (Or.inr ((mem p).1 hp))
  · intro r hr
    apply (isGLB_foldl L p₀).2
    intro p hp
    rcases hp with hp | hp
    · rw [hp]; exact hr p₀ h₀
    · exact hr p ((mem p).2 hp)

/-- The set of the grades of a family. -/
def range {I : Type} (p : I → Grade) : Set Grade :=
  { x | ∃ i, p i = x }

theorem add_le_add : ∀ p q r s : Grade, p ≤ q → r ≤ s → p + r ≤ q + s := by decide

theorem mul_le_mul_left : ∀ r p q : Grade, p ≤ q → r * p ≤ r * q := by decide

/-- The greatest lower bound of a family is superadditive, for every family `(pᵢ)` and `(qᵢ)`.
RFC: `\textstyle\bigwedge{+}_p` -/
theorem glb_add {I : Type} (p q : I → Grade) {g h k : Grade} (hg : IsGLB (range p) g)
    (hh : IsGLB (range q) h) (hk : IsGLB (range fun i => p i + q i) k) : g + h ≤ k :=
  hk.2 (g + h) fun _ ⟨i, hi⟩ => hi ▸ add_le_add _ _ _ _ (hg.1 (p i) ⟨i, rfl⟩) (hh.1 (q i) ⟨i, rfl⟩)

-- ADE: `·-GLBˡ` of `Has-well-behaved-GLBs`, in `Graded/Modality.agda`.
/-- The multiplication by a grade commutes with the greatest lower bound of a family indexed by a
non-empty set.
RFC: `\textstyle\bigwedge{\cdot}_p`
The proof is the finiteness of the grades: the grades `p` such that `l ≤ r · p` form a filter, which
has a least element. -/
theorem glb_mul {I : Type} (p : I → Grade) (i₀ : I) (r : Grade) {g : Grade}
    (hg : IsGLB (range p) g) : IsGLB (range fun i => r * p i) (r * g) := by
  refine ⟨fun _ ⟨i, hi⟩ => hi ▸ mul_le_mul_left r _ _ (hg.1 (p i) ⟨i, rfl⟩), ?_⟩
  intro l hl
  have filter : ∀ r l : Grade, (∃ p, l ≤ r * p) → ∃ f, ∀ p, l ≤ r * p ↔ f ≤ p := by decide
  obtain ⟨f, hf⟩ := filter r l ⟨p i₀, hl _ ⟨i₀, rfl⟩⟩
  exact (hf g).2 (hg.2 f fun x ⟨i, hi⟩ => hi ▸ (hf (p i)).1 (hl _ ⟨i, rfl⟩))

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

end Sic
