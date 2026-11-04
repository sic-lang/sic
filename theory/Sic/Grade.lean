module

public import Sic.Multiplicity

/-!
# Grades

The grades of RFC 33: a grade counts the uses of a variable along two axes, its uses at run time and
all its uses, as a pair of multiplicities.
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

/-- `none / none`, the grade `𝟘`. -/
def noneNone : Grade := ⟨.zero, .zero, by decide⟩

/-- `none / linear`, the grade `⟨0, 1⟩`. -/
def noneLinear : Grade := ⟨.zero, .one, by decide⟩

/-- `none / unrestricted`, the grade `⟨0, ω⟩`. -/
def noneUnrestricted : Grade := ⟨.zero, .omega, by decide⟩

/-- `linear / linear`, the grade `𝟙`. -/
def linearLinear : Grade := ⟨.one, .one, by decide⟩

/-- `linear / unrestricted`, the grade `⟨1, ω⟩`. -/
def linearUnrestricted : Grade := ⟨.one, .omega, by decide⟩

/-- `affine / linear`, the grade `⟨ω, 1⟩`. -/
def affineLinear : Grade := ⟨.omega, .one, by decide⟩

/-- `unrestricted / unrestricted`, the grade `⟨ω, ω⟩`. -/
def unrestrictedUnrestricted : Grade := ⟨.omega, .omega, by decide⟩

/-- The grade `𝟘`, which `none / none` names. -/
abbrev zero : Grade := noneNone

/-- The grade `𝟙`, which `linear / linear` names. -/
abbrev one : Grade := linearLinear

/-- Every grade is one of the seven. -/
theorem cases (p : Grade) :
    p = noneNone ∨ p = noneLinear ∨ p = noneUnrestricted ∨ p = linearLinear ∨
      p = linearUnrestricted ∨ p = affineLinear ∨ p = unrestrictedUnrestricted := by
  obtain ⟨u, v, h⟩ := p
  cases u <;> cases v <;> simp_all [noneNone, noneLinear, noneUnrestricted, linearLinear,
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

/-- The addition of the grades, `⟨u₁, v₁⟩ + ⟨u₂, v₂⟩ = ⟨u₁ + u₂, v₁ + v₂⟩`. -/
def add (p q : Grade) : Grade where
  run := p.run + q.run
  total := p.total + q.total
  run_zero h := by
    rw [Multiplicity.add_eq_zero] at h ⊢
    exact ⟨p.run_zero h.1, q.run_zero h.2⟩

/-- The multiplication of the grades, `⟨u₁, v₁⟩ · ⟨u₂, v₂⟩ = ⟨u₁ · u₂, v₁ · v₂⟩`. -/
def mul (p q : Grade) : Grade where
  run := p.run * q.run
  total := p.total * q.total
  run_zero h := by
    rw [Multiplicity.mul_eq_zero] at h ⊢
    exact h.imp p.run_zero q.run_zero

/-- The meet of the grades, `⟨u₁, v₁⟩ ∧ ⟨u₂, v₂⟩ = ⟨u₁ ∧ u₂, v₁ ∧ v₂⟩`. -/
def meet (p q : Grade) : Grade where
  run := p.run ⊓ q.run
  total := p.total ⊓ q.total
  run_zero h := by
    rw [Multiplicity.meet_eq_zero] at h ⊢
    exact ⟨p.run_zero h.1, q.run_zero h.2⟩

instance : Add Grade := ⟨add⟩

instance : Mul Grade := ⟨mul⟩

instance : Min Grade := ⟨meet⟩

theorem add_def (p q : Grade) : p + q = add p q := rfl

theorem mul_def (p q : Grade) : p * q = mul p q := rfl

theorem meet_def (p q : Grade) : p ⊓ q = meet p q := rfl

/-- The order of the grades, `p ≤ q` when `p = p ∧ q`, as in ADE. -/
instance : LE Grade where
  le p q := p = p ⊓ q

instance (p q : Grade) : Decidable (p ≤ q) := inferInstanceAs (Decidable (p = p ⊓ q))

/-- The order of the grades is the order of the multiplicities on each component. -/
theorem le_iff (p q : Grade) : p ≤ q ↔ p.run ≤ q.run ∧ p.total ≤ q.total := by
  constructor
  · intro h
    exact ⟨congrArg run h, congrArg total h⟩
  · intro ⟨hr, ht⟩
    exact ext hr ht

/-! The tables of RFC 33 follow from those of the multiplicities, and the names of the grades
match their components. -/

theorem names :
    [noneNone, noneLinear, noneUnrestricted, linearLinear, linearUnrestricted, affineLinear,
      unrestrictedUnrestricted].map (fun p => (p.run, p.total)) =
    [(.zero, .zero), (.zero, .one), (.zero, .omega), (.one, .one), (.one, .omega), (.omega, .one),
      (.omega, .omega)] := rfl

/-- Passing a permission of grade `none / linear` to a parameter of the same grade uses it once, and
never at run time: `⟨0, 1⟩ · 𝟙 = ⟨0, 1⟩`. -/
example : noneLinear * one = noneLinear := by decide

/-- A variable used once in total, erased in one branch and at run time in another, is used once in
total and at most once at run time: `⟨0, 1⟩ ∧ 𝟙 = ⟨ω, 1⟩`. -/
example : noneLinear ⊓ one = affineLinear := by decide

/-- Without `⟨ω, 1⟩`, the meet of `⟨0, 1⟩` and `𝟙` would be `⟨ω, ω⟩`, and the multiplication would
not distribute over the meet: `⟨0, 1⟩ · ⟨ω, ω⟩` is `⟨0, ω⟩`, while `⟨0, 1⟩ · ⟨0, 1⟩ ∧ ⟨0, 1⟩ · 𝟙` is
`⟨0, 1⟩`. -/
example :
    (noneLinear.run * Multiplicity.omega, noneLinear.total * Multiplicity.omega) =
      (.zero, .omega) ∧
    (noneLinear * noneLinear ⊓ noneLinear * one) = noneLinear := by
  decide

/-- On the seven grades, the grades that allow discarding, `p ≤ 𝟘`, are exactly those that allow
duplicating, `p ≤ p + p`: `𝟘`, `⟨0, ω⟩` and `⟨ω, ω⟩`. -/
theorem discard_iff_duplicate :
    ∀ p : Grade, (p ≤ zero ↔ p ≤ p + p) ∧
      (p ≤ zero ↔ p = zero ∨ p = noneUnrestricted ∨ p = unrestrictedUnrestricted) := by
  decide

/-! ## Properties

The seven grades form a modality of ADE, a semiring ordered by its meet, whose zero is well
behaved. -/

-- ADE: `Modality`, in `Graded/Modality.agda`.
theorem add_assoc : ∀ p q r : Grade, (p + q) + r = p + (q + r) := by decide

theorem add_comm : ∀ p q : Grade, p + q = q + p := by decide

theorem zero_add : ∀ p : Grade, zero + p = p := by decide

theorem mul_assoc : ∀ p q r : Grade, (p * q) * r = p * (q * r) := by decide

theorem one_mul : ∀ p : Grade, one * p = p := by decide

theorem mul_one : ∀ p : Grade, p * one = p := by decide

theorem zero_mul : ∀ p : Grade, zero * p = zero := by decide

theorem mul_zero : ∀ p : Grade, p * zero = zero := by decide

theorem meet_assoc : ∀ p q r : Grade, (p ⊓ q) ⊓ r = p ⊓ (q ⊓ r) := by decide

theorem meet_comm : ∀ p q : Grade, p ⊓ q = q ⊓ p := by decide

theorem meet_idem : ∀ p : Grade, p ⊓ p = p := by decide

theorem add_meet : ∀ p q r : Grade,
    p + (q ⊓ r) = (p + q) ⊓ (p + r) ∧ (q ⊓ r) + p = (q + p) ⊓ (r + p) := by
  decide

/-- `(·₊)`: the multiplication distributes over the addition. -/
theorem mul_add : ∀ p q r : Grade,
    p * (q + r) = (p * q) + (p * r) ∧ (q + r) * p = (q * p) + (r * p) := by
  decide

/-- `(·∧)`: the multiplication distributes over the meet. -/
theorem mul_meet : ∀ p q r : Grade,
    p * (q ⊓ r) = (p * q) ⊓ (p * r) ∧ (q ⊓ r) * p = (q * p) ⊓ (r * p) := by
  decide

/-- `(+≤)`: the addition is monotone. -/
theorem add_le_add_right : ∀ p q r : Grade, p ≤ q → p + r ≤ q + r := by decide

/-- `(∧≤)`: the meet is the greatest lower bound of two grades. -/
theorem le_meet_iff : ∀ p q r : Grade, r ≤ p ∧ r ≤ q ↔ r ≤ p ⊓ q := by decide

/-- `(𝟘ₚ)`: the zero is well behaved. -/
theorem zero_well_behaved :
    zero ≠ one ∧ (∀ p q : Grade, p + q = zero → p = zero ∧ q = zero) ∧
      (∀ p q : Grade, p ⊓ q = zero → p = zero ∧ q = zero) ∧
      ∀ p q : Grade, p * q = zero → p = zero ∨ q = zero := by
  decide

/-! ## Meaning

A grade stands for the pairs of numbers of uses it allows, at run time and in total. -/

/-- The pairs of numbers of uses that the pair of multiplicities `⟨u, v⟩` allows, the uses at run
time being among all the uses, as `(uses_p)` writes it for a grade. -/
def usesPair (u v : Multiplicity) : Set (Nat × Nat) :=
  { x | x.1 ∈ Multiplicity.uses u ∧ x.2 ∈ Multiplicity.uses v ∧ x.1 ≤ x.2 }

/-- The pairs of numbers of uses that a grade allows, `(uses_p)`. -/
def uses (p : Grade) : Set (Nat × Nat) :=
  usesPair p.run p.total

theorem mem_uses {p : Grade} {x : Nat × Nat} :
    x ∈ uses p ↔ x.1 ∈ Multiplicity.uses p.run ∧ x.2 ∈ Multiplicity.uses p.total ∧ x.1 ≤ x.2 :=
  Iff.rfl

instance (x : Nat × Nat) (p : Grade) : Decidable (x ∈ uses p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
`IsBest S p` says that `p` is the best grade for the set `S` of pairs of numbers of uses,
`best(S) = p` in RFC 33: it allows all the pairs of `S`, and allows the fewest among the grades that
do.
-/
def IsBest (S : Set (Nat × Nat)) (p : Grade) : Prop :=
  S ⊆ uses p ∧ ∀ q, S ⊆ uses q → uses p ⊆ uses q

/-- The pairs with numbers up to `2`, which tell the grades apart. -/
def grid : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `(≤_p)`, where a grade is below another when it allows more pairs. -/
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

/-- The best grade is unique, so that `best(S)` is well defined. -/
theorem IsBest.unique {S : Set (Nat × Nat)} {p q : Grade} (hp : IsBest S p) (hq : IsBest S q) :
    p = q :=
  le_antisymm p q ((le_iff_uses p q).2 (hq.2 p hp.1)) ((le_iff_uses q p).2 (hp.2 q hq.1))

/-- The addition is the best abstraction of the addition of pairs of numbers, `(+_p)`. -/
theorem add_isBest (p q : Grade) :
    IsBest { x | ∃ a₁ b₁ a₂ b₂, (a₁, b₁) ∈ uses p ∧ (a₂, b₂) ∈ uses q ∧
      x = (a₁ + a₂, b₁ + b₂) } (p + q) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨a₁, b₁, a₂, b₂, ⟨h₁, h₂, h₃⟩, ⟨h₄, h₅, h₆⟩, rfl⟩
    refine ⟨(Multiplicity.add_isBest p.run q.run).1 _ ⟨a₁, a₂, h₁, h₄, rfl⟩,
      (Multiplicity.add_isBest p.total q.total).1 _ ⟨b₁, b₂, h₂, h₅, rfl⟩, ?_⟩
    exact Nat.add_le_add h₃ h₆
  · intro w H
    have key : ∀ p q w : Grade, (∀ y ∈ grid, ∀ z ∈ grid, y ∈ uses p → z ∈ uses q →
        (y.1 + z.1, y.2 + z.2) ∈ uses w) → w ≤ p + q := by
      decide +kernel
    exact (le_iff_uses w (p + q)).1 (key p q w fun y _ z _ hy hz =>
      H _ ⟨y.1, y.2, z.1, z.2, hy, hz, rfl⟩)

/-- The multiplication is the best abstraction of the multiplication of pairs of numbers, `(·_p)`. -/
theorem mul_isBest (p q : Grade) :
    IsBest { x | ∃ a₁ b₁ a₂ b₂, (a₁, b₁) ∈ uses p ∧ (a₂, b₂) ∈ uses q ∧
      x = (a₁ * a₂, b₁ * b₂) } (p * q) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨a₁, b₁, a₂, b₂, ⟨h₁, h₂, h₃⟩, ⟨h₄, h₅, h₆⟩, rfl⟩
    refine ⟨(Multiplicity.mul_isBest p.run q.run).1 _ ⟨a₁, a₂, h₁, h₄, rfl⟩,
      (Multiplicity.mul_isBest p.total q.total).1 _ ⟨b₁, b₂, h₂, h₅, rfl⟩, ?_⟩
    exact Nat.mul_le_mul h₃ h₆
  · intro w H
    have key : ∀ p q w : Grade, (∀ y ∈ grid, ∀ z ∈ grid, y ∈ uses p → z ∈ uses q →
        (y.1 * z.1, y.2 * z.2) ∈ uses w) → w ≤ p * q := by
      decide +kernel
    exact (le_iff_uses w (p * q)).1 (key p q w fun y _ z _ hy hz =>
      H _ ⟨y.1, y.2, z.1, z.2, hy, hz, rfl⟩)

/-- The meet is the best abstraction of the union, `(∧_p)`. -/
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

/-- The pair `⟨1, 0⟩` allows no pair of numbers of uses, since a use at run time is a use. -/
theorem usesPair_one_zero : ∀ x, x ∉ usesPair .one .zero := by
  rintro ⟨a, b⟩ ⟨h₁, h₂, h₃⟩
  simp at h₁ h₂
  omega

/-- The pair `⟨ω, 0⟩` allows only `(0, 0)`, as `𝟘` does. -/
theorem usesPair_omega_zero : usesPair .omega .zero ⊆ uses zero ∧ uses zero ⊆ usesPair .omega .zero := by
  refine ⟨?_, ?_⟩ <;> rintro ⟨a, b⟩ ⟨h₁, h₂, h₃⟩ <;> simp_all [zero, noneNone, uses, usesPair] <;> omega

/-- The seven grades allow non-empty sets of pairs, all different. -/
theorem uses_nonempty_injective :
    (∀ p : Grade, ∃ x, x ∈ uses p) ∧ ∀ p q : Grade, uses p ⊆ uses q → uses q ⊆ uses p → p = q := by
  refine ⟨?_, fun p q h₁ h₂ => le_antisymm p q ((le_iff_uses p q).2 h₂) ((le_iff_uses q p).2 h₁)⟩
  have key : ∀ p : Grade, ∃ x ∈ grid, x ∈ uses p := by decide
  intro p
  obtain ⟨x, _, hx⟩ := key p
  exact ⟨x, hx⟩

/-- The projection on the run-time multiplicity is sound for the first components of the pairs, but
not exact: `⟨ω, 1⟩` allows `0` and `1` uses at run time, which only `ω` allows among the
multiplicities, `(sound_run)`. -/
theorem sound_run (p : Grade) :
    { a | ∃ b, (a, b) ∈ uses p } ⊆ Multiplicity.uses p.run := by
  rintro a ⟨b, h, _, _⟩
  exact h

/-- The projection is not exact: `2` uses at run time are allowed by `ω`, not by `⟨ω, 1⟩`. -/
example : 2 ∈ Multiplicity.uses affineLinear.run ∧ ¬ 2 ∈ { a | ∃ b, (a, b) ∈ uses affineLinear } := by
  refine ⟨trivial, ?_⟩
  rintro ⟨b, _, h, h'⟩
  simp [affineLinear] at h h'
  omega

/-! ### Greatest lower bounds

Every non-empty set of grades has a greatest lower bound, its meet, which the usage of the recursion
of the data and codata types takes over all the shapes of a term. -/

-- ADE: `Greatest-lower-bound`, in `Graded/Modality.agda`.
/-- `(⋀_p)`: `g` is the greatest lower bound of the set `S` of grades, written `⋀ S`. -/
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

/-- Every non-empty set of grades has a greatest lower bound, `(⋀_p)`.
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

/-- `(⋀₊)`: the meet of a family is superadditive, for every family `(pᵢ)` and `(qᵢ)`. -/
theorem glb_add {I : Type} (p q : I → Grade) {g h k : Grade} (hg : IsGLB (range p) g)
    (hh : IsGLB (range q) h) (hk : IsGLB (range fun i => p i + q i) k) : g + h ≤ k :=
  hk.2 (g + h) fun _ ⟨i, hi⟩ => hi ▸ add_le_add _ _ _ _ (hg.1 (p i) ⟨i, rfl⟩) (hh.1 (q i) ⟨i, rfl⟩)

-- ADE: `·-GLBˡ` of `Has-well-behaved-GLBs`, in `Graded/Modality.agda`.
/-- `(⋀·)`: the multiplication by a grade commutes with the meet of a family indexed by a non-empty
set.
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

/-- `(run_p)`: the run-time multiplicity of a grade is its projection. -/
theorem run_mk (u v : Multiplicity) (h : v = .zero → u = .zero) : run ⟨u, v, h⟩ = u := rfl

/-- `(run_op)`: the projection preserves the operations and the units. -/
theorem run_op : ∀ p q : Grade, (p + q).run = p.run + q.run ∧ (p * q).run = p.run * q.run ∧
    (p ⊓ q).run = p.run ⊓ q.run ∧ zero.run = .zero ∧ one.run = .one :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `(run_≤)`: the projection preserves the order. -/
theorem run_le {p q : Grade} (h : p ≤ q) : p.run ≤ q.run :=
  ((le_iff p q).1 h).1

end Grade

end Sic
