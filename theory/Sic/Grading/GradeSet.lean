module

public import Sic.Grading.Mode
public import Sic.Math.Set

/-!
# Sets of Grades

The sets of grades of annex 11 of RFC 36: the greatest lower bound of a set of grades, which the
usage of the recursion of the data and codata types takes over all the shapes of a term, and the
sets of the grades that a term checked in a mode does not count, which the erasure replaces.
-/

@[expose] public section

namespace Sic.Grading

open Sic.Math

/-! ## Greatest Lower Bounds

Every non-empty decidable set of grades has a greatest lower bound, its meet, which the usage of the
recursion of the data and codata types takes over all the shapes of a term. -/

namespace Grade

-- ADE: `Greatest-lower-bound`, in `Graded/Modality.agda`.
/-- `g` is the greatest lower bound of the set `S` of grades, written `⋀ S`.
RFC: `\textstyle\bigwedge_p` -/
def IsGLB (S : Set Grade) (g : Grade) : Prop :=
  (∀ p, p ∈ S → g ≤ p) ∧ ∀ r, (∀ p, p ∈ S → r ≤ p) → r ≤ g

/-- The seven grades, in a list. -/
def all : List Grade :=
  [noneNone, noneLinear, noneUnrestricted, linearLinear, linearUnrestricted, affineLinear,
    unrestrictedUnrestricted]

theorem mem_all (p : Grade) : p ∈ all := by
  rcases cases p with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [all]

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
        exact (modality.le_meet_iff g x r).1 ⟨h g (Or.inl rfl), h x (Or.inr List.mem_cons_self)⟩
      · exact h p (Or.inr (List.mem_cons_of_mem _ hp))

/-- Every non-empty decidable set of grades has a greatest lower bound.
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

end Grade

/-! ## Uncounted Grades -/

namespace Mode

-- ADE: none.
/-- `S^m`: the grades of the positions that a term checked in the mode `m` checks in a more erased
mode, `m ⊙ p ≠ m`, and which it does not count.
RFC: `\mathsf{uncounted}_m` -/
def erased (m : Mode) : Set Grade := { p | m ⊙ p ≠ m }

instance (m : Mode) : DecidablePred (· ∈ m.erased) :=
  fun p => inferInstanceAs (Decidable (m ⊙ p ≠ m))

-- ADE: none.
/-- The three sets `S^m`: the mode `11ᵐ` of run time does not count the grades without use at run
time, the mode `01ᵐ` the grade `00ᵖ`, and the mode `00ᵐ`, which counts no use, erases nothing.
RFC: `\mathsf{values}_m` -/
theorem erased_values :
    (∀ p, p ∈ oneOne.erased ↔ p.run = .zero) ∧
    (∀ p, p ∈ zeroOne.erased ↔ p = Grade.zero) ∧
    (∀ p, p ∉ zeroZero.erased) := by
  decide

end Mode

-- ADE: none.
/-- A set `S` of grades erases only what a term checked in the mode `m` does not count, and
follows the rules of usage: a variable checked in the mode `m` uses itself with a grade outside
`S`, and a grade above a grade of `S`, or a part of a sum in `S`, is in `S`. -/
structure ErasesUncounted (m : Mode) (S : Set Grade) : Prop where
  /-- The grade `⌜m⌝` is not erased.
  RFC: `\mathsf{uncounted}_S.\mathsf{grade}` -/
  grade : m.grade ∉ S
  /-- A grade above a grade of `S` is in `S`.
  RFC: `\mathsf{uncounted}_S.{\le}` -/
  le : ∀ p q : Grade, p ≤ q → p ∈ S → q ∈ S
  /-- The first part of a sum in `S` is in `S`.
  RFC: `\mathsf{uncounted}_S.{+}` -/
  add : ∀ p q : Grade, p + q ∈ S → p ∈ S
  /-- A product in `S` whose first factor is not in `S` has its second factor in `S`.
  RFC: `\mathsf{uncounted}_S.{\cdot}` -/
  mul : ∀ p q : Grade, p ∉ S → p * q ∈ S → q ∈ S
  /-- A product of which a factor is in `S` is in `S`.
  RFC: `\mathsf{uncounted}_S.\mathsf{factor}` -/
  factor : ∀ p q : Grade, p ∈ S ∨ q ∈ S → p * q ∈ S
  /-- A grade not in `S` keeps the mode `m`, in which the term of a field of this grade is checked.
  RFC: `\mathsf{uncounted}_S.{\odot}` -/
  mode : ∀ p : Grade, p ∉ S → m ⊙ p = m

-- ADE: none.
/-- The set `S^m` erases only what a term checked in the mode `m` does not count.
RFC: `\mathsf{erases}_m` -/
theorem Mode.erasesUncounted (m : Mode) : ErasesUncounted m m.erased where
  grade := by revert m; decide
  le := by revert m; decide
  add := by revert m; decide
  mul := by revert m; decide
  factor := by revert m; decide
  mode := fun _ h => Decidable.of_not_not h

/-- A product of grades with a use at run time keeps the mode `11ᵐ`, factor by factor. -/
theorem Mode.oneOne_odot_mul :
    ∀ r p : Grade, r * p ∉ Mode.oneOne.erased → (Mode.oneOne ⊙ r) ⊙ p = .oneOne := by
  decide

end Sic.Grading
