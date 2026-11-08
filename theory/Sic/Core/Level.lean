module

public import Sic.Order

/-!
# Levels

The levels of annex 05 of RFC 36, which index the sorts, the universes `U_l` and the universes of
propositions `Ω_l`: `0`, a successor `l + 1`, the larger `l₁ ⊔ l₂` of two levels, or a level variable.
Two levels are equal, or ordered, when their values are whatever natural numbers their variables
take, so that the values are the meaning of the levels, exact by construction.
The equality and the order are decided by a normal form: the value of a level is the larger of a
constant and of the values of some variables, each plus a constant.

ADE have levels as terms of the type theory, which their rules of equality compare; the levels of
Sic are not terms, and their equality is defined by their values instead.
-/

@[expose] public section

namespace Sic.Core

/-- `l₁ ⊔ l₂`, the larger of two levels, or of two natural numbers. -/
infixl:68 " ⊔ " => Max.max

-- ADE: the terms `zeroᵘ`, `sucᵘ` and `_supᵘ_` of `Term`, in `Definition/Untyped.agda`.
/--
A level over `k` level variables, the prenex level variables of an entry of the signature.
The variables are numbered, since no construct binds them.
RFC: `\mathsf{syntax}_l`
-/
inductive Level (k : Nat) : Type where
  /-- `0`. -/
  | zero : Level k
  /-- `l + 1`, the successor of `l`. -/
  | succ (l : Level k) : Level k
  /-- `l₁ ⊔ l₂`, the larger of `l₁` and `l₂`. -/
  | max (l₁ l₂ : Level k) : Level k
  /-- The level variable `i`. -/
  | var (i : Fin k) : Level k
  deriving DecidableEq

namespace Level

variable {k : Nat}

instance : Max (Level k) := ⟨max⟩

-- ADE: none.
/-- The value `⟦l⟧_ρ` of the level `l` under the assignment `ρ`, which gives a natural number to
each level variable.
RFC: `\mathsf{value}_l` -/
def value (ρ : Fin k → Nat) : Level k → Nat
  | zero => 0
  | succ l => value ρ l + 1
  | max l₁ l₂ => Max.max (value ρ l₁) (value ρ l₂)
  | var i => ρ i

-- ADE: none.
/-- Two levels are equal when their values are equal under every assignment.
RFC: `=_l` -/
def Equal (l₁ l₂ : Level k) : Prop := ∀ ρ : Fin k → Nat, value ρ l₁ = value ρ l₂

/-- `l₁ ≈ l₂`, the equality of levels, written `l₁ = l₂` in the RFC, which is not the equality
`=` of their syntax in Lean. -/
instance : HasEquiv (Level k) := ⟨Equal⟩

-- ADE: none.
/-- A level is below another when its value is below under every assignment.
RFC: `\le_l` -/
def Le (l₁ l₂ : Level k) : Prop := ∀ ρ : Fin k → Nat, value ρ l₁ ≤ value ρ l₂

instance : LE (Level k) := ⟨Le⟩

theorem equal_def (l₁ l₂ : Level k) : l₁ ≈ l₂ ↔ ∀ ρ, value ρ l₁ = value ρ l₂ := Iff.rfl

theorem le_def (l₁ l₂ : Level k) : l₁ ≤ l₂ ↔ ∀ ρ, value ρ l₁ ≤ value ρ l₂ := Iff.rfl

/-! ## Properties

The equality is an equivalence and the order a preorder, whose equivalence is the equality. -/

-- ADE: none.
/-- The equality is an equivalence.
RFC: `\mathsf{equiv}_l.\mathsf{refl}`, `\mathsf{equiv}_l.\mathsf{symm}`, `\mathsf{equiv}_l.\mathsf{trans}` -/
theorem equivalence : Equivalence (α := Level k) (· ≈ ·) where
  refl _ _ := rfl
  symm h ρ := (h ρ).symm
  trans h₁ h₂ ρ := (h₁ ρ).trans (h₂ ρ)

-- ADE: none.
/-- The order is a preorder.
RFC: `\mathsf{preorder}_l.\mathsf{refl}`, `\mathsf{preorder}_l.\mathsf{trans}` -/
theorem preorder : IsPreorder (α := Level k) (· ≤ ·) where
  refl _ _ := Nat.le_refl _
  trans h₁ h₂ ρ := Nat.le_trans (h₁ ρ) (h₂ ρ)

-- ADE: none.
/-- The equivalence of the order is the equality.
RFC: `\mathsf{antisymmetry}_l` -/
theorem equal_iff_le_le (l₁ l₂ : Level k) : l₁ ≈ l₂ ↔ l₁ ≤ l₂ ∧ l₂ ≤ l₁ :=
  ⟨fun h => ⟨fun ρ => Nat.le_of_eq (h ρ), fun ρ => Nat.le_of_eq (h ρ).symm⟩,
    fun ⟨h₁, h₂⟩ ρ => Nat.le_antisymm (h₁ ρ) (h₂ ρ)⟩

-- ADE: none.
/-- The order is the one of the larger of two levels.
RFC: `{\le}{\sqcup}_l` -/
theorem le_iff_max_equal (l₁ l₂ : Level k) : l₁ ≤ l₂ ↔ l₁ ⊔ l₂ ≈ l₂ := by
  constructor
  · intro h ρ
    have := h ρ
    show Max.max (value ρ l₁) (value ρ l₂) = value ρ l₂
    omega
  · intro h ρ
    have := h ρ
    change Max.max (value ρ l₁) (value ρ l₂) = value ρ l₂ at this
    omega

/-! ## Normal Form

A level has the value of a normal form: the larger of a constant and, for each variable that the
level uses, of the variable plus a constant.
Two normal forms are compared by their constants, which decides the equality and the order of
levels. -/

/-- The largest of the `n` values of `f`, and `0` when `n` is `0`. -/
def supFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => Max.max (f 0) (supFin n fun i => f i.succ)

theorem supFin_le_iff : ∀ {n : Nat} (f : Fin n → Nat) (m : Nat),
    supFin n f ≤ m ↔ ∀ i, f i ≤ m
  | 0, f, m => ⟨fun _ i => i.elim0, fun _ => Nat.zero_le m⟩
  | n + 1, f, m => by
    show Max.max (f 0) (supFin n fun i => f i.succ) ≤ m ↔ _
    rw [Nat.max_le, supFin_le_iff]
    constructor
    · intro ⟨h₀, h⟩ i
      cases i using Fin.cases with
      | zero => exact h₀
      | succ i => exact h i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem le_supFin {n : Nat} (f : Fin n → Nat) (i : Fin n) : f i ≤ supFin n f :=
  (supFin_le_iff f _).mp (Nat.le_refl _) i

/-- A normal form over `k` variables. -/
structure Normal (k : Nat) where
  /-- The constant below the value. -/
  const : Nat
  /-- The constant added to each variable that the level uses, and `none` for the others. -/
  offset : Fin k → Option Nat

/-- The value of the variable `x` plus the offset `o`, and `0` without offset. -/
def shift (x : Nat) : Option Nat → Nat
  | some a => x + a
  | none => 0

/-- The value of a normal form under the assignment `ρ`. -/
def Normal.value (ρ : Fin k → Nat) (n : Normal k) : Nat :=
  Max.max n.const (supFin k fun i => shift (ρ i) (n.offset i))

/-- The larger of two offsets. -/
def maxOffset : Option Nat → Option Nat → Option Nat
  | some a, some b => some (Max.max a b)
  | some a, none => some a
  | none, o => o

/-- The normal form of a level. -/
def normalize : Level k → Normal k
  | zero => ⟨0, fun _ => none⟩
  | succ l => ⟨(normalize l).const + 1, fun i => ((normalize l).offset i).map (· + 1)⟩
  | max l₁ l₂ =>
    ⟨Max.max (normalize l₁).const (normalize l₂).const,
      fun i => maxOffset ((normalize l₁).offset i) ((normalize l₂).offset i)⟩
  | var i => ⟨0, fun j => if j = i then some 0 else none⟩

theorem shift_maxOffset (x : Nat) :
    ∀ o₁ o₂, shift x (maxOffset o₁ o₂) = Max.max (shift x o₁) (shift x o₂)
  | some a, some b => by simp only [maxOffset, shift]; omega
  | some a, none => by simp only [maxOffset, shift]; omega
  | none, some b => by simp only [maxOffset, shift]; omega
  | none, none => rfl

/-- A level has the value of its normal form. -/
theorem value_normalize (ρ : Fin k → Nat) : ∀ l : Level k, (normalize l).value ρ = value ρ l
  | zero => by
    show Max.max 0 (supFin k fun i => shift (ρ i) none) = 0
    have := (supFin_le_iff (fun i : Fin k => shift (ρ i) none) 0).mpr fun _ => Nat.le_refl 0
    omega
  | succ l => by
    have ih := value_normalize ρ l
    simp only [Normal.value, normalize, value] at ih ⊢
    rw [← ih]
    -- Both sides bound each other, through the bounds of `supFin`.
    apply Nat.le_antisymm
    · have : (supFin k fun i => shift (ρ i) (((normalize l).offset i).map (· + 1))) ≤
          Max.max (normalize l).const (supFin k fun i => shift (ρ i) ((normalize l).offset i)) + 1 :=
        (supFin_le_iff _ _).mpr fun i => by
          have := le_supFin (fun i => shift (ρ i) ((normalize l).offset i)) i
          cases h : (normalize l).offset i <;> simp only [h, Option.map, shift] at this ⊢ <;> omega
      omega
    · have : (supFin k fun i => shift (ρ i) ((normalize l).offset i)) + 1 ≤
          Max.max ((normalize l).const + 1)
            (supFin k fun i => shift (ρ i) (((normalize l).offset i).map (· + 1))) := by
        have hs := (supFin_le_iff (fun i => shift (ρ i) ((normalize l).offset i))
          (Max.max ((normalize l).const + 1)
            (supFin k fun i => shift (ρ i) (((normalize l).offset i).map (· + 1))) - 1)).mpr
          fun i => by
            have := le_supFin (fun i => shift (ρ i) (((normalize l).offset i).map (· + 1))) i
            cases h : (normalize l).offset i <;> simp only [h, Option.map, shift] at this ⊢ <;>
              omega
        omega
      omega
  | max l₁ l₂ => by
    have ih₁ := value_normalize ρ l₁
    have ih₂ := value_normalize ρ l₂
    simp only [Normal.value, normalize, value, shift_maxOffset] at ih₁ ih₂ ⊢
    rw [← ih₁, ← ih₂]
    -- The largest of the larger of two values is the larger of their largest.
    have h₁ := le_supFin (fun i => Max.max (shift (ρ i) ((normalize l₁).offset i))
      (shift (ρ i) ((normalize l₂).offset i)))
    have h₂ := le_supFin (fun i => shift (ρ i) ((normalize l₁).offset i))
    have h₃ := le_supFin (fun i => shift (ρ i) ((normalize l₂).offset i))
    have hs₁ := (supFin_le_iff (fun i => Max.max (shift (ρ i) ((normalize l₁).offset i))
      (shift (ρ i) ((normalize l₂).offset i)))
      (Max.max (supFin k fun i => shift (ρ i) ((normalize l₁).offset i))
        (supFin k fun i => shift (ρ i) ((normalize l₂).offset i)))).mpr
      fun i => by have := h₂ i; have := h₃ i; omega
    have hs₂ := (supFin_le_iff (fun i => shift (ρ i) ((normalize l₁).offset i))
      (supFin k fun i => Max.max (shift (ρ i) ((normalize l₁).offset i))
        (shift (ρ i) ((normalize l₂).offset i)))).mpr
      fun i => by have := h₁ i; omega
    have hs₃ := (supFin_le_iff (fun i => shift (ρ i) ((normalize l₂).offset i))
      (supFin k fun i => Max.max (shift (ρ i) ((normalize l₁).offset i))
        (shift (ρ i) ((normalize l₂).offset i)))).mpr
      fun i => by have := h₁ i; omega
    omega
  | var i => by
    show Max.max 0 (supFin k fun j => shift (ρ j) (if j = i then some 0 else none)) = ρ i
    have h₁ : shift (ρ i) (if i = i then some 0 else none) ≤
        supFin k fun j => shift (ρ j) (if j = i then some 0 else none) :=
      le_supFin (fun j => shift (ρ j) (if j = i then some 0 else none)) i
    have h₂ := (supFin_le_iff (fun j => shift (ρ j) (if j = i then some 0 else none)) (ρ i)).mpr
      fun j => by
        by_cases h : j = i
        · subst h; simp [shift]
        · simp [h, shift]
    have h₃ : shift (ρ i) (if i = i then some 0 else none) = ρ i := by simp [shift]
    rw [h₃] at h₁
    omega

/-- One offset is below another when each variable that the first uses, the second uses with an
offset at least as large. -/
def OffsetLe : Option Nat → Option Nat → Prop
  | some a, some b => a ≤ b
  | some _, none => False
  | none, _ => True

instance : ∀ o₁ o₂, Decidable (OffsetLe o₁ o₂)
  | some a, some b => inferInstanceAs (Decidable (a ≤ b))
  | some _, none => isFalse id
  | none, _ => isTrue trivial

/-- The comparison of two normal forms: the constant of the first is below the value of the second
when the variables are `0`, and the offsets of the first are below those of the second. -/
def Normal.Le (n₁ n₂ : Normal k) : Prop :=
  n₁.const ≤ n₂.value (fun _ => 0) ∧ ∀ i, OffsetLe (n₁.offset i) (n₂.offset i)

instance (n₁ n₂ : Normal k) : Decidable (n₁.Le n₂) := inferInstanceAs (Decidable (_ ∧ _))

theorem shift_mono {x y : Nat} (h : x ≤ y) : ∀ o, shift x o ≤ shift y o
  | some _ => Nat.add_le_add_right h _
  | none => Nat.le_refl _

theorem Normal.value_mono (n : Normal k) {ρ₁ ρ₂ : Fin k → Nat} (h : ∀ i, ρ₁ i ≤ ρ₂ i) :
    n.value ρ₁ ≤ n.value ρ₂ := by
  have := (supFin_le_iff (fun i => shift (ρ₁ i) (n.offset i)) (n.value ρ₂)).mpr fun i =>
    Nat.le_trans (shift_mono (h i) _)
      (Nat.le_trans (le_supFin (fun i => shift (ρ₂ i) (n.offset i)) i) (Nat.le_max_right _ _))
  exact (Nat.max_le).mpr ⟨Nat.le_max_left _ _, this⟩

/-- The comparison of two normal forms decides the order of their values. -/
theorem Normal.le_iff (n₁ n₂ : Normal k) : n₁.Le n₂ ↔ ∀ ρ, n₁.value ρ ≤ n₂.value ρ := by
  constructor
  · intro ⟨hc, ho⟩ ρ
    refine (Nat.max_le).mpr ⟨Nat.le_trans hc (n₂.value_mono fun _ => Nat.zero_le _), ?_⟩
    refine (supFin_le_iff _ _).mpr fun i => ?_
    have hi := ho i
    revert hi
    cases n₁.offset i with
    | none => intro; exact Nat.zero_le _
    | some a =>
      cases h₂ : n₂.offset i with
      | none => intro hi; exact hi.elim
      | some b =>
        intro hi
        have := le_supFin (fun i => shift (ρ i) (n₂.offset i)) i
        simp only [h₂, shift, OffsetLe] at this hi ⊢
        exact Nat.le_trans (Nat.add_le_add_left hi _)
          (Nat.le_trans this (Nat.le_max_right _ _))
  · intro h
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) (h _), fun i => ?_⟩
    -- The variable `i` alone is made larger than the value of the second form when all the
    -- variables are `0`, so that the offset of the first one at `i` shows.
    obtain ⟨N, hN⟩ : ∃ N, N = n₂.value (fun _ => 0) + 1 := ⟨_, rfl⟩
    obtain ⟨ρ, hρi, hρj⟩ : ∃ ρ : Fin k → Nat, ρ i = N ∧ ∀ j, j ≠ i → ρ j = 0 :=
      ⟨fun j => if j = i then N else 0, by simp, fun j hj => by simp [hj]⟩
    have hρ := h ρ
    have bound : n₂.value ρ ≤ Max.max (n₂.value fun _ => 0) (shift N (n₂.offset i)) := by
      refine (Nat.max_le).mpr ⟨Nat.le_trans (Nat.le_max_left _ (supFin k _))
        (Nat.le_max_left _ _), (supFin_le_iff _ _).mpr fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; rw [hρi]; exact Nat.le_max_right _ _
      · rw [hρj j hj]
        exact Nat.le_trans (Nat.le_trans (le_supFin (fun j => shift 0 (n₂.offset j)) j)
          (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
    have below : shift (ρ i) (n₁.offset i) ≤ n₁.value ρ :=
      Nat.le_trans (le_supFin (fun j => shift (ρ j) (n₁.offset j)) i) (Nat.le_max_right _ _)
    rw [hρi] at below
    revert below bound
    cases n₁.offset i with
    | none => intros; trivial
    | some a =>
      cases n₂.offset i with
      | none =>
        intro below bound
        simp only [shift] at below bound
        omega
      | some b =>
        intro below bound
        simp only [shift] at below bound
        show a ≤ b
        omega

-- ADE: none.
/-- The order of two levels is decidable, by their normal forms.
RFC: `\mathsf{decidable}_l.{\le}` -/
instance (l₁ l₂ : Level k) : Decidable (l₁ ≤ l₂) :=
  decidable_of_iff ((normalize l₁).Le (normalize l₂)) (by
    rw [Normal.le_iff, le_def]
    simp only [value_normalize])

-- ADE: none.
/-- The equality of two levels is decidable, as the order is.
RFC: `\mathsf{decidable}_l.{=}` -/
instance (l₁ l₂ : Level k) : Decidable (l₁ ≈ l₂) :=
  decidable_of_iff (l₁ ≤ l₂ ∧ l₂ ≤ l₁) (equal_iff_le_le l₁ l₂).symm

end Level

end Sic.Core
