module

public import Sic.Core.Level

/-!
# Universes

The sorts of annex 07 of RFC 36: the universes `U_l`, whose elements are types, and the universes of
propositions `Ω_l`, whose elements are propositions, both indexed by a level.
A sort is named a universe here, since `Sort` is a keyword of Lean, and the RFC calls both kinds of
sorts universes.
The sort variables of the declarations and of the definitions stand for `U` or `Ω`, and each entry
of the signature is checked for each of them, so that the judgments only meet the two qualities
below, which the joins of sorts compute by `(⊔_s)`.

ADE have the universes `U_l` only, and no universes of propositions.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- The quality of a sort, as the sort qualities of Rocq: a universe or a universe of propositions.
RFC: `\mathsf{syntax}_s` -/
inductive Quality where
  /-- `U`, the quality of the universes. -/
  | type
  /-- `Ω`, the quality of the universes of propositions. -/
  | prop
  deriving DecidableEq

namespace Quality

/-- Decides a statement on all the qualities by checking both. -/
instance {P : Quality → Prop} [DecidablePred P] : Decidable (∀ s, P s) :=
  decidable_of_iff (P type ∧ P prop)
    ⟨fun ⟨h₁, h₂⟩ s => by cases s <;> assumption, fun h => ⟨h _, h _⟩⟩

-- ADE: none.
/-- The join of two qualities, `Ω` when both are, and `U` otherwise.
RFC: `\sqcup_s` -/
def join : Quality → Quality → Quality
  | prop, prop => prop
  | type, _ => type
  | _, type => type

instance : Max Quality := ⟨join⟩

-- ADE: none.
/-- A quality is below another when it is `Ω` whenever the other is.
RFC: `\le_s` -/
def Le (s₁ s₂ : Quality) : Prop := s₂ = prop → s₁ = prop

instance : LE Quality := ⟨Le⟩

instance (s₁ s₂ : Quality) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (s₂ = prop → s₁ = prop))

/-! ## Properties -/

-- ADE: none.
/-- The join of two qualities is the least quality above both.
RFC: `{\sqcup}{\le}_s.\mathsf{left}`
RFC: `{\sqcup}{\le}_s.\mathsf{right}`
RFC: `{\sqcup}{\le}_s.\mathsf{least}` -/
theorem join_isLeast : ∀ s₁ s₂ : Quality, IsLeastUpperBound (· ≤ ·) s₁ s₂ (s₁ ⊔ s₂) := by
  intro s₁ s₂
  cases s₁ <;> cases s₂ <;> exact ⟨by decide, by decide, by decide⟩

end Quality

-- ADE: `U`, in `Definition/Untyped.agda`, for the universes `U_l` only.
/-- A sort `κ` over `k` level variables, `s_l`: `U_l` or `Ω_l`.
RFC: `\mathsf{syntax}_\kappa` -/
structure Universe (k : Nat) where
  /-- `U` or `Ω`. -/
  quality : Quality
  /-- The level `l` of the sort. -/
  level : Level k
  deriving DecidableEq

namespace Universe

variable {k : Nat}

-- ADE: none.
/--
`κ₁ ≼ κ₂`: the sort `κ₂` bounds the sort `κ₁`, when the quality of `κ₁` is below the quality of
`κ₂`, so that `κ₁` is a universe of propositions when `κ₂` is, and the level of `κ₁` below the level
of `κ₂`.
RFC: `\preceq_\kappa`
-/
def Bounded (κ₁ κ₂ : Universe k) : Prop := κ₁.quality ≤ κ₂.quality ∧ κ₁.level ≤ κ₂.level

@[inherit_doc] infix:50 " ≼ " => Bounded

instance (κ₁ κ₂ : Universe k) : Decidable (κ₁ ≼ κ₂) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Properties -/

-- ADE: none.
/-- The relation `≼` is a preorder.
RFC: `\mathsf{preorder}_\kappa.\mathsf{refl}`
RFC: `\mathsf{preorder}_\kappa.\mathsf{trans}` -/
theorem preorder : IsPreorder (α := Universe k) (· ≼ ·) where
  refl _ := ⟨fun h => h, Level.preorder.refl _⟩
  trans h₁ h₂ := ⟨fun h => h₁.1 (h₂.1 h), Level.preorder.trans h₁.2 h₂.2⟩

-- ADE: none.
/-- The join of the qualities of two sorts at the same level is the least sort that bounds both.
RFC: `{\sqcup}{\preceq}_\kappa.\mathsf{left}`
RFC: `{\sqcup}{\preceq}_\kappa.\mathsf{right}`
RFC: `{\sqcup}{\preceq}_\kappa.\mathsf{least}` -/
theorem join_isLeast (s₁ s₂ : Quality) (l : Level k) :
    IsLeastUpperBound (· ≼ ·) (⟨s₁, l⟩ : Universe k) ⟨s₂, l⟩ ⟨s₁ ⊔ s₂, l⟩ :=
  have h := Quality.join_isLeast s₁ s₂
  ⟨⟨h.le_left, Level.preorder.refl _⟩, ⟨h.le_right, Level.preorder.refl _⟩,
    fun κ hκ₁ hκ₂ => ⟨h.least κ.quality hκ₁.1 hκ₂.1, hκ₁.2⟩⟩

end Universe

end Sic.Core
