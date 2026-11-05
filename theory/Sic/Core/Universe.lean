module

public import Sic.Core.Level

/-!
# Universes

The sorts of RFC 24: the universes `U_l`, whose elements are types, and the universes of strict
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
/-- The quality of a sort, as the sort qualities of Rocq: a universe or a universe of propositions. -/
inductive Quality where
  /-- `U`, the quality of the universes. -/
  | type
  /-- `Ω`, the quality of the universes of strict propositions. -/
  | prop
  deriving DecidableEq

namespace Quality

/-- Decides a statement on all the qualities by checking both. -/
instance {P : Quality → Prop} [DecidablePred P] : Decidable (∀ q, P q) :=
  decidable_of_iff (P type ∧ P prop)
    ⟨fun ⟨h₁, h₂⟩ q => by cases q <;> assumption, fun h => ⟨h _, h _⟩⟩

-- ADE: none.
/-- `(⊔_s)`: the join of two qualities, `Ω` when both are, and `U` otherwise. -/
def join : Quality → Quality → Quality
  | prop, prop => prop
  | _, _ => type

instance : Max Quality := ⟨join⟩

/-- A quality is below another when it is `Ω` whenever the other is. -/
def Le (q₁ q₂ : Quality) : Prop := q₂ = prop → q₁ = prop

instance : LE Quality := ⟨Le⟩

instance (q₁ q₂ : Quality) : Decidable (q₁ ≤ q₂) :=
  inferInstanceAs (Decidable (q₂ = prop → q₁ = prop))

/-! The table of `(⊔_s)`. -/

example : prop ⊔ prop = prop := rfl

example : type ⊔ prop = type := rfl

example : prop ⊔ type = type := rfl

example : type ⊔ type = type := rfl

/-- The join is the least quality above both, as the RFC says. -/
theorem join_isLeast : ∀ q₁ q₂ : Quality,
    q₁ ≤ q₁ ⊔ q₂ ∧ q₂ ≤ q₁ ⊔ q₂ ∧ ∀ q, q₁ ≤ q → q₂ ≤ q → q₁ ⊔ q₂ ≤ q := by
  decide

end Quality

-- ADE: `U`, in `Definition/Untyped.agda`, for the universes `U_l` only.
/-- A sort `κ` over `k` level variables: `U_l` or `Ω_l`. -/
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
`κ₁ ≼ κ₂`: the sort `κ₂` bounds the sort `κ₁`, when the level of `κ₁` is below the level of `κ₂`,
and `κ₁` is a universe of propositions when `κ₂` is.
-/
def Bounded (κ₁ κ₂ : Universe k) : Prop := κ₁.level ≤ κ₂.level ∧ κ₁.quality ≤ κ₂.quality

@[inherit_doc] infix:50 " ≼ " => Bounded

instance (κ₁ κ₂ : Universe k) : Decidable (κ₁ ≼ κ₂) := inferInstanceAs (Decidable (_ ∧ _))

theorem bounded_refl (κ : Universe k) : κ ≼ κ := ⟨Level.le_refl _, fun h => h⟩

theorem bounded_trans {κ₁ κ₂ κ₃ : Universe k} (h₁ : κ₁ ≼ κ₂) (h₂ : κ₂ ≼ κ₃) : κ₁ ≼ κ₃ :=
  ⟨Level.le_trans h₁.1 h₂.1, fun h => h₁.2 (h₂.2 h)⟩

/-- The join of the qualities of two sorts at a level is the least sort at this level that bounds
both, as the RFC says of the join of sorts. -/
theorem join_isLeast (q₁ q₂ : Quality) (l : Level k) :
    ⟨q₁, l⟩ ≼ ⟨q₁ ⊔ q₂, l⟩ ∧ ⟨q₂, l⟩ ≼ ⟨q₁ ⊔ q₂, l⟩ ∧
      ∀ κ : Universe k, ⟨q₁, l⟩ ≼ κ → ⟨q₂, l⟩ ≼ κ → ⟨q₁ ⊔ q₂, l⟩ ≼ κ := by
  obtain ⟨h₁, h₂, h⟩ := Quality.join_isLeast q₁ q₂
  exact ⟨⟨Level.le_refl _, h₁⟩, ⟨Level.le_refl _, h₂⟩,
    fun κ hκ₁ hκ₂ => ⟨hκ₁.1, h κ.quality hκ₁.2 hκ₂.2⟩⟩

end Universe

end Sic.Core
