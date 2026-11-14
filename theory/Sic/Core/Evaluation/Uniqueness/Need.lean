module

public import Sic.Core.Evaluation.Conservation.Recursions
public import Sic.Core.Evaluation.Paths

/-!
# Needs of the Recursions

The references that the recursions of a branch of a recursor need, for the proof of the invariant
of the uniqueness at run time: the proof of the case of the recursor compares them with the
references of the fields of the constructor and of the scope of the branches.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- The references that the recursions of a branch of a recursor of the multiplicity `ρ` need: for
each recursive result that it computes, on the field at the position `l`, one reference to the
field, unless `ρ` is `0`, and the reads of the scope by the branches, `U_χ`. -/
def Demand.need (ρ : Multiplicity) (Us : List Demand) (Uχ : Demand) : List (Option Nat) → Demand
  | [] => 𝟘ᵛ
  | none :: ks => Demand.need ρ Us Uχ ks
  | some l :: ks => (ρ.references ·ᶜ Us.getD l 𝟘ᵛ +ᶜ Uχ) +ᶜ Demand.need ρ Us Uχ ks

namespace Demand

variable {ρ : Multiplicity} {Us : List Demand} {Uχ : Demand} {b : Nat}

/-- The recursions need no reference to an address that neither their fields nor the scope refer
to. -/
theorem need_eq_zero : {ks : List (Option Nat)} →
    (∀ (j l : Nat), ks[j]? = some (some l) → ρ.references * Us.getD l 𝟘ᵛ b = .zero) →
      Uχ b = .zero → Demand.need ρ Us Uχ ks b = .zero
  | [], _, _ => rfl
  | none :: ks, h, hχ => need_eq_zero (ks := ks) (fun j => h (j + 1)) hχ
  | some l :: ks, h, hχ => by
    show (ρ.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need ρ Us Uχ ks b = _
    rw [h 0 l rfl, hχ, need_eq_zero (ks := ks) (fun j => h (j + 1)) hχ]
    rfl

/-- The recursions need the reads of the scope, when a result is computed. -/
theorem need_ne_zero_scope : {ks : List (Option Nat)} → {j l : Nat} → ks[j]? = some (some l) →
    Uχ b ≠ .zero → Demand.need ρ Us Uχ ks b ≠ .zero
  | some _ :: ks, 0, _, _, hχ =>
    Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_right _ _ hχ)
  | none :: ks, j + 1, _, h, hχ => need_ne_zero_scope (ks := ks) (j := j) (by simpa using h) hχ
  | some _ :: ks, j + 1, _, h, hχ =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_scope (ks := ks) (j := j) (by simpa using h) hχ)

/-- The recursions need a reference to the field of each result that is computed. -/
theorem need_ne_zero_field : {ks : List (Option Nat)} → {j l : Nat} → ks[j]? = some (some l) →
    ρ.references * Us.getD l 𝟘ᵛ b ≠ .zero → Demand.need ρ Us Uχ ks b ≠ .zero
  | some _ :: ks, 0, _, h, hl => by
    cases h
    exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_left _ _ hl)
  | none :: ks, j + 1, _, h, hl => need_ne_zero_field (ks := ks) (j := j) (by simpa using h) hl
  | some _ :: ks, j + 1, _, h, hl =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_field (ks := ks) (j := j) (by simpa using h) hl)

/-- The recursions need nothing when no result is computed. -/
theorem need_eq_zero_of_computed : {ks : List (Option Nat)} → {πs : List Multiplicity} →
    ks.length = πs.length → Multiplicity.computed ks πs = .zero →
      (∀ (j l : Nat) (π : Multiplicity), ks[j]? = some (some l) → πs[j]? = some π →
        π ≠ .zero) → Demand.need ρ Us Uχ ks b = .zero
  | [], _, _, _, _ => rfl
  | none :: ks, _ :: πs, hl, hs, hk =>
    need_eq_zero_of_computed (ks := ks) (πs := πs) (Nat.succ.inj hl) hs fun j => hk (j + 1)
  | some l :: ks, π :: πs, _, hs, hk =>
    absurd ((by decide : ∀ x y : Multiplicity, x + y = .zero → x = .zero) _ _ hs)
      (hk 0 l π rfl rfl)
  | _ :: _, [], hl, _, _ => nomatch hl

/-- The multiplicities of the results that are computed are not `0` together when one is computed.
-/
theorem computed_ne_zero : {ks : List (Option Nat)} → {πs : List Multiplicity} →
    ks.length = πs.length → {j l : Nat} → ks[j]? = some (some l) →
      (∀ (j l : Nat) (π : Multiplicity), ks[j]? = some (some l) → πs[j]? = some π →
        π ≠ .zero) → Multiplicity.computed ks πs ≠ .zero
  | some l :: ks, π :: πs, _, 0, _, _, hk => Multiplicity.add_ne_zero_left _ _ (hk 0 l π rfl rfl)
  | none :: ks, _ :: πs, hl, j + 1, _, h, hk =>
    computed_ne_zero (ks := ks) (πs := πs) (Nat.succ.inj hl) (j := j) (by simpa using h)
      fun j => hk (j + 1)
  | some _ :: ks, _ :: πs, hl, j + 1, _, h, hk =>
    Multiplicity.add_ne_zero_right _ _ (computed_ne_zero (ks := ks) (πs := πs) (Nat.succ.inj hl)
      (j := j) (by simpa using h) fun j => hk (j + 1))
  | _ :: _, [], hl, _, _, _, _ => nomatch hl

/-- The reads of the scope, as many times as the results that are computed are read, are within
what the recursions need, when they need no reference to their fields. -/
theorem computed_mul_le_need : {ks : List (Option Nat)} → {πs : List Multiplicity} →
    ks.length = πs.length →
      (∀ (j l : Nat), ks[j]? = some (some l) → ρ.references * Us.getD l 𝟘ᵛ b = .zero) →
      (∀ (j l : Nat) (π : Multiplicity), ks[j]? = some (some l) → πs[j]? = some π →
        π ≠ .zero) → Multiplicity.computed ks πs * Uχ b ≤ Demand.need ρ Us Uχ ks b
  | [], [], _, _, _ => by
    show Multiplicity.zero * Uχ b ≤ Multiplicity.zero
    cases Uχ b <;> decide
  | none :: ks, _ :: πs, hl, h, hk =>
    computed_mul_le_need (ks := ks) (πs := πs) (Nat.succ.inj hl) (fun j => h (j + 1))
      fun j => hk (j + 1)
  | some l :: ks, π :: πs, hl, h, hk => by
    have ih := computed_mul_le_need (ks := ks) (πs := πs) (Nat.succ.inj hl) (fun j => h (j + 1))
      fun j => hk (j + 1)
    show (π + Multiplicity.computed ks πs) * Uχ b ≤
      (ρ.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need ρ Us Uχ ks b
    rw [h 0 l rfl]
    exact (by decide : ∀ π s c n : Multiplicity, π ≠ .zero → s * c ≤ n →
      (π + s) * c ≤ (.zero + c) + n) _ _ _ _ (hk 0 l π rfl rfl) ih
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => nomatch hl

/-- The uses of the fields by the recursions are within what the recursions need, when the
branches read no variable of the scope at the address. -/
theorem recursions_le_need (hρ : ρ ≠ .zero) (hχ : Uχ b = .zero) : {ks : List (Option Nat)} →
    {πs : List Multiplicity} → ks.length = πs.length →
      (∀ (j l : Nat) (π : Multiplicity), ks[j]? = some (some l) → πs[j]? = some π →
        π ≠ .zero) → Demand.recursions ks πs Us b ≤ Demand.need ρ Us Uχ ks b
  | [], [], _, _ => Multiplicity.le_refl' .zero
  | none :: ks, _ :: πs, hl, hk =>
    recursions_le_need hρ hχ (ks := ks) (πs := πs) (Nat.succ.inj hl) fun j => hk (j + 1)
  | some l :: ks, π :: πs, hl, hk => by
    have ih := recursions_le_need hρ hχ (ks := ks) (πs := πs) (Nat.succ.inj hl)
      fun j => hk (j + 1)
    show π * Us.getD l 𝟘ᵛ b + Demand.recursions ks πs Us b ≤
      (ρ.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need ρ Us Uχ ks b
    rw [hχ]
    exact (by decide : ∀ π ρ u r n : Multiplicity, π ≠ .zero → ρ ≠ .zero → r ≤ n →
      π * u + r ≤ (ρ.references * u + .zero) + n) _ _ _ _ _ (hk 0 l π rfl rfl) hρ ih
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => nomatch hl

end Demand

end Sic.Core
