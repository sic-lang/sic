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
/-- The references that the recursions of a branch of a recursor of the multiplicity `ρ` need, for
each recursive result that it computes, on the field at the position `l`, what its value refers to:
one reference to the field, unless `ρ` is `0`, and the reads of the scope by the branches, `U_χ`,
for a result of the recursor, and the reads of the field and of the scope by the corecursor of a
nested result, `factor(σ) · ρ` and `factor(σ)` times. -/
def Demand.need (ρ : Multiplicity) (Us : List Demand) (Uχ : Demand) :
    List RecursiveResult → Demand
  | [] => 𝟘ᵛ
  | .erased :: ks => Demand.need ρ Us Uχ ks
  | .field l :: ks => (ρ.references ·ᶜ Us.getD l 𝟘ᵛ +ᶜ Uχ) +ᶜ Demand.need ρ Us Uχ ks
  | .nested l σ :: ks =>
    ((σ.factor * ρ) ·ᶜ Us.getD l 𝟘ᵛ +ᶜ σ.factor ·ᶜ Uχ) +ᶜ Demand.need ρ Us Uχ ks

namespace Demand

variable {ρ : Multiplicity} {Us : List Demand} {Uχ : Demand} {b : Nat}

/-- The recursions need no reference to an address that neither their fields nor the scope refer
to. -/
theorem need_eq_zero : {ks : List RecursiveResult} →
    (∀ (j : Nat) (k : RecursiveResult) l, ks[j]? = some k → k.fieldPosition = some l →
      k.factor ≠ .zero → ρ.references * Us.getD l 𝟘ᵛ b = .zero) →
      Uχ b = .zero → Demand.need ρ Us Uχ ks b = .zero
  | [], _, _ => rfl
  | .erased :: ks, h, hχ => need_eq_zero (ks := ks) (fun j => h (j + 1)) hχ
  | .field l :: ks, h, hχ => by
    show (ρ.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need ρ Us Uχ ks b = _
    rw [h 0 _ l rfl rfl (by simp [RecursiveResult.factor]), hχ, need_eq_zero (ks := ks) (fun j => h (j + 1)) hχ]
    rfl
  | .nested l σ :: ks, h, hχ => by
    show (σ.factor * ρ * Us.getD l 𝟘ᵛ b + σ.factor * Uχ b) + Demand.need ρ Us Uχ ks b = _
    rw [hχ, need_eq_zero (ks := ks) (fun j => h (j + 1)) hχ]
    by_cases hf : σ.factor = .zero
    · rw [hf]
      cases Us.getD l 𝟘ᵛ b <;> cases ρ <;> rfl
    · exact (by decide : ∀ f ρ u : Multiplicity, ρ.references * u = .zero →
        f * ρ * u + f * .zero + .zero = .zero) _ _ _ (h 0 _ l rfl rfl hf)

/-- The recursions need the reads of the scope, when a result that reads it is computed. -/
theorem need_ne_zero_scope : {ks : List RecursiveResult} → {j : Nat} → {k : RecursiveResult} →
    ks[j]? = some k → k.factor ≠ .zero → Uχ b ≠ .zero → Demand.need ρ Us Uχ ks b ≠ .zero
  | .field _ :: ks, 0, _, _, _, hχ =>
    Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_right _ _ hχ)
  | .nested _ σ :: ks, 0, _, h, hf, hχ => by
    cases h
    exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_right _ _
      (Multiplicity.mul_ne_zero _ _ hf hχ))
  | .erased :: ks, 0, _, h, hf, _ => by
    cases h
    exact absurd rfl hf
  | .erased :: ks, j + 1, _, h, hf, hχ => need_ne_zero_scope (ks := ks) (j := j) h hf hχ
  | .field _ :: ks, j + 1, _, h, hf, hχ =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_scope (ks := ks) (j := j) h hf hχ)
  | .nested _ _ :: ks, j + 1, _, h, hf, hχ =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_scope (ks := ks) (j := j) h hf hχ)

/-- The recursions need a reference to the field of each result of the recursor. -/
theorem need_ne_zero_field : {ks : List RecursiveResult} → {j l : Nat} →
    ks[j]? = some (.field l) → ρ.references * Us.getD l 𝟘ᵛ b ≠ .zero →
      Demand.need ρ Us Uχ ks b ≠ .zero
  | .field _ :: ks, 0, _, h, hl => by
    cases h
    exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_left _ _ hl)
  | .erased :: ks, 0, _, h, _ | .nested .. :: ks, 0, _, h, _ => nomatch h
  | .erased :: ks, j + 1, _, h, hl => need_ne_zero_field (ks := ks) (j := j) h hl
  | .field _ :: ks, j + 1, _, h, hl =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_field (ks := ks) (j := j) h hl)
  | .nested .. :: ks, j + 1, _, h, hl =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_field (ks := ks) (j := j) h hl)

/-- The recursions need the reads of the field of each nested result by its corecursor. -/
theorem need_ne_zero_nested : {ks : List RecursiveResult} → {j l : Nat} → {σ : Shape} →
    ks[j]? = some (.nested l σ) → σ.factor * ρ * Us.getD l 𝟘ᵛ b ≠ .zero →
      Demand.need ρ Us Uχ ks b ≠ .zero
  | .nested _ _ :: ks, 0, _, _, h, hl => by
    cases h
    exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.add_ne_zero_left _ _ hl)
  | .erased :: ks, 0, _, _, h, _ | .field _ :: ks, 0, _, _, h, _ => nomatch h
  | .erased :: ks, j + 1, _, _, h, hl => need_ne_zero_nested (ks := ks) (j := j) h hl
  | .field _ :: ks, j + 1, _, _, h, hl =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_nested (ks := ks) (j := j) h hl)
  | .nested .. :: ks, j + 1, _, _, h, hl =>
    Multiplicity.add_ne_zero_right _ _ (need_ne_zero_nested (ks := ks) (j := j) h hl)

/-- The recursions need nothing when no result reads anything. -/
theorem need_eq_zero_of_computed : {ks : List RecursiveResult} → {πs : List Multiplicity} →
    ks.length = πs.length → Multiplicity.computed ks πs = .zero →
      (∀ (j : Nat) (k : RecursiveResult) (π : Multiplicity), ks[j]? = some k → k ≠ .erased →
        πs[j]? = some π → π ≠ .zero) → Demand.need ρ Us Uχ ks b = .zero
  | [], _, _, _, _ => rfl
  | .erased :: ks, _ :: πs, hl, hs, hk => by
    have hs' : Multiplicity.computed ks πs = .zero :=
      (by decide : ∀ π s : Multiplicity, π * .zero + s = .zero → s = .zero) _ _ hs
    exact need_eq_zero_of_computed (ks := ks) (πs := πs) (Nat.succ.inj hl) hs' fun j => hk (j + 1)
  | .field l :: ks, π :: πs, _, hs, hk =>
    absurd ((by decide : ∀ x y : Multiplicity, x * .one + y = .zero → x = .zero) _ _ hs)
      (hk 0 _ π rfl (fun h => nomatch h) rfl)
  | .nested l σ :: ks, π :: πs, hl, hs, hk => by
    have hπ := hk 0 _ π rfl (fun h => nomatch h) rfl
    have hf : σ.factor = .zero := (by decide : ∀ π f s : Multiplicity, π ≠ .zero →
      π * f + s = .zero → f = .zero) _ _ _ hπ hs
    have hs' : Multiplicity.computed ks πs = .zero :=
      (by decide : ∀ π f s : Multiplicity, π * f + s = .zero → s = .zero) _ _ _ hs
    show (σ.factor * ρ * Us.getD l 𝟘ᵛ b + σ.factor * Uχ b) + Demand.need ρ Us Uχ ks b = _
    rw [hf, need_eq_zero_of_computed (ks := ks) (πs := πs) (Nat.succ.inj hl) hs'
      fun j => hk (j + 1)]
    cases ρ <;> cases Us.getD l 𝟘ᵛ b <;> cases Uχ b <;> rfl
  | _ :: _, [], hl, _, _ => nomatch hl

/-- The multiplicities of the results that are computed, times their factors, are not `0` together
when one of them reads the scope. -/
theorem computed_ne_zero : {ks : List RecursiveResult} → {πs : List Multiplicity} →
    ks.length = πs.length → {j : Nat} → {k : RecursiveResult} → ks[j]? = some k →
      k.factor ≠ .zero →
      (∀ (j : Nat) (k : RecursiveResult) (π : Multiplicity), ks[j]? = some k → k ≠ .erased →
        πs[j]? = some π → π ≠ .zero) → Multiplicity.computed ks πs ≠ .zero
  | k :: ks, π :: πs, _, 0, _, h, hf, hk => by
    cases h
    have hπ := hk 0 k π rfl (fun he => by subst he; exact hf rfl) rfl
    exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.mul_ne_zero _ _ hπ hf)
  | _ :: ks, _ :: πs, hl, j + 1, _, h, hf, hk =>
    Multiplicity.add_ne_zero_right _ _ (computed_ne_zero (ks := ks) (πs := πs) (Nat.succ.inj hl)
      (j := j) h hf fun j => hk (j + 1))
  | _ :: _, [], hl, _, _, _, _, _ => nomatch hl

/-- The reads of the scope, as many times as the results that are computed are read, each times its
factor, are within what the recursions need, when they need no reference to their fields. -/
theorem computed_mul_le_need : {ks : List RecursiveResult} → {πs : List Multiplicity} →
    ks.length = πs.length →
      (∀ (j : Nat) (k : RecursiveResult) l, ks[j]? = some k → k.fieldPosition = some l →
        k.factor ≠ .zero → ρ.references * Us.getD l 𝟘ᵛ b = .zero) →
      (∀ (j : Nat) (k : RecursiveResult) (π : Multiplicity), ks[j]? = some k → k ≠ .erased →
        πs[j]? = some π → π ≠ .zero) → Multiplicity.computed ks πs * Uχ b ≤ Demand.need ρ Us Uχ ks b
  | [], [], _, _, _ => by
    show Multiplicity.zero * Uχ b ≤ Multiplicity.zero
    cases Uχ b <;> decide
  | k :: ks, π :: πs, hl, h, hk => by
    have ih := computed_mul_le_need (ks := ks) (πs := πs) (Nat.succ.inj hl) (fun j => h (j + 1))
      fun j => hk (j + 1)
    show (π * k.factor + Multiplicity.computed ks πs) * Uχ b ≤ Demand.need ρ Us Uχ (k :: ks) b
    cases k with
    | erased =>
      show (π * .zero + Multiplicity.computed ks πs) * Uχ b ≤ Demand.need ρ Us Uχ ks b
      exact (by decide : ∀ π s c n : Multiplicity, s * c ≤ n → (π * .zero + s) * c ≤ n)
        _ _ _ _ ih
    | field l =>
      show (π * .one + Multiplicity.computed ks πs) * Uχ b ≤
        (ρ.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need ρ Us Uχ ks b
      rw [h 0 _ l rfl rfl (by simp [RecursiveResult.factor])]
      exact (by decide : ∀ π s c n : Multiplicity, π ≠ .zero → s * c ≤ n →
        (π * .one + s) * c ≤ (.zero + c) + n) _ _ _ _ (hk 0 _ π rfl (fun h => nomatch h) rfl) ih
    | nested l σ =>
      show (π * σ.factor + Multiplicity.computed ks πs) * Uχ b ≤
        (σ.factor * ρ * Us.getD l 𝟘ᵛ b + σ.factor * Uχ b) + Demand.need ρ Us Uχ ks b
      have hπ := hk 0 _ π rfl (fun h => nomatch h) rfl
      by_cases hf : σ.factor = .zero
      · rw [hf]
        exact (by decide : ∀ π ρ u s c n : Multiplicity, s * c ≤ n →
          (π * .zero + s) * c ≤ (.zero * ρ * u + .zero * c) + n) _ _ _ _ _ _ ih
      · exact (by decide : ∀ π f ρ u s c n : Multiplicity, π ≠ .zero →
          ρ.references * u = .zero → s * c ≤ n →
          (π * f + s) * c ≤ (f * ρ * u + f * c) + n) _ _ _ _ _ _ _ hπ
          (h 0 _ l rfl rfl hf) ih
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => nomatch hl

/-- The uses of the fields by the recursions of the recursor of the multiplicity `1` are within
what the recursions need, when the branches read no variable of the scope at the address. -/
theorem recursions_le_need (hρ : ρ = .one) (hχ : Uχ b = .zero) : {ks : List RecursiveResult} →
    {πs : List Multiplicity} → ks.length = πs.length →
      (∀ (j : Nat) (k : RecursiveResult) (π : Multiplicity), ks[j]? = some k → k ≠ .erased →
        πs[j]? = some π → π ≠ .zero) → Demand.recursions ks πs Us b ≤ Demand.need ρ Us Uχ ks b
  | [], [], _, _ => Multiplicity.le_refl' .zero
  | k :: ks, π :: πs, hl, hk => by
    have ih := recursions_le_need hρ hχ (ks := ks) (πs := πs) (Nat.succ.inj hl)
      fun j => hk (j + 1)
    subst hρ
    cases k with
    | erased => exact ih
    | field l =>
      show π * Us.getD l 𝟘ᵛ b + Demand.recursions ks πs Us b ≤
        (Multiplicity.one.references * Us.getD l 𝟘ᵛ b + Uχ b) + Demand.need .one Us Uχ ks b
      rw [hχ]
      exact (by decide : ∀ π u r n : Multiplicity, π ≠ .zero → r ≤ n →
        π * u + r ≤ (Multiplicity.one.references * u + .zero) + n) _ _ _ _
        (hk 0 _ π rfl (fun h => nomatch h) rfl) ih
    | nested l σ =>
      show (π * σ.factor) * Us.getD l 𝟘ᵛ b + Demand.recursions ks πs Us b ≤
        (σ.factor * .one * Us.getD l 𝟘ᵛ b + σ.factor * Uχ b) + Demand.need .one Us Uχ ks b
      rw [hχ]
      exact (by decide : ∀ π f u r n : Multiplicity, π ≠ .zero → r ≤ n →
        π * f * u + r ≤ (f * .one * u + f * .zero) + n) _ _ _ _ _
        (hk 0 _ π rfl (fun h => nomatch h) rfl) ih
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => nomatch hl

end Demand

end Sic.Core
