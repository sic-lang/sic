module

import Sic.Core.Substitution

/-!
# Meaning of the Substitution

The weakenings and the instantiation against their meaning.
-/

namespace SicTest.Meaning.Substitution

open Sic.Core Sic.Grade Sic.Core.Term

/-- A term that does not use the variable `x` is unchanged by `t[a/x]`. -/
theorem instantiate_wk1 (t : Term k n) (a : Term k n) : t.wk1.instantiate a = t :=
  (subst_wk _ _ t).trans (subst_var t)

/-!
The meaning of the weakenings: a weakening keeps the variables of the smaller context in the same
order, so it denotes a strictly increasing map between the indices, and every such map is the
meaning of a weakening.
Several weakenings may denote the same map, as `id` and `lift id` do.
-/

/-- The map `f` between indices is strictly increasing. -/
def StrictMono (f : Fin n → Fin m) : Prop := ∀ x y, x < y → f x < f y

theorem var_strictMono : ∀ ρ : Wk m n, StrictMono ρ.var
  | .id, _, _, h => h
  | .step ρ, x, y, h => Nat.succ_lt_succ (var_strictMono ρ x y h)
  | .lift _, ⟨0, _⟩, ⟨0, _⟩, h => absurd h (Nat.lt_irrefl 0)
  | .lift _, ⟨0, _⟩, ⟨_ + 1, _⟩, _ => Nat.succ_pos _
  | .lift _, ⟨_ + 1, _⟩, ⟨0, _⟩, h => absurd h (Nat.not_lt_zero _)
  | .lift ρ, ⟨_ + 1, _⟩, ⟨_ + 1, _⟩, h =>
    Nat.succ_lt_succ (var_strictMono ρ _ _ (Nat.lt_of_succ_lt_succ h))

/-!
How completeness is proved, by induction on the size `m` of the larger context: if the map sends
the innermost variable `0` to `0`, it is a `lift` of the map on the other variables, shifted down
by one, and otherwise none of its values is `0`, so it is a `step` of the map shifted down by one.
-/

theorem exists_wk : ∀ {m n : Nat} (f : Fin n → Fin m), StrictMono f → ∃ ρ : Wk m n, ρ.var = f
  | 0, 0, f, _ => ⟨.id, funext (·.elim0)⟩
  | 0, _ + 1, f, _ => (f 0).elim0
  | m + 1, n, f, hf => by
    by_cases h0 : ∃ h : 0 < n, (f ⟨0, h⟩).val = 0
    · obtain ⟨hn, h0⟩ := h0
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have pos : ∀ x : Fin n, 0 < (f x.succ).val := fun x =>
        h0 ▸ hf ⟨0, hn⟩ x.succ (Nat.succ_pos _)
      let g : Fin n → Fin m := fun x =>
        ⟨(f x.succ).val - 1, by have := (f x.succ).isLt; have := pos x; omega⟩
      have hg : StrictMono g := fun x y h => by
        have := hf x.succ y.succ (Nat.succ_lt_succ h); have := pos x
        show (f x.succ).val - 1 < (f y.succ).val - 1; omega
      obtain ⟨ρ, hρ⟩ := exists_wk g hg
      refine ⟨.lift ρ, funext fun x => Fin.ext ?_⟩
      match x with
      | ⟨0, _⟩ => exact h0.symm
      | ⟨x + 1, hx⟩ =>
        let y : Fin n := ⟨x, Nat.lt_of_succ_lt_succ hx⟩
        have := pos y
        show (ρ.var y).val + 1 = (f y.succ).val
        rw [hρ]
        show (f y.succ).val - 1 + 1 = _
        omega
    · have pos : ∀ x, 0 < (f x).val := fun x => by
        have := x.isLt
        have : ¬(f ⟨0, by omega⟩).val = 0 := fun h => h0 ⟨by omega, h⟩
        rcases Nat.eq_zero_or_pos x.val with hx | hx
        · rw [show x = ⟨0, by omega⟩ from Fin.ext hx]; omega
        · have := hf ⟨0, by omega⟩ x hx; omega
      let g : Fin n → Fin m := fun x =>
        ⟨(f x).val - 1, by have := (f x).isLt; have := pos x; omega⟩
      have hg : StrictMono g := fun x y h => by
        have := hf x y h; have := pos x
        show (f x).val - 1 < (f y).val - 1; omega
      obtain ⟨ρ, hρ⟩ := exists_wk g hg
      refine ⟨.step ρ, funext fun x => Fin.ext ?_⟩
      show (ρ.var x).val + 1 = _
      rw [hρ]; have := pos x
      show (f x).val - 1 + 1 = _; omega

/-- The weakenings denote exactly the strictly increasing maps between indices. -/
theorem strictMono_iff_wk (f : Fin n → Fin m) : StrictMono f ↔ ∃ ρ : Wk m n, ρ.var = f :=
  ⟨exists_wk f, fun ⟨ρ, h⟩ => h ▸ var_strictMono ρ⟩

/-!
The composition of the weakenings is a composition: `id` is neutral on both sides, and composing is
associative, as weakenings, not only as the maps they denote.
-/

theorem id_comp (ρ : Wk m n) : Wk.id.comp ρ = ρ := rfl

theorem comp_id : ∀ ρ : Wk m n, ρ.comp .id = ρ
  | .id => rfl
  | .step ρ => congrArg Wk.step (comp_id ρ)
  | .lift _ => rfl

theorem comp_assoc : ∀ (ρ₁ : Wk m l) (ρ₂ : Wk l j) (ρ₃ : Wk j n),
    (ρ₁.comp ρ₂).comp ρ₃ = ρ₁.comp (ρ₂.comp ρ₃)
  | .id, _, _ => rfl
  | .step ρ₁, ρ₂, ρ₃ => congrArg Wk.step (comp_assoc ρ₁ ρ₂ ρ₃)
  | .lift _, .id, _ => rfl
  | .lift ρ₁, .step ρ₂, ρ₃ => congrArg Wk.step (comp_assoc ρ₁ ρ₂ ρ₃)
  | .lift _, .lift _, .id => rfl
  | .lift ρ₁, .lift ρ₂, .step ρ₃ => congrArg Wk.step (comp_assoc ρ₁ ρ₂ ρ₃)
  | .lift ρ₁, .lift ρ₂, .lift ρ₃ => congrArg Wk.lift (comp_assoc ρ₁ ρ₂ ρ₃)

end SicTest.Meaning.Substitution
