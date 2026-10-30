module

import Sic.Core.Level

/-!
# Validation of the Levels

The definitions of `Sic.Core.Level` checked against RFC 24, on the Church numerals, and against the
laws of levels.
-/

namespace Sic.Core.Level.Validation

open Level

/-! The claims of RFC 24, with two level variables `l₁` and `l₂`. -/

/-- `l₁ ⊔ l₁` equals `l₁`. -/
example : (var 0 ⊔ var 0 : Level 2) ≈ var 0 := fun _ => Nat.max_self _

/-- `l₁ ⊔ l₂` does not equal `l₁`: they have different values when `l₁` is `0` and `l₂` is `1`. -/
example : ¬(var 0 ⊔ var 1 : Level 2) ≈ var 0 := fun h => absurd (h fun i => i.val) (by decide)

/-- `l₁ ⊔ l₂` has the same value as `l₁` exactly when `l₂` is at most `l₁`. -/
example (ρ : Fin 2 → Nat) : eval ρ (var 0 ⊔ var 1) = eval ρ (var 0) ↔ ρ 1 ≤ ρ 0 := by
  simp only [eval_max, eval]; omega

/-- Without variables, two levels are equal when they have the same value. -/
theorem equiv_iff_eval {l₁ l₂ : Level 0} : l₁ ≈ l₂ ↔ eval Fin.elim0 l₁ = eval Fin.elim0 l₂ :=
  ⟨fun h => h _, fun h ρ => by rw [show ρ = Fin.elim0 from funext (·.elim0)]; exact h⟩

/-! The Church numerals of the literature, with one level variable `l`. -/

/--
The type `Nat_l` of the Church numerals, which `(Π)` puts at the level
`(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))`, lives at the level `l + 1`, above the types its numerals iterate
over, where the numerals of System F iterate over every type, their own included.
-/
example : (succ (var 0) ⊔ ((var 0 ⊔ var 0) ⊔ (var 0 ⊔ var 0)) : Level 1) ≈ succ (var 0) :=
  fun ρ => by simp only [eval_max, eval]; omega

/-!
The laws of levels, which every valuation satisfies: `⊔` is associative, commutative and idempotent,
`0` is its unit, and the successor distributes over it and is larger than its argument.
-/

section Laws

variable {k : Nat} (l l₁ l₂ l₃ : Level k)

example : ((l₁ ⊔ l₂) ⊔ l₃) ≈ (l₁ ⊔ (l₂ ⊔ l₃)) := fun ρ => by simp only [eval_max]; omega
example : (l₁ ⊔ l₂) ≈ (l₂ ⊔ l₁) := fun ρ => by simp only [eval_max]; omega
example : (l ⊔ l) ≈ l := fun ρ => by simp only [eval_max]; omega
example : (zero ⊔ l) ≈ l := fun ρ => by simp only [eval_max, eval]; omega
example : succ (l₁ ⊔ l₂) ≈ (succ l₁ ⊔ succ l₂) := fun ρ => by simp only [eval_max, eval]; omega
example : (l ⊔ succ l) ≈ succ l := fun ρ => by simp only [eval_max, eval]; omega
example : ¬succ l ≈ l := fun h => by have := h fun _ => 0; simp only [eval] at this; omega

end Laws

end Sic.Core.Level.Validation
