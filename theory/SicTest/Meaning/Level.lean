module

public import Sic.Core.Level

/-!
# Meaning of the Levels

The equality of levels against its meaning, and the laws of levels.
-/

@[expose] public section

namespace SicTest.Meaning.Level

open Sic.Core Sic.Core.Level

/-- Without variables, two levels are equal when they have the same value. -/
theorem equiv_iff_eval {l₁ l₂ : Level 0} : l₁ ≈ l₂ ↔ eval Fin.elim0 l₁ = eval Fin.elim0 l₂ :=
  ⟨fun h => h _, fun h ρ => by rw [show ρ = Fin.elim0 from funext (·.elim0)]; exact h⟩

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

end SicTest.Meaning.Level
