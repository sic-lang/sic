module

import Sic.Core.Level

/-!
# RFC 24: Levels

The claims of RFC 24 on its levels.
-/

@[expose] public section

namespace SicTest.Rfc24.Level

open Sic.Core Sic.Core.Level

/-! The claims of RFC 24, with two level variables `l₁` and `l₂`. -/

/-- `l₁ ⊔ l₁` equals `l₁`. -/
example : (var 0 ⊔ var 0 : Level 2) ≈ var 0 := fun _ => Nat.max_self _

/-- `l₁ ⊔ l₂` does not equal `l₁`: they have different values when `l₁` is `0` and `l₂` is `1`. -/
example : ¬(var 0 ⊔ var 1 : Level 2) ≈ var 0 := fun h => absurd (h fun i => i.val) (by decide)

/-- `l₁ ⊔ l₂` has the same value as `l₁` exactly when `l₂` is at most `l₁`. -/
example (ρ : Fin 2 → Nat) : eval ρ (var 0 ⊔ var 1) = eval ρ (var 0) ↔ ρ 1 ≤ ρ 0 := by
  simp only [eval_max, eval]; omega

end SicTest.Rfc24.Level
