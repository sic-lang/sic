module

public import Sic.Core.Usage.Renaming

/-!
# Renaming a Vector of Grades

The vector of grades renamed of annex 10 of RFC 36 on two renamings: the one that renames the two
variables `x, y` of a scope to the variable `z`, whose grades add up, and the one that skips a new
variable, which gets the grade `00ᵖ`.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- The renaming of the scope `x, y` in the scope `z` that renames both variables to `z`. -/
def contract : Ren [.var] [.var, .var] := fun {_} x =>
  match x with
  | .zero => .zero
  | .succ .zero => .zero

/-- The variables `x` and `y`, used once each, rename to `z`, used twice, which the grade `ωωᵖ`
allows: `(x ▶ 11ᵖ, y ▶ 11ᵖ)[ξ] = (z ▶ ωωᵖ)`. -/
example : GradeVector.rename (Δ := [.var, .var]) (fun _ => Grade.one) contract =
    fun _ => Grade.unrestrictedUnrestricted := by
  decide

/-- The variable `x`, used once, renamed in the scope extended by a new variable, which it does not
use: `(x ▶ 11ᵖ)[ξ] = (x ▶ 11ᵖ, y ▶ 00ᵖ)`. -/
example : GradeVector.rename (Δ := [.var]) (fun _ => Grade.one) (Ren.weaken (e := .var)) =
    (fun _ => Grade.one : GradeVector 1) ∙ Grade.zero := by
  decide

end SicExample.Core
