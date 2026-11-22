module

public import Sic.Core.Syntax

/-!
# Grades of the Binders

The grades of the variables that the binders of the syntax of annex 08 of RFC 36 introduce, which
the rules of usage of annex 17 write in their premises by the extension `•` of the grade vectors of
annex 10: each variable of a telescope at the grade of its entry, or at a grade given for its
position; the recursive results of a branch of a recursor, whose positions the nestings of its
fields give, have their grades with the recursive results, in `Results`.
They read the grades that the syntax carries, and no judgment, so that the usage, which checks them,
and the relation of run time, which relates the variables that they do not erase, both read them.

ADE extend their grade vectors by one grade for each variable, by `_∙_` in `Graded/Context.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • (r · p₁) • … • (r · pₐ)`: the vector `γ` extended by a grade for each variable of a telescope
whose parameters are `ps`, the grade `pᵢ` of its entry multiplied by `r`, the first variable first. -/
def _root_.Sic.Grading.GradeVector.extendParams {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    (ps : List Parameter) → GradeVector (Γ.extend ps.length).length
  | [] => γ
  | p :: ps => extendParams (Γ := .var :: Γ) (γ ∙ (r * p.usage)) r ps

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • (r · q₁) • … • (r · qₐ)`: the vector `γ` extended by a grade for each variable of the
telescope `Θ`, the grade `qᵢ` with which the types after its entry use it multiplied by `r`, the
first variable first. -/
def _root_.Sic.Grading.GradeVector.extendTelescope {k : Nat} {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    {ps : List Parameter} → Telescope k Γ ps → GradeVector (Γ.extend ps.length).length
  | [], .nil => γ
  | _ :: _, .cons q _ _ Θ => extendTelescope (Γ := .var :: Γ) (γ ∙ (r * q)) r Θ

/-- The grades of the entries whose parameters are `ps`, the grade `p l` of the entry at each
position `l`, and `0`, erased, after them. -/
def Parameter.grades (ps : List Parameter) : Nat → Grade :=
  fun l => (ps.map (·.usage)).getD l Grade.zero

/-- The grade of the entry at a position is that of its parameter. -/
theorem Parameter.grades_of_getElem? {ps : List Parameter} {l : Nat} {p : Parameter}
    (h : ps[l]? = some p) : Parameter.grades ps l = p.usage := by
  simp [Parameter.grades, List.getD_eq_getElem?_getD, h]

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • g₀ • … • gₐ₋₁`: the vector `γ` extended by the grade `g l` of the variable of the entry at
each position `l` of a telescope whose parameters are `ps`, the first one at `0`. -/
def _root_.Sic.Grading.GradeVector.extendGrades {Γ : Scope} (γ : GradeVector Γ.length) (g : Nat → Grade) :
    (ps : List Parameter) → GradeVector (Γ.extend ps.length).length
  | [] => γ
  | _ :: ps => extendGrades (Γ := .var :: Γ) (γ ∙ g 0) (fun l => g (l + 1)) ps

end Sic.Core
