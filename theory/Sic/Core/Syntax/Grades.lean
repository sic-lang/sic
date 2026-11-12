module

public import Sic.Core.Syntax

/-!
# Grades of the Binders

The grades of the variables that the binders of the syntax of annex 08 of RFC 36 introduce, which
the rules of usage of annex 12 write in their premises by the extension `•` of the grade vectors of
annex 10: each variable of a telescope at the grade of its entry, or at a grade given for its
position, and each recursive result of a branch of a recursor at its grade.
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

-- ADE: none.
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

-- ADE: none.
/-- `e_l`: the grade of the recursive result of the field at each position `l` of the fields whose
recursive fields the types `rs` of the block mark, the first field at `0`, read from the grades `es`
of the recursive results in order, and `0` for a field that is not recursive. -/
def Telescope.resultGrades : List (Option Name) → List Grade → Nat → Grade
  | some _ :: _, e :: _, 0 => e
  | some _ :: rs, _ :: es, l + 1 => Telescope.resultGrades rs es l
  | none :: rs, es, l + 1 => Telescope.resultGrades rs es l
  | _, _, _ => Grade.zero

/-- `e_{jil}`: the grade of the recursive result of the field at each position `l` of the branch at
the position `i` of the branches `us`, whose recursive fields the types `rs` of the block mark. -/
def Branches.resultGrades {k : Nat} {Γ : Scope} (us : Branches k Γ) (i : Nat)
    (rs : List (Option Name)) : Nat → Grade :=
  Telescope.resultGrades rs (us.grades i)

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • e_{l₁} • … • e_{l_b}`: the vector `γ` extended by the grade `e l` of the recursive result of
each recursive field, at its position `l` in the fields whose entries have the parameters `ps` and
whose recursive fields the types `rs` of the block mark, the first field at `0`, in order. -/
def _root_.Sic.Grading.GradeVector.extendResults {Γ : Scope} (γ : GradeVector Γ.length) (e : Nat → Grade) :
    (rs : List (Option Name)) → (ps : List Parameter) →
      GradeVector (Γ.extend (Telescope.resultParams rs ps).length).length
  | some _ :: rs, _ :: ps =>
    extendResults (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) rs ps
  | none :: rs, _ :: ps => extendResults γ (fun l => e (l + 1)) rs ps
  | [], _ | some _ :: _, [] | none :: _, [] => γ

-- ADE: none.
/-- `e_{l₁} + … + e_{l_b}`: the sum of the grades `e l` of the recursive results of the recursive
fields that the types `rs` of the block mark, at their positions `l`, the first field at `0`. -/
def Telescope.resultSum (e : Nat → Grade) : List (Option Name) → Grade
  | [] => Grade.zero
  | some _ :: rs => e 0 + Telescope.resultSum (fun l => e (l + 1)) rs
  | none :: rs => Telescope.resultSum (fun l => e (l + 1)) rs

end Sic.Core
