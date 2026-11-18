module

public import Sic.Core.Nesting

/-!
# Grades of the Binders

The grades of the variables that the binders of the syntax of annex 08 of RFC 36 introduce, which
the rules of usage of annex 12 write in their premises by the extension `•` of the grade vectors of
annex 10: each variable of a telescope at the grade of its entry, or at a grade given for its
position, and each recursive result of a branch of a recursor at its grade, a result for each
field whose nesting of annex 14 has a position.
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
nestings are `ns`, the first field at `0`, read from the grades `es` of the recursive results in
order, and `0` for a field without result, whose nesting has no position. -/
def Telescope.resultGrades : List (Nest Name) → List Grade → Nat → Grade
  | .direct _ :: _, e :: _, 0 => e
  | .inst _ :: _, e :: _, 0 => e
  | .direct _ :: ns, _ :: es, l + 1 => Telescope.resultGrades ns es l
  | .inst _ :: ns, _ :: es, l + 1 => Telescope.resultGrades ns es l
  | .plain :: ns, es, l + 1 => Telescope.resultGrades ns es l
  | _, _, _ => Grade.zero

/-- A position has the grade `0`, erased, when no grade of a recursive result is left. -/
theorem Telescope.resultGrades_nil : (ns : List (Nest Name)) → (l : Nat) →
    Telescope.resultGrades ns [] l = Grade.zero
  | [], _ | .direct _ :: _, _ | .inst _ :: _, _ => rfl
  | .plain :: _, 0 => rfl
  | .plain :: ns, l + 1 => Telescope.resultGrades_nil ns l

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • e_{l₁} • … • e_{l_b}`: the vector `γ` extended by the grade `e l` of the recursive result of
each field that has one, at its position `l` in the fields whose entries have the parameters `ps`
and whose nestings are `ns`, the first field at `0`, in order. -/
def _root_.Sic.Grading.GradeVector.extendResults {Γ : Scope} (γ : GradeVector Γ.length) (e : Nat → Grade) :
    (ns : List (Nest Name)) → (ps : List Parameter) →
      GradeVector (Γ.extend (Telescope.nestResultParams ns ps).length).length
  | .direct _ :: ns, _ :: ps =>
    extendResults (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) ns ps
  | .inst _ :: ns, _ :: ps =>
    extendResults (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) ns ps
  | .plain :: ns, _ :: ps => extendResults γ (fun l => e (l + 1)) ns ps
  | [], _ | .plain :: _, [] | .direct _ :: _, [] | .inst _ :: _, [] => γ

/-- The extension by the recursive results at the grades `es`, in order, is the extension by the
variables of the telescope of their parameters at these grades. -/
theorem _root_.Sic.Grading.GradeVector.extendResults_resultGrades {Γ : Scope} :
    (γ : GradeVector Γ.length) → (ns : List (Nest Name)) → (ps : List Parameter) →
    (es : List Grade) →
    γ.extendResults (Telescope.resultGrades ns es) ns ps =
      γ.extendGrades (fun l => es.getD l Grade.zero) (Telescope.nestResultParams ns ps)
  | γ, .direct _ :: ns, _ :: ps, e :: es =>
    extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ e) ns ps es
  | γ, .inst _ :: ns, _ :: ps, e :: es =>
    extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ e) ns ps es
  | γ, .direct _ :: ns, _ :: ps, [] => by
    have h := extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ Grade.zero) ns ps []
    rw [funext (Telescope.resultGrades_nil ns)] at h
    exact h
  | γ, .inst _ :: ns, _ :: ps, [] => by
    have h := extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ Grade.zero) ns ps []
    rw [funext (Telescope.resultGrades_nil ns)] at h
    exact h
  | γ, .plain :: ns, _ :: ps, es => extendResults_resultGrades γ ns ps es
  | _, [], _, _ | _, .plain :: _, [], _ | _, .direct _ :: _, [], _
  | _, .inst _ :: _, [], _ => rfl

-- ADE: none.
/-- `e_{l₁} + … + e_{l_b}`: the sum of the grades `e l` of the recursive results of the fields whose
nestings `ns` have a position, at their positions `l`, the first field at `0`. -/
def Telescope.resultSum (e : Nat → Grade) : List (Nest Name) → Grade
  | [] => Grade.zero
  | .direct _ :: ns => e 0 + Telescope.resultSum (fun l => e (l + 1)) ns
  | .inst _ :: ns => e 0 + Telescope.resultSum (fun l => e (l + 1)) ns
  | .plain :: ns => Telescope.resultSum (fun l => e (l + 1)) ns

end Sic.Core
