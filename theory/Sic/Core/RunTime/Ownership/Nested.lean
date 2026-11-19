module

public import Sic.Core.Erasure
import Sic.Core.Syntax.Signature

/-!
# Ownership of the Nested Fields at Run Time

What the rule of the recursor of annex 13 of RFC 36 gives the ownership of the corecursor of a
nested result at run time, which the erasure of a recursor whose branches have nested results will
read: in the mode `11ᵐ`, on the axis of the uses at run time, the variable of a nested field used at
run time, seen at the requirement `ς` of the corecursors, keeps the ownership of the term of the
recursor times the requirement `r̂` of its recursion, since `r̂` reads the empty prefix of the paths
of the field, and its shape, which meets the requirements of its observations at this ownership,
meets the requirements of the recursions there, since `r̂` reads every prefix of the paths of the
destructors observed and the value of the ownership of a result is monotone in its arguments.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- In the mode `11ᵐ`, on the axis of the uses at run time, the variable of a nested field that the
recursor uses at run time, of the coefficient `κ_l` that the erasure gives it, seen at the
requirement `ς` of the corecursors, keeps the ownership `o · r̂` of the term of each level of the
recursion: `r̂` is below the requirement of the field times `ς` times the grade with which the
recursor uses the field, the pair of the empty prefix of the paths of its shape. -/
theorem Ownership.nestedField_keeps {sig : Signature} {decl : TypeDeclaration}
    {v : Lifting.Variables} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) {l : Nat} {σ : Shape} {p : Parameter}
    (hσ : (con.nestedShapes sig v .oneOne Grade.run decl.names qs ps χ I)[l]? = some (some σ))
    (hp : (con.params I)[l]? = some p) (hc : (v.recursion * p.usage).run ≠ .zero) (o : Grade) :
    (o * decl.recursionRequirement sig v .oneOne χ qs ps I).run ≤
      v.requirement.run * ((o * decl.recursionRequirement sig v .oneOne χ qs ps I).run *
        v.recursion.fieldCoefficient (some p)) := by
  have h1 : ∀ x : Multiplicity, Multiplicity.one * x = x := by decide
  have hc' : (Mode.oneOne.grade * v.recursion * p.usage).run ≠ .zero := by
    show Multiplicity.one * v.recursion.run * p.usage.run ≠ .zero
    rw [h1]
    exact hc
  have hR := TypeDeclaration.recursionRequirement_run_le_nested hi hσ hp hc' List.mem_cons_self
  have hne := TypeDeclaration.recursionRequirement_run_ne_zero (decl := decl) (sig := sig) (v := v)
    (m := .oneOne) (χ := χ) (qs := qs) (ps := ps) (I := I)
  show o.run * _ ≤ v.requirement.run * (o.run * _ * (p.requirement.run * (v.recursion.run *
    p.usage.run)))
  change _ ≤ _ * (Multiplicity.one * v.recursion.run * p.usage.run) at hR
  rw [h1] at hR
  have key : ∀ o R a s b c : Multiplicity, R ≠ .zero → R ≤ a * s * (b * c) →
      o * R ≤ s * (o * R * (a * (b * c))) := by decide
  exact key _ _ _ _ _ _ hne (by simpa only [Multiplicity.modality.semiring.mul_assoc] using hR)

-- ADE: none.
/-- In the mode `11ᵐ`, on the axis of the uses at run time, the shape of a nested field that the
recursor uses at run time, which meets the requirements of its observations at the ownership
`o · r̂` of the term of each level of the recursion, meets the requirements of the recursions there:
`r̂` is below the requirement of the field times the product along each prefix of the paths of the
destructors observed times the grade with which the recursor uses the field, so that each
observation keeps `o · r̂`. -/
theorem Ownership.nestedField_requires {sig : Signature} {decl : TypeDeclaration}
    {v : Lifting.Variables} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) {l : Nat} {σ : Shape} {p : Parameter}
    (hσ : (con.nestedShapes sig v .oneOne Grade.run decl.names qs ps χ I)[l]? = some (some σ))
    (hp : (con.params I)[l]? = some p) (hc : (v.recursion * p.usage).run ≠ .zero) (o : Grade)
    (hmeets : σ.Meets (o * decl.recursionRequirement sig v .oneOne χ qs ps I).run
      v.requirement.run) :
    σ.Requires (o * decl.recursionRequirement sig v .oneOne χ qs ps I).run v.requirement.run := by
  have h1 : ∀ x : Multiplicity, Multiplicity.one * x = x := by decide
  have hc' : (Mode.oneOne.grade * v.recursion * p.usage).run ≠ .zero := by
    show Multiplicity.one * v.recursion.run * p.usage.run ≠ .zero
    rw [h1]
    exact hc
  exact ⟨hmeets, Shape.keeps_of_prefixes (ϱ := p.requirement.run)
    (π := (Mode.oneOne.grade * v.recursion * p.usage).run)
    TypeDeclaration.recursionRequirement_run_ne_zero σ v.requirement.run hmeets
    fun _ hy => TypeDeclaration.recursionRequirement_run_le_nested hi hσ hp hc'
      (List.mem_cons_of_mem _ hy)⟩

end Sic.Core
