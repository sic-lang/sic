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

/-! ## Shapes of the Nested Fields -/

mutual

-- ADE: none.
/-- The observations of a field keep the ownership `o · R` of the term, when the shape meets the
requirements of the observations at it and `R`, not `0`, is below `ϱ · y · π` for the product `y`
along each prefix of the paths after a prefix of the product `a`: the product along the prefix that
a destructor observed ends is `a` times the value `w` of the ownership of its result at the least
ownerships of its arguments, so that `R ≤ R · w`, and the value at any ownerships that meet these
is above `w`. -/
theorem Shape.keeps_of_prefixes {ς R o ϱ π : Multiplicity} (hR : R ≠ .zero) :
    (σ : Shape) → (a : Multiplicity) → σ.Meets (o * R) ς →
      (∀ y ∈ σ.prefixes ς a, R ≤ ϱ * y * π) → σ.Keeps (o * R) ς
  | .nil, _, _, _ => trivial
  | .cons _ c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ _ next rest, a, ⟨hm, hmr⟩, hy => by
    have hyr : ∀ y ∈ rest.prefixes ς a, R ≤ ϱ * y * π := fun y h => hy y (by
      simp only [Shape.prefixes]
      exact List.mem_append_right _ h)
    refine ⟨fun hρ => ?_, Shape.keeps_of_prefixes hR rest a hmr hyr⟩
    obtain ⟨_, hargs, hmn⟩ := hm hρ
    obtain ⟨-, w, hw⟩ := hargs ϱs' fun k => (by decide : ∀ x : Multiplicity, x ≤ x) _
    have hy' : ∀ y ∈ (a * w) :: next.prefixes ς (a * w), R ≤ ϱ * y * π := fun y h => hy y (by
      simp only [Shape.prefixes, hρ, ↓reduceIte, hw, Option.getD_some]
      exact List.mem_append_left _ h)
    have hRw : R ≤ R * w :=
      (by decide : ∀ r ϱ a w π : Multiplicity, r ≠ .zero → r ≤ ϱ * (a * w) * π → r ≤ r * w)
        _ _ _ _ _ hR (hy' _ List.mem_cons_self)
    refine ⟨fun os hos v hv => ?_, Shape.Next.keeps_of_prefixes hR next (a * w) hmn
      fun y h => hy' y (List.mem_cons_of_mem _ h)⟩
    have hmono := ResultOwnership.value_mono ψ₀
      (Shape.argOwnerships (next.scale ς) ϱs' πs ϱs πs')
      (Shape.argOwnerships (next.scale ς) os πs ϱs πs') fun k => by
        unfold Shape.argOwnerships
        split
        · exact (by decide : ∀ x : Multiplicity, x ≤ x) _
        · exact (by decide : ∀ s x y q : Multiplicity, x ≤ y → s * (x * q) ≤ s * (y * q))
            _ _ _ _ (hos k)
    rw [hw, hv] at hmono
    cases hmono with
    | some hwv =>
      exact (by decide : ∀ o R w v : Multiplicity, R ≤ R * w → w ≤ v → o * R ≤ o * R * v)
        _ _ _ _ hRw hwv

-- ADE: none.
/-- The observations from the shape of a result keep the ownership `o · R` of the term in the same
conditions: the recursor itself asks nothing, and the next lifting as a shape does. -/
theorem Shape.Next.keeps_of_prefixes {ς R o ϱ π : Multiplicity} (hR : R ≠ .zero) :
    (next : Shape.Next) → (a : Multiplicity) → next.Meets (o * R) ς →
      (∀ y ∈ next.prefixes ς a, R ≤ ϱ * y * π) → next.Keeps (o * R) ς
  | .recursor _, _, _, _ => trivial
  | .lifting σ, a, hm, hy => Shape.keeps_of_prefixes hR σ a hm hy

end

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
