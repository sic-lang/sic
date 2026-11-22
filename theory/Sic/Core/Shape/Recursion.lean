module

public import Sic.Core.Shape.Ownership
public import Sic.Core.Shape.Results
import Sic.Core.Syntax.Signature

/-!
# Requirement of the Recursion

The requirement `r̂` of the recursion of a recursor of annex 18 of RFC 36, `(recursion_p)`, on a
block of data types: on each axis of the grades, the meet of `11ᵖ`, of the coefficient of each
recursive field, and of the pairs that each nested field gives along the paths of its shape, read in
the mode of the recursor and on the axis, so that every value that a recursion observes keeps the
ownership of the term of the recursor times `r̂`, which every level of the recursion has.
The ownership of the source reads it in the mode of the recursor, and the erasure, which keeps it at
run time, in the mode `11ᵐ`, from the entry of the signature that declares the block.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The pairs `c_l ◀ r_l · ς · ψ₁⁻ · … · ψ_h⁻` that the nested fields of the cases of the block give
the requirement of the recursion on the axis `ax`, for a recursor of the variables `v`, checked in
the mode `m`, whose results that are motives have the ownership `χ`, at the instance `I` of the
qualities `qs` and of the grades `ps`: for each nested field of the requirement `r_l`, used with the
grade `c_l = ⌜m⌝ · r · q_l`, the pair of each product that its shape on the axis gives, on the
axis. -/
def TypeDeclaration.nestedPairs (decl : TypeDeclaration) (sig : Signature) (v : Lifting.Variables)
    (m : Mode) (χ : Grade) (qs : List Quality) (ps : List Grade)
    (I : Instance decl.sorts decl.grades) (ax : Grade → Multiplicity) :
    List (Multiplicity × Multiplicity) :=
  (decl.cases.map fun x =>
    ((x.2.2.nestedShapes sig v m ax decl.names qs ps χ I).zip (x.2.2.params I)).flatMap fun
      | (some σ, p) => (σ.recursion (ax v.requirement)).map fun y =>
          (ax p.requirement * y, ax ((m.grade * v.recursion) * p.usage))
      | (none, _) => []).flatten

/-- The nested fields of the constructors of the block have shapes on the two axes of the grades,
for a recursor of the variables `v`, checked in the mode `m`, whose results that are motives have
the ownership `χ`, at the instance `I` of the qualities `qs` and of the grades `ps`: each lifting
that the requirement of the recursion reads is declared, so that it reads the same shapes in a
signature that has more entries before theirs, all of distinct names. -/
def TypeDeclaration.NestedHaveShapes (decl : TypeDeclaration) (sig : Signature)
    (v : Lifting.Variables) (m : Mode) (χ : Grade) (qs : List Quality) (ps : List Grade)
    (I : Instance decl.sorts decl.grades) : Prop :=
  ∀ (i j : Nat) (T : DataType decl.sorts decl.grades decl.levels decl.scope)
    (con : Constructor decl.sorts decl.grades decl.levels decl.scope),
    decl.cases[i]? = some (j, T, con) → ∀ ax ∈ [Grade.run, Grade.total],
      con.NestedHaveShapes sig v m ax decl.names qs ps χ I

/-- `recursion_Σ;m(𝒟.{s̄'; p̄'}; s_C, r, ς, χ)`: the requirement `r̂` of the recursion of a recursor
checked in the mode `m`, of the variables `v`, the quality `s_C` of the sorts of its motives, its
grade `r` and the requirement `ς` of the lifted destructors, whose results that are motives have
the ownership `χ`, on the block at the instance `I` of the qualities `qs` and of the grades `ps`, in
the signature `sig`: its term is used with the grade `⌜m⌝ · r`, and its nested fields give their
pairs on each axis `β`.
RFC: `\mathsf{recursion}_{\mathcal{D}}` -/
def TypeDeclaration.recursionRequirement (decl : TypeDeclaration) (sig : Signature)
    (v : Lifting.Variables) (m : Mode) (χ : Grade) (qs : List Quality) (ps : List Grade)
    (I : Instance decl.sorts decl.grades) : Grade :=
  Parameter.recursion (m.grade * v.recursion) (decl.recursivePositions I)
    (decl.cases.map fun x => x.2.2.params I) (decl.nestedPairs sig v m χ qs ps I)

/-- The requirement of the recursion of a recursor of the variables `v`, checked in the mode `11ᵐ`,
whose results that are motives have the ownership `χ`, on the block of the data type `D`, at the
instance of the qualities `qs` and of the grades `ps`, in the signature `sig`, when the entry
declares it. -/
def Entry.recursionRequirement (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (χ : Grade) : Entry → Option Grade :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.dataTypes.find? (·.name == D)).map fun _ =>
        decl.recursionRequirement sig v .oneOne χ qs ps hqp.inst
    else none

/-- `recursion_Σ(T, r)`: the requirement `r̂` of the recursion of a recursor of the variables `v`,
whose results that are motives have the ownership `χ`, on the block of the data type `D`, at the
instance of the qualities `qs` and of the grades `ps`, in the mode `11ᵐ`, read from the last entry
of the signature that declares the block, which the erasure of the recursor keeps at run time, and
`11ᵖ`, which states nothing more than the term, when no entry declares it.
RFC: `\mathsf{recursion}_c` -/
def Signature.recursionRequirement (sig : Signature) (D : Name) (qs : List Quality)
    (ps : List Grade) (v : Lifting.Variables) (χ : Grade) : Grade :=
  (sig.findSome? (Entry.recursionRequirement sig D qs ps v χ)).getD .linearLinear

/-! ## Properties -/

/-- The requirement of the recursion of a recursor on a block is below, at run time, the coefficient
of each recursive field of each of its constructors that the recursor uses at run time, at each
instance. -/
theorem TypeDeclaration.recursionRequirement_run_le {decl : TypeDeclaration} {sig : Signature}
    {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) {l : Nat}
    (hl : l ∈ ((con.fields I).recursion decl.names).zipIdx.filterMap (fun y => y.1.map fun _ => y.2))
    {p : Parameter} (hp : (con.params I)[l]? = some p)
    (hc : ((m.grade * v.recursion) * p.usage).run ≠ .zero) :
    (decl.recursionRequirement sig v m χ qs ps I).run ≤
      p.requirement.run * ((m.grade * v.recursion) * p.usage).run :=
  Parameter.recursion_run_le (by rw [TypeDeclaration.recursivePositions, List.getElem?_map, hi]; rfl)
    (by rw [List.getElem?_map, hi]; rfl) hl hp hc

/-- An entry that does not introduce the name `D` gives the requirement of the recursion on the
block of no data type named `D`. -/
theorem Entry.recursionRequirement_of_not_mem {sig : Signature} {D : Name} {qs : List Quality}
    {ps : List Grade} {v : Lifting.Variables} {χ : Grade} :
    {e : Entry} → D ∉ e.names → Entry.recursionRequirement sig D qs ps v χ e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the requirement of the recursion that the erasure
reads is the one of the block of the data type, in the mode `11ᵐ`, along the whole signature. -/
theorem Signature.Distinct.recursionRequirement {sig₀ : Signature} {v : Lifting.Variables}
    {χ : Grade} : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.findSome? (Entry.recursionRequirement sig₀ D qs ps v χ) =
      some (decl.recursionRequirement sig₀ v .oneOne χ qs ps hqp.inst) := by
    intro _ hd _ _ _ ⟨hm, hT, hD⟩ _ _ hqp
    subst hD
    refine (hd.findSome?_lookup hm (TypeDeclaration.name_mem_names hT)).trans ?_
    simp only [hqp, ↓reduceDIte,
      List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hm)) hT, Option.map_some]

/-- In a signature whose names are distinct, the requirement of the recursion that the erasure of a
recursor reads is the one of the block of its data type, in the mode `11ᵐ`. -/
theorem Signature.Distinct.recursionRequirement_eq {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl : TypeDeclaration} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) (v : Lifting.Variables)
    (χ : Grade) :
    sig.recursionRequirement D qs ps v χ =
      decl.recursionRequirement sig v .oneOne χ qs ps hqp.inst := by
  rw [Signature.recursionRequirement, hd.recursionRequirement h hqp, Option.getD_some]

/-- Each product along a prefix of a path of the shape of a nested field gives the requirement of
the recursion a pair, of the requirement of the field times the product and of the grade with which
the recursor uses the field. -/
theorem TypeDeclaration.mem_nestedPairs {decl : TypeDeclaration} {sig : Signature}
    {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} {ax : Grade → Multiplicity} {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) {l : Nat} {σ : Shape} {p : Parameter}
    (hσ : (con.nestedShapes sig v m ax decl.names qs ps χ I)[l]? = some (some σ))
    (hp : (con.params I)[l]? = some p) {y : Multiplicity} (hy : y ∈ σ.recursion (ax v.requirement)) :
    (ax p.requirement * y, ax ((m.grade * v.recursion) * p.usage)) ∈
      decl.nestedPairs sig v m χ qs ps I ax := by
  unfold TypeDeclaration.nestedPairs
  refine List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨(j, T, con), List.mem_of_getElem? hi, rfl⟩, ?_⟩
  refine List.mem_flatMap.2 ⟨(some σ, p), List.mem_of_getElem? (i := l) ?_, ?_⟩
  · rw [List.getElem?_zip_eq_some]
    exact ⟨hσ, hp⟩
  · exact List.mem_map.2 ⟨y, hy, rfl⟩

/-- The requirement of the recursion of a recursor is never `0` at run time. -/
theorem TypeDeclaration.recursionRequirement_run_ne_zero {decl : TypeDeclaration}
    {sig : Signature} {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality}
    {ps : List Grade} {I : Instance decl.sorts decl.grades} :
    (decl.recursionRequirement sig v m χ qs ps I).run ≠ .zero :=
  Parameter.recursionAxis_ne_zero _

/-- The requirement of the recursion of a recursor on a block is below, at run time, the requirement
of each nested field that the recursor uses at run time times the product along each prefix of the
paths of its shape times the grade with which the recursor uses the field, at each instance. -/
theorem TypeDeclaration.recursionRequirement_run_le_nested {decl : TypeDeclaration}
    {sig : Signature} {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality}
    {ps : List Grade} {I : Instance decl.sorts decl.grades} {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) {l : Nat} {σ : Shape} {p : Parameter}
    (hσ : (con.nestedShapes sig v m Grade.run decl.names qs ps χ I)[l]? = some (some σ))
    (hp : (con.params I)[l]? = some p) (hc : ((m.grade * v.recursion) * p.usage).run ≠ .zero)
    {y : Multiplicity} (hy : y ∈ σ.recursion v.requirement.run) :
    (decl.recursionRequirement sig v m χ qs ps I).run ≤
      (p.requirement.run * y) * ((m.grade * v.recursion) * p.usage).run :=
  Parameter.recursionAxis_le hc
    (List.mem_append_right _ (TypeDeclaration.mem_nestedPairs hi hσ hp hy))

end Sic.Core
