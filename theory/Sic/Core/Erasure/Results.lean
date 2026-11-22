module

public import Sic.Core.Shape.Results
import Sic.Core.Syntax.Signature

/-!
# Recursive Results of the Branches of the Target Language

The recursive results of the branches of a recursor of the target language of annex 19 of RFC 36,
`w`: what computes each recursive result of a branch, the recursor on a recursive field, the
corecursor of a lifting on a nested field, of the shape of annex 14 of the type of the field, or
nothing when the result is erased.

The erasure of a recursor reads them from the signature, `results_Σ(T, κ_C, r, ς, χ)`, where the
quality `s_C` of the sort `κ_C` of the motives, the grade `r` of the recursor and the requirement
`ς` of the lifted destructors are the variables of the lifting, and `χ` is the ownership of the
results that are motives: one for each field of each constructor of the block whose nesting has a
position, in order, as the typing binds one recursive result for each of these fields, the recursor
on a recursive field, and the corecursor of the lifting of the type of a nested field, of its shape
in the mode `11ᵐ` on the axis of the uses at run time, which the evaluation runs; a nested field
whose type has no shape, since the signature does not declare its lifting, has its result erased, in
a term that no rule types.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- `w`: the recursive result of a branch of a recursor of the target language: `erased`, the RFC's
`⊥`, when the result is erased, `field l` when it is the recursor on the recursive field `l`, and
`nested l σ` when it is the corecursor of a lifting, of the shape `σ`, on the nested field `l`; the
positions are counted from `0`, while the RFC counts them from `1`.
RFC: `\mathsf{syntax}_w` -/
inductive RecursiveResult where
  /-- `⊥`. -/
  | erased
  /-- `l`. -/
  | field (l : Nat)
  /-- `n.Ξ`. -/
  | nested (l : Nat) (σ : Shape)

/-- The position of the field on which a result recurses, by the recursor on the field itself or by
the recursors on its observations, if any. -/
def RecursiveResult.fieldPosition : RecursiveResult → Option Nat
  | .field l | .nested l _ => some l
  | .erased => none

/-- The factor of a result, the multiplicity by which it multiplies the uses of the scope by the
recursion that computes it: `0` when it is erased, `1` for the recursor itself, and the factor of the
shape of a nested result.
RFC: `\mathsf{factor}_w` -/
def RecursiveResult.factor : RecursiveResult → Multiplicity
  | .erased => .zero
  | .field _ => .one
  | .nested _ σ => σ.factor

/-! ## Recursive Results of a Block -/

/-- What computes the recursive result of the field at the position `l`, whose nesting has a
position: the recursor on the field itself when it is recursive, of the type `D` of the block that
`recursion` gives, the corecursor of the lifting of its type when its type has the shape `shape`,
and nothing otherwise, in a term that no rule types. -/
def RecursiveResult.ofField (recursion : Option Name) (shape : Option Shape) (l : Nat) :
    RecursiveResult :=
  match recursion, shape with
  | some _, _ => .field l
  | none, some σ => .nested l σ
  | none, none => .erased

/-- `w̄`: the recursive results of the fields of the constructor `con` at the instance `I`, in a
block whose types are named `names`, for a recursor of the variables `v` whose results that are
motives have the ownership `χ`, at the instance of the qualities `qs` and of the grades `ps`, in
the signature `sig`: one for each field whose nesting has a position, in order, what computes it,
the shapes of the nested fields read in the mode `11ᵐ` on the axis of the uses at run time. -/
def Constructor.recursiveResults {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) : List RecursiveResult :=
  ((con.fields I).nest names).zipIdx.filterMap fun y =>
    if y.1.isPlain then none
    else some (RecursiveResult.ofField ((con.fields I).recursionAt names y.2)
      (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[y.2]?.join y.2)

/-- The recursive results of the fields of each constructor of the block, in the order of the
cases, for a recursor of the variables `v` whose results that are motives have the ownership `χ`, at
the instance `I` of the qualities `qs` and of the grades `ps`, in the signature `sig`. -/
def TypeDeclaration.recursiveResults (decl : TypeDeclaration) (sig : Signature)
    (v : Lifting.Variables) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (I : Instance decl.sorts decl.grades) : List (List RecursiveResult) :=
  decl.cases.map fun x => x.2.2.recursiveResults sig v decl.names qs ps χ I

/-- The recursive results of the fields of each constructor of the block of the data type `D`, for a
recursor of the variables `v` whose results that are motives have the ownership `χ`, at the instance
of the qualities `qs` and of the grades `ps`, in the signature `sig`, when the entry declares
them. -/
def Entry.recursiveResults (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (χ : Grade) : Entry → Option (List (List RecursiveResult)) :=
  Entry.lookup D fun decl =>
    if hqp : decl.AsMany qs ps then
      (decl.dataTypes.find? (·.name == D)).map fun _ =>
        decl.recursiveResults sig v qs ps χ hqp.inst
    else none

/-- `results_Σ(T, κ_C, r, ς, χ)`: the recursive results `w̄̄` of the fields of each constructor of the
block of the data type `D`, in the order of the declaration, which is that of the branches of a
recursor, for a recursor of the variables `v`, which are the quality `s_C` of the sort `κ_C` of its
motives, its grade `r` and the requirement `ς` of the lifted destructors, whose results that are
motives have the ownership `χ`, at the instance of the qualities `qs` and of the grades `ps`, in the
last entry of the signature that declares the block, which the erasure of a recursor reads to tell
what computes each recursive result, and none when no entry declares it.
RFC: `\mathsf{results}_c` -/
def Signature.recursiveResults (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (χ : Grade) : List (List RecursiveResult) :=
  (sig.findSome? (Entry.recursiveResults sig D qs ps v χ)).getD []

/-! ## Properties -/

/-- An entry that does not introduce the name `D` gives the recursive results of no data type named
`D`. -/
theorem Entry.recursiveResults_of_not_mem {sig : Signature} {D : Name} {qs : List Quality}
    {ps : List Grade} {v : Lifting.Variables} {χ : Grade} :
    {e : Entry} → D ∉ e.names → Entry.recursiveResults sig D qs ps v χ e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the recursive results that the erasure reads are those
of the block of the data type, along the whole signature. -/
theorem Signature.Distinct.findSome?_recursiveResults {sig₀ : Signature} {v : Lifting.Variables}
    {χ : Grade} : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : decl.AsMany qs ps) →
    sig.findSome? (Entry.recursiveResults sig₀ D qs ps v χ) =
      some (decl.recursiveResults sig₀ v qs ps χ hqp.inst)
  | [], _, _, _, _, h, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp => by
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : Entry.recursiveResults sig₀ D qs ps v χ (.typeDeclaration decl) =
          some (decl.recursiveResults sig₀ v qs ps χ hqp.inst) := by
        simp only [Entry.recursiveResults,
          Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT), hqp, ↓reduceDIte,
          ← hD, List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.recursiveResults_of_not_mem hDe]; rfl)]
      exact hd.findSome?_recursiveResults ⟨he', hT, hD⟩ hqp

/-- In a signature whose names are distinct, the recursive results that the erasure of a recursor
reads are those of the block of its data type, at the instance. -/
theorem Signature.Distinct.recursiveResults {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl : TypeDeclaration} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ps : List Grade}
    (hqp : decl.AsMany qs ps) (v : Lifting.Variables)
    (χ : Grade) :
    sig.recursiveResults D qs ps v χ =
      decl.recursiveResults sig v qs ps χ hqp.inst := by
  rw [Signature.recursiveResults, hd.findSome?_recursiveResults h hqp, Option.getD_some]

/-- The recursive results of the fields of the constructor `con` are the results of the fields that
have one, at their positions, in order. -/
theorem Constructor.recursiveResults_eq_map {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) :
    con.recursiveResults sig v names qs ps χ I =
      (Telescope.nestPositions ((con.fields I).nest names) 0).map fun l =>
        RecursiveResult.ofField ((con.fields I).recursionAt names l)
          (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join l :=
  Telescope.filterMap_eq_map_nestPositions (fun l => RecursiveResult.ofField
    ((con.fields I).recursionAt names l)
    (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join l) _ 0

/-! ## Alignment With the Recursive Results of the Typing -/

/-- The constructor `con` has one recursive result in the erasure for each recursive result that
the typing binds in its branch, so that the `j`-th results of both are those of the same field. -/
theorem Constructor.length_recursiveResults {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) :
    (con.recursiveResults sig v names qs ps χ I).length = (con.nestResultParams I names).length := by
  rw [Constructor.recursiveResults_eq_map, List.length_map]
  exact Telescope.length_nestPositions _ _ (Telescope.length_nest names (con.fields I)) 0

/-- The `j`-th recursive result of the constructor `con` in the erasure is the one of the `j`-th of
its fields whose nesting has a position, which the typing binds the `j`-th result of its branch:
the recursor on the field when it is recursive, the corecursor of the shape of its type when the
type has one, and `⊥` otherwise. -/
theorem Constructor.getElem?_recursiveResults {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) (i : Nat) :
    (con.recursiveResults sig v names qs ps χ I)[i]? =
      ((Telescope.nestPositions ((con.fields I).nest names) 0)[i]?).map fun l =>
        RecursiveResult.ofField ((con.fields I).recursionAt names l)
          (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join l := by
  rw [Constructor.recursiveResults_eq_map, List.getElem?_map]

/-- The recursive result of a field is the recursor on this field exactly when the field is
recursive. -/
theorem RecursiveResult.ofField_eq_field {r : Option Name} {s : Option Shape} {l l' : Nat} :
    RecursiveResult.ofField r s l = .field l' ↔ l' = l ∧ r.isSome := by
  cases r <;> cases s <;> simp [RecursiveResult.ofField, eq_comm]

/-- The recursive result of a field is erased exactly when the field is not recursive and its type
has no shape. -/
theorem RecursiveResult.ofField_eq_erased {r : Option Name} {s : Option Shape} {l : Nat} :
    RecursiveResult.ofField r s l = .erased ↔ r = none ∧ s = none := by
  cases r <;> cases s <;> simp [RecursiveResult.ofField]

/-- The recursive result of a field is nested on this field, at the shape `σ`, exactly when the
field is not recursive and its type has the shape `σ`. -/
theorem RecursiveResult.ofField_eq_nested {r : Option Name} {s : Option Shape} {l l' : Nat}
    {σ : Shape} : RecursiveResult.ofField r s l = .nested l' σ ↔ l' = l ∧ r = none ∧ s = some σ := by
  cases r <;> cases s <;> simp [RecursiveResult.ofField, eq_comm]

/-- The recursive result of the `j`-th field of the constructor `con` whose nesting has a
position, the field `l`, is the corecursor of the shape `σ` exactly when the field is not recursive
and the shape of its nested result is `σ`. -/
theorem Constructor.recursiveResults_eq_nested {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {v : Lifting.Variables} {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g} {i l : Nat}
    (hl : (Telescope.nestPositions ((con.fields I).nest names) 0)[i]? = some l) (σ : Shape) :
    (con.recursiveResults sig v names qs ps χ I)[i]? = some (.nested l σ) ↔
      (con.fields I).recursionAt names l = none ∧
        (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]? = some (some σ) := by
  rw [Constructor.getElem?_recursiveResults, hl, Option.map_some, Option.some.injEq,
    RecursiveResult.ofField_eq_nested, Option.join_eq_some_iff]
  simp

/-- A recursive result of the constructor `con` that is the corecursor of the shape `σ` on the field
`l` is that of a field at the nesting of an instance, a nested field, whose nested result has the
shape `σ`. -/
theorem Constructor.inst_of_recursiveResults_eq_nested {j g k' : Nat} {Δ : Scope}
    {sig : Signature} {v : Lifting.Variables} {names : List Name} {qs : List Quality}
    {ps : List Grade} {χ : Grade} {con : Constructor j g k' Δ} {I : Instance j g} {i l : Nat}
    {σ : Shape} (h : (con.recursiveResults sig v names qs ps χ I)[i]? = some (.nested l σ)) :
    (∃ ms, ((con.fields I).nest names)[l]? = some (.inst ms)) ∧
      (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]? = some (some σ) := by
  rw [Constructor.getElem?_recursiveResults] at h
  obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hr, hs⟩ := RecursiveResult.ofField_eq_nested.1 he
  refine ⟨?_, Option.join_eq_some_iff.1 hs⟩
  obtain ⟨n, hn, hp⟩ := Telescope.mem_nestPositions.1
    ((Nat.zero_add l).symm ▸ List.mem_of_getElem? hl' : 0 + l ∈ _)
  rw [Telescope.recursionAt, Telescope.recursion_eq_map_nest, List.getElem?_map, hn] at hr
  cases n with
  | plain => cases hp
  | direct _ => cases hr
  | inst ms => exact ⟨ms, hn⟩

end Sic.Core
