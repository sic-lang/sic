module

public import Sic.Core.Shape.Results
import Sic.Core.Syntax.Signature

/-!
# Recursive Results of the Branches of the Target Language

The recursive results of the branches of a recursor of the target language of annex 19 of RFC 36,
`w`: what computes each recursive result of a branch, the recursor on a recursive field, the
corecursor of a lifting on a nested field, of the shape of annex 14 of the type of the field, or
nothing when the result is erased.

The erasure of a recursor reads them from the signature, `results_Σ(T, r, ς, χ)`: one for each
field of each constructor of the block whose nesting has a position, in order, as the typing binds
one recursive result for each of these fields, the recursor on a recursive field, and the
corecursor of the lifting of the type of a nested field, of its shape in the mode `11ᵐ` on the axis
of the uses at run time, which the evaluation runs; a nested field whose type has no shape, since
the signature does not declare its lifting, has its result erased, in a term that no rule types.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
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

-- ADE: none.
/-- The result at the position `l` of a field, or erased when there is none: a recursive result
that the evaluation computes by the recursor. -/
def RecursiveResult.ofPosition : Option Nat → RecursiveResult
  | none => .erased
  | some l => .field l

-- ADE: none.
/-- The position of the field of a result that the recursor computes, if any: a nested result, which
the evaluation does not compute by the recursor, has none. -/
def RecursiveResult.position : RecursiveResult → Option Nat
  | .field l => some l
  | .erased | .nested .. => none

-- ADE: none.
/-- The position of the field on which a result recurses, by the recursor on the field itself or by
the recursors on its observations, if any. -/
def RecursiveResult.fieldPosition : RecursiveResult → Option Nat
  | .field l | .nested l _ => some l
  | .erased => none

-- ADE: none.
/-- The result is the corecursor of a lifting, on a nested field. -/
def RecursiveResult.IsNested : RecursiveResult → Prop
  | .nested .. => True
  | .erased | .field _ => False

-- ADE: none.
/-- The factor of a result, the multiplicity by which it multiplies the uses of the scope by the
recursion that computes it: `0` when it is erased, `1` for the recursor itself, and the factor of the
shape of a nested result.
RFC: `\mathsf{factor}_w` -/
def RecursiveResult.factor : RecursiveResult → Multiplicity
  | .erased => .zero
  | .field _ => .one
  | .nested _ σ => σ.factor

/-- A result that is not nested multiplies the uses by its multiplicity when the recursor computes it,
and by `0` when it does not. -/
theorem RecursiveResult.mul_factor {r : RecursiveResult} (h : ¬ r.IsNested) (π : Multiplicity) :
    π * r.factor = if r.position.isSome then π else .zero := by
  cases r with
  | erased => cases π <;> rfl
  | field _ => cases π <;> rfl
  | nested _ _ => exact absurd trivial h

/-- The result of a position is not nested. -/
theorem RecursiveResult.not_isNested_ofPosition (o : Option Nat) :
    ¬ (RecursiveResult.ofPosition o).IsNested := by
  cases o <;> exact id

/-- An erased result has no position. -/
@[simp]
theorem RecursiveResult.position_erased : RecursiveResult.erased.position = none := rfl

/-- A result of a position has this position. -/
@[simp]
theorem RecursiveResult.position_ofPosition (o : Option Nat) :
    (RecursiveResult.ofPosition o).position = o := by
  cases o <;> rfl

/-! ## Recursive Results of a Block -/

-- ADE: none.
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

-- ADE: none.
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

-- ADE: none.
/-- The recursive results of the fields of each constructor of the block, in the order of the
cases, for a recursor of the variables `v` whose results that are motives have the ownership `χ`, at
the instance `I` of the qualities `qs` and of the grades `ps`, in the signature `sig`. -/
def TypeDeclaration.recursiveResults (decl : TypeDeclaration) (sig : Signature)
    (v : Lifting.Variables) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (I : Instance decl.sorts decl.grades) : List (List RecursiveResult) :=
  decl.cases.map fun x => x.2.2.recursiveResults sig v decl.names qs ps χ I

-- ADE: none.
/-- The recursive results of the fields of each constructor of the block of the data type `D`, for a
recursor of the variables `v` whose results that are motives have the ownership `χ`, at the instance
of the qualities `qs` and of the grades `ps`, in the signature `sig`, when the entry declares
them. -/
def Entry.recursiveResults (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (χ : Grade) : Entry → Option (List (List RecursiveResult))
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.dataTypes.find? (·.name == D)).map fun _ =>
          decl.recursiveResults sig v qs ps χ (.ofLists qs ps hq hp)
      else none
    else none
  | _ => none

-- ADE: none.
/-- `results_Σ(T, r, ς, χ)`: the recursive results `w̄̄` of the fields of each constructor of the
block of the data type `D`, in the order of the declaration, which is that of the branches of a
recursor, for a recursor of the variables `v`, its grade `r` and the requirement `ς` of the lifted
destructors, whose results that are motives have the ownership `χ`, at the instance of the qualities
`qs` and of the grades `ps`, in the last entry of the signature that declares the block, which the
erasure of a recursor reads to tell what computes each recursive result, and none when no entry
declares it. -/
def Signature.recursiveResults (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (χ : Grade) : List (List RecursiveResult) :=
  (sig.findSome? (Entry.recursiveResults sig D qs ps v χ)).getD []

/-! ## Properties -/

-- ADE: none.
/-- An entry that does not introduce the name `D` gives the recursive results of no data type named
`D`. -/
theorem Entry.recursiveResults_of_not_mem {sig : Signature} {D : Name} {qs : List Quality}
    {ps : List Grade} {v : Lifting.Variables} {χ : Grade} :
    {e : Entry} → D ∉ e.names → Entry.recursiveResults sig D qs ps v χ e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.dataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.name_mem_names hT)
    simp only [Entry.recursiveResults]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.map_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

-- ADE: none.
/-- In a signature whose names are distinct, the recursive results that the erasure reads are those
of the block of the data type, along the whole signature. -/
theorem Signature.Distinct.findSome?_recursiveResults {sig₀ : Signature} {v : Lifting.Variables}
    {χ : Grade} : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.findSome? (Entry.recursiveResults sig₀ D qs ps v χ) =
      some (decl.recursiveResults sig₀ v qs ps χ (.ofLists qs ps hq hp))
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : Entry.recursiveResults sig₀ D qs ps v χ (.typeDeclaration decl) =
          some (decl.recursiveResults sig₀ v qs ps χ (.ofLists qs ps hq hp)) := by
        simp only [Entry.recursiveResults, hq, hp, ↓reduceDIte, ← hD,
          List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.recursiveResults_of_not_mem hDe]; rfl)]
      exact hd.findSome?_recursiveResults ⟨he', hT, hD⟩ hq hp

-- ADE: none.
/-- In a signature whose names are distinct, the recursive results that the erasure of a recursor
reads are those of the block of its data type, at the instance. -/
theorem Signature.Distinct.recursiveResults {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl : TypeDeclaration} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades) (v : Lifting.Variables)
    (χ : Grade) :
    sig.recursiveResults D qs ps v χ =
      decl.recursiveResults sig v qs ps χ (.ofLists qs ps hq hp) := by
  rw [Signature.recursiveResults, hd.findSome?_recursiveResults h hq hp, Option.getD_some]

/-- The recursive results of fields none of which is nested, whose nestings are `ns`, from the
position `o`, are the recursors on their recursive fields, at their positions, when `f` gives a
type of the block for each recursive field. -/
theorem RecursiveResult.filterMap_ofField {f : Nat → Option Name} {s : Nat → Option Shape} :
    (ns : List (Nest Name)) → (o : Nat) → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
    (∀ i (D : Name), ns[i]? = some (.direct D) → (f (o + i)).isSome) →
    (ns.zipIdx o).filterMap (fun y => if y.1.isPlain then none
      else some (RecursiveResult.ofField (f y.2) (s y.2) y.2)) =
      (((ns.map Nest.blockName).zipIdx o).filterMap fun y => y.1.map fun _ => y.2).map .field
  | [], _, _, _ => rfl
  | .inst ms :: _, _, hn, _ => absurd rfl (hn _ List.mem_cons_self ms)
  | .plain :: ns, o, hn, hf => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Nest.isPlain, ↓reduceIte, List.map_cons,
      Nest.blockName, Option.map_none]
    exact RecursiveResult.filterMap_ofField ns (o + 1)
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))
      (fun i D h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D h)
  | .direct D :: ns, o, hn, hf => by
    obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.1 (hf 0 D rfl)
    rw [Nat.add_zero] at hD'
    rw [List.zipIdx_cons, List.filterMap_cons, List.map_cons, List.zipIdx_cons,
      List.filterMap_cons, RecursiveResult.filterMap_ofField ns (o + 1)
        (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))
        (fun i D h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D h)]
    simp only [Nest.isPlain, Bool.false_eq_true, ↓reduceIte, Nest.blockName, Option.map_some,
      RecursiveResult.ofField, hD', List.map_cons]

-- ADE: none.
/-- The recursive results of the fields of a constructor none of which is nested are the recursors
on its recursive fields, at their positions: a block without nested field has no other results. -/
theorem Constructor.recursiveResults_of_not_nested {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {v : Lifting.Variables} {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g}
    (hn : ∀ ν ∈ (con.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    con.recursiveResults sig v names qs ps χ I =
      (((con.fields I).recursion names).zipIdx.filterMap fun y => y.1.map fun _ => y.2).map
        .field := by
  rw [Constructor.recursiveResults, Telescope.recursion_eq_map_nest]
  refine RecursiveResult.filterMap_ofField (f := (con.fields I).recursionAt names)
    (s := fun l => (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join) _ 0 hn
    fun i D h => ?_
  rw [Nat.zero_add, Telescope.recursionAt, Telescope.recursion_eq_map_nest, List.getElem?_map, h]
  rfl

-- ADE: none.
/-- The recursive results of the fields of a block none of whose constructors has a nested field
are the recursors on their recursive fields, at their positions. -/
theorem TypeDeclaration.recursiveResults_of_not_nested {decl : TypeDeclaration} {sig : Signature}
    {v : Lifting.Variables} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades}
    (hn : ∀ (i : Nat) j T con, decl.cases[i]? = some (j, T, con) →
      ∀ ν ∈ (con.fields I).nest decl.names, ∀ ms, ν ≠ .inst ms) :
    decl.recursiveResults sig v qs ps χ I =
      (decl.recursivePositions I).map (·.map .field) := by
  rw [TypeDeclaration.recursiveResults, TypeDeclaration.recursivePositions, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  exact Constructor.recursiveResults_of_not_nested (hn i x.1 x.2.1 x.2.2 hi)

/-! ## Alignment With the Recursive Results of the Typing -/

/-- The fields whose nestings `ns` have a position, from the position `o`, are as many as the
recursive results that the typing binds for fields of the parameters `ps`. -/
theorem Telescope.length_filterMap_nest {β : Type} (f : Nat → β) :
    (ns : List (Nest Name)) → (ps : List Parameter) → ns.length = ps.length → (o : Nat) →
      ((ns.zipIdx o).filterMap fun y => if y.1.isPlain then none else some (f y.2)).length =
        (Telescope.nestResultParams ns ps).length
  | [], [], _, _ => rfl
  | .plain :: ns, _ :: ps, h, o => Telescope.length_filterMap_nest f ns ps (Nat.succ.inj h) (o + 1)
  | .direct _ :: ns, _ :: ps, h, o | .inst _ :: ns, _ :: ps, h, o =>
    congrArg (· + 1) (Telescope.length_filterMap_nest f ns ps (Nat.succ.inj h) (o + 1))

-- ADE: none.
/-- The constructor `con` has one recursive result in the erasure for each recursive result that
the typing binds in its branch, so that the `j`-th results of both are those of the same field. -/
theorem Constructor.length_recursiveResults {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) :
    (con.recursiveResults sig v names qs ps χ I).length = (con.nestResultParams I names).length :=
  Telescope.length_filterMap_nest (fun l => RecursiveResult.ofField
    ((con.fields I).recursionAt names l)
    (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join l) _ _
    (Telescope.length_nest names (con.fields I)) 0

-- ADE: none.
/-- The `j`-th recursive result of the constructor `con` in the erasure is the one of the `j`-th of
its fields whose nesting has a position, which the typing binds the `j`-th result of its branch:
the recursor on the field when it is recursive, the corecursor of the shape of its type when the
type has one, and `⊥` otherwise. -/
theorem Constructor.getElem?_recursiveResults {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (names : List Name) (qs : List Quality) (ps : List Grade) (χ : Grade)
    (con : Constructor j g k' Δ) (I : Instance j g) (i : Nat) :
    (con.recursiveResults sig v names qs ps χ I)[i]? =
      ((((con.fields I).nest names).zipIdx.filterMap fun y =>
          if y.1.isPlain then none else some y.2)[i]?).map fun l =>
        RecursiveResult.ofField ((con.fields I).recursionAt names l)
          (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join l := by
  rw [Constructor.recursiveResults, ← List.getElem?_map, List.map_filterMap]
  congr 2
  funext y
  split <;> rfl

/-- The recursive result of a field is nested on this field, at the shape `σ`, exactly when the
field is not recursive and its type has the shape `σ`. -/
theorem RecursiveResult.ofField_eq_nested {r : Option Name} {s : Option Shape} {l l' : Nat}
    {σ : Shape} : RecursiveResult.ofField r s l = .nested l' σ ↔ l' = l ∧ r = none ∧ s = some σ := by
  cases r <;> cases s <;> simp [RecursiveResult.ofField, eq_comm]

-- ADE: none.
/-- The recursive result of the `j`-th field of the constructor `con` whose nesting has a
position, the field `l`, is the corecursor of the shape `σ` exactly when the field is not recursive
and the shape of its nested result is `σ`. -/
theorem Constructor.recursiveResults_eq_nested {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {v : Lifting.Variables} {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g} {i l : Nat}
    (hl : (((con.fields I).nest names).zipIdx.filterMap fun y =>
      if y.1.isPlain then none else some y.2)[i]? = some l) (σ : Shape) :
    (con.recursiveResults sig v names qs ps χ I)[i]? = some (.nested l σ) ↔
      (con.fields I).recursionAt names l = none ∧
        (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]? = some (some σ) := by
  rw [Constructor.getElem?_recursiveResults, hl, Option.map_some, Option.some.injEq,
    RecursiveResult.ofField_eq_nested, Option.join_eq_some_iff]
  simp

end Sic.Core
