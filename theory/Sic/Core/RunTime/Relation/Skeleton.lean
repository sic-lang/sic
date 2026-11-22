module

public import Sic.Core.Erasure
import Sic.Core.Syntax.Signature
import Sic.Math.Relation

/-!
# Skeletons at Run Time

The skeleton of annex 14 of RFC 36 at run time, on whose term the erasure of a recursor whose grade
is erased runs: in a signature whose names are distinct, the skeleton of a data type is that of the
block of its declaration, and the case of a constructor that of its block; the term of the skeleton
of a type with exactly one constructor unfolds into this constructor applied to the terms of the
skeletons of the types of its recursive fields, and to `↯` for its other fields.

The depth of the skeleton, the number of the types of the block, is never reached along a path of
types that has an end: a type with exactly one constructor is above the types of its recursive
fields, and a type accessible for this relation is above none of its ancestors, which are distinct
types of the block, fewer than them.

ADE erase the eliminations of the pairs and of the unit whose grade is erased by running their
branch on erased fields, in `Graded/Erasure/Extraction.agda`, without recursive results, so that
they need no skeleton.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Signatures -/

/-- In a signature whose names are distinct, the skeleton of a data type is that of the block of its
declaration, at the instance, within the depth of the number of the types of the block. -/
theorem Signature.Distinct.skeleton : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.skeleton D qs ps =
      decl.skeleton hqp.inst decl.names.length D := by
    intro _ hd _ _ _ ⟨hm, hT, hD⟩ _ _ hqp
    subst hD
    unfold Signature.skeleton Entry.skeleton
    rw [hd.findSome?_lookup hm (TypeDeclaration.name_mem_names hT)]
    simp only [hqp, ↓reduceDIte,
      List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hm)) hT, Option.map_some,
      Option.getD_some]

/-! ## Unfolding -/

/-- The term of the skeleton of a data type `D` with exactly one constructor `c`, of the case `i` of
its block, within the depth `d + 1`: the constructor of the case `i` applied to the term of the
skeleton of the type of each recursive field within the depth `d`, and to `↯` for each other field,
each at the multiplicity `0`. -/
theorem TypeDeclaration.skeleton_succ {decl : TypeDeclaration} (hn : decl.names.Nodup)
    (I : Instance decl.sorts decl.grades) {n d : Nat} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (hD : T.name = D) {c : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hc : T.constructors = [c]) {i : Nat}
    (hi : Entry.constructorCase D c.name (.typeDeclaration decl) = some i) :
    ((decl.skeleton I (d + 1) D).target : Target n) =
      .ctor i (Targets.ofList (((c.fields I).recursion decl.names).map fun
        | some D' => (.zero, (decl.skeleton I d D').target)
        | none => (.zero, .erased))) := by
  subst hD
  simp only [Entry.constructorCase,
    Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT)] at hi
  simp only [TypeDeclaration.skeleton,
    List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, hc, hi, Skeleton.target,
    Skeleton.targets_eq_ofList, List.map_map]
  congr 3
  funext r
  cases r <;> rfl

/-! ## Acyclicity -/

/-- `D' ≺ D`: the data type `D` of the block of the type declaration `decl` has exactly one
constructor, of which a recursive field, at the instance `I`, is of the type `D'`, so that a closed
term of `D` holds one of `D'`. -/
def TypeDeclaration.Below (decl : TypeDeclaration) (I : Instance decl.sorts decl.grades)
    (D' D : Name) : Prop :=
  ∃ T ∈ decl.dataTypes, T.name = D ∧ ∃ c, T.constructors = [c] ∧
    some D' ∈ (c.fields I).recursion decl.names

/-- A data type `D` of the block accessible for `≺` is none of its ancestors, the types of the block
that it is below by the transitive closure of `≺`, so that distinct ancestors are fewer than the
types of the block: the depth of the skeleton, their number minus the number of the ancestors, is
never reached. -/
theorem TypeDeclaration.length_ancestors_lt {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {D : Name} (h : Acc (decl.Below I) D)
    (hD : D ∈ decl.names) {A : List Name} (hA : A.Nodup) (hAn : ∀ X ∈ A, X ∈ decl.names)
    (hAD : ∀ X ∈ A, Relation.TransGen (decl.Below I) D X) : A.length < decl.names.length := by
  have hDA : D ∉ A := fun hm => h.not_transGen_self (hAD D hm)
  have hle := List.length_le_of_nodup_subset (List.nodup_cons.2 ⟨hDA, hA⟩) fun X hX => by
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hD
    · exact hAn X hX
  exact hle

end Sic.Core
