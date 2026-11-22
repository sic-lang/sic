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
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.skeleton D qs ps =
      decl.skeleton (.ofLists qs ps hq hp) decl.names.length D
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    unfold Signature.skeleton
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : Entry.skeleton D qs ps (.typeDeclaration decl) =
          some (decl.skeleton (.ofLists qs ps hq hp) decl.names.length D) := by
        simp only [Entry.skeleton, Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT),
          hq, hp, ↓reduceDIte, ← hD,
          List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs, Option.getD_some]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.skeleton_of_not_mem hDe]; rfl)]
      exact hd.skeleton ⟨he', hT, hD⟩ hq hp

/-- An entry that does not introduce the name `D` gives the case of no constructor of `D`. -/
theorem Entry.constructorCase_of_not_mem {D c : Name} :
    {e : Entry} → D ∉ e.names → Entry.constructorCase D c e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- A signature none of whose entries introduces the name `D` gives the case of no constructor of
`D`. -/
theorem Signature.constructorCase_of_not_mem {D c : Name} :
    {sig : Signature} → (∀ e ∈ sig, D ∉ e.names) → sig.constructorCase D c = none
  | [], _ => rfl
  | e :: sig, h => by
    unfold Signature.constructorCase
    rw [List.findSome?_cons_of_isNone
      (by rw [Entry.constructorCase_of_not_mem (h e List.mem_cons_self)]; rfl)]
    exact Signature.constructorCase_of_not_mem fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- In a signature whose names are distinct, the case of a constructor of a data type is its case in
the block of its declaration. -/
theorem Signature.Distinct.constructorCase {c : Name} : {sig : Signature} → sig.Distinct →
    {D : Name} → {decl : TypeDeclaration} →
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} → sig.HasDataType D decl T →
    sig.constructorCase D c = Entry.constructorCase D c (.typeDeclaration decl)
  | [], _, _, _, _, h => nomatch h.1
  | e :: sig, ⟨hd, _, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩ => by
    unfold Signature.constructorCase
    rcases List.mem_cons.1 he with rfl | he'
    · cases hc : Entry.constructorCase D c (.typeDeclaration decl) with
      | some i => rw [List.findSome?_cons_of_isSome (by rw [hc]; rfl), hc]
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hc]; rfl)]
        exact Signature.constructorCase_of_not_mem fun e' he'' hDe =>
          hfresh _ he'' D (hD ▸ TypeDeclaration.name_mem_names hT) hDe
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.constructorCase_of_not_mem hDe]; rfl)]
      exact hd.constructorCase ⟨he', hT, hD⟩

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
