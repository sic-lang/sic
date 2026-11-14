module

public import Sic.Core.Evaluation.Heap
import Sic.Core.Syntax.Signature
import Sic.Math.Relation

/-!
# Skeletons at Run Time

The skeleton of annex 16 of RFC 36 at run time, which the erasure of a recursor whose grade is
erased runs on: in a signature whose names are distinct, the skeleton of a data type is that of the
block of its declaration, and the case of a constructor that of its block; the skeleton of a type
with exactly one constructor unfolds into this constructor applied to the skeletons of the types of
its recursive fields, and to `↯` for its other fields; a skeleton evaluates in every environment and
heap.

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

/-- An entry that does not introduce the name `D` gives the skeleton of no data type named `D`. -/
theorem Entry.skeleton_of_not_mem {n : Nat} {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → (Entry.skeleton D qs ps e : Option (Target n)) = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.dataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.name_mem_names hT)
    simp only [Entry.skeleton]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.map_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

-- ADE: none.
/-- In a signature whose names are distinct, the skeleton of a data type is that of the block of its
declaration, at the instance, within the depth of the number of the types of the block. -/
theorem Signature.Distinct.skeleton {n : Nat} : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    (sig.skeleton D qs ps : Target n) =
      decl.skeleton (.ofLists qs ps hq hp) decl.names.length D
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    unfold Signature.skeleton
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : (Entry.skeleton D qs ps (.typeDeclaration decl) : Option (Target n)) =
          some (decl.skeleton (.ofLists qs ps hq hp) decl.names.length D) := by
        simp only [Entry.skeleton, hq, hp, ↓reduceDIte, ← hD,
          List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs, Option.getD_some]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.skeleton_of_not_mem hDe]; rfl)]
      exact hd.skeleton ⟨he', hT, hD⟩ hq hp

/-- An entry that does not introduce the name `D` gives the case of no constructor of `D`. -/
theorem Entry.constructorCase_of_not_mem {D c : Name} :
    {e : Entry} → D ∉ e.names → Entry.constructorCase D c e = none
  | .typeDeclaration decl, hD => by
    simp only [Entry.constructorCase]
    refine List.findIdx?_eq_none_iff.2 fun x hx => ?_
    have hT := (TypeDeclaration.mem_casesFrom hx).1
    cases h : (x.2.1.name == D) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.1 h ▸ TypeDeclaration.name_mem_names hT) hD
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

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

-- ADE: none.
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

-- ADE: none.
/-- The skeleton of a data type `D` with exactly one constructor `c`, of the case `i` of its block,
within the depth `d + 1`: the constructor of the case `i` applied to the skeleton of the type of each
recursive field within the depth `d`, and to `↯` for each other field, each at the multiplicity
`0`. -/
theorem TypeDeclaration.skeleton_succ {decl : TypeDeclaration} (hn : decl.names.Nodup)
    (I : Instance decl.sorts decl.grades) {n d : Nat} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (hD : T.name = D) {c : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hc : T.constructors = [c]) {i : Nat}
    (hi : Entry.constructorCase D c.name (.typeDeclaration decl) = some i) :
    (decl.skeleton I (d + 1) D : Target n) =
      .ctor i (Targets.ofList (((c.fields I).recursion decl.names).map fun
        | some D' => (.zero, decl.skeleton I d D')
        | none => (.zero, .erased))) := by
  subst hD
  simp only [Entry.constructorCase] at hi
  simp only [TypeDeclaration.skeleton,
    List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, hc, hi]
  rfl

/-! ## Evaluation -/

mutual

-- ADE: none.
/-- A skeleton evaluates, at every weight, in every environment and heap, to a value in a heap that
extends it, reading no cell. -/
theorem Target.IsSkeleton.eval (P : Program) {n : Nat} {M : Target n} (h : M.IsSkeleton)
    (ϖ : Multiplicity) (H : Heap) (E : List Nat) :
    ∃ a H', Eval P ϖ H E M a H' [] ∧ H.Extends H' :=
  match h with
  | .erased => ⟨_, _, .erased, List.prefix_append _ _⟩
  | .ctor hs =>
    have ⟨_, _, hM, hH⟩ := Targets.IsSkeleton.eval P hs ϖ H E
    ⟨_, _, .ctor hM, hH.trans (List.prefix_append _ _)⟩

-- ADE: none.
/-- Skeletons evaluate, at every weight, in every environment and heap, to values in a heap that
extends it, reading no cell. -/
theorem Targets.IsSkeleton.eval (P : Program) {n : Nat} {Ms : Targets n} (h : Ms.IsSkeleton)
    (ϖ : Multiplicity) (H : Heap) (E : List Nat) :
    ∃ as H', EvalAll P ϖ H E Ms as H' [] ∧ H.Extends H' :=
  match h with
  | .nil => ⟨_, _, .nil, List.prefix_refl _⟩
  | .cons (π := π) hM hs =>
    have ⟨_, H₁, hM', hH₁⟩ := Target.IsSkeleton.eval P hM (ϖ * π) H E
    have ⟨_, _, hs', hH₂⟩ := Targets.IsSkeleton.eval P hs ϖ H₁ E
    ⟨_, _, .cons hM' hs', hH₁.trans hH₂⟩

end

/-! ## Acyclicity -/

-- ADE: none.
/-- `D' ≺ D`: the data type `D` of the block of the type declaration `decl` has exactly one
constructor, of which a recursive field, at the instance `I`, is of the type `D'`, so that a closed
term of `D` holds one of `D'`. -/
def TypeDeclaration.Below (decl : TypeDeclaration) (I : Instance decl.sorts decl.grades)
    (D' D : Name) : Prop :=
  ∃ T ∈ decl.dataTypes, T.name = D ∧ ∃ c, T.constructors = [c] ∧
    some D' ∈ (c.fields I).recursion decl.names

-- ADE: none.
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
