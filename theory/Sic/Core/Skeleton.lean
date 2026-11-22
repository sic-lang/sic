module

public import Sic.Core.Syntax

/-!
# Skeletons

The skeleton of a data type of annex 14 of RFC 36, on whose term the erasure of a recursor runs
when its term is erased, without the scope of the term of the target language that it stands for: a
skeleton mentions no variable, so that the shape of a nested result holds the skeleton of a motive,
on whose term the recursor of the multiplicity `0` runs, whatever the scope of the branch that
builds it.
The skeleton of a data type is read from the signature alone; the term of the target language that
a skeleton stands for is in `Sic/Core/Erasure.lean`.

ADE have no skeletons.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- `Z`: a skeleton, the empty skeleton `□`, which holds nothing, or the constructor `c_i` of the
case `i` in its block applied to a skeleton for each of its fields.
RFC: `\mathsf{syntax}_Z` -/
inductive Skeleton : Type where
  /-- `□`. -/
  | empty : Skeleton
  /-- `c_i⟨Z₁, …, Z_a⟩`. -/
  | ctor (case : Nat) (fields : List Skeleton) : Skeleton

/-- The skeleton of the data type `D` of the block of the type declaration `decl`, at the instance
`I`, within the depth `d`: the constructor of its case applied to `□` for each field that is not
recursive and to the skeleton of the type of each recursive field, when `D` has exactly one
constructor, and `□` when it has none or several, or when the depth is reached. -/
def TypeDeclaration.skeleton (decl : TypeDeclaration) (I : Instance decl.sorts decl.grades) :
    Nat → Name → Skeleton
  | 0, _ => .empty
  | d + 1, D =>
    match decl.dataTypes.find? (·.name == D) with
    | some T =>
      match T.constructors with
      | [con] =>
        match decl.cases.findIdx? (fun x => x.2.1.name == D && x.2.2.name == con.name) with
        | some i => .ctor i (((con.fields I).recursion decl.names).map fun
            | some D' => decl.skeleton I d D'
            | none => .empty)
        | none => .empty
      | _ => .empty
    | none => .empty

/-- The skeleton of the data type `D` at the instance of the qualities `qs` and of the grades `ps`,
within the depth of the number of the types of its block, when the entry declares it. -/
def Entry.skeleton (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option Skeleton :=
  Entry.lookup D fun decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.dataTypes.find? (·.name == D)).map fun _ =>
          decl.skeleton (.ofLists qs ps hq hp) decl.names.length D
      else none
    else none

/-- The skeleton of the data type `D` at the instance of the qualities `qs` and of the grades `ps`,
in the last entry of the signature that declares it, and `□` when the signature has no such entry,
which the erasure of a recursor on an erased term reads: in a block whose types have one
constructor at most, the type of a term gives its form, which the skeleton rebuilds, so that the
recursor runs its branches on the term of the skeleton.
The depth of the number of the types of the block is reached only on a type without closed term:
along a path of a closed term of a type, no type of the block comes twice, since each type has one
constructor, so that the term would hold a term of the same form, without end.
RFC: `\mathsf{skeleton}_D` -/
def Signature.skeleton (sig : Signature) (D : Name) (qs : List Quality)
    (ps : List Grade) : Skeleton :=
  (sig.findSome? (Entry.skeleton D qs ps)).getD .empty

/-- An entry that does not introduce the name `D` gives the skeleton of no data type named `D`. -/
theorem Entry.skeleton_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.skeleton D qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

end Sic.Core
