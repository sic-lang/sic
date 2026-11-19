module

/-!
# Skeletons

The skeleton of a data type of annex 16 of RFC 36, which the erasure of a recursor runs on when its
term is erased, without the scope of the term of the target language that it stands for: a skeleton
mentions no variable, so that the shape of a nested result holds the skeleton of a motive, which
the recursor of the multiplicity `0` runs on, whatever the scope of the branch that builds it.
The term of the target language that a skeleton stands for is in `Sic/Core/Erasure.lean`.

ADE have no skeletons.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- A skeleton: `↯`, or a constructor of the case `i` of its block applied to skeletons, each stored
at the multiplicity `0` and at the requirement `ω`, the term of the target language that it stands
for being built of these alone. -/
inductive Skeleton : Type where
  /-- `↯`. -/
  | erased : Skeleton
  /-- `c_i(k̄)`. -/
  | ctor (case : Nat) (fields : List Skeleton) : Skeleton

end Sic.Core
