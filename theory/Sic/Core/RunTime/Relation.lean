module

public import Sic.Core.Meaning

/-!
# Relation of Run Time

The relation of run time of annex 20 of RFC 36, `t ®_H a : A`, between a closed term `t` of the
source of a closed type `A` and the address `a` of a value of the target language in the heap `H`,
which states that the value at `a` is what the erasure by `S^{11ᵐ}` of `t` computes at run time: the
type computes to a canonical type, whose relation of run time, which the meaning gives, relates the
term to the address.

ADE relate a term to the term of the target language that it extracts to, `t ® v ∷ A / [A]`, by
recursion on the proof that `A` is reducible, in `Graded/Erasure/LogicalRelation.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `_®_∷_/_`, in `Graded/Erasure/LogicalRelation.agda`.
/-- `t ®_H a : A`: the closed type `A` computes to a type or a proposition whose relation of run time
relates the closed term `t` to the address `a` in the heap `H`.
RFC: `\circledR_A` -/
def RunsAs (sig : Signature) (ι : Interpretation) (P : Program) (H : Heap) (t : Term 0 [])
    (a : Nat) (A : Term 0 []) : Prop :=
  ∃ v R, Computesι sig ι A v ∧ HasRun sig ι P v R ∧ R.computed sig ι H t a

end Sic.Core
