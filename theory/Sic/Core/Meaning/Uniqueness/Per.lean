module

public import Sic.Core.Meaning
import Sic.Core.Meaning.RunTime.Properties
import Sic.Math.Nat

/-!
# Partial Equivalence Relations of the Levels

The relations of every level are partial equivalence relations, by induction on the level, from
which `Sic.Core.Meaning.Uniqueness` proves that they are unique.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The relations of every level are partial equivalence relations, and their relations of run time
unique, in a signature whose names are distinct. -/
theorem levelRel_isPer {sig : Signature} {ι : Interpretation} (hd : sig.Distinct) (n : Nat) :
    (levelRel sig ι n).IsPer :=
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  { univ_isPer := fun h => UnivRel.isPer hd ih (levelRel_univ_iff.1 h)
    univ_unique := fun h h' =>
      UnivRel.unique hd ih (levelRel_univ_iff.1 h) _ (levelRel_univ_iff.1 h')
    prop_unique := fun h h' =>
      PropRel.unique hd ih (levelRel_prop_iff.1 h) _ (levelRel_prop_iff.1 h')
    run_unique := fun h h' =>
      RunUnivRel.congr hd ih (fun m hm => (ih m hm).run_unique) (levelRel_run_iff.1 h) _
        (levelRel_run_iff.1 h') }
termination_by n
decreasing_by all_goals assumption

/-- The relations of the levels below `n` are partial equivalence relations, in a signature whose
names are distinct: the hypothesis that the laws of the graphs of the level `n` take. -/
theorem levelRel_isPer_lt {sig : Signature} {ι : Interpretation} (hd : sig.Distinct) (n : Nat) :
    ∀ m, m < n → (levelRel sig ι m).IsPer :=
  Nat.forall_lt (levelRel_isPer hd) n

end Sic.Core
