module

public import Sic.Core.Evaluation.Conservation
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.RunTime.Uses.Erasure
import Sic.Core.Usage.Signature

/-!
# Uses of the Program of a Signature

The program of a well-used signature whose names are distinct is well used, `⊢ ⌊Σ⌋ ▶` of annex 17 of
RFC 36, which the conservation of the bindings assumes: each body of the program is the erasure of
the body of a constant definition of the mode `11ᵐ`, which uses no variable in the signature before
it, and so in the whole signature, in which the program erases it.

ADE have no signatures.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `⊢ ⌊Σ⌋ ▶`: the program of a well-used signature whose names are distinct, erased at run time,
reads no variable in its bodies, and its binders as their multiplicities allow.
RFC: `\mathsf{usage}_{\lfloor \Sigma \rfloor}` -/
theorem UsageSig.compile_usage {sig : Signature} (hd : sig.Distinct) (hu : UsageSig sig) :
    (sig.compile Mode.oneOne.erased).Usage := by
  intro f qs ps M hM
  obtain ⟨e, he, hc⟩ := List.exists_of_findSome?_eq_some hM
  cases e with
  | constantDefinition d =>
    simp only [Entry.compile] at hc
    split at hc
    case isFalse => exact nomatch hc
    rename_i hn
    split at hc
    case isFalse => exact nomatch hc
    rename_i hq
    split at hc
    case isFalse => exact nomatch hc
    rename_i hp
    cases hc
    have h := Usage.erase_usage hd Scope.FirstOrder.nil hn.2
      (hu.constantDefinition_usage he (.ofLists qs ps hq hp))
    rwa [GradeVector.run_commutes.run_zero] at h
  | _ => simp only [Entry.compile] at hc; exact nomatch hc

end Sic.Core
