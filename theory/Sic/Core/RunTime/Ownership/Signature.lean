module

public import Sic.Core.Evaluation.Claims
public import Sic.Core.Ownership
public import Sic.Grading.GradeSet
import Sic.Core.Ownership.Signature
import Sic.Core.RunTime.Ownership.Erasure

/-!
# Ownership of the Program of a Signature

The program of a signature whose names are distinct and whose entries have their ownerships has its
ownership, `⊢ ⌊Σ⌋ ◀ Ω` of annex 20 of RFC 36, which the uniqueness at run time assumes, when `Ω`
gives each constant the run-time multiplicity of the ownership of its entry: each body of the
program is the erasure of the body of a constant definition of the mode `11ᵐ`, whose value has the
ownership of the definition in the signature before it, and so in the whole signature, in which the
program erases it.

ADE have no signatures, and no ownership.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- `⊢ ⌊Σ⌋ ◀ Ω`: each body of the program of a signature whose names are distinct and whose entries
have their ownerships, erased at run time, has the ownership that `Ω` gives its constant, the
run-time multiplicity of the ownership of its entry.
RFC: `\mathsf{own}_{\lfloor \Sigma \rfloor}` -/
theorem OwnershipSig.compile_ownership {sig : Signature} (hd : sig.Distinct)
    (hs : OwnershipSig sig) {Ω : Name → Multiplicity}
    (hΩ : ∀ f j k' g m p A, sig.HasConstant f j k' g m p A → Ω f = p.run) :
    (sig.compile Mode.oneOne.erased).Ownership Ω := by
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
    rename_i hqp
    cases hc
    rw [← hn.1, hΩ _ _ _ _ _ _ _ (.constantDefinition he)]
    exact Ownership.erase_ownership hd hs hΩ Scope.FirstOrder.nil (fun x => nomatch x) hn.2
      (hs.constantDefinition_ownership hd he hqp.inst)
  | _ => simp only [Entry.compile] at hc; exact nomatch hc

end Sic.Core
