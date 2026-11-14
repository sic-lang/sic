module

public import Sic.Core.Evaluation.Claims
public import Sic.Core.Ownership
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.Evaluation.Uniqueness
import Sic.Core.RunTime.Ownership.Erasure
import Sic.Core.RunTime.Ownership.Signature
import Sic.Core.RunTime.Uses.Erasure
import Sic.Core.RunTime.Uses.Signature

/-!
# Uniqueness of the Extraction

The uniqueness of what the value of the extraction owns alone, of annex 20 of RFC 36: the erasure by
`S^{11ᵐ}` of a closed term used in the mode `11ᵐ` and owned alone at run time, run under the
program of a signature whose names are distinct and whose entries have their usages and their
ownerships, has a value whose reach refers once at most to each address that it claims,
`(uniq_⌊⌋)`.
A closed term runs in the empty heap, which no frame refers to, so that the invariant of the
evaluation, `reach_⇓`, is read at the frame that refers to nothing: what remains is that the value
itself does not share what it owns alone.
The erasure keeps no level, so that the run is the same at every value of the level variables of the
term, and the typing is not needed: the usage and the ownership alone bound the references.

ADE have no ownership, and no uniqueness at run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- The erasure by `S^{11ᵐ}` of a closed term used in the mode `11ᵐ`, whose ownership has the
run-time multiplicity `1`, run at the weight `1` in the empty heap under the program of a signature
whose names are distinct and whose entries have their usages and their ownerships, has a value
whose reach, under an annotation valid for its heap, refers once at most to each address that the
value claims.
RFC: `\mathsf{uniq}_{\lfloor\rfloor}` -/
theorem extraction_uniqueness {sig : Signature} {k : Nat} {t : Term k []}
    {γ : GradeVector ([] : Scope).length} (hd : sig.Distinct) (hu : UsageSig sig)
    (hs : OwnershipSig sig) {Ω : Name → Multiplicity}
    (hΩ : ∀ f j k' g m p A, sig.HasConstant f j k' g m p A → Ω f = p.run)
    (hut : Usage sig γ .oneOne t) {φ : Var [] .var → Grade} {o : Grade}
    (hot : Ownership sig φ .oneOne o t) (ho : o.run = .one) {a : Nat} {H : Heap} {R : List Nat}
    (h : Eval (sig.compile Mode.oneOne.erased) .one [] []
      (t.erase sig Mode.oneOne.erased Scope.FirstOrder.nil) a H R) :
    ∃ (g : Heap.Annotation) (U : Demand), g.Valid Ω H ∧ Heap.ValueReach H g a U ∧
      ∀ b, Heap.Claims H g a b → U b ≠ .omega := by
  have hM := Ownership.erase_ownership hd hs hΩ Scope.FirstOrder.nil
    (φ' := 𝟘ᵛ) (fun x => nomatch x) rfl hot
  rw [ho] at hM
  have hν := Usage.erase_usage hd Scope.FirstOrder.nil rfl hut
  obtain ⟨g, U, -, hg, hU, -, hB⟩ := Eval.reach (hs.compile_ownership hd hΩ)
    (hu.compile_usage hd) h hM hν (g := ⟨fun _ _ => 𝟘ᵛ, fun _ _ => 𝟘ᵛ⟩)
    (fun ℓ _ _ _ _ _ _ hℓ => nomatch hℓ) .nil (F := 𝟘ᵛ) (fun _ _ => rfl)
    (fun b ⟨x, _⟩ => x.elim0)
  exact ⟨g, U, hg, hU, fun b hb => by
    have := hB rfl b hb
    rwa [show (𝟘ᵛ : Demand) b + U b = U b from
      Multiplicity.modality.semiring.zero_add _] at this⟩

end Sic.Core
