module

public import Sic.Core.Evaluation.Conservation
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.RunTime.Uses.Erasure
import Sic.Core.RunTime.Uses.Signature

/-!
# Uses of the Extraction

The conservation of the bindings by the extraction, of annex 20 of RFC 36: the erasure by
`S^{11ᵐ}` of a closed term used in the mode `11ᵐ`, run under the program of a well-used signature
whose names are distinct, reads each cell of its heap as the multiplicity of the cell allows, once
the reads that its value can still do are counted, `(cons_⌊⌋)`; when its value holds no closure,
each cell of the multiplicity `1` is read exactly once, and no cell of the multiplicity `0`,
`(cons_⌊⌋.data)`.
The erasure keeps no level, so that the run is the same at every value of the level variables of the
term, and the typing is not needed: the usage alone bounds the reads.

ADE prove the resource correctness of their machine, which runs the terms of the source language
rather than their extraction.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The run-time multiplicities of the grades of the empty scope are the vector `0^ν`. -/
theorem GradeVector.run_nil (γ : GradeVector ([] : Scope).length) : γ.run = 𝟘ᵛ :=
  funext fun x => x.elim0

-- ADE: none.
/-- The erasure by `S^{11ᵐ}` of a closed term used in the mode `11ᵐ`, run at the weight `1` in the
empty heap under the program of a well-used signature whose names are distinct, reads each cell of
its heap as the multiplicity of the cell allows, once the reads that its value can still do are
counted.
RFC: `\mathsf{cons}_{\lfloor\rfloor}` -/
theorem extraction_conservation {sig : Signature} {k : Nat} {t : Term k []}
    {γ : GradeVector ([] : Scope).length} (hd : sig.Distinct) (hu : UsageSig sig)
    (hut : Usage sig γ .oneOne t) {a : Nat} {H : Heap} {R : List Nat}
    (h : Eval (sig.compile Mode.oneOne.erased) .one [] []
      (t.erase sig Mode.oneOne.erased Scope.FirstOrder.nil) a H R) :
    ∃ D, H.ValueDemand a D ∧ ∀ c π ℓ, H[c]? = some (.cell π ℓ) → π ≤ Demand.uses R c + D c := by
  have hM := Usage.erase_usage hd Scope.FirstOrder.nil rfl hut
  rw [GradeVector.run_nil] at hM
  exact Eval.conservation (hu.compile_usage hd) hM h

-- ADE: none.
/-- The erasure by `S^{11ᵐ}` of a closed term used in the mode `11ᵐ`, run as in
`extraction_conservation` to a value that holds no closure, reads each cell of the multiplicity `1`
of its heap exactly once, and never a cell of the multiplicity `0`.
RFC: `\mathsf{cons}_{\lfloor\rfloor}.\mathsf{data}` -/
theorem extraction_conservation_data {sig : Signature} {k : Nat} {t : Term k []}
    {γ : GradeVector ([] : Scope).length} (hd : sig.Distinct) (hu : UsageSig sig)
    (hut : Usage sig γ .oneOne t) {a : Nat} {H : Heap} {R : List Nat}
    (h : Eval (sig.compile Mode.oneOne.erased) .one [] []
      (t.erase sig Mode.oneOne.erased Scope.FirstOrder.nil) a H R)
    (hdata : H.IsData a) (c ℓ : Nat) :
    (H[c]? = some (.cell .one ℓ) → R.count c = 1) ∧
      (H[c]? = some (.cell .zero ℓ) → R.count c = 0) := by
  have hM := Usage.erase_usage hd Scope.FirstOrder.nil rfl hut
  rw [GradeVector.run_nil] at hM
  exact Eval.conservation_data (hu.compile_usage hd) hM h hdata c ℓ

end Sic.Core
