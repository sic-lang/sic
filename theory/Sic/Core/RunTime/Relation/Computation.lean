module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed

/-!
# Computation of the Relation of Run Time

The relation of run time of annex 20 of RFC 36, `t ®_H a : A`, relates a term as the canonical term
it computes to, so that it holds of a term exactly when it holds of the terms it reduces to; and it
relates the terms of a type as those of every type equal to it, whose relations of run time are the
same, when the term is a term of the type, which tells a proposition from a type without terms
whose relations of run time are the same.

ADE prove that their relation is kept by the reduction of the source, `sourceRedSubstTerm` and
`sourceRedSubstTerm′`, in `Graded/Erasure/LogicalRelation/Reduction.agda`, by recursion on the proof
that the type is reducible, and by the conversion, `convTermʳ`, in
`Graded/Erasure/LogicalRelation/Conversion.agda`, by recursion on the proofs that both types are
reducible; here both follow from the computation of the term and from the equality of the types,
which compares their relations of run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `sourceRedSubstTerm` and `sourceRedSubstTerm′`, in
-- `Graded/Erasure/LogicalRelation/Reduction.agda`.
/-- A term is related at run time to the addresses that the terms it reduces to are related to, in
a signature whose names are distinct. -/
theorem RunsAs.redStar_iff {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t t' : Term 0 []} {a : Nat} {A : Term 0 []} (hd : sig.Distinct)
    (h : RedStar (sig.interpret ι) t t') : RunsAs sig ι P H t a A ↔ RunsAs sig ι P H t' a A := by
  simp only [RunsAs, RunRel.computed, Computesι.redStar_iff hd h]

-- ADE: `convTermʳ`, in `Graded/Erasure/LogicalRelation/Conversion.agda`.
/-- A term of a type is related at run time at every type equal to it, in a signature whose names
are distinct: the equality of the types gives them the same relations of run time, and the term,
a proof when the type is a proposition, makes the type equal to it a proposition too. -/
theorem RunsAs.conv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t : Term 0 []} {a : Nat} {A B : Term 0 []} (hd : sig.Distinct)
    (ht : EqTermClause sig ι t t A) (hAB : EqTypeClause sig ι A B) :
    RunsAs sig ι P H t a A → RunsAs sig ι P H t a B := by
  obtain ⟨v, w, R, hA, hB, hv, hw, hr⟩ := hAB
  rintro ⟨v', hA', h⟩
  cases Computesι.det hd hA hA'
  rcases h with hp | ⟨Q, hQ, htQ⟩
  · obtain ⟨v₁, R₁, hA₁, hv₁, htt⟩ := ht.2 ⟨v, hA, hp⟩
    cases Computesι.det hd hA hA₁
    exact ⟨w, hB, .inl (hv.isProp_of_prop hd hw hp ((hv₁.unique hd hv t t).1 htt))⟩
  · exact ⟨w, hB, .inr ⟨Q, (hr P Q).1 hQ, htQ⟩⟩

/-- A term is related at run time to the addresses that a term with the same computations is related
to. -/
theorem RunsAs.congr_computes {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t t' : Term 0 []} {a : Nat} {A : Term 0 []}
    (h : ∀ w, Computesι sig ι t w ↔ Computesι sig ι t' w) :
    RunsAs sig ι P H t a A ↔ RunsAs sig ι P H t' a A := by
  simp only [RunsAs, RunRel.computed, h]

end Sic.Core
