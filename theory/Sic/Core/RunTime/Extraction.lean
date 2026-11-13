module

public import Sic.Core.RunTime.Signature
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.RunTime.Properties
import Sic.Core.Soundness.Substitution
import Sic.Core.Typing.Presuppositions

/-!
# Extraction

The soundness of the extraction, of annex 20 of RFC 36: the erasure by `S^{11ᵐ}` of a closed term
typed and used in the mode `11ᵐ`, run in the empty heap, computes a value to which the relation of
run time of its type relates the term, `(sound_⌊⌋)`; at an instance of a data type that is not a
proposition, this value is the constructor of the case of the constructor that the term computes,
`(sound_c)`.

ADE state the soundness of their extraction for the natural numbers and for the unit types, whose
closed terms and their erasures reduce to the same numeral or to the unit.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `soundness-ℕ`, in `Graded/Erasure/Consequences/Soundness.agda`.
/-- The erasure by `S^{11ᵐ}` of a closed term typed and used in the mode `11ᵐ`, at every value of
its level variables, evaluates in the empty heap and the empty environment to an address in a heap,
to which the term is related at its type, in a signature whose entries use their variables as their
grades allow, when the interpretation gives the constant declarations of the signature terms of
their types and the program realizes the signature.
RFC: `\mathsf{sound}_{\lfloor\rfloor}` -/
theorem extraction {ι : Interpretation} {P : Program} {sig : Signature} {k : Nat}
    {t A : Term k []} {γ : GradeVector ([] : Scope).length} (hι : ValidInterpretation ι sig)
    (hP : ValidProgram ι P sig) (hu : UsageSig sig) (h : HasType sig .empty t A)
    (hut : Usage sig γ .oneOne t) (ρ : Fin k → Nat) :
    ∃ a H R, Eval P [] [] ((t.atLevels ρ).erase sig Mode.oneOne.erased Scope.FirstOrder.nil) a H R ∧
      RunsAs sig ι P H (t.atLevels ρ) a (A.atLevels ρ) := by
  obtain ⟨a, H, R, he, -, hr⟩ :=
    fundamental.hasType (hΓ := Scope.FirstOrder.nil) hι hP hu h hut ρ (fun x => nomatch x) [] [] []
      ((EqSubst.empty_iff _ _).2 trivial) trivial rfl
  rw [Term.subst_empty, Term.subst_empty] at hr
  exact ⟨a, H, R, he, hr⟩

-- ADE: `soundness-ℕ`, in `Graded/Erasure/Consequences/Soundness.agda`.
/-- The erasure by `S^{11ᵐ}` of a closed term typed and used in the mode `11ᵐ`, whose type computes,
at a value of its level variables, to an instance of a data type that is not a proposition,
evaluates in the empty heap and the empty environment to the constructor of the target language of
the case of the constructor that the term computes, under the hypotheses of `extraction`.
RFC: `\mathsf{sound}_c` -/
theorem extraction_ctor {ι : Interpretation} {P : Program} {sig : Signature} {k : Nat}
    {t A : Term k []} {γ : GradeVector ([] : Scope).length} {D : Name} {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (hι : ValidInterpretation ι sig) (hP : ValidProgram ι P sig) (hu : UsageSig sig)
    (h : HasType sig .empty t A) (hut : Usage sig γ .oneOne t) (ρ : Fin k → Nat)
    (hD : sig.HasDataType D decl T) (hA : Computesι sig ι (A.atLevels ρ) (.inst D qs ls ps as))
    (hp : ¬ IsProp sig ι (.inst D qs ls ps as)) :
    ∃ a H R v c ts i bs,
      Eval P [] [] ((t.atLevels ρ).erase sig Mode.oneOne.erased Scope.FirstOrder.nil) a H R ∧
        Computesι sig ι (t.atLevels ρ) v ∧ v.IsCtor D c ts ∧ sig.constructorCase D c = some i ∧
          H[a]? = some (.ctor i bs) := by
  have hd := (presuppositions.hasType h).distinct
  obtain ⟨a, H, R₀, he, v', hA', hr⟩ := extraction hι hP hu h hut ρ
  cases Computesι.det hd hA hA'
  obtain hr | ⟨R, hR, w, hw, hR'⟩ := hr
  · exact absurd hr hp
  cases hR with
  | prop n b hb _ => exact absurd ⟨n, b, hb⟩ hp
  | univ n hR =>
    rw [levelRel_run_iff] at hR
    cases hR with
    | codata h' _ _ _ hv => exact (hd.inst_data_codata hD h' hv).elim
    | data h' _ _ _ hv _ _ S _ =>
      obtain ⟨-, rfl, -, -, -, -⟩ := Term.inst.inj hv
      refine hR' (fun D' H v a => ∃ c ts i bs, v.IsCtor D' c ts ∧ sig.constructorCase D' c = some i ∧
        H[a]? = some (.ctor i bs)) ?_ |>.elim fun c ⟨ts, i, bs, hc, hi, ha⟩ =>
          ⟨a, H, R₀, w, c, ts, i, bs, he, hw, hc, hi, ha⟩
      intro T' _ H v a ⟨c, _, i, ts, bs, hc, hi, ha, _⟩
      exact ⟨c.name, ts, i, bs, hc, hi, ha⟩

end Sic.Core
