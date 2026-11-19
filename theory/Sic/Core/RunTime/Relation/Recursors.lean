module

public import Sic.Core.RunTime.Relation.Recursors.Results
public import Sic.Core.RunTime.Relation.Recursors.Constructor
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Data
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Relation.Recursors.Evaluation
import Sic.Core.RunTime.Relation.Skeleton
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Syntax.Signature
import Sic.Math.Relation

/-!
# Run Time of the Recursors

The recursors at run time: the erasure of a recursor evaluates its term, or the term of the
skeleton of its instance when its grade is erased, then eliminates the value of the case of its
constructor by the branch of the case, with its fields and its recursive results, each the recursor
on its recursive field, or `↯` when its grade is erased.

When the grade of the recursor is used at run time, the term of the recursor is related to the
address of its value at its instance, by `(®_μ)`, the least relations closed under its clauses: the
relations of the canonical terms that `(®_μ)` relates and on whose addresses the recursor evaluates
to the address of a value related to the recursor at the motive are closed, since the recursor on a
constructor steps to its branch, at the terms of the fields and at the recursive results, which
these relations relate to the addresses of the fields and of the results.

When the grade of the recursor is erased, every type of the block has one constructor at most, and
every field of the branch is erased, so that the term of the skeleton of the instance stands for
the term: the term computes to a canonical term that `(eq_μ)` relates, and the relations of the
canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`, and on the terms of whose
skeletons the recursor evaluates to the address of a value related to the recursor at the motive,
are closed, since the term of the skeleton of a type unfolds into its constructor, applied to the
terms of the skeletons of the types of its recursive fields,
within a depth that their ancestors, fewer than the types of the block, never reach.

Both cases eliminate a constructor in the same way, once its fields are related to their addresses
and its recursive results evaluated, which `RunsAs.recursor_ctor` states.

ADE prove the validity of their recursors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- The fields of arguments related at the recursive fields by `Q`, a recursive field of a type `D`
of which is marked by `rs`, have terms that `Q D` relates. -/
theorem Terms.RecRel.exists_of_mem {Q : Name → TermRel} {D : Name} : {ps : List Parameter} →
    (rs : List (Option Name)) → rs.length = ps.length → (ts us : Args 0 [] ps) →
    Terms.RecRel Q rs ts.terms us.terms → some D ∈ rs → ∃ t u, Q D t u
  | [], [], _, .nil, .nil, _, h => nomatch h
  | _ :: _, some _ :: rs, hl, .cons t ts, .cons u us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      exact ⟨t, u, hq.1⟩
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq.2 hm
  | _ :: _, none :: rs, hl, .cons _ ts, .cons _ us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq hm
  | [], _ :: _, hl, _, _, _, _ => nomatch hl
  | _ :: _, [], hl, _, _, _, _ => nomatch hl


/-! ## Recursors -/

section

variable {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {decl : TypeDeclaration} {D : Name}
  {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {as : InstanceArgs 0 Γ decl.scope} {r ς χ' : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
  {χ : GradeVector Γ.length} {δs : Nat → GradeVector Γ.length} {gs : Nat → Nat → Grade}
  {κ : Universe 0}

/-- `r ∉ S`, by induction on `(®_μ)`: the erased recursor eliminates the address of a term of the
instance related to it to the address of a value to which the recursor on the term is related at
the motive at the term. -/
theorem RunsAs.recursor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {h' : Nat} {C : Term 0 (.var :: Γ)} (hh : decl.dataTypes[h']? = some T)
    (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∉ Mode.oneOne.erased) {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ))
    (ht : RunsAs sig ι P H₁ t a ((Term.inst D qs ls ps as).subst σ)) :
    ∃ b H₂ tr, EvalRec P ϖ₀ H₁ E r.run
        (sig.recursionRequirement D qs ps ⟨κ.quality, r, ς⟩ χ').run (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a b H₂ tr ∧
      H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The relations of run time of the block at the arguments substituted.
  obtain ⟨S, hS, hU⟩ := hv.runUnivRel hd hdecl hq hl hp hadm hasσ hs P
  have ihmono : ∀ m,
      m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
  have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
    fun X Y hXY T hT c hc H =>
      RunTelRel.mono hd ihmono (K := Eq) (fun e => e ▸ List.prefix_refl _) (fun _ => rfl)
        (hS X T hT c hc) _ _ (hS Y T hT c hc)
        (fun _ => Nest.map_rel₃
          (fun D' H _ e _ _ => e ▸ RunRel.computed_mono (hXY D' H)) _) H H rfl
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let ϱ := (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  -- The relations of the canonical terms that `(®_μ)` relates and on whose addresses the erased
  -- recursor evaluates, in each heap that extends `H`, to the address of a value related to the
  -- recursor at the motive.
  let X : Name → RunRel := fun D' H₀ w a => DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D' H₀ w a ∧
    ∀ ϖ' H', H₀.Extends H' → H.Extends H' →
      ValidTerm₀ sig ι w (.inst D' qs ls ps (as.subst σ)) →
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        ∃ b H₂ tr, EvalRec P ϖ' H' E r.run ϱ Ns a b H₂ tr ∧ H'.Extends H₂ ∧
          RunsAs sig ι P H₂ (f D' w) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w))
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ H₀ w a, T'.runCtorRel sig (.ofLists qs ps hq hp) T'.name (S X) H₀ w a →
      X T'.name H₀ w a := by
    intro T' hT' H₀ w a hc
    have hcb := DataType.runCtorRel_mono (List.prefix_refl H₀)
      (fun c hc' ts bs => hmono X _ (fun _ _ _ _ h => h.1) T' hT' c hc' H₀ ts bs) hc
    refine ⟨DataType.runBlockRel_fold hmono hT' hcb, fun ϖ' H' hH' hHH' hwv C' hC' => ?_⟩
    obtain ⟨con, hcon, i, fs, bs, hw, hi, ha, hSX⟩ := hc
    -- The case of the constructor.
    obtain ⟨j₀, hij⟩ := hd.cases_of_constructorCase ⟨hdecl, hT', rfl⟩ hcon hi
    obtain ⟨i', j, hi', hj⟩ := TypeDeclaration.exists_cases hT' hcon
    obtain rfl : i = i' := List.getElem?_inj_of_nodup_map (hd.cases_nodup hdecl) hij hi' rfl
    rw [hidx j T' hj] at hC'
    obtain ⟨v, H₃, tr, hev, hH₃, hrun⟩ := RunsAs.recursor_ctor (ϱ := ϱ) hd ⟨hdecl, hT, rfl⟩ hv hadm
      has hCs
      hCv hus hns hrec husr hg hχ hs hσ hEV hE hj hcon hi' hw hwv hHH' ϖ' (hH'.getElem? ha)
      (fun l p hlp => ⟨_, by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ π π' : Multiplicity, π * π' ≤ π * π') _ _⟩)
      (fun l p hlp => ⟨_, _, by rw [List.getElem?_map, hlp]; rfl,
        by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ a r q : Grade, (a * (r * q)).run ≤ a.run * (r.run * q.run)) _ _ _⟩)
      (fun l hl => by
        -- The requirement of the recursion is below the coefficient of the field.
        have hlt := Telescope.lt_of_mem_positions _ 0 hl
        rw [Telescope.length_recursion, Nat.zero_add] at hlt
        refine ⟨_, _, by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl,
          by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl, fun hne => ?_⟩
        show (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run ≤ _
        rw [hd.recursionRequirement_eq ⟨hdecl, hT, rfl⟩ hq hp]
        have h1 : Mode.oneOne.grade * r = r := Grade.modality.semiring.one_mul r
        have hle := TypeDeclaration.recursionRequirement_run_le (sig := sig)
          (v := ⟨κ.quality, r, ς⟩) (m := .oneOne) (χ := χ') (qs := qs) (ps := ps) hi' hl
          (List.getElem?_eq_getElem hlt) (by rw [h1]; rwa [(Grade.run_op _ _).2.1])
        rw [h1] at hle
        rwa [(Grade.run_op _ _).2.1] at hle)
      (fun h0 => absurd ((by decide : ∀ g : Grade, g.run = .zero → g ∈ Mode.oneOne.erased) r h0) hr)
      fun ts hfs hts hrecV => by
        subst hfs
        -- The fields, related at their types.
        refine ⟨(RunsAsArgs.of_fields hd hdecl hv hT' hcon hq hl hp hadm hasσ hs hS
          (fun T' hT' => (hU T' hT').1) (fun _ _ _ _ h => h.1) hts (gs i)
          (fun l p hl' hgl => (by decide : ∀ r p g x : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + x * r → g ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased) r p.usage
            (gs i l) _ hr (hg i j T' con l p hi' hl') hgl) hSX).mono hd hH', ?_⟩
        -- The recursive results used at run time, of fields that `X` relates.
        rw [Telescope.recursion_eq_map_nest] at hrecV ⊢
        refine RunTelRel.recAt (hS X T' hT' con hcon) _ (Telescope.length_nest _ _)
          (hns i j T' con hi') (fun l D hD => ?_) ts bs hSX hrecV _
          (fun l p hl' he => (by decide : ∀ r p g e : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + e * r → e ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased)
            r p.usage _ _ hr (hg i j T' con l p hi' hl') he)
        have hr' : (con.fields (.ofLists qs ps hq hp)).nestAt decl.names l = .direct D := by
          simp only [Telescope.nestAt, hD, Option.getD_some]
        refine ⟨(_, (X D).computed sig ι), by rw [hr']; rfl,
          fun t b ⟨v, hcv, hXv⟩ hVt ϖ'' H'' hH'' => ?_⟩
        have hDn := Telescope.mem_names_of_direct_mem (List.mem_of_getElem? hD)
        obtain ⟨C₃, hC₃⟩ := Motives.get_idxOf hT hnd hCs hDn
        obtain ⟨j₃, T₃, C₃', hj₃, rfl, hC₃', -⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn (Motives.get_subst σ hC₃)
        rw [hidx j₃ T₃ hj₃, hC₃'] at hC₃
        cases hC₃
        have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        obtain ⟨b', H₃, tr', hev, hH₃, hrun⟩ := hXv.2 ϖ'' H'' (hH'.trans hH'') (hHH'.trans hH'')
          (hvv.trans hvv.symm) C₃ ((hidx j₃ T₃ hj₃).symm ▸ hC₃')
        refine ⟨b', H₃, tr', hev, hH₃, fun C hC => ?_⟩
        obtain ⟨j₄, T₄, C₄, hj₄, hT₄, hC₄, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hDn hC
        have hj₄₃ : j₄ = j₃ :=
          List.getElem?_inj_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hj₄ hj₃ hT₄
        rw [hj₄₃, hC₃'] at hC₄
        have hCC : C₄ = C₃ := by cases hC₄; rfl
        rw [hCC]
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃' hcv.1 hVt hrun
    exact ⟨v, H₃, tr, hev, hH₃, hrun C' hC'⟩
  -- The term of the recursor, related to its address by `(®_μ)`, which the relations `X` contain.
  obtain ⟨v, hv₀, hp₀ | ⟨R, hR, w, htw, hRw⟩⟩ := ht
  · cases Computesι.det hd hv₀ (hI _)
    obtain ⟨_, _, hp₁⟩ := hp₀
    exact (RunUnivRel.not_prop hd (hU T hT).1 (levelRel_prop_iff.1 hp₁)).elim
  · cases Computesι.det hd hv₀ (hI _)
    rw [HasRun.eq hd hR (.univ _ (levelRel_run_iff.2 (hU T hT).1))] at hRw
    have hwv := (ValidEqTerm₀.redStar_iff hd htw.1).1 htv
    have hC₀ : Cs.get (decl.names.idxOf T.name) = some ⟨0, C⟩ := (hidx h' T hh).symm ▸ hC
    obtain ⟨b, H₂, tr, hev, hH₂, hrun⟩ :=
      (hRw X hclosed).2 ϖ₀ H₁ (List.prefix_refl _) hH₁ (hwv.trans hwv.symm) C hC₀
    exact ⟨b, H₂, tr, hev, hH₂, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC htw.1 htv hrun⟩

/-- `r ∈ S`, by induction on `(eq_μ)`: the term of the skeleton of the instance evaluates to an
address that the erased recursor eliminates to the address of a value to which the recursor on a
term of the instance is related at the motive at the term, when every type of the block has one
constructor at most. -/
theorem RunsAs.recursor_skeleton (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {h' : Nat} {C : Term 0 (.var :: Γ)} (hh : decl.dataTypes[h']? = some T)
    (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∈ Mode.oneOne.erased) (h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ)) :
    ∃ a H₂ b H₃ tr, Eval P (ϖ₀ * r.run) H₁ E ((sig.skeleton D qs ps).target : Target Γ.length) a H₂ [] ∧
      EvalRec P ϖ₀ H₂ E r.run .omega (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a b H₃
        tr ∧ H₁.Extends H₃ ∧
      RunsAs sig ι P H₃ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, -, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  -- The erased recursor on the term of a skeleton of the type `D'` of a canonical term `v`, within
  -- the depth of the number of the types of the block minus that of the ancestors `A` of `D'`,
  -- evaluates, in each heap that extends the heap of this term, to the address of a value related
  -- to the recursor on `v` at the motive.
  let Pk : Name → Term 0 [] → Prop := fun D' v => ∀ (A : List Name) (d : Nat), A.Nodup →
    (∀ X ∈ A, X ∈ decl.names) → (∀ X ∈ A, Relation.TransGen (decl.Below I) D' X) →
    d + A.length = decl.names.length → ∀ ϖ' H₂ a H₃ tr₀, H.Extends H₂ →
    Eval P ϖ' H₂ E ((decl.skeleton I d D').target : Target Γ.length) a H₃ tr₀ →
    ValidTerm₀ sig ι v (.inst D' qs ls ps (as.subst σ)) → ∀ ϖ'' H', H₃.Extends H' →
    ∃ b H₄ tr, EvalRec P ϖ'' H' E r.run .omega Ns a b H₄ tr ∧ H'.Extends H₄ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        RunsAs sig ι P H₄ (f D' v) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))
  -- The relations of the canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`,
  -- and on the terms of whose skeletons the erased recursor evaluates as `Pk` states.
  let X : Name → TermRel := fun D' v w =>
    DataType.blockRel decl.dataTypes SM D' v w ∧ Acc (decl.Below I) D' ∧ Pk D' v
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ v w, T'.ctorRel T'.name (SM X) v w →
      X T'.name v w := by
    intro T' hT' v w hc
    obtain ⟨con, hcon, fs, fs₂, hvc, hwc, hSX⟩ := hc
    have hSX' := hmonoM X _ (fun _ _ _ h => h.1) T' hT' con hcon fs fs₂ hSX
    obtain ⟨ts, us', rfl, rfl, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hSX'
    have hrX := hrecM X T' hT' con hcon _ _ hSX
    have hcons : T'.constructors = [con] :=
      List.eq_singleton_of_mem_of_length_le_one hcon (h1 T' hT')
    -- The type is accessible for `≺`: each type below it is that of a recursive field.
    have hacc : Acc (decl.Below I) T'.name := Acc.intro _ fun D'' ⟨T₀, hT₀, hn₀, c₀, hc₀, hm⟩ => by
      cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT₀ hT' hn₀
      rw [hcons] at hc₀
      cases hc₀
      obtain ⟨_, _, _, _, _, _, hX₁⟩ :=
        Terms.RecRel.exists_of_mem _ (Telescope.length_recursion _ _) ts us' hrX hm
      exact hX₁.2.1
    refine ⟨DataType.blockRel_closed hmonoM hT'
      ⟨con, hcon, ts.terms, us'.terms, hvc, hwc, hSX'⟩, hacc, ?_⟩
    intro A d hA hAn hAD hdA _ H₂ a H₃ _ hH₂ hev hvv ϖ'' H' hH'
    -- The depth is not reached, since the ancestors are fewer than the types of the block.
    have hlt := TypeDeclaration.length_ancestors_lt hacc (TypeDeclaration.name_mem_names hT') hA
      hAn hAD
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    -- The term of the skeleton unfolds into the constructor of the case of the type.
    obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
    rw [TypeDeclaration.skeleton_succ hnd I hT' rfl hcons
      (Entry.constructorCase_of_cases (hd.cases_nodup hdecl) hi)] at hev
    cases hev with
    | @ctor _ _ _ H₂₀ _ _ _ bs _ hall =>
    have hH₂₀ : H₂₀.Extends H' := (List.prefix_append H₂₀ _).trans hH'
    have hHH' : H.Extends H' := hH₂.trans (hall.extends.trans hH₂₀)
    have hbl : bs.length = (con.params I).length := by
      rw [EvalAll.length_ofList _ hall, List.length_map, Telescope.length_recursion]
    -- The fields of the term of the skeleton are stored at the multiplicity `0`, and the grade of
    -- the recursor has no use at run time.
    have hπv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          r.run * π₀ ≤ r.run * p.usage.run := fun l p hlp => by
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨.zero, ?_, (by decide : ∀ (r : Grade) (π π' : Multiplicity),
        r ∈ Mode.oneOne.erased → r.run * π ≤ r.run * π') r _ _ hr⟩
      rw [Targets.multiplicities_ofList, List.map_map, List.getElem?_map,
        List.getElem?_eq_getElem hl, Option.map_some]
      congr 1
      simp only [Function.comp_apply]
      split <;> rfl
    -- The fields of the term of the skeleton are stored at the requirement `ω`, and the
    -- coefficients of their ownerships are `0`, since the grade of the recursor has no use at run
    -- time.
    have hκv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀ ϱ₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
            | none => (.zero, .erased))).requirements[l]? = some ϱ₀ ∧
          (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀) := fun l p hlp => by
      obtain ⟨π₀, hπ₀, -⟩ := hπv l p hlp
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨π₀, .omega, hπ₀, ?_, (by decide : ∀ (r a q : Grade) (π : Multiplicity),
        r ∈ Mode.oneOne.erased → (a * (r * q)).run ≤ .omega * (r.run * π)) r _ _ _ hr⟩
      rw [Targets.requirements_ofList, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hl)]
      rfl
    obtain ⟨b, H₄, tr, hevr, hH₄, hrun⟩ := RunsAs.recursor_ctor hd ⟨hdecl, hT, rfl⟩ hv hadm has
      hCs hCv hus hns hrec husr hg hχ hs hσ hEV hE hj hcon hi hvc hvv hHH' ϖ''
      (hH'.getElem? List.getElem?_concat_length) hπv hκv
      (fun l hl => by
        -- The fields of the term of the skeleton, which the recursor does not use, state nothing of
        -- the requirement of its recursion.
        have hlt := Telescope.lt_of_mem_positions _ 0 hl
        rw [Telescope.length_recursion, Nat.zero_add] at hlt
        obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, -⟩ := hκv l _ (List.getElem?_eq_getElem hlt)
        exact ⟨π₀, ϱ₀, hπ₀, hϱ₀, fun hne => absurd ((by decide : ∀ (g : Grade) (π : Multiplicity),
          g ∈ Mode.oneOne.erased → g.run * π = .zero) r π₀ hr) hne⟩)
      (fun _ => rfl)
      fun ts' hfs _ _ => by
        rw [hfs]
        -- The fields are erased, at grades erased since the grade of the recursor is.
        refine ⟨RunsAsArgs.of_erased ts' bs _ (fun l p hl' => (by decide : ∀ r p g x : Grade,
          r ∈ Mode.oneOne.erased → r * p ≤ g + x * r → g ∈ Mode.oneOne.erased) r p.usage
          (gs i l) _ hr (hg i j T' con l p hi hl')) hbl, ?_⟩
        -- The recursive results used at run time, on the terms of the skeletons of the recursive
        -- fields.
        refine EvalAll.recAt _ (fun D'' hD'' t u ⟨v₁, w₁, hcv, hcw, hX₁⟩ ϖa Ha b' Hb Rb hHa hevb
          hHb ϖb H'' hH'' => ?_) (Telescope.length_recursion _ _) _ ts us' (List.prefix_refl _)
          hall hrX
        have hDn := Telescope.mem_recursion hD''
        obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hDn
        have htu := hval T₃ hT₃ t u ⟨v₁, w₁, hcv, hcw, hX₁.1⟩
        have hVt := htu.trans htu.symm
        have hvv₁ := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        have hb : decl.Below I T₃.name T'.name := ⟨T', hT', rfl, con, hcons, hD''⟩
        obtain ⟨b'', H₅, tr', hev', hH₅, hrun'⟩ := hX₁.2.2 (T'.name :: A) d'
          (List.nodup_cons.2 ⟨fun hm => hacc.not_transGen_self (hAD _ hm), hA⟩)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact TypeDeclaration.name_mem_names hT'
            · exact hAn X hX)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact .single hb
            · exact .trans (.single hb) (hAD X hX))
          (by simp only [List.length_cons]; omega) ϖa Ha b' Hb Rb (hH₂.trans hHa) hevb
          (hvv₁.trans hvv₁.symm) ϖb H'' (hHb.trans (hH₂₀.trans hH''))
        refine ⟨b'', H₅, tr', hev', hH₅, fun C₄ hC₄ => ?_⟩
        obtain ⟨j₄, T₄, C₄', hj₄, hT₄, hC₄', rfl⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn hC₄
        obtain rfl : T₄ = T₃ := List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd)
          (List.mem_of_getElem? hj₄) hT₃ hT₄
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₄ hC₄' hcv.1 hVt
          (hrun' C₄' ((hidx j₄ _ hj₄).symm ▸ hC₄'))
    refine ⟨b, H₄, tr, hevr, hH₄, fun C' hC' => hrun C' ?_⟩
    rwa [hidx j T' hj] at hC'
  -- The term of the recursor computes to a canonical term that `(eq_μ)` relates, which the
  -- relations `X` contain.
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ := htv.2.1 fun ⟨v, hv', _, _, hk⟩ => by
    cases Computesι.det hd (hI _) hv'
    exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hUM T hT).1) hk
  cases Computesι.det hd (hI _) hv'
  have hX := ((HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T hT).1)) _ _).1 hrel) X
    hclosed
  have hww := (ValidEqTerm₀.redStar_iff hd hw₁.1).1 htv
  obtain ⟨a, H₂, hev, hH₂⟩ :=
    (decl.skeleton I decl.names.length T.name).target_isData.eval P (ϖ₀ * r.run) H₁ E
  obtain ⟨b, H₃, tr, hevr, hH₃, hrun⟩ := hX.2.2 [] _ List.nodup_nil (fun _ h => nomatch h)
    (fun _ h => nomatch h) rfl _ H₁ a H₂ [] hH₁ hev (hww.trans hww.symm) ϖ₀ H₂
    (List.prefix_refl _)
  refine ⟨a, H₂, b, H₃, tr, ?_, hevr, hH₂.trans hH₃, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC
    hw₁.1 htv (hrun C ((hidx h' T hh).symm ▸ hC))⟩
  rw [hd.skeleton ⟨hdecl, hT, rfl⟩ hq hp]
  exact hev


-- ADE: the cases `natrecₘ`, `prodrecₘ`, `unitrecₘ` and `emptyrecₘ` of `fundamental`, in
-- `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- `(rec)` keeps the validity at run time: the erasure of the recursor evaluates its term, or the
term of the skeleton of its instance when its grade `r` is erased, then the branch of the case of
its value. A recursor on a block of propositions has no constructor, in the mode `11ᵐ`, so that no
term of its instance is true and none is substituted. -/
theorem RunValid.recursor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {γ : GradeVector Γ.length} {t : Term 0 Γ} {h' : Nat} {C : Term 0 (.var :: Γ)}
    (hh : decl.dataTypes[h']? = some T) (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : r ∉ Mode.oneOne.erased → RunValid sig ι P hΓ ctx γ t (.inst D qs ls ps as))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      Mode.oneOne.grade * r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hr : (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) → r.mode = .oneOne)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases = []) :
    RunValid sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ χ) (.recursor r ς χ' D qs ls ps as t κ Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  intro w σ H E V hσ hEV hE
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS := Mode.erasesUncounted .oneOne
  have hEχ : RunsAsSubst sig ι P H ctx χ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  have hg' : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r := fun i j T' con l p hi hl' => by
    have h₁ := hg i j T' con l p hi hl'
    rwa [show Mode.oneOne.grade = Grade.one from rfl, Grade.modality.semiring.one_mul] at h₁
  have htσ : ValidTerm₀ sig ι (t.subst σ) ((Term.inst T.name qs ls ps as).subst σ) :=
    ht.2 σ σ hσ
  have hCσ : (C.subst₀ (Subst₀.single t)).subst σ =
      (C.subst (Subst.lift σ)).subst₀ (Subst₀.single (t.subst σ)) :=
    Term.subst_subst₀_of (Subst₀.Swaps.single _ _) C
  rw [hCσ]
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality with
  | prop =>
    -- No term of an instance of a block of propositions without constructor is true.
    have hasσ := has.2 σ σ hσ
    obtain ⟨S, hP, hmono, -, -, -⟩ := hv.propRel hd hdecl hq hl hp hadm hasσ hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have hI : Computesι sig ι (.inst T.name qs ls ps (as.subst σ))
        (.inst T.name qs ls ps (as.subst σ)) := ⟨.refl _, .inst _ _ _ _ _⟩
    obtain ⟨v', R', hv', hR', hrel⟩ := htσ.2.2 ⟨_, hI, _, _, hP'⟩
    cases Computesι.det hd hI hv'
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      (HasEq.unique hd hR' (.prop _ _ hP' fun _ _ => .rfl) _ _).1 hrel
    obtain ⟨T₀, hT₀, -, con₀, hcon₀, -⟩ := DataType.blockTruth_inv hmono htrue
    obtain ⟨i, j, hi, -⟩ := TypeDeclaration.exists_cases hT₀ hcon₀
    rw [hprop hs] at hi
    cases hi
  | type =>
    by_cases hrS : r ∈ Mode.oneOne.erased
    · -- The term of the skeleton of the instance stands for the term.
      have h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1 := fun T' hT' => by
        refine Nat.le_of_not_lt fun h2 => ?_
        exact (by decide : ∀ r : Grade, r ∈ Mode.oneOne.erased → r.mode ≠ .oneOne) r hrS
          (hr ⟨T', hT', h2⟩)
      obtain ⟨a, H₂, b, H₃, tr, hev, hevr, hH₃, hrun⟩ := RunsAs.recursor_skeleton hd h hv hadm
        has hh hC hCs hCv hus hns hrec husr hg' hχ hs hrS h1 hσ hEV hEχ (List.prefix_refl H) w htσ
      refine ⟨b, H₃, [] ++ tr, ?_, hH₃, hrun⟩
      show Eval P w H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _) b H₃ _
      rw [ite_eq_left hrS, ite_eq_left hrS]
      exact .recursor hev hevr
    · -- The term evaluates to the address of its value.
      have hγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h (hS.mul _ _ hrS (hS.add _ _ h'))) hE
      obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr hrS (w * r.run) σ H E V hσ hEV hγ
      obtain ⟨b, H₂, tr₂, hevr, hH₂, hrun⟩ := RunsAs.recursor hd h hv hadm has hh hC hCs hCv hus hns
        hrec husr hg' hχ hs hrS hσ hEV hEχ hH₁ w htσ hta
      refine ⟨b, H₂, tr₁ ++ tr₂, ?_, hH₁.trans hH₂, hrun⟩
      show Eval P w H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _) b H₂ _
      rw [ite_eq_right hrS, ite_eq_right hrS]
      exact .recursor hev hevr


end

end Sic.Core
