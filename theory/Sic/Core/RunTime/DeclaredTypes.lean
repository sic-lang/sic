module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Levels
import Sic.Core.RunTime.Monotonicity
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Run Time of the Declared Types

The constructors of the data types of a meaningful declaration at run time: a constructor applied
to arguments of its fields, allocated with the addresses of their values, is related to its address
at its instance, when each argument is related to its address at the type of its field, as `(®_μ)`
relates it once unfolded, `(®_c)` relating the fields by the relation of run time of the telescope
of the fields, whose recursive fields are related by `(®_μ)`, as their types, the instances of the
block, say.
Conversely, the relation of run time of an instance of a data type of a type is `(®_μ)` of its
block, and the arguments that the relation of the fields relates to addresses are related to them at
their fields, which the recursors read.

The relation of run time of the fields that the graph gives is that of the fields at the values of
the levels, which the meaning of the declaration makes meaningful, and that the declaration tells
the recursive fields of, so that the arguments are related at these fields, then at the fields at
the levels of the instance, which differ from them only by levels of the same values.

ADE prove the validity of their constructors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- A term related to an address at a type that computes to the type of a field is related to it by
the relation of run time of the field. -/
theorem RunFieldRel.of_runsAs (hd : sig.Distinct) {n : Nat} {v A t : Term 0 []} {R : RunRel}
    {H : Heap} {b : Nat} (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R)
    (hA : Computesι sig ι A v) (h : RunsAs sig ι P H t b A) : R H t b := by
  obtain ⟨v', hA', h⟩ := h
  cases Computesι.det hd hA hA'
  have huniv : ∀ m R₀, (levelRel sig ι m).run P v R₀ → R₀.computed sig ι H t b :=
    fun m R₀ hR₀ => by
      rcases h with ⟨_, _, hp⟩ | ⟨Q, hQ, htQ⟩
      · exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 hR₀) (levelRel_prop_iff.1 hp)).elim
      · rw [HasRun.eq hd hQ (.univ m hR₀)] at htQ
        exact htQ
  cases hR with
  | univ h' => exact huniv n _ (levelRel_run_iff.2 h')
  | univBelow m _ h' => exact huniv m _ h'
  | prop _ => trivial
  | propBelow _ _ _ => trivial

/-- Arguments of a closed telescope of the graph of run time, which the meaning relates to
themselves and which are related to addresses at its fields, are related to them by the relation of
run time of the terms of its fields, when its recursive fields are instances whose terms are related
by the relations of these fields. -/
theorem RunTelRel.of_runsAsArgs (hd : sig.Distinct) {n : Nat} {inst : Name → Term 0 []}
    {H : Heap} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : RunFieldsRel} →
      {rs : Nat → Option RunRel} → {rsN : Nat → Option Name} →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S → Θ.RecHeads sig ι inst rsN →
      (∀ i R, rs i = some R → ∃ D, rsN i = some D ∧
        ∀ t b, RunsAs sig ι P H t b (inst D) → R H t b) →
      (g : Nat → Grade) → (∀ l p, ps[l]? = some p → p.usage ∉ Mode.oneOne.erased →
        g l ∉ Mode.oneOne.erased) →
      (ts : Args 0 [] ps) → EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
      (bs : List Nat) → RunsAsArgs sig ι P H g ts bs Θ → S H ts.terms bs
  | [], .nil, _, _, _, h', _, _, _, _, .nil, _, [], _ => by cases h'; trivial
  | [], .nil, _, _, _, _, _, _, _, _, .nil, _, _ :: _, h => (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, _, _, _, _, _, _, .cons _ _, _, [], h => (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, _, h', hH, hR, g, hg, .cons t ts, h, b :: bs, hargs => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    obtain ⟨hb, hbs⟩ := hargs
    rw [Telescope.RecHeads] at hH
    have hg' : ∀ l (p : Parameter), _ → p.usage ∉ Mode.oneOne.erased →
        g (l + 1) ∉ Mode.oneOne.erased :=
      fun l p hl => hg (l + 1) p hl
    cases h' with
    | cons hA hF hRf G hG _ =>
      have hFtt := hF.of_validEqTerm hA ht
      exact And.intro ⟨hFtt, fun hp => hRf.of_runsAs hd hA (hb (hg 0 _ rfl hp))⟩
        (RunTelRel.of_runsAsArgs hd (hG t hFtt) (hH.2 t ht) (fun i R h => hR (i + 1) R h) _ hg'
          ts hts bs hbs)
    | recursive hrs G hG =>
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      exact And.intro (fun hp => hRD t b (hH.1 D hD ▸ hb (hg 0 _ rfl hp)))
        (RunTelRel.of_runsAsArgs hd (hG t) (hH.2 t ht) (fun i R h => hR (i + 1) R h) _ hg' ts hts
          bs hbs)

/-- A term related to an address by the relation of run time of the type of a field is related to
it at a type that computes to this type: the converse of `RunFieldRel.of_runsAs`. -/
theorem RunFieldRel.runsAs {n : Nat} {v A t : Term 0 []} {R : RunRel} {H : Heap} {b : Nat}
    (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R) (hA : Computesι sig ι A v)
    (h : R H t b) : RunsAs sig ι P H t b A := by
  cases hR with
  | univ h' => exact ⟨v, hA, .inr ⟨_, .univ n (levelRel_run_iff.2 h'), h⟩⟩
  | univBelow m _ h' => exact ⟨v, hA, .inr ⟨_, .univ m h', h⟩⟩
  | prop h' => exact ⟨v, hA, .inl ⟨n, _, levelRel_prop_iff.2 h'⟩⟩
  | propBelow m _ h' => exact ⟨v, hA, .inl ⟨m, _, h'⟩⟩

/-- Arguments of a closed telescope of the graph of run time, which the meaning relates to
themselves and which its relation of run time relates to addresses, are related to them at its
fields, when the relations of its recursive fields relate only terms related at their instances: the
converse of `RunTelRel.of_runsAsArgs`. -/
theorem RunsAsArgs.of_runTelRel {n : Nat} {inst : Name → Term 0 []} {H : Heap} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : RunFieldsRel} →
      {rs : Nat → Option RunRel} → {rsN : Nat → Option Name} →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S → Θ.RecHeads sig ι inst rsN →
      (∀ i R, rs i = some R → ∃ D, rsN i = some D ∧
        ∀ t b, R H t b → RunsAs sig ι P H t b (inst D)) →
      (g : Nat → Grade) → (∀ l p, ps[l]? = some p → g l ∉ Mode.oneOne.erased →
        p.usage ∉ Mode.oneOne.erased) →
      (ts : Args 0 [] ps) → EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
      (bs : List Nat) → S H ts.terms bs → RunsAsArgs sig ι P H g ts bs Θ
  | [], .nil, _, _, _, _, _, _, _, _, .nil, _, [], _ => trivial
  | [], .nil, _, _, _, h', _, _, _, _, .nil, _, _ :: _, h => by cases h'; exact (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, _, h', _, _, _, _, .cons _ _, _, [], h => by
    cases h' <;> exact (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, _, h', hH, hR, g, hg, .cons t ts, h, b :: bs, hS => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    rw [Telescope.RecHeads] at hH
    have hg' : ∀ l (p : Parameter), _ → g (l + 1) ∉ Mode.oneOne.erased →
        p.usage ∉ Mode.oneOne.erased :=
      fun l p hl => hg (l + 1) p hl
    cases h' with
    | cons hA _ hRf G hG _ =>
      obtain ⟨⟨hFtt, hb⟩, hbs⟩ := hS
      exact And.intro (fun hp => hRf.runsAs hA (hb (hg 0 _ rfl hp)))
        (RunsAsArgs.of_runTelRel (hG t hFtt) (hH.2 t ht) (fun i R h => hR (i + 1) R h) _ hg' ts
          hts bs hbs)
    | recursive hrs G hG =>
      obtain ⟨hb, hbs⟩ := hS
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      exact And.intro (fun hp => hH.1 D hD ▸ hRD t b (hb (hg 0 _ rfl hp)))
        (RunsAsArgs.of_runTelRel (hG t) (hH.2 t ht) (fun i R h => hR (i + 1) R h) _ hg' ts hts bs
          hbs)

/-- The relation of run time of an instance of a data type of a type is `(®_μ)` of its block, for
relations of the fields that the graph of a level gives, in a signature whose names are distinct. -/
theorem HasRun.data (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasDataType D decl T)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {R : RunRel}
    (hR : HasRun sig ι P (.inst D qs ls ps as) R)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ n S, (∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m)
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) ∧
      R = DataType.runBlockRel sig decl.dataTypes S D := by
  cases hR with
  | prop n b hb _ =>
    cases levelRel_prop_iff.1 hb with
    | data h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, -⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata hc _ _ _ hv' => exact (hd.inst_data_codata h hc hv').elim
  | univ n hn =>
    cases levelRel_run_iff.1 hn with
    | data h' _ _ _ hv' _ _ S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasDataType_unique h h'
      cases eq_of_heq has
      exact ⟨n, S, hS, rfl⟩
    | codata hc _ _ _ hv' => exact (hd.inst_data_codata h hc hv').elim

-- ADE: none.
/-- `(c)` at run time, closed: a constructor of a data type of `Σ`, whose type declaration is
meaningful, applied to arguments of its fields that the meaning relates to themselves, is related at
its instance to the address of a value of its case whose fields are the addresses to which the
arguments are related, in a signature whose names are distinct: a proof of a proposition is related
to every address, and a term of a type, by `(®_μ)` unfolded once. -/
theorem RunsAs.ctor (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst)
    {ts : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      ts.toSubst ts.toSubst)
    {i : Nat} (hi : sig.constructorCase D con.name = some i) {H : Heap} {a : Nat} {bs : List Nat}
    (ha : H[a]? = some (.ctor i bs))
    (hbs : RunsAsArgs sig ι P H (Parameter.grades (con.params (.ofLists qs ps hq hp))) ts bs
      (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) :
    RunsAs sig ι P H (.ctor D qs ls ps as con.name ts.terms) a (.inst D qs ls ps as) := by
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : ∀ D', Computesι sig ι (.inst D' qs ls ps as) (.inst D' qs ls ps as) :=
    fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · obtain ⟨S, hS, hU⟩ := hv.runUnivRel hd hdecl hq hl hp hadm has hs P
    have hR : ∀ T' ∈ decl.dataTypes, HasRun sig ι P (.inst T'.name qs ls ps as)
        (DataType.runBlockRel sig decl.dataTypes S T'.name) := fun T' hT' =>
      .univ _ (levelRel_run_iff.2 (hU T' hT').1)
    have ihm : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
        (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
        RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
    have ihmono : ∀ m,
        m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
        RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
    have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
        ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
      fun X Y hXY T hT c hc H =>
        RunTelRel.mono hd ihmono (List.prefix_refl H) (hS X T hT c hc) _ _ (hS Y T hT c hc)
          (fun _ => Option.rel_map (fun D' _ _ => RunRel.computed_mono (hXY D' H)) _)
    refine ⟨_, hw _, .inr ⟨_, hR T hT, _, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩,
      DataType.runBlockRel_fold hmono hT ⟨con, hc, i, ts.terms, bs, ⟨qs, ls, ps, _, as, rfl⟩, hi, ha,
        ?_⟩⟩⟩
    -- The fields at the values of the levels, which the meaning of the declaration gives.
    have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
      fun i => Level.ofNat_closedValue _
    have has' := EqSubst.levelEquiv
      (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
    have hn : (((decl.sort (.ofLists qs ps hq hp)).atLevels
          fun i => (ls.getFin hl i).closedValue).level.closedValue)
        = ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue :=
      Level.subst_equiv hls _ Fin.elim0
    have hΘ : Telescope.LevelEquiv (((con.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) :=
      (Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _)
    have hF := (hv.fields _ hadm hT hc fun i => (ls.getFin hl i).closedValue).2 _ _ has'
    let X : Name → RunRel := DataType.runBlockRel sig decl.dataTypes S
    obtain ⟨S', h₁, -⟩ := hF.runTelRel hd P hs fun D' => (X D').computed sig ι
    have h₁' := hn ▸ RunTelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₁ hΘ
    -- The recursive fields are the instances of the block, whose terms `(®_μ)` relates.
    have hrec : ∀ j R, ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names j).map
          (fun D' => (X D').computed sig ι) = some R →
        ∃ D', (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names j = some D' ∧
          ∀ t b, RunsAs sig ι P H t b (((decl.blockInstance (.ofLists qs ps hq hp) D'
            (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
            as.toSubst) → R H t b := fun j R hj => by
      cases hr : (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names j with
      | none => rw [hr] at hj; cases hj
      | some D' =>
        rw [hr] at hj
        cases hj
        refine ⟨D', rfl, fun t b htb => ?_⟩
        obtain ⟨T', hT', rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.recursionAt_mem hr)
        exact RunFieldRel.of_runsAs hd (.univ (hU T' hT').1) (hw _)
          (htb.levelEquiv (decl.blockInstance_atLevels_subst hq hl hp as T'.name))
    have hE : EqSubst sig ι (Context.empty.append (((con.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)) ts.toSubst ts.toSubst :=
      EqSubst.levelEquiv (Context.LevelEquiv.append .empty hΘ.symm) hts
    have hS' := RunTelRel.of_runsAsArgs hd h₁ hF.recHeads hrec _
      (fun _ _ hl hp => (Parameter.grades_of_getElem? hl).symm ▸ hp) ts hE bs
      (hbs.levelEquiv hΘ.symm)
    exact (RunTelRel.congr hd (hn ▸ ihm) (hn ▸ ih) (hS X T hT con hc) _ _ h₁'
      (fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) H ts.terms bs).2 hS'
  · obtain ⟨S, hP, -⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    exact ⟨_, hw _, .inl ⟨_, _, levelRel_prop_iff.2 (hP T hT).1⟩⟩

-- ADE: none.
/-- `(c)` at run time: a constructor of a data type of `Σ`, whose type declaration is meaningful,
applied to arguments of its fields valid at run time with the grades `γ`, is valid at run time at its
instance with the grades `γ`, in a signature whose names are distinct: its erasure evaluates its
arguments, then allocates a value of its case with their addresses. -/
theorem RunValid.ctor (hd : sig.Distinct) {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ}
    {γ : GradeVector Γ.length} {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {ts : Args 0 Γ (con.params (.ofLists qs ps hq hp))}
    (hts : ValidArgsΓ sig ι ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
    (hrun : RunValidArgs sig ι P hΓ ctx γ ts
      (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) :
    RunValid sig ι P hΓ ctx γ (.ctor D qs ls ps as con.name ts.terms) (.inst D qs ls ps as) := by
  intro σ H E hσ hE
  have hfg := hd.fieldGrades h hc hq hp
  obtain ⟨hdecl, hT, rfl⟩ := h
  obtain ⟨i, hi⟩ := Signature.constructorCase_of_mem hdecl hT hc
  have he : (Term.ctor T.name qs ls ps as con.name ts.terms).erase sig Mode.oneOne.erased hΓ =
      .ctor i (ts.terms.erase sig Mode.oneOne.erased hΓ
        ((con.params (.ofLists qs ps hq hp)).map (·.usage))) := by
    rw [Term.erase, hi, hfg]
    rfl
  obtain ⟨bs, H', hevs, hH', hruns⟩ := hrun σ H E hσ hE
  have hH'' : H'.Extends (H' ++ [.ctor i bs]) := List.prefix_append _ _
  refine ⟨H'.length, H' ++ [.ctor i bs], he ▸ .ctor hevs, hH'.trans hH'', ?_⟩
  have hts' := hts.2 σ σ hσ
  rw [Constructor.fieldsAt_subst] at hts' hruns
  have hc' := RunsAs.ctor hd ⟨hdecl, hT, rfl⟩ hv hc hq hl hp hadm (has.2 σ σ hσ) hts' hi
    List.getElem?_concat_length (hruns.mono hd hH'')
  rw [Args.terms_subst] at hc'
  exact hc'

end

end Sic.Core
