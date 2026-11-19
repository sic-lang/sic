module

public import Sic.Core.RunTime.Relation.Recursors.Evaluation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Relation.Substitution
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Constructors at Run Time

The erased recursor eliminates the address of a constructor of a type of a block by the branch of
its case, which `RunsAs.recursor_ctor` states, as both cases of the recursors at run time do.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- Terms related to themselves at the recursive fields by `Q` are related to themselves by `Q'`,
when `Q'` relates each term to itself that `Q` does. -/
theorem Terms.RecRel.of_diag {Q Q' : Name → TermRel} :
    (rs : List (Option Name)) → {ts : Terms 0 []} →
      (∀ D, some D ∈ rs → ∀ t, Q D t t → Q' D t t) → Terms.RecRel Q rs ts ts →
        Terms.RecRel Q' rs ts ts
  | some D :: rs, .cons _ _, h, hqs =>
    ⟨h D (List.mem_cons_self ..) _ hqs.1,
      Terms.RecRel.of_diag rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hqs.2⟩
  | none :: rs, .cons _ _, h, hs =>
    Terms.RecRel.of_diag (Q := Q) rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hs
  | [], _, _, _ | some _ :: _, .nil, _, _ | none :: _, .nil, _, _ => trivial


/-! ## Branches -/

section

variable {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {decl : TypeDeclaration} {D : Name}
  {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {as : InstanceArgs 0 Γ decl.scope} {r ς χ' : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
  {χ : GradeVector Γ.length} {δs : Nat → GradeVector Γ.length} {gs : Nat → Nat → Grade}
  {κ : Universe 0}

/-- The branches of a recursor are valid at run time: each branch, in the context extended by the
fields of its constructor and by its recursive results, at the grades of its variables. -/
def RunValidBranches (sig : Signature) (ι : Interpretation) (P : Program) (hΓ : Γ.FirstOrder)
    (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) (as : InstanceArgs 0 Γ decl.scope) (Cs : Motives 0 Γ)
    (us : Branches 0 Γ) (δs : Nat → GradeVector Γ.length) (gs : Nat → Nat → Grade) : Prop :=
  ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
    con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
    us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
      (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
    RunValid sig ι P ((hΓ.extend _).extend _)
      ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
      (((δs i).extendGrades (gs i) (con.params (.ofLists qs ps hq hp))).extendResults
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
        (con.params (.ofLists qs ps hq hp))) u
      ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
        (Ren.weakenN _))

/-- The motives of a block of data types, one for each type, give one to each name of the block. -/
theorem Motives.get_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩) {D' : Name}
    (hD' : D' ∈ decl.names) : ∃ C, Cs.get (decl.names.idxOf D') = some ⟨0, C⟩ := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  rw [TypeDeclaration.idxOf_dataTypes hnd hj]
  exact hCs j T' hj

/-- The motive of a name of a block of data types in its motives substituted by `σ` is the motive of
the type of this name, substituted. -/
theorem Motives.get_subst_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (σ : Subst 0 [] Γ) {D' : Name} (hD' : D' ∈ decl.names) {C}
    (hC : (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩) :
    ∃ j T' C', decl.dataTypes[j]? = some T' ∧ T'.name = D' ∧ Cs.get j = some ⟨0, C'⟩ ∧
      C = C'.subst (Subst.lift σ) := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  obtain ⟨C', hC'⟩ := hCs j T' hj
  rw [TypeDeclaration.idxOf_dataTypes hnd hj, Motives.get_subst σ hC'] at hC
  cases hC
  exact ⟨j, T', C', hj, rfl, hC', rfl⟩

/-- A recursor on a term is related at the motive at the term as on the value of the term. -/
theorem RunsAs.recursor_of_redStar (hd : sig.Distinct)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    {σ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ σ) {j : Nat}
    {T' : DataType decl.sorts decl.grades decl.levels decl.scope} {C' : Term 0 (.var :: Γ)}
    (hj : decl.dataTypes[j]? = some T') (hCj : Cs.get j = some ⟨0, C'⟩) {t v : Term 0 []}
    (htv : RedStar (sig.interpret ι) t v)
    (hvt : ValidTerm₀ sig ι t (.inst T'.name qs ls ps (as.subst σ))) {H : Heap} {b : Nat}
    (hrun : RunsAs sig ι P H
      (.recursor r ς χ' T'.name qs ls ps (as.subst σ) v κ (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))) :
    RunsAs sig ι P H (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  have hvv := (ValidEqTerm₀.redStar_iff hd htv).1 hvt
  have hrv := hrec j T' C' hj hCj σ hσ v (hvv.trans hvv.symm)
  have hmot := (hCv j T' C' hj hCj).motive hσ hvv
  exact (RunsAs.redStar_iff hd (RedStar.recursor htv)).2 (hrun.conv hd hrv.2 hmot.2)

/-- The erased recursor eliminates the address of a constructor of a type of the block, by the
branch of its case, to the address of a value to which the recursor on a term of the instance that
computes to this constructor is related at the motive at the term, when the fields of the
constructor are related to their addresses at their grades in the branch, and the recursive
results used at run time evaluate to addresses related to them. -/
theorem RunsAs.recursor_ctor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
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
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {σ : Subst 0 [] Γ} {H : Heap}
    {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V)
    (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {i j : Nat} {T' : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T') (hcon : con ∈ T'.constructors)
    (hi : decl.cases[i]? = some (j, T', con)) {fs : Terms 0 []} {w : Term 0 []}
    (hw : w.IsCtor T'.name con.name fs)
    (hwv : ValidTerm₀ sig ι w (.inst T'.name qs ls ps (as.subst σ))) {H' : Heap}
    (hH' : H.Extends H') (ϖ₀ : Multiplicity) {a : Nat} {πv ϱv : List Multiplicity}
    {bs : List Nat} (ha : H'[a]? = some (.ctor i πv ϱv bs))
    (hπv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀, πv[l]? = some π₀ ∧ r.run * π₀ ≤ r.run * p.usage.run)
    (hκv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
        (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀))
    {ϱ : Multiplicity}
    (hϱv : ∀ l ∈ ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
        (fun y => y.1.map fun _ => y.2), ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
          (r.run * π₀ ≠ .zero → ϱ ≤ ϱ₀ * (r.run * π₀)))
    (hϱ0 : r.run = .zero → ϱ = .omega)
    (hfr : ∀ ts : Args 0 [] (con.params (.ofLists qs ps hq hp)), ts.terms = fs →
      EqSubst sig ι (Context.empty.append
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ))) ts.toSubst ts.toSubst →
      Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms →
      RunsAsArgs sig ι P H' (gs i) ts bs
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)) ∧
      Terms.RecAt (fun D' t b => ∀ ϖ' H'', H'.Extends H'' → ∃ v H₂ tr,
        EvalRec P ϖ' H'' E r.run ϱ (us.erase sig Mode.oneOne.erased hΓ r
          (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) b v H₂
          tr ∧ H''.Extends H₂ ∧
        ∀ C, (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩ →
          RunsAs sig ι P H₂ (.recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) v
            (C.subst₀ (Subst₀.single t)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) (us.grades i) ts.terms bs) :
    ∃ v H₃ tr, EvalRec P ϖ₀ H' E r.run ϱ (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a v H₃ tr ∧
      H'.Extends H₃ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ →
        RunsAs sig ι P H₃ (.recursor r ς χ' T'.name qs ls ps (as.subst σ) w κ (Cs.subst σ) (us.subst σ))
          v ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hT' : T' ∈ decl.dataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, -, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  -- The meaning of the constructor gives the arguments of its fields.
  obtain ⟨qs', ls', ps', Δ', as', rfl⟩ := hw
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ := hwv.2.1 fun ⟨v, hv', _, _, hk⟩ => by
    cases Computesι.det hd (hI _) hv'
    exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hUM T' hT').1) hk
  cases Computesι.det hd (hI _) hv'
  cases Computesι.det hd hw₁ ⟨.refl _, .ctor _ _ _ _ _ _ _⟩
  have hrel' := (HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T' hT').1)) _ _).1 hrel
  obtain ⟨T'', hT'', hn'', con'', hcon'', fs₁, fs₂, hv₁, -, hS''⟩ :=
    DataType.blockRel_inv hmonoM hrel'
  cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT'' hT' hn''
  obtain ⟨-, hcn, rfl⟩ := hv₁.inj ⟨_, _, _, _, _, rfl⟩
  cases List.eq_of_nodup_map (hd.constructors_nodup ⟨hdecl, hT', rfl⟩) hcon'' hcon hcn
  have hself := (hiffM T' hT' con hcon).2.2 _ _ hS''
  obtain ⟨ts, -, rfl, -, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hself
  have hts := ((hiffM T' hT' con hcon).1 ts ts).1 hself
  have hrecV : Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms :=
    Terms.RecRel.mono _ (fun D hD t₁ t₂ h₁₂ => by
        obtain ⟨T₃, hT₃, rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.mem_recursion hD)
        have h' := hval T₃ hT₃ t₁ t₂ h₁₂
        exact h'.trans h'.symm)
      (hrecM _ T' hT' con hcon _ _ hself)
  obtain ⟨hfa, hQ⟩ := hfr ts rfl hts hrecV
  -- The case of the constructor, its branch and its recursive results.
  obtain ⟨u, hu⟩ := hus i j T' con hi
  have hn := hns i j T' con hi
  have hrn := Telescope.recursion_eq_map_nest decl.names (con.fields (.ofLists qs ps hq hp))
  obtain ⟨Rt, hRt⟩ := Constructor.results_isSome con (.ofLists qs ps hq hp)
    (fun _ hD' => Motives.get_idxOf hT hnd hCs hD') hn
  -- The terms of the recursive results, the recursor on each recursive field.
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  obtain ⟨rs, hrsf, hrs⟩ : ∃ rs,
      ts.results f ((con.fields (.ofLists qs ps hq hp)).nest decl.names) = some rs ∧ Constructor.ResultTerms sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp)
        decl.names (ls.getFin hl) (as.subst σ)
        (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
        (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ts rs := by
    obtain ⟨rs, h₁, h₂⟩ := Constructor.resultTerms_results (sig := sig) (v := ⟨κ.quality, r, ς⟩)
      (names := decl.names) (ls.getFin hl) (as.subst σ)
      (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
      (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ts hn
    rw [funext fun D'' => funext fun t =>
      Term.recursorAt_subst₀ r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ) D'' t] at h₁
    exact ⟨rs, h₁, h₂⟩
  obtain ⟨gs₀, hgs, hget⟩ := Branches.get_erase sig Mode.oneOne.erased hΓ r us
    (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams T.name qs ps).getD [])
    hu
  -- The positions of the recursive fields of each case.
  let rfs : List (List Nat) := decl.cases.map fun x =>
    ((x.2.2.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
      fun y => y.1.map fun _ => y.2
  have hrfs : sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ' = rfs.map (·.map .field) := by
    rw [hd.recursiveResults ⟨hdecl, hT, rfl⟩ hq hp,
      TypeDeclaration.recursiveResults_of_not_nested hns]
    rfl
  rw [hrfs] at hQ hget ⊢
  rw [RecursiveResult.headD_drop_map_field] at hget
  simp only [RecursiveResult.getD_map_field] at hget
  rw [hgs] at hQ
  have hpos : (rfs.drop i).headD [] =
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
        fun y => y.1.map fun _ => y.2 :=
    List.headD_drop (by rw [List.getElem?_map, hi]; rfl)
  have hpos' : (rfs.drop i).headD [] =
      (((con.fields (.ofLists qs ps hq hp)).nest decl.names).map Nest.blockName).zipIdx.filterMap
        fun y => y.1.map fun _ => y.2 := hrn ▸ hpos
  obtain ⟨vs, H₂, tr₁, hevs, hH₂, hruns⟩ := Args.evalResults hd
    ((con.fields (.ofLists qs ps hq hp)).nest decl.names) (Telescope.length_nest _ _)
    ts 0 bs List.drop_zero (RunsAsArgs.length hfa) gs₀.toList gs₀.length_toList (hrn ▸ hQ)
    (Constructor.results_subst_append hRt σ ts) hrsf ϖ₀ H' (List.prefix_refl _)
  -- The branch, at the substitution of its context by `σ`, the fields and the results.
  have hres := EqSubst.results (sig := sig) (ι := ι) (f₁ := f) (f₂ := f) _ ts ts
    (Constructor.results_subst_append hRt σ ts) hrsf hrsf
    (Terms.RecRel.of_diag _ (fun D hD t₁ hVt C hC => by
        obtain ⟨j₃, T₃, C₃, hj₃, rfl, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ
          (Telescope.mem_recursion (hrn ▸ hD)) hC
        exact hrec j₃ T₃ C₃ hj₃ hC₃ σ hσ t₁ hVt) (hrn ▸ hrecV))
  have hEqbr := (EqSubst.append_append_iff _ Rt _ _ _ _).2
    ⟨(EqSubst.append_append_iff ctx _ σ σ _ _).2
      ⟨hσ, by rw [Constructor.fieldsAt_subst]; exact hts⟩, hres⟩
  have hχi : RunsAsSubst sig ι P H₂ ctx (δs i) σ V :=
    RunsAsSubst.of_counted ctx (fun x hδ => (by decide : ∀ c d x : Grade,
        c ≤ d + x → d ∉ Mode.oneOne.erased → c ∉ Mode.oneOne.erased) _ _ _
        (hχ i j T' con hi x) hδ) (hE.mono hd (hH'.trans hH₂))
  have hfa₂ : RunsAsArgs sig ι P H₂ (gs i) ts bs
      ((con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as).subst σ) := by
    rw [Constructor.fieldsAt_subst]
    exact hfa.mono hd hH₂
  have hσr := RunsAsSubst.append _ Rt (RunsAsSubst.append ctx _ hχi hfa₂) hruns
  obtain ⟨C', hC'⟩ : ∃ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ := hCs j T' hj
  have hbr := husr i j T' con C' Rt u hi hC' hRt hu
  rw [hgs, GradeVector.extendResults_resultGrades] at hbr
  -- The branch binds its variables to cells, at the multiplicities of its binders.
  let πs₀ : Fin (con.params (.ofLists qs ps hq hp)).length → Multiplicity := fun l =>
    r.fieldMultiplicity
      (((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?.map (·.usage))
      ((((rfs.drop i).headD []).map RecursiveResult.field).zip gs₀.toList |>.find?
        fun x => x.1.fieldPosition == some (l : Nat))
  let πs₀' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length → Multiplicity :=
    fun j => gs₀[j].run
  have hlen : ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)).length = (bs ++ vs).length := by
    simp only [List.length_map, List.length_append, List.length_ofFn, RunsAsArgs.length hfa,
      RunsAsArgs.length hruns]
  let H₂' := H₂.bind ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)) (bs ++ vs)
  have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
  have hB : H₂'.Binds ((List.range' H₂.length (bs ++ vs).length).reverse ++ E)
      (vs.reverse ++ (bs.reverse ++ V)) := by
    have h' := (Heap.binds_bind H₂ hlen).reverse.append (hEV.mono (hH'.trans (hH₂.trans hH₂')))
    rwa [List.reverse_append, List.append_assoc] at h'
  obtain ⟨v, H₃, tr₂, hev, hH₃, hrun⟩ := hbr ϖ₀ _ H₂' _ _ hEqbr hB (hσr.mono hd hH₂')
  -- The erased recursor steps to the erased branch.
  have hks : List.ofFn
      (fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?) =
      List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field l)
        gs₀.toList (((((con.fields (.ofLists qs ps hq hp)).nest decl.names).map
          Nest.blockName).zipIdx 0).filterMap fun y => y.1.map fun _ => y.2) := by
    rw [hpos']
    exact List.ofFn_ite_getElem? _ _ RecursiveResult.ofPosition gs₀ _
      (Telescope.length_positions _ (Telescope.length_nest _ _) hn 0)
  have hπs' : List.ofFn πs₀' = gs₀.toList.map Grade.run := by
    apply List.ext_getElem <;> simp [πs₀']
  rw [← hπs'] at hevs
  -- The parameter of each field, which the signature gives the case.
  have hfs : ∀ (l : Nat) (p' : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p' →
      ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[l]? = some p' :=
    fun l p' hp' => by
      rw [hd.caseFieldParams ⟨hdecl, hT, rfl⟩ hq hp, Option.getD_some,
        List.headD_drop (by rw [List.getElem?_map, hi]; rfl), hp']
  -- The uses of each field by the branch are within those that the constructor allows.
  have hπ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length,
      ∃ π₀, πv[(l : Nat)]? = some π₀ ∧ r.run * π₀ ≤ πs₀ l + r.run * recursionsAt
      (List.ofFn fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?)
      (List.ofFn πs₀') l := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, hπ₀, hle⟩ := hπv l p' hp'
    refine ⟨π₀, hπ₀, ?_⟩
    have hgl := hg i j T' con l p' hi hp'
    rw [hgs] at hgl
    have he := Grade.fieldMultiplicity_positions r p'.usage
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) gs₀.toList 0 l hn
    have hr := Telescope.recursionsAt_positions Mode.oneOne.erased (by decide)
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) gs₀.toList 0 l hn
    rw [Nat.zero_add] at he hr
    rw [hks, hπs', hr]
    simp only [πs₀, hfs l p' hp', Option.map_some, hpos', he]
    exact Grade.run_mul_le_fieldMultiplicity π₀ r p'.usage _ _ hle hgl
  -- The coefficient of the ownership of each field is within the one that the constructor
  -- allows.
  have hκ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length, ∃ π₀ ϱ₀,
      πv[(l : Nat)]? = some π₀ ∧ ϱv[(l : Nat)]? = some ϱ₀ ∧
      r.fieldCoefficient ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?
        ≤ ϱ₀ * (r.run * π₀) := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hκv l p' hp'
    refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
    rw [hfs l p' hp']
    exact hle
  -- The requirement of the recursion is within the requirement times the uses of each field on
  -- which a recursive result recurses: such a field has recursions, so that the constructor
  -- allows uses of it unless the grade of the recursor has none at run time.
  have hϱ : ∀ (j' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) (l : Nat),
      (if gs₀[j'] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j' : Nat)]?) = .field l →
        ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧ ϱ ≤ ϱ₀ * (r.run * π₀) := by
    intro j' l hl
    have hl₀ := hl
    split at hl
    · cases hl
    · rename_i hg'
      have hl' : ((rfs.drop i).headD [])[(j' : Nat)]? = some l := by
        revert hl
        cases ((rfs.drop i).headD [])[(j' : Nat)]? <;> simp [RecursiveResult.ofPosition]
      rw [hpos] at hl'
      obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hϱv l (List.mem_of_getElem? hl')
      refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
      have hlt := Telescope.lt_of_mem_positions _ 0 (List.mem_of_getElem? hl')
      rw [Telescope.length_recursion, Nat.zero_add] at hlt
      obtain ⟨π₁, hπ₁, hle₁⟩ := hπ ⟨l, hlt⟩
      cases hπ₀.symm.trans hπ₁
      have hne := recursionsAt_ne_zero (l := l) (k := .field l) (π := πs₀' j') rfl
        ((by decide : ∀ g : Grade, g ∉ Mode.oneOne.erased → g.run * .one ≠ .zero) _ hg')
        (ks := List.ofFn
          fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
          if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
          else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?)
        (πs := List.ofFn πs₀') (j := j')
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]; exact congrArg some hl₀)
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn])
      by_cases hz : r.run * π₀ = .zero
      · rw [hϱ0 ((by decide : ∀ ρ π₀ π x : Multiplicity, ρ * π₀ ≤ π + ρ * x → x ≠ .zero →
          ρ * π₀ = .zero → ρ = .zero) _ _ _ _ hle₁ hne hz)]
        exact (by decide : ∀ x : Multiplicity, .omega ≤ x) _
      · exact hle hz
  refine ⟨v, H₃, tr₁ ++ tr₂, .iota ha hget (RunsAsArgs.length hfa) hπ hκ hϱ (hks ▸ hevs)
    ((Eval.cast _).2 hev), hH₂.trans (hH₂'.trans hH₃), fun C'' hC'' => ?_⟩
  rw [hC'] at hC''
  cases hC''
  -- The recursor on the constructor steps to the branch, at the motive at the constructor.
  rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hrun
  have hrun₁ := (RunsAs.redStar_iff hd
    (.step (Red.iota_subst (D' := T'.name) (qs'' := qs') (ls'' := ls') (ps'' := ps') (as := as')
      ⟨hdecl, hT', rfl⟩ hi σ hq hl hp ts hu hrs) (.refl _))).2 hrun
  have hca : ValidEqTerm₀ sig ι
      (.ctor T'.name qs ls ps (as.subst σ) con.name ts.terms)
      (.ctor T'.name qs' ls' ps' as' con.name ts.terms) (.inst T'.name qs ls ps (as.subst σ)) :=
    hval T' hT' _ _ ⟨_, _, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩,
      DataType.blockRel_closed hmonoM hT' ⟨con, hcon, ts.terms, ts.terms, ⟨_, _, _, _, _, rfl⟩,
        ⟨_, _, _, _, _, rfl⟩, hself⟩⟩
  have hmot := (hCv j T' C' hj hC').motive hσ hca
  have hrw := hrec j T' C' hj hC' σ hσ _ hwv
  exact hrun₁.conv hd (hrw.conv hmot.symm).2 hmot.2


end

end Sic.Core
