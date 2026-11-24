module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.Corecursors
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.Corecursors.Erasure
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Levels
import Sic.Core.RunTime.Relation.Observations
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Relation.Substitution
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Run Time of the Corecursors

The position that the branch of a recursive destructor gives is a constructor of the type of
positions of the prelude, which has no recursive field: a new state, whose packing unpacks into the
nested pairs of the arguments of the state, related to the addresses that the evaluation unpacks
when the grade of the corecursor is used at run time, and whose entries have grades without use at
run time otherwise, so that the evaluation does not read it; or a term already built, related to
the address of its field.

A corecursor is related to the address of the closure of its branches that its erasure allocates,
by coinduction: the relations of `(®_ν)`, joined with the corecursors of the block from states
related to the addresses of such closures, are consistent with the clauses of `(®_ν)`, since an
observation by a destructor whose grade is used at run time runs its branch, valid at run time at
the state and the arguments, and gives the observation, or a position that it resumes into a new
closure of the same branches or into a term already built.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Corecursors -/

/-- The extension of a vector by the variables of a telescope at the grades of their entries times
`r` is its extension by these grades times `r`, at their positions. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_eq_extendGrades {Γ : Scope} :
    (γ : GradeVector Γ.length) → (r : Grade) → (ps : List Parameter) →
    γ.extendParams r ps = γ.extendGrades (fun l => r * Parameter.grades ps l) ps
  | _, _, [] => rfl
  | γ, r, p :: ps => by
    rw [GradeVector.extendParams, GradeVector.extendGrades,
      extendParams_eq_extendGrades (Γ := .var :: Γ)]
    rfl

/-- The branches of a corecursor whose destructors have a grade used at run time are valid at run
time with the grades `δs i` of the variables of the context, those of the entries of the state
`r` times their grades and those of the arguments their grades, at the results of their
destructors, as the usage of `(corec)` premises them in the mode `11ᵐ`, in every environment that
binds their scope through a renaming: the premise that the Lean of `(corec)` at run time reads. -/
def RunValidCorecBranches (sig : Signature) (ι : Interpretation) (P : Program) {Γ : Scope}
    (hΓ : Γ.FirstOrder) (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ) (gs : DestructorBranches 0 Γ)
    (δs : Nat → GradeVector Γ.length) : Prop :=
  ∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps'') (p q ς : Grade)
    (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
    (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
    (g : Term 0 ((Γ.extend ps''.length).extend ps₁.length)),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    (hd : (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ) →
    gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → p ∉ Mode.oneOne.erased →
    RunValidRen sig ι P ((hΓ.extend _).extend _)
      ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubstOf T'.name qs ls ps (as.rename (Ren.weakenN ps''.length))
          (Term.corecAt r T'.name qs ls ps as Ss gs ps''))))
      (((δs i).extendParams (Mode.oneOne.grade * r) ps'').extendParams Mode.oneOne.grade ps₁) g
      (Term.branchResult decl.names B
        ((decl.sort hqp.inst).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted)
        ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubstOf T'.name qs ls ps (as.rename (Ren.weakenN ps''.length))
            (Term.corecAt r T'.name qs ls ps as Ss gs ps'')))))

/-- `(corec)` at run time, closed: a corecursor of a codata type of `Σ`, whose type declaration is
meaningful, from a closed state related to the addresses of a closure of its branches erased, at a
substitution of the context of its branches for which addresses stand as the grades `δ` require, the
branches renamed by `g` in an environment that binds each variable `g x` as `E` binds `x`, is
related to the closure at its instance, in a signature whose names are distinct: the relations of the
corecursors of the block from such states and closures, together with `(®_ν)`, are consistent with
the clauses of `(®_ν)`, since an observation by a destructor whose grade is used at run time runs its
branch, valid at run time, and resumes its position into such a closure or into a term already
built. -/
theorem RunsAs.corec (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels)
    (hadm : decl.constraint hqp.inst) {Γ : Scope} {hΓ : Γ.FirstOrder}
    {ctx : Context 0 Γ} {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params hqp.inst).substLevels (ls.getFin hl)))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body hqp.inst).recursionAt decl.names i = some D') → sig.HasPrelude)
    {r : Grade} {Ss : States 0 Γ} {gs : DestructorBranches 0 Γ} {δ : GradeVector Γ.length}
    {δs : Nat → GradeVector Γ.length}
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hgv : CorecBranchesValid sig ι ctx decl qs ls ps hqp hl as r Ss gs)
    (hgr : RunValidCorecBranches sig ι P hΓ ctx decl qs ls ps hqp hl as r Ss gs δs)
    (hδ : ∀ i j T' d (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership Grade ps₁.length), decl.codataCases[i]? = some (j, T', d) →
      (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ → δ ≤ᶜ p ·ᶜ δs i)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ)
    (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx δ σ V) {j : Nat}
    {T' : CodataType decl.sorts decl.grades decl.levels decl.scope} {ps'' : List Parameter}
    {S' : Telescope 0 Γ ps''} (hj : decl.codataTypes[j]? = some T')
    (hS' : Ss.get j = some ⟨0, ps'', S'⟩) {ts : Args 0 [] ps''} {bs : List Nat}
    (hts : EqSubst sig ι (Context.empty.append (S'.subst σ)) ts.toSubst ts.toSubst)
    (hbs : RunsAsArgs sig ι P H (fun l => r * Parameter.grades ps'' l) ts bs (S'.subst σ))
    {m : Nat} {g : TargetRen m Γ.length} {E' : List Nat}
    (hg : ∀ x : Fin Γ.length, E'[(g x : Nat)]? = E[(x : Nat)]?)
    {a : Nat} (ha : H[a]? = some (.corec m E'
      ((gs.erase sig Mode.oneOne.erased hΓ ((sig.destructorGrades D qs ps).getD [])
        (((sig.resumedTypes D qs ps).getD []).map
          fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity))
        (((sig.destructorArguments D qs ps).getD []).map fun ⟨j, as⟩ =>
          ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩,
            as))).rename g)
      (ps''.map fun p => (r * p.usage).run) (ps''.map (·.requirement.run)) bs)) :
    RunsAs sig ι P H (.corec r T'.name qs ls ps (as.subst σ) ts.terms (Ss.subst σ) (gs.subst σ)) a
      (.inst T'.name qs ls ps (as.subst σ)) := by
  obtain ⟨hdecl, hT, hD⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hn := TypeDeclaration.codataTypes_nodup hnd
  have hT' : T' ∈ decl.codataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := hqp.inst
  have hw : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => (Whnf.inst ..).computes
  cases hs : (decl.sort I).quality with
  | prop =>
    -- A proposition, whose proofs are related to every address.
    obtain ⟨_, -, hPr⟩ := hv.codataPropRel hd hdecl hqp hl hadm hasσ hs
    exact ⟨_, hw _, .inl ⟨_, _, levelRel_prop_iff.2 (hPr T' hT').1⟩⟩
  | type =>
    -- The relations of run time of the instances of the block.
    obtain ⟨Sr, hU⟩ := hv.codataRunUnivRel hd hdecl hqp hl hadm hasσ hs P
    obtain ⟨n, S, hnS, hS, -⟩ := HasRun.codata hd (D := T'.name) ⟨hdecl, hT', rfl⟩ hqp hl
      (.univ _ (levelRel_run_iff.2 (hU T' hT').1)) hs
    have hFR : ∀ T₁ ∈ decl.codataTypes, RunFieldRel sig ι P n (fun m _ => levelRel sig ι m)
        (.inst T₁.name qs ls ps (as.subst σ))
        ((CodataType.runBlockRel decl.codataTypes S T₁.name).computed sig ι) := fun T₁ hT₁ =>
      .univ (.codata ⟨hdecl, hT₁, rfl⟩ hqp hl rfl hs hnS S hS)
    have hmono : ∀ X Y : Name → RunRel, (∀ D' H₁ v b, X D' H₁ v b → Y D' H₁ v b) →
        ∀ T₁ ∈ decl.codataTypes, ∀ H₁ o b, S X T₁ H₁ o b → S Y T₁ H₁ o b :=
      fun X Y hXY T₁ hT₁ H₁ => RunDesRel.mono hd (List.prefix_refl H₁) (hS X T₁ hT₁) _ _
        (hS Y T₁ hT₁) (fun _ => Option.rel_map (fun D' H₂ _ _ => RunRel.computed_mono (hXY D' H₂)) _)
    have e : ((decl.sort I).atLevels ρ).level.closedValue = n :=
      (decl.sort_atLevels_closedValue hqp hl).trans hnS
    -- The grades of the destructors and the resumptions that the erasure of the closure reads.
    obtain ⟨grs, hgrs, hgrs'⟩ := hd.destructorGrades h hqp
    have hrt := hd.resumedTypes h hqp
    let ks : List Resumption := ((sig.resumedTypes D qs ps).getD []).map
      fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity)
    let pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade) :=
      ((sig.destructorArguments D qs ps).getD []).map fun ⟨j, as⟩ =>
        ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩, as)
    let Ps := gs.erase sig Mode.oneOne.erased hΓ ((sig.destructorGrades D qs ps).getD []) ks pss
    -- The corecursors of the block from closed states related to the addresses of closures of the
    -- branches, renamed in an environment that binds the renamed scope as `E` binds the scope,
    -- joined with `(®_ν)`; a closure stores the requirements at run time of the entries of its
    -- state when `r` is used at run time, and any requirements otherwise, which no branch reads.
    let Clo : Name → RunRel := fun D' H₁ v b =>
      ∃ (j₁ : Nat) (T₁ : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (ps₁ : List Parameter) (S₁ : Telescope 0 Γ ps₁) (ts₁ : Args 0 [] ps₁) (bs₁ : List Nat)
        (ϱs₁ : List Multiplicity) (m : Nat) (g : TargetRen m Γ.length) (E' : List Nat),
        decl.codataTypes[j₁]? = some T₁ ∧ T₁.name = D' ∧ Ss.get j₁ = some ⟨0, ps₁, S₁⟩ ∧
        EqSubst sig ι (Context.empty.append (S₁.subst σ)) ts₁.toSubst ts₁.toSubst ∧
        H.Extends H₁ ∧
        RunsAsArgs sig ι P H₁ (fun l => r * Parameter.grades ps₁ l) ts₁ bs₁ (S₁.subst σ) ∧
        (∀ x : Fin Γ.length, E'[(g x : Nat)]? = E[(x : Nat)]?) ∧
        H₁[b]? = some (.corec m E' (Ps.rename g) (ps₁.map fun p => (r * p.usage).run) ϱs₁ bs₁) ∧
        ϱs₁.length = ps₁.length ∧ (r ∉ Mode.oneOne.erased → ϱs₁ = ps₁.map (·.requirement.run)) ∧
        v = .corec r D' qs ls ps (as.subst σ) ts₁.terms (Ss.subst σ) (gs.subst σ)
    let X : Name → RunRel := fun D' H₁ v b =>
      CodataType.runBlockRel decl.codataTypes S D' H₁ v b ∨ Clo D' H₁ v b
    have hcons : ∀ T₁ ∈ decl.codataTypes, ∀ H₁ v b, X T₁.name H₁ v b →
        runCorecRel T₁.name (S X T₁) H₁ v b := by
      intro T₁ hT₁ H₁ v b hx
      rcases hx with ⟨X', hX', hx'⟩ | ⟨j₁, T₂, ps₁, S₁, ts₁, bs₁, ϱs₁, m, g₁, E₁, hj₁, hn₁, hS₁,
        hts₁, hH₁, hbs₁, hg₁, hb, hϱl, hϱs₁, rfl⟩
      · exact runCorecRel_mono (fun o b' => hmono X' X (fun D' H₂ v' b'' h => .inl ⟨X', hX', h⟩)
          T₁ hT₁ H₁ o b') (hX' T₁ hT₁ H₁ v b hx')
      obtain rfl : T₂ = T₁ := List.eq_of_nodup_map hn (List.mem_of_getElem? hj₁) hT₁ hn₁
      have h₀ : sig.HasCodataType T₂.name decl T₂ := ⟨hdecl, hT₁, rfl⟩
      refine ⟨_, ⟨r, qs, ls, ps, _, as.subst σ, ts₁.terms, Ss.subst σ, gs.subst σ, rfl, rfl⟩, ?_⟩
      have hSρ : RunDesRel sig ι P ((decl.sort I).atLevels ρ).level.closedValue
          (fun m _ => levelRel sig ι m) T₂.name
          (fun i => ((T₂.body I).recursionAt decl.names i).map fun D' => (X D').computed sig ι)
          ((T₂.body I).substLevels Lρ) (as.subst σ).toSubst (S X T₂) := by
        rw [e]
        exact RunDesRel.atLevels_of_substLevels hd (hS X T₂ hT₁)
      -- The case of a destructor of the type and its branch.
      have hcase : ∀ {d p q ς ps' Ξ} {Θ : Telescope decl.levels Ξ ps'}
          {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length},
          (T₂.body I).Pos d p q ς Ξ Θ B ψ → ∃ i g, decl.codataCases[i]? = some (j₁, T₂, d) ∧
            gs.get i = some ⟨0, ps₁.length, ps'.length, g⟩ := fun {d p q ς ps' Ξ Θ B ψ} hpos => by
        have hm := TypeDeclaration.mem_codataCases_of hj₁ hpos.mem
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
        obtain ⟨g, -, hg, -⟩ := hgv.1 i j₁ T₂ d ps₁ S₁ hi hS₁ p q ς ps' Ξ Θ B ψ hpos
        exact ⟨i, g, hi, hg⟩
      refine RunDesRel.of_obs hd Lρ (T₂.body I) (rs := (T₂.body I).recursionAt decl.names)
        (hv.destructorsAtClosedLevels hqp hl hadm hasσ T₂ hT₁) (fun i hi => by rw [hi]; rfl)
        (fun i D' hi => by rw [hi]; exact ⟨_, rfl⟩) hSρ ?_ ?_
      · -- The observations by a destructor that is not recursive step to its branch, whose
        -- premise makes it a term of the result of the destructor.
        intro d p q ς ps' Ξ Θ B ψ hpos ts₂ us₂ hτ hr0
        obtain ⟨i, g, hi, hg⟩ := hcase hpos
        have hτ' := (EqSubst.substLevels_iff_atLevels L Θ (Subst.LevelEquiv.refl _)).2 hτ
        have hb := ValidEqTerm₀.corecBranch hpos
          (hgv.2 i j₁ T₂ d ps₁ S₁ p q ς ps' Ξ Θ B ψ g g hi hS₁ hpos hg hg) hσ hts₁ hτ'
        have hred₁ := Red.beta_corec (ι := ι) hd h₀ hqp hl hi hpos hg σ ts₁ ts₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hred₂ := Red.beta_corec (ι := ι) hd h₀ hqp hl hi hpos hg σ ts₁ us₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hbn : B.blockName decl.names = none := by
          rw [← hpos.recursionAt_index]
          exact hr0
        simp only [Term.branchResult, hbn] at hb
        simp only [Term.observed, hbn] at hred₁ hred₂
        rw [Term.observation_subst_args, Term.observation_subst_args]
        exact (((ValidEqTerm₀.red_iff hd hred₂).2
          ((ValidEqTerm₀.red_iff hd hred₁).2 hb).symm).symm).levelEquiv (Term.LevelEquiv.refl _)
          (Term.LevelEquiv.refl _) (Term.closedValues_levelEquiv L B (Subst.LevelEquiv.refl _))
      · -- The observation by a destructor whose grade is used at run time runs its branch, valid
        -- at run time, and resumes its value.
        intro d p q ς ps' Ξ Θ B ψ hpos i' hpr hi' H₂ hH₂ ts₂ bs₂ hτ hbs₂ ϖ₀
        obtain ⟨i, g, hi, hg⟩ := hcase hpos
        obtain rfl : i' = i :=
          Option.some.inj (hi'.symm.trans (hd.destructorCase_of_codataCases hdecl hi))
        have hτ' := (EqSubst.substLevels_iff_atLevels L Θ (Subst.LevelEquiv.refl _)).2 hτ
        have hbs₂' :=
          RunsAsArgs.levelEquiv hd (Θ.closedValues_levelEquiv L (Subst.LevelEquiv.refl _)).symm hbs₂
        -- The branch in the closure, at the grade of its destructor.
        have hpg : ((sig.destructorGrades D qs ps).getD [])[i']? = some p := by
          rw [hgrs]
          exact hgrs' i' j₁ T₂ d hi p (hpos.grade (hd.destructors_nodup h₀))
        have hget :=
          DestructorBranches.get_erase (sig := sig) Mode.oneOne.erased hΓ gs _ ks pss hg hpg
        simp only [hpr, ↓reduceIte] at hget
        -- The parameters of the entries of the state and of the arguments of the branch, and the
        -- ownership of its result.
        have hpss : (pss.drop i').headD ([], ResultOwnership.noArguments) =
            (ps₁.map fun p => ⟨r * p.usage, p.requirement⟩, ⟨ps', ψ, ς⟩) :=
          List.headD_drop (by
            simp [pss, hd.destructorArguments h hqp, hi, hS₁]
            rw [hpos.arguments (hd.destructors_nodup h₀)]
            rfl)
        rw [hpss, Mode.grade_odot_of_not_erased p hpr, ResultOwnership.toArity_self] at hget
        -- The uses of each entry and of each argument by the branch are those that the closure
        -- and the observation allow.
        have hπ₁ : ∀ j : Fin ps₁.length, ∃ π₁,
            (ps₁.map fun p => (r * p.usage).run)[(j : Nat)]? = some π₁ ∧
            π₁ ≤ ((ps₁.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(j : Nat)]?.map
              fun q => (Grade.one * q.usage).run).getD .omega := fun j =>
          ⟨_, List.getElem?_eq_getElem (by simp), by
            simp only [List.getElem?_map, List.getElem?_eq_getElem j.2, Option.map_some,
              Option.getD_some, List.getElem_map, Grade.modality.semiring.one_mul]
            exact Multiplicity.le_refl' _⟩
        have hπ₂ : ∀ j : Fin ps'.length, ∃ π₂,
            (ps'.map (·.usage.run))[(j : Nat)]? = some π₂ ∧
            π₂ ≤ (ps'[(j : Nat)]?.map
              fun q => (Grade.one * q.usage).run).getD .omega := fun j =>
          ⟨_, List.getElem?_eq_getElem (by simp), by
            simp only [List.getElem?_eq_getElem j.2, Option.map_some,
              Option.getD_some, List.getElem_map, Grade.modality.semiring.one_mul]
            exact Multiplicity.le_refl' _⟩
        -- The ownership that the branch gives each entry of the state is within the requirement
        -- that the closure stores, which is that of the entry when `r` is used at run time, and
        -- the multiplicity of the entry is `0` otherwise.
        have hϱ₁ : ∀ j : Fin ps₁.length, ∃ ϱ₁, ϱs₁[(j : Nat)]? = some ϱ₁ ∧
            ((ps₁.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(j : Nat)]?.map
              (·.requirement.run)).getD .omega *
            ((ps₁.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(j : Nat)]?.map
              fun q => (Grade.one * q.usage).run).getD .omega ≤
            ϱ₁ * ((ps₁.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(j : Nat)]?.map
              fun q => (Grade.one * q.usage).run).getD .omega := fun j => by
          obtain ⟨ϱ₁, hϱ₁⟩ : ∃ ϱ₁, ϱs₁[(j : Nat)]? = some ϱ₁ :=
            ⟨_, List.getElem?_eq_getElem (by rw [hϱl]; exact j.2)⟩
          refine ⟨ϱ₁, hϱ₁, ?_⟩
          simp only [List.getElem?_map, List.getElem?_eq_getElem j.2, Option.map_some,
            Option.getD_some, Grade.modality.semiring.one_mul]
          by_cases hr : r ∈ Mode.oneOne.erased
          · rw [(Mode.erased_values.1 _).1 ((by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased →
              r * u ∈ Mode.oneOne.erased) r _ hr)]
            exact (by decide : ∀ π π' : Multiplicity, π * .zero ≤ π' * .zero) _ _
          · rw [hϱs₁ hr, List.getElem?_map, List.getElem?_eq_getElem j.2] at hϱ₁
            cases hϱ₁
            exact Multiplicity.le_refl' _
        have hϱ₂ : ∀ j : Fin ps'.length, ∃ ϱ₂, (ps'.map (·.requirement.run))[(j : Nat)]? = some ϱ₂ ∧
            (ps'[(j : Nat)]?.map (·.requirement.run)).getD .omega ≤ ϱ₂ := fun j =>
          ⟨_, List.getElem?_eq_getElem (by simp), by
            simp only [List.getElem?_eq_getElem j.2, Option.map_some, Option.getD_some,
              List.getElem_map]
            exact Multiplicity.le_refl' _⟩
        -- The constant of the ownership of the result at run time is that of the type of the
        -- positions.
        have hψc : (ψ.map Grade.run).constant.getD .omega ≤
            (ψ.constant.getD .unrestrictedUnrestricted).run := by
          simp only [ResultOwnership.map]
          cases ψ.constant <;> exact Multiplicity.le_refl' _
        -- The context of the branch, at the grades of its variables.
        have hc := fun (a' : Scope.Entry) (x : Var Ξ a') =>
          hpos.obsSubstOf_corecAt σ r T₂.name qs ls ps as Ss gs ts₁
            (InstanceArgs.toSubst_rename_subst_append σ as ts₁) x
        have hEq := (EqSubst.append_append_iff (ctx.append S₁) _ _ _ _ _).2
          ⟨(EqSubst.append_append_iff ctx S₁ _ _ _ _).2 ⟨hσ, hts₁⟩,
            by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hτ'⟩
        have hδi : RunsAsSubst sig ι P H₂ ctx (δs i') σ V :=
          RunsAsSubst.of_counted ctx (fun x hx => (by decide : ∀ c p u : Grade, c ≤ p * u →
            p ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased → c ∉ Mode.oneOne.erased) _ _ _
            (hδ i' j₁ T₂ d p q ς ps' Ξ Θ B ψ hi hpos x) hpr hx) (hE.mono hd (hH₁.trans hH₂))
        have hbs₁' : RunsAsArgs sig ι P H₂
            (fun l => (Mode.oneOne.grade * r) * Parameter.grades ps₁ l) ts₁ bs₁ (S₁.subst σ) :=
          RunsAsArgs.of_counted (fun l h' => (by decide : ∀ r u : Grade,
            (Mode.oneOne.grade * r) * u ∉ Mode.oneOne.erased → r * u ∉ Mode.oneOne.erased) r _ h')
            (hbs₁.mono hd hH₂)
        have hbs₂'' := RunsAsArgs.of_counted (g' := fun l => Mode.oneOne.grade *
          Parameter.grades ps' l) (fun l h' => (by decide : ∀ u : Grade,
            Mode.oneOne.grade * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) _ h') hbs₂'
        have hσr := RunsAsSubst.append (ctx.append S₁) _ (RunsAsSubst.append ctx S₁ hδi hbs₁')
          (by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hbs₂'')
        have hbr := hgr i' j₁ T₂ d ps₁ S₁ p q ς ps' Ξ Θ B ψ g hi hS₁ hpos hg hpr
        rw [GradeVector.extendParams_eq_extendGrades,
          GradeVector.extendParams_eq_extendGrades] at hbr
        -- The branch binds its variables to cells, at the multiplicities of its binders.
        let πs₁ : Fin ps₁.length → Multiplicity := fun j =>
          ((ps₁.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(j : Nat)]?.map
            fun q => (Grade.one * q.usage).run).getD .omega
        let πs₂ : Fin ps'.length → Multiplicity := fun j =>
          (ps'[(j : Nat)]?.map fun q => (Grade.one * q.usage).run).getD .omega
        have hlen₁ := RunsAsArgs.length hbs₁
        have hlen₂ := RunsAsArgs.length hbs₂
        have hlen : ((List.ofFn πs₁ ++ List.ofFn πs₂).map (ϖ₀ * ·)).length =
            (bs₁ ++ bs₂).length := by
          simp only [List.length_map, List.length_append, List.length_ofFn, hlen₁, hlen₂]
        let H₂' := H₂.bind ((List.ofFn πs₁ ++ List.ofFn πs₂).map (ϖ₀ * ·)) (bs₁ ++ bs₂)
        have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
        have hB : H₂'.Binds ((List.range' H₂.length (bs₁ ++ bs₂).length).reverse ++ E)
            (bs₂.reverse ++ (bs₁.reverse ++ V)) := by
          have h' := (Heap.binds_bind H₂ hlen).reverse.append
            (hEV.mono (hH₁.trans (hH₂.trans hH₂')))
          rwa [List.reverse_append, List.append_assoc] at h'
        -- The renamed branch runs in the environment of the closure, extended by the cells of its
        -- variables, which binds its renamed scope as the environment of the branch binds it.
        have hL : ((List.range' H₂.length (bs₁ ++ bs₂).length).reverse).length =
            ps₁.length + ps'.length := by
          simp only [List.length_reverse, List.length_range', List.length_append, hlen₁, hlen₂]
        obtain ⟨w₀, H₃, tr, hev, hH₃, hrun⟩ := hbr ϖ₀ _ H₂' _ _ hEq hB (hσr.mono hd hH₂')
          (fun x => g₁.lift (ps₁.length + ps'.length)
            (Fin.cast (Scope.length_extend_extend Γ ps₁.length ps'.length) x))
          ((List.range' H₂.length (bs₁ ++ bs₂).length).reverse ++ E₁)
          (fun x => TargetRen.getElem?_lift hg₁ _ hL _)
        rw [Term.branchResult_corecAt] at hrun
        rw [← Target.rename_cast] at hev
        have hclo : H₂[b]? =
            some (.corec m E₁ (Ps.rename g₁) (ps₁.map fun p => (r * p.usage).run) ϱs₁ bs₁) :=
          hH₂.getElem? hb
        have hred := Red.beta_corec (ι := ι) hd h₀ hqp hl hi hpos hg σ ts₁ ts₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hrn := hpos.resultName decl.names (hd.destructors_nodup h₀)
        rw [Term.observation_subst_args]
        cases hbn : B.blockName decl.names with
        | none =>
          -- The branch gives the observation.
          have hk : ks.getD i' .none = .none := by
            simp only [ks, hrt, Option.getD_some, List.map_map, List.getD_eq_getElem?_getD,
              List.getElem?_map, hi, Option.map_some, Function.comp_apply]
            rw [hrn, hbn]
            rfl
          rw [hk] at hget
          simp only [Term.branchResult, hbn] at hrun
          simp only [Term.observed, hbn] at hred
          refine ⟨w₀, H₃, tr, .beta hclo
            (by rw [TargetCorecBranches.get_rename, hget]; rfl) hlen₁ hlen₂ hπ₁ hπ₂ hϱ₁ hϱ₂ rfl
            (Multiplicity.le_refl' _) hev .none,
            fun _ => ?_,
            fun D' R hD' => ?_⟩
          · exact ((RunsAs.redStar_iff hd (.step hred (.refl _))).2 hrun).levelEquiv hd
              (Term.closedValues_levelEquiv L B (Subst.LevelEquiv.refl _))
          · simp only [hpos.recursionAt_index, hbn] at hD'
            cases hD'
        | some D₃ =>
          -- The branch gives a position of the corecursor of the type of the result.
          obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
            (Term.blockName_mem hbn)
          obtain ⟨j₃, hj₃⟩ := List.mem_iff_getElem?.1 hT₃
          obtain ⟨ps₃, S₃, hS₃⟩ := hSs j₃ T₃ hj₃
          have hpr : sig.HasPrelude := hpre ⟨j₁, T₂, hpos.index, T₃.name, hj₁,
            by rw [hpos.recursionAt_index]; exact hbn⟩
          have hst : (Ss.subst σ).stateOf decl.names T₃.name =
              some ⟨ps₃, S₃.subst σ, Ss.sorts j₃⟩ := by
            rw [States.stateOf_subst, States.stateOf_of_get hnd hj₃ hS₃]
            rfl
          have hk : ks.getD i' .none =
              Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps₃.length) := by
            simp only [ks, hrt, Option.getD_some, List.map_map, List.getD_eq_getElem?_getD,
              List.getElem?_map, hi, Option.map_some, Function.comp_apply]
            rw [hrn, hbn]
            simp only [Option.bind_some, TypeDeclaration.idxOf?_codataTypes hnd hj₃, States.arity,
              hS₃]
            rfl
          rw [hk] at hget
          have hb := ValidEqTerm₀.corecBranch hpos
            (hgv.2 i' j₁ T₂ d ps₁ S₁ p q ς ps' Ξ Θ B ψ g g hi hS₁ hpos hg hg) hσ hts₁ hτ'
          simp only [Term.branchResult, hbn, hst] at hb hrun
          simp only [Term.observed, hbn, hst] at hred
          obtain ⟨v', H₄, hres, -, hnext | ⟨rfl, hdone⟩⟩ := RunsAs.resume hd hpr hs hb hrun
            m E₁ (Ps.rename g₁) T₃.name qs ls ps (as.subst σ) (Ss.subst σ) (gs.subst σ) _ hψc
          · -- A new state: a new closure of the branches.
            obtain ⟨ts₃, bs₃, ϱs₃, hred', hτ₃, hbs₃, rfl, hϱs₃, rfl⟩ := hnext
            refine ⟨_, _, tr, .beta hclo
              (by rw [TargetCorecBranches.get_rename, hget]; rfl) hlen₁ hlen₂ hπ₁ hπ₂ hϱ₁ hϱ₂ rfl
              (Multiplicity.le_refl' _) hev hres,
              fun hr0 => ?_,
              fun D' R hD' hR _ => ?_⟩
            · simp only [hpos.recursionAt_index, hbn] at hr0
              cases hr0
            · simp only [hpos.recursionAt_index, hbn, Option.map_some, Option.some.injEq] at hD' hR
              subst hD' hR
              exact ⟨_, ⟨.step hred hred', .corec _ _ _ _ _ _ _ _ _⟩, .inr ⟨j₃, T₃, ps₃, S₃, ts₃,
                bs₃, ϱs₃, m, g₁, E₁, hj₃, rfl, hS₃, hτ₃,
                (hH₁.trans (hH₂.trans (hH₂'.trans hH₃))).trans (List.prefix_append _ _),
                hbs₃.mono hd (List.prefix_append _ _), hg₁, by simp, hϱs₃.1, hϱs₃.2, rfl⟩⟩
          · -- A term already built, related at the instance of the type of the result.
            refine ⟨_, _, tr, .beta hclo
              (by rw [TargetCorecBranches.get_rename, hget]; rfl) hlen₁ hlen₂ hπ₁ hπ₂ hϱ₁ hϱ₂ rfl
              (Multiplicity.le_refl' _) hev hres,
              fun hr0 => ?_, fun D' R hD' hR he => ?_⟩
            · simp only [hpos.recursionAt_index, hbn] at hr0
              cases hr0
            · simp only [hpos.recursionAt_index, hbn, Option.map_some, Option.some.injEq] at hD' hR
              subst hD' hR
              have h₁ := ((RunsAs.redStar_iff hd (.step hred (.refl _))).2 hdone).levelEquiv hd
                (Term.closedValues_levelEquiv L B (Subst.LevelEquiv.refl _))
              rw [Term.atLevels, Destructors.Pos.obsSubstOf_def, he] at h₁
              exact RunRel.computed_mono (fun _ _ h => .inl h)
                (RunFieldRel.of_runsAs hd (hFR T₃ hT₃) (hw _)
                  (h₁.levelEquiv hd
                    (decl.blockInstance_atLevels_subst hqp hl (as.subst σ) T₃.name)))
    -- The corecursor is related to the closure.
    exact ⟨_, hw _, .inr ⟨_, .univ n (levelRel_run_iff.2 (.codata ⟨hdecl, hT', rfl⟩ hqp hl rfl hs
      hnS S hS)), _, (Whnf.corec ..).computes, X, hcons,
      .inr ⟨j, T', ps'', S', ts, bs, _, m, g, E', hj, rfl, hS', hts, List.prefix_refl _, hbs, hg,
        ha, List.length_map .., fun _ => rfl, rfl⟩⟩⟩

/-- `(corec)` at run time: a corecursor of a codata type of `Σ`, whose type declaration is
meaningful, from a state valid at run time with the grades `γ` when its grade `r` is used at run
time, with branches valid at run time with the grades `δs i`, which `δ` bounds, is valid at run time
at its instance with the grades `r · γ + δ`, in a signature whose names are distinct: its erasure
evaluates its state and allocates the closure of its branches, to which `RunsAs.corec` relates it,
in every environment that binds the scope through a renaming. -/
theorem RunValidRen.corec (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels)
    (hadm : decl.constraint hqp.inst) {Γ : Scope} {hΓ : Γ.FirstOrder}
    {ctx : Context 0 Γ} {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params hqp.inst).substLevels (ls.getFin hl)))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body hqp.inst).recursionAt decl.names i = some D') → sig.HasPrelude)
    {r : Grade} {Ss : States 0 Γ} {gs : DestructorBranches 0 Γ} {γ δ : GradeVector Γ.length}
    {δs : Nat → GradeVector Γ.length} {h' : Nat} {ps' : List Parameter} {S : Telescope 0 Γ ps'}
    {ss : Args 0 Γ ps'} (hh : decl.codataTypes[h']? = some T)
    (hS : Ss.get h' = some ⟨0, ps', S⟩) (hss : ValidArgsΓ sig ι ctx ss S)
    (hssr : r ∉ Mode.oneOne.erased → RunValidArgsRen sig ι P hΓ ctx γ ss S)
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hgv : CorecBranchesValid sig ι ctx decl qs ls ps hqp hl as r Ss gs)
    (hgr : RunValidCorecBranches sig ι P hΓ ctx decl qs ls ps hqp hl as r Ss gs δs)
    (hδ : ∀ i j T' d (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership Grade ps₁.length), decl.codataCases[i]? = some (j, T', d) →
      (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ → δ ≤ᶜ p ·ᶜ δs i) :
    RunValidRen sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ δ) (.corec r D qs ls ps as ss.terms Ss gs)
      (.inst D qs ls ps as) := by
  intro ϖ₀ σ H E V hσ hEV hE _ g E' hg
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS₀ := Mode.erasesUncounted .oneOne
  have hEδ : RunsAsSubst sig ι P H ctx δ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS₀.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  -- The erasure evaluates the state, each entry at its grade times `r`.
  have hst : (((sig.position T.name).bind Ss.get).elim [] fun ⟨_, ps, _⟩ =>
      ps.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter)) =
      ps'.map fun p => ⟨r * p.usage, p.requirement⟩ := by
    rw [hd.position h hh, Option.bind_some, hS]
    rfl
  obtain ⟨bs, H', tr, hev, hH', hbs⟩ : ∃ bs H' tr, EvalAll P ϖ₀ H E'
      ((ss.terms.erase sig Mode.oneOne.erased hΓ
        (ps'.map fun p => ⟨r * p.usage, p.requirement⟩)).rename g) bs H' tr ∧
      H.Extends H' ∧
      RunsAsArgs sig ι P H' (fun l => r * Parameter.grades ps' l) (ss.subst σ) bs (S.subst σ) := by
    by_cases hr : r ∈ Mode.oneOne.erased
    · -- Every entry is erased.
      have hrS := (by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased)
        r
      obtain ⟨bs, H', hev, hH', hl⟩ := Args.evalAll_erased (sig := sig) (P := P)
        Mode.oneOne.erased hΓ g ϖ₀ E' ss (ps'.map fun p => ⟨r * p.usage, p.requirement⟩)
          (fun u hu => by
            obtain ⟨u', -, rfl⟩ := List.mem_map.1 hu
            exact hrS u'.usage hr) H
      exact ⟨bs, H', [], hev, hH', RunsAsArgs.of_erased (ss.subst σ) bs (S.subst σ)
        (fun _ _ _ => hrS _ hr) hl⟩
    · -- The state is valid at run time with the grades `γ`.
      have hEγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h ((by decide : ∀ r u : Grade, r ∉ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased →
          u ∈ Mode.oneOne.erased) r _ hr (hS₀.add _ _ h'))) hE
      obtain ⟨bs, H', tr, hev, hH', hrs⟩ := hssr hr (ϖ₀ * r.run) σ H E V hσ hEV hEγ g E' hg
      refine ⟨bs, H', tr, ?_, hH', RunsAsArgs.of_counted (fun l h' => (by decide : ∀ r u : Grade,
        r * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) r _ h') hrs⟩
      exact Terms.evalAll_erase_mul_of_not_erased hΓ hr g _ _ hev
  -- Then it allocates the closure of its branches, to which the corecursor is related.
  refine ⟨H'.length, H' ++ [.corec _ E' ((gs.erase sig Mode.oneOne.erased hΓ
    ((sig.destructorGrades T.name qs ps).getD []) (((sig.resumedTypes T.name qs ps).getD []).map
      fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity))
    (((sig.destructorArguments T.name qs ps).getD []).map fun ⟨j, as⟩ =>
      ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩,
        as))).rename g)
    (ps'.map fun p => (r * p.usage).run) (ps'.map (·.requirement.run)) bs], tr, ?_,
    hH'.trans (List.prefix_append _ _), ?_⟩
  · have hev' := Eval.corec (Ps := (gs.erase sig Mode.oneOne.erased hΓ
      ((sig.destructorGrades T.name qs ps).getD []) (((sig.resumedTypes T.name qs ps).getD []).map
        fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity))
      (((sig.destructorArguments T.name qs ps).getD []).map fun ⟨j, as⟩ =>
        ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩,
          as))).rename g) hev
    rw [Targets.multiplicities_rename, Targets.requirements_rename,
      Args.multiplicities_erase_map sig Mode.oneOne.erased hΓ (r * ·) ss,
      Args.requirements_erase_map sig Mode.oneOne.erased hΓ (r * ·) ss] at hev'
    rw [Term.erase, hst]
    exact hev'
  · rw [Term.corec_subst]
    exact RunsAs.corec hd h hv hqp hl hadm has hpre hSs hgv hgr hδ hσ
      ((hEV.mono hH').mono (List.prefix_append _ _))
      ((hEδ.mono hd hH').mono hd (List.prefix_append _ _)) hh hS (hss.2 σ σ hσ)
      (hbs.mono hd (List.prefix_append _ _)) hg (by simp)

end

end Sic.Core
