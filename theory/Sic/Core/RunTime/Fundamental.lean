module

public import Sic.Core.Lifting.Extension
public import Sic.Core.RunTime.Relation.Corecursors
public import Sic.Core.RunTime.Relation.Recursors.Results
public import Sic.Core.Typing
public import Sic.Core.Usage
import Sic.Core.Meaning.Judgments
import Sic.Core.Results.Functionality
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Observations
import Sic.Core.RunTime.Relation.Recursors
import Sic.Core.RunTime.Relation.Rules
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Substitution
import Sic.Core.Typing.Induction
import Sic.Core.Typing.Lifting
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature
import Sic.Core.Usage.Inversion

/-!
# Fundamental Lemma of the Run Time

The fundamental lemma of annex 22 of RFC 36: a term typed and used in the mode `11ᵐ` of run time, in
a context whose variables are all of the first order, is valid at run time with its grades,
`Σ; γ; Γ ⊨^® t : A`, at every value of its level variables, when the program `𝒫` realizes the
constants of the mode `11ᵐ` of the signature, `(hyp_𝒫)`.

The proof is by the induction on the derivations, `Derivations.induction`, on the typing, as the
soundness of the typing is: each case inverts the usage of the term, `Usage.inv_…`, which gives
the grades of the rule of its form above those of the judgment, and concludes by the lemma of the
same name in `Rules`, `DeclaredTypes`, `Recursors` or `Corecursors`, from the validity at run time
of the subterms, at the usages that the inversion gives them, and from the meaning of their
typings, which the soundness gives, then by the subsumption `RunValidRen.sub`.
A proof, which the erasure erases, ignores its usage and concludes by `RunValidRen.proof`, from the
meaning of its type, a proposition.
The induction proves the validity at run time in every environment that binds the scope through a
renaming, `RunValidRen`, since the erasure of a nested result copies the branches of its recursor,
renamed, under new binders; `RunValidRen.runValid` gives back `RunValid` at the identity.
The usage checks in the mode `11ᵐ` again each subterm of a grade that `S^{11ᵐ}` does not erase, and
the erasure replaces the others, so that the induction stays in the mode `11ᵐ`.

ADE prove their fundamental lemma, `fundamental`, in
`Graded/Erasure/LogicalRelation/Fundamental.agda`, by recursion on the typing, with the inversion
of the usage, `inv-usage-…`, of `Graded/Usage/Inversion.agda`, and the subsumption of their
validity, `subsumption-▸⊩ʳ∷[]-≤`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The program `𝒫` realizes the constants of the signature `Σ_T` of the mode `11ᵐ` of run time, in
the signature `Σ`: each of them, at each closed instance of its variables, is valid at run time in
the empty context, at its type at this instance. -/
def Program.Realizes (sig : Signature) (ι : Interpretation) (P : Program) (sigT : Signature) :
    Prop :=
  ∀ {f : Name} {j k' g : Nat} {p : Grade} {A : Instance j g → Term k' []},
    sigT.HasConstant f j k' g .oneOne p A →
      ∀ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade)
        (hqp : Instance.AsMany j g qs ps)
        (hl : ls.length = k'),
        RunValid sig ι P Scope.FirstOrder.nil .empty 𝟘ᶜ (.const f qs ls ps)
          (Signature.instanceType A hqp.inst (ls.getFin hl))

/-- The premise of `(corec)` at run time on its branches, each branch valid at run time for every
value of the level variables, in every environment that binds its scope through a renaming, when the
grade of its destructor is used at run time, holds at the levels without variables `ρ`, as
`CorecBranchesEqValid.atLevels` does for the meaning. -/
theorem RunValidCorecBranches.atLevels {sig : Signature} {ι : Interpretation} {P : Program}
    {k : Nat} {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {decl : TypeDeclaration}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs : DestructorBranches k Γ} {δs : Nat → GradeVector Γ.length}
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ) →
      gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → p ∉ Mode.oneOne.erased → ∀ ρ,
      RunValidRen sig ι P ((hΓ.extend _).extend _)
        (((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))).atLevels ρ)
        (((δs i).extendParams (Mode.oneOne.grade * r) ps'').extendParams Mode.oneOne.grade ps₁)
        (g.atLevels ρ)
        ((Term.branchResult decl.names B
          ((decl.sort hqp.inst).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))).atLevels ρ))
    (ρ : Fin k → Nat) :
    RunValidCorecBranches sig ι P hΓ (ctx.atLevels ρ) decl qs
      (ls.map (Level.atLevels ρ)) ps hqp (Level.length_atLevels ρ hl)
      (as.atLevels ρ) r (Ss.substLevels fun i => .ofNat (ρ i))
      (gs.substLevels fun i => .ofNat (ρ i)) δs := by
  intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hpr
  obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
  obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels _ hg
  have hb := hgt i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hpos hg₀ hpr ρ
  have hcl := fun (a : Scope.Entry) (x : Var Ξ a) =>
    hpos.obsSubst_corecAt_atLevels ρ r T'.name qs ls ps as Ss gs ps'' x
  simp only [Context.atLevels, Context.substLevels_append,
    Telescope.substLevels_subst_of (fun x => hcl _ x), Telescope.substLevels_substLevels,
    Term.atLevels, Term.branchResult_substLevels, States.substLevels_rename,
    Universe.substLevels_substLevels,
    Term.substLevels_subst_of (Subst.liftN_substLevels_of _ (fun x => hcl _ x)),
    Term.substLevels_substLevels] at hb
  erw [Context.substLevels_append (fun i => (.ofNat (ρ i) : Level 0)) ctx S₀] at hb
  rw [List.getFin_map]
  exact hb

/-- The types of the entries of a telescope that extends a well-formed context, at every value of
the level variables, and at every closed substitution of the context that the meaning relates to
itself, are terms of universes at every term of the types of the entries before them, in a signature
that gives the entries of the typing their meaning: each entry of a well-formed context is a term of
a sort, which the soundness of the typing makes meaningful. -/
theorem WfCtx.validSorts {ι : Interpretation} {sigM sig : Signature} (hd : sigM.Distinct)
    (hord : sigM.LiftsInOrder) (hι : sigM.ValidEntries ι sig) {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context k Γ) → (Θ : Telescope k Γ ps) →
      WfCtx sig (ctx.append Θ) → ∀ ρ θ, EqSubst sigM ι (ctx.atLevels ρ) θ θ →
        Telescope.ValidSorts₀ sigM ι ((Θ.atLevels ρ).subst θ)
  | _, [], _, .nil, _, _, _, _ => trivial
  | Γ, _ :: _, ctx, .cons _ _ A Θ, h, ρ, θ, hθ => by
    have hA : WfCtx sig (ctx.var A) := WfCtx.of_append (Γ := .var :: Γ) h
    obtain ⟨κ, hκ⟩ : ∃ κ, HasType sig ctx A (.sort κ) := by
      cases hA with
      | var hA' =>
        cases hA' with
        | univType hT => exact ⟨_, hT⟩
        | propType hT => exact ⟨_, hT⟩
    have hv := (soundnessIn.hasType hd hord hι hκ ρ).2 θ θ hθ
    refine ⟨⟨_, hv⟩, fun v hv' => ?_⟩
    rw [Telescope.subst_lift_single_snoc]
    exact WfCtx.validSorts hd hord hι (ctx.var A) Θ h ρ _
      ((EqSubst.var_iff _ _ _ _).2 ⟨hθ, hv'⟩)

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time, at every value of its level variables and in
every environment that binds the scope through a renaming, in a well-formed signature `Σ` that gives
the entries of `Σ_T` their meaning, when the program `𝒫` realizes the constants of `Σ_T` of the mode
`11ᵐ`. -/
structure FundamentalIn : Prop where
  /-- A typing. -/
  hasType : ∀ {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {t A : Term k Γ} {γ : GradeVector Γ.length},
    WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → HasType sig ctx t A →
      Usage sig γ .oneOne t →
        ∀ ρ, RunValidRen sigM ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ)
  /-- Arguments of a telescope. -/
  hasArgs : ∀ {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps}
    {Θ : Telescope k Γ ps} {γ : GradeVector Γ.length},
    WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → HasArgs sig ctx ts Θ →
      UsageArgs sig γ .oneOne ts →
        ∀ ρ, RunValidArgsRen sigM ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time, in every environment that binds the scope through
a renaming, in a well-formed signature `Σ` that gives the entries of `Σ_T` their meaning, when the
program realizes the constants of `Σ_T` of the mode `11ᵐ`. -/
theorem fundamentalIn : FundamentalIn := by
  suffices H : Derivations.Conclusion
      (hasType := fun sig {k Γ} ctx t A _ => ∀ {ι P sigM} {hΓ : Γ.FirstOrder}
        {γ : GradeVector Γ.length}, WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig →
          Usage sig γ .oneOne t →
            ∀ ρ, RunValidRen sigM ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ))
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => ∀ {ι P sigM} {hΓ : Γ.FirstOrder}
        {γ : GradeVector Γ.length}, WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig →
          UsageArgs sig γ .oneOne ts →
            ∀ ρ, RunValidArgsRen sigM ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)) from
    ⟨fun hw hι hP h hU => H.hasType h hw hι hP hU, fun hw hι hP h hU => H.hasArgs h hw hι hP hU⟩
  apply Derivations.induction
  case hasType_var =>
    refine fun hctx hx hctx_ih => fun hw hι hP hU => ?_
    exact fun ρ => by
      obtain ⟨δ, hγ, hts⟩ := Usage.inv_var hU rfl
      cases hts
      refine RunValidRen.sub hγ (RunValidRen.var (hx.substLevels _) ?_)
      simp [GradeVector.add, GradeVector.update, Sic.Math.Vector.zero, Mode.grade, Mode.erased]
      rfl
  case hasType_secondOrder =>
    intro sig k Γ ps ψ ctx X Θ A ts hX hts hts_ih ι P sigM hΓ γ hw hι hP hU
    exact nomatch hΓ _ X.mem
  case hasType_const =>
    intro sig k Γ ctx f j k' g m p A qs ls ps hctx h hqp hl hctx_ih ι P sigM hΓ γ hw hι hP hU
    exact fun ρ => by
      have hdT := (presuppositions.wfCtx hctx).distinct
      obtain ⟨-, hm⟩ := Usage.inv_const hdT h hU rfl
      have hm' : _ = Mode.oneOne := (by decide : ∀ m : Mode, Mode.oneOne ·ᵐ m = .oneOne →
        m = .oneOne) _ hm
      subst hm'
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have hc := RunValidRen.const (hΓ := hΓ) (ctx := ctx.atLevels ρ) (γ := γ)
        (hP h qs _ ps hqp hl')
      rw [Signature.instanceType, Term.weakenClosed_nil, List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
  case hasType_univ =>
    refine fun hctx hctx_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.erased (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.univ hctx) ρ) rfl
  case hasType_prop =>
    refine fun hctx hctx_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.erased (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.prop hctx) ρ) rfl
  case hasType_inst =>
    refine fun h hqp hl hadm has has_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.erased
        (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.inst h hqp hl hadm has) ρ) rfl
  case hasType_equality =>
    refine fun hA ht hu hA_ih ht_ih hu_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.erased
        (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.equality hA ht hu) ρ) rfl
  case hasType_reflProof =>
    refine fun hA ht hA_ih ht_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.proof
        (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.equality hA ht ht) ρ) rfl
  case hasType_transp =>
    exact fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih => fun hw hι hP hU =>
      (Usage.inv_transp hU rfl).elim
  case hasType_propExt =>
    refine fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.proof (soundnessIn.hasType hw.distinct hw.liftsInOrder hι
        (.equality (.prop (contextPresuppositions.hasType hA)) hA hB) ρ) rfl
  case hasType_coind =>
    refine fun h hqp hl hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih
        ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.proof (soundnessIn.hasType hw.distinct hw.liftsInOrder hι
        (.equality (.inst h.hasDeclaredType hqp hl hadm has) ht₁ ht₂) ρ) rfl
  case hasType_ctor =>
    intro sig k Γ ctx decl D T con qs ls ps as h hc hqp hl hadm has ts hts has_ih hts_ih ι P sigM
      hΓ γ hw hι hP hU
    exact fun ρ => by
      have hdT := (presuppositions.hasArgs hts).distinct
      obtain ⟨γ', hγ, hus⟩ := Usage.inv_ctor hdT h hc hqp hU rfl
      obtain ⟨hM, hv⟩ := hι.hasDataType h
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := ValidInstanceArgs.atLevels hl
        (soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has) ρ
      have hts' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hts ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hrun := hts_ih (hΓ := hΓ) hw hι hP hus ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hrun
      have hc' := RunValidRen.ctor (P := P) hw.distinct hM hv hc hqp hl' hadm
        has' (by rw [List.getFin_map]; exact hts')
        (by rw [List.getFin_map]; exact hrun)
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact RunValidRen.sub hγ hc'
  case hasType_recursor =>
    intro sig k Γ ctx decl D T qs ls ps as r ς χ t Cs us κ h' C h hqp hl hadm has ht hh hC hCl hCs
      hCt hul hus Rs hRs hut hκ has_ih ht_ih hCt_ih hut_ih ι P sigM hΓ γ hw hι hP hU
    exact fun ρ => by
      have hdT := (presuppositions.hasType ht).distinct
      obtain ⟨γ', _, δs, gs, πs, hγ, -, htu, hRU, hbu, hg, hχ, hr, hprop, -⟩ :=
        Usage.inv_recursor hdT h hqp hl hU rfl
      obtain ⟨hM, hv⟩ := hι.hasDataType h
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := ValidInstanceArgs.atLevels hl
        (soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has) ρ
      have ht' := soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ
      rw [Term.atLevels_inst] at ht'
      have hprem : ValidRecursorPremises sigM ι (ctx.atLevels ρ) decl qs (ls.map (Level.atLevels ρ))
          ps hqp (as.atLevels ρ)
          (Cs.atLevels ρ)
          (us.atLevels ρ)
          (κ.atLevels ρ) :=
        ValidRecursorPremises.atLevels ρ hCs (fun j T' C' hj hC' =>
          soundnessIn.hasType hw.distinct hw.liftsInOrder hι (hCt j T' C' hj hC') ρ) hus
      have hRs' : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
          ∃ πs, Constructor.ResultTypes sigM ⟨κ.quality, r, ς⟩ con hqp.inst decl.names
            ((ls.map (Level.atLevels ρ)).getFin hl')
            (as.atLevels ρ)
            (Lifting.ofMotives decl.names qs
              (ls.map (Level.atLevels ρ)) ps
              (as.atLevels ρ)
              (κ.atLevels ρ).level χ
              (Cs.atLevels ρ))
            ((Rs con).atLevels ρ) πs :=
        fun i j T' con hi => (hRs i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h
      -- The factors of the results that the usage reads are those of the typing.
      have hRsπ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
          Constructor.ResultTypes sigM ⟨κ.quality, r, ς⟩ con hqp.inst decl.names
            ((ls.map (Level.atLevels ρ)).getFin hl')
            (as.atLevels ρ)
            (Lifting.ofMotives decl.names qs
              (ls.map (Level.atLevels ρ)) ps
              (as.atLevels ρ)
              (κ.atLevels ρ).level χ
              (Cs.atLevels ρ))
            ((Rs con).atLevels ρ) (πs i) :=
        fun i j T' con hi => by
          obtain ⟨πs', h₁⟩ := hRs i j T' con hi
          obtain ⟨R, h₂⟩ := hRU i j T' con hi
          obtain ⟨-, hπ⟩ := Terms.ResultTypes.unique hdT h₁ h₂
          subst hπ
          exact Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1)
            _ h₁
      have hut' : ∀ i j T' con C' u₁ u₂, decl.cases[i]? = some (j, T', con) →
          (Cs.atLevels ρ).get j = some ⟨0, C'⟩ →
          (us.atLevels ρ).get i =
            some ⟨(con.params hqp.inst).length,
              (con.nestResultParams hqp.inst decl.names).length, u₁⟩ →
          (us.atLevels ρ).get i =
            some ⟨(con.params hqp.inst).length,
              (con.nestResultParams hqp.inst decl.names).length, u₂⟩ →
          ValidEqTermΓ sigM ι (((ctx.atLevels ρ).append (con.fieldsAt hqp.inst
            ((ls.map (Level.atLevels ρ)).getFin hl')
            (as.atLevels ρ))).append
              ((Rs con).atLevels ρ)) u₁ u₂
            ((C'.atCtor T'.name qs (ls.map (Level.atLevels ρ)) ps
              (as.atLevels ρ) con.name
              (con.params hqp.inst)).rename (Ren.weakenN _)) :=
        fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ => by
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
        obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
        cases Branches.get_inj hu₀ hu₀'
        have hb :=
          soundnessIn.hasType hw.distinct hw.liftsInOrder hι (hut i j T' con C₀ u₀ hi hC₀ hu₀) ρ
        simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
        erw [Term.atCtor_substLevels] at hb
        rw [List.getFin_map]
        exact hb
      have hrec : ∀ j T' C', decl.dataTypes[j]? = some T' →
          (Cs.atLevels ρ).get j = some ⟨0, C'⟩ →
          ∀ σ, EqSubst sigM ι (ctx.atLevels ρ) σ σ → ∀ t₁ t₂,
          ValidEqTerm₀ sigM ι t₁ t₂ ((Term.inst T'.name qs
            (ls.map (Level.atLevels ρ)) ps
            (as.atLevels ρ)).subst σ) →
          ValidEqTerm₀ sigM ι (.recursor r ς χ T'.name qs
            (ls.map (Level.atLevels ρ)) ps
            ((as.atLevels ρ).subst σ) t₁
            (κ.atLevels ρ)
            ((Cs.atLevels ρ).subst σ)
            ((us.atLevels ρ).subst σ))
            (.recursor r ς χ T'.name qs
            (ls.map (Level.atLevels ρ)) ps
            ((as.atLevels ρ).subst σ) t₂
            (κ.atLevels ρ)
            ((Cs.atLevels ρ).subst σ)
            ((us.atLevels ρ).subst σ))
            ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)) :=
        fun j T' C' hj hC' σ hσ t₁ t₂ ht₀ =>
          ValidEqTerm₀.recursor_block hι hw.liftsInOrder h hqp hl' hl' hadm ht'.1.1 has'
            hprem hprem.branches hRs' hRs' hut' hκ hσ hj hC' ht₀
      have htr : r ∉ Mode.oneOne.erased → RunValidRen sigM ι P hΓ (ctx.atLevels ρ) γ'
          (t.atLevels ρ) _ := fun hr' => by
        have htr := ht_ih (hΓ := hΓ) hw hι hP
          ((Mode.erasesUncounted .oneOne).mode _ hr' ▸ htu) ρ
        simp only [Term.atLevels, Term.substLevels] at htr
        exact htr
      have husr : RunValidBranches sigM ι P hΓ (ctx.atLevels ρ) decl qs
          (ls.map (Level.atLevels ρ)) ps hqp hl'
          (as.atLevels ρ)
          (Cs.atLevels ρ)
          (us.atLevels ρ) δs gs
          (fun con => (Rs con).atLevels ρ) :=
        fun i j T' con C' u hi hC' hu₁ => by
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
        have hb := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ (hΓ := (hΓ.extend _).extend _) hw hι hP
          (hbu i j T' con u₀ hi hu₀) ρ
        simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
        erw [Term.atCtor_substLevels] at hb
        simp only [Branches.atLevels, Branches.grades_substLevels]
        rw [List.getFin_map]
        exact hb
      -- The context of each branch is meaningful, and the types of its recursive results are
      -- terms of universes, by the typing of the branch.
      have hctx : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
          ValidCtx₀ sigM ι (((ctx.atLevels ρ).append (con.fieldsAt hqp.inst
            ((ls.map (Level.atLevels ρ)).getFin hl')
            (as.atLevels ρ))).append
              ((Rs con).atLevels ρ)) :=
        fun i j T' con hi => by
          have hjT := TypeDeclaration.dataTypes_getElem?_of_cases (List.mem_of_getElem? hi)
          obtain ⟨C', hC'⟩ := hprem.motives j T' hjT
          obtain ⟨u, hu₁⟩ := hprem.branches i j T' con hi
          exact (hut' i j T' con C' u u hi hC' hu₁ hu₁).1.1
      have hsorts : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) → ∀ θ,
          EqSubst sigM ι ((ctx.atLevels ρ).append (con.fieldsAt hqp.inst
            ((ls.map (Level.atLevels ρ)).getFin hl')
            (as.atLevels ρ))) θ θ →
          Telescope.ValidSorts₀ sigM ι
            (((Rs con).atLevels ρ).subst θ) :=
        fun i j T' con hi θ hθ => by
          have hjT := TypeDeclaration.dataTypes_getElem?_of_cases (List.mem_of_getElem? hi)
          obtain ⟨C₀, hC₀⟩ := hCs j T' hjT
          obtain ⟨u₀, hu₀⟩ := hus i j T' con hi
          have hwf := contextPresuppositions.hasType (hut i j T' con C₀ u₀ hi hC₀ hu₀)
          have hs := WfCtx.validSorts hw.distinct hw.liftsInOrder hι _ _ hwf ρ θ (by
            simp only [Context.atLevels, Constructor.fieldsAt_substLevels,
              Context.substLevels_append]
            rw [List.getFin_map] at hθ
            exact hθ)
          exact hs
      have hc := RunValidRen.recursor (P := P) (γ := γ') hw.distinct hw.liftsInOrder hM hv hadm
        has' hh (Motives.get_substLevels_of _ hC) hprem
        ⟨hRsπ, hctx, hsorts, hrec, fun i j T' con l p hi hl => by
          simpa only [Branches.atLevels, Branches.grades_substLevels,
            show Mode.oneOne.grade = Grade.one from rfl, Grade.modality.semiring.one_mul]
            using hg i j T' con l p hi hl,
          fun i j T' con hi => by
            simpa only [Branches.atLevels, Branches.grades_substLevels] using hχ i j T' con hi⟩
        ht' htr husr (hr rfl) (fun hq' => match hc : decl.cases with
          | [] => rfl
          | _ :: _ => absurd rfl (hprop hq' (hc ▸ List.cons_ne_nil _ _)))
        hw.erasesPropDestructors
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_single]
      simp only [Term.substLevels]
      exact RunValidRen.sub hγ hc
  case hasType_obs =>
    intro sig k Γ ctx decl D T qs ls ps as t d p q ς ps' Ξ Θ B ψ bs h hqp hl hadm hd has ht hbs
      has_ih ht_ih hbs_ih ι P sigM hΓ γ hw hι hP hU
    exact fun ρ => by
      have hWf := presuppositions.hasType ht
      obtain ⟨γ', δ, hγ, hut, hbus, hm⟩ := Usage.inv_obs hWf.distinct h hqp hd hU rfl
      have hpr : _ ∉ Mode.oneOne.erased := (by decide : ∀ p : Grade,
        Mode.oneOne ·ᵐ p.mode = .oneOne → p ∉ Mode.oneOne.erased) _ hm
      obtain ⟨hM, hv⟩ := hι.hasCodataType h
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := ValidInstanceArgs.atLevels hl
        (soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has) ρ
      have ht' := soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ
      rw [Term.atLevels_inst] at ht'
      have htr := ht_ih (hΓ := hΓ) hw hι hP hut ρ
      simp only [Term.atLevels, Term.substLevels] at htr
      have hbs' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hbs ρ
      have hbr := hbs_ih (hΓ := hΓ) hw hι hP hbus ρ
      have hcl := fun {a} (x : Var Ξ a) =>
        hd.obsSubst_observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps as t x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs' hbr
      have hc := RunValidRen.obs hw.distinct hM hv hqp hl' hadm
        has' hd
        hpr (hWf.destructor_mode h hadm hd) ht' htr (by rw [List.getFin_map]; exact hbs')
        (by rw [List.getFin_map]; exact hbr)
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact RunValidRen.sub hγ hc
  case hasType_corec =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' ps' S ss h hqp hl hadm hpre has hh hS hss
      hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih hgt_ih ι P sigM hΓ γ hw hι hP hU
    exact fun ρ => by
      have hdT := (presuppositions.hasArgs hss).distinct
      obtain ⟨γ', δ, δs, hγ, -, hssu, hgu, hδ, -⟩ := Usage.inv_corec hdT h hqp hh hS hU rfl
      obtain ⟨hM, hv⟩ := hι.hasCodataType h
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := ValidInstanceArgs.atLevels hl
        (soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has) ρ
      have hss' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hss ρ
      have hssr := fun hr => hss_ih (hΓ := hΓ) hw hι hP
        ((Mode.erasesUncounted .oneOne).mode _ hr ▸ hssu) ρ
      have hc := RunValidRen.corec (P := P) (γ := γ') hw.distinct hM hv hqp hl' hadm
        has' (fun he e he' => (hι e (hpre he e he')).1) hh
        (States.get_substLevels_of _ hS) hss' hssr
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hqp hl hgs
          (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
            soundnessIn.hasType hw.distinct hw.liftsInOrder hι
              (hgt i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
        (RunValidCorecBranches.atLevels hqp hl
          (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hpr =>
            hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hw hι hP
              ((Mode.erasesUncounted .oneOne).mode _ hpr ▸
                hgu i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
        hδ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact RunValidRen.sub hγ hc
  case hasType_conv =>
    refine fun ht h ht_ih h_ih => fun hw hι hP hU => ?_
    exact fun ρ =>
      RunValidRen.conv (soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ)
        (soundnessIn.eqType hw.distinct hw.liftsInOrder hι h ρ) (ht_ih hw hι hP hU ρ)
  case hasArgs_nil =>
    refine fun hctx hctx_ih => fun hw hι hP hU => ?_
    cases hU with
    | nil => exact fun _ => RunValidArgsRen.nil
  case hasArgs_cons =>
    intro sig k Γ ps ctx q p t A ts Θ ht hts ht_ih hts_ih ι P sigM hΓ γ hw hι hP hU
    cases hU with
    | cons hu hus =>
      exact fun ρ => by
        have hts' := hts_ih (hΓ := hΓ) hw hι hP hus ρ
        simp only [Telescope.atLevels] at hts'
        rw [Telescope.substLevels_subst₀_single] at hts'
        exact RunValidArgsRen.cons hw.distinct (fun hp => ht_ih hw hι hP
          ((Mode.erasesUncounted .oneOne).mode _ hp ▸ hu) ρ) hts'
  all_goals intros; trivial

end Sic.Core
