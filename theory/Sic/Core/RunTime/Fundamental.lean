module

public import Sic.Core.Lifting.Extension
public import Sic.Core.RunTime.Relation.Corecursors
public import Sic.Core.RunTime.Relation.Recursors.Results
public import Sic.Core.Typing
public import Sic.Core.Usage
import Sic.Core.Results.Extension
import Sic.Core.Results.Functionality
import Sic.Core.Results.Substitution
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Observations
import Sic.Core.RunTime.Relation.Recursors
import Sic.Core.RunTime.Relation.Rules
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature
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

The proof is by induction on the typing, `Derivable.fundamental`, as the soundness of the typing
is: each case inverts the usage of the term, `Usage.inv_…`, which gives
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

-- ADE: none.
/-- The program `𝒫` realizes the constants of the signature `Σ_T` of the mode `11ᵐ` of run time, in
the signature `Σ`: each of them, at each closed instance of its variables, is valid at run time in
the empty context, at its type at this instance. -/
def Program.Realizes (sig : Signature) (ι : Interpretation) (P : Program) (sigT : Signature) :
    Prop :=
  ∀ {f : Name} {j k' g : Nat} {p : Grade} {A : Instance j g → Term k' []},
    sigT.HasConstant f j k' g .oneOne p A →
      ∀ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (hq : qs.length = j)
        (hl : ls.length = k') (hp : ps.length = g),
        RunValid sig ι P Scope.FirstOrder.nil .empty 𝟘ᶜ (.const f qs ls ps)
          (Signature.instanceType A (.ofLists qs ps hq hp) (ls.getFin hl))

-- ADE: none.
/-- The premise of `(corec)` at run time on its branches, each branch valid at run time for every
value of the level variables, in every environment that binds its scope through a renaming, when the
grade of its destructor is used at run time, holds at the levels without variables `ρ`, as
`CorecBranchesEqValid.atLevels` does for the meaning. -/
theorem RunValidCorecBranches.atLevels {sig : Signature} {ι : Interpretation} {P : Program}
    {k : Nat} {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {decl : TypeDeclaration}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs : DestructorBranches k Γ} {δs : Nat → GradeVector Γ.length}
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → p ∉ Mode.oneOne.erased → ∀ ρ,
      RunValidRen sig ι P ((hΓ.extend _).extend _)
        (((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))).atLevels ρ)
        (((δs i).extendParams (Mode.oneOne.grade * r) ps'').extendParams Mode.oneOne.grade ps₁)
        (g.atLevels ρ)
        ((Term.branchResult decl.names B
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))).atLevels ρ))
    (ρ : Fin k → Nat) :
    RunValidCorecBranches sig ι P hΓ (ctx.atLevels ρ) decl qs
      (ls.map (Level.subst fun i => .ofNat (ρ i))) ps hq ((List.length_map _).trans hl) hp
      (as.substLevels fun i => .ofNat (ρ i)) r (Ss.substLevels fun i => .ofNat (ρ i))
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

-- ADE: none.
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
      | WfCtx.var hA' =>
        cases hA' with
        | WfType.univType hT => exact ⟨_, hT⟩
        | WfType.propType hT => exact ⟨_, hT⟩
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

-- ADE: none.
/-- What a typing, or a typing of arguments, in the signature `Σ_T` says of the terms used in the mode
`11ᵐ`, in a context whose variables are all of the first order, in a well-formed signature `Σ` that
gives the entries of `Σ_T` their meaning, when the program `𝒫` realizes the constants of `Σ_T` of
the mode `11ᵐ`: that they are valid at run time. -/
def Judgment.Fundamental : Judgment → Prop
  | @hasType sig k Γ ctx t A => ∀ {ι : Interpretation} {P : Program} {sigM : Signature}
      {hΓ : Γ.FirstOrder} {γ : GradeVector Γ.length},
      WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → Usage sig γ .oneOne t →
        ∀ ρ : Fin k → Nat,
          RunValidRen sigM ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ)
  | @hasArgs sig k Γ _ ctx ts Θ => ∀ {ι : Interpretation} {P : Program} {sigM : Signature}
      {hΓ : Γ.FirstOrder} {γ : GradeVector Γ.length},
      WfSig sigM → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → UsageArgs sig γ .oneOne ts →
        ∀ ρ : Fin k → Nat,
          RunValidArgsRen sigM ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)
  | _ => True

-- ADE: none.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time, as `Judgment.Fundamental` says, by induction on
its derivation. -/
theorem Derivable.fundamental {J : Judgment} (h : Derivable J) : J.Fundamental := by
  induction h with
  | HasType.var hctx hx hctx_ih =>
    intro ι P sigM hΓ γ hw hι hP hu ρ
    obtain ⟨δ, hγ, hts⟩ := Usage.inv_var hu rfl
    cases hts
    refine RunValidRen.sub hγ (RunValidRen.var (hx.substLevels _) ?_)
    simp [GradeVector.add, GradeVector.update, Sic.Math.Vector.zero, Mode.grade, Mode.erased]
    rfl
  | HasType.secondOrder _ _ _ =>
    rename_i X _ _ _ _ _ _
    intro ι P sigM hΓ γ hw hι hP _
    exact nomatch hΓ _ X.mem
  | HasType.const hctx h hq hl hp hctx_ih =>
    intro ι P sigM hΓ γ hw hι hP hu
    rename_i ctx _ _ _ _ m _ _ qs ls ps
    intro ρ
    have hdT := (presuppositions.wfCtx hctx).distinct
    obtain ⟨-, hm⟩ := Usage.inv_const hdT h hu rfl
    have hm' : _ = Mode.oneOne := (by decide : ∀ m : Mode, Mode.oneOne ·ᵐ m = .oneOne →
      m = .oneOne) _ hm
    subst hm'
    have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
      (List.length_map _).trans hl
    have hc := RunValidRen.const (hΓ := hΓ) (ctx := ctx.atLevels ρ) (γ := γ)
      (hP h qs _ ps hq hl' hp)
    rw [Signature.instanceType, Term.weakenClosed_nil, List.getFin_map] at hc
    simp only [Term.atLevels, Signature.instanceType_substLevels]
    exact hc
  | HasType.univ hctx hctx_ih =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.erased (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.univ hctx) ρ) rfl
  | HasType.prop hctx hctx_ih =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.erased (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.prop hctx) ρ) rfl
  | HasType.inst h hq hl hp hadm has has_ih =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.erased
      (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.inst h hq hl hp hadm has) ρ) rfl
  | HasType.equality hA ht hu hA_ih ht_ih hu_ih =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.erased
      (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.equality hA ht hu) ρ) rfl
  | HasType.reflProof hA ht hA_ih ht_ih =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.proof
      (soundnessIn.hasType hw.distinct hw.liftsInOrder hι (.equality hA ht ht) ρ) rfl
  | HasType.transp _ _ _ _ _ _ _ _ _ _ _ _ =>
    intro ι P sigM hΓ γ hw hι hP hu
    exact (Usage.inv_transp hu rfl).elim
  | HasType.propExt hA hB _ _ hA_ih hB_ih _ _ =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.proof (soundnessIn.hasType hw.distinct hw.liftsInOrder hι
      (.equality (.prop (contextPresuppositions.hasType hA)) hA hB) ρ) rfl
  | HasType.coind h hq hl hp hadm has _ _ _ _ ht₁ ht₂ _ _ _ _ _ _ _ _ has_ih _ ht₁_ih ht₂_ih _ _ _ _
      =>
    intro ι P sigM hΓ γ hw hι hP _ ρ
    exact RunValidRen.proof (soundnessIn.hasType hw.distinct hw.liftsInOrder hι
      (.equality (.inst h.hasDeclaredType hq hl hp hadm has) ht₁ ht₂) ρ) rfl
  | HasType.ctor h hc hq hl hp hadm has hts has_ih hts_ih =>
    intro ι P sigM hΓ γ hw hι hP hu
    rename_i ls _ _ _
    intro ρ
    have hdT := (presuppositions.hasArgs hts).distinct
    obtain ⟨γ', hγ, hus⟩ := Usage.inv_ctor hdT h hc hq hp hu rfl
    obtain ⟨hM, hv⟩ := hι.hasDataType h
    have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
      (List.length_map _).trans hl
    have has' := soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has ρ
    simp only [Context.atLevels, Context.substLevels_substLevels] at has'
    have hts' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hts ρ
    simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
    have hrun := (hts_ih (hΓ := hΓ) hw hι hP hus) ρ
    simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hrun
    have hc' := RunValidRen.ctor (P := P) hw.distinct hM hv hc hq hl' hp hadm
      (by rw [List.getFin_map]; exact has') (by rw [List.getFin_map]; exact hts')
      (by rw [List.getFin_map]; exact hrun)
    simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
    exact RunValidRen.sub hγ hc'
  | HasType.recursor h hq hl hp hadm has ht hh hC _ hCs hCt _ hus hRs hut hκ has_ih ht_ih hCt_ih
      hut_ih =>
    intro ι P sigM hΓ γ hw hι hP hu
    rename_i ctx decl _ _ qs ls ps as r ς χ' t Cs us κ _ _ _ _ Rs
    intro ρ
    rename_i Rs
    have hdT := (presuppositions.hasType ht).distinct
    obtain ⟨γ', χ, δs, gs, πs, hγ, -, htu, hRU, hbu, hg, hχ, hr, hprop, -⟩ :=
      Usage.inv_recursor hdT h hq hl hp hu rfl
    obtain ⟨hM, hv⟩ := hι.hasDataType h
    have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
      (List.length_map _).trans hl
    have has' := soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has ρ
    simp only [Context.atLevels, Context.substLevels_substLevels] at has'
    have has'' : ValidInstanceArgsΓ sigM ι (ctx.atLevels ρ)
        (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
        ((decl.params (.ofLists qs ps hq hp)).substLevels
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')) := by
      rw [List.getFin_map]; exact has'
    have ht' := soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ
    simp only [Context.atLevels, Term.atLevels, Term.substLevels] at ht'
    have hCs' : ∀ j T', decl.dataTypes[j]? = some T' →
        ∃ C', (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ :=
      fun j T' hj => let ⟨_, hC'⟩ := hCs j T' hj; ⟨_, Motives.get_substLevels_of _ hC'⟩
    have hCv : ∀ j T' C', decl.dataTypes[j]? = some T' →
        (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ →
        ValidTermΓ sigM ι ((ctx.atLevels ρ).var (.inst T'.name qs
          (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0)))) C'
          (.sort (κ.substLevels fun i => (.ofNat (ρ i) : Level 0))) := fun j T' C' hj hC' => by
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
      have hCv := soundnessIn.hasType hw.distinct hw.liftsInOrder hι (hCt j T' C₀ hj hC₀) ρ
      simp only [Context.atLevels, Context.substLevels, Term.atLevels, Term.substLevels] at hCv
      exact hCv
    have husN : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
          some ⟨(con.params (.ofLists qs ps hq hp)).length,
            (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ :=
      fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩
    have hRs' : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sigM ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
          (Lifting.ofMotives decl.names qs
            (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
            (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
            (κ.substLevels fun i => (.ofNat (ρ i) : Level 0)).level χ'
            (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)))
          ((Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0)) πs :=
      fun i j T' con hi => (hRs i j T' con hi).imp fun _ h =>
        Terms.ResultTypes.ofTypeDeclarations (fun _ he => (hι _ he).1)
          (Constructor.ResultTypes.substLevels_ofMotives _ h)
    -- The factors of the results that the usage reads are those of the typing.
    have hRsπ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        Constructor.ResultTypes sigM ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
          (Lifting.ofMotives decl.names qs
            (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
            (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
            (κ.substLevels fun i => (.ofNat (ρ i) : Level 0)).level χ'
            (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)))
          ((Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0)) (πs i) :=
      fun i j T' con hi => by
        obtain ⟨πs', h₁⟩ := hRs i j T' con hi
        obtain ⟨R, h₂⟩ := hRU i j T' con hi
        obtain ⟨-, hπ⟩ := Terms.ResultTypes.unique hdT h₁ h₂
        subst hπ
        exact Terms.ResultTypes.ofTypeDeclarations (fun _ he => (hι _ he).1)
          (Constructor.ResultTypes.substLevels_ofMotives _ h₁)
    have hut' : ∀ i j T' con C' u₁ u₂, decl.cases[i]? = some (j, T', con) →
        (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ →
        (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
          some ⟨(con.params (.ofLists qs ps hq hp)).length,
            (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
        (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
          some ⟨(con.params (.ofLists qs ps hq hp)).length,
            (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
        ValidEqTermΓ sigM ι (((ctx.atLevels ρ).append (con.fieldsAt (.ofLists qs ps hq hp)
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0)))).append
            ((Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0))) u₁ u₂
          ((C'.atCtor T'.name qs (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
            (as.substLevels fun i => (.ofNat (ρ i) : Level 0)) con.name
            (con.params (.ofLists qs ps hq hp))).rename (Ren.weakenN _)) :=
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
        (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ →
        ∀ σ, EqSubst sigM ι (ctx.atLevels ρ) σ σ → ∀ t₁ t₂,
        ValidEqTerm₀ sigM ι t₁ t₂ ((Term.inst T'.name qs
          (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0))).subst σ) →
        ValidEqTerm₀ sigM ι (.recursor r ς χ' T'.name qs
          (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
          ((as.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ) t₁
          (κ.substLevels fun i => (.ofNat (ρ i) : Level 0))
          ((Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ)
          ((us.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ))
          (.recursor r ς χ' T'.name qs
          (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
          ((as.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ) t₂
          (κ.substLevels fun i => (.ofNat (ρ i) : Level 0))
          ((Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ)
          ((us.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ))
          ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)) :=
      fun j T' C' hj hC' σ hσ t₁ t₂ ht₀ =>
        ValidEqTerm₀.recursor_block hι hw.liftsInOrder h hq hl' hl' hp hadm ht'.1.1 has'' hCs' hCv
          husN husN
          hRs' hRs' hut' hκ hσ hj hC' ht₀
    have htr : r ∉ Mode.oneOne.erased → RunValidRen sigM ι P hΓ (ctx.atLevels ρ) γ'
        (t.substLevels fun i => (.ofNat (ρ i) : Level 0)) _ := fun hr' => by
      have htr := (ht_ih (hΓ := hΓ) hw hι hP ((Mode.erasesUncounted .oneOne).mode _ hr' ▸ htu)) ρ
      simp only [Term.atLevels, Term.substLevels] at htr
      exact htr
    have husr : RunValidBranches sigM ι P hΓ (ctx.atLevels ρ) decl qs
        (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps hq hl' hp
        (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
        (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0))
        (us.substLevels fun i => (.ofNat (ρ i) : Level 0)) δs gs
        (fun con => (Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0)) :=
      fun i j T' con C' u hi hC' hu₁ => by
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
      have hb := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ (hΓ := (hΓ.extend _).extend _) hw hι hP
        (hbu i j T' con u₀ hi hu₀) ρ
      simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
      erw [Term.atCtor_substLevels] at hb
      simp only [Branches.grades_substLevels]
      rw [List.getFin_map]
      exact hb
    -- The context of each branch is meaningful, and the types of its recursive results are
    -- terms of universes, by the typing of the branch.
    have hctx : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ValidCtx₀ sigM ι (((ctx.atLevels ρ).append (con.fieldsAt (.ofLists qs ps hq hp)
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0)))).append
            ((Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0))) :=
      fun i j T' con hi => by
        have hjT := (TypeDeclaration.getElem?_of_mem_casesFrom (List.mem_of_getElem? hi)).2
        rw [Nat.sub_zero] at hjT
        obtain ⟨C', hC'⟩ := hCs' j T' hjT
        obtain ⟨u, hu₁⟩ := husN i j T' con hi
        exact (hut' i j T' con C' u u hi hC' hu₁ hu₁).1.1
    have hsorts : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) → ∀ θ,
        EqSubst sigM ι ((ctx.atLevels ρ).append (con.fieldsAt (.ofLists qs ps hq hp)
          ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0)))) θ θ →
        Telescope.ValidSorts₀ sigM ι
          (((Rs con).substLevels fun i => (.ofNat (ρ i) : Level 0)).subst θ) :=
      fun i j T' con hi θ hθ => by
        have hjT := (TypeDeclaration.getElem?_of_mem_casesFrom (List.mem_of_getElem? hi)).2
        rw [Nat.sub_zero] at hjT
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
      has'' hh (Motives.get_substLevels_of _ hC) hCs' hCv husN hRsπ hctx hsorts hrec ht' htr husr
      (fun i j T' con l p hi hl => by
        simpa only [Branches.grades_substLevels] using hg i j T' con l p hi hl)
      (fun i j T' con hi => by
        simpa only [Branches.grades_substLevels] using hχ i j T' con hi)
      (hr rfl) (fun hq' => match hc : decl.cases with
        | [] => rfl
        | _ :: _ => absurd rfl (hprop hq' (hc ▸ List.cons_ne_nil _ _)))
      (fun {_ _ _} hT {_ _} _ _ hI hκ' {_ _ _ _ _ _ _ _ _} hpos =>
        WfSig.destructor_erased hw hT hI hpos hκ')
    simp only [Term.atLevels]
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
      (fun x => by cases x <;> rfl)]
    simp only [Term.substLevels]
    exact RunValidRen.sub hγ hc
  | HasType.obs h hq hl hp hadm hpos has ht hbs has_ih ht_ih hbs_ih =>
    intro ι P sigM hΓ γ hw hι hP hu
    rename_i D _ qs ls ps as t d p _ _ ps' Ξ _ _ _ _
    intro ρ
    have hWf := presuppositions.hasType ht
    obtain ⟨γ', δ, hγ, hut, hbus, hm⟩ := Usage.inv_obs hWf.distinct h hq hp hpos hu rfl
    have hpr : _ ∉ Mode.oneOne.erased := (by decide : ∀ p : Grade,
      Mode.oneOne ·ᵐ p.mode = .oneOne → p ∉ Mode.oneOne.erased) _ hm
    obtain ⟨hM, hv⟩ := hι.hasCodataType h
    have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
      (List.length_map _).trans hl
    have has' := soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has ρ
    simp only [Context.atLevels, Context.substLevels_substLevels] at has'
    have ht' := soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ
    simp only [Term.atLevels, Term.substLevels] at ht'
    have htr := (ht_ih (hΓ := hΓ) hw hι hP hut) ρ
    simp only [Term.atLevels, Term.substLevels] at htr
    have hbs' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hbs ρ
    have hbr := (hbs_ih (hΓ := hΓ) hw hι hP hbus) ρ
    have hcl : ∀ {a} (x : Var Ξ a),
        ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).substLevels
          (fun i => (.ofNat (ρ i) : Level 0)) =
          hpos.obsSubst ((t.substLevels (fun i => (.ofNat (ρ i) : Level 0))).observation D qs
            (ls.map (Level.subst (fun i => (.ofNat (ρ i) : Level 0)))) ps
            (as.substLevels (fun i => (.ofNat (ρ i) : Level 0))))
            (as.substLevels (fun i => (.ofNat (ρ i) : Level 0))).toSubst x := fun x =>
      hpos.obsSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0))
        (fun d ps' => Term.observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps
          as t d ps')
        (InstanceArgs.toSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0)) as) x
    simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
      Telescope.substLevels_substLevels] at hbs' hbr
    have hc := RunValidRen.obs hw.distinct hM hv hq hl' hp hadm
      (by rw [List.getFin_map]; exact has') hpos
      hpr (hWf.destructor_mode h hadm hpos) ht' htr (by rw [List.getFin_map]; exact hbs')
      (by rw [List.getFin_map]; exact hbr)
    rw [List.getFin_map] at hc
    simp only [Term.atLevels, Term.substLevels_instantiate,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
      Term.substLevels, ← Args.terms_substLevels]
    exact RunValidRen.sub hγ hc
  | HasType.corec h hq hl hp hadm hpre has hh hS hss _ hSs _ _ hgs hgt has_ih hss_ih _ hgt_ih =>
    intro ι P sigM hΓ γ hw hι hP hu
    rename_i ls _ _ _ _ _ _ _ _ _ _ _ _ _
    intro ρ
    have hdT := (presuppositions.hasArgs hss).distinct
    obtain ⟨γ', δ, δs, hγ, -, hssu, hgu, hδ, -⟩ := Usage.inv_corec hdT h hq hp hh hS hu rfl
    obtain ⟨hM, hv⟩ := hι.hasCodataType h
    have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
      (List.length_map _).trans hl
    have has' := soundnessIn.hasInstanceArgs hw.distinct hw.liftsInOrder hι has ρ
    simp only [Context.atLevels, Context.substLevels_substLevels] at has'
    have hss' := soundnessIn.hasArgs hw.distinct hw.liftsInOrder hι hss ρ
    have hssr := fun hr => (hss_ih (hΓ := hΓ) hw hι hP ((Mode.erasesUncounted .oneOne).mode _ hr ▸ hssu)) ρ
    have hc := RunValidRen.corec (P := P) (γ := γ') hw.distinct hM hv hq hl' hp hadm
      (by rw [List.getFin_map]; exact has') (fun he e he' => (hι e (hpre he e he')).1) hh
      (States.get_substLevels_of _ hS) hss' hssr
      (fun j T' hj =>
        have ⟨ps'', S', hS'⟩ := hSs j T' hj
        ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
      (CorecBranchesValid.atLevels hq hl hp hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
          soundnessIn.hasType hw.distinct hw.liftsInOrder hι
            (hgt i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
      (RunValidCorecBranches.atLevels hq hl hp
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hpr =>
          hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hw hι hP
            ((Mode.erasesUncounted .oneOne).mode _ hpr ▸
              hgu i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
      hδ
    simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
    exact RunValidRen.sub hγ hc
  | HasType.conv ht h ht_ih h_ih =>
    intro ι P sigM hΓ γ hw hι hP hu ρ
    exact RunValidRen.conv (soundnessIn.hasType hw.distinct hw.liftsInOrder hι ht ρ)
      (soundnessIn.eqType hw.distinct hw.liftsInOrder hι h ρ) (ht_ih hw hι hP hu ρ)
  | HasArgs.nil _ _ =>
    intro ι P sigM hΓ γ hw hι hP hu _
    cases hu
    exact RunValidArgsRen.nil
  | HasArgs.cons ht hts ht_ih hts_ih =>
    intro ι P sigM hΓ γ hw hι hP hu' ρ
    rename_i t _ _ _
    cases hu' with
    | cons hu hus =>
      have hts' := (hts_ih (hΓ := hΓ) hw hι hP hus) ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact RunValidArgsRen.cons hw.distinct
        (fun hp => ht_ih hw hι hP ((Mode.erasesUncounted .oneOne).mode _ hp ▸ hu) ρ) hts'
  | _ => trivial

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time, in every environment that binds the scope through
a renaming, in a well-formed signature `Σ` that gives the entries of `Σ_T` their meaning, when the
program realizes the constants of `Σ_T` of the mode `11ᵐ`. -/
theorem fundamentalIn : FundamentalIn :=
  ⟨fun hw hι hP h => h.fundamental hw hι hP, fun hw hι hP h => h.fundamental hw hι hP⟩

end Sic.Core
