module

public import Sic.Core.RunTime.Corecursors
public import Sic.Core.Typing
public import Sic.Core.Usage
import Sic.Core.RunTime.DeclaredTypes
import Sic.Core.RunTime.Recursors
import Sic.Core.RunTime.Rules
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Judgments
import Sic.Core.Soundness.Recursors
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature
import Sic.Core.Usage.Inversion

/-!
# Fundamental Lemma of the Run Time

The fundamental lemma of annex 20 of RFC 36: a term typed and used in the mode `11ᵐ` of run time, in
a context whose variables are all of the first order, is valid at run time with its grades,
`Σ; γ; Γ ⊨^® t : A`, at every value of its level variables, when the program `𝒫` realizes the
constants of the mode `11ᵐ` of the signature, `(hyp_𝒫)`.

The proof is by mutual structural recursion on the typing, in the clause `where` of the theorem, as
the soundness of the typing is: each case inverts the usage of the term, `Usage.inv_…`, which gives
the grades of the rule of its form above those of the judgment, and concludes by the lemma of the
same name in `Rules`, `DeclaredTypes`, `Recursors` or `Corecursors`, from the validity at run time
of the subterms, at the usages that the inversion gives them, and from the meaning of their
typings, which the soundness gives, then by the subsumption `RunValid.sub`.
The usage checks in the mode `11ᵐ` again each subterm of a grade that `S^{11ᵐ}` does not erase, and
the erasure replaces the others, so that the recursion stays in the mode `11ᵐ`.

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
value of the level variables when the grade of its destructor is used at run time, holds at the
levels without variables `ρ`, as `CorecBranchesEqValid.atLevels` does for the meaning. -/
theorem RunValidCorecBranches.atLevels {sig : Signature} {ι : Interpretation} {P : Program}
    {k : Nat} {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {decl : TypeDeclaration}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs : CorecBranches k Γ} {δs : Nat → GradeVector Γ.length}
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
      gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → p ∉ Mode.oneOne.erased → ∀ ρ,
      RunValid sig ι P ((hΓ.extend _).extend _)
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
  intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg hpr
  obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
  obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_substLevels _ hg
  have hb := hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hpos hg₀ hpr ρ
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

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time, at every value of its level variables, in a
signature `Σ` whose names are distinct and that gives the entries of `Σ_T` their meaning, when the
program `𝒫` realizes the constants of `Σ_T` of the mode `11ᵐ`. -/
structure FundamentalIn : Prop where
  /-- A typing. -/
  hasType : ∀ {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {t A : Term k Γ} {γ : GradeVector Γ.length},
    sigM.Distinct → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → HasType sig ctx t A →
      Usage sig γ .oneOne t →
        ∀ ρ, RunValid sigM ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ)
  /-- Arguments of a telescope. -/
  hasArgs : ∀ {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps}
    {Θ : Telescope k Γ ps} {γ : GradeVector Γ.length},
    sigM.Distinct → sigM.ValidEntries ι sig → P.Realizes sigM ι sig → HasArgs sig ctx ts Θ →
      UsageArgs sig γ .oneOne ts →
        ∀ ρ, RunValidArgs sigM ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed in the signature `Σ_T` and used in the mode `11ᵐ`, in a context whose variables
are all of the first order, is valid at run time in a signature `Σ` whose names are distinct and
that gives the entries of `Σ_T` their meaning, when the program realizes the constants of `Σ_T` of
the mode `11ᵐ`. -/
theorem fundamentalIn : FundamentalIn :=
  ⟨hasType, hasArgs⟩
where
  hasType {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
      {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {t A : Term k Γ} {γ : GradeVector Γ.length}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) (hP : P.Realizes sigM ι sig) :
      HasType sig ctx t A → Usage sig γ .oneOne t →
        ∀ ρ, RunValid sigM ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ)
    | .var hctx hx, hu => fun ρ => by
      obtain ⟨δ, hγ, hts⟩ := Usage.inv_var hu rfl
      cases hts
      refine RunValid.sub hγ (RunValid.var (hx.substLevels _) ?_)
      simp [GradeVector.add, GradeVector.update, Sic.Math.Vector.zero, Mode.grade, Mode.erased]
      rfl
    | .secondOrder (X := X) _ _, _ => nomatch hΓ _ X.mem
    | .const (qs := qs) (ls := ls) (ps := ps) hctx h hq hl hp, hu => fun ρ => by
      have hdT := (presuppositions.wfCtx hctx).distinct
      obtain ⟨-, hm⟩ := Usage.inv_const hdT h hu rfl
      have hm' : _ = Mode.oneOne := (by decide : ∀ m : Mode, Mode.oneOne ·ᵐ m = .oneOne →
        m = .oneOne) _ hm
      subst hm'
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have hc := RunValid.const (hΓ := hΓ) (ctx := ctx.atLevels ρ) (γ := γ)
        (hP h qs _ ps hq hl' hp)
      rw [Signature.instanceType, Term.weakenClosed_nil, List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .univ hctx, _ => fun ρ => RunValid.erased (soundnessIn.hasType hd hι (.univ hctx) ρ) rfl
    | .prop hctx, _ => fun ρ => RunValid.erased (soundnessIn.hasType hd hι (.prop hctx) ρ) rfl
    | .inst h hq hl hp hadm has, _ => fun ρ =>
      RunValid.erased (soundnessIn.hasType hd hι (.inst h hq hl hp hadm has) ρ) rfl
    | .conv ht h, hu => fun ρ =>
      RunValid.conv (soundnessIn.hasType hd hι ht ρ) (soundnessIn.eqType hd hι h ρ)
        (hasType hd hι hP ht hu ρ)
    | .ctor (ls := ls) h hc hq hl hp hadm has hts, hu => fun ρ => by
      have hdT := (presuppositions.hasArgs hts).distinct
      obtain ⟨γ', hγ, hus⟩ := Usage.inv_ctor hdT h hc hq hp hu rfl
      obtain ⟨hM, hv⟩ := hι.hasDataType h
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := soundnessIn.hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hts' := soundnessIn.hasArgs hd hι hts ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hrun := hasArgs (hΓ := hΓ) hd hι hP hts hus ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hrun
      have hc' := RunValid.ctor (P := P) hd hM hv hc hq hl' hp hadm
        (by rw [List.getFin_map]; exact has') (by rw [List.getFin_map]; exact hts')
        (by rw [List.getFin_map]; exact hrun)
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact RunValid.sub hγ hc'
    | .obs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (Ξ := Ξ) h hq hl hp hadm hpos
        has ht hbs, hu => fun ρ => by
      have hWf := presuppositions.hasType ht
      obtain ⟨γ', δ, hγ, hut, hbus, hm⟩ := Usage.inv_obs hWf.distinct h hq hp hpos hu rfl
      have hpr : _ ∉ Mode.oneOne.erased := (by decide : ∀ p : Grade,
        Mode.oneOne ·ᵐ p.mode = .oneOne → p ∉ Mode.oneOne.erased) _ hm
      obtain ⟨hM, hv⟩ := hι.hasCodataType h
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := soundnessIn.hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := soundnessIn.hasType hd hι ht ρ
      simp only [Term.atLevels, Term.substLevels] at ht'
      have htr := hasType (hΓ := hΓ) hd hι hP ht hut ρ
      simp only [Term.atLevels, Term.substLevels] at htr
      have hbs' := soundnessIn.hasArgs hd hι hbs ρ
      have hbr := hasArgs (hΓ := hΓ) hd hι hP hbs hbus ρ
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
      have hc := RunValid.obs hd hM hv hq hl' hp hadm (by rw [List.getFin_map]; exact has') hpos hpr
        (hWf.destructor_mode h hadm hpos) ht' htr (by rw [List.getFin_map]; exact hbs')
        (by rw [List.getFin_map]; exact hbr)
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact RunValid.sub hγ hc
    | .recursor (decl := decl) (qs := qs) (ls := ls) (ps := ps) (as := as) (r := r) (t := t)
        (Cs := Cs) (us := us) (κ := κ) (T := T) (C := C) h hq hl hp hadm has ht hh hC _ hCs hCt _ hus hut
        hκ, hu => fun ρ => by
      have hdT := (presuppositions.hasType ht).distinct
      obtain ⟨γ', χ, δs, gs, hγ, -, htu, hbu, hg, hχ, hr, hprop⟩ :=
        Usage.inv_recursor hdT h hq hp hu rfl
      obtain ⟨hM, hv⟩ := hι.hasDataType h
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := soundnessIn.hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have has'' : ValidInstanceArgsΓ sigM ι (ctx.atLevels ρ)
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
          ((decl.params (.ofLists qs ps hq hp)).substLevels
            ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')) := by
        rw [List.getFin_map]; exact has'
      have ht' := soundnessIn.hasType hd hι ht ρ
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
        have hCv := soundnessIn.hasType hd hι (hCt j T' C₀ hj hC₀) ρ
        simp only [Context.atLevels, Context.substLevels, Term.atLevels, Term.substLevels] at hCv
        exact hCv
      have hus' : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
          ∃ u, (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
            some ⟨(con.params (.ofLists qs ps hq hp)).length,
              (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ :=
        fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩
      have hut' : ∀ i j T' con C' R u₁ u₂, decl.cases[i]? = some (j, T', con) →
          (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ →
          con.results (.ofLists qs ps hq hp) decl.names
            (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)) = some R →
          (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
            some ⟨(con.params (.ofLists qs ps hq hp)).length,
              (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
          (us.substLevels fun i => (.ofNat (ρ i) : Level 0)).get i =
            some ⟨(con.params (.ofLists qs ps hq hp)).length,
              (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
          ValidEqTermΓ sigM ι (((ctx.atLevels ρ).append (con.fieldsAt (.ofLists qs ps hq hp)
            ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl')
            (as.substLevels fun i => (.ofNat (ρ i) : Level 0)))).append R) u₁ u₂
            ((C'.atCtor T'.name qs (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
              (as.substLevels fun i => (.ofNat (ρ i) : Level 0)) con.name
              (con.params (.ofLists qs ps hq hp))).rename (Ren.weakenN _)) :=
        fun i j T' con C' R u₁ u₂ hi hC' hR hu₁ hu₂ => by
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_substLevels_inv _ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
        obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
        cases Branches.get_inj hu₀ hu₀'
        have hb := soundnessIn.hasType hd hι (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ρ
        simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
        erw [Term.atCtor_substLevels] at hb
        rw [List.getFin_map]
        exact hb
      have hrec : ∀ j T' C', decl.dataTypes[j]? = some T' →
          (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).get j = some ⟨0, C'⟩ →
          ∀ σ, EqSubst sigM ι (ctx.atLevels ρ) σ σ → ∀ t₀,
          ValidTerm₀ sigM ι t₀ ((Term.inst T'.name qs
            (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
            (as.substLevels fun i => (.ofNat (ρ i) : Level 0))).subst σ) →
          ValidTerm₀ sigM ι (.recursor r T'.name qs
            (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
            ((as.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ) t₀
            ((Cs.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ)
            ((us.substLevels fun i => (.ofNat (ρ i) : Level 0)).subst σ))
            ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₀)) :=
        fun j T' C' hj hC' σ hσ t₀ ht₀ =>
          ValidEqTerm₀.recursor_block hι h hq hl' hp hadm ht'.1.1 has'' hCs' hCv hus' hus' hut' hκ
            hσ hj hC' ht₀
      have htr : r ∉ Mode.oneOne.erased → RunValid sigM ι P hΓ (ctx.atLevels ρ) γ'
          (t.substLevels fun i => (.ofNat (ρ i) : Level 0)) _ := fun hr' => by
        have htr := hasType (hΓ := hΓ) hd hι hP ht
          ((Mode.erasesUncounted .oneOne).mode _ hr' ▸ htu) ρ
        simp only [Term.atLevels, Term.substLevels] at htr
        exact htr
      have husr : RunValidBranches sigM ι P hΓ (ctx.atLevels ρ) decl qs
          (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps hq hl' hp
          (as.substLevels fun i => (.ofNat (ρ i) : Level 0))
          (Cs.substLevels fun i => (.ofNat (ρ i) : Level 0))
          (us.substLevels fun i => (.ofNat (ρ i) : Level 0)) δs gs :=
        fun i j T' con C' R u hi hC' hR hu₁ => by
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_substLevels_inv _ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
        have hb := hasType (hΓ := (hΓ.extend _).extend _) hd hι hP
          (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) (hbu i j T' con u₀ hi hu₀) ρ
        simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
        erw [Term.atCtor_substLevels] at hb
        simp only [Branches.resultGrades, Branches.grades_substLevels]
        rw [List.getFin_map]
        exact hb
      have hc := RunValid.recursor (P := P) (γ := γ') hd hM hv hadm has'' hh
        (Motives.get_substLevels_of _ hC) hCs' hCv hus' hrec ht' htr husr
        (by simpa only [Branches.resultGrades, Branches.grades_substLevels] using hg)
        (by simpa only [Branches.resultGrades, Branches.grades_substLevels] using hχ)
        (hr rfl) (fun hq' => match hc : decl.cases with
          | [] => rfl
          | _ :: _ => absurd rfl (hprop hq' (hc ▸ List.cons_ne_nil _ _)))
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact RunValid.sub hγ hc
    | .corec (ls := ls) (as := as) (S := S) h hq hl hp hadm hpre has hh hS hss _ hSs _ _ hgs hgt,
        hu => fun ρ => by
      have hdT := (presuppositions.hasArgs hss).distinct
      obtain ⟨γ', δ, δs, hγ, -, hssu, hgu, hδ, -⟩ := Usage.inv_corec hdT h hq hp hh hS hu rfl
      obtain ⟨hM, hv⟩ := hι.hasCodataType h
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := soundnessIn.hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hss' := soundnessIn.hasArgs hd hι hss ρ
      have hssr := fun hr => hasArgs (hΓ := hΓ) hd hι hP hss
        ((Mode.erasesUncounted .oneOne).mode _ hr ▸ hssu) ρ
      have hc := RunValid.corec (P := P) (γ := γ') hd hM hv hq hl' hp hadm
        (by rw [List.getFin_map]; exact has') (fun he e he' => (hι e (hpre he e he')).1) hh
        (States.get_substLevels_of _ hS) hss' hssr
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hq hl hp hgs
          (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
            soundnessIn.hasType hd hι (hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
        (RunValidCorecBranches.atLevels hq hl hp
          (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg hpr =>
            hasType hd hι hP (hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg)
              ((Mode.erasesUncounted .oneOne).mode _ hpr ▸
                hgu i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
        hδ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact RunValid.sub hγ hc
  hasArgs {ι : Interpretation} {P : Program} {sigM sig : Signature} {k : Nat} {Γ : Scope}
      {hΓ : Γ.FirstOrder} {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps}
      {Θ : Telescope k Γ ps} {γ : GradeVector Γ.length}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) (hP : P.Realizes sigM ι sig) :
      HasArgs sig ctx ts Θ → UsageArgs sig γ .oneOne ts →
        ∀ ρ, RunValidArgs sigM ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)
    | .nil _, .nil => fun _ => RunValidArgs.nil
    | .cons (t := t) ht hts, .cons hu hus => fun ρ => by
      have hts' := hasArgs (hΓ := hΓ) hd hι hP hts hus ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact RunValidArgs.cons hd (fun hp => hasType hd hι hP ht
        ((Mode.erasesUncounted .oneOne).mode _ hp ▸ hu) ρ) hts'

end Sic.Core
