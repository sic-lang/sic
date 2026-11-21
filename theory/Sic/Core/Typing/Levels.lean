module

public import Sic.Core.Typing
import Sic.Core.Results.Substitution

/-!
# Typing at Instantiated Levels

The judgments in a context of annex 15 of RFC 36 hold once levels replace their level variables,
in the context, the terms, the types, the telescopes and the sorts: a rule reads the levels only by
the equality and the order of levels, which every instantiation keeps, and by the instances of the
entries of the signature, whose levels are instantiated in turn.

The entries of the signature are checked once with their level variables, and the rules use them
at the levels of each instance; the lifting of a codata type has more level variables than the
type, whose parameters and destructors it reads at its own.
The proof is by induction on the derivations of all the judgments, `Derivable.levelsStable`.

ADE have no level variables: their levels are terms, which their substitutions instantiate.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- The judgments in a context hold once levels replace their level variables. -/
structure StableUnderLevels : Prop where
  /-- A well-formed context is well formed at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\Gamma` -/
  wfCtx : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ}, WfCtx sig ctx → WfCtx sig (ctx.substLevels ls')
  /-- A type is a type at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.A` -/
  wfType : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {A : Term k Γ},
    WfType sig ctx A → WfType sig (ctx.substLevels ls') (A.substLevels ls')
  /-- Equal types are equal at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {A B : Term k Γ},
    EqType sig ctx A B → EqType sig (ctx.substLevels ls') (A.substLevels ls') (B.substLevels ls')
  /-- A term of a type is a term of it at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.t` -/
  hasType : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {t A : Term k Γ},
    HasType sig ctx t A → HasType sig (ctx.substLevels ls') (t.substLevels ls') (A.substLevels ls')
  /-- Equal terms are equal at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {t u A : Term k Γ},
    EqTerm sig ctx t u A →
      EqTerm sig (ctx.substLevels ls') (t.substLevels ls') (u.substLevels ls') (A.substLevels ls')
  /-- Arguments of a telescope are arguments of it at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps},
    HasArgs sig ctx ts Θ →
      HasArgs sig (ctx.substLevels ls') (ts.substLevels ls') (Θ.substLevels ls')
  /-- Equal arguments of a telescope are equal at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps},
    EqArgs sig ctx ts us Θ →
      EqArgs sig (ctx.substLevels ls') (ts.substLevels ls') (us.substLevels ls')
        (Θ.substLevels ls')
  /-- Arguments of an instance are arguments of its parameters at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    HasInstanceArgs sig ctx as params →
      HasInstanceArgs sig (ctx.substLevels ls') (as.substLevels ls') (params.substLevels ls')
  /-- Equal arguments of instances are equal at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    EqInstanceArgs sig ctx as₁ as₂ params →
      EqInstanceArgs sig (ctx.substLevels ls') (as₁.substLevels ls') (as₂.substLevels ls')
        (params.substLevels ls')
  /-- A telescope in a sort is in the sort at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
    WfTelescope sig ctx Θ κ →
      WfTelescope sig (ctx.substLevels ls') (Θ.substLevels ls') (κ.substLevels ls')
  /-- A telescope in sorts is in the sorts at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)}
    {l : Level k},
    WfTelescopeSorts sig ctx Θ κs l →
      WfTelescopeSorts sig (ctx.substLevels ls') (Θ.substLevels ls')
        (κs.map (Universe.substLevels ls')) (l.subst ls')
  /-- Equal telescopes in a sort are equal in the sort at instantiated levels.
  RFC: `\mathsf{lvl}_\vdash.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ →
      EqTelescope sig (ctx.substLevels ls') (Θ₁.substLevels ls') (Θ₂.substLevels ls')
        (κ.substLevels ls')

-- ADE: none.
/-- What a judgment in a context says once levels replace its level variables: that it holds at
the levels instantiated. -/
def Judgment.LevelsStable : Judgment → Prop
  | @wfCtx sig k _ ctx => ∀ {k' : Nat} (ls' : Fin k → Level k'), WfCtx sig (ctx.substLevels ls')
  | @wfType sig k _ ctx A => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      WfType sig (ctx.substLevels ls') (A.substLevels ls')
  | @eqType sig k _ ctx A B => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      EqType sig (ctx.substLevels ls') (A.substLevels ls') (B.substLevels ls')
  | @hasType sig k _ ctx t A => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      HasType sig (ctx.substLevels ls') (t.substLevels ls') (A.substLevels ls')
  | @eqTerm sig k _ ctx t u A => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      EqTerm sig (ctx.substLevels ls') (t.substLevels ls') (u.substLevels ls') (A.substLevels ls')
  | @hasArgs sig k _ _ ctx ts Θ => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      HasArgs sig (ctx.substLevels ls') (ts.substLevels ls') (Θ.substLevels ls')
  | @eqArgs sig k _ _ ctx ts us Θ => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      EqArgs sig (ctx.substLevels ls') (ts.substLevels ls') (us.substLevels ls')
        (Θ.substLevels ls')
  | @hasInstanceArgs sig k _ _ ctx as params => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      HasInstanceArgs sig (ctx.substLevels ls') (as.substLevels ls') (params.substLevels ls')
  | @eqInstanceArgs sig k _ _ ctx as₁ as₂ params => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      EqInstanceArgs sig (ctx.substLevels ls') (as₁.substLevels ls') (as₂.substLevels ls')
        (params.substLevels ls')
  | @wfTelescope sig k _ _ ctx Θ κ => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      WfTelescope sig (ctx.substLevels ls') (Θ.substLevels ls') (κ.substLevels ls')
  | @wfTelescopeSorts sig k _ _ ctx Θ κs l => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      WfTelescopeSorts sig (ctx.substLevels ls') (Θ.substLevels ls')
        (κs.map (Universe.substLevels ls')) (l.subst ls')
  | @eqTelescope sig k _ _ ctx Θ₁ Θ₂ κ => ∀ {k' : Nat} (ls' : Fin k → Level k'),
      EqTelescope sig (ctx.substLevels ls') (Θ₁.substLevels ls') (Θ₂.substLevels ls')
        (κ.substLevels ls')
  | _ => True

-- ADE: none.
/-- The judgments in a context hold once levels replace their level variables, by induction on
their derivations. -/
theorem Derivable.levelsStable {J : Judgment} (h : Derivable J) : J.LevelsStable := by
  induction h with
  | WfCtx.empty h h_ih =>
    intro k' ls'
    exact .empty h
  | WfCtx.var h h_ih =>
    intro k' ls'
    exact .var (h_ih ls')
  | WfCtx.secondOrder h h_ih =>
    intro k' ls'
    have ih := (h_ih ls')
    rw [Context.substLevels_append] at ih
    exact .secondOrder ih
  | WfType.univType h h_ih =>
    intro k' ls'
    exact .univType (h_ih ls')
  | WfType.propType h h_ih =>
    intro k' ls'
    exact .propType (h_ih ls')
  | EqType.refl h h_ih =>
    intro k' ls'
    exact .refl (h_ih ls')
  | EqType.symm h h_ih =>
    intro k' ls'
    exact .symm (h_ih ls')
  | EqType.trans h₁ h₂ h₁_ih h₂_ih =>
    intro k' ls'
    exact .trans (h₁_ih ls') (h₂_ih ls')
  | EqType.univType h h_ih =>
    intro k' ls'
    exact .univType (h_ih ls')
  | EqType.propType h h_ih =>
    intro k' ls'
    exact .propType (h_ih ls')
  | HasType.var hctx hx hctx_ih =>
    intro k' ls'
    exact .var (hctx_ih ls') (hx.substLevels ls')
  | HasType.secondOrder hX hts hts_ih =>
    intro k' ls'
    rw [Term.substLevels_instantiate]
    exact .secondOrder (hX.substLevels ls') (hts_ih ls')
  | HasType.const hctx h hq hl hp hctx_ih =>
    intro k' ls'
    rename_i ls _
    rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls hl]
    exact .const (hctx_ih ls') h hq _ hp
  | HasType.univ hctx hctx_ih =>
    intro k' ls'
    exact .univ (hctx_ih ls')
  | HasType.prop hctx hctx_ih =>
    intro k' ls'
    exact .prop (hctx_ih ls')
  | HasType.inst h hq hl hp hadm has has_ih =>
    intro k' ls'
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels, Term.substLevels, Universe.substLevels_substLevels_getFin]
    exact .inst h hq _ hp hadm has'
  | HasType.equality hA ht hu hA_ih ht_ih hu_ih =>
    intro k' ls'
    exact .equality (hA_ih ls') (ht_ih ls') (hu_ih ls')
  | HasType.reflProof hA ht hA_ih ht_ih =>
    intro k' ls'
    exact .reflProof (hA_ih ls') (ht_ih ls')
  | HasType.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro k' ls'
    rename_i κ _ t₁ t₂ _ _ _
    have hu' := (hu_ih ls')
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    exact .transp (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls') (ht₂_ih ls')
      (hC_ih ls') (ht_ih ls') hu'
  | HasType.propExt hA hB ht hu hA_ih hB_ih ht_ih hu_ih =>
    intro k' ls'
    have ht' := (ht_ih ls')
    have hu' := (hu_ih ls')
    rw [Term.substLevels_rename] at ht' hu'
    exact .propExt (hA_ih ls') (hB_ih ls') ht' hu'
  | HasType.coind h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih
      hAt_ih ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih =>
    intro k' ls'
    rename_i sig k Γ _ decl _ _ qs ls ps as l' t₁ t₂ _ As gs _ A κs
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    let p₀ : Parameter := ⟨Grade.one, Grade.one⟩
    have hsort := congrArg Universe.level
      (Universe.substLevels_substLevels_getFin ls' (decl.sort (.ofLists qs ps hq hp)) ls hl)
    rw [Term.substLevels, show ((decl.sort (.ofLists qs ps hq hp)).substLevels
      (ls.getFin hl)).level.subst ls' = _ from hsort]
    refine .coind (l' := l'.subst ls') (κs := fun i => (κs i).substLevels ls') h hq _ hp hadm has'
      hh (Terms.get_substLevels_of ls' hA) ((Terms.length_substLevels ls' As).trans hAl) ?_
      (ht₁_ih ls') (ht₂_ih ls') ?_
      ((DestructorBranches.length_substLevels ls' gs).trans hgl) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j T' A' hj hA'
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels ls' hA'
      have ih := (hAt_ih j T' A₀ hj hA₀ ls')
      simp only [Context.substLevels, Term.substLevels_rename] at ih
      exact ih
    · have ih := (ht_ih ls')
      rw [show ((A.subst₀ (Subst₀.liftN 1 (Subst₀.single t₁))).subst₀ (Subst₀.single t₂)) =
          A.instantiate (Args.cons (p := p₀) t₁ (Args.cons (p := p₀) t₂ .nil)) from rfl,
        Term.substLevels_instantiate] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      obtain ⟨g, hg⟩ := hgs i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      exact ⟨_, DestructorBranches.get_substLevels_of ls' hg⟩
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      have e := congrArg (Telescope.substLevels ls') (hΘ i j T' d p q ς ps₁ Ξ Θ B ψ hi hd)
      rw [Telescope.substLevels_subst_of
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
        Telescope.substLevels_subst_of
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ .zero) : Term k (Γ.extend 3))),
        Telescope.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at e
      exact e
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      have e := congrArg (Term.substLevels ls') (hB i j T' d p q ς ps₁ Ξ Θ B ψ hi hd)
      rw [Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ .zero) : Term k (Γ.extend 3)))),
        Term.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at e
      exact e
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels ls' hA'
      have ih := (hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ hi hA₀ hd hn ls')
      erw [Context.substLevels_append] at ih
      simp only [Context.substLevels, Term.substLevels_rename, Term.substLevels] at ih
      erw [Telescope.substLevels_subst_of
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
        Telescope.substLevels_substLevels_getFin,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
        Term.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels ls' hA'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg
      have ih := (hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ g₀ hi hA₀ hd hn hg₀ ls')
      erw [Context.substLevels_append] at ih
      simp only [Context.substLevels, Term.substLevels_rename, Term.substLevels] at ih
      erw [Telescope.substLevels_subst_of
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
        Telescope.substLevels_substLevels_getFin,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
        Term.substLevels_substLevels_getFin, Term.observation_substLevels,
        Term.observation_substLevels, InstanceArgs.substLevels_rename] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels ls' hA'
      obtain ⟨A₀', hA₀', rfl⟩ := Terms.get_substLevels ls' hA''
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg
      have ih := hgr_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ D' j' A₀' g₀ hi hA₀ hd hn hj' hA₀'
        hg₀ ls'
      replace ih : HasType sig _ _ ((((A₀'.rename (Ren.liftN 2 (Ren.weakenN 3))).rename
          (Ren.liftN 2 (Ren.weakenN ps₁.length))).instantiate
            (Args.cons (p := p₀) ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)
            (Args.cons (p := p₀) ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁) .nil))).substLevels ls') := ih
      erw [Term.substLevels_instantiate, Context.substLevels_append,
        Telescope.substLevels_subst_of
          (hd.obsSubst_observation_substLevels ls' T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
        Telescope.substLevels_substLevels_getFin] at ih
      simp only [Context.substLevels, Term.substLevels_rename, Args.substLevels] at ih
      rw [Term.observation_substLevels, Term.observation_substLevels,
        InstanceArgs.substLevels_rename] at ih
      exact ih
  | HasType.ctor h hc hq hl hp hadm has hts has_ih hts_ih =>
    intro k' ls'
    rename_i ls _ _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := (hts_ih ls')
    rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl] at hts'
    rw [Term.ctor_substLevels]
    exact .ctor h hc hq _ hp hadm has' hts'
  | HasType.recursor h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus hRs hut hκ has_ih ht_ih hCt_ih
      hut_ih =>
    intro k' ls'
    rename_i ls _ _ _ _ _ t Cs us κ _ _ Rs
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    refine .recursor (κ := κ.substLevels ls') (Rs := fun con => (Rs con).substLevels ls') h hq _
      hp hadm has' (ht_ih ls') hh (Motives.get_substLevels_of ls' hC)
      ((Motives.length_substLevels ls' Cs).trans hCl) ?_ ?_
      ((Branches.length_substLevels ls' us).trans hul) ?_ ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      exact (hCt_ih j T' C₀ hj hC₀ ls')
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀,
        ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  | HasType.obs h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih =>
    intro k' ls'
    rename_i D _ qs ls ps as t _ _ _ _ _ Ξ _ _ _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as t x
    have hbs' := (hbs_ih ls')
    rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
    rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin, Term.obs_substLevels]
    exact .obs h hq _ hp hadm hd has' (ht_ih ls') hbs'
  | HasType.corec h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih
      hgt_ih =>
    intro k' ls'
    rename_i ctx _ _ _ qs ls ps as r Ss gs _ ps' _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.corec_substLevels]
    refine .corec h hq _ hp hadm hpre has' hh (States.get_substLevels_of ls' hS)
      (hss_ih ls') ((States.length_substLevels ls' Ss).trans hSl) ?_ ?_
      ((DestructorBranches.length_substLevels ls' gs).trans hgl) ?_ ?_
    · intro j T' hj
      obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
      exact ⟨ps'', _, States.get_substLevels_of ls' hS'⟩
    · intro j T' ps'' S' hj hS'
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      have ih := (hSt_ih j T' ps'' S₀ hj hS₀ ls')
      rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
      exact ih
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, DestructorBranches.get_substLevels_of ls' hg⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg
      have ho {a : Scope.Entry} (x : Var Ξ a) := hd.obsSubst_substLevels ls'
        (o' := (Term.corecAt r T'.name qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
          (Ss.substLevels ls') (gs.substLevels ls') ps'').observation T'.name qs
          (ls.map (Level.subst ls')) ps ((as.substLevels ls').rename (Ren.weakenN ps''.length)))
        (fun d ps' => by
          rw [Term.observation_substLevels, Term.corecAt_substLevels,
            InstanceArgs.substLevels_rename])
        (θ := (as.rename (Ren.weakenN ps''.length)).toSubst)
        (θ' := ((as.substLevels ls').rename (Ren.weakenN ps''.length)).toSubst)
        (fun x => by rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename]) x
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  | HasType.conv ht h ht_ih h_ih =>
    intro k' ls'
    exact .conv (ht_ih ls') (h_ih ls')
  | EqTerm.refl h h_ih =>
    intro k' ls'
    exact .refl (h_ih ls')
  | EqTerm.symm h h_ih =>
    intro k' ls'
    exact .symm (h_ih ls')
  | EqTerm.trans h₁ h₂ h₁_ih h₂_ih =>
    intro k' ls'
    exact .trans (h₁_ih ls') (h₂_ih ls')
  | EqTerm.conv h hA h_ih hA_ih =>
    intro k' ls'
    exact .conv (h_ih ls') (hA_ih ls')
  | EqTerm.irr ht hu hA ht_ih hu_ih hA_ih =>
    intro k' ls'
    exact .irr (ht_ih ls') (hu_ih ls') (hA_ih ls')
  | EqTerm.secondOrder hX hts hts_ih =>
    intro k' ls'
    rw [Term.substLevels_instantiate]
    exact .secondOrder (hX.substLevels ls') (hts_ih ls')
  | EqTerm.delta hctx h hq hl hp hctx_ih =>
    intro k' ls'
    rename_i ls _
    rw [Signature.instanceType_substLevels, Signature.instanceType_substLevels,
      ← Level.getFin_map_subst ls' ls hl]
    exact .delta (hctx_ih ls') h hq _ hp
  | EqTerm.const hctx h hq hl₁ hl₂ hp hls hctx_ih =>
    intro k' ls'
    rename_i ls _ _
    rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls hl₁]
    exact .const (hctx_ih ls') h hq _ _ hp (Level.getFin_map_subst_equal ls' hls)
  | EqTerm.univ hctx hl hctx_ih =>
    intro k' ls'
    exact .univ (hctx_ih ls') (Level.subst_equal ls' hl)
  | EqTerm.prop hctx hl hctx_ih =>
    intro k' ls'
    exact .prop (hctx_ih ls') (Level.subst_equal ls' hl)
  | EqTerm.inst h hq hl₁ hl₂ hp hadm has hls has_ih =>
    intro k' ls'
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels, Term.substLevels, Term.substLevels,
      Universe.substLevels_substLevels_getFin]
    exact .inst h hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls)
  | EqTerm.equality hA ht hu hl hA_ih ht_ih hu_ih =>
    intro k' ls'
    exact
    .equality (hA_ih ls') (ht_ih ls') (hu_ih ls') (Level.subst_equal ls' hl)
  | EqTerm.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro k' ls'
    rename_i κ _ _ t₁ _ t₂ _ _ _ _ _ _ _
    have hu' := (hu_ih ls')
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    exact .transp (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls') (ht₂_ih ls')
      (hC_ih ls') (ht_ih ls') hu'
  | EqTerm.transpSame hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih =>
    intro k' ls'
    rename_i κ _ t₁ t₂ _ _ _
    have hu' := (hu_ih ls')
    have hCC' := (hCC_ih ls')
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu' hCC'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hCC' ⊢
    exact .transpSame (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls')
      (ht₂_ih ls') (hC_ih ls') (ht_ih ls') hu' hCC'
  | EqTerm.ctor h hc hq hl₁ hl₂ hp hadm has hls hts has_ih hts_ih =>
    intro k' ls'
    rename_i ls _ _ _ _ _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := (hts_ih ls')
    rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl₁] at hts'
    rw [Term.ctor_substLevels, Term.ctor_substLevels]
    exact .ctor h hc hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls) hts'
  | EqTerm.recursor h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁
      hus₂ hes hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih =>
    intro k' ls'
    rename_i ls _ _ _ _ _ _ _ t _ Cs₁ Cs₂ us₁ us₂ κ _ _ Rs₁ Rs₂
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    refine .recursor (κ := κ.substLevels ls') (Rs₁ := fun con => (Rs₁ con).substLevels ls')
      (Rs₂ := fun con => (Rs₂ con).substLevels ls') h hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls) (ht_ih ls') hh
      (Motives.get_substLevels_of ls' hC) ((Motives.length_substLevels ls' Cs₁).trans hCl₁)
      ((Motives.length_substLevels ls' Cs₂).trans hCl₂) ?_ ?_ ?_
      ((Branches.length_substLevels ls' us₁).trans hul₁)
      ((Branches.length_substLevels ls' us₂).trans hul₂) ?_ ?_
      (by funext i; rw [Branches.grades_substLevels, Branches.grades_substLevels, hes]) ?_ ?_ ?_
      hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs₁ j T' hj
      exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs₂ j T' hj
      exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
    · intro j T' C₁' C₂' hj h₁ h₂
      obtain ⟨C₁₀, hC₁₀, rfl⟩ := Motives.get_substLevels ls' h₁
      obtain ⟨C₂₀, hC₂₀, rfl⟩ := Motives.get_substLevels ls' h₂
      exact (hCt_ih j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀ ls')
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus₁ i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus₂ i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs₁ i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con hi
      exact (hRs₂ i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u₁ u₂ hi hC' hu₁ hu₂
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₁₀, hu₁₀, rfl⟩ := Branches.get_substLevels ls' hu₁
      obtain ⟨u₂₀, hu₂₀, rfl⟩ := Branches.get_substLevels ls' hu₂
      have ih := (hut_ih i j T' con C₀ u₁₀ u₂₀ hi hC₀ hu₁₀ hu₂₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl₁] at ih
      exact ih
  | EqTerm.obs h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih =>
    intro k' ls'
    rename_i D _ qs ls _ ps as _ t _ _ _ _ _ _ Ξ _ _ _ _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as t x
    have hbs' := (hbs_ih ls')
    rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
    rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin, Term.obs_substLevels, Term.obs_substLevels]
    exact .obs h hq _ _ hp hadm hd has' (Level.getFin_map_subst_equal ls' hls) (ht_ih ls')
      hbs'
  | EqTerm.corec h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁
      hgl₂ hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih =>
    intro k' ls'
    rename_i sig _ _ ctx _ _ _ qs ls _ ps as _ r Ss₁ Ss₂ gs₁ gs₂ _ ps' _ _ _ _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.corec_substLevels, Term.corec_substLevels]
    refine .corec h hq _ _ hp hadm hpre has' (Level.getFin_map_subst_equal ls' hls) hh
      (States.get_substLevels_of ls' hS₁) (States.get_substLevels_of ls' hS₂) (hss_ih ls')
      ((States.length_substLevels ls' Ss₁).trans hSl₁)
      ((States.length_substLevels ls' Ss₂).trans hSl₂) ?_
      (fun j => by rw [States.sorts_substLevels, States.sorts_substLevels, hSk j]) ?_ ?_
      ((DestructorBranches.length_substLevels ls' gs₁).trans hgl₁)
      ((DestructorBranches.length_substLevels ls' gs₂).trans hgl₂) ?_ ?_
    · intro j T' hj
      obtain ⟨ps'', S₁', S₂', h₁, h₂⟩ := hSs j T' hj
      exact ⟨ps'', _, _, States.get_substLevels_of ls' h₁, States.get_substLevels_of ls' h₂⟩
    · intro j T' ps'' S₁' hj h₁
      obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_substLevels ls' h₁
      have ih := (hSt_ih j T' ps'' S₁₀ hj hS₁₀ ls')
      rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
      exact ih
    · intro j T' ps'' S₁' S₂' hj h₁ h₂
      obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_substLevels ls' h₁
      obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_substLevels ls' h₂
      have ih : EqTelescope sig _ _ _
          ⟨.type, (Telescope.packLevel (Ss₁.sorts j) .zero).subst ls'⟩ :=
        (hSe_ih j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀ ls')
      rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
      exact ih
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, _, DestructorBranches.get_substLevels_of ls' hg₁,
        DestructorBranches.get_substLevels_of ls' hg₂⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g₁₀, hg₁₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg₁
      obtain ⟨g₂₀, hg₂₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg₂
      have ho {a : Scope.Entry} (x : Var Ξ a) := hd.obsSubst_substLevels ls'
        (o' := (Term.corecAt r T'.name qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
          (Ss₁.substLevels ls') (gs₁.substLevels ls') ps'').observation T'.name qs
          (ls.map (Level.subst ls')) ps ((as.substLevels ls').rename (Ren.weakenN ps''.length)))
        (fun d ps' => by
          rw [Term.observation_substLevels, Term.corecAt_substLevels,
            InstanceArgs.substLevels_rename])
        (θ := (as.rename (Ren.weakenN ps''.length)).toSubst)
        (θ' := ((as.substLevels ls').rename (Ren.weakenN ps''.length)).toSubst)
        (fun x => by rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename]) x
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  | EqTerm.iota h hc hq hl hp hadm has hts hi hC hu hrs hCl hCs hCt hul hus hRs hut hκ has_ih hts_ih
      hCt_ih hut_ih =>
    intro k' ls'
    rename_i sig _ _ _ _ _ _ con _ ls _ _ _ _ _ Cs us κ i j _ u _ _ Rs
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := (hts_ih ls')
    rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl] at hts'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (Term.substLevels ls' _))
        (fun x => by cases x <;> rfl),
      Term.substLevels_instantiate, Term.substLevels_instantiate, Args.substLevels_rename]
    show EqTerm sig _ (.recursor _ _ _ _ _ _ _ _ (Term.substLevels ls' (.ctor _ _ _ _ _ _ _)) _ _ _)
      _ _
    rw [Term.ctor_substLevels]
    refine .iota (κ := κ.substLevels ls') (Rs := fun con => (Rs con).substLevels ls') h hc hq _
      hp hadm has' hts' hi (Motives.get_substLevels_of ls' hC)
      (Branches.get_substLevels_of ls' hu) (hrs.substLevels_recursorAt ls')
      ((Motives.length_substLevels ls' Cs).trans hCl) ?_ ?_
      ((Branches.length_substLevels ls' us).trans hul) ?_ ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      exact (hCt_ih j T' C₀ hj hC₀ ls')
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  | EqTerm.etaCtor h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus hRs hut hκ has_ih
      ht_ih he_ih hCt_ih hut_ih =>
    intro k' ls'
    rename_i k Γ _ _ _ T con qs ls ps as _ _ _ t Cs us κ i j _ e Rs
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have hu' := Branches.get_substLevels_of ls' hu
    erw [show Term.substLevels ls'
          (e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp)) :
            Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)) =
        (e.substLevels ls').atCtor T.name qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
          con.name (con.params (.ofLists qs ps hq hp)) from
      Term.atCtor_substLevels ls' e _ _ _ _ _ _ _] at hu'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl),
      Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl)]
    refine .etaCtor (κ := κ.substLevels ls') (Rs := fun con => (Rs con).substLevels ls') h hc hq
      _ hp hadm hr has' (ht_ih ls') (he_ih ls') hi (Motives.get_substLevels_of ls' hC)
      hu' ((Motives.length_substLevels ls' Cs).trans hCl) ?_ ?_
      ((Branches.length_substLevels ls' us).trans hul) ?_ ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      exact (hCt_ih j T' C₀ hj hC₀ ls')
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  | EqTerm.beta h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih
      hss_ih hbs_ih hSt_ih hgt_ih =>
    intro k' ls'
    rename_i ctx _ D _ qs ls ps as r Ss gs _ i ps' _ ss d p q ς _ Ξ₀ _ _ _ g _
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho₀ {a : Scope.Entry} (x : Var Ξ₀ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as
        (.corec r D qs ls ps as ss.terms Ss gs) x
    have hbs' := (hbs_ih ls')
    rw [Telescope.substLevels_subst_of ho₀, Telescope.substLevels_substLevels_getFin,
      Term.corec_substLevels] at hbs'
    rw [Term.obs_substLevels, Term.observed_substLevels, Term.substLevels_instantiate,
      Term.substLevels_instantiate, Args.substLevels_rename, Term.substLevels_instantiate,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho₀),
      Term.substLevels_substLevels_getFin, Universe.substLevels_substLevels_getFin,
      Term.corec_substLevels]
    refine .beta h hq _ hp hadm hpre has' hh (States.get_substLevels_of ls' hS)
      (hss_ih ls') hi hd (DestructorBranches.get_substLevels_of ls' hg) hbs'
      ((States.length_substLevels ls' Ss).trans hSl) ?_ ?_
      ((DestructorBranches.length_substLevels ls' gs).trans hgl) ?_ ?_
    · intro j T' hj
      obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
      exact ⟨ps'', _, States.get_substLevels_of ls' hS'⟩
    · intro j T' ps'' S' hj hS'
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      have ih := (hSt_ih j T' ps'' S₀ hj hS₀ ls')
      rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
      exact ih
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, DestructorBranches.get_substLevels_of ls' hg⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels ls' hg
      have ho {a : Scope.Entry} (x : Var Ξ a) := hd.obsSubst_substLevels ls'
        (o' := (Term.corecAt r T'.name qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
          (Ss.substLevels ls') (gs.substLevels ls') ps'').observation T'.name qs
          (ls.map (Level.subst ls')) ps ((as.substLevels ls').rename (Ren.weakenN ps''.length)))
        (fun d ps' => by
          rw [Term.observation_substLevels, Term.corecAt_substLevels,
            InstanceArgs.substLevels_rename])
        (θ := (as.rename (Ren.weakenN ps''.length)).toSubst)
        (θ' := ((as.substLevels ls').rename (Ren.weakenN ps''.length)).toSubst)
        (fun x => by rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename]) x
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ ls')
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  | EqTerm.etaObs h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih =>
    intro k' ls'
    rename_i D _ qs ls ps as t u
    have has' := (has_ih ls')
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels]
    refine .etaObs h hq _ hp hadm hr has' (ht_ih ls') (hu_ih ls') ?_
    intro d p q ς ps' Ξ Θ B ψ hd
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as t x
    have ih := (hobs_ih d p q ς ps' Ξ Θ B ψ hd ls')
    rw [Context.substLevels_append, Telescope.substLevels_subst_of ho,
      Telescope.substLevels_substLevels_getFin, Term.observation_substLevels ls' D qs ls ps as t,
      Term.observation_substLevels ls' D qs ls ps as u,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin] at ih
    exact ih
  | HasArgs.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | HasArgs.cons ht hts ht_ih hts_ih =>
    intro k' ls'
    rename_i t _ _ _
    refine .cons (ht_ih ls') ?_
    have ih := (hts_ih ls')
    rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)] at ih
    exact ih
  | EqArgs.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | EqArgs.cons ht hts ht_ih hts_ih =>
    intro k' ls'
    rename_i t _ _ _ _ _
    refine .cons (ht_ih ls') ?_
    have ih := (hts_ih ls')
    rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)] at ih
    exact ih
  | HasInstanceArgs.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | HasInstanceArgs.var has ha has_ih ha_ih =>
    intro k' ls'
    rename_i as _ _ _
    refine .var (has_ih ls') ?_
    have ih := (ha_ih ls')
    rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x)] at ih
    exact ih
  | HasInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro k' ls'
    rename_i as _ _ _ _
    refine .secondOrder (has_ih ls') ?_
    have ih := (hB_ih ls')
    rw [Context.substLevels_append,
      Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x),
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _
        (fun x => InstanceArgs.toSubst_substLevels ls' as x))] at ih
    exact ih
  | EqInstanceArgs.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | EqInstanceArgs.var has ha has_ih ha_ih =>
    intro k' ls'
    rename_i as _ _ _ _ _
    refine .var (has_ih ls') ?_
    have ih := (ha_ih ls')
    rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x)] at ih
    exact ih
  | EqInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro k' ls'
    rename_i as _ _ _ _ _ _
    refine .secondOrder (has_ih ls') ?_
    have ih := (hB_ih ls')
    rw [Context.substLevels_append,
      Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x),
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _
        (fun x => InstanceArgs.toSubst_substLevels ls' as x))] at ih
    exact ih
  | WfTelescope.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | WfTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro k' ls'
    exact
    .cons (hA_ih ls') (Universe.substLevels_bounded ls' hκ) (hΘ_ih ls') hp
  | WfTelescopeSorts.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | WfTelescopeSorts.cons hA hl hΘ hp hA_ih hΘ_ih =>
    intro k' ls'
    exact
    .cons (hA_ih ls') (Level.subst_le ls' hl) (hΘ_ih ls') hp
  | EqTelescope.nil hctx hctx_ih =>
    intro k' ls'
    exact .nil (hctx_ih ls')
  | EqTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro k' ls'
    exact
    .cons (hA_ih ls') (Universe.substLevels_bounded ls' hκ) (hΘ_ih ls') hp
  | _ => trivial

-- ADE: none.
/-- The judgments in a context hold once levels replace their level variables.
RFC: `\mathsf{lvl}_\vdash.\Gamma`
RFC: `\mathsf{lvl}_\vdash.A`
RFC: `\mathsf{lvl}_\vdash.A_\equiv`
RFC: `\mathsf{lvl}_\vdash.t`
RFC: `\mathsf{lvl}_\vdash.t_\equiv`
RFC: `\mathsf{lvl}_\vdash.\bar t`
RFC: `\mathsf{lvl}_\vdash.\bar t_\equiv`
RFC: `\mathsf{lvl}_\vdash.\bar a`
RFC: `\mathsf{lvl}_\vdash.\bar a_\equiv`
RFC: `\mathsf{lvl}_\vdash.\Theta`
RFC: `\mathsf{lvl}_\vdash.\Theta_{\bar\kappa}`
RFC: `\mathsf{lvl}_\vdash.\Theta_\equiv` -/
theorem stableUnderLevels : StableUnderLevels :=
  ⟨fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls'),
    fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls'),
    fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls'),
    fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls'),
    fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls'),
    fun ls' => (·.levelsStable ls'), fun ls' => (·.levelsStable ls')⟩

end Sic.Core
