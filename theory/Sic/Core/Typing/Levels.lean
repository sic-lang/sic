module

public import Sic.Core.Typing
import Sic.Core.Results.Substitution
import Sic.Core.Typing.Induction

/-!
# Typing at Instantiated Levels

The judgments in a context of annex 15 of RFC 36 hold once levels replace their level variables,
in the context, the terms, the types, the telescopes and the sorts: a rule reads the levels only by
the equality and the order of levels, which every instantiation keeps, and by the instances of the
entries of the signature, whose levels are instantiated in turn.

The entries of the signature are checked once with their level variables, and the rules use them
at the levels of each instance; the lifting of a codata type has more level variables than the
type, whose parameters and destructors it reads at its own.
The proof is by the induction on the derivations, `Derivations.induction`, with the fields of
`StableUnderLevels` as its motives.

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
theorem stableUnderLevels : StableUnderLevels := by
  suffices H : Derivations.Conclusion
      (wfCtx := fun sig {k Γ} ctx _ => ∀ {k'} (ls' : Fin k → Level k'),
        WfCtx sig (ctx.substLevels ls'))
      (wfType := fun sig {k Γ} ctx A _ => ∀ {k'} (ls' : Fin k → Level k'),
        WfType sig (ctx.substLevels ls') (A.substLevels ls'))
      (eqType := fun sig {k Γ} ctx A B _ => ∀ {k'} (ls' : Fin k → Level k'),
        EqType sig (ctx.substLevels ls') (A.substLevels ls') (B.substLevels ls'))
      (hasType := fun sig {k Γ} ctx t A _ => ∀ {k'} (ls' : Fin k → Level k'),
        HasType sig (ctx.substLevels ls') (t.substLevels ls') (A.substLevels ls'))
      (eqTerm := fun sig {k Γ} ctx t u A _ => ∀ {k'} (ls' : Fin k → Level k'),
        EqTerm sig (ctx.substLevels ls') (t.substLevels ls') (u.substLevels ls')
          (A.substLevels ls'))
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => ∀ {k'} (ls' : Fin k → Level k'),
        HasArgs sig (ctx.substLevels ls') (ts.substLevels ls') (Θ.substLevels ls'))
      (eqArgs := fun sig {k Γ ps} ctx ts us Θ _ => ∀ {k'} (ls' : Fin k → Level k'),
        EqArgs sig (ctx.substLevels ls') (ts.substLevels ls') (us.substLevels ls')
          (Θ.substLevels ls'))
      (hasInstanceArgs := fun sig {k Γ Δ} ctx as params _ => ∀ {k'} (ls' : Fin k → Level k'),
        HasInstanceArgs sig (ctx.substLevels ls') (as.substLevels ls') (params.substLevels ls'))
      (eqInstanceArgs := fun sig {k Γ Δ} ctx as₁ as₂ params _ => ∀ {k'} (ls' : Fin k → Level k'),
        EqInstanceArgs sig (ctx.substLevels ls') (as₁.substLevels ls') (as₂.substLevels ls')
          (params.substLevels ls'))
      (wfTelescope := fun sig {k Γ ps} ctx Θ κ _ => ∀ {k'} (ls' : Fin k → Level k'),
        WfTelescope sig (ctx.substLevels ls') (Θ.substLevels ls') (κ.substLevels ls'))
      (wfTelescopeSorts := fun sig {k Γ ps} ctx Θ κs l _ => ∀ {k'} (ls' : Fin k → Level k'),
        WfTelescopeSorts sig (ctx.substLevels ls') (Θ.substLevels ls')
          (κs.map (Universe.substLevels ls')) (l.subst ls'))
      (eqTelescope := fun sig {k Γ ps} ctx Θ₁ Θ₂ κ _ => ∀ {k'} (ls' : Fin k → Level k'),
        EqTelescope sig (ctx.substLevels ls') (Θ₁.substLevels ls') (Θ₂.substLevels ls')
          (κ.substLevels ls')) from
    ⟨fun ls' => fun h => H.wfCtx h ls', fun ls' => fun h => H.wfType h ls',
      fun ls' => fun h => H.eqType h ls', fun ls' => fun h => H.hasType h ls',
      fun ls' => fun h => H.eqTerm h ls', fun ls' => fun h => H.hasArgs h ls',
      fun ls' => fun h => H.eqArgs h ls', fun ls' => fun h => H.hasInstanceArgs h ls',
      fun ls' => fun h => H.eqInstanceArgs h ls', fun ls' => fun h => H.wfTelescope h ls',
      fun ls' => fun h => H.wfTelescopeSorts h ls', fun ls' => fun h => H.eqTelescope h ls'⟩
  apply Derivations.induction
  case wfCtx_empty => exact fun h h_ih => fun ls' => .empty h
  case wfCtx_var => exact fun h h_ih => fun ls' => .var (h_ih ls')
  case wfCtx_secondOrder =>
    refine fun h h_ih => fun ls' => ?_
    have ih := h_ih ls'
    rw [Context.substLevels_append] at ih
    exact .secondOrder ih
  case wfType_univType => exact fun h h_ih => fun ls' => .univType (h_ih ls')
  case wfType_propType => exact fun h h_ih => fun ls' => .propType (h_ih ls')
  case eqType_refl => exact fun h h_ih => fun ls' => .refl (h_ih ls')
  case eqType_symm => exact fun h h_ih => fun ls' => .symm (h_ih ls')
  case eqType_trans => exact fun h₁ h₂ h₁_ih h₂_ih => fun ls' => .trans (h₁_ih ls') (h₂_ih ls')
  case eqType_univType => exact fun h h_ih => fun ls' => .univType (h_ih ls')
  case eqType_propType => exact fun h h_ih => fun ls' => .propType (h_ih ls')
  case hasType_var =>
    exact fun hctx hx hctx_ih => fun ls' =>
      .var (hctx_ih ls') (hx.substLevels ls')
  case hasType_secondOrder =>
    refine fun hX hts hts_ih => fun ls' => ?_
    rw [Term.substLevels_instantiate]
    exact .secondOrder (hX.substLevels ls') (hts_ih ls')
  case hasType_const =>
    intro sig k Γ ctx f j k' g m p A qs ls ps hctx h hq hl hp hctx_ih _ ls'
    rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls hl]
    exact .const (hctx_ih ls') h hq _ hp
  case hasType_univ => exact fun hctx hctx_ih => fun ls' => .univ (hctx_ih ls')
  case hasType_prop => exact fun hctx hctx_ih => fun ls' => .prop (hctx_ih ls')
  case hasType_inst =>
    refine fun h hq hl hp hadm has has_ih => fun ls' => ?_
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels, Term.substLevels, Universe.substLevels_substLevels_getFin]
    exact .inst h hq _ hp hadm has'
  case hasType_equality =>
    exact fun hA ht hu hA_ih ht_ih hu_ih => fun ls' =>
      .equality (hA_ih ls') (ht_ih ls') (hu_ih ls')
  case hasType_reflProof =>
    exact fun hA ht hA_ih ht_ih => fun ls' =>
      .reflProof (hA_ih ls') (ht_ih ls')
  case hasType_transp =>
    intro sig k Γ ctx s l κ A t₁ t₂ t u C hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih
      k' ls'
    have hu' := hu_ih ls'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    exact .transp (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls') (ht₂_ih ls')
      (hC_ih ls') (ht_ih ls') hu'
  case hasType_propExt =>
    refine fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => fun ls' => ?_
    have ht' := ht_ih ls'
    have hu' := hu_ih ls'
    rw [Term.substLevels_rename] at ht' hu'
    exact .propExt (hA_ih ls') (hB_ih ls') ht' hu'
  case hasType_coind =>
    intro sig k Γ ctx decl D T qs ls ps as l' t₁ t₂ t As gs h' A κs h hq hl hp hadm has hh hA hAl
      hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih
      hgr_ih k' ls'
    have has' := has_ih ls'
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
      have ih := hAt_ih j T' A₀ hj hA₀ ls'
      simp only [Context.substLevels, Term.substLevels_rename] at ih
      exact ih
    · have ih := ht_ih ls'
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
      have ih := hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ hi hA₀ hd hn ls'
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
      have ih := hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ g₀ hi hA₀ hd hn hg₀ ls'
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
  case hasType_ctor =>
    intro sig k Γ ctx decl D T con qs ls ps as h hc hq hl hp hadm has ts hts has_ih hts_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := hts_ih ls'
    rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl] at hts'
    rw [Term.ctor_substLevels]
    exact .ctor h hc hq _ hp hadm has' hts'
  case hasType_recursor =>
    intro sig k Γ ctx decl D T qs ls ps as r ς χ t Cs us κ h' C h hq hl hp hadm has ht hh hC hCl hCs
      hCt hul hus Rs hRs hut hκ has_ih ht_ih hCt_ih hut_ih k' ls'
    have has' := has_ih ls'
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
      exact hCt_ih j T' C₀ hj hC₀ ls'
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀,
        ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  case hasType_obs =>
    intro sig k Γ ctx decl D T qs ls ps as t d p q ς ps' Ξ Θ B ψ bs h hq hl hp hadm hd has ht hbs
      has_ih ht_ih hbs_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as t x
    have hbs' := hbs_ih ls'
    rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
    rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin, Term.obs_substLevels]
    exact .obs h hq _ hp hadm hd has' (ht_ih ls') hbs'
  case hasType_corec =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' ps' S ss h hq hl hp hadm hpre has hh hS hss
      hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih hgt_ih k' ls'
    have has' := has_ih ls'
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
      have ih := hSt_ih j T' ps'' S₀ hj hS₀ ls'
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
      have ih := hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  case hasType_conv => exact fun ht h ht_ih h_ih => fun ls' => .conv (ht_ih ls') (h_ih ls')
  case eqTerm_refl => exact fun h h_ih => fun ls' => .refl (h_ih ls')
  case eqTerm_symm => exact fun h h_ih => fun ls' => .symm (h_ih ls')
  case eqTerm_trans => exact fun h₁ h₂ h₁_ih h₂_ih => fun ls' => .trans (h₁_ih ls') (h₂_ih ls')
  case eqTerm_conv => exact fun h hA h_ih hA_ih => fun ls' => .conv (h_ih ls') (hA_ih ls')
  case eqTerm_irr =>
    exact fun ht hu hA ht_ih hu_ih hA_ih => fun ls' =>
      .irr (ht_ih ls') (hu_ih ls') (hA_ih ls')
  case eqTerm_secondOrder =>
    refine fun hX hts hts_ih => fun ls' => ?_
    rw [Term.substLevels_instantiate]
    exact .secondOrder (hX.substLevels ls') (hts_ih ls')
  case eqTerm_delta =>
    intro sig k Γ ctx d qs ls ps hctx h hq hl hp hctx_ih k' ls'
    rw [Signature.instanceType_substLevels, Signature.instanceType_substLevels,
      ← Level.getFin_map_subst ls' ls hl]
    exact .delta (hctx_ih ls') h hq _ hp
  case eqTerm_const =>
    intro sig k Γ ctx f j k' g m p A qs ls₁ ls₂ ps hctx h hq hl₁ hl₂ hp hls hctx_ih _ ls'
    rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls₁ hl₁]
    exact .const (hctx_ih ls') h hq _ _ hp (Level.getFin_map_subst_equal ls' hls)
  case eqTerm_univ =>
    exact fun hctx hl hctx_ih => fun ls' =>
      .univ (hctx_ih ls') (Level.subst_equal ls' hl)
  case eqTerm_prop =>
    exact fun hctx hl hctx_ih => fun ls' =>
      .prop (hctx_ih ls') (Level.subst_equal ls' hl)
  case eqTerm_inst =>
    refine fun h hq hl₁ hl₂ hp hadm has hls has_ih => fun ls' => ?_
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels, Term.substLevels, Term.substLevels,
      Universe.substLevels_substLevels_getFin]
    exact .inst h hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls)
  case eqTerm_equality =>
    exact fun hA ht hu hl hA_ih ht_ih hu_ih => fun ls' =>
      .equality (hA_ih ls') (ht_ih ls') (hu_ih ls') (Level.subst_equal ls' hl)
  case eqTerm_transp =>
    intro sig k Γ ctx s l κ A A' t₁ t₁' t₂ t₂' t t' u u' C C' hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih
      ht₂_ih hC_ih ht_ih hu_ih k' ls'
    have hu' := hu_ih ls'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)]
    exact .transp (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls') (ht₂_ih ls')
      (hC_ih ls') (ht_ih ls') hu'
  case eqTerm_transpSame =>
    intro sig k Γ ctx s l κ A t₁ t₂ t u C hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih
      hu_ih hCC_ih k' ls'
    have hu' := hu_ih ls'
    have hCC' := hCC_ih ls'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hu' hCC'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels ls'))
      (fun x => by cases x <;> rfl)] at hCC' ⊢
    exact .transpSame (κ := κ.substLevels ls') (hA_ih ls') (ht₁_ih ls')
      (ht₂_ih ls') (hC_ih ls') (ht_ih ls') hu' hCC'
  case eqTerm_ctor =>
    intro sig k Γ ctx decl D T con qs ls₁ ls₂ ps as₁ as₂ h hc hq hl₁ hl₂ hp hadm has hls ts us hts
      has_ih hts_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := hts_ih ls'
    rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls₁ hl₁] at hts'
    rw [Term.ctor_substLevels, Term.ctor_substLevels]
    exact .ctor h hc hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls) hts'
  case eqTerm_recursor =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ r ς χ t₁ t₂ Cs₁ Cs₂ us₁ us₂ κ h' C₁ h hq hl₁
      hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes Rs₁ Rs₂ hRs₁ hRs₂
      hut hκ has_ih ht_ih hCt_ih hut_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels ls'))
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
      exact hCt_ih j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀ ls'
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
      have ih := hut_ih i j T' con C₀ u₁₀ u₂₀ hi hC₀ hu₁₀ hu₂₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls₁ hl₁] at ih
      exact ih
  case eqTerm_obs =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ t₁ t₂ d p q ς ps' Ξ Θ B ψ bs₁ bs₂ h hq hl₁ hl₂
      hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls₁ ps as₁ t₁ x
    have hbs' := hbs_ih ls'
    rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
    rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin, Term.obs_substLevels, Term.obs_substLevels]
    exact .obs h hq _ _ hp hadm hd has' (Level.getFin_map_subst_equal ls' hls) (ht_ih ls')
      hbs'
  case eqTerm_corec =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ r Ss₁ Ss₂ gs₁ gs₂ h' ps' S₁ S₂ ss₁ ss₂ h hq hl₁
      hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂ hgs hgt has_ih
      hss_ih hSt_ih hSe_ih hgt_ih k' ls'
    have has' := has_ih ls'
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
      have ih := hSt_ih j T' ps'' S₁₀ hj hS₁₀ ls'
      rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
      exact ih
    · intro j T' ps'' S₁' S₂' hj h₁ h₂
      obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_substLevels ls' h₁
      obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_substLevels ls' h₂
      have ih : EqTelescope sig _ _ _
          ⟨.type, (Telescope.packLevel (Ss₁.sorts j) .zero).subst ls'⟩ :=
        hSe_ih j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀ ls'
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
        (o' := (Term.corecAt r T'.name qs (ls₁.map (Level.subst ls')) ps (as₁.substLevels ls')
          (Ss₁.substLevels ls') (gs₁.substLevels ls') ps'').observation T'.name qs
          (ls₁.map (Level.subst ls')) ps ((as₁.substLevels ls').rename (Ren.weakenN ps''.length)))
        (fun d ps' => by
          rw [Term.observation_substLevels, Term.corecAt_substLevels,
            InstanceArgs.substLevels_rename])
        (θ := (as₁.rename (Ren.weakenN ps''.length)).toSubst)
        (θ' := ((as₁.substLevels ls').rename (Ren.weakenN ps''.length)).toSubst)
        (fun x => by rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename]) x
      have ih := hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  case eqTerm_iota =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ Cs us κ i j C h hc hq hl hp hadm u has ts hts
      hi hC hu rs hrs hCl hCs hCt hul hus Rs hRs hut hκ has_ih hts_ih hCt_ih hut_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have hts' := hts_ih ls'
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
      exact hCt_ih j T' C₀ hj hC₀ ls'
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  case eqTerm_etaCtor =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ t Cs us κ i j C e h hc hq hl hp hadm hr has ht
      he hi hC hu hCl hCs hCt hul hus Rs hRs hut hκ has_ih ht_ih he_ih hCt_ih hut_ih k' ls'
    have has' := has_ih ls'
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
      exact hCt_ih j T' C₀ hj hC₀ ls'
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_substLevels_of ls' hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
      have ih := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append,
        Constructor.fieldsAt_substLevels, Term.substLevels_rename,
        Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
      exact ih
  case eqTerm_beta =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' i ps' S ss d p q ς ps₀ Ξ₀ Θ₀ B₀ ψ₀ g bs h hq
      hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih hss_ih hbs_ih hSt_ih
      hgt_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    have ho₀ {a : Scope.Entry} (x : Var Ξ₀ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as
        (.corec r D qs ls ps as ss.terms Ss gs) x
    have hbs' := hbs_ih ls'
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
      have ih := hSt_ih j T' ps'' S₀ hj hS₀ ls'
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
      have ih := hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ ls'
      rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
        Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
        Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
        States.substLevels_rename, States.substLevels_rename,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  case eqTerm_etaObs =>
    intro sig k Γ ctx decl D T qs ls ps as t u h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih
      hobs_ih k' ls'
    have has' := has_ih ls'
    rw [Context.substLevels_substLevels_getFin] at has'
    rw [Term.substLevels]
    refine .etaObs h hq _ hp hadm hr has' (ht_ih ls') (hu_ih ls') ?_
    intro d p q ς ps' Ξ Θ B ψ hd
    have ho {a : Scope.Entry} (x : Var Ξ a) :=
      hd.obsSubst_observation_substLevels ls' D qs ls ps as t x
    have ih := hobs_ih d p q ς ps' Ξ Θ B ψ hd ls'
    rw [Context.substLevels_append, Telescope.substLevels_subst_of ho,
      Telescope.substLevels_substLevels_getFin, Term.observation_substLevels ls' D qs ls ps as t,
      Term.observation_substLevels ls' D qs ls ps as u,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
      Term.substLevels_substLevels_getFin] at ih
    exact ih
  case hasArgs_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case hasArgs_cons =>
    intro sig k Γ ps ctx q p t A ts Θ ht hts ht_ih hts_ih k' ls'
    refine .cons (ht_ih ls') ?_
    have ih := hts_ih ls'
    rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)] at ih
    exact ih
  case eqArgs_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case eqArgs_cons =>
    intro sig k Γ ps ctx q p t u A ts us Θ ht hts ht_ih hts_ih k' ls'
    refine .cons (ht_ih ls') ?_
    have ih := hts_ih ls'
    rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun x => by cases x <;> rfl)] at ih
    exact ih
  case hasInstanceArgs_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case hasInstanceArgs_var =>
    intro sig k Γ Δ ctx as params a A has ha has_ih ha_ih k' ls'
    refine .var (has_ih ls') ?_
    have ih := ha_ih ls'
    rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x)] at ih
    exact ih
  case hasInstanceArgs_secondOrder =>
    intro sig k Γ Δ ps ψ ctx as params Θ A B has hB has_ih hB_ih k' ls'
    refine .secondOrder (has_ih ls') ?_
    have ih := hB_ih ls'
    rw [Context.substLevels_append,
      Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x),
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _
        (fun x => InstanceArgs.toSubst_substLevels ls' as x))] at ih
    exact ih
  case eqInstanceArgs_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case eqInstanceArgs_var =>
    intro sig k Γ Δ ctx as₁ as₂ params a₁ a₂ A has ha has_ih ha_ih k' ls'
    refine .var (has_ih ls') ?_
    have ih := ha_ih ls'
    rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as₁ x)] at ih
    exact ih
  case eqInstanceArgs_secondOrder =>
    intro sig k Γ Δ ps ψ ctx as₁ as₂ params Θ A B₁ B₂ has hB has_ih hB_ih k' ls'
    refine .secondOrder (has_ih ls') ?_
    have ih := hB_ih ls'
    rw [Context.substLevels_append,
      Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as₁ x),
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _
        (fun x => InstanceArgs.toSubst_substLevels ls' as₁ x))] at ih
    exact ih
  case wfTelescope_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case wfTelescope_cons =>
    exact fun hA hκ hΘ hp hA_ih hΘ_ih => fun ls' =>
      .cons (hA_ih ls') (Universe.substLevels_bounded ls' hκ) (hΘ_ih ls') hp
  case wfTelescopeSorts_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case wfTelescopeSorts_cons =>
    exact fun hA hl hΘ hp hA_ih hΘ_ih => fun ls' =>
      .cons (hA_ih ls') (Level.subst_le ls' hl) (hΘ_ih ls') hp
  case eqTelescope_nil => exact fun hctx hctx_ih => fun ls' => .nil (hctx_ih ls')
  case eqTelescope_cons =>
    exact fun hA hκ hΘ hp hA_ih hΘ_ih => fun ls' =>
      .cons (hA_ih ls') (Universe.substLevels_bounded ls' hκ) (hΘ_ih ls') hp
  case wfSig_empty | wfSig_constantDefinition | wfSig_constantDeclaration | wfSig_typeDeclaration |
      wfSig_lifting | wfConstantDefinition_intro | wfConstantDeclaration_intro | wfFields_nil |
      wfFields_cons | wfFields_recursive | wfFields_nested | wfDestructors_nil |
      wfDestructors_cons | wfDestructors_nested | wfDestructors_recursive | wfTypeDeclaration_data |
      wfTypeDeclaration_codata => intros; trivial
end Sic.Core
