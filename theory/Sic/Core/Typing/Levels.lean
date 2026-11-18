module

public import Sic.Core.Typing
import Sic.Core.Results.Substitution

/-!
# Typing at Instantiated Levels

The judgments in a context of annex 14 of RFC 36 hold once levels replace their level variables,
in the context, the terms, the types, the telescopes and the sorts: a rule reads the levels only by
the equality and the order of levels, which every instantiation keeps, and by the instances of the
entries of the signature, whose levels are instantiated in turn.

The entries of the signature are checked once with their level variables, and the rules use them
at the levels of each instance; the lifting of a codata type has more level variables than the
type, whose parameters and destructors it reads at its own.
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.

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
theorem stableUnderLevels : StableUnderLevels :=
  ⟨wfCtx, wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs,
    wfTelescope, wfTelescopeSorts, eqTelescope⟩
where
  wfCtx {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} {ctx : Context k Γ} :
      WfCtx sig ctx → WfCtx sig (ctx.substLevels ls')
    | .empty h => .empty h
    | .var h => .var (wfType ls' h)
    | .secondOrder h => by
      have ih := wfType ls' h
      rw [Context.substLevels_append] at ih
      exact .secondOrder ih
  wfType {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} {ctx : Context k Γ}
      {A : Term k Γ} : WfType sig ctx A → WfType sig (ctx.substLevels ls') (A.substLevels ls')
    | .univType h => .univType (hasType ls' h)
    | .propType h => .propType (hasType ls' h)
  eqType {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} {ctx : Context k Γ}
      {A B : Term k Γ} :
      EqType sig ctx A B → EqType sig (ctx.substLevels ls') (A.substLevels ls') (B.substLevels ls')
    | .refl h => .refl (wfType ls' h)
    | .symm h => .symm (eqType ls' h)
    | .trans h₁ h₂ => .trans (eqType ls' h₁) (eqType ls' h₂)
    | .univType h => .univType (eqTerm ls' h)
    | .propType h => .propType (eqTerm ls' h)
  hasType {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} {ctx : Context k Γ}
      {t A : Term k Γ} :
      HasType sig ctx t A →
        HasType sig (ctx.substLevels ls') (t.substLevels ls') (A.substLevels ls')
    | .var hctx hx => .var (wfCtx ls' hctx) (hx.substLevels ls')
    | .secondOrder hX hts => by
      rw [Term.substLevels_instantiate]
      exact .secondOrder (hX.substLevels ls') (hasArgs ls' hts)
    | .const (ls := ls) hctx h hq hl hp => by
      rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls hl]
      exact .const (wfCtx ls' hctx) h hq _ hp
    | .univ hctx => .univ (wfCtx ls' hctx)
    | .prop hctx => .prop (wfCtx ls' hctx)
    | .inst (ls := ls) h hq hl hp hadm has => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.substLevels, Term.substLevels, Universe.substLevels_substLevels_getFin]
      exact .inst h hq _ hp hadm has'
    | .ctor (ls := ls) h hc hq hl hp hadm has hts => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have hts' := hasArgs ls' hts
      rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl] at hts'
      rw [Term.ctor_substLevels]
      exact .ctor h hc hq _ hp hadm has' hts'
    | .recursor (ls := ls) (as := as) (t := t) (Cs := Cs) (us := us) (κ := κ) h hq hl hp hadm has
        ht hh hC hCl hCs hCt hul hus hRs hut hκ => by
      rename_i Rs
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl)]
      refine .recursor (κ := κ.substLevels ls') (Rs := fun con => (Rs con).substLevels ls') h hq _
        hp hadm has' (hasType ls' ht) hh (Motives.get_substLevels_of ls' hC)
        ((Motives.length_substLevels ls' Cs).trans hCl) ?_ ?_
        ((Branches.length_substLevels ls' us).trans hul) ?_ ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        exact hasType ls' (hCt j T' C₀ hj hC₀)
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_substLevels_of ls' hu⟩
      · intro i j T' con hi
        exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
      · intro i j T' con C' u hi hC' hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
        have ih := hasType ls' (hut i j T' con C₀ u₀ hi hC₀ hu₀)
        rw [Context.substLevels_append, Context.substLevels_append,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename,
          Term.atCtor_substLevels ls' C₀,
          ← Level.getFin_map_subst ls' ls hl] at ih
        exact ih
    | .obs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (Ξ := Ξ) h hq hl hp hadm
        hd has ht hbs => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have ho {a : Scope.Entry} (x : Var Ξ a) :=
        hd.obsSubst_substLevels ls' (Term.observation_substLevels ls' D qs ls ps as t)
          (fun x => InstanceArgs.toSubst_substLevels ls' as x) x
      have hbs' := hasArgs ls' hbs
      rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
      rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin, Term.obs_substLevels]
      exact .obs h hq _ hp hadm hd has' (hasType ls' ht) hbs'
    | .corec (r := r) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs) h hq hl hp
        hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.corec_substLevels]
      refine .corec h hq _ hp hadm hpre has' hh (States.get_substLevels_of ls' hS)
        (hasArgs ls' hss) ((States.length_substLevels ls' Ss).trans hSl) ?_ ?_
        ((CorecBranches.length_substLevels ls' gs).trans hgl) ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_substLevels_of ls' hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        have ih := wfTelescopeSorts ls' (hSt j T' ps'' S₀ hj hS₀)
        rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
        exact ih
      · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_substLevels_of ls' hg⟩
      · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_substLevels ls' hg
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
        have ih := hasType ls' (hgt i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
        rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
          Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
          Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
          States.substLevels_rename, States.substLevels_rename,
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
          Term.substLevels_substLevels_getFin] at ih
        exact ih
    | .conv ht h => .conv (hasType ls' ht) (eqType ls' h)
  eqTerm {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} {ctx : Context k Γ}
      {t u A : Term k Γ} :
      EqTerm sig ctx t u A →
        EqTerm sig (ctx.substLevels ls') (t.substLevels ls') (u.substLevels ls')
          (A.substLevels ls')
    | .refl h => .refl (hasType ls' h)
    | .symm h => .symm (eqTerm ls' h)
    | .trans h₁ h₂ => .trans (eqTerm ls' h₁) (eqTerm ls' h₂)
    | .conv h hA => .conv (eqTerm ls' h) (eqType ls' hA)
    | .irr ht hu hA => .irr (hasType ls' ht) (hasType ls' hu) (hasType ls' hA)
    | .secondOrder hX hts => by
      rw [Term.substLevels_instantiate]
      exact .secondOrder (hX.substLevels ls') (eqArgs ls' hts)
    | .delta (ls := ls) hctx h hq hl hp => by
      rw [Signature.instanceType_substLevels, Signature.instanceType_substLevels,
        ← Level.getFin_map_subst ls' ls hl]
      exact .delta (wfCtx ls' hctx) h hq _ hp
    | .const (ls₁ := ls) hctx h hq hl₁ hl₂ hp hls => by
      rw [Signature.instanceType_substLevels, ← Level.getFin_map_subst ls' ls hl₁]
      exact .const (wfCtx ls' hctx) h hq _ _ hp (Level.getFin_map_subst_equal ls' hls)
    | .univ hctx hl => .univ (wfCtx ls' hctx) (Level.subst_equal ls' hl)
    | .prop hctx hl => .prop (wfCtx ls' hctx) (Level.subst_equal ls' hl)
    | .inst h hq hl₁ hl₂ hp hadm has hls => by
      have has' := eqInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.substLevels, Term.substLevels, Term.substLevels,
        Universe.substLevels_substLevels_getFin]
      exact .inst h hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls)
    | .ctor (ls₁ := ls) h hc hq hl₁ hl₂ hp hadm has hls hts => by
      have has' := eqInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have hts' := eqArgs ls' hts
      rw [Constructor.fieldsAt_substLevels, ← Level.getFin_map_subst ls' ls hl₁] at hts'
      rw [Term.ctor_substLevels, Term.ctor_substLevels]
      exact .ctor h hc hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls) hts'
    | .recursor (ls₁ := ls) (t₁ := t) (Cs₁ := Cs₁) (Cs₂ := Cs₂) (us₁ := us₁) (us₂ := us₂) (κ := κ)
        h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes hRs₁ hRs₂ hut hκ => by
      rename_i Rs₁ Rs₂
      have has' := eqInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl)]
      refine .recursor (κ := κ.substLevels ls') (Rs₁ := fun con => (Rs₁ con).substLevels ls')
        (Rs₂ := fun con => (Rs₂ con).substLevels ls') h hq _ _ hp hadm has' (Level.getFin_map_subst_equal ls' hls) (eqTerm ls' ht) hh
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
        exact eqTerm ls' (hCt j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀)
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
        have ih := eqTerm ls' (hut i j T' con C₀ u₁₀ u₂₀ hi hC₀ hu₁₀ hu₂₀)
        rw [Context.substLevels_append, Context.substLevels_append,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename,
          Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl₁] at ih
        exact ih
    | .obs (D := D) (qs := qs) (ls₁ := ls) (ps := ps) (as₁ := as) (t₁ := t) (Ξ := Ξ) h hq hl₁ hl₂
        hp hadm hd has hls ht hbs => by
      have has' := eqInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have ho {a : Scope.Entry} (x : Var Ξ a) :=
        hd.obsSubst_substLevels ls' (Term.observation_substLevels ls' D qs ls ps as t)
          (fun x => InstanceArgs.toSubst_substLevels ls' as x) x
      have hbs' := eqArgs ls' hbs
      rw [Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin] at hbs'
      rw [Term.substLevels_instantiate, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin, Term.obs_substLevels, Term.obs_substLevels]
      exact .obs h hq _ _ hp hadm hd has' (Level.getFin_map_subst_equal ls' hls) (eqTerm ls' ht)
        hbs'
    | .corec (r := r) (qs := qs) (ls₁ := ls) (ps := ps) (as₁ := as) (Ss₁ := Ss₁) (Ss₂ := Ss₂)
        (gs₁ := gs₁) (gs₂ := gs₂) h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs
        hSk hSt hSe hgl₁ hgl₂ hgs hgt => by
      have has' := eqInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.corec_substLevels, Term.corec_substLevels]
      refine .corec h hq _ _ hp hadm hpre has' (Level.getFin_map_subst_equal ls' hls) hh
        (States.get_substLevels_of ls' hS₁) (States.get_substLevels_of ls' hS₂) (eqArgs ls' hss)
        ((States.length_substLevels ls' Ss₁).trans hSl₁)
        ((States.length_substLevels ls' Ss₂).trans hSl₂) ?_
        (fun j => by rw [States.sorts_substLevels, States.sorts_substLevels, hSk j]) ?_ ?_
        ((CorecBranches.length_substLevels ls' gs₁).trans hgl₁)
        ((CorecBranches.length_substLevels ls' gs₂).trans hgl₂) ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S₁', S₂', h₁, h₂⟩ := hSs j T' hj
        exact ⟨ps'', _, _, States.get_substLevels_of ls' h₁, States.get_substLevels_of ls' h₂⟩
      · intro j T' ps'' S₁' hj h₁
        obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_substLevels ls' h₁
        have ih := wfTelescopeSorts ls' (hSt j T' ps'' S₁₀ hj hS₁₀)
        rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
        exact ih
      · intro j T' ps'' S₁' S₂' hj h₁ h₂
        obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_substLevels ls' h₁
        obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_substLevels ls' h₂
        have ih : EqTelescope sig _ _ _
            ⟨.type, (Telescope.packLevel (Ss₁.sorts j) .zero).subst ls'⟩ :=
          eqTelescope ls' (hSe j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀)
        rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
        exact ih
      · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
        exact ⟨_, _, CorecBranches.get_substLevels_of ls' hg₁,
          CorecBranches.get_substLevels_of ls' hg₂⟩
      · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g₁₀, hg₁₀, rfl⟩ := CorecBranches.get_substLevels ls' hg₁
        obtain ⟨g₂₀, hg₂₀, rfl⟩ := CorecBranches.get_substLevels ls' hg₂
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
        have ih := eqTerm ls'
          (hgt i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀)
        rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
          Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
          Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
          States.substLevels_rename, States.substLevels_rename,
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
          Term.substLevels_substLevels_getFin] at ih
        exact ih
    | .iota (r := r) (ς := ς) (χ := χ) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as)
        (Cs := Cs) (us := us) (κ := κ) h hc hq hl hp hadm has hts hi hC hu hrs hCl hCs hCt
        hul hus hRs hut hκ => by
      rename_i Rs
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have hts' := hasArgs ls' hts
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
        exact hasType ls' (hCt j T' C₀ hj hC₀)
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_substLevels_of ls' hu⟩
      · intro i j T' con hi
        exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
      · intro i j T' con C' u hi hC' hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
        have ih := hasType ls' (hut i j T' con C₀ u₀ hi hC₀ hu₀)
        rw [Context.substLevels_append, Context.substLevels_append,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename,
          Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
        exact ih
    | .etaCtor (D := D) (T := T) (con := con) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t)
        (e := e) (Cs := Cs) (us := us) (κ := κ) h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs
        hCt hul hus hRs hut hκ => by
      rename_i Rs
      have has' := hasInstanceArgs ls' has
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
        _ hp hadm hr has' (hasType ls' ht) (hasType ls' he) hi (Motives.get_substLevels_of ls' hC)
        hu' ((Motives.length_substLevels ls' Cs).trans hCl) ?_ ?_
        ((Branches.length_substLevels ls' us).trans hul) ?_ ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_substLevels_of ls' hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        exact hasType ls' (hCt j T' C₀ hj hC₀)
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_substLevels_of ls' hu⟩
      · intro i j T' con hi
        exact (hRs i j T' con hi).imp fun _ => Constructor.ResultTypes.substLevels_ofMotives ls'
      · intro i j T' con C' u hi hC' hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels ls' hu
        have ih := hasType ls' (hut i j T' con C₀ u₀ hi hC₀ hu₀)
        rw [Context.substLevels_append, Context.substLevels_append,
          Constructor.fieldsAt_substLevels, Term.substLevels_rename,
          Term.atCtor_substLevels ls' C₀, ← Level.getFin_map_subst ls' ls hl] at ih
        exact ih
    | .beta (r := r) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs)
        (ss := ss) (Ξ₀ := Ξ₀) h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs
        hgt => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      have ho₀ {a : Scope.Entry} (x : Var Ξ₀ a) := hd.obsSubst_substLevels ls'
        (Term.observation_substLevels ls' D qs ls ps as (.corec r D qs ls ps as ss.terms Ss gs))
        (fun x => InstanceArgs.toSubst_substLevels ls' as x) x
      have hbs' := hasArgs ls' hbs
      rw [Telescope.substLevels_subst_of ho₀, Telescope.substLevels_substLevels_getFin,
        Term.corec_substLevels] at hbs'
      rw [Term.obs_substLevels, Term.observed_substLevels, Term.substLevels_instantiate,
        Term.substLevels_instantiate, Args.substLevels_rename, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho₀),
        Term.substLevels_substLevels_getFin, Universe.substLevels_substLevels_getFin,
        Term.corec_substLevels]
      refine .beta h hq _ hp hadm hpre has' hh (States.get_substLevels_of ls' hS)
        (hasArgs ls' hss) hi hd (CorecBranches.get_substLevels_of ls' hg) hbs'
        ((States.length_substLevels ls' Ss).trans hSl) ?_ ?_
        ((CorecBranches.length_substLevels ls' gs).trans hgl) ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_substLevels_of ls' hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        have ih := wfTelescopeSorts ls' (hSt j T' ps'' S₀ hj hS₀)
        rw [Telescope.packLevel_subst, ← States.sorts_substLevels] at ih
        exact ih
      · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_substLevels_of ls' hg⟩
      · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels ls' hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_substLevels ls' hg
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
        have ih := hasType ls' (hgt i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
        rw [Context.substLevels_append, Context.substLevels_append ls' ctx S₀,
          Telescope.substLevels_subst_of ho, Telescope.substLevels_substLevels_getFin,
          Term.branchResult_substLevels, Universe.substLevels_substLevels_getFin,
          States.substLevels_rename, States.substLevels_rename,
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
          Term.substLevels_substLevels_getFin] at ih
        exact ih
    | .etaObs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (u := u) h hq hl hp
        hadm hr has ht hu hobs => by
      have has' := hasInstanceArgs ls' has
      rw [Context.substLevels_substLevels_getFin] at has'
      rw [Term.substLevels]
      refine .etaObs h hq _ hp hadm hr has' (hasType ls' ht) (hasType ls' hu) ?_
      intro d p q ς ps' Ξ Θ B ψ hd
      have ho {a : Scope.Entry} (x : Var Ξ a) :=
        hd.obsSubst_substLevels ls' (Term.observation_substLevels ls' D qs ls ps as t)
          (fun x => InstanceArgs.toSubst_substLevels ls' as x) x
      have ih := eqTerm ls' (hobs d p q ς ps' Ξ Θ B ψ hd)
      rw [Context.substLevels_append, Telescope.substLevels_subst_of ho,
        Telescope.substLevels_substLevels_getFin, Term.observation_substLevels ls' D qs ls ps as t,
        Term.observation_substLevels ls' D qs ls ps as u,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      exact ih
  hasArgs {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps} :
      HasArgs sig ctx ts Θ →
        HasArgs sig (ctx.substLevels ls') (ts.substLevels ls') (Θ.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .cons (t := t) ht hts => by
      refine .cons (hasType ls' ht) ?_
      have ih := hasArgs ls' hts
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl)] at ih
      exact ih
  eqArgs {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} :
      EqArgs sig ctx ts us Θ →
        EqArgs sig (ctx.substLevels ls') (ts.substLevels ls') (us.substLevels ls')
          (Θ.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .cons (t := t) ht hts => by
      refine .cons (eqTerm ls' ht) ?_
      have ih := eqArgs ls' hts
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun x => by cases x <;> rfl)] at ih
      exact ih
  hasInstanceArgs {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ Δ : Scope}
      {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
      HasInstanceArgs sig ctx as params →
        HasInstanceArgs sig (ctx.substLevels ls') (as.substLevels ls') (params.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .var (as := as) has ha => by
      refine .var (hasInstanceArgs ls' has) ?_
      have ih := hasType ls' ha
      rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x)] at ih
      exact ih
    | .secondOrder (as := as) has hB => by
      refine .secondOrder (hasInstanceArgs ls' has) ?_
      have ih := hasType ls' hB
      rw [Context.substLevels_append,
        Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x),
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (fun x => InstanceArgs.toSubst_substLevels ls' as x))] at ih
      exact ih
  eqInstanceArgs {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ Δ : Scope}
      {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} :
      EqInstanceArgs sig ctx as₁ as₂ params →
        EqInstanceArgs sig (ctx.substLevels ls') (as₁.substLevels ls') (as₂.substLevels ls')
          (params.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .var (as₁ := as) has ha => by
      refine .var (eqInstanceArgs ls' has) ?_
      have ih := eqTerm ls' ha
      rw [Term.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x)] at ih
      exact ih
    | .secondOrder (as₁ := as) has hB => by
      refine .secondOrder (eqInstanceArgs ls' has) ?_
      have ih := eqTerm ls' hB
      rw [Context.substLevels_append,
        Telescope.substLevels_subst_of (fun x => InstanceArgs.toSubst_substLevels ls' as x),
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _
          (fun x => InstanceArgs.toSubst_substLevels ls' as x))] at ih
      exact ih
  wfTelescope {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k} :
      WfTelescope sig ctx Θ κ →
        WfTelescope sig (ctx.substLevels ls') (Θ.substLevels ls') (κ.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .cons hA hκ hΘ hp =>
      .cons (hasType ls' hA) (Universe.substLevels_bounded ls' hκ) (wfTelescope ls' hΘ) hp
  wfTelescopeSorts {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)}
      {l : Level k} :
      WfTelescopeSorts sig ctx Θ κs l →
        WfTelescopeSorts sig (ctx.substLevels ls') (Θ.substLevels ls')
          (κs.map (Universe.substLevels ls')) (l.subst ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .cons hA hl hΘ hp =>
      .cons (hasType ls' hA) (Level.subst_le ls' hl) (wfTelescopeSorts ls' hΘ) hp
  eqTelescope {sig : Signature} {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} :
      EqTelescope sig ctx Θ₁ Θ₂ κ →
        EqTelescope sig (ctx.substLevels ls') (Θ₁.substLevels ls') (Θ₂.substLevels ls')
          (κ.substLevels ls')
    | .nil hctx => .nil (wfCtx ls' hctx)
    | .cons hA hκ hΘ hp =>
      .cons (eqTerm ls' hA) (Universe.substLevels_bounded ls' hκ) (eqTelescope ls' hΘ) hp

end Sic.Core
