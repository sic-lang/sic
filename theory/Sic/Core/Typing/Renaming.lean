module

public import Sic.Core.Typing

/-!
# Renaming of the Typing

The judgments of typing and of equality of annex 13 of RFC 36 are stable under the typed renamings
`Σ; Γ ⊢ ξ : Δ`: a judgment in the context `Δ` holds, renamed by `ξ`, in the context `Γ`, whose
declarations give each variable of `Δ` its type, renamed.

A renaming is the substitution of the second order `Ren.toSubst`, so that the proof states the
judgments substituted by it, and the laws of the substitutions give the premises of each rule.
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.
Under the binders of a rule, the renaming is lifted, and the context extended by the type renamed is
well formed: the relation `TypedRen.Lifted` lifts a typed renaming under variables without this
condition, and the clause of the judgment `Σ ⊢ Γ` builds the context extended at the leaves of the
derivation, from the derivation of the context extended, which the rule `(ctx_x)` gives with a
derivation of its type, a subderivation renamed by the renaming before the lift.

ADE weaken by the renamings that keep the order of the variables, `ρ ∷ Δ ⊇ Γ`, and build the context
extended from the derivation of the type, which the rules of a binder do not always have, by a
well-founded recursion on the sizes of the derivations; here the renamings are all those that the
context types, and the recursion is structural.
-/

@[expose] public section

namespace Sic.Core

/-! ## Typed Renamings -/

-- ADE: `_»_∷ʷ_⊇_`, in `Definition/Typed/Weakening.agda`, for the renamings that keep the order.
/-- `Σ; Γ ⊢ ξ : Δ`: the renaming `ξ` of the scope `Δ` in the scope `Γ` is typed, the context `Γ` being
well formed and declaring the image of each variable of `Δ` with its type, renamed.
RFC: `\mathsf{ren}_\vdash` -/
structure TypedRen (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx' : Context k Γ) (ξ : Ren Γ Δ)
    (ctx : Context k Δ) : Prop where
  /-- The context of the renaming is well formed. -/
  wfCtx : WfCtx sig ctx'
  /-- The image of a variable is declared with its type, renamed. -/
  varIn : ∀ {x : Var Δ .var} {A : Term k Δ}, ctx.VarIn x A → ctx'.VarIn (ξ x) (A.rename ξ)
  /-- The image of a second-order variable is declared with its telescope and its type, renamed. -/
  secondOrderIn : ∀ {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)},
    ctx.SecondOrderIn X Θ A → ctx'.SecondOrderIn (ξ X) (Θ.rename ξ) (A.rename (Ren.liftN _ ξ))

-- ADE: `_∷_⊇_`, in `Definition/Typed/Weakening.agda`, whose constructor `lift` it has.
/-- A typed renaming `ξ` lifted under variables, as the substitution `θ` that gives each variable the
abstraction of its image, whose contexts are extended by a type and by the type substituted, without
the condition that the context extended be well formed, which the leaves of a derivation in the
context extended give.
The substitution is lifted as the substitutions of the rules are, so that the judgments under the
binders of a rule hold at the substitution of the rule without conversion. -/
inductive TypedRen.Lifted (sig : Signature) {k : Nat} :
    {Γ Δ : Scope} → Context k Γ → Subst k Γ Δ → Ren Γ Δ → Context k Δ → Prop where
  /-- A typed renaming, as a substitution. -/
  | base {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ}
      (h : TypedRen sig ctx' ξ ctx) (hθ : ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) :
      Lifted sig ctx' @θ @ξ ctx
  /-- A lifted renaming, lifted under a variable. -/
  | var {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ}
      (A : Term k Δ) (h : Lifted sig ctx' @θ @ξ ctx) :
      Lifted sig (ctx'.var (A.subst θ)) (Subst.lift θ) (Ren.lift ξ) (ctx.var A)

variable {sig : Signature} {k : Nat}

/-- The substitution of a lifted renaming gives each variable the abstraction of its image. -/
theorem TypedRen.Lifted.eta {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
    {ctx : Context k Δ} : Lifted sig ctx' @θ @ξ ctx → ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)
  | .base _ hθ => hθ
  | .var _ h => Subst.lift_eta_of h.eta

/-- A lifted renaming, lifted under the variables of a telescope. -/
theorem TypedRen.Lifted.append {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → Lifted sig ctx' @θ @ξ ctx →
      Lifted sig (ctx'.append (Θ.subst θ)) (Subst.liftN ps.length θ) (Ren.liftN ps.length ξ)
        (ctx.append Θ)
  | [], .nil, h => h
  | _ :: _, .cons _ _ A Θ, h => TypedRen.Lifted.append Θ (h.var A)

-- ADE: `wkIndex`, in `Definition/Typed/Weakening.agda`.
/-- The image of a variable by a lifted renaming is declared with its type, substituted. -/
theorem TypedRen.Lifted.varIn {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} {x : Var Δ .var} {A : Term k Δ} :
    Lifted sig ctx' @θ @ξ ctx → ctx.VarIn x A → ctx'.VarIn (ξ x) (A.subst θ)
  | .base h hθ, hx => by rw [← Term.rename_eq_subst_of hθ]; exact h.varIn hx
  | .var B _, .zero => by rw [Term.subst_lift_rename_weaken]; exact .zero
  | .var B h, .succVar hx => by rw [Term.subst_lift_rename_weaken]; exact .succVar (h.varIn hx)

-- ADE: none.
/-- The image of a second-order variable by a lifted renaming is declared with its telescope and its
type, substituted. -/
theorem TypedRen.Lifted.secondOrderIn {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} :
    Lifted sig ctx' @θ @ξ ctx → ctx.SecondOrderIn X Θ A →
      ctx'.SecondOrderIn (ξ X) (Θ.subst θ) (A.subst (Subst.liftN _ θ))
  | .base h hθ, hX => by
    rw [← Telescope.rename_eq_subst_of hθ, ← Term.rename_eq_subst_of (Subst.liftN_eta_of _ hθ)]
    exact h.secondOrderIn hX
  | .var B h, .succVar hX => by
    rw [Telescope.subst_lift_rename_weaken, Term.subst_liftN_lift_rename_weaken]
    exact .succVar (h.secondOrderIn hX)

/-! ## Stability of the Typing -/

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`.
/-- The judgments in a context are stable under the typed renamings of the context. -/
structure StableUnderRenaming : Prop where
  /-- A type, renamed, is a type.
  RFC: `\mathsf{ren}_\vdash.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {ξ : Ren Γ Δ}
    {ctx : Context k Δ} {A : Term k Δ},
    WfType sig ctx A → TypedRen sig ctx' ξ ctx → WfType sig ctx' (A.rename ξ)
  /-- Equal types, renamed, are equal.
  RFC: `\mathsf{ren}_\vdash.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {ξ : Ren Γ Δ}
    {ctx : Context k Δ} {A B : Term k Δ},
    EqType sig ctx A B → TypedRen sig ctx' ξ ctx → EqType sig ctx' (A.rename ξ) (B.rename ξ)
  /-- A term of a type, renamed, is a term of the type, renamed.
  RFC: `\mathsf{ren}_\vdash.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {ξ : Ren Γ Δ}
    {ctx : Context k Δ} {t A : Term k Δ},
    HasType sig ctx t A → TypedRen sig ctx' ξ ctx → HasType sig ctx' (t.rename ξ) (A.rename ξ)
  /-- Equal terms of a type, renamed, are equal at the type, renamed.
  RFC: `\mathsf{ren}_\vdash.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {ξ : Ren Γ Δ}
    {ctx : Context k Δ} {t u A : Term k Δ},
    EqTerm sig ctx t u A → TypedRen sig ctx' ξ ctx →
      EqTerm sig ctx' (t.rename ξ) (u.rename ξ) (A.rename ξ)
  /-- Arguments of a telescope, renamed, are arguments of the telescope, renamed.
  RFC: `\mathsf{ren}_\vdash.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {ts : Args k Δ ps}
    {Θ : Telescope k Δ ps},
    HasArgs sig ctx ts Θ → TypedRen sig ctx' ξ ctx → HasArgs sig ctx' (ts.rename ξ) (Θ.rename ξ)
  /-- Equal arguments of a telescope, renamed, are equal arguments of the telescope, renamed.
  RFC: `\mathsf{ren}_\vdash.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {ts us : Args k Δ ps}
    {Θ : Telescope k Δ ps},
    EqArgs sig ctx ts us Θ → TypedRen sig ctx' ξ ctx →
      EqArgs sig ctx' (ts.rename ξ) (us.rename ξ) (Θ.rename ξ)
  /-- Arguments of an instance, renamed, are arguments of its parameters.
  RFC: `\mathsf{ren}_\vdash.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} {as : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    HasInstanceArgs sig ctx as params → TypedRen sig ctx' ξ ctx →
      HasInstanceArgs sig ctx' (as.rename ξ) params
  /-- Equal arguments of instances, renamed, are equal arguments of the parameters.
  RFC: `\mathsf{ren}_\vdash.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    EqInstanceArgs sig ctx as₁ as₂ params → TypedRen sig ctx' ξ ctx →
      EqInstanceArgs sig ctx' (as₁.rename ξ) (as₂.rename ξ) params
  /-- A telescope in a sort, renamed, is in the sort.
  RFC: `\mathsf{ren}_\vdash.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
    {κ : Universe k},
    WfTelescope sig ctx Θ κ → TypedRen sig ctx' ξ ctx → WfTelescope sig ctx' (Θ.rename ξ) κ
  /-- Equal telescopes in a sort, renamed, are equal in the sort.
  RFC: `\mathsf{ren}_\vdash.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps}
    {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → TypedRen sig ctx' ξ ctx →
      EqTelescope sig ctx' (Θ₁.rename ξ) (Θ₂.rename ξ) κ

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`.
/-- The judgments in a context are stable under the typed renamings of the context.
RFC: `\mathsf{ren}_\vdash.A`
RFC: `\mathsf{ren}_\vdash.A_\equiv`
RFC: `\mathsf{ren}_\vdash.t`
RFC: `\mathsf{ren}_\vdash.t_\equiv`
RFC: `\mathsf{ren}_\vdash.\bar t`
RFC: `\mathsf{ren}_\vdash.\bar t_\equiv`
RFC: `\mathsf{ren}_\vdash.\bar a`
RFC: `\mathsf{ren}_\vdash.\bar a_\equiv`
RFC: `\mathsf{ren}_\vdash.\Theta`
RFC: `\mathsf{ren}_\vdash.\Theta_\equiv` -/
theorem stableUnderRenaming : StableUnderRenaming :=
  ⟨fun h hξ => by rw [Term.rename_eq_subst]; exact wfType h (.base hξ fun _ => rfl),
    fun h hξ => by rw [Term.rename_eq_subst, Term.rename_eq_subst]; exact eqType h (.base hξ fun _ => rfl),
    fun h hξ => by rw [Term.rename_eq_subst, Term.rename_eq_subst]; exact hasType h (.base hξ fun _ => rfl),
    fun h hξ => by
      rw [Term.rename_eq_subst, Term.rename_eq_subst, Term.rename_eq_subst]
      exact eqTerm h (.base hξ fun _ => rfl),
    fun h hξ => by
      rw [Args.rename_eq_subst, Telescope.rename_eq_subst]; exact hasArgs h (.base hξ fun _ => rfl),
    fun h hξ => by
      rw [Args.rename_eq_subst, Args.rename_eq_subst, Telescope.rename_eq_subst]
      exact eqArgs h (.base hξ fun _ => rfl),
    fun h hξ => by rw [InstanceArgs.rename_eq_subst]; exact hasInstanceArgs h (.base hξ fun _ => rfl),
    fun h hξ => by
      rw [InstanceArgs.rename_eq_subst, InstanceArgs.rename_eq_subst]
      exact eqInstanceArgs h (.base hξ fun _ => rfl),
    fun h hξ => by rw [Telescope.rename_eq_subst]; exact wfTelescope h (.base hξ fun _ => rfl),
    fun h hξ => by
      rw [Telescope.rename_eq_subst, Telescope.rename_eq_subst]; exact eqTelescope h (.base hξ fun _ => rfl)⟩
where
  wfCtx {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ctx : Context k Δ} : WfCtx sig ctx → TypedRen.Lifted sig ctx' @θ @ξ ctx → WfCtx sig ctx'
    | _, .base hξ _ => hξ.wfCtx
    | .var hA, .var _ hξ => .var (wfType hA hξ)
  wfType {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ctx : Context k Δ} {A : Term k Δ} :
      WfType sig ctx A → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        WfType sig ctx' (A.subst θ)
    | .univType h, hξ => .univType (hasType h hξ)
    | .propType h, hξ => .propType (hasType h hξ)
  eqType {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ctx : Context k Δ} {A B : Term k Δ} :
      EqType sig ctx A B → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        EqType sig ctx' (A.subst θ) (B.subst θ)
    | .refl h, hξ => .refl (wfType h hξ)
    | .symm h, hξ => .symm (eqType h hξ)
    | .trans h₁ h₂, hξ => .trans (eqType h₁ hξ) (eqType h₂ hξ)
    | .univType h, hξ => .univType (eqTerm h hξ)
    | .propType h, hξ => .propType (eqTerm h hξ)
  hasType {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ctx : Context k Δ} {t A : Term k Δ} :
      HasType sig ctx t A → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        HasType sig ctx' (t.subst θ) (A.subst θ)
    | .var (x := x) hctx hx, hξ => by
      rw [Term.var_subst_of (hξ.eta x)]
      exact .var (wfCtx hctx hξ) (hξ.varIn hx)
    | .secondOrder (X := X) hX hts, hξ => by
      rw [Term.var_subst_of (hξ.eta X), Term.instantiate_subst]
      exact .secondOrder (hξ.secondOrderIn hX) (hasArgs hts hξ)
    | .const hctx h hq hl hp, hξ => by
      rw [Signature.instanceType, Term.weakenClosed_subst]
      exact .const (wfCtx hctx hξ) h hq hl hp
    | .univ hctx, hξ => .univ (wfCtx hctx hξ)
    | .prop hctx, hξ => .prop (wfCtx hctx hξ)
    | .inst h hq hl hp hadm has, hξ => .inst h hq hl hp hadm (hasInstanceArgs has hξ)
    | .ctor h hc hq hl hp hadm has hts, hξ => by
      rw [Term.ctor_subst]
      refine .ctor h hc hq hl hp hadm (hasInstanceArgs has hξ) ?_
      rw [← Constructor.fieldsAt_subst]
      exact hasArgs hts hξ
    | .recursor (as := as) (t := t) (Cs := Cs) (us := us) (C := C) h hq hl hp hadm has ht hh hC hCl
        hCs hCt hul hus hut hκ, hξ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t _)]
      refine .recursor h hq hl hp hadm (hasInstanceArgs has hξ) (hasType ht hξ) hh
        (Motives.get_subst _ hC) ((Motives.length_subst _ Cs).trans hCl) ?_ ?_
        ((Branches.length_subst _ us).trans hul) ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst _ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hξ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst _ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv _ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv _ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hξ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst _ C₀] at ih
        exact ih
    | .obs (as := as) (t := t) (ls := ls) (qs := qs) (ps := ps) (D := D) (Θ := Θ) (B := B) (bs := bs)
        h hq hl hp hadm hd has ht hbs, hξ => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
        (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst]
      refine .obs h hq hl hp hadm hd (hasInstanceArgs has hξ) (hasType ht hξ) ?_
      rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
      exact hasArgs hbs hξ
    | .corec (r := r) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs) (ss := ss)
        (κs := κs) h hq hl hp hadm has hh hS hss hSl hSs hSt hgl hgs hgt, hξ => by
      rw [Term.corec_subst]
      refine .corec (κs := κs) h hq hl hp hadm (hasInstanceArgs has hξ) hh (States.get_subst _ hS)
        (hasArgs hss hξ) ((States.length_subst _ Ss).trans hSl) ?_ ?_
        ((CorecBranches.length_subst _ gs).trans hgl) ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst _ hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        exact wfTelescope (hSt j T' ps'' S₀ hj hS₀) hξ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst _ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv _ hg
        have ih := hasType (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
          ((hξ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
        exact ih
    | .conv ht h, hξ => .conv (hasType ht hξ) (eqType h hξ)
  eqTerm {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ctx : Context k Δ} {t u A : Term k Δ} :
      EqTerm sig ctx t u A → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        EqTerm sig ctx' (t.subst θ) (u.subst θ)
          (A.subst θ)
    | .refl h, hξ => .refl (hasType h hξ)
    | .symm h, hξ => .symm (eqTerm h hξ)
    | .trans h₁ h₂, hξ => .trans (eqTerm h₁ hξ) (eqTerm h₂ hξ)
    | .conv h hA, hξ => .conv (eqTerm h hξ) (eqType hA hξ)
    | .irr ht hu hA, hξ => .irr (hasType ht hξ) (hasType hu hξ) (hasType hA hξ)
    | .secondOrder (X := X) hX hts, hξ => by
      rw [Term.var_subst_of (hξ.eta X), Term.var_subst_of (hξ.eta X), Term.instantiate_subst]
      exact .secondOrder (hξ.secondOrderIn hX) (eqArgs hts hξ)
    | .delta hctx h hq hl hp, hξ => by
      rw [Signature.instanceType, Signature.instanceType, Term.weakenClosed_subst,
        Term.weakenClosed_subst]
      exact .delta (wfCtx hctx hξ) h hq hl hp
    | .const hctx h hq hl₁ hl₂ hp hls, hξ => by
      rw [Signature.instanceType, Term.weakenClosed_subst]
      exact .const (wfCtx hctx hξ) h hq hl₁ hl₂ hp hls
    | .univ hctx hl, hξ => .univ (wfCtx hctx hξ) hl
    | .prop hctx hl, hξ => .prop (wfCtx hctx hξ) hl
    | .inst h hq hl₁ hl₂ hp hadm has hls, hξ =>
      .inst h hq hl₁ hl₂ hp hadm (eqInstanceArgs has hξ) hls
    | .ctor h hc hq hl₁ hl₂ hp hadm has hls hts, hξ => by
      rw [Term.ctor_subst, Term.ctor_subst]
      refine .ctor h hc hq hl₁ hl₂ hp hadm (eqInstanceArgs has hξ) hls ?_
      rw [← Constructor.fieldsAt_subst]
      exact eqArgs hts hξ
    | .recursor (as₁ := as) (t₁ := t) (Cs₁ := Cs₁) (Cs₂ := Cs₂) (us₁ := us₁) (us₂ := us₂)
        h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hut hκ,
        hξ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
      refine .recursor h hq hl₁ hl₂ hp hadm (eqInstanceArgs has hξ) hls (eqTerm ht hξ) hh
        (Motives.get_subst θ hC) ((Motives.length_subst θ Cs₁).trans hCl₁)
        ((Motives.length_subst θ Cs₂).trans hCl₂) ?_ ?_ ?_ ((Branches.length_subst θ us₁).trans hul₁)
        ((Branches.length_subst θ us₂).trans hul₂) ?_ ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs₁ j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs₂ j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C₁' C₂' hj h₁ h₂
        obtain ⟨C₁₀, hC₁₀, rfl⟩ := Motives.get_subst_inv θ h₁
        obtain ⟨C₂₀, hC₂₀, rfl⟩ := Motives.get_subst_inv θ h₂
        have ih := eqTerm (hCt j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀) (hξ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus₁ i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus₂ i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con C' R u₁ u₂ hi hC' hR hu₁ hu₂
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv θ hR
        obtain ⟨u₁₀, hu₁₀, rfl⟩ := Branches.get_subst_inv θ hu₁
        obtain ⟨u₂₀, hu₂₀, rfl⟩ := Branches.get_subst_inv θ hu₂
        have ih := eqTerm (hut i j T' con C₀ R₀ u₁₀ u₂₀ hi hC₀ hR₀ hu₁₀ hu₂₀)
          ((hξ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .obs (as₁ := as) (t₁ := t) (ls₁ := ls) (qs := qs) (ps := ps) (D := D) (bs₁ := bs₁)
        (bs₂ := bs₂) h hq hl₁ hl₂ hp hadm hd has hls ht hbs, hξ => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
        (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst, Term.obs_subst]
      refine .obs h hq hl₁ hl₂ hp hadm hd (eqInstanceArgs has hξ) hls (eqTerm ht hξ) ?_
      rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
      exact eqArgs hbs hξ
    | .corec (r := r) (qs := qs) (ls₁ := ls) (ps := ps) (as₁ := as) (Ss₁ := Ss₁) (Ss₂ := Ss₂)
        (gs₁ := gs₁) (gs₂ := gs₂) (ss₁ := ss₁) (ss₂ := ss₂) (κs := κs) h hq hl₁ hl₂ hp hadm has hls
        hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSt hgl₁ hgl₂ hgs hgt, hξ => by
      rw [Term.corec_subst, Term.corec_subst]
      refine .corec (κs := κs) h hq hl₁ hl₂ hp hadm (eqInstanceArgs has hξ) hls hh
        (States.get_subst θ hS₁) (States.get_subst θ hS₂) (eqArgs hss hξ)
        ((States.length_subst θ Ss₁).trans hSl₁) ((States.length_subst θ Ss₂).trans hSl₂) ?_ ?_
        ((CorecBranches.length_subst θ gs₁).trans hgl₁) ((CorecBranches.length_subst θ gs₂).trans hgl₂)
        ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S₁', S₂', h₁, h₂⟩ := hSs j T' hj
        exact ⟨ps'', _, _, States.get_subst θ h₁, States.get_subst θ h₂⟩
      · intro j T' ps'' S₁' S₂' hj h₁ h₂
        obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_subst_inv θ h₁
        obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_subst_inv θ h₂
        exact eqTelescope (hSt j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀) hξ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, _, CorecBranches.get_subst θ hg₁, CorecBranches.get_subst θ hg₂⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₁₀, hg₁₀, rfl⟩ := CorecBranches.get_subst_inv θ hg₁
        obtain ⟨g₂₀, hg₂₀, rfl⟩ := CorecBranches.get_subst_inv θ hg₂
        have ih := eqTerm (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀)
          ((hξ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Telescope.subst_subst_of
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''))] at ih
        exact ih
    | .iota (r := r) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (Cs := Cs) (us := us)
        h hc hq hl hp hadm has hts hi hC hu hCl hCs hCt hul hus hut hκ,
        hξ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ θ), Term.instantiate_subst,
        Term.instantiate_subst, Args.subst_liftN_rename_weakenN,
        Args.results_subst θ (f' := fun D' t => .recursor r D' qs ls ps (as.subst θ) t (Cs.subst θ)
          (us.subst θ)) (fun _ _ => rfl)]
      show EqTerm sig ctx' (.recursor _ _ _ _ _ _ (Term.subst θ (.ctor _ _ _ _ _ _ _)) _ _) _ _
      rw [Term.ctor_subst]
      refine .iota h hc hq hl hp hadm (hasInstanceArgs has hξ) ?_ hi (Motives.get_subst θ hC)
        (Branches.get_subst θ hu) ((Motives.length_subst θ Cs).trans hCl) ?_ ?_
        ((Branches.length_subst θ us).trans hul) ?_ ?_ hκ
      · rw [← Constructor.fieldsAt_subst]
        exact hasArgs hts hξ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hξ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv θ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hξ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .etaCtor (D := D) (T := T) (con := con) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t)
        (e := e) (Cs := Cs) (us := us) (i := i) h hc hq hl hp hadm hr has ht he hi hC hu hCl
        hCs hCt hul hus hut hκ, hξ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ),
        Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
      have hu' := Branches.get_subst θ hu
      rw [show ((e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).subst
            (Subst.liftN 0 (Subst.liftN _ θ)) :
              Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)) =
          (e.subst (Subst.lift θ)).atCtor T.name qs ls ps (as.subst θ) con.name
            (con.params (.ofLists qs ps hq hp)) from Term.atCtor_subst θ e _ _ _ _ _ _ _] at hu'
      have he' := hasType he (hξ.var (.inst D qs ls ps as))
      refine .etaCtor h hc hq hl hp hadm hr (hasInstanceArgs has hξ) (hasType ht hξ) he' hi (Motives.get_subst θ hC) hu'
        ((Motives.length_subst θ Cs).trans hCl) ?_ ?_ ((Branches.length_subst θ us).trans hul) ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hξ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv θ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hξ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .beta (r := r) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs)
        (ss := ss) (κs := κs) h hq hl hp hadm has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt,
        hξ => by
      rw [Term.obs_subst, Term.corec_subst, Term.instantiate_subst, Term.instantiate_subst,
        Args.subst_liftN_rename_weakenN, Term.instantiate_subst, Term.subst_subst_of
          (Subst.liftN_subst_of _ (hd.obsSubst_observation_subst θ D qs ls ps as _)),
        Term.corec_subst]
      refine .beta (κs := κs) h hq hl hp hadm (hasInstanceArgs has hξ) hh (States.get_subst θ hS)
        (hasArgs hss hξ) hi hd (CorecBranches.get_subst θ hg) ?_
        ((States.length_subst θ Ss).trans hSl) ?_ ?_ ((CorecBranches.length_subst θ gs).trans hgl)
        ?_ ?_
      · dsimp only [Subst.liftN, Scope.extend]
        rw [← Term.corec_subst,
          ← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as _)]
        exact hasArgs hbs hξ
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst θ hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        exact wfTelescope (hSt j T' ps'' S₀ hj hS₀) hξ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst θ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv θ hg
        have ih := hasType (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
          ((hξ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
        exact ih
    | .etaObs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (u := u) h hq hl hp
        hadm has ht hu hobs, hξ => by
      refine .etaObs h hq hl hp hadm (hasInstanceArgs has hξ) (hasType ht hξ) (hasType hu hξ) ?_
      intro d p q ps' Ξ Θ B ψ hd
      have ih := eqTerm (hobs d p q ps' Ξ Θ B ψ hd) (hξ.append _)
      rw [Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t),
        Term.observation_subst θ D qs ls ps as t, Term.observation_subst θ D qs ls ps as u,
        Term.subst_subst_of (Subst.liftN_subst_of _
          (hd.obsSubst_observation_subst θ D qs ls ps as t))] at ih
      exact ih
  hasArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {ts : Args k Δ ps} {Θ : Telescope k Δ ps} :
      HasArgs sig ctx ts Θ → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        HasArgs sig ctx' (ts.subst θ) (Θ.subst θ)
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .cons (t := t) ht hts, hξ => by
      refine .cons (hasType ht hξ) ?_
      rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
      exact hasArgs hts hξ
  eqArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {ts us : Args k Δ ps} {Θ : Telescope k Δ ps} :
      EqArgs sig ctx ts us Θ → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        EqArgs sig ctx' (ts.subst θ) (us.subst θ)
          (Θ.subst θ)
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .cons (t := t) ht hts, hξ => by
      refine .cons (eqTerm ht hξ) ?_
      rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
      exact eqArgs hts hξ
  hasInstanceArgs {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {as : InstanceArgs k Δ Ψ} {params : Context k Ψ} :
      HasInstanceArgs sig ctx as params → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        HasInstanceArgs sig ctx' (as.subst θ) params
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .var (as := as) (A := A) has ha, hξ => by
      refine .var (hasInstanceArgs has hξ) ?_
      rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
      exact hasType ha hξ
    | .secondOrder (as := as) (Θ := Θ) (A := A) has hB, hξ => by
      refine .secondOrder (hasInstanceArgs has hξ) ?_
      have ih := hasType hB (hξ.append _)
      rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
        Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
      exact ih
  eqInstanceArgs {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ} :
      EqInstanceArgs sig ctx as₁ as₂ params → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        EqInstanceArgs sig ctx' (as₁.subst θ) (as₂.subst θ) params
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .var (as₁ := as) (A := A) has ha, hξ => by
      refine .var (eqInstanceArgs has hξ) ?_
      rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
      exact eqTerm ha hξ
    | .secondOrder (as₁ := as) (Θ := Θ) (A := A) has hB, hξ => by
      refine .secondOrder (eqInstanceArgs has hξ) ?_
      have ih := eqTerm hB (hξ.append _)
      rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
        Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
      exact ih
  wfTelescope {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
      {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
      {κ : Universe k} :
      WfTelescope sig ctx Θ κ → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        WfTelescope sig ctx' (Θ.subst θ) κ
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .cons (A := A) hA hκ hΘ hp, hξ => by
      refine .cons (hasType hA hξ) hκ ?_ hp
      exact wfTelescope hΘ (hξ.var A)
  eqTelescope {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
      {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps}
      {κ : Universe k} :
      EqTelescope sig ctx Θ₁ Θ₂ κ → TypedRen.Lifted sig ctx' @θ @ξ ctx →
        EqTelescope sig ctx' (Θ₁.subst θ) (Θ₂.subst θ) κ
    | .nil hctx, hξ => .nil (wfCtx hctx hξ)
    | .cons (A₁ := A) hA hκ hΘ hp, hξ => by
      refine .cons (eqTerm hA hξ) hκ ?_ hp
      exact eqTelescope hΘ (hξ.var A)

end Sic.Core
