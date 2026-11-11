module

public import Sic.Core.Typing
import Sic.Core.Substitution.Composition

/-!
# Lifted Substitutions of the Typing

The judgments of typing and of equality of annex 14 of RFC 36 are stable under the substitutions of
the second order that a family of typed substitutions gives and that the rules lift under their
binders: a judgment in a context, substituted, holds in the context of the substitution.
The renamings and the substitutions of the first order are two such families, whose stability
follows from this one, so that the proof by cases on the rules is written once.

A family gives the context of each of its substitutions well formed, the image of each second-order
variable a variable declared with its telescope and its type, substituted, and the image of each
variable a term of its type, substituted, in the context lifted when it is well formed.
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.
Under the binders of a rule, the substitution is lifted, and the context extended by the type
substituted is well formed: the relation `Subst.Lifted` lifts a substitution under variables without
this condition, and the clause of the judgment `Σ ⊢ Γ` builds the context extended at the leaves of
the derivation, from the derivation of the context extended, which the rule `(ctx_x)` gives with a
derivation of its type, a subderivation substituted by the substitution before the lift.

ADE prove the weakening and the substitution apart, each by cases on the rules, and build the
context extended from the derivation of the type, which the rules of a binder do not always have, by
a well-founded recursion on the sizes of the derivations; here the recursion is structural.
-/

@[expose] public section

namespace Sic.Core

variable {sig : Signature} {k : Nat}

-- ADE: `_∷_⊇_`, in `Definition/Typed/Weakening.agda`, whose constructor `lift` it has.
/-- A substitution `θ` of the family `Base`, lifted under variables, whose contexts are extended by
a type and by the type substituted, without the condition that the context extended be well formed,
which the leaves of a derivation in the context extended give.
The substitution is lifted as the substitutions of the rules are, so that the judgments under the
binders of a rule hold at the substitution of the rule without conversion. -/
inductive Subst.Lifted (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) :
    {Γ Δ : Scope} → Context k Γ → Subst k Γ Δ → Context k Δ → Prop where
  /-- A substitution of the family. -/
  | base {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      (h : Base ctx' @θ ctx) : Lifted @Base ctx' @θ ctx
  /-- A lifted substitution, lifted under a variable. -/
  | var {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      (A : Term k Δ) (h : Lifted @Base ctx' @θ ctx) :
      Lifted @Base (ctx'.var (A.subst θ)) (Subst.lift θ) (ctx.var A)

-- ADE: none.
/-- What a family `Base` of substitutions gives for the typing to be stable under them. -/
structure Subst.Liftable (sig : Signature)
    (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) : Prop where
  /-- The context of a substitution of the family is well formed. -/
  wfCtx : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ},
    Base ctx' @θ ctx → WfCtx sig ctx'
  /-- The image of a second-order variable is the abstraction of a variable declared with its
  telescope and its type, substituted. -/
  secondOrderIn : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {ps : List Parameter} {ψ : ResultOwnership ps.length} {X : Var Δ (.secondOrder ps ψ)}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)},
    Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A →
      ∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ))
  /-- The image of a variable by a lifted substitution is a term of its type, substituted, when the
  context of the substitution is well formed. -/
  varIn : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {x : Var Δ .var} {A : Term k Δ},
    Subst.Lifted @Base ctx' @θ ctx → ctx.VarIn x A → WfCtx sig ctx' →
      HasType sig ctx' ((Term.var₀ x).subst θ) (A.subst θ)

variable {Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop}

/-- A lifted substitution, lifted under the variables of a telescope. -/
theorem Subst.Lifted.append {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → Lifted @Base ctx' @θ ctx →
      Lifted @Base (ctx'.append (Θ.subst θ)) (Subst.liftN ps.length θ) (ctx.append Θ)
  | [], .nil, h => h
  | _ :: _, .cons _ _ A Θ, h => Subst.Lifted.append Θ (h.var A)

-- ADE: none.
/-- The image of a second-order variable by a lifted substitution is the abstraction of a variable
declared with its telescope and its type, substituted. -/
theorem Subst.Lifted.secondOrderIn {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} :
    Lifted @Base ctx' @θ ctx → Subst.Liftable sig @Base → ctx.SecondOrderIn X Θ A →
      ∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ))
  | .base h, hB, hX => hB.secondOrderIn h hX
  | .var B h, hB, .succVar hX => by
    obtain ⟨Y, hY, hYin⟩ := h.secondOrderIn hB hX
    refine ⟨Y.succ, ?_, ?_⟩
    · show Term.rename _ _ = _
      dsimp only
      rw [hY]
      exact Var.eta_rename Ren.weaken Y
    · rw [Telescope.subst_lift_rename_weaken, Term.subst_liftN_lift_rename_weaken]
      exact .succVar hYin

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`, and `subst-⊢`,
-- `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the lifted substitutions of a family. -/
structure Subst.Stable (sig : Signature)
    (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) : Prop where
  /-- A type, substituted, is a type. -/
  wfType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {A : Term k Δ},
    WfType sig ctx A → Lifted @Base ctx' @θ ctx → WfType sig ctx' (A.subst θ)
  /-- Equal types, substituted, are equal. -/
  eqType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {A B : Term k Δ},
    EqType sig ctx A B → Lifted @Base ctx' @θ ctx → EqType sig ctx' (A.subst θ) (B.subst θ)
  /-- A term of a type, substituted, is a term of the type, substituted. -/
  hasType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {t A : Term k Δ},
    HasType sig ctx t A → Lifted @Base ctx' @θ ctx → HasType sig ctx' (t.subst θ) (A.subst θ)
  /-- Equal terms of a type, substituted, are equal at the type, substituted. -/
  eqTerm : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {t u A : Term k Δ},
    EqTerm sig ctx t u A → Lifted @Base ctx' @θ ctx →
      EqTerm sig ctx' (t.subst θ) (u.subst θ) (A.subst θ)
  /-- Arguments of a telescope, substituted, are arguments of the telescope, substituted. -/
  hasArgs : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ts : Args k Δ ps} {Θ : Telescope k Δ ps},
    HasArgs sig ctx ts Θ → Lifted @Base ctx' @θ ctx → HasArgs sig ctx' (ts.subst θ) (Θ.subst θ)
  /-- Equal arguments of a telescope, substituted, are equal arguments of the telescope,
  substituted. -/
  eqArgs : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ts us : Args k Δ ps} {Θ : Telescope k Δ ps},
    EqArgs sig ctx ts us Θ → Lifted @Base ctx' @θ ctx →
      EqArgs sig ctx' (ts.subst θ) (us.subst θ) (Θ.subst θ)
  /-- Arguments of an instance, substituted, are arguments of its parameters. -/
  hasInstanceArgs : ∀ {Γ Δ Ψ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {as : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    HasInstanceArgs sig ctx as params → Lifted @Base ctx' @θ ctx →
      HasInstanceArgs sig ctx' (as.subst θ) params
  /-- Equal arguments of instances, substituted, are equal arguments of the parameters. -/
  eqInstanceArgs : ∀ {Γ Δ Ψ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    EqInstanceArgs sig ctx as₁ as₂ params → Lifted @Base ctx' @θ ctx →
      EqInstanceArgs sig ctx' (as₁.subst θ) (as₂.subst θ) params
  /-- A telescope in a sort, substituted, is in the sort. -/
  wfTelescope : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κ : Universe k},
    WfTelescope sig ctx Θ κ → Lifted @Base ctx' @θ ctx → WfTelescope sig ctx' (Θ.subst θ) κ
  /-- A telescope in sorts, substituted, is in the sorts. -/
  wfTelescopeSorts : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
    {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κs : List (Universe k)}
    {l : Level k}, WfTelescopeSorts sig ctx Θ κs l → Lifted @Base ctx' @θ ctx →
      WfTelescopeSorts sig ctx' (Θ.subst θ) κs l
  /-- Equal telescopes in a sort, substituted, are equal in the sort. -/
  eqTelescope : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → Lifted @Base ctx' @θ ctx →
      EqTelescope sig ctx' (Θ₁.subst θ) (Θ₂.subst θ) κ

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`, and `subst-⊢`,
-- `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the lifted substitutions of a family that gives what
`Subst.Liftable` says. -/
theorem Subst.Liftable.stable (hB : Subst.Liftable sig @Base) : Subst.Stable sig @Base :=
  ⟨wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope,
    wfTelescopeSorts, eqTelescope⟩
where
  wfCtx {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
      {ctx : Context k Δ} : WfCtx sig ctx → Subst.Lifted @Base ctx' @θ ctx → WfCtx sig ctx'
    | _, .base hθ => hB.wfCtx hθ
    | .var hA, .var _ hθ => .var (wfType hA hθ)
  wfType {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
      {ctx : Context k Δ} {A : Term k Δ} :
      WfType sig ctx A → Subst.Lifted @Base ctx' @θ ctx →
        WfType sig ctx' (A.subst θ)
    | .univType h, hθ => .univType (hasType h hθ)
    | .propType h, hθ => .propType (hasType h hθ)
  eqType {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
      {ctx : Context k Δ} {A B : Term k Δ} :
      EqType sig ctx A B → Subst.Lifted @Base ctx' @θ ctx →
        EqType sig ctx' (A.subst θ) (B.subst θ)
    | .refl h, hθ => .refl (wfType h hθ)
    | .symm h, hθ => .symm (eqType h hθ)
    | .trans h₁ h₂, hθ => .trans (eqType h₁ hθ) (eqType h₂ hθ)
    | .univType h, hθ => .univType (eqTerm h hθ)
    | .propType h, hθ => .propType (eqTerm h hθ)
  hasType {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
      {ctx : Context k Δ} {t A : Term k Δ} :
      HasType sig ctx t A → Subst.Lifted @Base ctx' @θ ctx →
        HasType sig ctx' (t.subst θ) (A.subst θ)
    | .var hctx hx, hθ => hB.varIn hθ hx (wfCtx hctx hθ)
    | .secondOrder hX hts, hθ => by
      obtain ⟨Y, hY, hYin⟩ := hθ.secondOrderIn hB hX
      rw [Term.var_subst_of hY, Term.instantiate_subst]
      exact .secondOrder hYin (hasArgs hts hθ)
    | .const hctx h hq hl hp, hθ => by
      rw [Signature.instanceType, Term.weakenClosed_subst]
      exact .const (wfCtx hctx hθ) h hq hl hp
    | .univ hctx, hθ => .univ (wfCtx hctx hθ)
    | .prop hctx, hθ => .prop (wfCtx hctx hθ)
    | .inst h hq hl hp hadm has, hθ => .inst h hq hl hp hadm (hasInstanceArgs has hθ)
    | .ctor h hc hq hl hp hadm has hts, hθ => by
      rw [Term.ctor_subst]
      refine .ctor h hc hq hl hp hadm (hasInstanceArgs has hθ) ?_
      rw [← Constructor.fieldsAt_subst]
      exact hasArgs hts hθ
    | .recursor (as := as) (t := t) (Cs := Cs) (us := us) (C := C) h hq hl hp hadm has ht hh hC hCl
        hCs hCt hul hus hut hκ, hθ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t _)]
      refine .recursor h hq hl hp hadm (hasInstanceArgs has hθ) (hasType ht hθ) hh
        (Motives.get_subst _ hC) ((Motives.length_subst _ Cs).trans hCl) ?_ ?_
        ((Branches.length_subst _ us).trans hul) ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst _ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hθ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst _ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv _ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv _ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hθ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst _ C₀] at ih
        exact ih
    | .obs (as := as) (t := t) (ls := ls) (qs := qs) (ps := ps) (D := D) (Θ := Θ) (B := B) (bs := bs)
        h hq hl hp hadm hd has ht hbs, hθ => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
        (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst]
      refine .obs h hq hl hp hadm hd (hasInstanceArgs has hθ) (hasType ht hθ) ?_
      rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
      exact hasArgs hbs hθ
    | .corec (r := r) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs) (ss := ss)
        h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt, hθ => by
      rw [Term.corec_subst]
      refine .corec h hq hl hp hadm hpre (hasInstanceArgs has hθ) hh (States.get_subst _ hS)
        (hasArgs hss hθ) ((States.length_subst _ Ss).trans hSl) ?_ ?_
        ((CorecBranches.length_subst _ gs).trans hgl) ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst _ hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        rw [States.sorts_subst]
        exact wfTelescopeSorts (hSt j T' ps'' S₀ hj hS₀) hθ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst _ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv _ hg
        have ih := hasType (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
          ((hθ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
          States.subst_liftN_rename_weakenN] at ih
        rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
        exact ih
    | .conv ht h, hθ => .conv (hasType ht hθ) (eqType h hθ)
  eqTerm {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
      {ctx : Context k Δ} {t u A : Term k Δ} :
      EqTerm sig ctx t u A → Subst.Lifted @Base ctx' @θ ctx →
        EqTerm sig ctx' (t.subst θ) (u.subst θ)
          (A.subst θ)
    | .refl h, hθ => .refl (hasType h hθ)
    | .symm h, hθ => .symm (eqTerm h hθ)
    | .trans h₁ h₂, hθ => .trans (eqTerm h₁ hθ) (eqTerm h₂ hθ)
    | .conv h hA, hθ => .conv (eqTerm h hθ) (eqType hA hθ)
    | .irr ht hu hA, hθ => .irr (hasType ht hθ) (hasType hu hθ) (hasType hA hθ)
    | .secondOrder hX hts, hθ => by
      obtain ⟨Y, hY, hYin⟩ := hθ.secondOrderIn hB hX
      rw [Term.var_subst_of hY, Term.var_subst_of hY, Term.instantiate_subst]
      exact .secondOrder hYin (eqArgs hts hθ)
    | .delta hctx h hq hl hp, hθ => by
      rw [Signature.instanceType, Signature.instanceType, Term.weakenClosed_subst,
        Term.weakenClosed_subst]
      exact .delta (wfCtx hctx hθ) h hq hl hp
    | .const hctx h hq hl₁ hl₂ hp hls, hθ => by
      rw [Signature.instanceType, Term.weakenClosed_subst]
      exact .const (wfCtx hctx hθ) h hq hl₁ hl₂ hp hls
    | .univ hctx hl, hθ => .univ (wfCtx hctx hθ) hl
    | .prop hctx hl, hθ => .prop (wfCtx hctx hθ) hl
    | .inst h hq hl₁ hl₂ hp hadm has hls, hθ =>
      .inst h hq hl₁ hl₂ hp hadm (eqInstanceArgs has hθ) hls
    | .ctor h hc hq hl₁ hl₂ hp hadm has hls hts, hθ => by
      rw [Term.ctor_subst, Term.ctor_subst]
      refine .ctor h hc hq hl₁ hl₂ hp hadm (eqInstanceArgs has hθ) hls ?_
      rw [← Constructor.fieldsAt_subst]
      exact eqArgs hts hθ
    | .recursor (as₁ := as) (t₁ := t) (Cs₁ := Cs₁) (Cs₂ := Cs₂) (us₁ := us₁) (us₂ := us₂)
        h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes hut
        hκ, hθ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
      refine .recursor h hq hl₁ hl₂ hp hadm (eqInstanceArgs has hθ) hls (eqTerm ht hθ) hh
        (Motives.get_subst θ hC) ((Motives.length_subst θ Cs₁).trans hCl₁)
        ((Motives.length_subst θ Cs₂).trans hCl₂) ?_ ?_ ?_ ((Branches.length_subst θ us₁).trans hul₁)
        ((Branches.length_subst θ us₂).trans hul₂) ?_ ?_
        (by funext i; rw [Branches.grades_subst, Branches.grades_subst, hes]) ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs₁ j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs₂ j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C₁' C₂' hj h₁ h₂
        obtain ⟨C₁₀, hC₁₀, rfl⟩ := Motives.get_subst_inv θ h₁
        obtain ⟨C₂₀, hC₂₀, rfl⟩ := Motives.get_subst_inv θ h₂
        have ih := eqTerm (hCt j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀) (hθ.var _)
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
          ((hθ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .obs (as₁ := as) (t₁ := t) (ls₁ := ls) (qs := qs) (ps := ps) (D := D) (bs₁ := bs₁)
        (bs₂ := bs₂) h hq hl₁ hl₂ hp hadm hd has hls ht hbs, hθ => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
        (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst, Term.obs_subst]
      refine .obs h hq hl₁ hl₂ hp hadm hd (eqInstanceArgs has hθ) hls (eqTerm ht hθ) ?_
      rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
      exact eqArgs hbs hθ
    | .corec (r := r) (qs := qs) (ls₁ := ls) (ps := ps) (as₁ := as) (Ss₁ := Ss₁) (Ss₂ := Ss₂)
        (gs₁ := gs₁) (gs₂ := gs₂) (ss₁ := ss₁) (ss₂ := ss₂) h hq hl₁ hl₂ hp hadm hpre has hls
        hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂ hgs hgt, hθ => by
      rw [Term.corec_subst, Term.corec_subst]
      refine .corec h hq hl₁ hl₂ hp hadm hpre (eqInstanceArgs has hθ) hls hh
        (States.get_subst θ hS₁) (States.get_subst θ hS₂) (eqArgs hss hθ)
        ((States.length_subst θ Ss₁).trans hSl₁) ((States.length_subst θ Ss₂).trans hSl₂) ?_
        (fun j => by rw [States.sorts_subst, States.sorts_subst]; exact hSk j) ?_ ?_
        ((CorecBranches.length_subst θ gs₁).trans hgl₁) ((CorecBranches.length_subst θ gs₂).trans hgl₂)
        ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S₁', S₂', h₁, h₂⟩ := hSs j T' hj
        exact ⟨ps'', _, _, States.get_subst θ h₁, States.get_subst θ h₂⟩
      · intro j T' ps'' S₁' hj h₁
        obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_subst_inv θ h₁
        rw [States.sorts_subst]
        exact wfTelescopeSorts (hSt j T' ps'' S₁₀ hj hS₁₀) hθ
      · intro j T' ps'' S₁' S₂' hj h₁ h₂
        obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_subst_inv θ h₁
        obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_subst_inv θ h₂
        rw [States.sorts_subst]
        exact eqTelescope (hSe j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀) hθ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, _, CorecBranches.get_subst θ hg₁, CorecBranches.get_subst θ hg₂⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₁₀, hg₁₀, rfl⟩ := CorecBranches.get_subst_inv θ hg₁
        obtain ⟨g₂₀, hg₂₀, rfl⟩ := CorecBranches.get_subst_inv θ hg₂
        have ih := eqTerm (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀)
          ((hθ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
          States.subst_liftN_rename_weakenN] at ih
        rw [Telescope.subst_subst_of
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''))] at ih
        exact ih
    | .iota (r := r) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (Cs := Cs) (us := us)
        h hc hq hl hp hadm has hts hi hC hu hCl hCs hCt hul hus hut hκ,
        hθ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ θ), Term.instantiate_subst,
        Term.instantiate_subst, Args.subst_liftN_rename_weakenN,
        Args.results_subst θ (f' := fun D' t => .recursor r D' qs ls ps (as.subst θ) t (Cs.subst θ)
          (us.subst θ)) (fun _ _ => rfl)]
      show EqTerm sig ctx' (.recursor _ _ _ _ _ _ (Term.subst θ (.ctor _ _ _ _ _ _ _)) _ _) _ _
      rw [Term.ctor_subst]
      refine .iota h hc hq hl hp hadm (hasInstanceArgs has hθ) ?_ hi (Motives.get_subst θ hC)
        (Branches.get_subst θ hu) ((Motives.length_subst θ Cs).trans hCl) ?_ ?_
        ((Branches.length_subst θ us).trans hul) ?_ ?_ hκ
      · rw [← Constructor.fieldsAt_subst]
        exact hasArgs hts hθ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hθ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv θ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hθ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .etaCtor (D := D) (T := T) (con := con) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t)
        (e := e) (Cs := Cs) (us := us) (i := i) h hc hq hl hp hadm hr has ht he hi hC hu hCl
        hCs hCt hul hus hut hκ, hθ => by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ),
        Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
      have hu' := Branches.get_subst θ hu
      rw [show ((e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).subst
            (Subst.liftN 0 (Subst.liftN _ θ)) :
              Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)) =
          (e.subst (Subst.lift θ)).atCtor T.name qs ls ps (as.subst θ) con.name
            (con.params (.ofLists qs ps hq hp)) from Term.atCtor_subst θ e _ _ _ _ _ _ _] at hu'
      have he' := hasType he (hθ.var (.inst D qs ls ps as))
      refine .etaCtor h hc hq hl hp hadm hr (hasInstanceArgs has hθ) (hasType ht hθ) he' hi (Motives.get_subst θ hC) hu'
        ((Motives.length_subst θ Cs).trans hCl) ?_ ?_ ((Branches.length_subst θ us).trans hul) ?_ ?_ hκ
      · intro j T' hj
        obtain ⟨C', hC'⟩ := hCs j T' hj
        exact ⟨_, Motives.get_subst θ hC'⟩
      · intro j T' C' hj hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        have ih := hasType (hCt j T' C₀ hj hC₀) (hθ.var _)
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst θ hu⟩
      · intro i j T' con C' R u hi hC' hR hu
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_subst_inv θ hR
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
        have ih := hasType (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ((hθ.append _).append _)
        rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
        exact ih
    | .beta (r := r) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (Ss := Ss) (gs := gs)
        (ss := ss) h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt,
        hθ => by
      rw [Term.obs_subst, Term.corec_subst, Term.observed_subst, Term.instantiate_subst, Term.instantiate_subst,
        Args.subst_liftN_rename_weakenN, Term.instantiate_subst, Term.subst_subst_of
          (Subst.liftN_subst_of _ (hd.obsSubst_observation_subst θ D qs ls ps as _)),
        Term.corec_subst]
      refine .beta h hq hl hp hadm hpre (hasInstanceArgs has hθ) hh (States.get_subst θ hS)
        (hasArgs hss hθ) hi hd (CorecBranches.get_subst θ hg) ?_
        ((States.length_subst θ Ss).trans hSl) ?_ ?_ ((CorecBranches.length_subst θ gs).trans hgl)
        ?_ ?_
      · dsimp only [Subst.liftN, Scope.extend]
        rw [← Term.corec_subst,
          ← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as _)]
        exact hasArgs hbs hθ
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst θ hS'⟩
      · intro j T' ps'' S' hj hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        rw [States.sorts_subst]
        exact wfTelescopeSorts (hSt j T' ps'' S₀ hj hS₀) hθ
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst θ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv θ hg
        have ih := hasType (hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
          ((hθ.append S₀).append _)
        dsimp only [Scope.extend] at ih
        rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
          States.subst_liftN_rename_weakenN] at ih
        rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
          Term.subst_subst_of (Subst.liftN_subst_of _
            (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
        exact ih
    | .etaObs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (u := u) h hq hl hp
        hadm hr has ht hu hobs, hθ => by
      refine .etaObs h hq hl hp hadm hr (hasInstanceArgs has hθ) (hasType ht hθ) (hasType hu hθ) ?_
      intro d p q ps' Ξ Θ B ψ hd
      have ih := eqTerm (hobs d p q ps' Ξ Θ B ψ hd) (hθ.append _)
      rw [Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t),
        Term.observation_subst θ D qs ls ps as t, Term.observation_subst θ D qs ls ps as u,
        Term.subst_subst_of (Subst.liftN_subst_of _
          (hd.obsSubst_observation_subst θ D qs ls ps as t))] at ih
      exact ih
  hasArgs {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ctx : Context k Δ} {ts : Args k Δ ps} {Θ : Telescope k Δ ps} :
      HasArgs sig ctx ts Θ → Subst.Lifted @Base ctx' @θ ctx →
        HasArgs sig ctx' (ts.subst θ) (Θ.subst θ)
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .cons (t := t) ht hts, hθ => by
      refine .cons (hasType ht hθ) ?_
      rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
      exact hasArgs hts hθ
  eqArgs {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ctx : Context k Δ} {ts us : Args k Δ ps} {Θ : Telescope k Δ ps} :
      EqArgs sig ctx ts us Θ → Subst.Lifted @Base ctx' @θ ctx →
        EqArgs sig ctx' (ts.subst θ) (us.subst θ)
          (Θ.subst θ)
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .cons (t := t) ht hts, hθ => by
      refine .cons (eqTerm ht hθ) ?_
      rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
      exact eqArgs hts hθ
  hasInstanceArgs {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ctx : Context k Δ} {as : InstanceArgs k Δ Ψ} {params : Context k Ψ} :
      HasInstanceArgs sig ctx as params → Subst.Lifted @Base ctx' @θ ctx →
        HasInstanceArgs sig ctx' (as.subst θ) params
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .var (as := as) (A := A) has ha, hθ => by
      refine .var (hasInstanceArgs has hθ) ?_
      rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
      exact hasType ha hθ
    | .secondOrder (as := as) (Θ := Θ) (A := A) has hB, hθ => by
      refine .secondOrder (hasInstanceArgs has hθ) ?_
      have ih := hasType hB (hθ.append _)
      rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
        Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
      exact ih
  eqInstanceArgs {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
      {θ : Subst k Γ Δ} {ctx : Context k Δ} {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ} :
      EqInstanceArgs sig ctx as₁ as₂ params → Subst.Lifted @Base ctx' @θ ctx →
        EqInstanceArgs sig ctx' (as₁.subst θ) (as₂.subst θ) params
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .var (as₁ := as) (A := A) has ha, hθ => by
      refine .var (eqInstanceArgs has hθ) ?_
      rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
      exact eqTerm ha hθ
    | .secondOrder (as₁ := as) (Θ := Θ) (A := A) has hB, hθ => by
      refine .secondOrder (eqInstanceArgs has hθ) ?_
      have ih := eqTerm hB (hθ.append _)
      rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
        Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
      exact ih
  wfTelescope {Γ Δ : Scope} {ps : List Parameter}
      {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
      {κ : Universe k} :
      WfTelescope sig ctx Θ κ → Subst.Lifted @Base ctx' @θ ctx →
        WfTelescope sig ctx' (Θ.subst θ) κ
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .cons (A := A) hA hκ hΘ hp, hθ => by
      refine .cons (hasType hA hθ) hκ ?_ hp
      exact wfTelescope hΘ (hθ.var A)
  wfTelescopeSorts {Γ Δ : Scope} {ps : List Parameter}
      {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
      {κs : List (Universe k)} {l : Level k} :
      WfTelescopeSorts sig ctx Θ κs l → Subst.Lifted @Base ctx' @θ ctx →
        WfTelescopeSorts sig ctx' (Θ.subst θ) κs l
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .cons (A := A) hA hl hΘ hp, hθ => by
      refine .cons (hasType hA hθ) hl ?_ hp
      exact wfTelescopeSorts hΘ (hθ.var A)
  eqTelescope {Γ Δ : Scope} {ps : List Parameter}
      {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps}
      {κ : Universe k} :
      EqTelescope sig ctx Θ₁ Θ₂ κ → Subst.Lifted @Base ctx' @θ ctx →
        EqTelescope sig ctx' (Θ₁.subst θ) (Θ₂.subst θ) κ
    | .nil hctx, hθ => .nil (wfCtx hctx hθ)
    | .cons (A₁ := A) hA hκ hΘ hp, hθ => by
      refine .cons (eqTerm hA hθ) hκ ?_ hp
      exact eqTelescope hΘ (hθ.var A)
end Sic.Core
