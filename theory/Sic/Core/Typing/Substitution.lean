module

public import Sic.Core.Typing.Lifted
import Sic.Core.Typing.Renaming

/-!
# Substitution of the Typing

The judgments of typing and of equality of annex 14 of RFC 36 are stable under the typed
substitutions of the first order `Σ; Γ ⊢ σ : Δ`: a judgment in the context `Δ` holds, substituted by
`σ`, in the context `Γ`, in which the term that `σ` gives each variable of `Δ` has its type,
substituted.

A substitution of the first order is the substitution of the second order `Subst₀.toSubst`, and the
typed substitutions are a family of substitutions that `Subst.Liftable` accepts: under the binders
of a rule, the term that a typed substitution lifted gives a variable is the term it gives without
the lift, renamed by the weakening, which keeps its type by the stability of the typing under the
typed renamings.

The substitution of the first order gives each second-order variable a variable, so that an
application of it stays one, whose type the rule `(var_X)` gives.
The substitutions of the second order, which give abstractions to these variables, are not typed,
since no rule needs them yet.
-/

@[expose] public section

namespace Sic.Core

/-! ## Typed Substitutions -/

-- ADE: `_⊢ˢʷ_∷_`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- `Σ; Γ ⊢ σ : Δ`: the substitution `σ` of the first order of the scope `Δ` in the scope `Γ` is
typed, the context `Γ` being well formed, the term that `σ` gives each variable of `Δ` having its
type, substituted, and each second-order variable of `Δ` being a variable of `Γ` declared with its
telescope and its type, substituted.
RFC: `\mathsf{subst}_\vdash` -/
structure TypedSubst (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx' : Context k Γ)
    (σ : Subst₀ k Γ Δ) (ctx : Context k Δ) : Prop where
  /-- The context of the substitution is well formed. -/
  wfCtx : WfCtx sig ctx'
  /-- The term of a variable has its type, substituted. -/
  varIn : ∀ {x : Var Δ .var} {A : Term k Δ}, ctx.VarIn x A → HasType sig ctx' (σ x).eta (A.subst₀ σ)
  /-- A second-order variable is a variable declared with its telescope and its type, substituted. -/
  secondOrderIn : ∀ {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)},
    ctx.SecondOrderIn X Θ A →
      ∃ Y, σ X = .var Y ∧ ctx'.SecondOrderIn Y (Θ.subst₀ σ) (A.subst₀ (Subst₀.liftN _ σ))

variable {sig : Signature} {k : Nat}

-- ADE: `⊢ˢʷ∷-sgSubst`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- `Σ; Γ ⊢ [t / x] : (Γ, x : A)`: the substitution of a term of a type for a variable of this type is
typed.
RFC: `\mathsf{subst}_\vdash.\mathsf{single}` -/
theorem TypedSubst.single {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
    (ht : HasType sig ctx t A) : TypedSubst sig ctx (Subst₀.single t) (ctx.var A) :=
  have hctx := contextPresuppositions.hasType ht
  have hB (B : Term k Γ) : (B.rename Ren.weaken).subst₀ (Subst₀.single t) = B :=
    (Term.subst₀_rename_of (σ := Subst₀.single t) (ξ := Ren.weaken) (σ' := Subst₀.id)
      (fun _ => rfl) B).trans (Term.subst₀_id B)
  ⟨hctx, fun
    | .zero => by
      show HasType sig ctx t _
      rw [hB]
      exact ht
    | .succVar hy => by
      show HasType sig ctx (Term.var₀ _) _
      rw [hB]
      exact .var hctx hy,
    fun
    | .succVar (Θ := Θ) (A := B) hX => ⟨_, rfl, by
      rw [(Telescope.subst₀_rename_of (σ := Subst₀.single t) (ξ := Ren.weaken) (σ' := Subst₀.id)
          (fun _ => rfl) Θ).trans (Telescope.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl) Θ),
        (Term.subst₀_rename_of (σ := Subst₀.liftN _ (Subst₀.single t))
          (ξ := Ren.liftN _ Ren.weaken) (σ' := Subst₀.liftN _ Subst₀.id)
          (Subst₀.liftN_rename_of _ fun _ => rfl) B).trans
          (Term.subst₀_id_of (σ := Subst₀.liftN _ Subst₀.id) (Subst₀.liftN_id_of _ fun _ => rfl) B)]
      exact hX⟩⟩

-- ADE: none.
/-- The substitutions of the second order of the typed substitutions of the first order. -/
def TypedSubst.Base (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx' : Context k Γ)
    (θ : Subst k Γ Δ) (ctx : Context k Δ) : Prop :=
  ∃ σ : Subst₀ k Γ Δ, TypedSubst sig ctx' σ ctx ∧ (@θ) = (Subst₀.toSubst σ : Subst k Γ Δ)

-- ADE: `subst-∷∈→⊢∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The term that a typed substitution lifted under variables gives a variable has its type,
substituted, when the context of the substitution is well formed. -/
theorem TypedSubst.Base.varIn {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {x : Var Δ .var} {A : Term k Δ} :
    Subst.Lifted (@TypedSubst.Base sig k) ctx' @θ ctx → ctx.VarIn x A → WfCtx sig ctx' →
      HasType sig ctx' ((Term.var₀ x).subst θ) (A.subst θ)
  | .base ⟨σ, h, rfl⟩, hx, _ => by
    have hσ := h.varIn hx
    rw [Term.subst₀_eq_subst] at hσ
    exact hσ
  | .var B h, .zero, hctx => by
    rw [Term.subst_lift_rename_weaken]
    exact .var hctx .zero
  | .var B h, .succVar hy, hctx => by
    cases hctx with
    | var hB =>
      have ih := TypedSubst.Base.varIn h hy (contextPresuppositions.wfType hB)
      rw [Term.subst_lift_rename_weaken]
      exact stableUnderRenaming.hasType ih (TypedRen.weaken (.var hB))

-- ADE: none.
/-- The typed substitutions give what the stability of the typing asks of a family of
substitutions. -/
theorem TypedSubst.liftable : Subst.Liftable sig (@TypedSubst.Base sig k) where
  wfCtx := fun ⟨_, h, _⟩ => h.wfCtx
  secondOrderIn := fun ⟨σ, h, hθ⟩ hX => by
    cases hθ
    obtain ⟨Y, hY, hYin⟩ := h.secondOrderIn hX
    refine ⟨Y, ?_, ?_⟩
    · show (σ _).eta = _
      rw [hY, Val.eta]
    · rw [Telescope.subst₀_eq_subst, Term.subst₀_liftN_eq_subst] at hYin
      exact hYin
  varIn := TypedSubst.Base.varIn

/-! ## Stability of the Typing -/

-- ADE: `subst-⊢`, `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in
-- `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the typed substitutions of the first order of the
context. -/
structure StableUnderSubstitution : Prop where
  /-- A type, substituted, is a type.
  RFC: `\mathsf{subst}_\vdash.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ}
    {ctx : Context k Δ} {A : Term k Δ},
    WfType sig ctx A → TypedSubst sig ctx' σ ctx → WfType sig ctx' (A.subst₀ σ)
  /-- Equal types, substituted, are equal.
  RFC: `\mathsf{subst}_\vdash.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ}
    {ctx : Context k Δ} {A B : Term k Δ},
    EqType sig ctx A B → TypedSubst sig ctx' σ ctx → EqType sig ctx' (A.subst₀ σ) (B.subst₀ σ)
  /-- A term of a type, substituted, is a term of the type, substituted.
  RFC: `\mathsf{subst}_\vdash.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ}
    {ctx : Context k Δ} {t A : Term k Δ},
    HasType sig ctx t A → TypedSubst sig ctx' σ ctx → HasType sig ctx' (t.subst₀ σ) (A.subst₀ σ)
  /-- Equal terms of a type, substituted, are equal at the type, substituted.
  RFC: `\mathsf{subst}_\vdash.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ}
    {ctx : Context k Δ} {t u A : Term k Δ},
    EqTerm sig ctx t u A → TypedSubst sig ctx' σ ctx →
      EqTerm sig ctx' (t.subst₀ σ) (u.subst₀ σ) (A.subst₀ σ)
  /-- Arguments of a telescope, substituted, are arguments of the telescope, substituted.
  RFC: `\mathsf{subst}_\vdash.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {ts : Args k Δ ps}
    {Θ : Telescope k Δ ps},
    HasArgs sig ctx ts Θ → TypedSubst sig ctx' σ ctx →
      HasArgs sig ctx' (ts.subst₀ σ) (Θ.subst₀ σ)
  /-- Equal arguments of a telescope, substituted, are equal arguments of the telescope,
  substituted.
  RFC: `\mathsf{subst}_\vdash.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {ts us : Args k Δ ps}
    {Θ : Telescope k Δ ps},
    EqArgs sig ctx ts us Θ → TypedSubst sig ctx' σ ctx →
      EqArgs sig ctx' (ts.subst₀ σ) (us.subst₀ σ) (Θ.subst₀ σ)
  /-- Arguments of an instance, substituted, are arguments of its parameters.
  RFC: `\mathsf{subst}_\vdash.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
    {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {as : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    HasInstanceArgs sig ctx as params → TypedSubst sig ctx' σ ctx →
      HasInstanceArgs sig ctx' (as.subst₀ σ) params
  /-- Equal arguments of instances, substituted, are equal arguments of the parameters.
  RFC: `\mathsf{subst}_\vdash.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {ctx' : Context k Γ}
    {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    EqInstanceArgs sig ctx as₁ as₂ params → TypedSubst sig ctx' σ ctx →
      EqInstanceArgs sig ctx' (as₁.subst₀ σ) (as₂.subst₀ σ) params
  /-- A telescope in a sort, substituted, is in the sort.
  RFC: `\mathsf{subst}_\vdash.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
    {κ : Universe k},
    WfTelescope sig ctx Θ κ → TypedSubst sig ctx' σ ctx → WfTelescope sig ctx' (Θ.subst₀ σ) κ
  /-- A telescope in sorts, substituted, is in the sorts.
  RFC: `\mathsf{subst}_\vdash.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
    {κs : List (Universe k)} {l : Level k},
    WfTelescopeSorts sig ctx Θ κs l → TypedSubst sig ctx' σ ctx →
      WfTelescopeSorts sig ctx' (Θ.subst₀ σ) κs l
  /-- Equal telescopes in a sort, substituted, are equal in the sort.
  RFC: `\mathsf{subst}_\vdash.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps}
    {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → TypedSubst sig ctx' σ ctx →
      EqTelescope sig ctx' (Θ₁.subst₀ σ) (Θ₂.subst₀ σ) κ

-- ADE: `subst-⊢`, `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in
-- `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the typed substitutions of the first order of the
context.
RFC: `\mathsf{subst}_\vdash.A`
RFC: `\mathsf{subst}_\vdash.A_\equiv`
RFC: `\mathsf{subst}_\vdash.t`
RFC: `\mathsf{subst}_\vdash.t_\equiv`
RFC: `\mathsf{subst}_\vdash.\bar t`
RFC: `\mathsf{subst}_\vdash.\bar t_\equiv`
RFC: `\mathsf{subst}_\vdash.\bar a`
RFC: `\mathsf{subst}_\vdash.\bar a_\equiv`
RFC: `\mathsf{subst}_\vdash.\Theta`
RFC: `\mathsf{subst}_\vdash.\Theta_{\bar\kappa}`
RFC: `\mathsf{subst}_\vdash.\Theta_\equiv` -/
theorem stableUnderSubstitution : StableUnderSubstitution :=
  ⟨fun h hσ => by
      rw [Term.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.wfType h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Term.subst₀_eq_subst, Term.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.eqType h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Term.subst₀_eq_subst, Term.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.hasType h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Term.subst₀_eq_subst, Term.subst₀_eq_subst, Term.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.eqTerm h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Args.subst₀_eq_subst, Telescope.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.hasArgs h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Args.subst₀_eq_subst, Args.subst₀_eq_subst, Telescope.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.eqArgs h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [InstanceArgs.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.hasInstanceArgs h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [InstanceArgs.subst₀_eq_subst, InstanceArgs.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.eqInstanceArgs h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Telescope.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.wfTelescope h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Telescope.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.wfTelescopeSorts h (.base ⟨_, hσ, rfl⟩),
    fun h hσ => by
      rw [Telescope.subst₀_eq_subst, Telescope.subst₀_eq_subst]
      exact TypedSubst.liftable.stable.eqTelescope h (.base ⟨_, hσ, rfl⟩)⟩

end Sic.Core
