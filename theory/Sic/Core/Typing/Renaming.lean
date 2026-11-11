module

public import Sic.Core.Typing.Lifted

/-!
# Renaming of the Typing

The judgments of typing and of equality of annex 14 of RFC 36 are stable under the typed renamings
`Σ; Γ ⊢ ξ : Δ`: a judgment in the context `Δ` holds, renamed by `ξ`, in the context `Γ`, whose
declarations give each variable of `Δ` its type, renamed.

A renaming is the substitution of the second order `Ren.toSubst`, and the typed renamings are a
family of substitutions that `Subst.Liftable` accepts: a typed renaming lifted under variables gives
each variable a variable, declared with its type, substituted, so that the rule `(var_x)` types it.

ADE weaken by the renamings that keep the order of the variables, `ρ ∷ Δ ⊇ Γ`; here the renamings are
all those that the context types.
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

variable {sig : Signature} {k : Nat}

-- ADE: none.
/-- The substitutions of the second order of the typed renamings, which give each variable the
abstraction of its image. -/
def TypedRen.Base (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx' : Context k Γ) (θ : Subst k Γ Δ)
    (ctx : Context k Δ) : Prop :=
  ∃ ξ : Ren Γ Δ, TypedRen sig ctx' ξ ctx ∧ ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)

-- ADE: `wkIndex`, in `Definition/Typed/Weakening.agda`.
/-- A typed renaming lifted under variables gives each variable the abstraction of a variable,
declared with its type, substituted. -/
theorem TypedRen.Base.lifted {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} :
    Subst.Lifted (@TypedRen.Base sig k) ctx' @θ ctx →
      ∃ ξ : Ren Γ Δ, (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) ∧
        ∀ {x : Var Δ .var} {A : Term k Δ}, ctx.VarIn x A → ctx'.VarIn (ξ x) (A.subst θ)
  | .base ⟨ξ, h, hθ⟩ => ⟨ξ, hθ, fun hx => by rw [← Term.rename_eq_subst_of hθ]; exact h.varIn hx⟩
  | .var B h =>
    let ⟨ξ, hθ, hv⟩ := TypedRen.Base.lifted h
    ⟨Ren.lift ξ, Subst.lift_eta_of hθ, fun
      | .zero => by rw [Term.subst_lift_rename_weaken]; exact .zero
      | .succVar hx => by rw [Term.subst_lift_rename_weaken]; exact .succVar (hv hx)⟩

-- ADE: none.
/-- The typed renamings give what the stability of the typing asks of a family of substitutions. -/
theorem TypedRen.liftable : Subst.Liftable sig (@TypedRen.Base sig k) where
  wfCtx := fun ⟨_, h, _⟩ => h.wfCtx
  secondOrderIn := fun ⟨ξ, h, hθ⟩ hX => ⟨ξ _, hθ _, by
    rw [← Telescope.rename_eq_subst_of hθ, ← Term.rename_eq_subst_of (Subst.liftN_eta_of _ hθ)]
    exact h.secondOrderIn hX⟩
  varIn := fun {_ _ _ _ _ x _} hθ hx hctx => by
    obtain ⟨ξ, hθ, hv⟩ := TypedRen.Base.lifted hθ
    rw [Term.var_subst_of (hθ x)]
    exact .var hctx (hv hx)

-- ADE: `step`, in `Definition/Typed/Weakening.agda`.
/-- The renaming of a context in the context extended by a variable is typed, when the context
extended is well formed. -/
theorem TypedRen.weaken {Γ : Scope} {ctx : Context k Γ} {B : Term k Γ} (h : WfCtx sig (ctx.var B)) :
    TypedRen sig (ctx.var B) Ren.weaken ctx :=
  ⟨h, .succVar, .succVar⟩

-- ADE: `_•ₜ_`, in `Definition/Typed/Weakening.agda`.
/-- Two typed renamings compose. -/
theorem TypedRen.comp {Γ Δ Ξ : Scope} {ctx₁ : Context k Γ} {ctx₂ : Context k Δ}
    {ctx₃ : Context k Ξ} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ} (h₁ : TypedRen sig ctx₁ ξ₁ ctx₂)
    (h₂ : TypedRen sig ctx₂ ξ₂ ctx₃) : TypedRen sig ctx₁ (fun x => ξ₁ (ξ₂ x)) ctx₃ :=
  ⟨h₁.wfCtx, fun hx => by
    rw [← Term.rename_rename_of (ξ₁ := ξ₁) (ξ₂ := ξ₂) (fun _ => rfl)]
    exact h₁.varIn (h₂.varIn hx),
    fun hX => by
    rw [← Telescope.rename_rename_of (ξ₁ := ξ₁) (ξ₂ := ξ₂) (fun _ => rfl),
      ← Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := ξ₁) (ξ₂ := ξ₂) (fun _ => rfl))]
    exact h₁.secondOrderIn (h₂.secondOrderIn hX)⟩

-- ADE: `lift`, the constructor of `_∷_⊇_`, in `Definition/Typed/Weakening.agda`.
/-- A typed renaming lifted under a variable, whose type, renamed, is a type. -/
theorem TypedRen.lift {Γ Δ : Scope} {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ}
    {A : Term k Δ} (h : TypedRen sig ctx' ξ ctx) (hA : WfType sig ctx' (A.rename ξ)) :
    TypedRen sig (ctx'.var (A.rename ξ)) (Ren.lift ξ) (ctx.var A) :=
  ⟨.var hA, fun
    | .zero => by
      rw [Term.rename_rename_of (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
        (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl),
        ← Term.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := ξ) (fun _ => rfl)]
      exact .zero
    | .succVar hx => by
      rw [Term.rename_rename_of (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
        (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl),
        ← Term.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := ξ) (fun _ => rfl)]
      exact .succVar (h.varIn hx),
    fun
    | .succVar hX => by
      rw [Telescope.rename_rename_of (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
        (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl),
        ← Telescope.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := ξ) (fun _ => rfl),
        Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
          (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl)),
        ← Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.weaken) (ξ₂ := ξ) (fun _ => rfl))]
      exact .succVar (h.secondOrderIn hX)⟩

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
  /-- A telescope in sorts, renamed, is in the sorts.
  RFC: `\mathsf{ren}_\vdash.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
    {κs : List (Universe k)} {l : Level k},
    WfTelescopeSorts sig ctx Θ κs l → TypedRen sig ctx' ξ ctx →
      WfTelescopeSorts sig ctx' (Θ.rename ξ) κs l
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
RFC: `\mathsf{ren}_\vdash.\Theta_{\bar\kappa}`
RFC: `\mathsf{ren}_\vdash.\Theta_\equiv` -/
theorem stableUnderRenaming : StableUnderRenaming :=
  ⟨fun h hξ => by
      rw [Term.rename_eq_subst]; exact TypedRen.liftable.stable.wfType h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Term.rename_eq_subst, Term.rename_eq_subst]
      exact TypedRen.liftable.stable.eqType h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Term.rename_eq_subst, Term.rename_eq_subst]
      exact TypedRen.liftable.stable.hasType h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Term.rename_eq_subst, Term.rename_eq_subst, Term.rename_eq_subst]
      exact TypedRen.liftable.stable.eqTerm h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Args.rename_eq_subst, Telescope.rename_eq_subst]
      exact TypedRen.liftable.stable.hasArgs h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Args.rename_eq_subst, Args.rename_eq_subst, Telescope.rename_eq_subst]
      exact TypedRen.liftable.stable.eqArgs h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [InstanceArgs.rename_eq_subst]
      exact TypedRen.liftable.stable.hasInstanceArgs h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [InstanceArgs.rename_eq_subst, InstanceArgs.rename_eq_subst]
      exact TypedRen.liftable.stable.eqInstanceArgs h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Telescope.rename_eq_subst]
      exact TypedRen.liftable.stable.wfTelescope h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Telescope.rename_eq_subst]
      exact TypedRen.liftable.stable.wfTelescopeSorts h (.base ⟨_, hξ, fun _ => rfl⟩),
    fun h hξ => by
      rw [Telescope.rename_eq_subst, Telescope.rename_eq_subst]
      exact TypedRen.liftable.stable.eqTelescope h (.base ⟨_, hξ, fun _ => rfl⟩)⟩

end Sic.Core
