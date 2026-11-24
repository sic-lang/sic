module

public import Sic.Core.Typing.Renaming
import Sic.Core.Typing.Lifting.Context
import Sic.Core.Typing.Presuppositions

/-!
# Typing of the Parameters Themselves

The parameters of a well-formed context, as the arguments of an instance in their own scope, are
arguments of the context: the types of a type declaration name its own types at the parameters
themselves, and the lifting of a codata type declares a term of the type at them.

Each parameter is the abstraction of its variable over the variables of its telescope, so the proof
types these variables as arguments of the telescope, in the context extended by it, and then the
variable applied to them, by the rule `(var_X)`.

ADE have no second-order variables and no declared types: their identity substitution gives each
variable itself.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Variables of a Telescope -/

/-- The renaming of a context in the context extended by a telescope is typed, when the context
extended is well formed. -/
theorem TypedRen.weakenN {Γ : Scope} : {ps : List Parameter} → {ctx : Context k Γ} →
    {Θ : Telescope k Γ ps} → WfCtx sig (ctx.append Θ) →
      TypedRen sig (ctx.append Θ) (Ren.weakenN ps.length) ctx
  | [], _, .nil, h =>
    ⟨h, fun {_ A} hx => by
      have e := Term.rename_id_of (α := Ren.weakenN (Γ := Γ) 0) (fun _ => rfl) A
      rw [← e] at hx
      exact hx,
      fun {ps _ _ Θ A} hX => by
      have e₁ := Telescope.rename_id_of (α := Ren.weakenN (Γ := Γ) 0) (fun _ => rfl) Θ
      have e₂ := Term.rename_id_of (Ren.liftN_id_of ps.length (α := Ren.weakenN (Γ := Γ) 0)
        (fun _ => rfl)) A
      rw [← e₁, ← e₂] at hX
      exact hX⟩
  | _ :: _, _, .cons _ _ _ _, h =>
    match WfCtx.of_append (Γ := .var :: Γ) h with
    | .var hA => (TypedRen.weakenN (Γ := .var :: Γ) h).comp (TypedRen.weaken (.var hA))

/-- The variables of a telescope are arguments of it, in the context extended by it. -/
theorem HasArgs.bound {Γ : Scope} : {ps : List Parameter} → {ctx : Context k Γ} →
    {Θ : Telescope k Γ ps} → WfCtx sig (ctx.append Θ) →
      HasArgs sig (ctx.append Θ) (Args.bound ps) (Θ.rename (Ren.weakenN ps.length))
  | [], _, .nil, h => .nil h
  | _ :: ps, ctx, .cons _ _ A Θ, h => by
    obtain ⟨hA⟩ : ∃ _ : WfType sig ctx A, True :=
      match WfCtx.of_append (Γ := .var :: Γ) h with
      | .var hA => ⟨hA, trivial⟩
    have hx := (TypedRen.weakenN (Γ := .var :: Γ) (ctx := ctx.var A) (Θ := Θ) h).varIn .zero
    rw [Term.rename_rename_of (α₁ := Ren.weakenN (Γ := .var :: Γ) ps.length) (α₂ := Ren.weaken)
      (α₃ := Ren.weakenN (Γ := Γ) (ps.length + 1)) (fun _ => rfl) A] at hx
    refine .cons (.var h hx) ?_
    have e : (Θ.rename (Ren.lift (Ren.weakenN (Γ := Γ) (ps.length + 1)))).subst₀
          (Subst₀.single (.var₀ (Var.weakenN ps.length .zero))) =
        Θ.rename (Ren.weakenN (Γ := .var :: Γ) ps.length) :=
      (Telescope.subst₀_rename_of (fun _ => rfl) Θ).trans
        (Telescope.subst₀_eq_rename_of_eta (α := Ren.weakenN (Γ := .var :: Γ) ps.length)
          (fun x => match x with
            | .zero => rfl
            | .succ _ => rfl) Θ)
    exact e ▸ HasArgs.bound (Γ := .var :: Γ) h

/-- A second-order variable, as an abstraction over the variables of its telescope, is a term of its
type, in the context extended by its telescope. -/
theorem HasType.eta {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
    {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps}
    {A : Term k (Γ.extend ps.length)} (hX : ctx.SecondOrderIn X Θ A)
    (h : WfCtx sig (ctx.append Θ)) : HasType sig (ctx.append Θ) (Var.eta X) A := by
  have ht := HasType.secondOrder ((TypedRen.weakenN h).secondOrderIn hX) (HasArgs.bound h)
  rw [Term.instantiate_bound_rename] at ht
  exact ht

/-! ## Parameters Themselves -/

/-- The parameters of a well-formed context, themselves, are arguments of the context. -/
theorem HasInstanceArgs.identity : {Δ : Scope} → {ctx : Context k Δ} → WfCtx sig ctx →
    HasInstanceArgs sig ctx (.identity Δ) ctx
  | _, _, .empty h => .nil (.empty h)
  | _, _, .var (A := A) hA => by
    have hw := TypedRen.weaken (.var hA)
    refine .var (stableUnderRenaming.hasInstanceArgs
      (HasInstanceArgs.identity (contextPresuppositions.wfType hA)) hw) ?_
    rw [← Term.rename_eq_subst_of (fun x => InstanceArgs.identity_rename_toSubst Ren.weaken x) A]
    exact .var (.var hA) .zero
  | _, _, .secondOrder (ps := ps) (ψ := ψ) (Θ := Θ) (A := A) hA => by
    have hw := TypedRen.weakenSecondOrder (ψ := ψ) (.secondOrder hA)
    refine .secondOrder (stableUnderRenaming.hasInstanceArgs
      (HasInstanceArgs.identity (WfCtx.of_append (contextPresuppositions.wfType hA))) hw) ?_
    rw [← Telescope.rename_eq_subst_of
        (fun x => InstanceArgs.identity_rename_toSubst Ren.weaken x) Θ,
      ← Term.rename_eq_subst_of (Subst.liftN_eta_of ps.length
        (fun x => InstanceArgs.identity_rename_toSubst Ren.weaken x)) A]
    exact .eta .zero (hw.liftN (contextPresuppositions.wfType hA)).wfCtx

end Sic.Core
