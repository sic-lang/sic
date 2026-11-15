module

public import Sic.Core.Lifting
public import Sic.Core.Typing.Renaming
import Sic.Core.Substitution.Composition
import Sic.Core.Typing.Prelude
import Sic.Core.Typing.Presuppositions

/-!
# Typing of the Parameters of a Lifting

The parameters of a lifting of annex 20 of RFC 36 are well formed when the parameters that it lifts
are well formed and each parameter lifted is a type, and the renaming of the parameters in the
parameters lifted is then typed: a type of the declaration is a type of its lifting.

The motive of a parameter is a type over a term of this parameter, so that the parameter, at the
variables of its telescope, has to be a type: `Context.LiftsTypes` states it of each parameter
lifted, in the context of the parameters before it.

The proof is by structural recursion on the parameters: the parameters before the last one give
their renaming typed, which types the last parameter renamed, and its motive when it is lifted.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Contexts Extended by a Telescope -/

/-- A context extended by a telescope is well formed only if the context is. -/
theorem WfCtx.of_append {Γ : Scope} : {ps : List Parameter} → {ctx : Context k Γ} →
    {Θ : Telescope k Γ ps} → WfCtx sig (ctx.append Θ) → WfCtx sig ctx
  | [], _, .nil, h => h
  | _ :: _, _, .cons _ _ _ _, h =>
    match WfCtx.of_append (Γ := .var :: Γ) h with
    | .var hA => contextPresuppositions.wfType hA

/-- A context extended by a telescope, and by a type in this context, is well formed: it is the
context extended by the telescope followed by one more entry. -/
theorem WfCtx.append_snoc {Γ : Scope} {p : Parameter} {q : Grade} : {ps : List Parameter} →
    {ctx : Context k Γ} → {Θ : Telescope k Γ ps} → {B : Term k (Γ.extend ps.length)} →
      WfType sig (ctx.append Θ) B → WfCtx sig (ctx.append (Θ.snoc (p := p) q B))
  | [], _, .nil, _, h => .var h
  | _ :: _, _, .cons _ _ _ _, _, h => WfCtx.append_snoc (Γ := .var :: Γ) h

/-! ## Typed Renamings -/

/-- The renaming of a context in the context extended by a second-order variable is typed, when the
context extended is well formed. -/
theorem TypedRen.weakenSecondOrder {Γ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx : Context k Γ} {Θ : Telescope k Γ ps}
    {A : Term k (Γ.extend ps.length)} (h : WfCtx sig (ctx.secondOrder Θ A ψ)) :
    TypedRen sig (ctx.secondOrder Θ A ψ) Ren.weaken ctx :=
  ⟨h, .succSecondOrder, .succSecondOrder⟩

/-- A typed renaming lifted under the variables of a telescope, in the contexts extended by the
telescope and by the telescope renamed, when the first one is well formed. -/
theorem TypedRen.liftN {Γ Δ : Scope} : {ps : List Parameter} → {ctx' : Context k Γ} →
    {α : Ren Γ Δ} → {ctx : Context k Δ} → {Θ : Telescope k Δ ps} → TypedRen sig ctx' α ctx →
      WfCtx sig (ctx.append Θ) →
        TypedRen sig (ctx'.append (Θ.rename α)) (Ren.liftN ps.length α) (ctx.append Θ)
  | [], _, _, _, .nil, h, _ => h
  | _ :: _, _, _, _, .cons _ _ _ _, h, hΘ =>
    match WfCtx.of_append (Γ := .var :: Δ) hΘ with
    | .var hA =>
      TypedRen.liftN (Γ := .var :: Γ) (Δ := .var :: Δ)
        (h.lift (stableUnderRenaming.wfType hA h)) hΘ

/-- A typed renaming lifted under a second-order variable, whose type, renamed, is a type in the
context extended by its telescope, renamed. -/
theorem TypedRen.liftSecondOrder {Γ Δ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ} {α : Ren Γ Δ} {ctx : Context k Δ}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} (h : TypedRen sig ctx' α ctx)
    (hA : WfType sig (ctx'.append (Θ.rename α)) (A.rename (Ren.liftN ps.length α))) :
    TypedRen sig (ctx'.secondOrder (Θ.rename α) (A.rename (Ren.liftN ps.length α)) ψ) (Ren.lift α)
      (ctx.secondOrder Θ A ψ) :=
  ⟨.secondOrder hA, fun
    | .succSecondOrder hx => by
      rw [Term.rename_rename_of (α₁ := Ren.lift α) (α₂ := Ren.weaken)
        (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl),
        ← Term.rename_rename_of (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl)]
      exact .succSecondOrder (h.varIn hx),
    fun
    | .zero => by
      rw [Telescope.rename_rename_of (α₁ := Ren.lift α) (α₂ := Ren.weaken)
        (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl),
        ← Telescope.rename_rename_of (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl),
        Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.lift α) (α₂ := Ren.weaken)
          (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl)),
        ← Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl))]
      exact .zero
    | .succSecondOrder hX => by
      rw [Telescope.rename_rename_of (α₁ := Ren.lift α) (α₂ := Ren.weaken)
        (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl),
        ← Telescope.rename_rename_of (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl),
        Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.lift α) (α₂ := Ren.weaken)
          (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl)),
        ← Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl))]
      exact .succSecondOrder (h.secondOrderIn hX)⟩

/-! ## Parameters Lifted -/

-- ADE: none.
/-- Each parameter of the context at a position of `S`, the first parameter at `0`, is a type, at
the variables of its telescope, in the context of the parameters before it, extended by it and by
its telescope. -/
def Context.LiftsTypes (sig : Signature) (S : List Nat) : {Δ : Scope} → Context k Δ → Prop
  | _, .empty => True
  | _, .var (Γ := Δ) ctx A =>
    ctx.LiftsTypes sig S ∧ (Δ.length ∈ S → WfType sig (ctx.var A) (.var₀ .zero))
  | _, .secondOrder (Γ := Δ) ctx Θ A ψ =>
    ctx.LiftsTypes sig S ∧
      (Δ.length ∈ S →
        WfType sig ((ctx.secondOrder Θ A ψ).append (Θ.rename Ren.weaken)) (Var.eta .zero))

/-- The renaming of a lifting extended by a parameter lifted skips the motive of the parameter. -/
theorem Lifting.cons_true_ren {Δ' Δ : Scope} {e : Scope.Entry} (l : Level k)
    (ρ : Lifting k Δ' Δ) :
    @Lifting.ren k _ _ (Lifting.cons (e := e) l true ρ) =
      fun {_} x => Ren.weaken (e := e.motive) (Ren.lift ρ.ren x) := by
  funext a x
  cases x <;> rfl

/-- The renaming of a lifting extended by a variable, lifted or not, is typed in the contexts
extended by the variable, followed by its motive if it is lifted, when the variable lifted is a
type. -/
theorem TypedRen.liftedVar {Δ' Δ : Scope} {ctx' : Context k Δ'} {ρ : Lifting k Δ' Δ}
    {ctx : Context k Δ} {A : Term k Δ} (s : Quality) (l : Level k)
    (h : TypedRen sig ctx' ρ.ren ctx) (hA : WfType sig ctx A) :
    (b : Bool) → (b = true → WfType sig (ctx.var A) (.var₀ .zero)) →
      TypedRen sig (Context.liftedVar ⟨s, l⟩ b ctx' (A.rename ρ.ren)) (Lifting.cons l b ρ).ren
        (ctx.var A)
  | false, _ => h.lift (stableUnderRenaming.wfType hA h)
  | true, hx => by
    have hρ := h.lift (stableUnderRenaming.wfType hA h)
    have hx' := stableUnderRenaming.wfType (hx rfl) hρ
    rw [Lifting.cons_true_ren]
    exact (TypedRen.weakenSecondOrder
      (.secondOrder (WfType.ofSort (HasType.sort (.var hx') _)))).comp hρ

/-- The renaming of a lifting extended by a second-order variable, lifted or not, is typed in the
contexts extended by the variable, followed by its motive if it is lifted, when the variable lifted,
at the variables of its telescope, is a type. -/
theorem TypedRen.liftedSecondOrder {Δ' Δ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Δ'} {ρ : Lifting k Δ' Δ}
    {ctx : Context k Δ} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} (s : Quality)
    (l : Level k) (h : TypedRen sig ctx' ρ.ren ctx) (hA : WfType sig (ctx.append Θ) A) :
    (b : Bool) →
      (b = true →
        WfType sig ((ctx.secondOrder Θ A ψ).append (Θ.rename Ren.weaken)) (Var.eta .zero)) →
        TypedRen sig
          (Context.liftedSecondOrder ⟨s, l⟩ b ctx' (Θ.rename ρ.ren)
            (A.rename (Ren.liftN ps.length ρ.ren)) ψ)
          (Lifting.cons l b ρ).ren (ctx.secondOrder Θ A ψ)
  | false, _ =>
    h.liftSecondOrder
      (stableUnderRenaming.wfType hA (h.liftN (contextPresuppositions.wfType hA)))
  | true, hX => by
    have hρ := h.liftSecondOrder (ψ := ψ)
      (stableUnderRenaming.wfType hA (h.liftN (contextPresuppositions.wfType hA)))
    have hX' := stableUnderRenaming.wfType (hX rfl)
      (hρ.liftN (contextPresuppositions.wfType (hX rfl)))
    rw [Telescope.rename_rename_of (α₁ := Ren.lift ρ.ren) (α₂ := Ren.weaken)
        (α₃ := fun x => Ren.weaken (ρ.ren x)) (fun _ => rfl),
      ← Telescope.rename_rename_of (α₁ := Ren.weaken) (α₂ := ρ.ren) (fun _ => rfl),
      Var.eta_rename (e := .secondOrder ps ψ) (Ren.lift ρ.ren) .zero] at hX'
    rw [Lifting.cons_true_ren]
    exact (TypedRen.weakenSecondOrder
      (.secondOrder (WfType.ofSort (HasType.sort (WfCtx.append_snoc hX') _)))).comp hρ

-- ADE: none.
/-- The parameters of a lifting are well formed, and the renaming of the parameters in them is
typed, when the parameters are well formed and each parameter lifted is a type. -/
theorem Context.lifted_typedRen (S : List Nat) (s : Quality) (lv : Nat → Level k) :
    {Δ : Scope} → {ctx : Context k Δ} → WfCtx sig ctx → ctx.LiftsTypes sig S →
      TypedRen sig (ctx.lifted S s lv) (Lifting.base S lv Δ).ren ctx
  | _, .empty, h, _ => ⟨h, fun hx => (nomatch hx), fun hX => (nomatch hX)⟩
  | _, .var _ _, .var hA, hS =>
    TypedRen.liftedVar s _
      (Context.lifted_typedRen S s lv (contextPresuppositions.wfType hA) hS.1) hA _
      fun hb => hS.2 (of_decide_eq_true hb)
  | _, .secondOrder _ _ _ _, .secondOrder hA, hS =>
    TypedRen.liftedSecondOrder s _
      (Context.lifted_typedRen S s lv (WfCtx.of_append (contextPresuppositions.wfType hA)) hS.1)
      hA _ fun hb => hS.2 (of_decide_eq_true hb)

end Sic.Core
