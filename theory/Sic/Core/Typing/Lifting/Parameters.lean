module

public import Sic.Core.Typing.Lifting.Context
public import Sic.Core.Typing.Lifting.Types
import Sic.Core.Lifting.Substitution
import Sic.Core.Substitution.Composition
import Sic.Core.Typing.Identity
import Sic.Core.Typing.Levels
import Sic.Core.Typing.Prelude
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature

/-!
# Typed Lifting of the Parameters

The lifting of the parameters of a codata type in the parameters of its lifting, of annex 20 of
RFC 36, is typed, `Lifting.Typed`, when the parameters are well formed and each parameter lifted is
a type: the motive of each parameter lifted is declared over the telescope of the parameter, followed
by a term of it, in the sort of its level.
The parameters of the lifting, the parameters lifted followed by the term `y` of the type at them,
are then well formed, at each instance that the constraint of the type declaration admits.

The proof is by structural recursion on the parameters, as for their renaming: a parameter that is
not lifted lifts the typed lifting of the parameters before it, and a parameter lifted declares its
motive after it.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Parameters Lifted at Other Levels -/

/-- The parameters lifted are types at instantiated levels. -/
theorem Context.LiftsTypes.substLevels {k' : Nat} (ls' : Fin k → Level k') {S : List Nat} :
    {Δ : Scope} → {ctx : Context k Δ} → ctx.LiftsTypes sig S →
      (ctx.substLevels ls').LiftsTypes sig S
  | _, .empty, _ => trivial
  | _, .var _ _, h => ⟨h.1.substLevels ls', fun hS => stableUnderLevels.wfType ls' (h.2 hS)⟩
  | _, .secondOrder ctx Θ A ψ, h =>
    ⟨h.1.substLevels ls', fun hS => by
      have hX := stableUnderLevels.wfType ls' (h.2 hS)
      rw [Context.substLevels_append, Telescope.substLevels_rename, Var.eta_substLevels] at hX
      exact hX⟩

/-! ## Typed Lifting Extended by a Parameter -/

/-- The lifting extended by a variable, lifted or not, is typed in the contexts extended by the
variable, followed by its motive if it is lifted, when the variable lifted is a type. -/
theorem Lifting.Typed.liftedVar {Δ' Δ : Scope} {ctx' : Context k Δ'} {ρ : Lifting k Δ' Δ}
    {ctx : Context k Δ} {A : Term k Δ} (s : Quality) (l : Level k)
    (h : Lifting.Typed sig s ctx' ρ ctx) (hA : WfType sig ctx A) :
    (b : Bool) → (b = true → WfType sig (ctx.var A) (.var₀ .zero)) →
      Lifting.Typed sig s (Context.liftedVar ⟨s, l⟩ b ctx' (A.rename ρ.ren)) (Lifting.cons l b ρ)
        (ctx.var A)
  | false, _ => h.lift hA
  | true, hx =>
    have hρ := TypedRen.liftedVar s l h.ren hA true hx
    have hw := (h.lift hA).weakenSecondOrder hρ.wfCtx
    { ren := hρ
      var := fun {x y l'} hm =>
        match x, hm with
        | .zero, hm => by
          cases hm
          exact ⟨hx rfl, .zero⟩
        | .succ x, hm => by
          obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hm
          cases he
          exact hw.var (x := .succ x) (y := .succ (.succ y₀))
            (show Option.map _ (Option.map _ (ρ.motive x)) = _ by rw [hx₀]; rfl)
      secondOrder := fun {ps ψ X y l' Θ A'} hm hX =>
        match X, hX, hm with
        | .succ X, hX, hm => by
          obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hm
          cases he
          have hy := hw.secondOrder (X := .succ X) (y := .succ (.succ y₀))
            (show Option.map _ (Option.map _ (ρ.motive X)) = _ by rw [hx₀]; rfl) hX
          rw [Lifting.cons_true_ren]
          exact hy }

/-- The lifting extended by a second-order variable, lifted or not, is typed in the contexts
extended by the variable, followed by its motive if it is lifted, when the variable lifted is a
type, at the variables of its telescope. -/
theorem Lifting.Typed.liftedSecondOrder {Δ' Δ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Δ'} {ρ : Lifting k Δ' Δ}
    {ctx : Context k Δ} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} (s : Quality)
    (l : Level k) (h : Lifting.Typed sig s ctx' ρ ctx) (hA : WfType sig (ctx.append Θ) A) :
    (b : Bool) →
      (b = true →
        WfType sig ((ctx.secondOrder Θ A ψ).append (Θ.rename Ren.weaken)) (Var.eta .zero)) →
        Lifting.Typed sig s
          (Context.liftedSecondOrder ⟨s, l⟩ b ctx' (Θ.rename ρ.ren)
            (A.rename (Ren.liftN ps.length ρ.ren)) ψ)
          (Lifting.cons l b ρ) (ctx.secondOrder Θ A ψ)
  | false, _ => h.liftSecondOrder hA
  | true, hx =>
    have hρ := TypedRen.liftedSecondOrder s l h.ren hA true hx
    have hw := (h.liftSecondOrder (ψ := ψ) hA).weakenSecondOrder hρ.wfCtx
    { ren := hρ
      var := fun {x y l'} hm =>
        match x, hm with
        | .succ x, hm => by
          obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hm
          cases he
          exact hw.var (x := .succ x) (y := .succ (.succ y₀))
            (show Option.map _ (Option.map _ (ρ.motive x)) = _ by rw [hx₀]; rfl)
      secondOrder := fun {ps' ψ' X y l' Θ' A'} hm hX =>
        match X, hX, hm with
        | .zero, .zero, hm => by
          cases hm
          refine ⟨hx rfl, ?_⟩
          have hy := Context.SecondOrderIn.zero (ctx := ctx'.secondOrder (Θ.rename ρ.ren)
              (A.rename (Ren.liftN ps.length ρ.ren)) ψ)
            (Θ := ((Θ.rename ρ.ren).rename Ren.weaken).snoc (p := Lifting.termParam)
              .unrestrictedUnrestricted (Var.eta .zero))
            (A := .sort ⟨s, l⟩) (ψ := Lifting.resultOwnership .unrestrictedUnrestricted _)
          rw [Telescope.rename_snoc, Var.eta_rename (e := .secondOrder ps ψ),
            Telescope.rename_rename_of (α₁ := Ren.weaken) (α₂ := Ren.weaken)
              (α₃ := fun x => Ren.weaken (Ren.weaken x)) (fun _ => rfl),
            Telescope.rename_rename_of (α₁ := fun x => Ren.weaken (Ren.weaken x)) (α₂ := ρ.ren)
              (α₃ := (Lifting.cons (e := .secondOrder ps ψ) l true ρ).ren ∘ Ren.weaken)
              (fun _ => rfl)] at hy
          rw [Telescope.rename_rename_of
            (α₁ := (Lifting.cons (e := .secondOrder ps ψ) l true ρ).ren) (α₂ := Ren.weaken)
            (α₃ := (Lifting.cons (e := .secondOrder ps ψ) l true ρ).ren ∘ Ren.weaken)
            (fun _ => rfl)]
          exact hy
        | .succ X, hX, hm => by
          obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hm
          cases he
          have hy := hw.secondOrder (X := .succ X) (y := .succ (.succ y₀))
            (show Option.map _ (Option.map _ (ρ.motive X)) = _ by rw [hx₀]; rfl) hX
          rw [Lifting.cons_true_ren]
          exact hy }

/-! ## Typed Lifting of the Parameters -/

-- ADE: none.
/-- The lifting of the parameters in the parameters lifted is typed, when the parameters are well
formed and each parameter lifted is a type. -/
theorem Context.lifted_typed (S : List Nat) (s : Quality) (lv : Nat → Level k) :
    {Δ : Scope} → {ctx : Context k Δ} → WfCtx sig ctx → ctx.LiftsTypes sig S →
      Lifting.Typed sig s (ctx.lifted S s lv) (Lifting.base S lv Δ) ctx
  | _, .empty, h, _ =>
    ⟨⟨h, fun hx => (nomatch hx), fun hX => (nomatch hX)⟩, fun {x} => (nomatch x),
      fun {_ _ X} => (nomatch X)⟩
  | _, .var _ _, .var hA, hS =>
    Lifting.Typed.liftedVar s _
      (Context.lifted_typed S s lv (contextPresuppositions.wfType hA) hS.1) hA _
      fun hb => hS.2 (of_decide_eq_true hb)
  | _, .secondOrder _ _ _ _, .secondOrder hA, hS =>
    Lifting.Typed.liftedSecondOrder s _
      (Context.lifted_typed S s lv (WfCtx.of_append (contextPresuppositions.wfType hA)) hS.1)
      hA _ fun hb => hS.2 (of_decide_eq_true hb)

/-! ## Parameters of a Lifting -/

-- ADE: none.
/-- The instance of a codata type of a well-formed signature at its variables and at its parameters,
among those of its lifting, of which the parameter `y` of the lifting is a term, is a type in these
parameters, at an instance that the constraint of its type declaration admits. -/
theorem TypeDeclaration.liftedInstance_wfType {decl : TypeDeclaration} {F : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hsig : WfSig sig)
    (hT : sig.HasCodataType F decl T) (n : Nat) {ι : Instance decl.sorts decl.grades}
    (hadm : decl.constraint ι) :
    WfType sig ((decl.params ι).substLevels (Level.lifted n))
      (decl.liftedInstance F n ι (.identity decl.scope)) := by
  have hP := stableUnderLevels.wfCtx (Level.lifted n) (hsig.wfCtx_params hT.1 hadm)
  have hq : (List.ofFn ι.sorts).length = decl.sorts := List.length_ofFn
  have hl : (List.ofFn (Level.lifted (k := decl.levels) n)).length = decl.levels :=
    List.length_ofFn
  have hp : (List.ofFn ι.grades).length = decl.grades := List.length_ofFn
  have has : HasInstanceArgs sig ((decl.params ι).substLevels (Level.lifted n))
      (.identity decl.scope)
      ((decl.params (.ofLists _ _ hq hp)).substLevels
        ((List.ofFn (Level.lifted n)).getFin hl)) := by
    rw [List.getFin_ofFn, Instance.ofLists_ofFn]
    exact HasInstanceArgs.identity hP
  exact .ofSort (.inst ⟨hT.1, .inr ⟨T, hT.2.1, hT.2.2, rfl⟩⟩ hq hl hp
    ((Instance.ofLists_ofFn ι hq hp).symm ▸ hadm) has)

-- ADE: none.
/-- The lifting of the parameters of a codata type of a well-formed signature, under the term `y`
of the type at them, is typed in the parameters of the lifting of the type, at an instance that the
constraint of its type declaration admits, when each parameter lifted is a type. -/
theorem TypeDeclaration.lifting_typed {decl : TypeDeclaration} {F : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hsig : WfSig sig)
    (hT : sig.HasCodataType F decl T) (S : List Nat) {ns : List Name}
    (body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns)
    (I : Instance (decl.sorts + 1) (decl.grades + 3)) (hadm : decl.constraint I.lifted)
    (hS : (decl.params I.lifted).LiftsTypes sig S) :
    Lifting.Typed sig (I.sorts (Fin.last decl.sorts)) ((decl.lifting F S ns body).params I)
      (Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).lift
      (((decl.params I.lifted).substLevels (Level.lifted S.length)).var
        (decl.liftedInstance F S.length I.lifted (.identity decl.scope))) :=
  (Context.lifted_typed S _ _
    (stableUnderLevels.wfCtx (Level.lifted S.length) (hsig.wfCtx_params hT.1 hadm))
    (hS.substLevels _)).lift (decl.liftedInstance_wfType hsig hT S.length hadm)

end Sic.Core
