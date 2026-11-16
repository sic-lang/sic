module

public import Sic.Core.Typing.Renaming
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Shape
import Sic.Core.Lifting.Substitution
import Sic.Core.Typing.Inversion
import Sic.Core.Typing.Lifting.Context
import Sic.Core.Typing.Prelude
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Substitution

/-!
# Typing of the Types Lifted

A type lifted of annex 20 of RFC 36 is a type of the sort of its level, in the context of the
lifting, when the type that it lifts is typed and the term at which it is lifted is a term of this
type.

The contexts of a lifting are those of a typed lifting, `Lifting.Typed`: the renaming of the lifting
is typed, each variable lifted is a type, at the variables of its telescope, and its motive is
declared over this telescope followed by a term of the variable, in the sort of its level.

The proof is by structural recursion on the relation of the lifting: the inversion of the rule of
the type gives its premises, which the rule of the type lifted takes, renamed, with those that the
recursion gives for the arguments lifted.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Telescopes Followed by an Entry -/

/-- Arguments of a telescope, followed by a term of a type at these arguments, are arguments of the
telescope followed by this type. -/
theorem HasArgs.snoc {Γ : Scope} {ctx : Context k Γ} {p : Parameter} {q : Grade} {e : Term k Γ} :
    {ps : List Parameter} → {ts : Args k Γ ps} → {Θ : Telescope k Γ ps} →
      {T : Term k (Γ.extend ps.length)} → HasArgs sig ctx ts Θ →
        HasType sig ctx e (T.instantiate ts) → HasArgs sig ctx (ts.snoc (p := p) e) (Θ.snoc q T)
  | [], .nil, .nil, _, .nil hctx, he => .cons he (.nil hctx)
  | _ :: ps, .cons t _, .cons _ _ _ Θ, T, .cons ht hts, he =>
    .cons ht (Telescope.subst₀_snoc (ps := ps) q (Subst₀.single t) Θ T ▸
      HasArgs.snoc (T := Term.subst₀ (Subst₀.liftN ps.length (Subst₀.single t)) T) hts he)

/-- A term of a sort in a context extended by a telescope and then by a type is one in the context
extended by the telescope followed by this type. -/
theorem HasType.append_snoc {Γ : Scope} {p : Parameter} {q : Grade} {κ : Universe k} :
    {ps : List Parameter} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
      {A : Term k (Γ.extend ps.length)} → {B : Term k (.var :: Γ.extend ps.length)} →
        HasType sig ((ctx.append Θ).var A) B (.sort κ) →
          HasType sig (ctx.append (Θ.snoc (p := p) q A)) (Scope.extend_snoc Γ ps p ▸ B) (.sort κ)
  | [], _, .nil, _, _, h => h
  | _ :: _, _, .cons _ _ _ _, _, _, h => HasType.append_snoc (Γ := .var :: Γ) h

/-! ## Typed Liftings -/

/-- The renaming of a lifting under `n` new variables is its renaming under these variables. -/
theorem Lifting.liftN_ren {Γ' Γ : Scope} (n : Nat) (ρ : Lifting k Γ' Γ) :
    @Lifting.ren k _ _ (ρ.liftN n) = fun {_} x => Ren.liftN n ρ.ren x := by
  funext a x
  exact go n ρ x
where
  /-- The equality at a variable, by recursion on the number of the variables. -/
  go {Γ' Γ : Scope} : (n : Nat) → (ρ : Lifting k Γ' Γ) →
      ∀ {a} (x : Var (Γ.extend n) a), (ρ.liftN n).ren x = Ren.liftN n ρ.ren x
    | 0, _, _, _ => rfl
    | n + 1, ρ, _, x => go n ρ.lift x

-- ADE: none.
/-- `Σ; Γ' ⊢ ρ : Γ`: the lifting `ρ` of the scope `Γ` in the scope `Γ'` is typed, with motives in
the sorts of the quality `s`: its renaming is typed, each variable lifted is a type, at the
variables of its telescope, and its motive is declared over this telescope followed by a term of the
variable, in the sort of its level, and the motive of each type of the block lifted is a type over a
term of its instance. -/
structure Lifting.Typed (sig : Signature) (s : Quality) {Γ' Γ : Scope} (ctx' : Context k Γ')
    (ρ : Lifting k Γ' Γ) (ctx : Context k Γ) : Prop where
  /-- The renaming of the lifting is typed. -/
  ren : TypedRen sig ctx' ρ.ren ctx
  /-- A variable lifted is a type, and its motive is declared over a term of it. -/
  var : ∀ {x : Var Γ .var} {y : Var Γ' Scope.Entry.var.motive} {l : Level k},
    ρ.motive x = some (y, l) →
      WfType sig ctx (.var₀ x) ∧
        ctx'.SecondOrderIn y
          (Telescope.snoc (p := Lifting.termParam) .unrestrictedUnrestricted .nil
            (.var₀ (ρ.ren x)))
          (.sort ⟨s, l⟩)
  /-- The motive of a type of the block lifted is a type over a term of the instance of this type,
  in the sort of its level. -/
  block : ∀ {D : Name} {b : Lifting.BlockMotive k Γ' Γ}, ρ.block D = some b →
    HasType sig (ctx'.var (b.type.rename ρ.ren)) b.motive (.sort ⟨s, b.level⟩)
  /-- A second-order variable lifted is a type, at the variables of its telescope, and its motive is
  declared over this telescope followed by a term of the variable at them. -/
  secondOrder : ∀ {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
    {X : Var Γ (.secondOrder ps ψ)} {y : Var Γ' (Scope.Entry.secondOrder ps ψ).motive}
    {l : Level k} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)},
    ρ.motive X = some (y, l) → ctx.SecondOrderIn X Θ A →
      WfType sig (ctx.append Θ) (Var.eta X) ∧
        ctx'.SecondOrderIn y
          ((Θ.rename ρ.ren).snoc (p := Lifting.termParam) .unrestrictedUnrestricted
            (Var.eta (ρ.ren X)))
          (.sort ⟨s, l⟩)

/-- The telescope of a motive, in a context extended by an entry, is the telescope of the motive of
the variable in this context. -/
theorem Lifting.motiveTelescope_weaken {Γ' Γ : Scope} {e : Scope.Entry} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} (α : Ren Γ' Γ) (X : Var Γ (.secondOrder ps ψ))
    (Θ : Telescope k Γ ps) :
    ((Θ.rename α).snoc (p := Lifting.termParam) .unrestrictedUnrestricted
        (Var.eta (α X))).rename (Ren.weaken (e := e)) =
      (Θ.rename fun x => Ren.weaken (e := e) (α x)).snoc .unrestrictedUnrestricted
        (Var.eta (Ren.weaken (e := e) (α X))) := by
  rw [Telescope.rename_snoc, Telescope.rename_rename_of (α₃ := fun x => Ren.weaken (e := e) (α x))
    (fun _ => rfl), Var.eta_rename (e := .secondOrder ps ψ)]

/-- A typed lifting in a context extended by a variable. -/
theorem Lifting.Typed.weaken {s : Quality} {Γ' Γ : Scope} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {B : Term k Γ'} (h : Lifting.Typed sig s ctx' ρ ctx)
    (hB : WfCtx sig (ctx'.var B)) : Lifting.Typed sig s (ctx'.var B) ρ.weaken ctx where
  ren := (TypedRen.weaken hB).comp h.ren
  var := fun {x y l} hx => by
    obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    exact ⟨(h.var hx₀).1, .succVar (h.var hx₀).2⟩
  block := fun {D b} hD => by
    obtain ⟨b₀, hD₀, rfl⟩ := Option.map_eq_some_iff.1 hD
    have hC := h.block hD₀
    have hT := match contextPresuppositions.hasType hC with | .var hT => hT
    have hα := TypedRen.weaken hB
    have e : (b₀.type.rename ρ.ren).rename (Ren.weaken (e := .var)) =
        b₀.type.rename (ρ.weaken (e := .var)).ren :=
      Term.rename_rename_of (fun _ => rfl) _
    have := stableUnderRenaming.hasType hC (hα.lift (stableUnderRenaming.wfType hT hα))
    rw [e] at this
    exact this
  secondOrder := fun {ps ψ X y l Θ A} hx hX => by
    obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    refine ⟨(h.secondOrder hx₀ hX).1, ?_⟩
    have hy := Context.SecondOrderIn.succVar (B := B) (h.secondOrder hx₀ hX).2
    rw [Lifting.motiveTelescope_weaken] at hy
    exact hy

/-- A typed lifting in a context extended by a second-order variable. -/
theorem Lifting.Typed.weakenSecondOrder {s : Quality} {Γ' Γ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ'} {ρ : Lifting k Γ' Γ}
    {ctx : Context k Γ} {Θ : Telescope k Γ' ps} {B : Term k (Γ'.extend ps.length)}
    (h : Lifting.Typed sig s ctx' ρ ctx) (hB : WfCtx sig (ctx'.secondOrder Θ B ψ)) :
    Lifting.Typed sig s (ctx'.secondOrder Θ B ψ) ρ.weaken ctx where
  ren := (TypedRen.weakenSecondOrder hB).comp h.ren
  var := fun {x y l} hx => by
    obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    exact ⟨(h.var hx₀).1, .succSecondOrder (h.var hx₀).2⟩
  block := fun {D b} hD => by
    obtain ⟨b₀, hD₀, rfl⟩ := Option.map_eq_some_iff.1 hD
    have hC := h.block hD₀
    have hT := match contextPresuppositions.hasType hC with | .var hT => hT
    have hα := TypedRen.weakenSecondOrder hB
    have e : (b₀.type.rename ρ.ren).rename (Ren.weaken (e := .secondOrder ps ψ)) =
        b₀.type.rename (ρ.weaken (e := .secondOrder ps ψ)).ren :=
      Term.rename_rename_of (fun _ => rfl) _
    have := stableUnderRenaming.hasType hC (hα.lift (stableUnderRenaming.wfType hT hα))
    rw [e] at this
    exact this
  secondOrder := fun {ps' ψ' X y l Θ' A} hx hX => by
    obtain ⟨⟨y₀, l₀⟩, hx₀, he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    refine ⟨(h.secondOrder hx₀ hX).1, ?_⟩
    have hy := Context.SecondOrderIn.succSecondOrder (Θ' := Θ) (B := B) (ψ' := ψ)
      (h.secondOrder hx₀ hX).2
    rw [Lifting.motiveTelescope_weaken] at hy
    exact hy

/-- A typed lifting under a variable, whose type is a type. -/
theorem Lifting.Typed.lift {s : Quality} {Γ' Γ : Scope} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {A : Term k Γ} (h : Lifting.Typed sig s ctx' ρ ctx)
    (hA : WfType sig ctx A) :
    Lifting.Typed sig s (ctx'.var (A.rename ρ.ren)) ρ.lift (ctx.var A) :=
  have hρ := h.ren.lift (stableUnderRenaming.wfType hA h.ren)
  have hw := h.weaken hρ.wfCtx
  { ren := hρ
    var := fun {x y l} hx =>
      match x, hx with
      | .succ x, hx =>
        ⟨stableUnderRenaming.wfType (hw.var hx).1 (TypedRen.weaken (.var hA)), (hw.var hx).2⟩
    block := fun {D b} hD => by
      obtain ⟨b₀, hD₀, rfl⟩ := Option.map_eq_some_iff.1 hD
      have hC := hw.block (b := b₀.weaken) (show Option.map _ (ρ.block D) = _ by rw [hD₀]; rfl)
      have e : (b₀.type.rename (Ren.weaken (e := .var))).rename ρ.lift.ren =
          b₀.type.rename ρ.weaken.ren :=
        Term.rename_rename_of (fun _ => rfl) _
      show HasType sig (Context.var _ ((b₀.type.rename (Ren.weaken (e := .var))).rename ρ.lift.ren))
        _ _
      rw [e]
      exact hC
    secondOrder := fun {ps ψ X y l Θ A} hx hX =>
      match X, hX, hx with
      | .succ X, .succVar (Θ := Θ) hX, hx => by
        obtain ⟨hw₁, hw₂⟩ := hw.secondOrder hx hX
        refine ⟨?_, ?_⟩
        · have := stableUnderRenaming.wfType hw₁
            ((TypedRen.weaken (.var hA)).liftN (contextPresuppositions.wfType hw₁))
          rw [Var.eta_rename (e := .secondOrder ps ψ)] at this
          exact this
        · have e : (Θ.rename (Ren.weaken (e := .var))).rename ρ.lift.ren = Θ.rename ρ.weaken.ren :=
            Telescope.rename_rename_of (fun _ => rfl) Θ
          rw [e]
          exact hw₂ }

/-- A typed lifting under a second-order variable, whose type is a type in the context extended by
its telescope. -/
theorem Lifting.Typed.liftSecondOrder {s : Quality} {Γ' Γ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ'} {ρ : Lifting k Γ' Γ}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
    (h : Lifting.Typed sig s ctx' ρ ctx) (hA : WfType sig (ctx.append Θ) A) :
    Lifting.Typed sig s
      (ctx'.secondOrder (Θ.rename ρ.ren) (A.rename (Ren.liftN ps.length ρ.ren)) ψ) ρ.lift
      (ctx.secondOrder Θ A ψ) :=
  have hρ := h.ren.liftSecondOrder (ψ := ψ)
    (stableUnderRenaming.wfType hA (h.ren.liftN (contextPresuppositions.wfType hA)))
  have hw := h.weakenSecondOrder hρ.wfCtx
  have hα := TypedRen.weakenSecondOrder (ψ := ψ) (.secondOrder hA)
  { ren := hρ
    var := fun {x y l} hx =>
      match x, hx with
      | .succ x, hx => ⟨stableUnderRenaming.wfType (hw.var hx).1 hα, (hw.var hx).2⟩
    block := fun {D b} hD => by
      obtain ⟨b₀, hD₀, rfl⟩ := Option.map_eq_some_iff.1 hD
      have hC := hw.block (b := b₀.weaken) (show Option.map _ (ρ.block D) = _ by rw [hD₀]; rfl)
      have e : (b₀.type.rename (Ren.weaken (e := .secondOrder ps ψ))).rename ρ.lift.ren =
          b₀.type.rename ρ.weaken.ren :=
        Term.rename_rename_of (fun _ => rfl) _
      show HasType sig (Context.var _ ((b₀.type.rename (Ren.weaken (e := .secondOrder ps ψ))).rename ρ.lift.ren))
        _ _
      rw [e]
      exact hC
    secondOrder := fun {ps' ψ' X y l Θ' A'} hx hX =>
      match X, hX, hx with
      | .succ X, .succSecondOrder (Θ := Θ₀) hX, hx => by
        obtain ⟨hw₁, hw₂⟩ := hw.secondOrder hx hX
        refine ⟨?_, ?_⟩
        · have := stableUnderRenaming.wfType hw₁
            (hα.liftN (contextPresuppositions.wfType hw₁))
          rw [Var.eta_rename (e := .secondOrder ps' ψ')] at this
          exact this
        · have e : (Θ₀.rename (Ren.weaken (e := .secondOrder ps ψ))).rename ρ.lift.ren =
              Θ₀.rename ρ.weaken.ren :=
            Telescope.rename_rename_of (fun _ => rfl) Θ₀
          rw [e]
          exact hw₂ }

/-- A typed lifting under the variables of a telescope, in the contexts extended by the telescope
and by the telescope renamed, when the first one is well formed. -/
theorem Lifting.Typed.liftN {s : Quality} {Γ' Γ : Scope} : {ps : List Parameter} →
    {ctx' : Context k Γ'} → {ρ : Lifting k Γ' Γ} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
      Lifting.Typed sig s ctx' ρ ctx → WfCtx sig (ctx.append Θ) →
        Lifting.Typed sig s (ctx'.append (Θ.rename ρ.ren)) (ρ.liftN ps.length) (ctx.append Θ)
  | [], _, _, _, .nil, h, _ => h
  | _ :: ps, _, _, _, .cons _ _ _ _, h, hΘ =>
    match WfCtx.of_append (Γ := .var :: Γ) hΘ with
    | .var hA => Lifting.Typed.liftN (Γ' := .var :: Γ') (Γ := .var :: Γ) (ps := ps) (h.lift hA) hΘ

/-! ## Types That Are Lifted -/

-- ADE: none.
/-- A type that is lifted, and typed, is a type: a variable lifted is one, at arguments of its
telescope, and an instance of a declared type is in the sort of its type declaration.
The variables lifted are those of a typed lifting, in any context. -/
theorem Term.Lifts.wfType {s : Quality} {v : Lifting.Variables} {Γ'' Γ' Γ : Scope}
    {ctx' : Context k Γ'} {ρ' : Lifting k Γ' Γ} {ρ : Lifting k Γ'' Γ} {ctx : Context k Γ}
    {n : Nest Name} {e A' : Term k Γ''} {A T : Term k Γ} {l : Level k}
    (hρ : Lifting.Typed sig s ctx' ρ' ctx)
    (hm : ∀ {a} (x : Var Γ a), (ρ.motive x).isSome → (ρ'.motive x).isSome) :
    Term.Lifts sig v ρ n e A A' l → HasType sig ctx A T → WfType sig ctx A
  | .var (a := .var) (x := x) (ts := .nil) hx _, _ => by
    obtain ⟨⟨y, l⟩, hx'⟩ := Option.isSome_iff_exists.1 (hm x (hx ▸ rfl))
    exact (hρ.var hx').1
  | .var (a := .secondOrder _ _) (x := X) (ts := ts) hx _, hA => by
    obtain ⟨⟨y, l⟩, hx'⟩ := Option.isSome_iff_exists.1 (hm X (hx ▸ rfl))
    obtain ⟨Θ, A₀, hX, hts⟩ := hA.secondOrder_inv
    rw [← Var.eta_instantiate X ts]
    exact (hρ.secondOrder hx' hX).1.instantiate hts
  | .block _ _, hA => by
    obtain ⟨decl, ζ, hΔ, hq, hl, hp, hD, hadm, has⟩ := hA.inst_inv
    subst hΔ
    exact .ofSort (.inst hD hq hl hp hadm has)
  | .inst hd hD .., hA => by
    obtain ⟨ζ, hq, hl, hp, hD, hadm, has⟩ := hA.inst_inv_of_mem hd hD
    exact .ofSort (.inst hD hq hl hp hadm has)

/-! ## Arguments That Are Lifted -/

/-- The arguments of an instance lifted, followed by the argument of a variable that is not
lifted, renamed. -/
theorem HasInstanceArgs.liftedVar_false {s : Quality} {Γ' Γ Δ₁ Δ : Scope} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ₁} {params' : Context k Δ₁} {ρ₀ : Lifting k Δ₁ Δ} {A : Term k Δ}
    {B : Term k Γ} (κ : Universe k) (l : Level k) (hρ : Lifting.Typed sig s ctx' ρ ctx)
    (has' : HasInstanceArgs sig ctx' as' params')
    (hc : ∀ {a} (x : Var Δ a),
      as'.toSubst (ρ₀.ren x) = (as.toSubst x).rename (Ren.liftN a.params.length ρ.ren))
    (hB : HasType sig ctx B (A.subst as.toSubst)) (b : Bool) (hb : b = false) :
    ∃ hΔ : .var :: Δ₁ = Scope.liftedCons b .var Δ₁,
      HasInstanceArgs sig ctx' (hΔ ▸ InstanceArgs.snoc (e := .var) as' (B.rename ρ.ren))
          (Context.liftedVar κ b params' (A.rename ρ₀.ren)) ∧
        ∀ {a} (x : Var (.var :: Δ) a),
          (hΔ ▸ InstanceArgs.snoc (e := .var) as' (B.rename ρ.ren)).toSubst
              ((Lifting.cons l b ρ₀).ren x) =
            ((InstanceArgs.snoc (e := .var) as B).toSubst x).rename
              (Ren.liftN a.params.length ρ.ren) := by
  subst hb
  refine ⟨rfl, .var has' ?_, fun x => ?_⟩
  · rw [Term.subst_rename_comm_of hc A]
    exact stableUnderRenaming.hasType hB hρ.ren
  · cases x with
    | zero => rfl
    | succ x => exact hc x

/-- The arguments of an instance lifted, followed by the argument of a second-order variable that
is not lifted, renamed. -/
theorem HasInstanceArgs.liftedSecondOrder_false {s : Quality} {Γ' Γ Δ₁ Δ : Scope}
    {ps : List Parameter} {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ₁} {params' : Context k Δ₁} {ρ₀ : Lifting k Δ₁ Δ}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
    (κ : Universe k) (l : Level k) (hρ : Lifting.Typed sig s ctx' ρ ctx)
    (has' : HasInstanceArgs sig ctx' as' params')
    (hc : ∀ {a} (x : Var Δ a),
      as'.toSubst (ρ₀.ren x) = (as.toSubst x).rename (Ren.liftN a.params.length ρ.ren))
    (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B (A.subst (Subst.liftN _ as.toSubst)))
    (b : Bool) (hb : b = false) :
    ∃ hΔ : .secondOrder ps ψ :: Δ₁ = Scope.liftedCons b (.secondOrder ps ψ) Δ₁,
      HasInstanceArgs sig ctx'
          (hΔ ▸ InstanceArgs.snoc (e := .secondOrder ps ψ) as'
            (B.rename (Ren.liftN ps.length ρ.ren)))
          (Context.liftedSecondOrder κ b params' (Θ.rename ρ₀.ren)
            (A.rename (Ren.liftN ps.length ρ₀.ren)) ψ) ∧
        ∀ {a} (x : Var (.secondOrder ps ψ :: Δ) a),
          (hΔ ▸ InstanceArgs.snoc (e := .secondOrder ps ψ) as'
              (B.rename (Ren.liftN ps.length ρ.ren))).toSubst ((Lifting.cons l b ρ₀).ren x) =
            ((InstanceArgs.snoc (e := .secondOrder ps ψ) as B).toSubst x).rename
              (Ren.liftN a.params.length ρ.ren) := by
  subst hb
  refine ⟨rfl, .secondOrder has' ?_, fun x => ?_⟩
  · rw [Telescope.subst_rename_comm_of hc Θ,
      Term.subst_rename_comm_of (Subst.liftN_rename_comm_of _ hc) A]
    exact stableUnderRenaming.hasType hB (hρ.ren.liftN (contextPresuppositions.hasType hB))
  · cases x with
    | zero => rfl
    | succ x => exact hc x

/-- The arguments of an instance lifted, followed by the argument of a variable lifted, renamed,
and by this argument lifted, a type over a term of the argument. -/
theorem HasInstanceArgs.liftedVar_true {s : Quality} {Γ' Γ Δ₁ Δ : Scope} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ₁} {params' : Context k Δ₁} {ρ₀ : Lifting k Δ₁ Δ} {A : Term k Δ}
    {B : Term k Γ} {B' : Term k (Γ'.extend (Scope.Entry.var.motive).params.length)}
    (l : Level k) (hρ : Lifting.Typed sig s ctx' ρ ctx)
    (has' : HasInstanceArgs sig ctx' as' params')
    (hc : ∀ {a} (x : Var Δ a),
      as'.toSubst (ρ₀.ren x) = (as.toSubst x).rename (Ren.liftN a.params.length ρ.ren))
    (hB : HasType sig ctx B (A.subst as.toSubst))
    (hB' : HasType sig (ctx'.var (B.rename ρ.ren)) B' (.sort ⟨s, l⟩)) (b : Bool)
    (hb : b = true) :
    ∃ hΔ : Scope.Entry.var.motive :: .var :: Δ₁ = Scope.liftedCons b .var Δ₁,
      HasInstanceArgs sig ctx'
          (hΔ ▸ InstanceArgs.snoc (e := Scope.Entry.var.motive)
            (InstanceArgs.snoc (e := .var) as' (B.rename ρ.ren)) B')
          (Context.liftedVar ⟨s, l⟩ b params' (A.rename ρ₀.ren)) ∧
        ∀ {a} (x : Var (.var :: Δ) a),
          (hΔ ▸ InstanceArgs.snoc (e := Scope.Entry.var.motive)
              (InstanceArgs.snoc (e := .var) as' (B.rename ρ.ren)) B').toSubst
              ((Lifting.cons l b ρ₀).ren x) =
            ((InstanceArgs.snoc (e := .var) as B).toSubst x).rename
              (Ren.liftN a.params.length ρ.ren) := by
  subst hb
  have hB₁ : HasType sig ctx' (B.rename ρ.ren) ((A.rename ρ₀.ren).subst as'.toSubst) := by
    rw [Term.subst_rename_comm_of hc A]
    exact stableUnderRenaming.hasType hB hρ.ren
  refine ⟨rfl, .secondOrder (.var has' hB₁) hB', fun x => ?_⟩
  cases x with
  | zero => rfl
  | succ x => exact hc x

/-- The arguments of an instance lifted, followed by the argument of a second-order variable
lifted, renamed, and by this argument lifted, a type over the telescope of the variable and a term
of the argument. -/
theorem HasInstanceArgs.liftedSecondOrder_true {s : Quality} {Γ' Γ Δ₁ Δ : Scope}
    {ps : List Parameter} {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ₁} {params' : Context k Δ₁} {ρ₀ : Lifting k Δ₁ Δ}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
    {B' : Term k (Γ'.extend ((Scope.Entry.secondOrder ps ψ).motive).params.length)}
    (l : Level k) (hρ : Lifting.Typed sig s ctx' ρ ctx)
    (has' : HasInstanceArgs sig ctx' as' params')
    (hc : ∀ {a} (x : Var Δ a),
      as'.toSubst (ρ₀.ren x) = (as.toSubst x).rename (Ren.liftN a.params.length ρ.ren))
    (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B (A.subst (Subst.liftN _ as.toSubst)))
    (hB' : HasType sig
      (ctx'.append ((((Θ.subst as.toSubst).rename ρ.ren).snoc (p := Lifting.termParam)
        .unrestrictedUnrestricted (B.rename (Ren.liftN ps.length ρ.ren)))))
      B' (.sort ⟨s, l⟩)) (b : Bool) (hb : b = true) :
    ∃ hΔ : (Scope.Entry.secondOrder ps ψ).motive :: .secondOrder ps ψ :: Δ₁ =
        Scope.liftedCons b (.secondOrder ps ψ) Δ₁,
      HasInstanceArgs sig ctx'
          (hΔ ▸ InstanceArgs.snoc (e := (Scope.Entry.secondOrder ps ψ).motive)
            (InstanceArgs.snoc (e := .secondOrder ps ψ) as'
              (B.rename (Ren.liftN ps.length ρ.ren))) B')
          (Context.liftedSecondOrder ⟨s, l⟩ b params' (Θ.rename ρ₀.ren)
            (A.rename (Ren.liftN ps.length ρ₀.ren)) ψ) ∧
        ∀ {a} (x : Var (.secondOrder ps ψ :: Δ) a),
          (hΔ ▸ InstanceArgs.snoc (e := (Scope.Entry.secondOrder ps ψ).motive)
              (InstanceArgs.snoc (e := .secondOrder ps ψ) as'
                (B.rename (Ren.liftN ps.length ρ.ren))) B').toSubst
              ((Lifting.cons l b ρ₀).ren x) =
            ((InstanceArgs.snoc (e := .secondOrder ps ψ) as B).toSubst x).rename
              (Ren.liftN a.params.length ρ.ren) := by
  subst hb
  have hB₁ : HasType sig (ctx'.append ((Θ.rename ρ₀.ren).subst as'.toSubst))
      (B.rename (Ren.liftN ps.length ρ.ren))
      ((A.rename (Ren.liftN ps.length ρ₀.ren)).subst (Subst.liftN _ as'.toSubst)) := by
    rw [Telescope.subst_rename_comm_of hc Θ,
      Term.subst_rename_comm_of (Subst.liftN_rename_comm_of _ hc) A]
    exact stableUnderRenaming.hasType hB (hρ.ren.liftN (contextPresuppositions.hasType hB))
  refine ⟨rfl, .secondOrder (.secondOrder has' hB₁) ?_, fun x => ?_⟩
  · rw [Telescope.subst_snoc,
      Telescope.subst_rename_of (α := Ren.weaken) (θ' := as'.toSubst) (fun _ => rfl),
      Telescope.subst_rename_comm_of hc Θ]
    have he : (Var.eta (k := k) (.zero : Var (.secondOrder ps ψ :: Δ₁) (.secondOrder ps ψ))).subst
        (Subst.liftN ps.length (InstanceArgs.snoc (e := .secondOrder ps ψ) as'
          (B.rename (Ren.liftN ps.length ρ.ren))).toSubst) =
        B.rename (Ren.liftN ps.length ρ.ren) :=
      Var.eta_subst (e := .secondOrder ps ψ)
        (InstanceArgs.snoc (e := .secondOrder ps ψ) as'
          (B.rename (Ren.liftN ps.length ρ.ren))).toSubst .zero
    rw [he]
    exact hB'
  · cases x with
    | zero => rfl
    | succ x => exact hc x

/-! ## Typing of the Types Lifted -/

-- ADE: none.
/-- A type lifted at a term of the type that it lifts, which is typed, is a type of the sort of its
level, in the context of a typed lifting whose motives have the quality of the lifting. -/
theorem Term.Lifts.hasType {v : Lifting.Variables} {Γ' Γ : Scope} {ctx' : Context k Γ'}
    {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {n : Nest Name} {e A' : Term k Γ'} {A T : Term k Γ}
    {l : Level k} (hρ : Lifting.Typed sig v.quality ctx' ρ ctx) (h : Term.Lifts sig v ρ n e A A' l)
    (hA : HasType sig ctx A T) (he : HasType sig ctx' e (A.rename ρ.ren)) :
    HasType sig ctx' A' (.sort ⟨v.quality, l⟩) :=
  type h hρ hA he
where
  /-- The typing of a type lifted, by recursion on the relation. -/
  type {Γ' Γ : Scope} {ctx' : Context k Γ'} {ρ : Lifting k Γ' Γ} {ctx : Context k Γ}
      {n : Nest Name} {e A' : Term k Γ'} {A T : Term k Γ} {l : Level k} :
      Term.Lifts sig v ρ n e A A' l → Lifting.Typed sig v.quality ctx' ρ ctx →
        HasType sig ctx A T → HasType sig ctx' e (A.rename ρ.ren) →
          HasType sig ctx' A' (.sort ⟨v.quality, l⟩)
    | .var (a := .var) (ts := .nil) hx _, hρ, _, he =>
      Term.sort_instantiate _ _ ▸
        HasType.secondOrder (hρ.var hx).2 (HasArgs.snoc (.nil hρ.ren.wfCtx) he)
    | .var (a := .secondOrder _ _) (x := X) (ts := ts) hx _, hρ, hA, he => by
      obtain ⟨Θ, A₀, hX, hts⟩ := hA.secondOrder_inv
      have he' : HasType sig ctx' e ((Var.eta (ρ.ren X)).instantiate (ts.rename ρ.ren)) := by
        rw [Var.eta_instantiate]
        exact he
      exact Term.sort_instantiate _ _ ▸ HasType.secondOrder (hρ.secondOrder hx hX).2
        (HasArgs.snoc (stableUnderRenaming.hasArgs hts hρ.ren) he')
    | .block hD hT, hρ, _, he =>
      stableUnderSubstitution.hasType (hρ.block hD) (TypedSubst.single (hT ▸ he))
    | .inst (decl := decl) (D := D) (qs := qs) (ls := ls) (ls' := ls') (ps := ps) (as := as)
        (S := S) (as' := as') (ns := ns) (body := body) hd hD _ hq hl hp has _ hL, hρ, hA, he => by
      obtain ⟨ζ, _, _, _, hDT, hadm, hargs⟩ := hA.inst_inv_of_mem hd hD
      have hlen := has.length_eq
      have hq' : (qs ++ [v.quality]).length = decl.sorts + 1 := by
        rw [List.length_append, hq]
        rfl
      have hp' : (ps ++ [v.recursion, v.requirement, v.ownership]).length = decl.grades + 3 := by
        rw [List.length_append, hp]
        rfl
      have hl' : (ls ++ ls').length = decl.levels + S.length := by
        rw [List.length_append, hl, hlen]
      obtain ⟨hΔ, has', hc⟩ := args has hρ hargs S
        (fun i => (Lifting.motiveLevel decl.levels S i).subst ((ls ++ ls').getFin hl'))
        (fun _ _ => Iff.rfl)
        (fun j h₁ h₂ => Lifting.motiveLevel_subst has.nodup hl hlen hl' j h₁ h₂)
      subst hΔ
      have hI := Instance.lifted_ofLists qs ps v.quality v.recursion v.requirement v.ownership hq
        hp hq' hp'
      have hadm' : decl.constraint (Instance.ofLists (qs ++ [v.quality])
          (ps ++ [v.recursion, v.requirement, v.ownership]) hq' hp').lifted := hI ▸ hadm
      have hargs' : HasInstanceArgs sig ctx' as'
          (Context.substLevels ((ls ++ ls').getFin hl')
            (Context.lifted S
              ((Instance.ofLists (qs ++ [v.quality])
                (ps ++ [v.recursion, v.requirement, v.ownership]) hq' hp').sorts
                (Fin.last decl.sorts))
              (Lifting.motiveLevel decl.levels S)
              (Context.substLevels (Level.lifted S.length)
                (decl.params (Instance.ofLists (qs ++ [v.quality])
                  (ps ++ [v.recursion, v.requirement, v.ownership]) hq' hp').lifted)))) := by
        rw [Context.lifted_substLevels, hI,
          Instance.sorts_last_ofLists qs _ v.quality hq hq' hp',
          Context.substLevels_substLevels, Level.lifted_subst ls ls' hl hl']
        exact has'
      have e₀ : ((InstanceArgs.identity (k := k) decl.scope).rename
            (Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).ren).subst
          as'.toSubst = as.rename ρ.ren :=
        InstanceArgs.toSubst_inj fun x => by
          rw [InstanceArgs.subst_rename_of (θ' := fun y => as'.toSubst
              ((Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).ren y))
              (fun _ => rfl),
            InstanceArgs.identity_subst, ← InstanceArgs.toSubst_rename,
            Lifting.base_ren S (Lifting.motiveLevel decl.levels S)
              (fun i => (Lifting.motiveLevel decl.levels S i).subst ((ls ++ ls').getFin hl'))]
          exact hc x
      have he' : HasType sig ctx' e
          (Term.subst as'.toSubst
            (Term.substLevels ((ls ++ ls').getFin hl')
              (decl.liftedInstance D S.length
                (Instance.ofLists (qs ++ [v.quality])
                  (ps ++ [v.recursion, v.requirement, v.ownership]) hq' hp').lifted
                ((InstanceArgs.identity decl.scope).rename
                  (Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).ren)))) := by
        rw [hI, decl.liftedInstance_substLevels D hq hp hl hl', InstanceArgs.substLevels_rename,
          InstanceArgs.identity_substLevels]
        show HasType sig ctx' e (.inst D qs ls ps _)
        rw [e₀]
        exact he
      rw [← decl.liftingSort_substLevels S hq hp hl hlen hq' hp' hl']
      exact HasType.inst (decl := decl.lifting D S ns body)
        (ζ := fun _ _ => .unrestrictedUnrestricted)
        ⟨hL, .inr ⟨_, List.mem_singleton_self _, rfl, rfl⟩⟩ hq' hl' hp' hadm' (.var hargs' he')
  /-- The typing of the arguments lifted of an instance, by recursion on the relation: they are
  arguments of the parameters lifted at the positions `S₂`, which are those of the relation among
  the positions of the parameters, with motives at the levels that `lv` gives, those of the
  relation, and they give the image of a parameter its argument, renamed. -/
  args {Γ' Γ : Scope} {ctx' : Context k Γ'} {ρ : Lifting k Γ' Γ} {ctx : Context k Γ} {Δ : Scope}
      {ns : List (Nest Name)} {as : InstanceArgs k Γ Δ} {S : List Nat} {ls : List (Level k)}
      {Δ' : Scope} {as' : InstanceArgs k Γ' Δ'} {params : Context k Δ} :
      InstanceArgs.Lifts sig v ρ ns as S ls as' → Lifting.Typed sig v.quality ctx' ρ ctx →
        HasInstanceArgs sig ctx as params → ∀ (S₂ : List Nat) (lv : Nat → Level k),
          (∀ i, i < Δ.length → (i ∈ S₂ ↔ i ∈ S)) →
            (∀ j (h₁ : j < S.length) (h₂ : j < ls.length), lv S[j] = ls[j]) →
              ∃ hΔ : Δ' = Δ.lifted S₂,
                HasInstanceArgs sig ctx' (hΔ ▸ as') (params.lifted S₂ v.quality lv) ∧
                  ∀ {a} (x : Var Δ a),
                    (hΔ ▸ as').toSubst ((Lifting.base S₂ lv Δ).ren x) =
                      (as.toSubst x).rename (Ren.liftN a.params.length ρ.ren)
    | .nil, hρ, .nil _, _, _, _, _ => ⟨rfl, .nil hρ.ren.wfCtx, fun x => nomatch x⟩
    | .absent (a := .var) (Δ := Δ₀) has _ _, hρ, .var hps ha, S₂, lv, hS, hlv => by
      obtain ⟨hΔ, has', hc⟩ :=
        args has hρ hps S₂ lv (fun i hi => hS i (Nat.lt_succ_of_lt hi)) hlv
      subst hΔ
      exact HasInstanceArgs.liftedVar_false _ (lv Δ₀.length) hρ has' hc ha _
        (decide_eq_false fun h =>
          Nat.lt_irrefl _ (has.lt _ ((hS _ (Nat.lt_succ_self _)).1 h)))
    | .absent (a := .secondOrder _ _) (Δ := Δ₀) has _ _, hρ, .secondOrder hps hb, S₂, lv, hS,
        hlv => by
      obtain ⟨hΔ, has', hc⟩ :=
        args has hρ hps S₂ lv (fun i hi => hS i (Nat.lt_succ_of_lt hi)) hlv
      subst hΔ
      exact HasInstanceArgs.liftedSecondOrder_false _ (lv Δ₀.length) hρ has' hc hb _
        (decide_eq_false fun h =>
          Nat.lt_irrefl _ (has.lt _ ((hS _ (Nat.lt_succ_self _)).1 h)))
    | .lifted (a := .var) (Δ := Δ₀) (S := S) (ls := ls) (l := l) (B := B) has hB, hρ,
        .var hps ha, S₂, lv, hS, hlv => by
      have hlen := has.length_eq
      obtain ⟨hΔ, has', hc⟩ := args has hρ hps S₂ lv
        (fun i hi => (hS i (Nat.lt_succ_of_lt hi)).trans
          ⟨fun h => (List.mem_append.1 h).elim id fun h' =>
            absurd (List.mem_singleton.1 h') (Nat.ne_of_lt hi), List.mem_append_left _⟩)
        (fun j h₁ h₂ => by
          have h := hlv j (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)
          rwa [List.getElem_append_left h₁, List.getElem_append_left h₂] at h)
      subst hΔ
      have hl : lv Δ₀.length = l := by
        have h := hlv S.length (by simp) (by simp [hlen])
        simpa [hlen] using h
      subst hl
      have hw := stableUnderRenaming.wfType
        (hB.wfType hρ (fun x h => Lifting.isSome_of_weaken ρ x h) ha) hρ.ren
      have ih := type hB (hρ.weaken (.var hw)) ha
        (Term.rename_rename_of (α₁ := Ren.weaken) (α₂ := ρ.ren) (fun _ => rfl) B ▸
          HasType.var (.var hw) .zero)
      exact HasInstanceArgs.liftedVar_true _ hρ has' hc ha ih _
        (decide_eq_true ((hS _ (Nat.lt_succ_self _)).2 (List.mem_append_right _ (.head _))))
    | .lifted (a := .secondOrder ps _) (Δ := Δ₀) (S := S) (ls := ls) (l := l) (B := B) has hB,
        hρ, .secondOrder hps hb, S₂, lv, hS, hlv => by
      have hlen := has.length_eq
      obtain ⟨hΔ, has', hc⟩ := args has hρ hps S₂ lv
        (fun i hi => (hS i (Nat.lt_succ_of_lt hi)).trans
          ⟨fun h => (List.mem_append.1 h).elim id fun h' =>
            absurd (List.mem_singleton.1 h') (Nat.ne_of_lt hi), List.mem_append_left _⟩)
        (fun j h₁ h₂ => by
          have h := hlv j (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)
          rwa [List.getElem_append_left h₁, List.getElem_append_left h₂] at h)
      subst hΔ
      have hl : lv Δ₀.length = l := by
        have h := hlv S.length (by simp) (by simp [hlen])
        simpa [hlen] using h
      subst hl
      have hρn := hρ.liftN (contextPresuppositions.hasType hb)
      have hw := stableUnderRenaming.wfType
        (hB.wfType hρn (fun x h => Lifting.isSome_of_weaken _ x h) hb) hρn.ren
      have ih := type hB (hρn.weaken (.var hw)) hb
        (Term.rename_rename_of (α₁ := Ren.weaken) (α₂ := (ρ.liftN ps.length).ren)
          (fun _ => rfl) B ▸ HasType.var (.var hw) .zero)
      rw [Lifting.liftN_ren] at ih
      exact HasInstanceArgs.liftedSecondOrder_true _ hρ has' hc hb (HasType.append_snoc ih) _
        (decide_eq_true ((hS _ (Nat.lt_succ_self _)).2 (List.mem_append_right _ (.head _))))

end Sic.Core
