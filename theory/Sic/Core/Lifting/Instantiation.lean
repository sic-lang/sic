module

public import Sic.Core.Lifting.Substitution
public import Sic.Core.Substitution.Composition
import Sic.Core.Lifting.Functionality

/-!
# Instantiation of the Liftings

A type lifted by a lifting that lifts variables, as the result of a destructor of the lifting of a
codata type of annex 13 of RFC 36 is, substituted by a substitution that gives each variable lifted
an abstraction lifted, at its nesting, and its motive this abstraction lifted, is the type
substituted, lifted at the term substituted: the motive of a variable applied to arguments becomes
the abstraction lifted at these arguments.

The type lifted has no position, since the lifting has no type of a block, while the type
substituted has the positions of the abstractions for its variables: its nesting is that of the
type, where each variable has the nesting at which its abstraction is lifted.
A variable that is not lifted has no position, so that an argument in which no variable lifted
occurs has none.

The lifting of the scope of the type substituted lifts no variable, as the one of the block of a
recursor: the abstraction lifted of a variable is lifted under the variables of its telescope, and
the stability of the lifting under the substitutions brings it under the entries that the relation
goes under, and to the arguments of the variable.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Arguments Followed by a Term -/

/-- Arguments followed by one more, substituted. -/
theorem Args.subst_snoc {Γ Δ : Scope} {p : Parameter} (θ : Subst k Γ Δ) :
    {ps : List Parameter} → (ts : Args k Δ ps) → (t : Term k Δ) →
      (ts.snoc (p := p) t).subst θ = (ts.subst θ).snoc (t.subst θ)
  | [], .nil, _ => rfl
  | _ :: _, .cons u us, t => congrArg (Args.cons (u.subst θ)) (Args.subst_snoc θ us t)

/-- The motive of a parameter lifted, in the scope of its telescope followed by a term, renamed
under this telescope, is this motive renamed under the telescope and under the term. -/
theorem Term.rename_extend_snoc : {Γ Δ : Scope} → (ps : List Parameter) → (p : Parameter) →
    (α : Ren Γ Δ) → (B : Term k (.var :: Δ.extend ps.length)) →
      (Scope.extend_snoc Δ ps p ▸ B).rename (Ren.liftN (ps ++ [p]).length α) =
        Scope.extend_snoc Γ ps p ▸ B.rename (Ren.lift (Ren.liftN ps.length α))
  | _, _, [], _, _, _ => rfl
  | Γ, Δ, _ :: ps, p, α, B =>
    Term.rename_extend_snoc (Γ := .var :: Γ) (Δ := .var :: Δ) ps p (Ren.lift α) B

/-! ## Substitutions That Keep the Variables Before the Last One -/

/-- A term of a scope, in the scope extended by an entry, substituted by a substitution that gives
each variable of the scope itself, is the term. -/
theorem Term.subst_rename_weaken_of {Γ : Scope} {e : Scope.Entry} {θ : Subst k Γ (e :: Γ)}
    (h : ∀ {a} (x : Var Γ a), θ (.succ x) = Var.eta x) (t : Term k Γ) :
    (t.rename Ren.weaken).subst θ = t :=
  (Term.subst_rename_of (θ' := fun x => Var.eta x) h t).trans (Term.subst_id_of (fun _ => rfl) t)

/-- A term over a variable, in the scope extended by an entry below it, substituted under this
variable by a substitution that gives each variable of the scope itself, is the term. -/
theorem Term.subst_lift_rename_lift_weaken_of {Γ : Scope} {e e' : Scope.Entry}
    {θ : Subst k Γ (e :: Γ)} (h : ∀ {a} (x : Var Γ a), θ (.succ x) = Var.eta x)
    (t : Term k (e' :: Γ)) :
    (t.rename (Ren.lift Ren.weaken)).subst (Subst.lift θ) = t :=
  have key : ∀ {a} (x : Var (e' :: Γ) a),
      Subst.lift θ (Ren.lift Ren.weaken x) = Var.eta x
    | _, .zero => rfl
    | _, .succ x => by
      show (θ (.succ x)).rename (Ren.liftN _ Ren.weaken) = _
      rw [h x]
      exact Var.eta_rename Ren.weaken x
  (Term.subst_rename_of key t).trans (Term.subst_id_of (fun _ => rfl) t)

/-! ## Liftings That Lift No Variable, Substituted -/

/-- A lifting that lifts no variable, under a variable, substituted by a term for this variable
in the scope that it lifts and by this term renamed in the other. -/
theorem Lifting.Substitutes.single {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (u : Term k Γ) :
    Lifting.Substitutes (Subst₀.toSubst (Subst₀.single u))
      (Subst₀.toSubst (Subst₀.single (u.rename ρ.ren)))
      (ρ.lift (e := .var)) ρ where
  ren := fun x =>
    match x with
    | .zero => rfl
    | .succ x => (Var.eta_rename ρ.ren x).symm
  motive := fun x =>
    match x with
    | .zero => rfl
    | .succ x => by
      show (ρ.motive x).map _ = none
      rw [hρ x]
      rfl
  motive' := hρ
  block := fun D => by
    show ρ.block D = ((ρ.block D).map _).map _
    cases ρ.block D with
    | none => rfl
    | some b =>
      show some b = some (Lifting.BlockMotive.mk
        ((b.type.rename Ren.weaken).subst (Subst₀.toSubst (Subst₀.single u)))
        ((b.motive.rename (Ren.lift Ren.weaken)).subst
          (Subst.lift (Subst₀.toSubst (Subst₀.single (u.rename ρ.ren))))) b.level b.ownership)
      rw [Term.subst_rename_weaken_of (fun _ => rfl),
        Term.subst_lift_rename_lift_weaken_of (fun _ => rfl)]

/-- A lifting that lifts no variable, in a scope extended by a variable, substituted by a term for
this variable. -/
theorem Lifting.Substitutes.weakenSingle {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (e : Term k Γ') :
    Lifting.Substitutes (fun x => Var.eta x) (Subst₀.toSubst (Subst₀.single e))
      (ρ.weaken (e := .var)) ρ where
  ren := fun x => (Var.eta_rename ρ.ren x).symm
  motive := fun x => by
    show (ρ.motive x).map _ = none
    rw [hρ x]
    rfl
  motive' := hρ
  block := fun D => by
    show ρ.block D = ((ρ.block D).map _).map _
    cases ρ.block D with
    | none => rfl
    | some b =>
      show some b = some (Lifting.BlockMotive.mk (b.type.subst fun x => Var.eta x)
        ((b.motive.rename (Ren.lift Ren.weaken)).subst
          (Subst.lift (Subst₀.toSubst (Subst₀.single e))))
        b.level b.ownership)
      rw [Term.subst_id_of (fun _ => rfl), Term.subst_lift_rename_lift_weaken_of (fun _ => rfl)]

/-- A lifting that lifts no variable, renamed under a new entry of both scopes. -/
theorem Lifting.Substitutes.ofLift {Γ' Γ : Scope} {e : Scope.Entry} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) :
    Lifting.Substitutes (Ren.toSubst Ren.weaken) (Ren.toSubst Ren.weaken) ρ (ρ.lift (e := e)) where
  ren := fun x => by
    show Var.eta (.succ (ρ.ren x)) = (Var.eta (.succ x)).rename (Ren.liftN _ (Ren.lift ρ.ren))
    exact (Var.eta_rename (k := k) (Ren.lift (e := e) ρ.ren) (.succ x)).symm
  motive := hρ
  motive' := fun x =>
    match x with
    | .zero => rfl
    | .succ x => by
      show (ρ.motive x).map _ = none
      rw [hρ x]
      rfl
  block := fun D => by
    show (ρ.block D).map _ = (ρ.block D).map _
    refine congrArg (fun f => Option.map f (ρ.block D)) (funext fun b => ?_)
    show Lifting.BlockMotive.mk (b.type.rename Ren.weaken)
        (b.motive.rename (Ren.lift Ren.weaken)) b.level b.ownership =
      Lifting.BlockMotive.mk (b.type.subst (Ren.toSubst Ren.weaken))
        (b.motive.subst (Subst.lift (Ren.toSubst Ren.weaken))) b.level b.ownership
    rw [Term.rename_eq_subst,
      Term.rename_eq_subst_of (θ := Subst.lift (Ren.toSubst Ren.weaken))
        (Subst.lift_eta_of fun _ => rfl) b.motive]

/-- A lifting that lifts no variable, renamed in a scope extended by a new entry. -/
theorem Lifting.Substitutes.ofWeaken {Γ' Γ : Scope} {e : Scope.Entry} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) :
    Lifting.Substitutes (Ren.toSubst fun x => x) (Ren.toSubst Ren.weaken) ρ
      (ρ.weaken (e := e)) where
  ren := fun x => by
    show Var.eta (.succ (ρ.ren x)) = (Var.eta x).rename (Ren.liftN _ fun y => (ρ.ren y).succ)
    exact (Var.eta_rename (fun y => (ρ.ren y).succ) x).symm
  motive := hρ
  motive' := fun x => by
    show (ρ.motive x).map _ = none
    rw [hρ x]
    rfl
  block := fun D => by
    show (ρ.block D).map _ = (ρ.block D).map _
    refine congrArg (fun f => Option.map f (ρ.block D)) (funext fun b => ?_)
    show Lifting.BlockMotive.mk b.type (b.motive.rename (Ren.lift Ren.weaken)) b.level b.ownership =
      Lifting.BlockMotive.mk (b.type.subst (Ren.toSubst fun x => x))
        (b.motive.subst (Subst.lift (Ren.toSubst Ren.weaken))) b.level b.ownership
    rw [Term.subst_id_of (θ := Ren.toSubst fun x => x) (fun _ => rfl),
      Term.rename_eq_subst_of (θ := Subst.lift (Ren.toSubst Ren.weaken))
        (Subst.lift_eta_of fun _ => rfl) b.motive]

/-- A lifting that lifts no variable, under new variables, substituted by substitutions that give
each variable of the scopes itself, and that commute with the renamings of the liftings. -/
theorem Lifting.Substitutes.ofLiftN {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (n : Nat) {τ : Subst k Γ (Γ.extend n)}
    {τ' : Subst k Γ' (Γ'.extend n)} (hτ : ∀ {a} (x : Var Γ a), τ (x.weakenN n) = Var.eta x)
    (hτ' : ∀ {a} (x : Var Γ' a), τ' (x.weakenN n) = Var.eta x)
    (hren : ∀ {a} (x : Var (Γ.extend n) a),
      τ' ((ρ.liftN n).ren x) = (τ x).rename (Ren.liftN a.params.length ρ.ren)) :
    Lifting.Substitutes τ τ' (ρ.liftN n) ρ where
  ren := hren
  motive := fun x => by
    cases h : (ρ.liftN n).motive x with
    | none => rfl
    | some _ =>
      obtain ⟨y, -, hy⟩ := Lifting.isSome_of_liftN n ρ x (h ▸ rfl)
      rw [hρ y] at hy
      exact nomatch hy
  motive' := hρ
  block := fun D => by
    rw [Lifting.liftN_block n ρ D]
    cases ρ.block D with
    | none => rfl
    | some b =>
      have key : ∀ {a} (x : Var (.var :: Γ') a),
          Subst.lift τ' (Ren.lift (Ren.weakenN n) x) = Var.eta x
        | _, .zero => rfl
        | _, .succ x => by
          show (τ' (x.weakenN n)).rename (Ren.liftN _ Ren.weaken) = _
          rw [hτ' x]
          exact Var.eta_rename Ren.weaken x
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level b.ownership
        ((Term.subst_rename_of (θ := τ) (α := Ren.weakenN n) (θ' := fun x => Var.eta x)
          (fun x => hτ x) b.type).trans (Term.subst_id_of (fun _ => rfl) b.type)).symm
        ((Term.subst_rename_of key b.motive).trans
          (Term.subst_id_of (fun _ => rfl) b.motive)).symm)

/-! ## Abstractions Lifted -/

/-- A type lifted is lifted likewise at the nesting and at the term, from the type and to the type,
that those of the lifting are equal to. -/
theorem Term.Lifts.congr {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n₁ n₂ : Nest Name}
    {e₁ e₂ : Term k Γ'} {A₁ A₂ : Term k Γ} {A₁' A₂' : Term k Γ'} {m : Lifting.Result k}
    (h : Term.Lifts sig v ρ n₁ e₁ A₁ A₁' m) (hn : n₁ = n₂) (he : e₁ = e₂) (hA : A₁ = A₂)
    (hA' : A₁' = A₂') : Term.Lifts sig v ρ n₂ e₂ A₂ A₂' m :=
  hn ▸ he ▸ hA ▸ hA' ▸ h

/-- The motive of a parameter lifted, in the scope of its telescope followed by a term, substituted
at the first order under this telescope, is this motive substituted under the telescope and under
the term. -/
theorem Term.subst₀_extend_snoc {Γ Δ : Scope} (ps : List Parameter) (p : Parameter)
    (σ : Subst₀ k Γ Δ) (B : Term k (.var :: Δ.extend ps.length)) :
    (Scope.extend_snoc Δ ps p ▸ B).subst₀ (Subst₀.liftN (ps ++ [p]).length σ) =
      Scope.extend_snoc Γ ps p ▸
        B.subst (Subst.lift (Subst.liftN ps.length (Subst₀.toSubst σ))) := by
  rw [Term.subst₀_liftN_eq_subst]
  exact Term.subst_extend_snoc ps p (Subst₀.toSubst σ) B

/-- A type lifted at the last variable of the scope in which a lifting that lifts no variable
lifts it, substituted under this variable. -/
theorem Term.Lifts.substWeaken {Γ' Γ Δ' Δ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'}
    {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ} (hs : Lifting.Substitutes θ θ' ρ ρ')
    {n : Nest Name} {A : Term k Δ} {B' : Term k (.var :: Δ')} {m : Lifting.Result k}
    (h : Term.Lifts sig v ρ.weaken n (.var₀ .zero) A B' m) :
    Term.Lifts sig v ρ'.weaken n (.var₀ .zero) (A.subst θ) (B'.subst (Subst.lift θ')) m := by
  have h' := h.subst hs.weaken
  rwa [Term.var₀_zero_subst_lift] at h'

/-- An abstraction lifted at the term that follows the variables of its telescope, by a lifting
that lifts no variable, renamed as this lifting is. -/
theorem Term.Lifts.renameAbstraction {Γ₂' Γ₂ Γ' Γ : Scope} {α : Ren Γ₂ Γ} {α' : Ren Γ₂' Γ'}
    {ρ : Lifting k Γ' Γ} {ρ₂ : Lifting k Γ₂' Γ₂}
    (hs : Lifting.Substitutes (Ren.toSubst α) (Ren.toSubst α') ρ ρ₂) (m : Nat) {n : Nest Name}
    {A : Term k (Γ.extend m)} {B' : Term k (.var :: Γ'.extend m)} {r : Lifting.Result k}
    (h : Term.Lifts sig v (ρ.liftN m).weaken n (.var₀ .zero) A B' r) :
    Term.Lifts sig v (ρ₂.liftN m).weaken n (.var₀ .zero) (A.rename (Ren.liftN m α))
      (B'.rename (Ren.lift (Ren.liftN m α'))) r := by
  have h' := h.substWeaken (hs.liftN m)
  have e₁ : A.subst (Subst.liftN m (Ren.toSubst α)) = A.rename (Ren.liftN m α) :=
    (Term.rename_eq_subst_of (Subst.liftN_eta_of m fun _ => rfl) A).symm
  have e₂ : B'.subst (Subst.lift (Subst.liftN m (Ren.toSubst α'))) =
      B'.rename (Ren.lift (Ren.liftN m α')) :=
    (Term.rename_eq_subst_of (Subst.lift_eta_of (Subst.liftN_eta_of m fun _ => rfl)) B').symm
  rw [e₁, e₂] at h'
  exact h'

/-- An abstraction lifted at the term that follows the variables of its telescope, by a lifting
that lifts no variable, at arguments for these variables and at a term: the abstraction at the
arguments is lifted at the term, to the abstraction lifted at the arguments, renamed, followed by
the term. -/
theorem Term.Lifts.instantiateAbstraction {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {n : Nest Name} (e : Term k Γ') {m : Lifting.Result k} :
    {ps : List Parameter} → {A : Term k (Γ.extend ps.length)} →
      {B' : Term k (.var :: Γ'.extend ps.length)} → (us : Args k Γ ps) →
      Term.Lifts sig v (ρ.liftN ps.length).weaken n (.var₀ .zero) A B' m →
        Term.Lifts sig v ρ n e (A.instantiate us)
          ((Scope.extend_snoc Γ' ps Lifting.termParam ▸ B').instantiate
            ((us.rename ρ.ren).snoc e)) m
  | [], A, B', .nil, h => by
    exact (h.subst (Lifting.Substitutes.weakenSingle hρ e)).congr rfl rfl
      (Term.subst_id_of (fun _ => rfl) A) (Term.subst₀_eq_subst (Subst₀.single e) B').symm
  | _ :: ps, A, B', .cons u us, h => by
    have h' : Term.Lifts sig v (ρ.liftN ps.length).weaken n (.var₀ .zero)
        (A.subst (Subst.liftN ps.length (Subst₀.toSubst (Subst₀.single u))))
        (B'.subst (Subst.lift (Subst.liftN ps.length
          (Subst₀.toSubst (Subst₀.single (u.rename ρ.ren)))))) m :=
      Term.Lifts.substWeaken ((Lifting.Substitutes.single hρ u).liftN ps.length) h
    exact (Term.Lifts.instantiateAbstraction hρ e us h').congr rfl rfl
      (congrArg (fun t => Term.instantiate t us)
        (Term.subst₀_liftN_eq_subst ps.length (Subst₀.single u) A).symm)
      (congrArg (fun t => Term.instantiate t ((us.rename ρ.ren).snoc e))
        (Term.subst₀_extend_snoc (Γ := Γ') (Δ := .var :: Γ') ps Lifting.termParam
          (Subst₀.single (u.rename ρ.ren)) B').symm)

/-! ## Liftings Instantiated -/

/-- The lifting `ρ'`, which lifts no variable, is the lifting `ρ` instantiated by `θ` in the scope
that it lifts and by `θ'` in the scope in which it lifts it, where `ν` gives the nestings of the
variables of `ρ`: what `θ'` gives the variable that a variable is, is what `θ` gives this variable,
renamed, a variable that `ρ` does not lift has no position, and what `θ'` gives the motive of a
variable lifted is what `θ` gives this variable, lifted, at its nesting, at the term that follows
the variables of its telescope, of the level of the motive. -/
structure Lifting.Instantiates (sig : Signature) (v : Lifting.Variables) {Γ' Γ Δ' Δ : Scope}
    (θ : Subst k Γ Δ) (θ' : Subst k Γ' Δ') (ρ : Lifting k Δ' Δ) (ρ' : Lifting k Γ' Γ)
    (ν : Nesting Name Δ) : Prop where
  /-- The substitutions commute with the renamings of the liftings. -/
  ren : ∀ {a} (x : Var Δ a), θ' (ρ.ren x) = (θ x).rename (Ren.liftN a.params.length ρ'.ren)
  /-- The lifting instantiated lifts no variable. -/
  motive' : ∀ {a} (x : Var Γ a), ρ'.motive x = none
  /-- A variable that is not lifted has no position. -/
  plain : ∀ {a} (x : Var Δ a), ρ.motive x = none → ν x = .plain
  /-- The motive of a variable lifted is given the abstraction for the variable, lifted. -/
  lifted : ∀ {a} (x : Var Δ a) (y : Var Δ' a.motive) (m : Lifting.Result k),
    ρ.motive x = some (y, m) →
    ∃ B' : Term k (.var :: Γ'.extend a.params.length),
      θ' y = Scope.extend_snoc Γ' a.params Lifting.termParam ▸ B' ∧
        Term.Lifts sig v (ρ'.liftN a.params.length).weaken (ν x) (.var₀ .zero) (θ x) B' m

namespace Lifting.Instantiates

variable {Γ' Γ Δ' Δ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ}
  {ρ' : Lifting k Γ' Γ} {ν : Nesting Name Δ}

/-- A lifting instantiated, under a new entry of the scopes, which is not lifted and has no
position. -/
theorem lift {e : Scope.Entry} (h : Lifting.Instantiates sig v θ θ' ρ ρ' @ν) :
    Lifting.Instantiates sig v (Subst.lift (e := e) θ) (Subst.lift θ') ρ.lift ρ'.lift
      (Nesting.lift @ν) where
  ren := Subst.lift_rename_comm_of h.ren
  motive' := fun x =>
    match x with
    | .zero => rfl
    | .succ x => by
      show (ρ'.motive x).map _ = none
      rw [h.motive' x]
      rfl
  plain := fun x =>
    match x with
    | .zero => fun _ => rfl
    | .succ x => fun hx =>
      h.plain x (Option.map_eq_none_iff.1 (hx : (ρ.motive x).map _ = none))
  lifted := fun x =>
    match x with
    | .zero => fun _ _ hx => nomatch hx
    | .succ x => fun y m hx => by
      obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1
        (hx : (ρ.motive x).map (Prod.map .succ id) = some (y, m))
      cases he
      obtain ⟨B', hB', hL⟩ := h.lifted x y₀ l₀ hy₀
      refine ⟨B'.rename (Ren.lift (Ren.liftN _ Ren.weaken)), ?_,
        hL.renameAbstraction (α := Ren.weaken) (α' := Ren.weaken)
          (Lifting.Substitutes.ofLift (e := e) h.motive') _⟩
      show (θ' y₀).rename (Ren.liftN _ Ren.weaken) = _
      rw [hB']
      exact Term.rename_extend_snoc _ _ Ren.weaken B'

/-- A lifting instantiated, under `n` new variables of the scopes. -/
theorem liftN : (n : Nat) → {Γ' Γ Δ' Δ : Scope} → {θ : Subst k Γ Δ} → {θ' : Subst k Γ' Δ'} →
    {ρ : Lifting k Δ' Δ} → {ρ' : Lifting k Γ' Γ} → {ν : Nesting Name Δ} →
      Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
        Lifting.Instantiates sig v (Subst.liftN n θ) (Subst.liftN n θ') (ρ.liftN n) (ρ'.liftN n)
          (Nesting.liftN n @ν)
  | 0, _, _, _, _, _, _, _, _, _, h => h
  | n + 1, Γ', Γ, Δ', Δ, _, _, _, _, _, h =>
    liftN (Γ' := .var :: Γ') (Γ := .var :: Γ) (Δ' := .var :: Δ') (Δ := .var :: Δ) n h.lift

/-- A lifting instantiated, in scopes extended by a new entry. -/
theorem weaken {e : Scope.Entry} (h : Lifting.Instantiates sig v θ θ' ρ ρ' @ν) :
    Lifting.Instantiates sig v θ (Subst.lift (e := e) θ') ρ.weaken ρ'.weaken @ν where
  ren := fun {a} x => by
    show (θ' (ρ.ren x)).rename (Ren.liftN a.params.length Ren.weaken) = _
    rw [h.ren x]
    exact Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := ρ'.ren)
      (α₃ := fun y => (ρ'.ren y).succ) fun _ => rfl) _
  motive' := fun x => by
    show (ρ'.motive x).map _ = none
    rw [h.motive' x]
    rfl
  plain := fun x hx => h.plain x (Option.map_eq_none_iff.1 (hx : (ρ.motive x).map _ = none))
  lifted := fun x y m hx => by
    obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1
      (hx : (ρ.motive x).map (Prod.map .succ id) = some (y, m))
    cases he
    obtain ⟨B', hB', hL⟩ := h.lifted x y₀ l₀ hy₀
    refine ⟨B'.rename (Ren.lift (Ren.liftN _ Ren.weaken)), ?_, ?_⟩
    · show (θ' y₀).rename (Ren.liftN _ Ren.weaken) = _
      rw [hB']
      exact Term.rename_extend_snoc _ _ Ren.weaken B'
    · have h' := hL.renameAbstraction (α := fun x => x) (α' := Ren.weaken)
        (Lifting.Substitutes.ofWeaken (e := e) h.motive') _
      rwa [Term.rename_id_of (Ren.liftN_id_of _ fun _ => rfl)] at h'

/-- A term renamed by a lifting and then substituted is the term substituted and then renamed by
the lifting instantiated, under `n` new variables. -/
theorem subst_rename (h : Lifting.Instantiates sig v θ θ' ρ ρ' @ν) (n : Nat)
    (t : Term k (Δ.extend n)) :
    (t.rename (Ren.liftN n ρ.ren)).subst (Subst.liftN n θ') =
      (t.subst (Subst.liftN n θ)).rename (Ren.liftN n ρ'.ren) :=
  (Term.subst_rename_of (fun _ => rfl) t).trans
    (Term.rename_subst_of (fun x => (Subst.liftN_rename_comm_of n h.ren x).symm) t).symm

end Lifting.Instantiates

/-! ## Types Without Position -/

/-- A type in which no variable with a position occurs, where no declared type holds one, has no
position. -/
theorem Term.nest_eq_plain_of_avoids {α : Type} {Γ : Scope} {ν : Nesting α Γ} {A : Term k Γ}
    (h : ∀ {e : Scope.Entry} (x : Var Γ e), ν x ≠ .plain → A.Avoids x) :
    A.nest (fun _ => none) @ν = .plain := by
  cases hp : (A.nest (fun _ => none) @ν).isPlain with
  | true => exact Nest.eq_plain_of_isPlain hp
  | false =>
    obtain ⟨e, x, hx, hfree⟩ := Term.exists_of_nest A fun h' => by
      rw [h'] at hp
      exact nomatch hp
    exact absurd (h x hx) hfree

/-- Arguments lifted at nestings none of which has a position are lifted at no nesting. -/
theorem InstanceArgs.Lifts.of_all_isPlain :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        ns.all Nest.isPlain = true → InstanceArgs.Lifts sig v ρ [] as S ms as'
  | _, _, _, _, _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, ns, _, _, _, _, _, _, .lifted has hB, hns => by
    cases ns with
    | nil => exact .lifted has hB
    | cons n ns =>
      rw [List.all_cons, Bool.and_eq_true] at hns
      have hn : n = .plain := Nest.eq_plain_of_isPlain hns.1
      subst hn
      exact .lifted (has.of_all_isPlain hns.2) hB
  | _, _, _, ns, _, _, _, _, _, _, .absent has hB hn, hns => by
    cases ns with
    | nil => exact .absent has hB hn
    | cons n ns =>
      rw [List.all_cons, Bool.and_eq_true] at hns
      exact .absent (has.of_all_isPlain hns.2) hB rfl

/-- Arguments lifted at their nestings are lifted at the nestings of the arguments of the nesting
of their instance. -/
theorem InstanceArgs.Lifts.ofArgs_args {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} {Δ : Scope} {as : InstanceArgs k Γ Δ} {S : List Nat}
    {ms : List (Lifting.Result k)} {Δ' : Scope} {as' : InstanceArgs k Γ' Δ'}
    (h : InstanceArgs.Lifts sig v ρ ns as S ms as') :
    InstanceArgs.Lifts sig v ρ (Nest.ofArgs ns).args as S ms as' := by
  unfold Nest.ofArgs
  split
  · next hns => exact h.of_all_isPlain hns
  · exact h

/-! ## Instantiation -/

mutual

/-- A type lifted at no position, substituted by an instantiation of its lifting, is the type
substituted, lifted by the lifting instantiated, at the term substituted and at the nesting of the
type, where the variables have the nestings of the instantiation, of the same result. -/
theorem Term.Lifts.instantiate :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m → n = .plain →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
          Term.Lifts sig v ρ' (A.nest (fun _ => none) @ν) (e.subst θ') (A.subst θ) (A'.subst θ') m
  | _, _, ρ, _, e, _, _, _, .var (x := x) (y := y) (m := m) (ts := ts) hx _, _, _, _, θ, θ', ρ',
      _, hI => by
    obtain ⟨B', hB', hL⟩ := hI.lifted x y m hx
    have e₁ : (ts.rename ρ.ren).subst θ' = (ts.subst θ).rename ρ'.ren :=
      (Args.subst_rename_of (fun _ => rfl) ts).trans
        (Args.rename_subst_of (fun x => (hI.ren x).symm) ts).symm
    rw [Term.subst, Term.subst, Args.subst_snoc, e₁, hB']
    exact hL.instantiateAbstraction hI.motive' (e.subst θ') (ts.subst θ)
  | _, _, _, _, _, _, _, _, .block _, hn, _, _, _, _, _, _, _ => nomatch hn
  | _, _, _, _, _, _, _, _, .inst h hD _ hqp hl has hS hL hπ, hn, _, _, _, _, _, _, hI => by
    subst hn
    simp only [Term.subst, InstanceArgs.subst]
    exact Term.Lifts.inst h hD (fun E => Nest.ofArgs_ne_direct _ E) hqp hl
      (has.instantiate rfl hI).ofArgs_args hS hL (hπ.inst_congr _ _ _)

/-- The arguments of an instance lifted at no position, substituted by an instantiation of their
lifting, are the arguments substituted, lifted by the lifting instantiated, at their nestings, at
the same parameters and of the same results. -/
theorem InstanceArgs.Lifts.instantiate :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' → ns = [] →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
          InstanceArgs.Lifts sig v ρ' (as.nest (fun _ => none) @ν) (as.subst θ) S ms
            (as'.subst θ')
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _ => .nil
  | _, _, _, _, _, _, _, _, _, _, .lifted (a := a) (B := B) (B' := B') has hB, hns, _, _, θ, θ',
      _, _, hI => by
    subst hns
    have hB' := hB.instantiate rfl (hI.liftN a.params.length).weaken
    rw [Term.var₀_zero_subst_lift] at hB'
    rw [InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst,
      hI.subst_rename a.params.length B,
      Term.subst_extend_snoc a.params Lifting.termParam θ' B']
    exact InstanceArgs.Lifts.lifted (has.instantiate rfl hI) hB'
  | _, _, _, _, _, _, _, _, _, _, .absent (a := a) (B := B) has hB _, hns, _, _, _, _, _, ν,
      hI => by
    subst hns
    have hN := hI.liftN a.params.length
    rw [InstanceArgs.subst, InstanceArgs.subst, hI.subst_rename a.params.length B]
    refine InstanceArgs.Lifts.absent (has.instantiate rfl hI)
      (fun y hy => nomatch (hN.motive' y).symm.trans (Option.eq_some_of_isSome hy))
      (Term.nest_eq_plain_of_avoids fun z hz => hB z ?_)
    cases hm : (Lifting.liftN a.params.length _).motive z with
    | none => exact absurd (hN.plain z hm) hz
    | some _ => rfl

end

end Sic.Core
