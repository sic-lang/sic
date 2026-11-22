module

public import Sic.Core.Lifting.Instantiation
import Sic.Core.Lifting.Shape
import Sic.Core.Substitution.Closed
import Sic.Core.Substitution.Levels
import Sic.Core.Substitution.Nesting
import Sic.Core.Syntax.Signature

/-!
# Liftings at the Observations of a Term

The result of a destructor of the lifting of a codata type of annex 13 of RFC 36, at an instance of
the lifting, at arguments lifted and at a term `t` of the instance lifted, is the result of the
destructor that it lifts, at the arguments of the instance and at the observations of `t`, lifted
at the observation of `t` by this destructor: the type of the recursive result of this observation.

The declaration lifts this result at the parameters of the type, where a parameter lifted becomes
its motive; the instance gives each parameter its argument and each motive the argument lifted, so
that the result is the instantiation of a lifting, whose nesting is that of the result of the
destructor, where the parameters have the nestings of the arguments.

The substitution of the destructors before a position by the observations of a term gives a
variable an observation, without position, or a variable of the scope at arguments: the nesting of a
type substituted by such a substitution is the nesting of the type.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Nestings of the Parameters of an Instance -/

/-- No parameter has a position at an instance none of whose arguments has a nesting. -/
theorem Nesting.ofArgs_nil {α : Type} {Δ : Scope} {a : Scope.Entry} (x : Var Δ a) :
    Nesting.ofArgs (α := α) [] x = .plain := by
  cases x <;> rfl

/-- The last parameter has the nesting of the last argument, the first of the nestings. -/
theorem Nesting.ofArgs_zero {α : Type} {Δ : Scope} {e : Scope.Entry} (ns : List (Nest α)) :
    Nesting.ofArgs (Δ := e :: Δ) ns .zero = ns.headD .plain := by
  cases ns <;> rfl

/-- A parameter before the last one has its nesting among the nestings after the first one. -/
theorem Nesting.ofArgs_succ {α : Type} {Δ : Scope} {e a : Scope.Entry} (ns : List (Nest α))
    (x : Var Δ a) : Nesting.ofArgs (Δ := e :: Δ) ns (.succ x) = Nesting.ofArgs ns.tail x := by
  cases ns with
  | nil => exact (Nesting.ofArgs_nil x).symm
  | cons _ _ => rfl

/-! ## Nesting of a Type Substituted -/

/-- The substitution `θ` keeps the nestings `ν` of the variables of its scope, at the nestings `ν'`
of the variables of the other: it gives a variable without position an observation, or it gives a
variable a variable with its nesting, at arguments. -/
def Subst.Nests {α : Type} {Γ Δ : Scope} (θ : Subst k Γ Δ) (ν : Nesting α Δ) (ν' : Nesting α Γ) :
    Prop :=
  ∀ {e : Scope.Entry} (x : Var Δ e),
    (ν x = .plain ∧
      ∃ (Ξ : Scope) (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
        (as : InstanceArgs k (Γ.extend e.params.length) Ξ) (t : Term k (Γ.extend e.params.length))
        (d : Name) (bs : Terms k (Γ.extend e.params.length)), θ x = .obs D qs ls ps as t d bs) ∨
      ∃ (y : Var Γ e) (us : Args k (Γ.extend e.params.length) e.params),
        θ x = .var (y.weakenN e.params.length) us ∧ ν' y = ν x

/-- A substitution that keeps the nestings keeps them under a new entry. -/
theorem Subst.Nests.lift {α : Type} {Γ Δ : Scope} {e₀ : Scope.Entry} {θ : Subst k Γ Δ}
    {ν : Nesting α Δ} {ν' : Nesting α Γ} (h : Subst.Nests θ @ν @ν') :
    Subst.Nests (Subst.lift (e := e₀) θ) (Nesting.lift @ν) (Nesting.lift @ν') := by
  intro e x
  cases x with
  | zero => exact .inr ⟨.zero, Args.bound _, rfl, rfl⟩
  | succ x =>
    have e' : Subst.lift (e := e₀) θ (.succ x) = (θ x).rename (Ren.liftN _ Ren.weaken) := rfl
    rcases h x with ⟨hν, Ξ, D, qs, ls, ps, as, t, d, bs, hθ⟩ | ⟨y, us, hθ, hν⟩
    · rw [show θ x = _ from hθ, Term.rename] at e'
      exact .inl ⟨hν, _, _, _, _, _, _, _, _, _, e'⟩
    · rw [show θ x = _ from hθ, Term.rename, Ren.liftN_weakenN] at e'
      exact .inr ⟨.succ y, _, e', hν⟩

/-- A substitution that keeps the nestings keeps them under new variables. -/
theorem Subst.Nests.liftN {α : Type} :
    (n : Nat) → {Γ Δ : Scope} → {θ : Subst k Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      Subst.Nests θ @ν @ν' →
        Subst.Nests (Subst.liftN n θ) (Nesting.liftN n @ν) (Nesting.liftN n @ν')
  | 0, _, _, _, _, _, h => h
  | n + 1, Γ, Δ, _, _, _, h => Subst.Nests.liftN n (Γ := .var :: Γ) (Δ := .var :: Δ) h.lift

/-- A substitution that keeps the nestings, followed by an observation for a new entry, without
position, keeps them. -/
theorem Subst.Nests.snocObs {α : Type} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ν : Nesting α Δ}
    {ν' : Nesting α Γ} (h : Subst.Nests θ @ν @ν') {e : Scope.Entry} {Ξ : Scope} (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k (Γ.extend e.params.length) Ξ) (t : Term k (Γ.extend e.params.length))
    (d : Name) (bs : Terms k (Γ.extend e.params.length)) :
    Subst.Nests (Subst.snoc (e := e) θ (.obs D qs ls ps as t d bs)) (Nesting.lift @ν) @ν' := by
  intro a x
  cases x with
  | zero => exact .inl ⟨rfl, Ξ, D, qs, ls, ps, as, t, d, bs, rfl⟩
  | succ x => exact h x

mutual

/-- A type substituted by a substitution that keeps the nestings has the nesting of the type, where
no declared type holds a position. -/
theorem Term.nest_subst_of {α : Type} :
    {Γ Δ : Scope} → {θ : Subst k Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      Subst.Nests θ @ν @ν' → (A : Term k Δ) →
        (A.subst θ).nest (fun _ => none) @ν' = A.nest (fun _ => none) @ν
  | _, _, θ, _, _, h, .var x ts => by
    rw [Term.subst]
    rcases h x with ⟨hν, Ξ, D, qs, ls, ps, as, t, d, bs, hθ⟩ | ⟨y, us, hθ, hν⟩
    · rw [show θ x = _ from hθ, Term.instantiate_eq_subst₀, Term.subst₀]
      exact hν.symm
    · rw [show θ x = _ from hθ, Term.instantiate_eq_subst₀, Term.subst₀_var,
        Args.toSubst₀_weakenN]
      exact hν
  | _, _, _, _, _, h, .inst _ _ _ _ as => by
    rw [Term.subst, Term.nest, Term.nest, InstanceArgs.nest_subst_of h as]
  | _, _, _, _, _, _, .sort _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .const _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, .equality .. | _, _, _, _, _, _, .refl ..
  | _, _, _, _, _, _, .transp .. | _, _, _, _, _, _, .propExt .. | _, _, _, _, _, _, .coind .. => by
    rw [Term.subst]; rfl

/-- The arguments of an instance substituted by a substitution that keeps the nestings have the
nestings of the arguments, where no declared type holds a position. -/
theorem InstanceArgs.nest_subst_of {α : Type} :
    {Γ Δ Ξ : Scope} → {θ : Subst k Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      Subst.Nests θ @ν @ν' → (as : InstanceArgs k Δ Ξ) →
        (as.subst θ).nest (fun _ => none) @ν' = as.nest (fun _ => none) @ν
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, h, .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.nest, InstanceArgs.nest,
      Term.nest_subst_of (h.liftN _) B, InstanceArgs.nest_subst_of h as]

end

/-- The substitution of the destructors before a position by observations keeps the nestings of
the variables of the scope of the position, where the destructors have no position, when the
substitution of the scope of the destructors keeps the nestings of its variables. -/
theorem Destructors.Pos.nests {α : Type} {k' : Nat} {Γ' : Scope}
    {o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)}
    (ho : ∀ d ps', ∃ (Ξ : Scope) (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k (Γ'.extend ps'.length) Ξ)
      (t : Term k (Γ'.extend ps'.length)) (d' : Name) (bs : Terms k (Γ'.extend ps'.length)),
      o d ps' = .obs D qs ls ps as t d' bs)
    {ν' : Nesting α Γ'} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {θ : Subst k Γ' Γ} → {ν : Nesting α Γ} → Subst.Nests θ @ν @ν' →
        Subst.Nests (hd.obsSubst o θ) (hd.nesting @ν) @ν'
  | _, _, _, _, _, _, _, .here, _, _, h => h
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (ψ' := ψ') hd, _, _, h => by
    obtain ⟨Ξ, D, qs, ls, ps, as, t, d'', bs, e⟩ := ho d' ps'
    refine hd.nests ho ?_
    show Subst.Nests (Subst.snoc (e := .secondOrder ps' ψ') _ (o d' ps')) _ _
    rw [e]
    exact h.snocObs (e := .secondOrder ps' ψ') D qs ls ps as t d'' bs

/-! ## Telescopes Used More -/

/-- A telescope whose entries are used more, at instantiated levels. -/
theorem Telescope.scale_substLevels {k' : Nat} (r : Grade) (ls' : Fin k → Level k') :
    {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      (Θ.scale r).substLevels ls' = (Θ.substLevels ls').scale r
  | _, _, .nil => rfl
  | _, _, .cons _ p A Θ =>
    congrArg (Telescope.cons .unrestrictedUnrestricted (p.scale r) (A.substLevels ls'))
      (Telescope.scale_substLevels r ls' Θ)

/-- A telescope whose entries are used more, substituted. -/
theorem Telescope.scale_subst (r : Grade) :
    {Γ Δ : Scope} → {ps : List Parameter} → (θ : Subst k Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.scale r).subst θ = (Θ.subst θ).scale r
  | _, _, _, _, .nil => rfl
  | _, _, _, θ, .cons _ p A Θ =>
    congrArg (Telescope.cons .unrestrictedUnrestricted (p.scale r) (A.subst θ))
      (Telescope.scale_subst r (Subst.lift θ) Θ)

/-! ## Destructors of a Lifting at a Position -/

/-- A term over as many variables as two equal numbers, brought to the other number and back, is
the term. -/
theorem Term.cast_cast {Γ : Scope} {n m : Nat} (h : n = m) (h' : m = n) (t : Term k (Γ.extend n)) :
    (h' ▸ (h ▸ t : Term k (Γ.extend m)) : Term k (Γ.extend n)) = t := by
  subst h
  rfl

/-- The destructor of a lifting at a position, which lifts the destructor of the same name at its
position in destructors with distinct names: its arguments are the arguments of this destructor,
at the observations by the destructors before it, used `r` times more, and its result is the result
of this destructor, at these observations, lifted at the observation by it.
The lifting of the scope of its position is the lifting of the destructors, in the scope extended
by the destructors of the lifting before the position, which the substitution of the destructors
before a position of the lifting leaves out. -/
theorem Destructors.Lifts.pos {Γ₀ : Scope} {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)} :
    {Γ' : Scope} → {ρ : Lifting k Γ' Γ₀} → {Ξ₀ : Scope} → {θ : Subst k Γ₀ Ξ₀} → {ns : List Name} →
      {ds : Destructors k Ξ₀ ns} → {ns' : List Name} → {ds' : Destructors k Γ' ns'} →
      Destructors.Lifts sig v κ o ρ @θ ds ds' → ns.Nodup →
      ∀ {d : Name} {p q ς : Grade} {ps : List Parameter} {Ξ : Scope} {Θ : Telescope k Ξ ps}
        {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
        (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) {p' q' ς' : Grade} {ps' : List Parameter}
        {Ξ' : Scope} {Θ' : Telescope k Ξ' ps'} {B' : Term k (Ξ'.extend ps'.length)}
        {ψ' : ResultOwnership Grade ps'.length}
        (hd' : Destructors.Pos d p' q' ς' ds' Ξ' Θ' B' ψ'),
        ∃ (m : Lifting.Result k) (hps : ps' = ps.map (Parameter.scale (v.recursion * m.factor)))
          (ρ₁ : Lifting k Ξ' Γ₀) (β : Ren Ξ' Γ'),
          (∀ {a} (x : Var Γ₀ a), ρ₁.ren x = β (ρ.ren x)) ∧
          (∀ {a} (x : Var Γ₀ a),
            ρ₁.motive x = (ρ.motive x).map (Prod.map (fun y => β y) id)) ∧
          (∀ {k'' : Nat} {Γ'' : Scope}
            (o' : Name → (ps : List Parameter) → Term k'' (Γ''.extend ps.length))
            (θ' : Subst k'' Γ'' Γ') {a} (z : Var Γ' a), hd'.obsSubst o' @θ' (β z) = θ' z) ∧
          (hps ▸ Θ' : Telescope k Ξ' (ps.map (Parameter.scale (v.recursion * m.factor)))) =
            ((Θ.subst (hd.obsSubst o @θ)).rename ρ₁.ren).scale (v.recursion * m.factor) ∧
          Term.Lifts sig v (ρ₁.liftN ps.length) .plain
            ((o d ps).rename (Ren.liftN ps.length ρ₁.ren))
            (B.subst (Subst.liftN ps.length (hd.obsSubst o @θ)))
            (((congrArg List.length hps).trans (List.length_map _)) ▸ B') m
  | _, _, _, _, _, _, _, _, .nil, _ => fun hd => nomatch hd
  | _, ρ, _, _, _, _, _, _, .lifted (B' := B₀') (m := m₀) hB _ hds, hnd => by
    intro hd p' q' ς' ps' Ξ' Θ' B' ψ' hd'
    have hnd' := List.nodup_cons.1 hnd
    cases hd' with
    | here =>
      cases hd with
      | here =>
        exact ⟨m₀, rfl, ρ, fun z => z, fun _ => rfl, fun x => by cases ρ.motive x <;> rfl,
          fun {_ _} _ _ {_} _ => rfl, rfl, hB.congr rfl rfl rfl (Term.cast_cast _ _ B₀').symm⟩
      | there hd₀ => exact absurd hd₀.mem hnd'.1
    | there hd'' =>
      cases hd with
      | here => exact absurd ((Destructors.Lifts.sublist hds).subset hd''.mem) hnd'.1
      | there hd₀ =>
        obtain ⟨m, hps, ρ₁, β, hr, hm, ho', hΘ, hL⟩ :=
          Destructors.Lifts.pos hds hnd'.2 hd₀ hd''
        refine ⟨m, hps, ρ₁, fun z => β (.succ z), fun x => hr x, fun x => ?_,
          fun {_ _} o' θ' {_} z => ho' o' _ (.succ z), hΘ, hL⟩
        rw [hm x]
        show ((ρ.motive x).map _).map _ = _
        cases ρ.motive x <;> rfl
  | _, _, _, _, _, _, _, _, .absent _ hds, hnd => by
    intro hd p' q' ς' ps' Ξ' Θ' B' ψ' hd'
    have hnd' := List.nodup_cons.1 hnd
    cases hd with
    | here => exact absurd ((Destructors.Lifts.sublist hds).subset hd'.mem) hnd'.1
    | there hd₀ => exact Destructors.Lifts.pos hds hnd'.2 hd₀ hd'

/-! ## Arguments Lifted as an Instantiation -/

/-- The instantiation of the lifting of parameters by arguments lifted, followed by an argument
lifted and its motive, for a parameter lifted. -/
theorem Lifting.Instantiates.consLifted {Γ' Γ Δ' Δ : Scope} {ρ : Lifting k Γ' Γ}
    {ρb : Lifting k Δ' Δ} {a : Scope.Entry} {ns : List (Nest Name)} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ'} {B : Term k (Γ.extend a.params.length)}
    {B' : Term k (.var :: Γ'.extend a.params.length)} {m : Lifting.Result k}
    (h : Lifting.Instantiates sig v as.toSubst as'.toSubst ρb ρ (Nesting.ofArgs ns.tail))
    (hB : Term.Lifts sig v (ρ.liftN a.params.length).weaken (ns.headD .plain) (.var₀ .zero) B B'
      m) :
    (b : Bool) → b = true → ∃ hΔ : a.motive :: a :: Δ' = Scope.liftedCons b a Δ',
      Lifting.Instantiates sig v (InstanceArgs.snoc as B).toSubst
        (hΔ ▸ InstanceArgs.snoc (e := a.motive)
          (.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren)))
          (Scope.extend_snoc Γ' a.params Lifting.termParam ▸ B')).toSubst
        (Lifting.cons m b ρb) ρ (Nesting.ofArgs ns)
  | true, _ =>
    ⟨rfl, {
      ren := fun x =>
        match x with
        | .zero => rfl
        | .succ x => h.ren x
      motive' := h.motive'
      plain := fun x =>
        match x with
        | .zero => fun hx => nomatch hx
        | .succ x => fun hx =>
          (Nesting.ofArgs_succ ns x).trans
            (h.plain x (Option.map_eq_none_iff.1 (hx : (ρb.motive x).map _ = none)))
      lifted := fun x =>
        match x with
        | .zero => fun y l' hx => by
          cases hx
          exact ⟨B', rfl, hB.congr (Nesting.ofArgs_zero ns).symm rfl rfl rfl⟩
        | .succ x => fun y l' hx => by
          obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1
            (hx : (ρb.motive x).map (Prod.map (fun y => .succ (.succ y)) id) = some (y, l'))
          cases he
          obtain ⟨B₀', hB₀', hL⟩ := h.lifted x y₀ l₀ hy₀
          exact ⟨B₀', hB₀', hL.congr (Nesting.ofArgs_succ ns x).symm rfl rfl rfl⟩ }⟩
  | false, hb => nomatch hb

/-- The instantiation of the lifting of parameters by arguments lifted, followed by an argument
kept, without position, for a parameter that is not lifted. -/
theorem Lifting.Instantiates.consAbsent {Γ' Γ Δ' Δ : Scope} {ρ : Lifting k Γ' Γ}
    {ρb : Lifting k Δ' Δ} {a : Scope.Entry} {ns : List (Nest Name)} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ'} {B : Term k (Γ.extend a.params.length)} (m : Lifting.Result k)
    (h : Lifting.Instantiates sig v as.toSubst as'.toSubst ρb ρ (Nesting.ofArgs ns.tail))
    (hn : ns.headD .plain = .plain) :
    (b : Bool) → b = false → ∃ hΔ : a :: Δ' = Scope.liftedCons b a Δ',
      Lifting.Instantiates sig v (InstanceArgs.snoc as B).toSubst
        (hΔ ▸ InstanceArgs.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren))).toSubst
        (Lifting.cons m b ρb) ρ (Nesting.ofArgs ns)
  | false, _ =>
    ⟨rfl, {
      ren := fun x =>
        match x with
        | .zero => rfl
        | .succ x => h.ren x
      motive' := h.motive'
      plain := fun x =>
        match x with
        | .zero => fun _ => (Nesting.ofArgs_zero ns).trans hn
        | .succ x => fun hx =>
          (Nesting.ofArgs_succ ns x).trans
            (h.plain x (Option.map_eq_none_iff.1 (hx : (ρb.motive x).map _ = none)))
      lifted := fun x =>
        match x with
        | .zero => fun _ _ hx => nomatch hx
        | .succ x => fun y l' hx => by
          obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1
            (hx : (ρb.motive x).map (Prod.map .succ id) = some (y, l'))
          cases he
          obtain ⟨B₀', hB₀', hL⟩ := h.lifted x y₀ l₀ hy₀
          exact ⟨B₀', hB₀', hL.congr (Nesting.ofArgs_succ ns x).symm rfl rfl rfl⟩ }⟩
  | true, hb => nomatch hb

/-- The arguments of an instance lifted, by a lifting that lifts no variable, are an instantiation
of the lifting of the parameters at the positions of the arguments lifted, whose motives have the
results of these: the arguments lifted are arguments of the parameters lifted, they give each
parameter its argument, renamed, and the motive of each parameter lifted its argument lifted, at
the nesting of this argument.
The positions `S₂` are those of the relation among the positions of the parameters, and `mv` gives
the results of the relation. -/
theorem InstanceArgs.Lifts.instantiates {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) :
    {ns : List (Nest Name)} → {Δ : Scope} → {as : InstanceArgs k Γ Δ} → {S : List Nat} →
      {ms : List (Lifting.Result k)} → {Δ' : Scope} → {as' : InstanceArgs k Γ' Δ'} →
      InstanceArgs.Lifts sig v ρ ns as S ms as' → ∀ (S₂ : List Nat) (mv : Nat → Lifting.Result k),
        (∀ i, i < Δ.length → (i ∈ S₂ ↔ i ∈ S)) →
          (∀ j (h₁ : j < S.length) (h₂ : j < ms.length), mv S[j] = ms[j]) →
            ∃ hΔ : Δ' = Δ.lifted S₂,
              Lifting.Instantiates sig v as.toSubst (hΔ ▸ as').toSubst (Lifting.base S₂ mv Δ) ρ
                (Nesting.ofArgs ns)
  | _, _, _, _, _, _, _, .nil, _, _, _, _ =>
    ⟨rfl, {
      ren := fun x => nomatch x
      motive' := hρ
      plain := fun x => nomatch x
      lifted := fun x => nomatch x }⟩
  | _, _, _, _, _, _, _, .lifted (Δ := Δ₀) (S := S) (ms := ms) (m := m) has hB, S₂, mv, hS,
      hlv => by
    have hlen := has.length_eq
    obtain ⟨hΔ, ih⟩ := InstanceArgs.Lifts.instantiates hρ has S₂ mv
      (fun i hi => (hS i (Nat.lt_succ_of_lt hi)).trans
        ⟨fun h => (List.mem_append.1 h).elim id fun h' =>
          absurd (List.mem_singleton.1 h') (Nat.ne_of_lt hi), List.mem_append_left _⟩)
      (fun j h₁ h₂ => by
        have h := hlv j (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)
        rwa [List.getElem_append_left h₁, List.getElem_append_left h₂] at h)
    subst hΔ
    have hl : mv Δ₀.length = m := by
      have h := hlv S.length (by simp) (by simp [hlen])
      simpa [hlen] using h
    subst hl
    exact ih.consLifted hB _
      (decide_eq_true ((hS _ (Nat.lt_succ_self _)).2 (List.mem_append_right _ (.head _))))
  | _, _, _, _, _, _, _, .absent (Δ := Δ₀) has _ hn, S₂, mv, hS, hlv => by
    obtain ⟨hΔ, ih⟩ := InstanceArgs.Lifts.instantiates hρ has S₂ mv
      (fun i hi => hS i (Nat.lt_succ_of_lt hi)) hlv
    subst hΔ
    exact ih.consAbsent (mv Δ₀.length) hn _
      (decide_eq_false fun h => Nat.lt_irrefl _ (has.lt _ ((hS _ (Nat.lt_succ_self _)).1 h)))

/-- The instantiation of a lifting by arguments, followed by a term and this term renamed, for a
variable that is not lifted, without position. -/
theorem Lifting.Instantiates.snocTerm {Γ' Γ Δ' Δ : Scope} {ρ : Lifting k Γ' Γ}
    {ρb : Lifting k Δ' Δ} {ν : Nesting Name Δ} {as : InstanceArgs k Γ Δ}
    {as' : InstanceArgs k Γ' Δ'}
    (h : Lifting.Instantiates sig v as.toSubst as'.toSubst ρb ρ @ν) (t : Term k Γ) :
    Lifting.Instantiates sig v (InstanceArgs.snoc (e := .var) as t).toSubst
      (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst (ρb.lift (e := .var)) ρ
      (Nesting.lift @ν) where
  ren := fun x =>
    match x with
    | .zero => rfl
    | .succ x => h.ren x
  motive' := h.motive'
  plain := fun x =>
    match x with
    | .zero => fun _ => rfl
    | .succ x => fun hx =>
      h.plain x (Option.map_eq_none_iff.1 (hx : (ρb.motive x).map _ = none))
  lifted := fun x =>
    match x with
    | .zero => fun _ _ hx => nomatch hx
    | .succ x => fun y l hx => by
      obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1
        (hx : (ρb.motive x).map (Prod.map .succ id) = some (y, l))
      cases he
      exact h.lifted x y₀ l₀ hy₀

/-- The instantiation of a lifting is one of the lifting in a scope with more entries, which a
renaming brings its variables and its motives to, by a substitution that gives the image of a
variable what the substitution of the instantiation gives this variable. -/
theorem Lifting.Instantiates.ofRen {Γ' Γ Δ' Δ Δ₂' : Scope} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρa : Lifting k Δ' Δ} {ρ : Lifting k Γ' Γ} {ν : Nesting Name Δ}
    (h : Lifting.Instantiates sig v θ θ' ρa ρ @ν) {θ₂' : Subst k Γ' Δ₂'} {ρ₂ : Lifting k Δ₂' Δ}
    (β : Ren Δ₂' Δ') (hθ : ∀ {a} (z : Var Δ' a), θ₂' (β z) = θ' z)
    (hr : ∀ {a} (x : Var Δ a), ρ₂.ren x = β (ρa.ren x))
    (hm : ∀ {a} (x : Var Δ a), ρ₂.motive x = (ρa.motive x).map (Prod.map (fun y => β y) id)) :
    Lifting.Instantiates sig v θ θ₂' ρ₂ ρ @ν where
  ren := fun x => by
    rw [hr x, hθ]
    exact h.ren x
  motive' := h.motive'
  plain := fun x hx => h.plain x (Option.map_eq_none_iff.1 ((hm x).symm.trans hx))
  lifted := fun x y l hx => by
    obtain ⟨⟨y₀, l₀⟩, hy₀, he⟩ := Option.map_eq_some_iff.1 ((hm x).symm.trans hx)
    cases he
    obtain ⟨B', hB', hL⟩ := h.lifted x y₀ l₀ hy₀
    exact ⟨B', (hθ y₀).trans hB', hL⟩

/-! ## Results of the Destructors of a Lifting -/

/-- A term over as many variables as two equal numbers, brought to the other number, at
instantiated levels and substituted under these variables. -/
theorem Term.substLevels_subst_cast {k' : Nat} {Γ Δ : Scope} {n m : Nat} (h : n = m)
    (ls' : Fin k → Level k') (θ : Subst k' Γ Δ) (B : Term k (Δ.extend n)) :
    ((h ▸ B : Term k (Δ.extend m)).substLevels ls').subst (Subst.liftN m θ) =
      (h ▸ (B.substLevels ls').subst (Subst.liftN n θ) : Term k' (Γ.extend m)) := by
  subst h
  rfl

/--
The result of a destructor `d` of the lifting of the codata type `D` at its parameters at the
positions `S`, as its declaration lifts it, in a signature `Σ₁`, at the levels of an instance of the
lifting, and the instantiation of its lifting by the arguments lifted `ā'` of this instance,
followed by a term `t` of the instance lifted, in a signature `Σ` whose names are distinct and
that has the type `D`: the result declared, substituted by this instantiation, is the result of the
destructor `d` of `D`, at the arguments `ā` and at the observations of `t` by the destructors
before it, with the nesting of this result, where the parameters have the nestings of the
arguments, and it is lifted at the observation of `t` by `d`.
The result declared is the result of `d` at the variables of the lifting and at the observations of
its parameter `y` by the destructors before `d`, a substitution that keeps the nestings of the
parameters, whatever they are.
The declaration lifts the result in the signature before the lifting, while the arguments of the
instance are lifted in the whole signature.
-/
theorem TypeDeclaration.Lifts.result {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    {sig₁ : Signature} (hsig : sig.Distinct) (hT : sig.HasCodataType D decl T)
    (hL : decl.Lifts sig₁ D S body)
    {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none)
    {qs : List Quality} {ls : List (Level k)} {ms : List (Lifting.Result k)} {ps : List Grade}
    (hqp : decl.AsMany qs ps) (hl : ls.length = decl.levels)
    (hq' : (qs ++ [v.quality]).length = decl.sorts + 1)
    (hl' : (ls ++ ms.map (·.level)).length = decl.levels + S.length)
    (hp' : (v.grades ps ms).length = decl.liftingGrades S)
    {nsA : List (Nest Name)} {as : InstanceArgs k Γ decl.scope}
    {as' : InstanceArgs k Γ' (decl.scope.lifted S)}
    (has : InstanceArgs.Lifts sig v ρ nsA as S ms as') (t : Term k Γ) {d : Name}
    {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps₁}
    {B : Term decl.levels (Ξ.extend ps₁.length)} {ψ : ResultOwnership Grade ps₁.length}
    (hd : Destructors.Pos d p q ς (T.body hqp.inst) Ξ Θ B ψ) {p' q' ς' : Grade}
    {ps₁' : List Parameter} {Ξ' : Scope} {Θ' : Telescope (decl.levels + S.length) Ξ' ps₁'}
    {B' : Term (decl.levels + S.length) (Ξ'.extend ps₁'.length)}
    {ψ' : ResultOwnership Grade ps₁'.length}
    (hd' : Destructors.Pos d p' q' ς'
      (body (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp')) Ξ' Θ' B' ψ')
    (o' : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) :
    ∃ (m : Lifting.Result k) (hps : ps₁' = ps₁.map (Parameter.scale (v.recursion * m.factor)))
      (ρ₁ : Lifting k Ξ' (.var :: decl.scope))
      (e₀ : Term k (Ξ'.extend ps₁.length))
      (A₀ : Term k (Scope.extend (.var :: decl.scope) ps₁.length))
      (A₀' : Term k (Ξ'.extend ps₁.length)),
      Term.Lifts sig₁ v (ρ₁.liftN ps₁.length) .plain e₀ A₀ A₀' m ∧
      Lifting.Instantiates sig v (InstanceArgs.snoc (e := .var) as t).toSubst
        (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst) ρ₁ ρ
        (Nesting.lift (Nesting.ofArgs nsA)) ∧
      (hps ▸ (Θ'.substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
          (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst) :
        Telescope k Γ' (ps₁.map (Parameter.scale (v.recursion * m.factor)))) =
        (((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)).rename
            ρ.ren).scale (v.recursion * m.factor) ∧
      A₀.nest (fun _ => none) (Nesting.liftN ps₁.length (Nesting.lift (Nesting.ofArgs nsA))) =
        B.nest (fun _ => none) (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs nsA))) ∧
      (∃ β : Subst (decl.levels + S.length) (.var :: decl.scope) Ξ,
        A₀ = ((B.substLevels (Level.lifted S.length)).subst (Subst.liftN ps₁.length β)).substLevels
          ((ls ++ ms.map (·.level)).getFin hl') ∧
        ∀ {α : Type} (ν : Nesting α decl.scope), Subst.Nests β (hd.nesting ν) (Nesting.lift ν)) ∧
      e₀.subst (Subst.liftN ps₁.length
          (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst)) =
        (t.observation D qs ls ps as d ps₁).rename (Ren.liftN ps₁.length ρ.ren) ∧
      A₀.subst (Subst.liftN ps₁.length (InstanceArgs.snoc (e := .var) as t).toSubst) =
        (B.substLevels (ls.getFin hl)).subst
          (Subst.liftN ps₁.length (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)) ∧
      A₀'.subst (Subst.liftN ps₁.length
          (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst)) =
        (((congrArg List.length hps).trans (List.length_map _)) ▸
          (B'.substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
            (Subst.liftN ps₁'.length
              (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst))) := by
  -- The destructors of the lifting are those of `T`, lifted, at each instance.
  obtain ⟨T₀, hT₀, hn₀, hb⟩ := hL
  cases eq_of_heq (hsig.hasCodataType_unique ⟨hT.1, hT₀, hn₀⟩ hT).2
  have hb' := hb (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp')
  rw [Instance.liftingVariables_ofLists qs ps v ms hqp.sorts hqp.grades,
    Instance.lifted_ofLists qs ps v.quality _ hqp.sorts hqp.grades] at hb'
  obtain ⟨m, hps, ρ₁, β, hr, hm, ho, hΘ, hL₀⟩ :=
    hb'.pos (hsig.destructors_nodup hT) (hd.substLevels (Level.lifted S.length)) hd'
  subst hps
  cases (hΘ : Θ' = _)
  -- The arguments lifted, followed by the term, instantiate the lifting of the position: the
  -- instance gives the motive of each parameter lifted the result of its argument lifted.
  obtain ⟨_, hI₀⟩ := has.instantiates hρ S
    (fun i => (decl.liftingMotive S (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp')
      i).substLevels ((ls ++ ms.map (·.level)).getFin hl'))
    (fun _ _ => Iff.rfl)
    (fun j h₁ h₂ => TypeDeclaration.liftingMotive_ofLists has.nodup hq' hl has.length_eq hl'
      hqp.grades
      hp' j h₁ h₂)
  have hI : Lifting.Instantiates sig v (InstanceArgs.snoc (e := .var) as t).toSubst
      (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst)
      (ρ₁.substLevels ((ls ++ ms.map (·.level)).getFin hl')) ρ (Nesting.lift (Nesting.ofArgs nsA)) := by
    have h₁ := Lifting.Instantiates.snocTerm hI₀ t
    rw [← Lifting.base_substLevels, ← Lifting.substLevels_lift] at h₁
    exact h₁.ofRen (fun z => β z) (fun z => ho _ _ z) (fun x => hr x) (fun x => by
      show (ρ₁.motive x).map _ = (((Lifting.base S _ decl.scope).lift.motive x).map _).map _
      rw [hm x]
      unfold TypeDeclaration.liftingScope
      cases (Lifting.base S _ decl.scope).lift.motive x <;> rfl)
  -- The observations of the parameter `y` of the lifting become those of the term.
  have hargs : (((InstanceArgs.identity (k := decl.levels + S.length) decl.scope).rename
        Ren.weaken).substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
      (InstanceArgs.snoc (e := .var) as t).toSubst = as := by
    rw [InstanceArgs.substLevels_rename, InstanceArgs.identity_substLevels]
    exact (InstanceArgs.subst_rename_of (α := Ren.weaken) (θ' := as.toSubst) (fun _ => rfl)
      _).trans (InstanceArgs.identity_subst_toSubst as)
  have hobs : ∀ d' ps',
      ((decl.liftedObservation D S.length hqp.inst d' ps').substLevels
          ((ls ++ ms.map (·.level)).getFin hl')).subst
        (Subst.liftN ps'.length (InstanceArgs.snoc (e := .var) as t).toSubst) =
      t.observation D qs ls ps as d' ps' := fun d' ps' => by
    have e_l : (List.ofFn (Level.lifted (k := decl.levels) S.length)).map
        (Level.subst ((ls ++ ms.map (·.level)).getFin hl')) = ls :=
      (List.map_ofFn ..).trans
        ((congrArg List.ofFn (Level.lifted_subst ls (ms.map fun m : Lifting.Result k => m.level) hl hl')).trans (List.ofFn_getFin ls hl))
    show ((Term.observation D (List.ofFn (qs.getFin hqp.sorts)) (List.ofFn (Level.lifted S.length))
      (List.ofFn (ps.getFin hqp.grades)) ((InstanceArgs.identity decl.scope).rename Ren.weaken)
      (.var₀ .zero) d' ps').substLevels _).subst _ = _
    rw [Term.observation_substLevels, Term.observation_subst, hargs, e_l, List.ofFn_getFin,
      List.ofFn_getFin]
    rfl
  have hθ₀ : ∀ {a} (y : Var decl.scope a),
      ((((InstanceArgs.identity (k := decl.levels + S.length) decl.scope).rename
          Ren.weaken).toSubst y).substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
        (Subst.liftN a.params.length (InstanceArgs.snoc (e := .var) as t).toSubst) =
      as.toSubst y := fun y => by
    rw [InstanceArgs.toSubst_substLevels, InstanceArgs.toSubst_subst, hargs]
  have hσ : ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst (decl.liftedObservation D S.length hqp.inst)
          ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst x).substLevels
          ((ls ++ ms.map (·.level)).getFin hl')).subst
        (Subst.liftN a.params.length (InstanceArgs.snoc (e := .var) as t).toSubst) =
      hd.obsSubst (t.observation D qs ls ps as) as.toSubst x := fun x => by
    have e₁ := hd.obsSubst_substLevels ((ls ++ ms.map (·.level)).getFin hl')
      (o := decl.liftedObservation D S.length hqp.inst)
      (o' := fun d' ps' => (decl.liftedObservation D S.length hqp.inst d'
        ps').substLevels ((ls ++ ms.map (·.level)).getFin hl'))
      (fun _ _ => rfl)
      (θ := ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst)
      (θ' := fun y => (((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst
        y).substLevels ((ls ++ ms.map (·.level)).getFin hl'))
      (fun _ => rfl) x
    rw [e₁]
    exact hd.obsSubst_subst (InstanceArgs.snoc (e := .var) as t).toSubst hobs (fun y => hθ₀ y) x
  -- The result lifted, at the levels and at the arguments of the instance.
  have hL₁ := (hL₀.congr rfl rfl
    (Term.subst_congr (Subst.liftN_congr ps₁.length fun x =>
      hd.obsSubst_posSubstLevels (Level.lifted S.length) _ _ x) _) rfl).substLevels
    ((ls ++ ms.map (·.level)).getFin hl')
  rw [Lifting.substLevels_liftN] at hL₁
  have hN : ∀ {α : Type} (ν : Nesting α decl.scope), Subst.Nests
      (hd.obsSubst (decl.liftedObservation D S.length hqp.inst)
        ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst)
      (hd.nesting ν) (Nesting.lift ν) := fun ν =>
    Destructors.Pos.nests (o := decl.liftedObservation D S.length hqp.inst)
      (ν' := Nesting.lift ν) (fun _ _ => ⟨_, _, _, _, _, _, _, _, _, rfl⟩) hd
      (θ := ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst)
      (ν := ν) fun x =>
        .inr ⟨.succ x, Args.bound _, InstanceArgs.identity_rename_toSubst Ren.weaken x, rfl⟩
  refine ⟨m.substLevels ((ls ++ ms.map (·.level)).getFin hl'), rfl, _, _, _, _, hL₁, hI, ?_, ?_,
    ⟨_, rfl, hN⟩, ?_, ?_, ?_⟩
  · refine (?_ : ∀ θ' : Subst k Γ' Ξ',
      (∀ {a} (x : Var (.var :: decl.scope) a), θ' (ρ₁.ren x) =
        ((InstanceArgs.snoc (e := .var) as t).toSubst x).rename
          (Ren.liftN a.params.length ρ.ren)) → Telescope.subst θ' _ = _) _ hI.ren
    intro θ' hθ'
    rw [Telescope.subst_congr (fun x =>
        hd.obsSubst_posSubstLevels (Level.lifted S.length) _ _ x) (Θ.substLevels _),
      Telescope.scale_substLevels, Telescope.scale_subst, Telescope.substLevels_rename,
      (Telescope.subst_rename_of (fun _ => rfl) _).trans
        (Telescope.rename_subst_of (fun x => (hθ' x).symm) _).symm,
      Telescope.substLevels_subst_of (ls' := (ls ++ ms.map (·.level)).getFin hl')
        (θ' := fun x =>
          (hd.obsSubst (decl.liftedObservation D S.length hqp.inst)
            ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst x).substLevels
            ((ls ++ ms.map (·.level)).getFin hl'))
        (fun _ => rfl),
      Telescope.subst_subst_of hσ, Telescope.substLevels_substLevels,
      Level.lifted_subst ls (ms.map fun m : Lifting.Result k => m.level) hl hl']
    rfl
  · rw [Term.nest_substLevels, Term.nest_subst_of (Subst.Nests.liftN ps₁.length (@hN _ (Nesting.ofArgs nsA))),
      Term.nest_substLevels]
  · rw [Term.substLevels_rename]
    exact (hI.subst_rename ps₁.length _).trans (congrArg (Term.rename _) (hobs d ps₁))
  · rw [Term.substLevels_subst_of (ls' := (ls ++ ms.map (·.level)).getFin hl')
        (θ' := Subst.liftN ps₁.length fun x =>
          (hd.obsSubst (decl.liftedObservation D S.length hqp.inst)
            ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst x).substLevels
            ((ls ++ ms.map (·.level)).getFin hl'))
        (Subst.liftN_substLevels_of ps₁.length fun _ => rfl),
      Term.subst_subst_of (Subst.liftN_subst_of ps₁.length hσ), Term.substLevels_substLevels,
      Level.lifted_subst ls (ms.map fun m : Lifting.Result k => m.level) hl hl']
  · exact Term.substLevels_subst_cast _ _ _ B'

/--
The result of a destructor `d` of the lifting of the codata type `D` at its parameters at the
positions `S`, in a signature whose names are distinct, at the instance of the lifting that the
instance `D.{s̄; l̄; p̄} ā` lifted at a term `t` is: at the arguments lifted `ā'` followed by `t`,
its arguments are the arguments of the destructor `d` of `D`, at the arguments `ā` and at the
observations of `t` by the destructors before it, used `r` times more, and its result is the
result of `d`, at these arguments and observations, lifted at the observation of `t` by `d`, at the
nesting of this result, where the parameters have the nestings of the arguments.
The destructors of the lifting before `d` are given any abstractions `o'`, on which neither its
arguments nor its result depend.
RFC: `\mathsf{inst}_{\uparrow}`
-/
theorem TypeDeclaration.Lifts.observation {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hsig : sig.Distinct) (hT : sig.HasCodataType D decl T) (hL : decl.Lifts sig D S body)
    {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none)
    {qs : List Quality} {ls : List (Level k)} {ms : List (Lifting.Result k)} {ps : List Grade}
    (hqp : decl.AsMany qs ps) (hl : ls.length = decl.levels)
    (hq' : (qs ++ [v.quality]).length = decl.sorts + 1)
    (hl' : (ls ++ ms.map (·.level)).length = decl.levels + S.length)
    (hp' : (v.grades ps ms).length = decl.liftingGrades S)
    {nsA : List (Nest Name)} {as : InstanceArgs k Γ decl.scope}
    {as' : InstanceArgs k Γ' (decl.scope.lifted S)}
    (has : InstanceArgs.Lifts sig v ρ nsA as S ms as') (t : Term k Γ) {d : Name}
    {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps₁}
    {B : Term decl.levels (Ξ.extend ps₁.length)} {ψ : ResultOwnership Grade ps₁.length}
    (hd : Destructors.Pos d p q ς (T.body hqp.inst) Ξ Θ B ψ) {p' q' ς' : Grade}
    {ps₁' : List Parameter} {Ξ' : Scope} {Θ' : Telescope (decl.levels + S.length) Ξ' ps₁'}
    {B' : Term (decl.levels + S.length) (Ξ'.extend ps₁'.length)}
    {ψ' : ResultOwnership Grade ps₁'.length}
    (hd' : Destructors.Pos d p' q' ς'
      (body (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp')) Ξ' Θ' B' ψ')
    (o' : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) :
    ∃ (m : Lifting.Result k) (hps : ps₁' = ps₁.map (Parameter.scale (v.recursion * m.factor))),
      (hps ▸ (Θ'.substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
          (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst) :
        Telescope k Γ' (ps₁.map (Parameter.scale (v.recursion * m.factor)))) =
        (((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)).rename
            ρ.ren).scale (v.recursion * m.factor) ∧
      Term.Lifts sig v (ρ.liftN ps₁.length)
        (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs nsA))))
        ((t.observation D qs ls ps as d ps₁).rename (Ren.liftN ps₁.length ρ.ren))
        ((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN ps₁.length (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
        (((congrArg List.length hps).trans (List.length_map _)) ▸
          (B'.substLevels ((ls ++ ms.map (·.level)).getFin hl')).subst
            (Subst.liftN ps₁'.length
              (hd'.obsSubst o' (InstanceArgs.snoc (e := .var) as' (t.rename ρ.ren)).toSubst)))
        m := by
  obtain ⟨m, hps, _, _, _, _, hL₁, hI, hΘ, h₁, -, h₂, h₃, h₄⟩ :=
    hL.result hsig hT hρ hqp hl hq' hl' hp' has t hd hd' o'
  exact ⟨m, hps, hΘ, (hL₁.instantiate rfl (hI.liftN ps₁.length)).congr h₁ h₂ h₃ h₄⟩

end Sic.Core
