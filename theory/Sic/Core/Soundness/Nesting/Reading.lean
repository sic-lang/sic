module

public import Sic.Core.Meaning.Levels
public import Sic.Core.Soundness.Signature
public import Sic.Core.Typing
import Sic.Core.Positivity.Nesting
import Sic.Core.Positivity.Substitution
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Substitution
import Sic.Core.Substitution.Nesting
import Sic.Core.Typing.Induction
import Sic.Core.Typing.Inversion
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature

/-!
# Types Read at Their Nestings

A type that is strictly positive in variables, as annex 15 of RFC 36 says it, is read by the graphs
of the nestings of annex 21, that of the equality and that of run time, at any closed types given
for these variables, when the graph reads them at their nestings.
This module holds what the two graphs share, stated of a reading `rd`, a property of two closed
types and of their nestings, which is the graph of the nestings of the equality, or that of run
time, reading both types with one relation.

The types given for the variables with a position have no meaning yet, as the types of a block
before its meaning, so that the judgments typed with these variables say nothing of them: the proof
carries, beside them, two equal closed substitutions of the context, at which every judgment is
meaningful, and which give the same abstractions to the variables without position.
What a variable with a position does not occur in is then the same at both, and has its meaning,
and a type whose nesting has a position is a variable with a position, read as given, or an
instance of a declared type whose arguments have positions, which each graph reads by its own
clause, `ReadsInstances`: it is an instance of a codata type none of whose destructors is
recursive, whose formation gives the strict positivity of its destructors and their typing in the
signature before it.

The destructors after a destructor whose result has a position are typed in its context, and are
those of the declaration renamed, which the strict positivity reads renamed: the properties are
stated of a type or of destructors renamed, the substitutions and the nestings being those of the
scope that the renaming reaches, so that no property of a renamed term has to be moved back to the
term.

The soundness of the typing is proved from these properties, which read it at the judgments of the
signatures before: they take it as a hypothesis, `TypingSound`.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-- Two pairs of closed substitutions of a scope `Γ'`, which the renaming `β` reaches from the
scope of a context: `(σ₁, σ₂)`, at which the judgments of the context are meaningful, and
`(σ₁', σ₂')`, which give the variables with a position, by the nestings `ν₁` and `ν₂`, types that
the reading `rd` reads at them, at the arguments at which it reads those of the first pair without
position, and which give the other variables what the first pair gives them.
The renaming is that of the destructors after a destructor on which they do not depend, which the
strict positivity reads renamed. -/
structure NestSubst {α I : Type} (sig : Signature) (ι : Interpretation)
    (rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop) {Γ' Γ : Scope}
    (ctx : Context 0 Γ) (β : Ren Γ' Γ) (ν₁ ν₂ : Nesting α Γ')
    (σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ') : Prop where
  /-- The two nestings give a position to the same variables. -/
  isPlain : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = (ν₂ x).isPlain
  /-- The first substitutions give the same abstraction to a variable without position. -/
  left : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = true → σ₁' x = σ₁ x
  /-- The second substitutions give the same abstraction to a variable without position. -/
  right : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = true → σ₂' x = σ₂ x
  /-- A variable with a position is given types read at its nestings. -/
  var : ∀ (x : Var Γ' .var), (ν₁ x).isPlain = false → ∀ s,
    rd s .plain .plain (σ₁ x) (σ₂ x) →
      rd s (ν₁ x) (ν₂ x) (σ₁' x) (σ₂' x)
  /-- A second-order variable of the context with a position is given abstractions whose instances
  at equal arguments of its telescope are read at its nestings. -/
  secondOrder : ∀ {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
    (X : Var Γ (.secondOrder ps ψ)) {Θ : Telescope 0 Γ ps} {A : Term 0 (Γ.extend ps.length)},
    ctx.SecondOrderIn X Θ A → (ν₁ (β X)).isPlain = false → ∀ s τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ.subst fun x => σ₁ (β x))) τ₁ τ₂ →
      rd s .plain .plain ((σ₁ (β X)).subst τ₁) ((σ₂ (β X)).subst τ₂) →
        rd s (ν₁ (β X)) (ν₂ (β X)) ((σ₁' (β X)).subst τ₁) ((σ₂' (β X)).subst τ₂)

/-- A second-order variable of a context is one of the context extended by a telescope, whose
telescope is its own, weakened. -/
theorem Context.SecondOrderIn.of_append {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → {ctx : Context k Γ} → (Θ : Telescope k Γ ps) →
      {ps' : List Parameter} → {ψ : ResultOwnership Grade ps'.length} →
      {X : Var Γ (.secondOrder ps' ψ)} → {Θ' : Telescope k (Γ.extend ps.length) ps'} →
      {A' : Term k ((Γ.extend ps.length).extend ps'.length)} →
      (ctx.append Θ).SecondOrderIn (X.weakenN ps.length) Θ' A' →
      ∃ (Θ₀ : Telescope k Γ ps') (A₀ : Term k (Γ.extend ps'.length)),
        ctx.SecondOrderIn X Θ₀ A₀ ∧ Θ' = Θ₀.rename (Ren.weakenN ps.length)
  | _, [], _, .nil, _, _, _, Θ', A', h => ⟨Θ', A', h, (Telescope.rename_id_of (fun _ => rfl) Θ').symm⟩
  | Γ, _ :: ps, ctx, .cons _ _ A Θ, _, _, X, _, _, h => by
    obtain ⟨Θ₁, A₁, h₁, rfl⟩ :=
      Context.SecondOrderIn.of_append (Γ := .var :: Γ) (ctx := ctx.var A) Θ (X := .succ X) h
    cases h₁ with
    | succVar h₀ =>
      exact ⟨_, _, h₀, Telescope.rename_rename_of (fun _ => rfl) _⟩

/-- A second-order variable of a context is one of a context equal to it up to its levels, with a
telescope equal to its own up to its levels. -/
theorem Context.SecondOrderIn.levelEquiv {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {ctx' : Context k Γ} {X : Var Γ (.secondOrder ps ψ)}
    {Θ' : Telescope k Γ ps} {A' : Term k (Γ.extend ps.length)}
    (hX : ctx'.SecondOrderIn X Θ' A') :
    ∀ {ctx : Context k Γ}, Context.LevelEquiv ctx ctx' →
      ∃ (Θ : Telescope k Γ ps) (A : Term k (Γ.extend ps.length)),
        ctx.SecondOrderIn X Θ A ∧ Telescope.LevelEquiv Θ Θ' := by
  induction hX with
  | zero =>
    intro ctx h
    cases h with
    | secondOrder _ _ hΘ _ => exact ⟨_, _, .zero, hΘ.rename _⟩
  | succVar _ ih =>
    intro ctx h
    cases h with
    | var h _ =>
      obtain ⟨Θ, A, hX, hΘ⟩ := ih h
      exact ⟨_, _, .succVar hX, hΘ.rename _⟩
  | succSecondOrder _ ih =>
    intro ctx h
    cases h with
    | secondOrder _ h _ _ =>
      obtain ⟨Θ, A, hX, hΘ⟩ := ih h
      exact ⟨_, _, .succSecondOrder hX, hΘ.rename _⟩

/-- The nestings of the variables of a scope under new variables give these no position. -/
theorem Nesting.liftN_empty {α : Type} {Γ : Scope} (n : Nat) (ν : Nesting α Γ) {e : Scope.Entry}
    (z : Var (Scope.extend [] n) e) : Nesting.liftN n @ν (Ren.liftN n Ren.empty z) = .plain :=
  (Nesting.liftN_rename n (ρ := Ren.empty) (ν := Nesting.plain) (ν' := @ν)
    (fun _ (x : Var [] _) => nomatch x) _ z).trans
    (Nesting.liftN_plain n (ν := Nesting.plain) (fun _ _ => rfl) _ z)

section

variable {α I : Type} {rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop} {Γ' Γ : Scope}
  {ctx : Context 0 Γ} {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting α Γ'}
  {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'}

/-- The pairs of substitutions of a context are those of a context equal to it up to its levels. -/
theorem NestSubst.levelEquiv {ctx' : Context 0 Γ} (hctx : Context.LevelEquiv ctx ctx')
    (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂') :
    NestSubst sig ι rd ctx' @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' where
  isPlain := h.isPlain
  left := h.left
  right := h.right
  var := h.var
  secondOrder X _ _ hX hp s τ₁ τ₂ hτ hr := by
    obtain ⟨Θ, A, hX', hΘ⟩ := hX.levelEquiv hctx
    exact h.secondOrder X hX' hp s τ₁ τ₂
      (EqSubst.levelEquiv
        (Context.LevelEquiv.empty.append
          (hΘ.symm.subst (Subst.LevelEquiv.refl fun x => σ₁ (β x)))) hτ) hr

/-- The pairs of substitutions of a context, followed by two abstractions for a second-order
variable of the context, which has no position. -/
theorem NestSubst.lift (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (Θ : Telescope 0 Γ ps) (B : Term 0 (Γ.extend ps.length))
    (ψ : ResultOwnership Grade ps.length) (f₁ f₂ : Term 0 (Scope.extend [] ps.length)) :
    NestSubst sig ι rd (ctx.secondOrder Θ B ψ) (Ren.lift @β)
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) (Nesting.lift (e := .secondOrder ps ψ) @ν₂)
      (Subst.snoc (e := .secondOrder ps ψ) σ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) σ₂ f₂)
      (Subst.snoc (e := .secondOrder ps ψ) σ₁' f₁) (Subst.snoc (e := .secondOrder ps ψ) σ₂' f₂) where
  isPlain x := by
    cases x with
    | zero => rfl
    | succ x => exact h.isPlain x
  left x hx := by
    cases x with
    | zero => rfl
    | succ x => exact h.left x hx
  right x hx := by
    cases x with
    | zero => rfl
    | succ x => exact h.right x hx
  var x hx := by
    cases x with
    | succ x => exact h.var x hx
  secondOrder X _ _ hX hp s τ₁ τ₂ hτ hr := by
    cases hX with
    | zero => exact nomatch hp
    | succSecondOrder hX =>
      rw [Telescope.subst_rename_of
        (θ := fun x => Subst.snoc (e := .secondOrder ps ψ) σ₁ f₁ (Ren.lift @β x))
        (α := Ren.weaken) (θ' := fun x => σ₁ (β x)) (fun _ => rfl)] at hτ
      exact h.secondOrder _ hX hp s τ₁ τ₂ hτ hr

/-- The pairs of substitutions of a context, followed by two abstractions for a second-order
variable that the renaming does not reach, which has no position. -/
theorem NestSubst.skip (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (ψ : ResultOwnership Grade ps.length)
    (f₁ f₂ : Term 0 (Scope.extend [] ps.length)) :
    NestSubst sig ι rd ctx (fun x => .succ (β x))
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) (Nesting.lift (e := .secondOrder ps ψ) @ν₂)
      (Subst.snoc (e := .secondOrder ps ψ) σ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) σ₂ f₂)
      (Subst.snoc (e := .secondOrder ps ψ) σ₁' f₁) (Subst.snoc (e := .secondOrder ps ψ) σ₂' f₂) where
  isPlain x := by
    cases x with
    | zero => rfl
    | succ x => exact h.isPlain x
  left x hx := by
    cases x with
    | zero => rfl
    | succ x => exact h.left x hx
  right x hx := by
    cases x with
    | zero => rfl
    | succ x => exact h.right x hx
  var x hx := by
    cases x with
    | succ x => exact h.var x hx
  secondOrder X _ _ hX hp s τ₁ τ₂ hτ hr := h.secondOrder X hX hp s τ₁ τ₂ hτ hr

/-- The pairs of substitutions of a context, followed by the same closed substitutions of the
variables of a telescope, which have no position. -/
theorem NestSubst.append (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (Θ : Telescope 0 Γ ps) (τ₁ τ₂ : Subst 0 [] (Scope.extend [] ps.length)) :
    NestSubst sig ι rd (ctx.append Θ) (Ren.liftN ps.length @β) (Nesting.liftN ps.length @ν₁)
      (Nesting.liftN ps.length @ν₂) (Subst.append σ₁ τ₁) (Subst.append σ₂ τ₂)
      (Subst.append σ₁' τ₁) (Subst.append σ₂' τ₂) where
  isPlain x := by
    rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Nesting.liftN_weakenN, Nesting.liftN_weakenN]
      exact h.isPlain y
    · rw [Nesting.liftN_empty, Nesting.liftN_empty]
  left x hx := by
    rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Nesting.liftN_weakenN] at hx
      rw [Subst.append_weakenN, Subst.append_weakenN]
      exact h.left y hx
    · rw [Subst.append_liftN_empty, Subst.append_liftN_empty]
  right x hx := by
    rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Nesting.liftN_weakenN] at hx
      rw [Subst.append_weakenN, Subst.append_weakenN]
      exact h.right y hx
    · rw [Subst.append_liftN_empty, Subst.append_liftN_empty]
  var x hx s hr := by
    rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Nesting.liftN_weakenN] at hx ⊢
      rw [Nesting.liftN_weakenN]
      rw [Subst.append_weakenN, Subst.append_weakenN] at hr ⊢
      exact h.var y hx s hr
    · rw [Nesting.liftN_empty] at hx
      exact nomatch hx
  secondOrder X _ _ hX hp s υ₁ υ₂ hυ hr := by
    rcases Var.cases_extend _ X with ⟨Y, rfl⟩ | ⟨z, rfl⟩
    · obtain ⟨Θ₀, A₀, hY, rfl⟩ := hX.of_append Θ
      rw [Ren.liftN_weakenN, Nesting.liftN_weakenN] at hp
      rw [Ren.liftN_weakenN, Nesting.liftN_weakenN, Nesting.liftN_weakenN]
      rw [Ren.liftN_weakenN, Subst.append_weakenN, Subst.append_weakenN] at hr
      rw [Subst.append_weakenN, Subst.append_weakenN]
      rw [Telescope.subst_rename_of (α := Ren.weakenN ps.length) (θ' := fun x => σ₁ (β x))
        (fun y => by rw [Ren.weakenN, Ren.liftN_weakenN, Subst.append_weakenN])] at hυ
      exact h.secondOrder Y hY hp s υ₁ υ₂ hυ hr
    · rw [Ren.liftN_comp_of ps.length (α₃ := Ren.empty) (fun y => nomatch y) z,
        Nesting.liftN_empty] at hp
      exact nomatch hp

/-- A telescope in which the variables with a position do not occur is the same at the two pairs of
substitutions. -/
theorem NestSubst.telescope_eq (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} {Θ : Telescope 0 Γ' ps}
    (hΘ : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → Θ.Avoids x) :
    Θ.subst σ₁' = Θ.subst σ₁ ∧ Θ.subst σ₂' = Θ.subst σ₂ :=
  ⟨Telescope.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.left x hx)
      | false => exact .inr (hΘ _ x hx),
    Telescope.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.right x hx)
      | false => exact .inr (hΘ _ x hx)⟩

/-- A term in which the variables with a position do not occur is the same at the two pairs of
substitutions. -/
theorem NestSubst.term_eq (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {A : Term 0 Γ'}
    (hA : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → A.Avoids x) :
    A.subst σ₁' = A.subst σ₁ ∧ A.subst σ₂' = A.subst σ₂ :=
  ⟨Term.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.left x hx)
      | false => exact .inr (hA _ x hx),
    Term.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.right x hx)
      | false => exact .inr (hA _ x hx)⟩

/-- Arguments in which the variables with a position do not occur are the same at the two pairs of
substitutions. -/
theorem NestSubst.args_eq (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} {ts : Args 0 Γ' ps}
    (hts : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → ts.Avoids x) :
    ts.subst σ₁' = ts.subst σ₁ ∧ ts.subst σ₂' = ts.subst σ₂ :=
  ⟨Args.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.left x hx)
      | false => exact .inr (hts _ x hx),
    Args.subst_eq_of_avoids fun x => by
      cases hx : (ν₁ x).isPlain with
      | true => exact .inl (h.right x hx)
      | false => exact .inr (hts _ x hx)⟩

end

/-! ## Types Without Position -/

section

variable {α I : Type} {rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop} {Γ' Γ : Scope}
  {ctx : Context 0 Γ} {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting α Γ'}
  {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'}

/-- The pairs of substitutions depend on the substitutions only through what they give each
variable. -/
theorem NestSubst.congr_subst (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {τ₁ τ₂ τ₁' τ₂' : Subst 0 [] Γ'} (e₁ : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₁ x = σ₁ x)
    (e₂ : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₂ x = σ₂ x)
    (e₁' : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₁' x = σ₁' x)
    (e₂' : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₂' x = σ₂' x) :
    NestSubst sig ι rd ctx @β @ν₁ @ν₂ @τ₁ @τ₂ @τ₁' @τ₂' where
  isPlain := h.isPlain
  left x hx := (e₁' x).trans ((h.left x hx).trans (e₁ x).symm)
  right x hx := (e₂' x).trans ((h.right x hx).trans (e₂ x).symm)
  var x hx s hr := by
    rw [e₁' x, e₂' x]
    rw [e₁ x, e₂ x] at hr
    exact h.var x hx s hr
  secondOrder X _ _ hX hp s υ₁ υ₂ hυ hr := by
    rw [e₁' (β X), e₂' (β X)]
    rw [e₁ (β X), e₂ (β X)] at hr
    rw [Subst.ext (σ := fun x => τ₁ (β x)) (σ' := fun x => σ₁ (β x)) fun x => e₁ (β x)] at hυ
    exact h.secondOrder X hX hp s υ₁ υ₂ hυ hr

/-- A type without position, strictly positive in the variables with a position, is the same at
the two pairs of substitutions: these variables do not occur in it. -/
theorem NestSubst.plain_eq (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂') {k : Nat}
    {marks : Name → Nat → Prop} {A : Term k Γ'} (ρ : Fin k → Nat)
    (hpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → Term.Positive marks x A)
    (hpl : (A.nest (fun _ => none) @ν₁).isPlain = true) :
    (A.atLevels ρ).subst σ₁' = (A.atLevels ρ).subst σ₁ ∧
      (A.atLevels ρ).subst σ₂' = (A.atLevels ρ).subst σ₂ :=
  h.term_eq fun e x hx => (Term.Positive.avoids (ν := @ν₁)
    (fun hp => by rw [hp] at hx; exact nomatch hx) (hpos e x hx)
    (Nest.eq_plain_of_isPlain hpl)).substLevels _

/-- A type without position under the variables of an abstraction, strictly positive in the
variables with a position, is the same at the two pairs of substitutions, under these variables. -/
theorem NestSubst.plain_eq_liftN (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {k : Nat} {marks : Name → Nat → Prop} (m : Nat) {A : Term k (Γ'.extend m)} (ρ : Fin k → Nat)
    (hpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
      Term.Positive marks (x.weakenN m) A)
    (hpl : (A.nest (fun _ => none) (Nesting.liftN m @ν₁)).isPlain = true) :
    (A.atLevels ρ).subst (Subst.liftN m @σ₁') = (A.atLevels ρ).subst (Subst.liftN m @σ₁) ∧
      (A.atLevels ρ).subst (Subst.liftN m @σ₂') = (A.atLevels ρ).subst (Subst.liftN m @σ₂) := by
  have hfree : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
      (A.atLevels ρ).Avoids (x.weakenN m) := fun e x hx =>
    (Term.Positive.avoids (ν := Nesting.liftN m @ν₁)
      (by
        rw [Nesting.liftN_weakenN]
        intro hp
        rw [hp] at hx
        exact nomatch hx)
      (hpos e x hx) (Nest.eq_plain_of_isPlain hpl)).substLevels _
  exact ⟨Term.subst_eq_of_avoids fun z =>
      (Subst.liftN_eq_or (P := fun x => (ν₁ x).isPlain = false) m
        (fun x => by
          cases hx : (ν₁ x).isPlain with
          | true => exact .inl (h.left x hx)
          | false => exact .inr rfl) z).imp id
        fun ⟨x, hz, hx⟩ => hz ▸ hfree _ x hx,
    Term.subst_eq_of_avoids fun z =>
      (Subst.liftN_eq_or (P := fun x => (ν₁ x).isPlain = false) m
        (fun x => by
          cases hx : (ν₁ x).isPlain with
          | true => exact .inl (h.right x hx)
          | false => exact .inr rfl) z).imp id
        fun ⟨x, hz, hx⟩ => hz ▸ hfree _ x hx⟩

/-- A type without position, strictly positive in the variables with a position, is read at the
second pair of substitutions as it is at the first one. -/
theorem NestSubst.reads_of_plain (h : NestSubst sig ι rd ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {k : Nat} {marks : Name → Nat → Prop} {A : Term k Γ'} (ρ : Fin k → Nat)
    (hpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → Term.Positive marks x A)
    (hpl : (A.nest (fun _ => none) @ν₁).isPlain = true) {s : I}
    (hr : rd s .plain .plain ((A.atLevels ρ).subst σ₁) ((A.atLevels ρ).subst σ₂)) :
    rd s (A.nest (fun _ => none) @ν₁) (A.nest (fun _ => none) @ν₂)
      ((A.atLevels ρ).subst σ₁') ((A.atLevels ρ).subst σ₂') := by
  obtain ⟨e₁, e₂⟩ := h.plain_eq ρ hpos hpl
  have hpl₂ : (A.nest (fun _ => none) @ν₂).isPlain = true :=
    (Term.nest_isPlain_congr (fun _ x => h.isPlain x) A).symm.trans hpl
  rw [Nest.eq_plain_of_isPlain hpl, Nest.eq_plain_of_isPlain hpl₂, e₁, e₂]
  exact hr

end

/-! ## Arguments of an Instance -/

section

variable {α I : Type} {rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop} {Δ : Scope}
  {pctx : Context 0 Δ} {ns₁ ns₂ : List (Nest α)}
  {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Δ}

/-- The pairs of substitutions of the parameters of an instance, followed by the arguments of a
variable, whose nestings are those of the arguments. -/
theorem NestSubst.params_var
    (ih : NestSubst sig ι rd pctx (fun x => x) (Nesting.ofArgs ns₁) (Nesting.ofArgs ns₂) @θ₁ @θ₂
      @θ₁' @θ₂')
    (A₀ : Term 0 Δ) {l₁ l₂ : Nest α} {t₁ t₂ t₁' t₂' : Term 0 []}
    (hpl : l₁.isPlain = l₂.isPlain) (hl : l₁.isPlain = true → t₁' = t₁)
    (hr : l₁.isPlain = true → t₂' = t₂)
    (hv : l₁.isPlain = false → ∀ s, rd s .plain .plain t₁ t₂ →
      rd s l₁ l₂ t₁' t₂') :
    NestSubst sig ι rd (pctx.var A₀) (fun x => x) (Nesting.ofArgs (l₁ :: ns₁))
      (Nesting.ofArgs (l₂ :: ns₂)) (Subst.snoc (e := .var) θ₁ t₁) (Subst.snoc (e := .var) θ₂ t₂)
      (Subst.snoc (e := .var) θ₁' t₁') (Subst.snoc (e := .var) θ₂' t₂') where
  isPlain x := by
    cases x with
    | zero => exact hpl
    | succ x => exact ih.isPlain x
  left x hx := by
    cases x with
    | zero => exact hl hx
    | succ x => exact ih.left x hx
  right x hx := by
    cases x with
    | zero => exact hr hx
    | succ x => exact ih.right x hx
  var x hx := by
    cases x with
    | zero => exact hv hx
    | succ x => exact ih.var x hx
  secondOrder X _ _ hX hp s τ₁ τ₂ hτ hr := by
    cases hX with
    | succVar hX =>
      rw [Telescope.subst_rename_of (θ := fun x => Subst.snoc (e := .var) θ₁ t₁ x)
        (α := Ren.weaken) (θ' := fun x => θ₁ x) (fun _ => rfl)] at hτ
      exact ih.secondOrder _ hX hp s τ₁ τ₂ hτ hr

/-- The pairs of substitutions of the parameters of an instance, followed by the abstractions for
a second-order variable, whose nestings are those of the abstractions. -/
theorem NestSubst.params_secondOrder
    (ih : NestSubst sig ι rd pctx (fun x => x) (Nesting.ofArgs ns₁) (Nesting.ofArgs ns₂) @θ₁ @θ₂
      @θ₁' @θ₂')
    {ps : List Parameter} (Θ₀ : Telescope 0 Δ ps) (A₀ : Term 0 (Δ.extend ps.length))
    (ψ : ResultOwnership Grade ps.length) {l₁ l₂ : Nest α}
    {f₁ f₂ f₁' f₂' : Term 0 (Scope.extend [] ps.length)}
    (hpl : l₁.isPlain = l₂.isPlain) (hl : l₁.isPlain = true → f₁' = f₁)
    (hr : l₁.isPlain = true → f₂' = f₂)
    (hso : l₁.isPlain = false → ∀ s τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ₀.subst fun x => θ₁ x)) τ₁ τ₂ →
      rd s .plain .plain (f₁.subst τ₁) (f₂.subst τ₂) →
        rd s l₁ l₂ (f₁'.subst τ₁) (f₂'.subst τ₂)) :
    NestSubst sig ι rd (pctx.secondOrder Θ₀ A₀ ψ) (fun x => x) (Nesting.ofArgs (l₁ :: ns₁))
      (Nesting.ofArgs (l₂ :: ns₂)) (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁)
      (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂) (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁')
      (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂') where
  isPlain x := by
    cases x with
    | zero => exact hpl
    | succ x => exact ih.isPlain x
  left x hx := by
    cases x with
    | zero => exact hl hx
    | succ x => exact ih.left x hx
  right x hx := by
    cases x with
    | zero => exact hr hx
    | succ x => exact ih.right x hx
  var x hx := by
    cases x with
    | succ x => exact ih.var x hx
  secondOrder X _ _ hX hp s τ₁ τ₂ hτ hr := by
    cases hX with
    | zero =>
      rw [Telescope.subst_rename_of
        (θ := fun x => Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁ x) (α := Ren.weaken)
        (θ' := fun x => θ₁ x) (fun _ => rfl)] at hτ
      exact hso hp s τ₁ τ₂ hτ hr
    | succSecondOrder hX =>
      rw [Telescope.subst_rename_of
        (θ := fun x => Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁ x) (α := Ren.weaken)
        (θ' := fun x => θ₁ x) (fun _ => rfl)] at hτ
      exact ih.secondOrder _ hX hp s τ₁ τ₂ hτ hr

end

/-! ## Soundness of the Typing -/

/-- The soundness of the typing, in the signatures whose entries the signature `Σ` gives their
meaning, of the judgments that the nested types read: the hypothesis of the properties of the
nested types, which the soundness of the typing reads at the signatures before, and proves of
these judgments. -/
structure TypingSound (sig : Signature) (ι : Interpretation) : Prop where
  /-- A typing. -/
  hasType : ∀ {sigT : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    sig.ValidEntries ι sigT → HasType sigT ctx t A → ValidTerm sig ι ctx t A
  /-- A telescope in a sort. -/
  wfTelescope : ∀ {sigT : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
    sig.ValidEntries ι sigT → WfTelescope sigT ctx Θ κ → ValidTelescope sig ι ctx Θ κ
  /-- Arguments of a telescope. -/
  hasArgs : ∀ {sigT : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts : Args k Γ ps} {Θ : Telescope k Γ ps},
    sig.ValidEntries ι sigT → HasArgs sigT ctx ts Θ → ValidArgs sig ι ctx ts Θ
  /-- Arguments of an instance. -/
  hasInstanceArgs : ∀ {sigT : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    sig.ValidEntries ι sigT → HasInstanceArgs sigT ctx as params →
      ValidInstanceArgs sig ι ctx as params

/-! ## Nested Types of a Signature -/

/-- The types typed in the signature `Σ_T` and strictly positive in the variables with a position
are read by `rd` at their nestings, at the second pair of two pairs of substitutions, when they are
read without position at the first pair, whose substitutions of the context are equal; the strict
positivity reads the parameters that a block `𝒟` whose names are fresh declares, and those that the
codata types of `Σ_T` do. -/
def ReadsNested {α I : Type} (sig : Signature) (ι : Interpretation)
    (rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop) (sigT : Signature) : Prop :=
  ∀ {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A T : Term k Γ}, HasType sigT ctx A T →
    ∀ (decl : TypeDeclaration), (∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) →
    ∀ (ρ : Fin k → Nat) {Γ' : Scope} (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting α Γ'}
      {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'},
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) x (A.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' → ∀ s,
      rd s .plain .plain (((A.rename β).atLevels ρ).subst σ₁)
        (((A.rename β).atLevels ρ).subst σ₂) →
      rd s ((A.rename β).nest (fun _ => none) @ν₁)
        ((A.rename β).nest (fun _ => none) @ν₂) (((A.rename β).atLevels ρ).subst σ₁')
        (((A.rename β).atLevels ρ).subst σ₂')

/-- The clause of the instances of a reading `rd`: an instance of a declared type, typed in the
signature `Σ_T`, whose arguments are strictly positive in the variables with a position, and one of
whose arguments has a position, is read by `rd` at its nesting, at the second pair of two pairs of
substitutions, when it is read without position at the first pair, and when its arguments give the
parameters of the type two pairs of substitutions, at the nestings of the arguments. -/
def ReadsInstances {α I : Type} (sig : Signature) (ι : Interpretation)
    (rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop) (sigT : Signature) : Prop :=
  ∀ {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {T : Term k Γ},
    HasType sigT ctx (.inst D qs ls ps as) T →
    ∀ (decl : TypeDeclaration), (∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) →
    ∀ (ρ : Fin k → Nat) {Γ' : Scope} (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting α Γ'}
      {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'},
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      (∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = (ν₂ x).isPlain) →
      (∀ {params : Context k Δ}, HasInstanceArgs sigT ctx as params →
        NestSubst sig ι rd (params.atLevels ρ) (fun x => x)
          (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁))
          (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₂))
          (((as.rename β).atLevels ρ).subst σ₁).toSubst
          (((as.rename β).atLevels ρ).subst σ₂).toSubst
          (((as.rename β).atLevels ρ).subst σ₁').toSubst
          (((as.rename β).atLevels ρ).subst σ₂').toSubst) →
      (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₁).isPlain = false → ∀ s,
      rd s .plain .plain ((((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ₁)
        ((((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ₂) →
      rd s (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₁)
        (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₂)
        ((((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ₁')
        ((((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ₂')

section

variable {α I : Type} {rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop}

/-! ## Readings -/

/-- The clause of a reading for a destructor whose result has no position, for the property `dr` of
the destructors and the sorts `ok` of the reading. Its hypotheses, at a sort `κ` that `ok` admits:
the result `B` has no position at the two nestings `ν₁` and `ν₂`; the arguments `Θ` are equal
telescopes of `U_κ` at the substitutions `θ₁` and `θ₂`, and the same at `θ₁'` and `θ₂'`; the
results are equal types of a sort `κ₁ ≼ κ` at `θ₁` and `θ₂` and equal arguments, and the same at
`θ₁'` and `θ₂'`; and the destructors after it are read at `θ₁'` and `θ₂'` extended by each pair of
equal abstractions for it. Its conclusion: the destructors are read at `θ₁'` and `θ₂'`. -/
def Reading.PlainHead (sig : Signature) (ι : Interpretation) {α I : Type}
    (dr : I → {Γ : Scope} → {ns : List Name} → Nesting α Γ → Nesting α Γ → Destructors 0 Γ ns →
      Subst 0 [] Γ → Subst 0 [] Γ → Prop)
    (ok : I → Universe 0 → Prop) : Prop :=
  ∀ {i : I} {κ κ₁ : Universe 0}, ok i κ → ∀ {Γ : Scope} {d : Name} {ns : List Name}
    {ps : List Parameter} {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting α Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ},
    B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) = .plain →
    B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) = .plain →
    ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂) →
    Θ.subst θ₁' = Θ.subst θ₁ → Θ.subst θ₂' = Θ.subst θ₂ → κ₁ ≼ κ →
    (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
        (.sort κ₁)) →
    (∀ τ, B.subst (Subst.append θ₁' τ) = B.subst (Subst.append θ₁ τ)) →
    (∀ τ, B.subst (Subst.append θ₂' τ) = B.subst (Subst.append θ₂ τ)) →
    (∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
      dr i (Nesting.lift (e := .secondOrder ps ψ) @ν₁) (Nesting.lift (e := .secondOrder ps ψ) @ν₂)
        ds (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁)
        (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂)) →
    dr i @ν₁ @ν₂ (.cons (d := d) p q ς Θ B ψ ds) @θ₁' @θ₂'

/-- The clause of a reading for a destructor whose result has a position, for the property `rd` of
the types, the property `dr` of the destructors and the sorts `ok` of the reading. Its hypotheses,
at a sort `κ` that `ok` admits: the result `B` has a position at the two nestings `ν₁` and `ν₂`; the
arguments `Θ` are equal telescopes of `U_κ` at the substitutions `θ₁` and `θ₂`, and the same at
`θ₁'` and `θ₂'`; the results at `θ₁'` and `θ₂'` and equal arguments are read at their nestings;
and the destructors after it are read at `θ₁'` and `θ₂'` extended by every pair of abstractions
for it. Its conclusion: the destructors are read at `θ₁'` and `θ₂'`. -/
def Reading.NestedHead (sig : Signature) (ι : Interpretation) {α I : Type}
    (rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop)
    (dr : I → {Γ : Scope} → {ns : List Name} → Nesting α Γ → Nesting α Γ → Destructors 0 Γ ns →
      Subst 0 [] Γ → Subst 0 [] Γ → Prop)
    (ok : I → Universe 0 → Prop) : Prop :=
  ∀ {i : I} {κ : Universe 0}, ok i κ → ∀ {Γ : Scope} {d : Name} {ns : List Name}
    {ps : List Parameter} {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting α Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ},
    B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) ≠ .plain →
    B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) ≠ .plain →
    ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂) →
    Θ.subst θ₁' = Θ.subst θ₁ → Θ.subst θ₂' = Θ.subst θ₂ →
    (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      rd i (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂))
        (B.subst (Subst.append θ₁' τ₁)) (B.subst (Subst.append θ₂' τ₂))) →
    (∀ f₁ f₂, dr i (Nesting.lift (e := .secondOrder ps ψ) @ν₁)
      (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁)
      (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂)) →
    dr i @ν₁ @ν₂ (.cons (d := d) p q ς Θ B ψ ds) @θ₁' @θ₂'

/-- A reading of the nested types: the property `rd` of two closed types and of their nestings,
that a graph of the nestings reads both with one relation, the same property `dr` of the
destructors of a codata type at two closed substitutions, and the sorts `ok` in which it reads
them, with what the graph gives of them: the clauses of its destructors, a type without position
that the meaning gives, and the clause of an instance of a codata type none of whose destructors is
recursive. -/
structure Reading (sig : Signature) (ι : Interpretation) (α I : Type) where
  /-- Two closed types are read at their nestings, with one relation. -/
  rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop
  /-- The destructors are read at two nestings of their scope and two closed substitutions, with
  one relation. -/
  dr : I → {Γ : Scope} → {ns : List Name} → Nesting α Γ → Nesting α Γ → Destructors 0 Γ ns →
    Subst 0 [] Γ → Subst 0 [] Γ → Prop
  /-- The sorts in which the destructors are read. -/
  ok : I → Universe 0 → Prop
  /-- Equal types of a sort that a sort of the reading bounds are read without position. -/
  plain : ∀ {i : I} {κ κ₁ : Universe 0} {A₁ A₂ : Term 0 []}, ok i κ → κ₁ ≼ κ →
    ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁) → rd i .plain .plain A₁ A₂
  /-- No destructor is read. -/
  nil : ∀ {i : I} {Γ : Scope} {ν₁ ν₂ : Nesting α Γ} {θ₁ θ₂ : Subst 0 [] Γ},
    dr i @ν₁ @ν₂ .nil @θ₁ @θ₂
  /-- A destructor whose arguments are equal telescopes and whose results are equal types at two
  equal closed substitutions, and are the same at two other substitutions, followed by destructors
  that are read at these, for each pair of equal abstractions for it, is read with them, as a
  destructor whose result has no position. -/
  plain_head : Reading.PlainHead sig ι dr ok
  /-- A destructor whose arguments are equal telescopes at two equal closed substitutions, and are
  the same at two other substitutions, at which its results are read at their nestings, at equal
  arguments, followed by destructors that are read at these substitutions, for each pair of
  abstractions for it, is read with them, as a destructor whose result has a position. -/
  nested_head : Reading.NestedHead sig ι rd dr ok
  /-- An instance of a codata type none of whose destructors is recursive, that the constraint of
  its block admits, read without position at two lists of arguments, lives in a sort of the
  reading, and is read at the nestings of two other lists of arguments at which its destructors are
  read, at the values of its levels. -/
  inst : ∀ {i : I} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as₁ as₂ as₁' as₂' : InstanceArgs 0 [] decl.scope}
    {νs₁ νs₂ : List (Nest α)} (_ : sig.HasCodataType D decl T)
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels),
    (∀ r ∈ (T.body hqp.inst).recursion decl.names, r = none) →
    decl.constraint hqp.inst →
    rd i .plain .plain (.inst D qs ls ps as₁) (.inst D qs ls ps as₂) →
    ∃ j, ok j ((decl.sort hqp.inst).atLevels fun x => (ls.getFin hl x).closedValue) ∧
      (dr j (Nesting.ofArgs νs₁) (Nesting.ofArgs νs₂)
          ((T.body hqp.inst).atLevels fun x => (ls.getFin hl x).closedValue)
          as₁'.toSubst as₂'.toSubst →
        rd i (.inst νs₁) (.inst νs₂) (.inst D qs ls ps as₁') (.inst D qs ls ps as₂'))

/-! ## Destructors of a Codata Type -/

section

variable {α I : Type}

/-- The head of a first destructor well formed in `Σ_T`, renamed by `β` and at the values `ρ` of
its levels, given the soundness of the typing in `Σ_T`, at two pairs of substitutions related as
`NestSubst` relates them, the first of which are equal substitutions of its context, when its
arguments avoid the variables with a position: its arguments are the same at both pairs and equal
telescopes at the first, and its results at equal arguments are equal types. -/
theorem WfDestructors.head_valid {α I : Type}
    {rd : I → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop} (hS : TypingSound sig ι)
    {sigT : Signature} (hent : sig.ValidEntries ι sigT) {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {ps : List Parameter} {Θ : Telescope k Γ ps}
    {B : Term k (Γ.extend ps.length)} {κ₁ κ : Universe k}
    (hΘ : WfTelescope sigT ctx Θ ⟨.type, κ.level⟩) (hB : HasType sigT (ctx.append Θ) B (.sort κ₁))
    (ρ : Fin k → Nat) {Γ' : Scope} {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting α Γ'}
    {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ'}
    (hΘav : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
      ((Θ.rename β).atLevels ρ).Avoids x)
    (hE : EqSubst sig ι (ctx.atLevels ρ) (fun x => θ₁ (β x)) (fun x => θ₂ (β x)))
    (hNS : NestSubst sig ι rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @θ₁ @θ₂ @θ₁' @θ₂') :
    ((Θ.rename β).atLevels ρ).subst θ₁' = ((Θ.rename β).atLevels ρ).subst θ₁ ∧
      ((Θ.rename β).atLevels ρ).subst θ₂' = ((Θ.rename β).atLevels ρ).subst θ₂ ∧
      ValidEqTelescope₀ sig ι ⟨.type, (κ.atLevels ρ).level⟩
        (((Θ.rename β).atLevels ρ).subst θ₁) (((Θ.rename β).atLevels ρ).subst θ₂) ∧
      ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (((Θ.rename β).atLevels ρ).subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₁ τ₁))
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₂ τ₂))
          (.sort (κ₁.atLevels ρ)) := by
  obtain ⟨hΘ₁, hΘ₂⟩ := hNS.telescope_eq hΘav
  refine ⟨hΘ₁, hΘ₂, ?_, fun τ₁ τ₂ hτ => ?_⟩
  · rw [Θ.atLevels_rename_subst ρ @β, Θ.atLevels_rename_subst ρ @β]
    exact (hS.wfTelescope hent hΘ ρ).2 _ _ hE
  · rw [Θ.atLevels_rename_subst ρ @β] at hτ
    rw [B.atLevels_rename_subst_append ρ @β, B.atLevels_rename_subst_append ρ @β]
    have h := hS.hasType hent hB ρ
    simp only [Context.atLevels, Context.substLevels_append] at h
    exact h.2 _ _ ((EqSubst.append_append_iff _ _ _ _ τ₁ τ₂).2 ⟨hE, hτ⟩)

/-- The destructors of a codata type none of which is recursive, well formed in a signature `Σ_T`
whose nested types a reading reads, and strictly positive in the variables with a position, are
read by the reading, at the second pair of two pairs of substitutions, the first of which are equal
substitutions of their context, given the soundness of the typing in `Σ_T`: by induction on their
formation, where the destructors after a destructor whose result has a position are read whatever
the abstractions for it, on which they do not depend. -/
theorem WfDestructors.reads (R : Reading sig ι α I) (hS : TypingSound sig ι) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT) (hread : ReadsNested sig ι R.rd sigT)
    {decl : TypeDeclaration}
    (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {J : Instance decl.sorts decl.grades}
    (ρ : Fin decl.levels → Nat) (i : I) {Γ : Scope} {ns : List Name} {ν₀ : Nesting Nat Γ}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} {Γ' : Scope} {β : Ren Γ' Γ}
    {ν₁ ν₂ : Nesting α Γ'} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ'} :
    WfDestructors sigT decl J @ν₀ as ctx ds κ → (∀ r ∈ ds.recursion decl.names, r = none) →
      R.ok i (κ.atLevels ρ) →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν₀ x).isPlain = true → (ν₁ (β x)).isPlain = true) →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) x (ds.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => θ₁ (β x)) (fun x => θ₂ (β x)) →
      NestSubst sig ι R.rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @θ₁ @θ₂ @θ₁' @θ₂' →
      R.dr i @ν₁ @ν₂ ((ds.rename β).atLevels ρ) @θ₁' @θ₂' := by
  intro h hrec hn hν₀ hpos hE hNS
  suffices H : Derivations.Conclusion
      (wfDestructors := fun sigT decl _ {Γ _} ν₀ _ ctx ds κ _ =>
        sig.ValidEntries ι sigT → ReadsNested sig ι R.rd sigT →
        (∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) → ∀ (ρ : Fin decl.levels → Nat) {Γ' : Scope}
        {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting α Γ'} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ'},
        (∀ r ∈ ds.recursion decl.names, r = none) → R.ok i (κ.atLevels ρ) →
        (∀ (e : Scope.Entry) (x : Var Γ e), (ν₀ x).isPlain = true → (ν₁ (β x)).isPlain = true) →
        (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
          Destructors.Positive (sigT.PositiveIn decl) x (ds.rename β)) →
        EqSubst sig ι (ctx.atLevels ρ) (fun x => θ₁ (β x)) (fun x => θ₂ (β x)) →
        NestSubst sig ι R.rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @θ₁ @θ₂ @θ₁' @θ₂' →
        R.dr i @ν₁ @ν₂ ((ds.rename β).atLevels ρ) @θ₁' @θ₂') from
    H.wfDestructors h hent hread fresh ρ hrec hn hν₀ hpos hE hNS
  apply Derivations.induction
  case wfDestructors_nil =>
    exact fun hctx hctx_ih => fun hent hread fresh ρ Γ' β ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hrec hn hν₀ hpos hE
        hNS =>
      R.nil
  case wfDestructors_cons =>
    intro sigT decl J Γ ν as d ns ps ctx p q ς Θ B ψ ds κ₁ κ _ hν hΘ hB hκ hp hds hΘ_ih hB_ih
      hds_ih hent hread fresh ρ Γ' β ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hrec hn hν₀ hpos hE hNS
    -- What the strict positivity gives of the destructor.
    have hΘav : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        ((Θ.rename β).atLevels ρ).Avoids x := fun e x hx =>
      (hpos e x hx).cons_inv.1.substLevels _
    have hBpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) (x.weakenN ps.length)
          (B.rename (Ren.liftN ps.length @β)) := fun e x hx =>
      (hpos e x hx).cons_inv.2.1
    have hdspos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) (.succ x) (ds.rename (Ren.lift @β)) :=
      fun e x hx => (hpos e x hx).cons_inv.2.2
    -- The arguments and the result, at the substitutions.
    obtain ⟨hΘ₁, hΘ₂, hΘv, hBv⟩ := WfDestructors.head_valid hS hent hΘ hB ρ hΘav hE hNS
    -- The result has no position, and the variables with a position do not occur in it.
    have hpl₁ : (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₁) = .plain := by
      rw [Term.nest_rename _ (Ren.liftN ps.length @β)
        (Nesting.liftN_rename ps.length (ν := fun x => ν₁ (β x)) fun _ _ => rfl) B]
      exact Nest.eq_plain_of_isPlain
        (Term.nest_isPlain_mono (Nesting.liftN_isPlain_mono _ hν₀) B (by rw [hν]; rfl))
    have hpl₂ : (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₂) = .plain :=
      Nest.eq_plain_of_isPlain ((Term.nest_isPlain_congr
        (Nesting.liftN_isPlain_congr ps.length fun _ x => hNS.isPlain x) _).symm.trans
        (by rw [hpl₁]; rfl))
    have hBav : ∀ (e : Scope.Entry) (z : Var (Γ'.extend ps.length) e),
        (Nesting.liftN ps.length @ν₁ z).isPlain = false →
        ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).Avoids z := fun e z hz => by
      obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z fun h => by
        rw [h] at hz
        exact nomatch hz
      exact (Term.Positive.avoids (ν := Nesting.liftN ps.length @ν₁)
        (by rwa [Nesting.liftN_weakenN]) (hBpos e x (Nest.isPlain_eq_false hx)) hpl₁).substLevels _
    have hB₁ := fun τ => ((hNS.append (Θ.atLevels ρ) τ τ).term_eq hBav).1
    have hB₂ := fun τ => ((hNS.append (Θ.atLevels ρ) τ τ).term_eq hBav).2
    rw [Destructors.rename]
    refine R.plain_head hn
      ((Term.nest_substLevels _ _ _).trans hpl₁) ((Term.nest_substLevels _ _ _).trans hpl₂)
      hΘv hΘ₁ hΘ₂ (Universe.substLevels_bounded _ hκ) hBv hB₁ hB₂ fun f₁ f₂ hf => ?_
    have e : ∀ (θ : Subst 0 [] Γ') (f : Term 0 (Scope.extend [] ps.length)),
        @Eq (Subst 0 [] (.secondOrder ps ψ :: Γ))
          (fun x => Subst.snoc (e := .secondOrder ps ψ) θ f (Ren.lift @β x))
          (Subst.snoc (e := .secondOrder ps ψ) (fun x => θ (β x)) f) := fun θ f =>
      Subst.ext fun x => by cases x <;> rfl
    refine hds_ih hent hread fresh ρ (β := Ren.lift @β)
      (fun r hr => hrec r (List.mem_cons_of_mem _ hr)) hn
      (fun e z => match z with
        | .zero => fun _ => rfl
        | .succ x => hν₀ e x)
      (fun e z hz => match z, hz with
        | .zero, hz => nomatch hz
        | .succ x, hz => hdspos e x hz)
      ((EqSubst.congr (e θ₁ f₁) (e θ₂ f₂)).2 ((EqSubst.secondOrder_iff _ _ _ ψ _ _).2
        ⟨hE, fun τ₁ τ₂ hτ => ?_⟩))
      (hNS.lift _ _ ψ f₁ f₂)
    show ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂)
      (((B.atLevels ρ).subst (Subst.liftN _ fun x => θ₁ (β x))).subst τ₁)
    rw [Term.subst_append, ← B.atLevels_rename_subst_append ρ @β]
    exact hf τ₁ τ₂ ((congrArg (fun Θ' => EqSubst sig ι (Context.empty.append Θ') τ₁ τ₂)
      (Θ.atLevels_rename_subst ρ @β θ₁)).mpr hτ)
  case wfDestructors_nested =>
    intro sigT decl J Γ ν as d ns ps ctx p q ς Θ B ψ ds κ₁ κ _ hν hΘ hB hκ hp hds hΘ_ih hB_ih
      hds_ih hent hread fresh ρ Γ' β ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hrec hn hν₀ hpos hE hNS
    have hds_eq : (ds.rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) @β) =
        ds.rename (fun x => .succ (β x)) := Destructors.rename_rename_of (fun _ => rfl) ds
    -- What the strict positivity gives of the destructor.
    have hΘav : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        ((Θ.rename β).atLevels ρ).Avoids x := fun e x hx =>
      (hpos e x hx).cons_inv.1.substLevels _
    have hBpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) (x.weakenN ps.length)
          (B.rename (Ren.liftN ps.length @β)) := fun e x hx =>
      (hpos e x hx).cons_inv.2.1
    have hdspos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) (.succ x)
          (ds.rename (fun x => .succ (e' := .secondOrder ps ψ) (β x))) :=
      fun e x hx => hds_eq ▸ (hpos e x hx).cons_inv.2.2
    -- The arguments and the result, at the substitutions.
    obtain ⟨hΘ₁, hΘ₂, hΘv, hBv⟩ := WfDestructors.head_valid hS hent hΘ hB ρ hΘav hE hNS
    have hEa : ∀ τ₁ τ₂,
        EqSubst sig ι (Context.empty.append (((Θ.rename β).atLevels ρ).subst θ₁)) τ₁ τ₂ →
        EqSubst sig ι ((ctx.atLevels ρ).append (Θ.atLevels ρ))
          (Subst.append (fun x => θ₁ (β x)) τ₁) (Subst.append (fun x => θ₂ (β x)) τ₂) :=
      fun τ₁ τ₂ hτ => by
        rw [Θ.atLevels_rename_subst ρ @β] at hτ
        exact (EqSubst.append_append_iff _ _ _ _ τ₁ τ₂).2 ⟨hE, hτ⟩
    have hκ' : κ₁.atLevels ρ ≼ κ.atLevels ρ := Universe.substLevels_bounded _ hκ
    -- The destructors after it, whatever the abstractions for it.
    have hrest : ∀ f₁ f₂ : Term 0 (Scope.extend [] ps.length),
        R.dr i (Nesting.lift (e := .secondOrder ps ψ) @ν₁)
          (Nesting.lift (e := .secondOrder ps ψ) @ν₂)
          (((ds.rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) @β)).atLevels ρ)
          (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁)
          (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) := fun f₁ f₂ => by
      rw [hds_eq]
      exact hds_ih hent hread fresh ρ
        (β := fun x => .succ (e' := .secondOrder ps ψ) (β x))
        (fun r hr => hrec r (List.mem_cons_of_mem _
          (by rw [Destructors.recursion_rename]; exact hr))) hn hν₀
        (fun e z hz => match z, hz with
          | .zero, hz => nomatch hz
          | .succ x, hz => hdspos e x hz)
        hE (hNS.skip ψ f₁ f₂)
    rw [Destructors.rename]
    cases hpl : ((B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₁)).isPlain with
    | true =>
      -- The result has no position at these nestings: the variables with a position do not
      -- occur in it.
      have hpl₁ := Nest.eq_plain_of_isPlain hpl
      have hpl₂ : (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
          (Nesting.liftN ps.length @ν₂) = .plain :=
        Nest.eq_plain_of_isPlain ((Term.nest_isPlain_congr
          (Nesting.liftN_isPlain_congr ps.length fun _ x => hNS.isPlain x) _).symm.trans hpl)
      have hBav : ∀ (e : Scope.Entry) (z : Var (Γ'.extend ps.length) e),
          (Nesting.liftN ps.length @ν₁ z).isPlain = false →
          ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).Avoids z := fun e z hz => by
        obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z fun h => by
          rw [h] at hz
          exact nomatch hz
        exact (Term.Positive.avoids (ν := Nesting.liftN ps.length @ν₁)
          (by rwa [Nesting.liftN_weakenN]) (hBpos e x (Nest.isPlain_eq_false hx))
          hpl₁).substLevels _
      have hB₁ := fun τ => ((hNS.append (Θ.atLevels ρ) τ τ).term_eq hBav).1
      have hB₂ := fun τ => ((hNS.append (Θ.atLevels ρ) τ τ).term_eq hBav).2
      exact R.plain_head hn
        ((Term.nest_substLevels _ _ _).trans hpl₁) ((Term.nest_substLevels _ _ _).trans hpl₂)
        hΘv hΘ₁ hΘ₂ hκ' hBv hB₁ hB₂ fun f₁ f₂ _ => hrest f₁ f₂
    | false =>
      -- The result has a position: the graph of the nestings reads it.
      have hpl₂ : ((B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
          (Nesting.liftN ps.length @ν₂)).isPlain = false :=
        (Term.nest_isPlain_congr
          (Nesting.liftN_isPlain_congr ps.length fun _ x => hNS.isPlain x) _).symm.trans hpl
      have e₁ : ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).nest (fun _ => none)
          (Nesting.liftN ps.length @ν₁) = (B.rename (Ren.liftN ps.length @β)).nest
            (fun _ => none) (Nesting.liftN ps.length @ν₁) := Term.nest_substLevels _ _ _
      have e₂ : ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).nest (fun _ => none)
          (Nesting.liftN ps.length @ν₂) = (B.rename (Ren.liftN ps.length @β)).nest
            (fun _ => none) (Nesting.liftN ps.length @ν₂) := Term.nest_substLevels _ _ _
      refine R.nested_head hn
        (fun h => by rw [e₁.symm.trans h] at hpl; exact nomatch hpl)
        (fun h => by rw [e₂.symm.trans h] at hpl₂; exact nomatch hpl₂)
        hΘv hΘ₁ hΘ₂ (fun τ₁ τ₂ hτ => ?_) hrest
      suffices h : R.rd i
          ((B.rename (Ren.liftN ps.length @β)).nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
          ((B.rename (Ren.liftN ps.length @β)).nest (fun _ => none) (Nesting.liftN ps.length @ν₂))
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₁' τ₁))
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₂' τ₂)) by
        rw [← e₁, ← e₂] at h
        exact h
      have eσ : ∀ (θ : Subst 0 [] Γ') (τ : Subst 0 [] (Scope.extend [] ps.length)),
          @Eq (Subst 0 [] (Γ.extend ps.length))
            (fun x => Subst.append θ τ (Ren.liftN ps.length @β x))
            (Subst.append (fun x => θ (β x)) τ) := fun θ τ =>
        Subst.ext (Subst.append_liftN_rename β (fun _ => rfl) τ)
      refine hread hB decl fresh ρ (Ren.liftN ps.length @β) (σ₁ := Subst.append θ₁ τ₁)
        (σ₂ := Subst.append θ₂ τ₂) (fun e z hz => ?_) ?_ ?_ i ?_
      · obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z fun h => by
          rw [h] at hz
          exact nomatch hz
        exact hBpos e x (Nest.isPlain_eq_false hx)
      · rw [Context.atLevels, Context.substLevels_append]
        exact (EqSubst.congr (eσ θ₁ τ₁) (eσ θ₂ τ₂)).2 (hEa τ₁ τ₂ hτ)
      · rw [Context.atLevels, Context.substLevels_append]
        exact hNS.append (Θ.atLevels ρ) τ₁ τ₂
      · exact R.plain hn hκ' (hBv τ₁ τ₂ hτ)
  case wfDestructors_recursive =>
    refine fun hD hΘ hp hds hΘ_ih hds_ih => fun hent hread fresh ρ Γ' β ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hrec hn
        hν₀ hpos hE hNS => ?_
    have h := hrec _ (List.mem_cons_self ..)
    simp only [TypeDeclaration.blockInstance, Term.blockName, hD, ite_true] at h
    exact nomatch h
  all_goals intros; trivial

end

/-! ## Nested Types of a Well-Formed Signature -/

mutual

/-- A type typed in the signature `Σ_T` and strictly positive in the variables with a position is
read by `rd` at its nesting, given the soundness of the typing in `Σ_T` and the clause of the
instances of `rd`: a type without position is the same at the two pairs of substitutions, a
variable with a position is read as given, and an instance of a declared type whose arguments have
positions is read by the clause, at the pairs of substitutions that its arguments give. -/
theorem Term.nestReads (hS : TypingSound sig ι) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT) (hinst : ReadsInstances sig ι rd sigT)
    (decl : TypeDeclaration) (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {k : Nat}
    (ρ : Fin k → Nat) {Γ : Scope} {ctx : Context k Γ} {T : Term k Γ} {Γ' : Scope}
    (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting α Γ'} {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'} :
    (A : Term k Γ) → HasType sigT ctx A T →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) x (A.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' → ∀ s,
      rd s .plain .plain (((A.rename β).atLevels ρ).subst σ₁)
        (((A.rename β).atLevels ρ).subst σ₂) →
      rd s ((A.rename β).nest (fun _ => none) @ν₁)
        ((A.rename β).nest (fun _ => none) @ν₂) (((A.rename β).atLevels ρ).subst σ₁')
        (((A.rename β).atLevels ρ).subst σ₂')
  | .var (e := .var) x .nil, _, hpos, _, hNS, s, hr => by
    cases hpl : (ν₁ (β x)).isPlain with
    | true => exact hNS.reads_of_plain ρ hpos hpl hr
    | false => exact hNS.var (β x) hpl s hr
  | .var (e := .secondOrder ps ψ) X ts, hA, hpos, hE, hNS, s, hr => by
    cases hpl : (ν₁ (β X)).isPlain with
    | true => exact hNS.reads_of_plain ρ hpos hpl hr
    | false =>
      obtain ⟨Θ, A', hX, hts⟩ := hA.secondOrder_inv
      have hfree : ∀ (e : Scope.Entry) (y : Var Γ' e), (ν₁ y).isPlain = false →
          ((ts.rename β).atLevels ρ).Avoids y := fun e y hy => by
        have h := hpos e y hy
        rw [Term.rename] at h
        exact h.var_args.substLevels _
      obtain ⟨et₁, et₂⟩ := hNS.args_eq hfree
      have ets : ∀ σ : Subst 0 [] Γ', ((ts.rename β).atLevels ρ).subst σ =
          (ts.atLevels ρ).subst (fun x => σ (β x)) := fun σ => by
        rw [Args.atLevels, Args.substLevels_rename]
        exact Args.subst_rename_of (fun _ => rfl) _
      have hsub : ∀ σ : Subst 0 [] Γ', (((Term.var X ts).rename β).atLevels ρ).subst σ =
          (σ (β X)).subst (((ts.rename β).atLevels ρ).subst σ).toSubst := fun σ => by
        rw [Term.rename, Term.atLevels, Term.substLevels, Term.subst]
        exact Term.instantiate_eq_subst _ _
      have hnest : ∀ ν : Nesting α Γ',
          ((Term.var X ts).rename β).nest (fun _ => none) @ν = ν (β X) := fun ν => by
        rw [Term.rename, Term.nest]
      rw [hsub, hsub, ets, ets] at hr
      rw [hsub, hsub, hnest, hnest, et₁, et₂, ets, ets]
      exact hNS.secondOrder X (hX.substLevels _) hpl s _ _ ((hS.hasArgs hent hts ρ).2 _ _ hE) hr
  | .inst (Δ := Δ) D qs ls ps as, hA, hpos, hE, hNS, s, hr => by
    cases hpl : (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₁).isPlain with
    | true => exact hNS.reads_of_plain ρ hpos hpl hr
    | false =>
      -- The arguments of the instance, at the nestings of the variables.
      have ih : ∀ {params : Context k Δ}, HasInstanceArgs sigT ctx as params →
          (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
            InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β)) →
          NestSubst sig ι rd (params.atLevels ρ) (fun x => x)
            (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁))
            (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₂))
            (((as.rename β).atLevels ρ).subst σ₁).toSubst
            (((as.rename β).atLevels ρ).subst σ₂).toSubst
            (((as.rename β).atLevels ρ).subst σ₁').toSubst
            (((as.rename β).atLevels ρ).subst σ₂').toSubst :=
        fun has hp => InstanceArgs.nestSubst hS hent hinst decl fresh ρ β D as has hp hE hNS
      exact hinst hA decl fresh ρ β
        (fun e x hx => by
          have h := hpos e x hx
          rw [Term.rename] at h
          exact h.inst_args)
        hE (fun x => hNS.isPlain x)
        (fun has => ih has fun e x hx => by
          have h := hpos e x hx
          rw [Term.rename] at h
          exact h.inst_args)
        hpl s hr
  | .sort _, _, hpos, _, hNS, _, hr | .const _ _ _ _, _, hpos, _, hNS, _, hr
  | .ctor _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .recursor _ _ _ _ _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .obs _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .corec _ _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .equality .., _, hpos, _, hNS, _, hr | .refl .., _, hpos, _, hNS, _, hr
  | .transp .., _, hpos, _, hNS, _, hr | .propExt .., _, hpos, _, hNS, _, hr
  | .coind .., _, hpos, _, hNS, _, hr =>
    hNS.reads_of_plain ρ hpos rfl hr

/-- The arguments of an instance typed in the signature `Σ_T` and strictly positive in the
variables with a position give the parameters, at the two pairs of substitutions, two pairs of
substitutions of the parameters, at the nestings of the arguments: the argument of each parameter
is read at its nesting, as a type under the variables of its abstraction. -/
theorem InstanceArgs.nestSubst (hS : TypingSound sig ι) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT) (hinst : ReadsInstances sig ι rd sigT)
    (decl : TypeDeclaration) (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {k : Nat}
    (ρ : Fin k → Nat) {Γ : Scope} {ctx : Context k Γ} {Γ' : Scope}
    (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting α Γ'} {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'} (D : Name) :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → {params : Context k Δ} →
      HasInstanceArgs sigT ctx as params →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι rd (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' →
      NestSubst sig ι rd (params.atLevels ρ) (fun x => x)
        (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁))
        (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₂))
        (((as.rename β).atLevels ρ).subst σ₁).toSubst (((as.rename β).atLevels ρ).subst σ₂).toSubst
        (((as.rename β).atLevels ρ).subst σ₁').toSubst
        (((as.rename β).atLevels ρ).subst σ₂').toSubst
  | _, .nil, _, .nil _, _, _, _ =>
    { isPlain := fun x => (nomatch x), left := fun x => (nomatch x), right := fun x => (nomatch x),
      var := fun x => (nomatch x), secondOrder := fun X => (nomatch X) }
  | _, .snoc (e := .var) as a, _, .var (A := A₀) has ha, hpos, hE, hNS => by
    have hposas : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β) := fun e x hx => by
      have h := hpos e x hx
      rw [InstanceArgs.rename] at h
      cases h with
      | positive _ h' _ => exact h'
      | absent h' _ => exact h'
    have hposa : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) x (a.rename β) := fun e x hx => by
      have h := hpos e x hx
      rw [InstanceArgs.rename] at h
      cases h with
      | positive _ _ hB => exact hB
      | absent _ hB => exact .absent hB
    have ih := InstanceArgs.nestSubst hS hent hinst decl fresh ρ β D as has hposas hE hNS
    exact (ih.params_var (A₀.atLevels ρ)
      (l₁ := (a.rename β).nest (fun _ => none) @ν₁) (l₂ := (a.rename β).nest (fun _ => none) @ν₂)
      (t₁ := ((a.rename β).atLevels ρ).subst σ₁) (t₂ := ((a.rename β).atLevels ρ).subst σ₂)
      (t₁' := ((a.rename β).atLevels ρ).subst σ₁') (t₂' := ((a.rename β).atLevels ρ).subst σ₂')
      (Term.nest_isPlain_congr (fun _ x => hNS.isPlain x) _)
      (fun h => (hNS.plain_eq ρ hposa h).1) (fun h => (hNS.plain_eq ρ hposa h).2)
      (fun _ s hr => Term.nestReads hS hent hinst decl fresh ρ β a ha hposa hE hNS s
        hr)).congr_subst
      (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)
      (fun x => by cases x <;> rfl)
  | _, .snoc (e := .secondOrder ps ψ) as B, _, .secondOrder (Θ := Θ₀) (A := A₀) has hB, hpos, hE,
      hNS => by
    have hposas : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β) := fun e x hx => by
      have h := hpos e x hx
      rw [InstanceArgs.rename] at h
      cases h with
      | positive _ h' _ => exact h'
      | absent h' _ => exact h'
    have hposB : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) (x.weakenN ps.length)
          (B.rename (Ren.liftN ps.length @β)) := fun e x hx => by
      have h := hpos e x hx
      rw [InstanceArgs.rename] at h
      cases h with
      | positive _ _ hB' => exact hB'
      | absent _ hB' => exact .absent hB'
    have ih := InstanceArgs.nestSubst hS hent hinst decl fresh ρ β D as has hposas hE hNS
    have eas : ∀ σ : Subst 0 [] Γ', ((as.rename β).atLevels ρ).subst σ =
        (as.atLevels ρ).subst (fun x => σ (β x)) := fun σ => by
      rw [InstanceArgs.atLevels, InstanceArgs.substLevels_rename]
      exact InstanceArgs.subst_rename_of (fun _ => rfl) _
    refine (ih.params_secondOrder (Θ₀.atLevels ρ) (A₀.atLevels ρ) ψ
      (l₁ := (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₁))
      (l₂ := (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₂))
      (f₁ := ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.liftN ps.length @σ₁))
      (f₂ := ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.liftN ps.length @σ₂))
      (f₁' := ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst
        (Subst.liftN ps.length @σ₁'))
      (f₂' := ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst
        (Subst.liftN ps.length @σ₂'))
      (Term.nest_isPlain_congr (Nesting.liftN_isPlain_congr ps.length fun _ x => hNS.isPlain x) _)
      (fun h => (hNS.plain_eq_liftN ps.length ρ hposB h).1)
      (fun h => (hNS.plain_eq_liftN ps.length ρ hposB h).2)
      (fun _ s τ₁ τ₂ hτ hr => ?_)).congr_subst
      (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl) (fun x => by cases x <;> rfl)
      (fun x => by cases x <;> rfl)
    rw [Term.subst_append, Term.subst_append] at hr ⊢
    have eσ : ∀ (σ : Subst 0 [] Γ') (τ : Subst 0 [] (Scope.extend [] ps.length)),
        @Eq (Subst 0 [] (Γ.extend ps.length))
          (fun x => Subst.append σ τ (Ren.liftN ps.length @β x))
          (Subst.append (fun x => σ (β x)) τ) := fun σ τ =>
      Subst.ext (Subst.append_liftN_rename β (fun _ => rfl) τ)
    have hΘeq : ((Θ₀.subst as.toSubst).atLevels ρ).subst (fun x => σ₁ (β x)) =
        (Θ₀.atLevels ρ).subst (fun x => (((as.rename β).atLevels ρ).subst σ₁).toSubst x) := by
      rw [eas, Telescope.atLevels, Telescope.substLevels_subst_of
        (InstanceArgs.toSubst_substLevels _ as)]
      exact Telescope.subst_subst_of (InstanceArgs.toSubst_subst _ _) _
    refine Term.nestReads hS hent hinst decl fresh ρ (Ren.liftN ps.length @β) B hB
      (fun e z hz => ?_) ?_ ?_ s hr
    · obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z fun h => by
        rw [h] at hz
        exact nomatch hz
      exact hposB e x (Nest.isPlain_eq_false hx)
    · rw [Context.atLevels, Context.substLevels_append]
      exact (EqSubst.congr (eσ σ₁ τ₁) (eσ σ₂ τ₂)).2
        ((EqSubst.append_append_iff _ _ _ _ τ₁ τ₂).2 ⟨hE, hΘeq ▸ hτ⟩)
    · rw [Context.atLevels, Context.substLevels_append]
      exact hNS.append _ τ₁ τ₂

end

/-- The types typed in a signature are read by `rd`, given the soundness of the typing in it and
the clause of the instances of `rd`. -/
theorem ReadsInstances.readsNested (hS : TypingSound sig ι) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT) (hinst : ReadsInstances sig ι rd sigT) :
    ReadsNested sig ι rd sigT :=
  fun hA decl fresh ρ _ β _ _ _ _ _ _ hpos hE hNS s hr =>
    Term.nestReads hS hent hinst decl fresh ρ β _ hA hpos hE hNS s hr

/-- The clause of the instances of a reading holds in the signatures whose entries have their
meaning, given the soundness of the typing in them: an instance of a declared type one of whose
arguments has a position is that of a codata type none of whose destructors is recursive, strictly
positive in the parameters whose arguments have positions, whose destructors are read at the
nestings of its arguments, by their formation in the signature before it; by induction on the
signature, since the destructors of a codata type are typed in the signature before its
declaration. -/
theorem Reading.readsInstances (R : Reading sig ι α I) (hS : TypingSound sig ι) :
    (sigT : Signature) → sig.ValidEntries ι sigT → ReadsInstances sig ι R.rd sigT
  | sigT, hent => fun hA decl fresh ρ _ β _ _ _ _ _ _ hposA hE hiso ih hpl s hr => by
    rename_i k Γ Δ ctx D qs ls ps as _ Γ' ν₁ ν₂ σ₁ σ₂ σ₁' σ₂'
    obtain ⟨declF, ζ, hΔ, hqp, hl, hD, hadm, has⟩ := hA.inst_inv
    subst hΔ
    have hsigT : WfSig sigT := presuppositions.wfCtx (contextPresuppositions.hasType hA)
    have hdT := hsigT.distinct
    have hpl₂ : (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₂).isPlain =
        false := (Term.nest_isPlain_congr (fun _ x => hiso x) _).symm.trans hpl
    have hall : ∀ ν : Nesting α Γ',
        (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν).isPlain = false →
        ((as.rename β).nest (fun _ => none) @ν).all Nest.isPlain = false ∧
          ((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν =
            .inst ((as.rename β).nest (fun _ => none) @ν) := fun ν h => by
      rw [Term.rename, Term.nest] at h ⊢
      rw [Nest.isPlain_ofArgs] at h
      refine ⟨h, ?_⟩
      unfold Nest.ofArgs
      rw [h]
      rfl
    obtain ⟨hall₁, hnest₁⟩ := hall @ν₁ hpl
    obtain ⟨-, hnest₂⟩ := hall @ν₂ hpl₂
    -- The declared type is a codata type none of whose destructors is recursive, strictly
    -- positive in its parameters whose arguments have positions.
    have hmark : ∀ {e' : Scope.Entry} (y : Var declF.scope e'),
        (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁) y).isPlain = false →
        sigT.PositiveIn decl D y.level := fun y hy =>
      InstanceArgs.marks_of_nest (fun e x hx => hposA e x (Nest.isPlain_eq_false hx)) y
        fun h => by
          rw [h] at hy
          exact nomatch hy
    have hDn : D ∈ declF.names := by
      rcases hD.2 with ⟨T, hT, rfl, -⟩ | ⟨T, hT, rfl, -⟩
      · exact TypeDeclaration.name_mem_names hT
      · exact TypeDeclaration.codata_name_mem_names hT
    have hcod : ∀ i, sigT.PositiveIn decl D i →
        ∃ T : CodataType declF.sorts declF.grades declF.levels declF.scope,
          sigT.HasCodataType D declF T ∧ T.positive i = true ∧
            ∀ J, ∀ r ∈ (T.body J).recursion declF.names, r = none := fun i hi => by
      rcases hi with hi | ⟨decl', T, hT, hTp, hTr⟩
      · have hDd : D ∈ decl.names := by
          rcases hi with ⟨T, hT, rfl, -⟩ | ⟨T, hT, rfl, -⟩
          · exact TypeDeclaration.name_mem_names hT
          · exact TypeDeclaration.codata_name_mem_names hT
        exact absurd hDn (fresh _ hD.1 D hDd)
      · have he := hdT.entry_unique hT.1 hD.1 (n := D)
          (hT.2.2 ▸ TypeDeclaration.codata_name_mem_names hT.2.1) hDn
        injection he with he
        subst he
        exact ⟨T, hT, hTp, hTr⟩
    obtain ⟨e₀, y₀, hy₀⟩ := InstanceArgs.exists_ofArgs (fun _ => none) (as.rename β) hall₁
    obtain ⟨T, hT, -, hTrec⟩ := hcod _ (hmark y₀ hy₀)
    have hTmark : ∀ {e' : Scope.Entry} (y : Var declF.scope e'),
        (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁) y).isPlain = false →
        T.positive y.level = true := fun y hy => by
      obtain ⟨T', hT', hp', -⟩ := hcod _ (hmark y hy)
      obtain ⟨-, hTT⟩ := hdT.hasCodataType_unique hT hT'
      cases hTT
      exact hp'
    -- Its formation, in the signature before it.
    obtain ⟨sigF, hsuf, hdecl⟩ := hsigT.wfTypeDeclaration hT.1
    have hentF : sig.ValidEntries ι sigF :=
      fun e he => hent e (Signature.subset_of_cons_suffix hsuf he)
    have freshF : ∀ e ∈ sigF, ∀ D' ∈ declF.names, D' ∉ e.names := hdecl.fresh
    cases hdecl with
    | data hb _ _ _ _ _ _ => exact absurd hT.2.1 (by simp [TypeDeclaration.codataTypes, hb])
    | codata hb _ _ hds hpF _ _ =>
      have hl' : (ls.map (Level.atLevels ρ)).length = declF.levels := Level.length_atLevels ρ hl
      have hTm := (hent.hasCodataType hT).1
      have hinst : ∀ σ : Subst 0 [] Γ',
          (((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ =
            .inst D qs (ls.map (Level.atLevels ρ)) ps
              (((as.rename β).atLevels ρ).subst σ) := fun σ => by
        rw [Term.rename, Term.atLevels, Term.substLevels, Term.subst]
        rfl
      rw [hinst, hinst] at hr
      rw [hinst, hinst, hnest₁, hnest₂]
      -- The instance lives in a sort of the reading, which reads it from its destructors.
      obtain ⟨j, hok, hfin⟩ := R.inst
        (νs₁ := (as.rename β).nest (fun _ => none) @ν₁)
        (νs₂ := (as.rename β).nest (fun _ => none) @ν₂)
        (as₁' := ((as.rename β).atLevels ρ).subst σ₁')
        (as₂' := ((as.rename β).atLevels ρ).subst σ₂') hTm hqp hl' (hTrec _) hadm hr
      refine hfin ?_
      -- The values of the levels of the instance.
      let ρF : Fin declF.levels → Nat := fun i =>
        ((ls.map (Level.atLevels ρ)).getFin hl' i).closedValue
      have hget : ∀ i,
          (ls.map (Level.atLevels ρ)).getFin hl' i =
            (ls.getFin hl i).atLevels ρ :=
        fun i => congrFun (Level.getFin_map_subst _ ls hl) i
      have hctxEq : Context.LevelEquiv
          (((declF.params hqp.inst).substLevels (ls.getFin hl)).atLevels ρ)
          ((declF.params hqp.inst).atLevels ρF) := by
        rw [Context.atLevels, Context.substLevels_substLevels]
        refine Context.substLevels_levelEquiv (fun i => ?_) _
        show (ls.getFin hl i).atLevels ρ ≈ _
        rw [← hget i]
        exact Level.equivalence.symm (Level.ofNat_closedValue _)
      -- The arguments at the first pair are equal arguments of the parameters.
      have eas : ∀ σ : Subst 0 [] Γ', ((as.rename β).atLevels ρ).subst σ =
          (as.atLevels ρ).subst (fun x => σ (β x)) := fun σ => by
        rw [InstanceArgs.atLevels, InstanceArgs.substLevels_rename]
        exact InstanceArgs.subst_rename_of (fun _ => rfl) _
      have hEF : EqSubst sig ι ((declF.params hqp.inst).atLevels ρF)
          (fun x => (((as.rename β).atLevels ρ).subst σ₁).toSubst x)
          (fun x => (((as.rename β).atLevels ρ).subst σ₂).toSubst x) := by
        rw [eas, eas]
        exact EqSubst.levelEquiv hctxEq ((hS.hasInstanceArgs hent has ρ).2 _ _ hE)
      -- The destructors of the type, at the nestings of the arguments.
      have hread : ReadsNested sig ι R.rd sigF :=
        ReadsInstances.readsNested hS hentF (Reading.readsInstances R hS sigF hentF)
      have hdr := WfDestructors.reads R hS hentF hread freshF ρF j (β := fun x => x)
        (hds _ hadm T hT.2.1) (hTrec _) hok
        (fun e y h => by
          cases hy : (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁) y).isPlain with
          | true => rfl
          | false =>
            simp only [Nesting.ofPositive, hTmark y hy, ite_true] at h
            exact nomatch h)
        (fun e y hy => by
          rw [Destructors.rename_id_of (fun _ => rfl)]
          exact hpF _ hadm T hT.2.1 y (hTmark y hy))
        hEF ((ih has).levelEquiv hctxEq)
      rw [Destructors.rename_id_of (fun _ => rfl)] at hdr
      exact hdr
termination_by sigT => sigT.length
decreasing_by
  have := List.IsSuffix.length_le hsuf
  simp only [List.length_cons] at this ⊢
  omega

end

end

end Sic.Core
