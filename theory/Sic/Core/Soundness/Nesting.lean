module

public import Sic.Core.Soundness.Levels
public import Sic.Core.Soundness.Signature
public import Sic.Core.Typing
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Positivity.Nesting
import Sic.Core.Positivity.Substitution
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Substitution.Nesting
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Inversion
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature

/-!
# Soundness of the Nested Types

A type that is strictly positive in variables, as annex 14 of RFC 36 says it, is read by the graph
of the nestings of annex 18 at any closed types given for these variables, when the graph reads
them at their nestings: the equality of its terms is then the same at two substitutions, as the
meaning of a nested field of a block asks, whatever the relations given at its positions.

The types given for the variables with a position have no meaning yet, as the types of a block
before its meaning, so that the judgments typed with these variables say nothing of them: the proof
carries, beside them, two equal closed substitutions of the context, at which every judgment is
meaningful, and which give the same abstractions to the variables without position.
What a variable with a position does not occur in is then the same at both, and has its meaning,
and a type whose nesting has a position is a variable with a position, read as given, or an
instance of a codata type none of whose destructors is recursive, whose formation gives the strict
positivity of its destructors and their typing in the signature before it: the proof is by
induction on the signature, and reads the destructors of such a type by induction on their
formation, where the destructors after a destructor whose result has a position do not depend on
it.

The destructors after a destructor whose result has a position are typed in its context, and are
those of the declaration renamed, which the strict positivity of the declaration reads: the
properties are stated of a type or of destructors renamed, the substitutions and the nestings being
those of the scope that the renaming reaches, so that no property of a renamed term has to be
moved back to the term.

The soundness of the typing is proved from these properties, which read it at the judgments of the
signatures before: they take it as a hypothesis, `TypingSound`.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Types Read by the Graph of the Nestings -/

-- ADE: none.
/-- The graph of the nestings of the sort of the quality `s` at the level `n` reads two closed
types, each at its nesting, with the same equality of their terms. -/
def NestReads (sig : Signature) (ι : Interpretation) (n : Nat) (s : Quality)
    (τ₁ τ₂ : Nest NestLeaf) (A₁ A₂ : Term 0 []) : Prop :=
  ∃ F, NestRel sig ι n (fun m _ => levelRel sig ι m) s τ₁ A₁ F ∧
    NestRel sig ι n (fun m _ => levelRel sig ι m) s τ₂ A₂ F

-- ADE: none.
/-- Two pairs of closed substitutions of a scope `Γ'`, which the renaming `β` reaches from the
scope of a context: `(σ₁, σ₂)`, at which the judgments of the context are meaningful, and
`(σ₁', σ₂')`, which give the variables with a position, by the nestings `ν₁` and `ν₂`, types that
the graph of the nestings reads at them with the same equality of their terms, at the arguments at
which it reads those of the first pair without position, and which give the other variables what
the first pair gives them.
The renaming is that of the destructors after a destructor on which they do not depend, which the
strict positivity reads renamed. -/
structure NestSubst (sig : Signature) (ι : Interpretation) (n : Nat) {Γ' Γ : Scope}
    (ctx : Context 0 Γ) (β : Ren Γ' Γ) (ν₁ ν₂ : Nesting NestLeaf Γ')
    (σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ') : Prop where
  /-- The two nestings give a position to the same variables. -/
  isPlain : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = (ν₂ x).isPlain
  /-- The first substitutions give the same abstraction to a variable without position. -/
  left : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = true → σ₁' x = σ₁ x
  /-- The second substitutions give the same abstraction to a variable without position. -/
  right : ∀ {e : Scope.Entry} (x : Var Γ' e), (ν₁ x).isPlain = true → σ₂' x = σ₂ x
  /-- A variable with a position is given types read at its nestings. -/
  var : ∀ (x : Var Γ' .var), (ν₁ x).isPlain = false → ∀ s,
    NestReads sig ι n s .plain .plain (σ₁ x) (σ₂ x) →
      NestReads sig ι n s (ν₁ x) (ν₂ x) (σ₁' x) (σ₂' x)
  /-- A second-order variable of the context with a position is given abstractions whose instances
  at equal arguments of its telescope are read at its nestings. -/
  secondOrder : ∀ {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
    (X : Var Γ (.secondOrder ps ψ)) {Θ : Telescope 0 Γ ps} {A : Term 0 (Γ.extend ps.length)},
    ctx.SecondOrderIn X Θ A → (ν₁ (β X)).isPlain = false → ∀ s τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ.subst fun x => σ₁ (β x))) τ₁ τ₂ →
      NestReads sig ι n s .plain .plain ((σ₁ (β X)).subst τ₁) ((σ₂ (β X)).subst τ₂) →
        NestReads sig ι n s (ν₁ (β X)) (ν₂ (β X)) ((σ₁' (β X)).subst τ₁) ((σ₂' (β X)).subst τ₂)

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

variable {n : Nat} {Γ' Γ : Scope} {ctx : Context 0 Γ} {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting NestLeaf Γ'}
  {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'}

/-- The pairs of substitutions of a context are those of a context equal to it up to its levels. -/
theorem NestSubst.levelEquiv {ctx' : Context 0 Γ} (hctx : Context.LevelEquiv ctx ctx')
    (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂') :
    NestSubst sig ι n ctx' @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' where
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
theorem NestSubst.lift (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (Θ : Telescope 0 Γ ps) (B : Term 0 (Γ.extend ps.length))
    (ψ : ResultOwnership Grade ps.length) (f₁ f₂ : Term 0 (Scope.extend [] ps.length)) :
    NestSubst sig ι n (ctx.secondOrder Θ B ψ) (Ren.lift @β)
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
theorem NestSubst.skip (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (ψ : ResultOwnership Grade ps.length)
    (f₁ f₂ : Term 0 (Scope.extend [] ps.length)) :
    NestSubst sig ι n ctx (fun x => .succ (β x))
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
theorem NestSubst.append (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {ps : List Parameter} (Θ : Telescope 0 Γ ps) (τ₁ τ₂ : Subst 0 [] (Scope.extend [] ps.length)) :
    NestSubst sig ι n (ctx.append Θ) (Ren.liftN ps.length @β) (Nesting.liftN ps.length @ν₁)
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
theorem NestSubst.telescope_eq (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
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
theorem NestSubst.term_eq (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
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
theorem NestSubst.args_eq (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
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

/-! ## Destructors Read by the Graph of the Nestings -/

/-- A destructor whose arguments are equal telescopes and whose results are equal types at two
equal closed substitutions, and are the same at two other substitutions, followed by destructors
that the graph of the nestings reads with one equality at these, for each pair of equal
abstractions for it, is read with them by the graph of the nestings with one equality, as a
destructor whose result has no position: the equality of its results and that of the destructors
after it are defined from the graph at the first substitution, which gives one at most. -/
theorem NestDesRel.of_plain_head (hd : sig.Distinct) {n : Nat} {κ κ₁ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting NestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
    (hν₁ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) = .plain)
    (hν₂ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) = .plain)
    (hΘ : ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂))
    (hΘ₁ : Θ.subst θ₁' = Θ.subst θ₁) (hΘ₂ : Θ.subst θ₂' = Θ.subst θ₂) (hκ : κ₁ ≼ κ)
    (hB : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
        (.sort κ₁))
    (hB₁ : ∀ τ, B.subst (Subst.append θ₁' τ) = B.subst (Subst.append θ₁ τ))
    (hB₂ : ∀ τ, B.subst (Subst.append θ₂' τ) = B.subst (Subst.append θ₂ τ))
    (hds : ∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
      ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁) S ∧
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) S) :
    ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₁
        (.cons (d := d) p q ς Θ B ψ ds) @θ₁' S ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₂
        (.cons (d := d) p q ς Θ B ψ ds) @θ₂' S := by
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have ihκ : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  have hSp := TelRel.isPer hd ihκ (fun _ => .plain) hT₁
  have hκn : κ₁.level.closedValue ≤ n := Nat.le_trans (hκ.2 Fin.elim0) hn
  -- The results at the first substitution and equal arguments are equal types.
  have hBB : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst))
        (B.subst (Subst.append θ₁ us.toSubst)) (.sort κ₁) := fun ts us hts =>
    have huu := hSp.trans (hSp.symm hts) hts
    (hB _ _ ((hT ts us).1 hts)).trans (hB _ _ ((hT us us).1 huu)).symm
  let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ w F', Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
      FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w F' ∧ F' t u
  have hFeq : ∀ (ts : Args 0 [] ps) w F₀,
      Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w →
      FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w F₀ →
      F ts.terms = F₀ := fun ts w F₀ hw hF₀ =>
    funext fun t => funext fun u => propext
      ⟨fun ⟨ts', hts', w', F', hw', hF', h'⟩ => by
        cases Args.terms_inj hts'
        cases Computesι.det hd hw hw'
        exact (FieldRel.unique hd ih hF' _ _ hF₀ t u).1 h',
      fun h' => ⟨ts, rfl, w, F₀, hw, hF₀, h'⟩⟩
  -- A type equal to the result at the first substitution and the arguments `ts` has the
  -- equality `F ts`.
  have hres : ∀ (ts : Args 0 [] ps) (A : Term 0 []),
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst)) A (.sort κ₁) →
      (∃ w, Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w (F ts.terms)) ∧
      ∃ v, Computesι sig ι A v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality v (F ts.terms) :=
    fun ts A hA => by
      obtain ⟨w₁, w₂, F₀, hw₁, hw₂, hF₁, hF₂, -⟩ := hA.fieldRel hκ.1 hκn
      rw [hFeq ts w₁ F₀ hw₁ hF₁]
      exact ⟨⟨w₁, hw₁, hF₁⟩, w₂, hw₂, hF₂⟩
  have hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u := fun ts us hts t u => by
    obtain ⟨ts', us', rfl, rfl, -⟩ := hT₁.to_eqSubst hd
      (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) _ _ hts
    have huu := hSp.trans (hSp.symm hts) hts
    obtain ⟨⟨w', hw', -⟩, -⟩ := hres us' _ (hBB us' us' huu)
    obtain ⟨-, v, hv, hFv⟩ := hres ts' _ (hBB ts' us' hts)
    cases Computesι.det hd hw' hv
    rw [hFeq us' w' _ hw' hFv]
  -- Equal abstractions for the destructor have equal instances at equal arguments.
  have hcond : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁)) :=
    fun f₁ f₂ hf τ₁ τ₂ hτ => by
      obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
          @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
        ⟨_, Subst.args_toSubst ps τ₁⟩
      obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
          @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
        ⟨_, Subst.args_toSubst ps τ₂⟩
      have hts := (hT ts us).2 hτ
      have htt := hSp.trans hts (hSp.symm hts)
      obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts htt)
      exact hF.validEqTerm hd hw (hf _ _ hts)
  let G : Term 0 (Scope.extend [] ps.length) → ObsRel := fun f o₁ o₂ => ∃ S',
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' ∧ S' o₁ o₂
  have hGeq : ∀ f S', NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' → G f = S' := fun f S' hS' =>
    funext fun o₁ => funext fun o₂ => propext
      ⟨fun ⟨_, h', hs⟩ => (NestDesRel.unique hd ih h' _ _ hS' o₁ o₂).1 hs,
        fun hs => ⟨S', hS', hs⟩⟩
  have hG : ∀ f, AbstractionRel SΘ F f f →
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
        (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) (G f) ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
        (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₂' f) (G f) := fun f hf => by
    obtain ⟨S', h₁, h₂⟩ := hds f f (hcond f f hf)
    rw [hGeq f S' h₁]
    exact ⟨h₁, h₂⟩
  have hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂ :=
    fun f₁ f₂ hf o₁ o₂ => by
      have hEp := AbstractionRel.isPer hSp (fun ts hts =>
        have ⟨⟨_, _, hF⟩, _⟩ := hres ts _ (hBB ts ts hts)
        FieldRel.isPer hd ih hF) hBresp
      obtain ⟨S', h₁, h₂⟩ := hds f₁ f₂ (hcond f₁ f₂ hf)
      have hf₂ := hEp.trans (hEp.symm hf) hf
      obtain ⟨S'', h₁', h₂'⟩ := hds f₂ f₂ (hcond f₂ f₂ hf₂)
      rw [hGeq f₁ S' h₁, hGeq f₂ S'' h₁']
      exact NestDesRel.unique hd ih h₂ _ _ h₂' o₁ o₂
  refine ⟨_, .cons hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).1) hresp,
    .cons hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).2) hresp⟩
  · obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts hts)
    rw [hB₁]
    exact .plain hw hF
  · obtain ⟨-, v, hv, hF⟩ := hres ts _ (hB _ _ ((hT ts ts).1 hts))
    rw [hB₂]
    exact .plain hv hF

/-- A destructor whose arguments are equal telescopes at two equal closed substitutions, and are
the same at two other substitutions, at which the graph of the nestings reads its results at their
nestings with one equality, at equal arguments, followed by destructors that the graph reads with
one equality at these substitutions, for each pair of abstractions for it, is read with them by the
graph of the nestings with one equality, as a destructor whose result has a position. -/
theorem NestDesRel.of_nested_head (hd : sig.Distinct) {n : Nat} {κ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting NestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
    (hν₁ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) ≠ .plain)
    (hν₂ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) ≠ .plain)
    (hΘ : ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂))
    (hΘ₁ : Θ.subst θ₁' = Θ.subst θ₁) (hΘ₂ : Θ.subst θ₂' = Θ.subst θ₂)
    (hB : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      NestReads sig ι n κ.quality (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂))
        (B.subst (Subst.append θ₁' τ₁)) (B.subst (Subst.append θ₂' τ₂)))
    (hds : ∀ f₁ f₂, ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁) S ∧
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) S) :
    ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₁
        (.cons (d := d) p q ς Θ B ψ ds) @θ₁' S ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₂
        (.cons (d := d) p q ς Θ B ψ ds) @θ₂' S := by
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have ihκ : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  have hSp := TelRel.isPer hd ihκ (fun _ => .plain) hT₁
  let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ F', NestRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
      (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
      (B.subst (Subst.append θ₁' ts.toSubst)) F' ∧ F' t u
  have hFeq : ∀ (ts : Args 0 [] ps) F₀,
      NestRel sig ι n (fun m _ => levelRel sig ι m) κ.quality
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.subst (Subst.append θ₁' ts.toSubst)) F₀ → F ts.terms = F₀ := fun ts F₀ hF₀ =>
    funext fun t => funext fun u => propext
      ⟨fun ⟨ts', hts', F', hF', h'⟩ => by
        cases Args.terms_inj hts'
        exact (NestRel.unique hd ih hF' _ _ hF₀ t u).1 h',
      fun h' => ⟨ts, rfl, F₀, hF₀, h'⟩⟩
  have hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u := fun ts us hts t u => by
    obtain ⟨ts', us', rfl, rfl, hE⟩ := hT₁.to_eqSubst hd
      (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) _ _ hts
    have huu := hSp.trans (hSp.symm hts) hts
    obtain ⟨F', h₁, h₂⟩ := hB _ _ hE
    obtain ⟨F'', h₁', h₂'⟩ := hB _ _ ((hT us' us').1 huu)
    rw [hFeq ts' F' h₁, hFeq us' F'' h₁']
    exact NestRel.unique hd ih h₂ _ _ h₂' t u
  -- The destructors after it have one equality, whatever the abstractions for it.
  let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
  obtain ⟨G, h₀₁, h₀₂⟩ := hds f₀ f₀
  refine ⟨_, .nested hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F (fun ts hts => ?_) hBresp G (fun f => ?_),
    .nested hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F (fun ts hts => ?_) hBresp G (fun f => ?_)⟩
  · obtain ⟨F', h₁, -⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hFeq ts F' h₁]
    exact h₁
  · obtain ⟨S, h₁, h₂⟩ := hds f f₀
    have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
      (NestDesRel.unique hd ih h₂ _ _ h₀₂ o₁ o₂)
    exact hSG ▸ h₁
  · obtain ⟨F', h₁, h₂⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hFeq ts F' h₁]
    exact h₂
  · obtain ⟨S, h₁, h₂⟩ := hds f₀ f
    have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
      (NestDesRel.unique hd ih h₁ _ _ h₀₁ o₁ o₂)
    exact hSG ▸ h₂

/-! ## Nested Types of a Signature -/

-- ADE: none.
/-- The types typed in the signature `Σ_T` and strictly positive in the variables with a position
are read by the graph of the nestings at their nestings, with one equality of their terms, at the
second pair of two pairs of substitutions, when they are read without position, with one equality
of their terms, at the first pair, whose substitutions of the context are equal; the strict
positivity reads the parameters that a block `𝒟` whose names are fresh declares, and those that the
codata types of `Σ_T` do. -/
def ReadsNested (sig : Signature) (ι : Interpretation) (sigT : Signature) : Prop :=
  ∀ {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A T : Term k Γ}, HasType sigT ctx A T →
    ∀ (decl : TypeDeclaration), (∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) →
    ∀ (ρ : Fin k → Nat) (n : Nat) {Γ' : Scope} (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting NestLeaf Γ'}
      {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'},
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) x (A.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι n (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' → ∀ s,
      NestReads sig ι n s .plain .plain (((A.rename β).atLevels ρ).subst σ₁)
        (((A.rename β).atLevels ρ).subst σ₂) →
      NestReads sig ι n s ((A.rename β).nest (fun _ => none) @ν₁)
        ((A.rename β).nest (fun _ => none) @ν₂) (((A.rename β).atLevels ρ).subst σ₁')
        (((A.rename β).atLevels ρ).subst σ₂')

-- ADE: none.
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

-- ADE: none.
/-- The destructors of a codata type none of which is recursive, well formed in a signature `Σ_T`
whose nested types the graph of the nestings reads, and strictly positive in the variables with a
position, are read by the graph of the nestings with one equality of the abstractions for them, at
the second pair of two pairs of substitutions, the first of which are equal substitutions of their
context, given the soundness of the typing in `Σ_T`: by induction on their formation, where the
destructors after a destructor whose result has a position are read whatever the abstractions for
it, on which they do not depend. -/
theorem WfDestructors.nestDesRel (hS : TypingSound sig ι) (hd : sig.Distinct) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT) (hread : ReadsNested sig ι sigT) {decl : TypeDeclaration}
    (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {I : Instance decl.sorts decl.grades}
    (ρ : Fin decl.levels → Nat) (n : Nat) {Γ : Scope} {ns : List Name} {ν₀ : Nesting Nat Γ}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} {Γ' : Scope} {β : Ren Γ' Γ}
    {ν₁ ν₂ : Nesting NestLeaf Γ'} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ'} :
    WfDestructors sigT decl I @ν₀ as ctx ds κ → (∀ r ∈ ds.recursion decl.names, r = none) →
      (κ.atLevels ρ).level.closedValue ≤ n →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν₀ x).isPlain = true → (ν₁ (β x)).isPlain = true) →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) x (ds.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => θ₁ (β x)) (fun x => θ₂ (β x)) →
      NestSubst sig ι n (ctx.atLevels ρ) @β @ν₁ @ν₂ @θ₁ @θ₂ @θ₁' @θ₂' →
      ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₁
          ((ds.rename β).atLevels ρ) @θ₁' S ∧
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) κ.quality @ν₂
          ((ds.rename β).atLevels ρ) @θ₂' S
  | .nil _, _, _, _, _, _, _ => ⟨fun _ _ => True, .nil, .nil⟩
  | .cons (ps := ps) (Θ := Θ) (B := B) (ψ := ψ) (ds := ds) (κ₁ := κ₁) _ hνB hΘ hB hκ _ hds,
      hrec, hn, hν₀, hpos, hE, hNS => by
    -- What the strict positivity gives of the destructor.
    have hΘav : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        ((Θ.rename β).atLevels ρ).Avoids x := fun e x hx => by
      have h := hpos e x hx
      rw [Destructors.rename] at h
      cases h with
      | cons hΘ' _ _ => exact hΘ'.substLevels _
    have hBpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) (x.weakenN ps.length)
          (B.rename (Ren.liftN ps.length @β)) := fun e x hx => by
      have h := hpos e x hx
      rw [Destructors.rename] at h
      cases h with
      | cons _ hB' _ => exact hB'
    have hdspos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) (.succ x) (ds.rename (Ren.lift @β)) :=
      fun e x hx => by
        have h := hpos e x hx
        rw [Destructors.rename] at h
        cases h with
        | cons _ _ hds' => exact hds'
    -- The arguments and the result, at the substitutions that the renaming composes.
    have hΘe : ∀ θ : Subst 0 [] Γ', ((Θ.rename β).atLevels ρ).subst θ =
        (Θ.atLevels ρ).subst (fun x => θ (β x)) := fun θ => by
      rw [Telescope.atLevels, Telescope.substLevels_rename]
      exact Telescope.subst_rename_of (fun _ => rfl) _
    have hBe : ∀ (θ : Subst 0 [] Γ') (τ : Subst 0 [] (Scope.extend [] ps.length)),
        ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ τ) =
          (B.atLevels ρ).subst (Subst.append (fun x => θ (β x)) τ) := fun θ τ => by
      rw [Term.atLevels, Term.substLevels_rename]
      exact Term.subst_rename_of (Subst.append_liftN_rename β (fun _ => rfl) τ) _
    obtain ⟨hΘ₁, hΘ₂⟩ := hNS.telescope_eq hΘav
    have hΘv : ValidEqTelescope₀ sig ι ⟨.type, (κ.atLevels ρ).level⟩
        (((Θ.rename β).atLevels ρ).subst θ₁) (((Θ.rename β).atLevels ρ).subst θ₂) := by
      rw [hΘe, hΘe]
      exact (hS.wfTelescope hent hΘ ρ).2 _ _ hE
    have hBv : ∀ τ₁ τ₂,
        EqSubst sig ι (Context.empty.append (((Θ.rename β).atLevels ρ).subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₁ τ₁))
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₂ τ₂))
          (.sort (κ₁.atLevels ρ)) := fun τ₁ τ₂ hτ => by
      rw [hΘe] at hτ
      rw [hBe, hBe]
      have h := hS.hasType hent hB ρ
      simp only [Context.atLevels, Context.substLevels_append] at h
      exact h.2 _ _ ((EqSubst.append_append_iff _ _ _ _ τ₁ τ₂).2 ⟨hE, hτ⟩)
    -- The result has no position, and the variables with a position do not occur in it.
    have hpl₁ : (B.rename (Ren.liftN ps.length @β)).nest (fun _ => none)
        (Nesting.liftN ps.length @ν₁) = .plain := by
      rw [Term.nest_rename _ (Ren.liftN ps.length @β)
        (Nesting.liftN_rename ps.length (ν := fun x => ν₁ (β x)) fun _ _ => rfl) B]
      exact Nest.eq_plain_of_isPlain
        (Term.nest_isPlain_mono (Nesting.liftN_isPlain_mono _ hν₀) B (by rw [hνB]; rfl))
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
    refine NestDesRel.of_plain_head hd hn
      ((Term.nest_substLevels _ _ _).trans hpl₁) ((Term.nest_substLevels _ _ _).trans hpl₂)
      hΘv hΘ₁ hΘ₂ (Universe.substLevels_bounded _ hκ) hBv hB₁ hB₂ fun f₁ f₂ hf => ?_
    have e : ∀ (θ : Subst 0 [] Γ') (f : Term 0 (Scope.extend [] ps.length)),
        @Eq (Subst 0 [] (.secondOrder ps ψ :: Γ))
          (fun x => Subst.snoc (e := .secondOrder ps ψ) θ f (Ren.lift @β x))
          (Subst.snoc (e := .secondOrder ps ψ) (fun x => θ (β x)) f) := fun θ f =>
      Subst.ext fun x => by cases x <;> rfl
    refine WfDestructors.nestDesRel hS hd hent hread fresh ρ n (β := Ren.lift @β) hds
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
    rw [Term.subst_append, ← hBe]
    exact hf τ₁ τ₂ ((congrArg (fun Θ' => EqSubst sig ι (Context.empty.append Θ') τ₁ τ₂)
      (hΘe θ₁)).mpr hτ)
  | .nested (ps := ps) (Θ := Θ) (B := B) (ψ := ψ) (ds := ds) (κ₁ := κ₁) _ _ hΘ hB hκ _ hds,
      hrec, hn, hν₀, hpos, hE, hNS => by
    have hds_eq : (ds.rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) @β) =
        ds.rename (fun x => .succ (β x)) := Destructors.rename_rename_of (fun _ => rfl) ds
    -- What the strict positivity gives of the destructor.
    have hΘav : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        ((Θ.rename β).atLevels ρ).Avoids x := fun e x hx => by
      have h := hpos e x hx
      rw [Destructors.rename] at h
      cases h with
      | cons hΘ' _ _ => exact hΘ'.substLevels _
    have hBpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) (x.weakenN ps.length)
          (B.rename (Ren.liftN ps.length @β)) := fun e x hx => by
      have h := hpos e x hx
      rw [Destructors.rename] at h
      cases h with
      | cons _ hB' _ => exact hB'
    have hdspos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Destructors.Positive (sigT.PositiveIn decl) (.succ x)
          (ds.rename (fun x => .succ (e' := .secondOrder ps ψ) (β x))) :=
      fun e x hx => by
        have h := hpos e x hx
        rw [Destructors.rename, hds_eq] at h
        cases h with
        | cons _ _ hds' => exact hds'
    -- The arguments and the result, at the substitutions that the renaming composes.
    have hΘe : ∀ θ : Subst 0 [] Γ', ((Θ.rename β).atLevels ρ).subst θ =
        (Θ.atLevels ρ).subst (fun x => θ (β x)) := fun θ => by
      rw [Telescope.atLevels, Telescope.substLevels_rename]
      exact Telescope.subst_rename_of (fun _ => rfl) _
    have hBe : ∀ (θ : Subst 0 [] Γ') (τ : Subst 0 [] (Scope.extend [] ps.length)),
        ((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ τ) =
          (B.atLevels ρ).subst (Subst.append (fun x => θ (β x)) τ) := fun θ τ => by
      rw [Term.atLevels, Term.substLevels_rename]
      exact Term.subst_rename_of (Subst.append_liftN_rename β (fun _ => rfl) τ) _
    obtain ⟨hΘ₁, hΘ₂⟩ := hNS.telescope_eq hΘav
    have hΘv : ValidEqTelescope₀ sig ι ⟨.type, (κ.atLevels ρ).level⟩
        (((Θ.rename β).atLevels ρ).subst θ₁) (((Θ.rename β).atLevels ρ).subst θ₂) := by
      rw [hΘe, hΘe]
      exact (hS.wfTelescope hent hΘ ρ).2 _ _ hE
    have hEa : ∀ τ₁ τ₂,
        EqSubst sig ι (Context.empty.append (((Θ.rename β).atLevels ρ).subst θ₁)) τ₁ τ₂ →
        EqSubst sig ι ((ctx.atLevels ρ).append (Θ.atLevels ρ))
          (Subst.append (fun x => θ₁ (β x)) τ₁) (Subst.append (fun x => θ₂ (β x)) τ₂) :=
      fun τ₁ τ₂ hτ => by
        rw [hΘe] at hτ
        exact (EqSubst.append_append_iff _ _ _ _ τ₁ τ₂).2 ⟨hE, hτ⟩
    have hBv : ∀ τ₁ τ₂,
        EqSubst sig ι (Context.empty.append (((Θ.rename β).atLevels ρ).subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₁ τ₁))
          (((B.rename (Ren.liftN ps.length @β)).atLevels ρ).subst (Subst.append θ₂ τ₂))
          (.sort (κ₁.atLevels ρ)) := fun τ₁ τ₂ hτ => by
      rw [hBe, hBe]
      have h := hS.hasType hent hB ρ
      simp only [Context.atLevels, Context.substLevels_append] at h
      exact h.2 _ _ (hEa τ₁ τ₂ hτ)
    have hκ' : κ₁.atLevels ρ ≼ κ.atLevels ρ := Universe.substLevels_bounded _ hκ
    -- The destructors after it, whatever the abstractions for it.
    have hrest : ∀ f₁ f₂ : Term 0 (Scope.extend [] ps.length),
        ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) (κ.atLevels ρ).quality
            (Nesting.lift (e := .secondOrder ps ψ) @ν₁)
            (((ds.rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) @β)).atLevels ρ)
            (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁) S ∧
          NestDesRel sig ι n (fun m _ => levelRel sig ι m) (κ.atLevels ρ).quality
            (Nesting.lift (e := .secondOrder ps ψ) @ν₂)
            (((ds.rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) @β)).atLevels ρ)
            (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) S := fun f₁ f₂ => by
      rw [hds_eq]
      exact WfDestructors.nestDesRel hS hd hent hread fresh ρ n
        (β := fun x => .succ (e' := .secondOrder ps ψ) (β x)) hds
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
      exact NestDesRel.of_plain_head hd hn
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
      refine NestDesRel.of_nested_head hd hn
        (fun h => by rw [e₁.symm.trans h] at hpl; exact nomatch hpl)
        (fun h => by rw [e₂.symm.trans h] at hpl₂; exact nomatch hpl₂)
        hΘv hΘ₁ hΘ₂ (fun τ₁ τ₂ hτ => ?_) hrest
      suffices h : NestReads sig ι n κ.quality
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
      refine hread hB decl fresh ρ n (Ren.liftN ps.length @β) (σ₁ := Subst.append θ₁ τ₁)
        (σ₂ := Subst.append θ₂ τ₂) (fun e z hz => ?_) ?_ ?_ κ.quality ?_
      · obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z fun h => by
          rw [h] at hz
          exact nomatch hz
        exact hBpos e x (Nest.isPlain_eq_false hx)
      · rw [Context.atLevels, Context.substLevels_append]
        exact (EqSubst.congr (eσ θ₁ τ₁) (eσ θ₂ τ₂)).2 (hEa τ₁ τ₂ hτ)
      · rw [Context.atLevels, Context.substLevels_append]
        exact hNS.append (Θ.atLevels ρ) τ₁ τ₂
      · obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, -⟩ :=
          (hBv τ₁ τ₂ hτ).fieldRel hκ'.1 (Nat.le_trans (hκ'.2 Fin.elim0) hn)
        exact ⟨F, .plain hc₁ hF₁, .plain hc₂ hF₂⟩
  | .recursive (D := D) hD _ _ _, hrec, _, _, _, _, _ => by
    have h := hrec _ (List.mem_cons_self ..)
    simp only [TypeDeclaration.blockInstance, Term.blockName, hD, ite_true] at h
    exact nomatch h
termination_by structural h => h

/-! ## Types Without Position -/

section

variable {n : Nat} {Γ' Γ : Scope} {ctx : Context 0 Γ} {β : Ren Γ' Γ} {ν₁ ν₂ : Nesting NestLeaf Γ'}
  {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'}

/-- The pairs of substitutions depend on the substitutions only through what they give each
variable. -/
theorem NestSubst.congr_subst (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {τ₁ τ₂ τ₁' τ₂' : Subst 0 [] Γ'} (e₁ : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₁ x = σ₁ x)
    (e₂ : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₂ x = σ₂ x)
    (e₁' : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₁' x = σ₁' x)
    (e₂' : ∀ {e : Scope.Entry} (x : Var Γ' e), τ₂' x = σ₂' x) :
    NestSubst sig ι n ctx @β @ν₁ @ν₂ @τ₁ @τ₂ @τ₁' @τ₂' where
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
theorem NestSubst.plain_eq (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂') {k : Nat}
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
theorem NestSubst.plain_eq_liftN (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
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
theorem NestSubst.reads_of_plain (h : NestSubst sig ι n ctx @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂')
    {k : Nat} {marks : Name → Nat → Prop} {A : Term k Γ'} (ρ : Fin k → Nat)
    (hpos : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false → Term.Positive marks x A)
    (hpl : (A.nest (fun _ => none) @ν₁).isPlain = true) {s : Quality}
    (hr : NestReads sig ι n s .plain .plain ((A.atLevels ρ).subst σ₁) ((A.atLevels ρ).subst σ₂)) :
    NestReads sig ι n s (A.nest (fun _ => none) @ν₁) (A.nest (fun _ => none) @ν₂)
      ((A.atLevels ρ).subst σ₁') ((A.atLevels ρ).subst σ₂') := by
  obtain ⟨e₁, e₂⟩ := h.plain_eq ρ hpos hpl
  have hpl₂ : (A.nest (fun _ => none) @ν₂).isPlain = true :=
    (Term.nest_isPlain_congr (fun _ x => h.isPlain x) A).symm.trans hpl
  rw [Nest.eq_plain_of_isPlain hpl, Nest.eq_plain_of_isPlain hpl₂, e₁, e₂]
  exact hr

end

/-! ## Arguments of an Instance -/

section

variable {n : Nat} {Δ : Scope} {pctx : Context 0 Δ} {ns₁ ns₂ : List (Nest NestLeaf)}
  {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Δ}

/-- The pairs of substitutions of the parameters of an instance, followed by the arguments of a
variable, whose nestings are those of the arguments. -/
theorem NestSubst.params_var
    (ih : NestSubst sig ι n pctx (fun x => x) (Nesting.ofArgs ns₁) (Nesting.ofArgs ns₂) @θ₁ @θ₂
      @θ₁' @θ₂')
    (A₀ : Term 0 Δ) {l₁ l₂ : Nest NestLeaf} {t₁ t₂ t₁' t₂' : Term 0 []}
    (hpl : l₁.isPlain = l₂.isPlain) (hl : l₁.isPlain = true → t₁' = t₁)
    (hr : l₁.isPlain = true → t₂' = t₂)
    (hv : l₁.isPlain = false → ∀ s, NestReads sig ι n s .plain .plain t₁ t₂ →
      NestReads sig ι n s l₁ l₂ t₁' t₂') :
    NestSubst sig ι n (pctx.var A₀) (fun x => x) (Nesting.ofArgs (l₁ :: ns₁))
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
    (ih : NestSubst sig ι n pctx (fun x => x) (Nesting.ofArgs ns₁) (Nesting.ofArgs ns₂) @θ₁ @θ₂
      @θ₁' @θ₂')
    {ps : List Parameter} (Θ₀ : Telescope 0 Δ ps) (A₀ : Term 0 (Δ.extend ps.length))
    (ψ : ResultOwnership Grade ps.length) {l₁ l₂ : Nest NestLeaf}
    {f₁ f₂ f₁' f₂' : Term 0 (Scope.extend [] ps.length)}
    (hpl : l₁.isPlain = l₂.isPlain) (hl : l₁.isPlain = true → f₁' = f₁)
    (hr : l₁.isPlain = true → f₂' = f₂)
    (hso : l₁.isPlain = false → ∀ s τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ₀.subst fun x => θ₁ x)) τ₁ τ₂ →
      NestReads sig ι n s .plain .plain (f₁.subst τ₁) (f₂.subst τ₂) →
        NestReads sig ι n s l₁ l₂ (f₁'.subst τ₁) (f₂'.subst τ₂)) :
    NestSubst sig ι n (pctx.secondOrder Θ₀ A₀ ψ) (fun x => x) (Nesting.ofArgs (l₁ :: ns₁))
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

/-- An instance of a codata type that is a type of a field of the sort of the quality `s` at the
level `n` lives at a level that `n` bounds, and `s` is the quality of the universes when it lives
in a universe. -/
theorem FieldRel.codata_inv (hd : sig.Distinct) {n : Nat} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue ≤ n ∧
      ((decl.sort (.ofLists qs ps hq hp)).quality = .type → s = .type) := by
  have hu : ∀ m R, UnivRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R →
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = m :=
    fun m R hu => by
      cases hu with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' _ hn' =>
        obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
        subst hD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
        exact hn'
  have hb : ∀ m b, PropRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) b →
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = m ∧
        (decl.sort (.ofLists qs ps hq hp)).quality = .prop :=
    fun m b hb => by
      cases hb with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' hs' hn' =>
        obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
        subst hD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
        exact ⟨hn', hs'⟩
  cases hF with
  | univ hs hu' => exact ⟨Nat.le_of_eq (hu n _ hu'), fun _ => hs⟩
  | univBelow hs m hm hu' =>
    exact ⟨Nat.le_trans (Nat.le_of_eq (hu m _ (levelRel_univ_iff.1 hu'))) (Nat.le_of_lt hm),
      fun _ => hs⟩
  | prop hb' =>
    obtain ⟨e, hκ'⟩ := hb n _ hb'
    exact ⟨Nat.le_of_eq e, fun hκ => nomatch hκ.symm.trans hκ'⟩
  | propBelow m hm hb' =>
    obtain ⟨e, hκ'⟩ := hb m _ (levelRel_prop_iff.1 hb')
    exact ⟨Nat.le_trans (Nat.le_of_eq e) (Nat.le_of_lt hm), fun hκ => nomatch hκ.symm.trans hκ'⟩

/-! ## Nested Types of a Well-Formed Signature -/

mutual

-- ADE: none.
/-- A type typed in the signature `Σ_T` and strictly positive in the variables with a position is
read by the graph of the nestings at its nesting, given the soundness of the typing in the
signatures that `Σ_T` ends with, and the same property of the signatures before its entries: a
type without position is the same at the two pairs of substitutions, a variable with a position is
read as given, and an instance of a declared type whose arguments have positions is that of a
codata type none of whose destructors is recursive, whose destructors are read at the nestings of
its arguments, by their formation in the signature before it. -/
theorem Term.nestReads (hS : TypingSound sig ι) (hd : sig.Distinct) {sigT : Signature} (hent : sig.ValidEntries ι sigT)
    (hprev : ∀ (e : Entry) (sigF : Signature), (e :: sigF) <:+ sigT → ReadsNested sig ι sigF)
    (decl : TypeDeclaration) (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {k : Nat}
    (ρ : Fin k → Nat) (n : Nat) {Γ : Scope} {ctx : Context k Γ} {T : Term k Γ} {Γ' : Scope}
    (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting NestLeaf Γ'} {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'} :
    (A : Term k Γ) → HasType sigT ctx A T →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        Term.Positive (sigT.PositiveIn decl) x (A.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι n (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' → ∀ s,
      NestReads sig ι n s .plain .plain (((A.rename β).atLevels ρ).subst σ₁)
        (((A.rename β).atLevels ρ).subst σ₂) →
      NestReads sig ι n s ((A.rename β).nest (fun _ => none) @ν₁)
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
      have hnest : ∀ ν : Nesting NestLeaf Γ',
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
          NestSubst sig ι n (params.atLevels ρ) (fun x => x)
            (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁))
            (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₂))
            (((as.rename β).atLevels ρ).subst σ₁).toSubst
            (((as.rename β).atLevels ρ).subst σ₂).toSubst
            (((as.rename β).atLevels ρ).subst σ₁').toSubst
            (((as.rename β).atLevels ρ).subst σ₂').toSubst :=
        fun has hp => InstanceArgs.nestSubst hS hd hent hprev decl fresh ρ n β D as has hp hE hNS
      obtain ⟨declF, ζ, hΔ, hq, hl, hp, hD, hadm, has⟩ := hA.inst_inv
      subst hΔ
      have hsigT : WfSig sigT := presuppositions.wfCtx (contextPresuppositions.hasType hA)
      have hdT := hsigT.distinct
      have hposA : ∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
          InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β) := fun e x hx => by
        have h := hpos e x hx
        rw [Term.rename] at h
        exact h.inst_args
      have hpl₂ : (((Term.inst D qs ls ps as).rename β).nest (fun _ => none) @ν₂).isPlain =
          false := (Term.nest_isPlain_congr (fun _ x => hNS.isPlain x) _).symm.trans hpl
      have hall : ∀ ν : Nesting NestLeaf Γ',
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
              ∀ I, ∀ r ∈ (T.body I).recursion declF.names, r = none := fun i hi => by
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
      have freshF : ∀ e ∈ sigF, ∀ D' ∈ declF.names, D' ∉ e.names := by
        cases hsigT.of_suffix hsuf with
        | typeDeclaration _ _ fr => exact fr
      cases hdecl with
      | data hb _ _ _ _ _ => exact absurd hT.2.1 (by simp [TypeDeclaration.codataTypes, hb])
      | codata hb _ _ hds hpF _ =>
        have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length =
            declF.levels := (List.length_map _).trans hl
        have hTm := (hent.hasCodataType hT).1
        have hinst : ∀ σ : Subst 0 [] Γ',
            (((Term.inst D qs ls ps as).rename β).atLevels ρ).subst σ =
              .inst D qs (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))) ps
                (((as.rename β).atLevels ρ).subst σ) := fun σ => by
          rw [Term.rename, Term.atLevels, Term.substLevels, Term.subst]
          rfl
        rw [hinst, hinst] at hr
        rw [hinst, hinst, hnest₁, hnest₂]
        -- The instance lives at a level that the level of the graph bounds.
        obtain ⟨FE, hrE, -⟩ := hr
        cases hrE with
        | plain hc hF =>
          cases Computesι.det hd ⟨.refl _, .inst D qs _ ps _⟩ hc
          obtain ⟨hn, hs⟩ := FieldRel.codata_inv hd hTm hq hl' hp hF
          -- The values of the levels of the instance.
          let ρF : Fin declF.levels → Nat := fun i =>
            ((ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl' i).closedValue
          have hls : ∀ i, (Level.ofNat (ρF i) : Level 0) ≈
              (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl' i :=
            fun i => Level.ofNat_closedValue _
          have hget : ∀ i,
              (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).getFin hl' i =
                (ls.getFin hl i).subst fun i => .ofNat (ρ i) :=
            fun i => congrFun (Level.getFin_map_subst _ ls hl) i
          have hctxEq : Context.LevelEquiv
              (((declF.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).atLevels ρ)
              ((declF.params (.ofLists qs ps hq hp)).atLevels ρF) := by
            rw [Context.atLevels, Context.substLevels_substLevels]
            refine Context.substLevels_levelEquiv (fun i => ?_) _
            rw [← hget i]
            exact Level.equivalence.symm (hls i)
          -- The arguments at the first pair are equal arguments of the parameters.
          have eas : ∀ σ : Subst 0 [] Γ', ((as.rename β).atLevels ρ).subst σ =
              (as.atLevels ρ).subst (fun x => σ (β x)) := fun σ => by
            rw [InstanceArgs.atLevels, InstanceArgs.substLevels_rename]
            exact InstanceArgs.subst_rename_of (fun _ => rfl) _
          have hEF : EqSubst sig ι ((declF.params (.ofLists qs ps hq hp)).atLevels ρF)
              (fun x => (((as.rename β).atLevels ρ).subst σ₁).toSubst x)
              (fun x => (((as.rename β).atLevels ρ).subst σ₂).toSubst x) := by
            rw [eas, eas]
            exact EqSubst.levelEquiv hctxEq ((hS.hasInstanceArgs hent has ρ).2 _ _ hE)
          -- The destructors of the type, at the nestings of the arguments.
          obtain ⟨S, hS₁, hS₂⟩ := WfDestructors.nestDesRel hS hd hentF
            (hprev _ _ hsuf) freshF ρF n (β := fun x => x) (hds _ hadm T hT.2.1) (hTrec _)
            (Nat.le_trans (Nat.le_of_eq (Level.closedValue_subst_equiv hls _)) hn)
            (fun e y h => by
              cases hy : (Nesting.ofArgs ((as.rename β).nest (fun _ => none) @ν₁) y).isPlain with
              | true => rfl
              | false =>
                simp only [Nesting.ofPositive, hTmark y hy, ite_true] at h
                exact nomatch h)
            (fun e y hy => by
              rw [Destructors.rename_id_of (fun _ => rfl)]
              exact hpF _ hadm T hT.2.1 y (hTmark y hy))
            hEF ((ih has hposA).levelEquiv hctxEq)
          rw [Destructors.rename_id_of (fun _ => rfl)] at hS₁ hS₂
          have hinv : ∀ m, m < n → (levelRel sig ι m).LevelInvariant :=
            fun m _ => levelRel_levelInvariant m
          have hrel : ∀ ν : Nesting NestLeaf declF.scope,
              Nesting.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) @ν @ν :=
            fun ν _ x => Nest.rel₃_refl (fun _ => ⟨Term.LevelEquiv.refl _, rfl⟩) _
          have hS₁' := NestDesRel.levelEquiv hinv hS₁
            (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
          have hS₂' := NestDesRel.levelEquiv hinv hS₂
            (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
          cases hκ : (declF.sort (.ofLists qs ps hq hp)).quality with
          | type =>
            rw [hκ] at hS₁' hS₂'
            exact ⟨_, .codata hTm hq hl' hp rfl (hs hκ) hκ hn (hTrec _) S hS₁',
              .codata hTm hq hl' hp rfl (hs hκ) hκ hn (hTrec _) S hS₂'⟩
          | prop =>
            rw [hκ] at hS₁' hS₂'
            exact ⟨_, .codataProp hTm hq hl' hp rfl hκ hn (hTrec _) S hS₁',
              .codataProp hTm hq hl' hp rfl hκ hn (hTrec _) S hS₂'⟩
  | .sort _, _, hpos, _, hNS, _, hr | .const _ _ _ _, _, hpos, _, hNS, _, hr
  | .ctor _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .recursor _ _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .obs _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr
  | .corec _ _ _ _ _ _ _ _ _, _, hpos, _, hNS, _, hr => hNS.reads_of_plain ρ hpos rfl hr

-- ADE: none.
/-- The arguments of an instance typed in the signature `Σ_T` and strictly positive in the
variables with a position give the parameters, at the two pairs of substitutions, two pairs of
substitutions of the parameters, at the nestings of the arguments: the argument of each parameter
is read at its nesting, as a type under the variables of its abstraction. -/
theorem InstanceArgs.nestSubst (hS : TypingSound sig ι) (hd : sig.Distinct) {sigT : Signature}
    (hent : sig.ValidEntries ι sigT)
    (hprev : ∀ (e : Entry) (sigF : Signature), (e :: sigF) <:+ sigT → ReadsNested sig ι sigF)
    (decl : TypeDeclaration) (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) {k : Nat}
    (ρ : Fin k → Nat) (n : Nat) {Γ : Scope} {ctx : Context k Γ} {Γ' : Scope}
    (β : Ren Γ' Γ) {ν₁ ν₂ : Nesting NestLeaf Γ'} {σ₁ σ₂ σ₁' σ₂' : Subst 0 [] Γ'} (D : Name) :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → {params : Context k Δ} →
      HasInstanceArgs sigT ctx as params →
      (∀ (e : Scope.Entry) (x : Var Γ' e), (ν₁ x).isPlain = false →
        InstanceArgs.Positive (sigT.PositiveIn decl) D x (as.rename β)) →
      EqSubst sig ι (ctx.atLevels ρ) (fun x => σ₁ (β x)) (fun x => σ₂ (β x)) →
      NestSubst sig ι n (ctx.atLevels ρ) @β @ν₁ @ν₂ @σ₁ @σ₂ @σ₁' @σ₂' →
      NestSubst sig ι n (params.atLevels ρ) (fun x => x)
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
    have ih := InstanceArgs.nestSubst hS hd hent hprev decl fresh ρ n β D as has hposas hE hNS
    exact (ih.params_var (A₀.atLevels ρ)
      (l₁ := (a.rename β).nest (fun _ => none) @ν₁) (l₂ := (a.rename β).nest (fun _ => none) @ν₂)
      (t₁ := ((a.rename β).atLevels ρ).subst σ₁) (t₂ := ((a.rename β).atLevels ρ).subst σ₂)
      (t₁' := ((a.rename β).atLevels ρ).subst σ₁') (t₂' := ((a.rename β).atLevels ρ).subst σ₂')
      (Term.nest_isPlain_congr (fun _ x => hNS.isPlain x) _)
      (fun h => (hNS.plain_eq ρ hposa h).1) (fun h => (hNS.plain_eq ρ hposa h).2)
      (fun _ s hr => Term.nestReads hS hd hent hprev decl fresh ρ n β a ha hposa hE hNS s
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
    have ih := InstanceArgs.nestSubst hS hd hent hprev decl fresh ρ n β D as has hposas hE hNS
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
    refine Term.nestReads hS hd hent hprev decl fresh ρ n (Ren.liftN ps.length @β) B hB
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

-- ADE: none.
/-- The types typed in a signature are read by the graph of the nestings, given the soundness of
the typing in the signatures that it ends with: by induction on the signature, since a type is
read through the codata types declared in it, whose destructors are typed in the signature before
their declaration. -/
theorem readsNested (hS : TypingSound sig ι) (hd : sig.Distinct) :
    (sigT : Signature) → sig.ValidEntries ι sigT → ReadsNested sig ι sigT
  | [], hent => fun hA decl fresh ρ n _ β _ _ _ _ _ _ hpos hE hNS s hr =>
    Term.nestReads hS hd hent (fun _ _ h => nomatch List.suffix_nil.1 h)
      decl fresh ρ n β _ hA hpos hE hNS s hr
  | e :: sigT, hent => fun hA decl fresh ρ n _ β _ _ _ _ _ _ hpos hE hNS s hr =>
    Term.nestReads hS hd hent
      (fun e' sigF h =>
        have hsub : sigF ⊆ e :: sigT := Signature.subset_of_cons_suffix h
        readsNested hS hd sigF fun x hx => hent x (hsub hx))
      decl fresh ρ n β _ hA hpos hE hNS s hr
termination_by sigT => sigT.length
decreasing_by
  have := h.length_le
  simp only [List.length_cons] at this ⊢
  omega

end

end Sic.Core
