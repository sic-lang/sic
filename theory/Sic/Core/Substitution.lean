module

public import Sic.Core.Syntax

/-!
# Substitution

The substitutions of RFC 24: the substitution `A[t̄ / Θ]` of the arguments of a telescope for its
variables, the instantiation `[x̄. B / X]` of a second-order variable, which replaces each application
`X[t̄]` by `B[t̄ / x̄]`, the substitution `[ā / Δ]` of the arguments of an instance for its parameters,
and the instantiation `[l̄' / l̄]` of the level variables.

A substitution of the second order replaces a second-order variable by an abstraction, so that it
substitutes the arguments of each application in the abstraction, which is not a subterm of the
term.
It is therefore built on a substitution of the first order, `subst₀`, which replaces each variable
either by a variable with the same telescope or, when it has none, by a term, and which recurses on
the term alone.
The renamings and the substitutions of both orders compose, and the substitution `B[t̄ / Θ]` commutes
with each of them, as the laws of composition below state.

ADE substitute terms for variables of the first order only, in `Definition/Untyped.agda`.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat}

/-! ## Renamings -/

-- ADE: `Wk`, in `Definition/Untyped/NotParametrised.agda`.
/-- A renaming of the scope `Δ` in the scope `Γ`, which keeps the telescope of each variable. -/
abbrev Ren (Γ Δ : Scope) : Type := ∀ {ps : List Grade}, Var Δ ps → Var Γ ps

namespace Ren

/-- The renaming `ρ` under a new entry. -/
def lift {Γ Δ : Scope} {qs : List Grade} (ρ : Ren Γ Δ) : Ren (qs :: Γ) (qs :: Δ) := fun x =>
  match x with
  | .zero => .zero
  | .succ x => .succ (ρ x)

/-- The renaming `ρ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Ren Γ Δ → Ren (Γ.extend n) (Δ.extend n)
  | 0, ρ => ρ
  | n + 1, ρ => liftN n (lift ρ)

/-- The renaming that skips a new entry. -/
def weaken {Γ : Scope} {qs : List Grade} : Ren (qs :: Γ) Γ := fun x => .succ x

end Ren

/-- The variable `x` in the scope extended by `n` new variables. -/
def Var.weakenN {Γ : Scope} {ps : List Grade} : (n : Nat) → Var Γ ps → Var (Γ.extend n) ps
  | 0, x => x
  | n + 1, x => Var.weakenN n (.succ x)

mutual

-- ADE: `wk`, in `Definition/Untyped.agda`.
/-- The term `t` renamed by `ρ`. -/
def Term.rename {Γ Δ : Scope} (ρ : Ren Γ Δ) : Term k Δ → Term k Γ
  | .var x ts => .var (ρ x) (ts.rename ρ)
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.rename ρ)

/-- The arguments `t̄` renamed by `ρ`. -/
def Args.rename {Γ Δ : Scope} {a : List Grade} (ρ : Ren Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.rename ρ) (ts.rename ρ)

/-- The arguments `ā` renamed by `ρ`, under the variables of each abstraction. -/
def InstanceArgs.rename {Γ Δ Ξ : Scope} (ρ : Ren Γ Δ) : InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.rename ρ) (B.rename (Ren.liftN _ ρ))

end

/-- The arguments `(x₁, …, xₐ)`: the new variables of the scope `Γ.extend a`, in order, for a
telescope whose entries have the grades `ps`. -/
def Args.bound {Γ : Scope} : (ps : List Grade) → Args k (Γ.extend ps.length) ps
  | [] => .nil
  | _ :: ps => .cons (.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := [] :: Γ) ps)

/-- `x̄. x[x̄]`: the variable `x` as an abstraction over a variable for each entry of its telescope. -/
def Var.eta {Γ : Scope} {ps : List Grade} (x : Var Γ ps) : Term k (Γ.extend ps.length) :=
  .var (x.weakenN ps.length) (Args.bound ps)

/-! ## Substitutions of the First Order -/

/-- What a substitution of the first order gives a variable whose telescope has the grades `ps`: a
variable with the same telescope, or a term when the telescope is empty. -/
inductive Val (k : Nat) (Γ : Scope) : List Grade → Type where
  /-- A variable. -/
  | var {ps : List Grade} (x : Var Γ ps) : Val k Γ ps
  /-- A term, for a variable without telescope. -/
  | term (t : Term k Γ) : Val k Γ []

/-- The value `v` renamed by `ρ`. -/
def Val.rename {Γ Δ : Scope} {a : List Grade} (ρ : Ren Γ Δ) : Val k Δ a → Val k Γ a
  | .var x => .var (ρ x)
  | .term t => .term (t.rename ρ)

-- ADE: `Subst`, in `Definition/Untyped.agda`.
/-- A substitution of the first order of the scope `Δ` in the scope `Γ`. -/
abbrev Subst₀ (k : Nat) (Γ Δ : Scope) : Type := ∀ {ps : List Grade}, Var Δ ps → Val k Γ ps

namespace Subst₀

/-- The identity, which gives each variable itself. -/
def id {Γ : Scope} : Subst₀ k Γ Γ := fun x => .var x

/-- The substitution `σ` under a new entry. -/
def lift {Γ Δ : Scope} {qs : List Grade} (σ : Subst₀ k Γ Δ) : Subst₀ k (qs :: Γ) (qs :: Δ) :=
  fun x =>
  match x with
  | .zero => .var .zero
  | .succ x => (σ x).rename Ren.weaken

/-- The substitution `σ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Subst₀ k Γ Δ → Subst₀ k (Γ.extend n) (Δ.extend n)
  | 0, σ => σ
  | n + 1, σ => liftN n (lift σ)

-- ADE: `sgSubst`, in `Definition/Untyped.agda`.
/-- `[t / x]`: the substitution of `t` for the last variable. -/
def single {Γ : Scope} (t : Term k Γ) : Subst₀ k Γ ([] :: Γ) := fun x =>
  match x with
  | .zero => .term t
  | .succ x => .var x

end Subst₀

mutual

-- ADE: `_[_]`, in `Definition/Untyped.agda`.
/-- The term `t` substituted by `σ`. -/
def Term.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Term k Δ → Term k Γ
  | .var x ts =>
    match σ x, ts.subst₀ σ with
    | .var y, us => .var y us
    | .term t, _ => t
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.subst₀ σ)

/-- The arguments `t̄` substituted by `σ`. -/
def Args.subst₀ {Γ Δ : Scope} {a : List Grade} (σ : Subst₀ k Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.subst₀ σ) (ts.subst₀ σ)

/-- The arguments `ā` substituted by `σ`, under the variables of each abstraction. -/
def InstanceArgs.subst₀ {Γ Δ Ξ : Scope} (σ : Subst₀ k Γ Δ) :
    InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.subst₀ σ) (B.subst₀ (Subst₀.liftN _ σ))

end

/--
`B[t̄ / Θ]`: the term `B`, over the new variables of a telescope, in which the arguments `t̄`
are substituted for these variables, the first one first, as the rule `(tel_,)` types them.
-/
def Term.instantiate {Γ : Scope} :
    {ps : List Grade} → Term k (Γ.extend ps.length) → Args k Γ ps → Term k Γ
  | [], B, .nil => B
  | _ :: ps, B, .cons t ts =>
    Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts

/-! ## Substitutions of the Second Order -/

/-- A substitution of the second order of the scope `Δ` in the scope `Γ`, which gives each variable an
abstraction over a variable for each entry of its telescope. -/
abbrev Subst (k : Nat) (Γ Δ : Scope) : Type :=
  ∀ {ps : List Grade}, Var Δ ps → Term k (Γ.extend ps.length)

namespace Subst

/-- The substitution `σ` under a new entry. -/
def lift {Γ Δ : Scope} {qs : List Grade} (σ : Subst k Γ Δ) : Subst k (qs :: Γ) (qs :: Δ) := fun x =>
  match x with
  | .zero => Var.eta .zero
  | .succ x => (σ x).rename (Ren.liftN _ Ren.weaken)

/-- The substitution `σ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Subst k Γ Δ → Subst k (Γ.extend n) (Δ.extend n)
  | 0, σ => σ
  | n + 1, σ => liftN n (lift σ)

end Subst

mutual

/-- The term `t` substituted by `σ`: an application `x[t̄]` becomes `B[t̄' / x̄]`, where `x̄. B` is what
`σ` gives `x`, and `t̄'` are the arguments substituted. -/
def Term.subst {Γ Δ : Scope} (σ : Subst k Γ Δ) : Term k Δ → Term k Γ
  | .var x ts => (σ x).instantiate (ts.subst σ)
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.subst σ)

/-- The arguments `t̄` substituted by `σ`. -/
def Args.subst {Γ Δ : Scope} {a : List Grade} (σ : Subst k Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.subst σ) (ts.subst σ)

/-- The arguments `ā` substituted by `σ`, under the variables of each abstraction. -/
def InstanceArgs.subst {Γ Δ Ξ : Scope} (σ : Subst k Γ Δ) :
    InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.subst σ) (B.subst (Subst.liftN _ σ))

end

/-- `[ā / Δ]`: the substitution that gives each parameter of `Δ` its argument in `ā`. -/
def InstanceArgs.toSubst {Γ : Scope} : {Δ : Scope} → InstanceArgs k Γ Δ → Subst k Γ Δ
  | _, .snoc _ B, _, .zero => B
  | _, .snoc as _, _, .succ x => as.toSubst x

/-! ## Instantiation of the Level Variables -/

/-- `l[l̄' / l̄]`: the level `l` in which the level `σ i` replaces the variable `i`. -/
def Level.subst {k k' : Nat} (σ : Fin k → Level k') : Level k → Level k'
  | .zero => .zero
  | .succ l => .succ (l.subst σ)
  | .max l₁ l₂ => .max (l₁.subst σ) (l₂.subst σ)
  | .var i => σ i

/-- The sort `κ` in which the levels `σ` replace the level variables. -/
def Universe.substLevels {k k' : Nat} (σ : Fin k → Level k') (κ : Universe k) : Universe k' :=
  ⟨κ.quality, κ.level.subst σ⟩

mutual

/-- `t[l̄' / l̄]`: the term `t` in which the levels `σ` replace the level variables. -/
def Term.substLevels {k' : Nat} {Γ : Scope} (σ : Fin k → Level k') : Term k Γ → Term k' Γ
  | .var x ts => .var x (ts.substLevels σ)
  | .sort κ => .sort (κ.substLevels σ)
  | .const c qs ls ps => .const c qs (ls.map (Level.subst σ)) ps
  | .inst D qs ls ps as => .inst D qs (ls.map (Level.subst σ)) ps (as.substLevels σ)

/-- The arguments `t̄` in which the levels `σ` replace the level variables. -/
def Args.substLevels {k' : Nat} {Γ : Scope} {a : List Grade} (σ : Fin k → Level k') :
    Args k Γ a → Args k' Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.substLevels σ) (ts.substLevels σ)

/-- The arguments `ā` in which the levels `σ` replace the level variables. -/
def InstanceArgs.substLevels {k' : Nat} {Γ Δ : Scope} (σ : Fin k → Level k') :
    InstanceArgs k Γ Δ → InstanceArgs k' Γ Δ
  | .nil => .nil
  | .snoc as B => .snoc (as.substLevels σ) (B.substLevels σ)

end

/-! ## Telescopes and Contexts -/

/-- The telescope `Θ` renamed by `ρ`. -/
def Telescope.rename {Γ Δ : Scope} {ps : List Grade} (ρ : Ren Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.rename ρ) (Θ.rename (Ren.lift ρ))

/-- `Θ[t / x]`: the telescope `Θ` substituted by `σ`. -/
def Telescope.subst₀ {Γ Δ : Scope} {ps : List Grade} (σ : Subst₀ k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst₀ σ) (Θ.subst₀ (Subst₀.lift σ))

/-- `Θ[ā / Δ]`: the telescope `Θ` substituted by `σ`. -/
def Telescope.subst {Γ Δ : Scope} {ps : List Grade} (σ : Subst k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst σ) (Θ.subst (Subst.lift σ))

/-- The telescope `Θ` in which the levels `σ` replace the level variables. -/
def Telescope.substLevels {k' : Nat} {Γ : Scope} {ps : List Grade} (σ : Fin k → Level k') :
    Telescope k Γ ps → Telescope k' Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.substLevels σ) (Θ.substLevels σ)

/-- The context `Γ` in which the levels `σ` replace the level variables. -/
def Context.substLevels {k' : Nat} {Γ : Scope} (σ : Fin k → Level k') :
    Context k Γ → Context k' Γ
  | .empty => .empty
  | .var ctx A => .var (ctx.substLevels σ) (A.substLevels σ)
  | .secondOrder ctx Θ A => .secondOrder (ctx.substLevels σ) (Θ.substLevels σ) (A.substLevels σ)

/-- `Γ, Θ`: the context `Γ` extended by the entries of the telescope `Θ`, whose grades it ignores. -/
def Context.append : {Γ : Scope} → {ps : List Grade} → Context k Γ → Telescope k Γ ps →
    Context k (Γ.extend ps.length)
  | _, [], ctx, .nil => ctx
  | _, _ :: _, ctx, .cons _ _ A Θ => Context.append (Γ := [] :: _) (ctx.var A) Θ

/-- A closed term in the scope `Γ`, which it does not use. -/
def Term.weakenClosed {Γ : Scope} (t : Term k []) : Term k Γ := t.rename fun x => by cases x

/-! ## Properties

The renamings and the substitutions of the first order that give each variable itself change
nothing, under the new variables of every abstraction. -/

theorem Ren.lift_id_of {Γ : Scope} {b : List Grade} {ρ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ρ x = x) :
    ∀ {a} (x : Var (b :: Γ) a), Ren.lift ρ x = x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {ρ : Ren Γ Γ}, (∀ {a} (x : Var Γ a), ρ x = x) →
      ∀ {a} (x : Var (Γ.extend n) a), Ren.liftN n ρ x = x
  | 0, _, h => h
  | n + 1, _, h => Ren.liftN_id_of (Γ := [] :: Γ) n (Ren.lift_id_of h)

mutual

theorem Term.rename_id_of {Γ : Scope} {ρ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ρ x = x) :
    (t : Term k Γ) → t.rename ρ = t
  | .var x ts => by rw [Term.rename, h x, Args.rename_id_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by rw [Term.rename, InstanceArgs.rename_id_of h as]

theorem Args.rename_id_of {Γ : Scope} {a : List Grade} {ρ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ρ x = x) :
    (ts : Args k Γ a) → ts.rename ρ = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.rename, Term.rename_id_of h t, Args.rename_id_of h ts]

theorem InstanceArgs.rename_id_of {Γ Ξ : Scope} {ρ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ρ x = x) :
    (as : InstanceArgs k Γ Ξ) → as.rename ρ = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename_id_of h as,
      Term.rename_id_of (Ren.liftN_id_of _ h) B]

end

/-- Renaming each variable to itself changes nothing. -/
theorem Term.rename_id {Γ : Scope} (t : Term k Γ) : t.rename (fun x => x) = t :=
  Term.rename_id_of (fun _ => rfl) t

theorem Subst₀.lift_id_of {Γ : Scope} {b : List Grade} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) :
    ∀ {a} (x : Var (b :: Γ) a), Subst₀.lift σ x = .var x
  | _, .zero => rfl
  | _, .succ x => by rw [Subst₀.lift, h x]; rfl

theorem Subst₀.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Γ}, (∀ {a} (x : Var Γ a), σ x = .var x) →
      ∀ {a} (x : Var (Γ.extend n) a), Subst₀.liftN n σ x = .var x
  | 0, _, h => h
  | n + 1, _, h => Subst₀.liftN_id_of (Γ := [] :: Γ) n (Subst₀.lift_id_of h)

mutual

theorem Term.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ} (h : ∀ {a} (x : Var Γ a), σ x = .var x) :
    (t : Term k Γ) → t.subst₀ σ = t
  | .var x ts => by unfold Term.subst₀; simp only [h x, Args.subst₀_id_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by rw [Term.subst₀, InstanceArgs.subst₀_id_of h as]

theorem Args.subst₀_id_of {Γ : Scope} {a : List Grade} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (ts : Args k Γ a) → ts.subst₀ σ = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.subst₀, Term.subst₀_id_of h t, Args.subst₀_id_of h ts]

theorem InstanceArgs.subst₀_id_of {Γ Ξ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (as : InstanceArgs k Γ Ξ) → as.subst₀ σ = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst₀_id_of h as,
      Term.subst₀_id_of (Subst₀.liftN_id_of _ h) B]

end

/-- The identity substitution of the first order changes nothing. -/
theorem Term.subst₀_id {Γ : Scope} (t : Term k Γ) : t.subst₀ Subst₀.id = t :=
  Term.subst₀_id_of (fun _ => rfl) t

/-- The renaming that skips `n` new variables. -/
def Ren.weakenN {Γ : Scope} (n : Nat) : Ren (Γ.extend n) Γ := fun x => x.weakenN n

/-- The value `v` substituted by `σ`. -/
def Val.subst₀ {Γ Δ : Scope} {a : List Grade} (σ : Subst₀ k Γ Δ) : Val k Δ a → Val k Γ a
  | .var x => σ x
  | .term t => .term (t.subst₀ σ)

/-- The application of a value to arguments: a variable applied to them, or the term itself. -/
def Val.apply {Γ : Scope} {a : List Grade} : Val k Γ a → Args k Γ a → Term k Γ
  | .var y, us => .var y us
  | .term t, _ => t

/-- A substitution of the first order applies to `x[t̄]` what it gives `x`. -/
theorem Term.subst₀_var {Γ Δ : Scope} {a : List Grade} (σ : Subst₀ k Γ Δ) (x : Var Δ a)
    (ts : Args k Δ a) : (Term.var x ts).subst₀ σ = (σ x).apply (ts.subst₀ σ) := by
  unfold Term.subst₀
  generalize σ x = v
  cases v <;> rfl

/-! ## Composition

A renaming or a substitution followed by another one is a single one, their composition, which the
laws below give variable by variable: each law holds for any three substitutions whose composition
agrees on every variable, so that it holds under the new variables of each abstraction, where the
lifts of the three substitutions compose as well.

The laws of the first order come first, as in the formalization of ADE: a renaming after a renaming,
a substitution after a renaming, a renaming after a substitution, then a substitution after a
substitution, which relies on the two before it.
The substitution `B[t̄ / Θ]` of the arguments of a telescope then commutes with each of them.
The laws of the second order rely on it, since a substitution of the second order instantiates the
abstraction that it gives each applied variable.
-/

/-! ### Renamings after Renamings -/

theorem Ren.lift_comp_of {Γ Δ Ξ : Scope} {b : List Grade} {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ}
    {ρ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) :
    ∀ {a} (x : Var (b :: Ξ) a), Ren.lift ρ₁ (Ren.lift ρ₂ x) = Ren.lift ρ₃ x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_comp_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ} {ρ₃ : Ren Γ Ξ},
      (∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Ren.liftN n ρ₁ (Ren.liftN n ρ₂ x) = Ren.liftN n ρ₃ x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Ren.liftN_comp_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ) n
      (Ren.lift_comp_of h)

mutual

-- ADE: `wk-comp`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `ρ₂` then by `ρ₁` is renaming by their composition `ρ₃`. -/
theorem Term.rename_rename_of {Γ Δ Ξ : Scope} {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ} {ρ₃ : Ren Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) :
    (t : Term k Ξ) → (t.rename ρ₂).rename ρ₁ = t.rename ρ₃
  | .var x ts => by rw [Term.rename, Term.rename, Term.rename, h x, Args.rename_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as]

theorem Args.rename_rename_of {Γ Δ Ξ : Scope} {a : List Grade} {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ}
    {ρ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) :
    (ts : Args k Ξ a) → (ts.rename ρ₂).rename ρ₁ = ts.rename ρ₃
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.rename, Args.rename, Term.rename_rename_of h t, Args.rename_rename_of h ts]

theorem InstanceArgs.rename_rename_of {Γ Δ Ξ Ψ : Scope} {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ}
    {ρ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ρ₂).rename ρ₁ = as.rename ρ₃
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename, InstanceArgs.rename,
      InstanceArgs.rename_rename_of h as, Term.rename_rename_of (Ren.liftN_comp_of _ h) B]

end

/-- Renaming a value by `ρ₂` then by `ρ₁` is renaming it by their composition `ρ₃`. -/
theorem Val.rename_rename_of {Γ Δ Ξ : Scope} {a : List Grade} {ρ₁ : Ren Γ Δ} {ρ₂ : Ren Δ Ξ}
    {ρ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ρ₁ (ρ₂ x) = ρ₃ x) :
    (v : Val k Ξ a) → (v.rename ρ₂).rename ρ₁ = v.rename ρ₃
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_rename_of h t)

/-- Renaming each variable to itself changes no value. -/
theorem Val.rename_id_of {Γ : Scope} {a : List Grade} {ρ : Ren Γ Γ}
    (h : ∀ {a} (x : Var Γ a), ρ x = x) : (v : Val k Γ a) → v.rename ρ = v
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_id_of h t)

/-! ### Substitutions after Renamings -/

theorem Subst₀.lift_rename_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst₀.lift σ (Ren.lift ρ x) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (Val.rename Ren.weaken) (h x)

theorem Subst₀.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst₀.liftN n σ (Ren.liftN n ρ x) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ) n
      (Subst₀.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `ρ` then substituting by `σ` is substituting by their composition `σ'`. -/
theorem Term.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (t : Term k Ξ) → (t.rename ρ).subst₀ σ = t.subst₀ σ'
  | .var x ts => by
    rw [Term.rename, Term.subst₀_var, Term.subst₀_var, h x, Args.subst₀_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as]

theorem Args.subst₀_rename_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (ts : Args k Ξ a) → (ts.rename ρ).subst₀ σ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst₀, Args.subst₀, Term.subst₀_rename_of h t,
      Args.subst₀_rename_of h ts]

theorem InstanceArgs.subst₀_rename_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ρ).subst₀ σ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst₀, InstanceArgs.subst₀,
      InstanceArgs.subst₀_rename_of h as, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) B]

end

/-- Renaming a value by `ρ` then substituting it by `σ` is substituting it by their composition
`σ'`. -/
theorem Val.subst₀_rename_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst₀ k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (v : Val k Ξ a) → (v.rename ρ).subst₀ σ = v.subst₀ σ'
  | .var x => h x
  | .term t => congrArg Val.term (Term.subst₀_rename_of h t)

/-! ### Renamings after Substitutions -/

theorem Subst₀.lift_rename_after_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst₀ k Δ Ξ}
    {ρ : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), (Subst₀.lift σ x).rename (Ren.lift ρ) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ x).rename Ren.weaken).rename (Ren.lift ρ) = (σ' x).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (ρ₁ := Ren.lift ρ) (ρ₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (ρ₁ := Ren.weaken) (ρ₂ := ρ) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Δ Ξ} {ρ : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ x).rename (Ren.liftN n ρ) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_after_of (Γ := [] :: Γ) (Δ := [] :: Δ)
      (Ξ := [] :: Ξ) n (Subst₀.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`.
/-- Substituting by `σ` then renaming by `ρ` is substituting by their composition `σ'`. -/
theorem Term.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) :
    (t : Term k Ξ) → (t.subst₀ σ).rename ρ = t.subst₀ σ'
  | .var x ts => by
    rw [Term.subst₀_var, Term.subst₀_var, ← h x, ← Args.rename_subst₀_of h ts]
    cases σ x <;> rfl
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as]

theorem Args.rename_subst₀_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst₀ k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) :
    (ts : Args k Ξ a) → (ts.subst₀ σ).rename ρ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.rename, Args.subst₀, Term.rename_subst₀_of h t,
      Args.rename_subst₀_of h ts]

theorem InstanceArgs.rename_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst₀ σ).rename ρ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.rename, InstanceArgs.subst₀,
      InstanceArgs.rename_subst₀_of h as,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) B]

end

/-- Substituting a value by `σ` then renaming it by `ρ` is substituting it by their composition
`σ'`. -/
theorem Val.rename_subst₀_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst₀ k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ρ = σ' x) :
    (v : Val k Ξ a) → (v.subst₀ σ).rename ρ = v.subst₀ σ'
  | .var x => h x
  | .term t => congrArg Val.term (Term.rename_subst₀_of h t)

/-- A value under a new entry, substituted under it, is the value substituted, under the entry. -/
theorem Val.rename_weaken_subst₀_lift {Γ Δ : Scope} {a b : List Grade} (σ : Subst₀ k Γ Δ)
    (v : Val k Δ a) :
    (v.rename Ren.weaken).subst₀ (Subst₀.lift (qs := b) σ) = (v.subst₀ σ).rename Ren.weaken :=
  (Val.subst₀_rename_of (fun _ => rfl) v).trans (Val.rename_subst₀_of (fun _ => rfl) v).symm

/-! ### Substitutions after Substitutions -/

theorem Subst₀.lift_subst₀_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst₀ k Δ Ξ}
    {τ : Subst₀ k Γ Δ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), (Subst₀.lift σ x).subst₀ (Subst₀.lift τ) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => (Val.rename_weaken_subst₀_lift τ (σ x)).trans (congrArg _ (h x))

theorem Subst₀.liftN_subst₀_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ x).subst₀ (Subst₀.liftN n τ) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_subst₀_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ) n
      (Subst₀.lift_subst₀_of h)

mutual

-- ADE: `substCompEq`, in `Definition/Untyped/Properties.agda`.
/-- Substituting by `σ` then by `τ` is substituting by their composition `σ'`. -/
theorem Term.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (t : Term k Ξ) → (t.subst₀ σ).subst₀ τ = t.subst₀ σ'
  | .var x ts => by
    rw [Term.subst₀_var, Term.subst₀_var, ← h x, ← Args.subst₀_subst₀_of h ts]
    cases σ x with
    | var y => exact Term.subst₀_var τ y _
    | term t => rfl
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_subst₀_of h as]

theorem Args.subst₀_subst₀_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst₀ k Δ Ξ}
    {τ : Subst₀ k Γ Δ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (ts : Args k Ξ a) → (ts.subst₀ σ).subst₀ τ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.subst₀, Args.subst₀, Term.subst₀_subst₀_of h t,
      Args.subst₀_subst₀_of h ts]

theorem InstanceArgs.subst₀_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst₀ σ).subst₀ τ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst₀, InstanceArgs.subst₀,
      InstanceArgs.subst₀_subst₀_of h as, Term.subst₀_subst₀_of (Subst₀.liftN_subst₀_of _ h) B]

end

/-! ### Weakenings and New Variables -/

/-- A renaming under new variables renames an old variable as it does without them. -/
theorem Ren.liftN_weakenN {Γ Δ : Scope} {a : List Grade} :
    ∀ (n : Nat) (ρ : Ren Γ Δ) (x : Var Δ a), Ren.liftN n ρ (x.weakenN n) = (ρ x).weakenN n
  | 0, _, _ => rfl
  | n + 1, ρ, x => Ren.liftN_weakenN (Γ := [] :: Γ) (Δ := [] :: Δ) n (Ren.lift ρ) x.succ

/-- A substitution under new variables gives an old variable what it gives it without them,
under them. -/
theorem Subst₀.liftN_weakenN {Γ Δ : Scope} {a : List Grade} :
    ∀ (n : Nat) (σ : Subst₀ k Γ Δ) (x : Var Δ a),
      Subst₀.liftN n σ (x.weakenN n) = (σ x).rename (Ren.weakenN n)
  | 0, σ, x => (Val.rename_id_of (fun _ => rfl) (σ x)).symm
  | n + 1, σ, x => by
    rw [Var.weakenN, Subst₀.liftN, Subst₀.liftN_weakenN (Γ := [] :: Γ) (Δ := [] :: Δ) n]
    exact Val.rename_rename_of (fun _ => rfl) (σ x)

/-- A renaming under the new variables keeps them. -/
theorem Args.bound_rename {Γ Δ : Scope} :
    ∀ (ps : List Grade) (ρ : Ren Γ Δ),
      (Args.bound (k := k) (Γ := Δ) ps).rename (Ren.liftN ps.length ρ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, ρ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).rename (Ren.liftN ps.length (Ren.lift ρ)))
        ((Args.bound (Γ := [] :: Δ) ps).rename (Ren.liftN ps.length (Ren.lift ρ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := [] :: Γ) ps)
    rw [Args.bound_rename ps (Ren.lift ρ), Term.rename, Ren.liftN_weakenN]
    rfl

/-- A substitution of the first order under the new variables keeps them. -/
theorem Args.bound_subst₀ {Γ Δ : Scope} :
    ∀ (ps : List Grade) (σ : Subst₀ k Γ Δ),
      (Args.bound (Γ := Δ) ps).subst₀ (Subst₀.liftN ps.length σ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, σ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst₀
          (Subst₀.liftN ps.length (Subst₀.lift σ)))
        ((Args.bound (Γ := [] :: Δ) ps).subst₀ (Subst₀.liftN ps.length (Subst₀.lift σ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := [] :: Γ) ps)
    rw [Args.bound_subst₀ ps (Subst₀.lift σ), Term.subst₀_var, Subst₀.liftN_weakenN]
    rfl

/-- Substituting each variable by itself changes no value. -/
theorem Val.subst₀_id_of {Γ : Scope} {a : List Grade} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (v : Val k Γ a) → v.subst₀ σ = v
  | .var x => h x
  | .term t => congrArg Val.term (Term.subst₀_id_of h t)

-- ADE: `substVar-to-subst`, in `Definition/Untyped/Properties.agda`.
/-- Substitutions of the first order that agree on every variable agree on every term. -/
theorem Term.subst₀_congr {Γ Δ : Scope} {σ σ' : Subst₀ k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), σ x = σ' x) (t : Term k Δ) : t.subst₀ σ = t.subst₀ σ' :=
  by rw [← Term.subst₀_rename_of (ρ := fun x => x) h t, Term.rename_id]

/-! ### Instantiation -/

/-- The substitution of the first order that `B[t̄ / Θ]` applies at once: each new variable of the
scope becomes its argument. -/
def Args.toSubst₀ {Γ : Scope} : {ps : List Grade} → Args k Γ ps → Subst₀ k Γ (Γ.extend ps.length)
  | [], .nil => Subst₀.id
  | _ :: ps, .cons t ts => fun x => (Subst₀.liftN ps.length (Subst₀.single t) x).subst₀ ts.toSubst₀

/-- `B[t̄ / Θ]` is the substitution `Args.toSubst₀`. -/
theorem Term.instantiate_eq_subst₀ {Γ : Scope} :
    {ps : List Grade} → (B : Term k (Γ.extend ps.length)) → (ts : Args k Γ ps) →
      B.instantiate ts = B.subst₀ ts.toSubst₀
  | [], B, .nil => (Term.subst₀_id B).symm
  | _ :: _, B, .cons _ ts =>
    (Term.instantiate_eq_subst₀ _ ts).trans (Term.subst₀_subst₀_of (fun _ => rfl) B)

/-- `Args.toSubst₀` keeps the old variables. -/
theorem Args.toSubst₀_weakenN {Γ : Scope} {a : List Grade} :
    {ps : List Grade} → (ts : Args k Γ ps) → (y : Var Γ a) →
      ts.toSubst₀ (y.weakenN ps.length) = .var y
  | [], .nil, _ => rfl
  | _ :: ps, .cons t ts, y => by
    show (Subst₀.liftN ps.length (Subst₀.single t) (y.succ.weakenN ps.length)).subst₀ ts.toSubst₀ = _
    rw [Subst₀.liftN_weakenN]
    exact Args.toSubst₀_weakenN ts y

/-- `Args.toSubst₀ t̄` gives the new variables the arguments `t̄`. -/
theorem Args.bound_toSubst₀ {Γ : Scope} :
    {ps : List Grade} → (ts : Args k Γ ps) → (Args.bound ps).subst₀ ts.toSubst₀ = ts
  | [], .nil => rfl
  | _ :: ps, .cons t ts => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst₀ (Args.toSubst₀ (.cons t ts)))
        ((Args.bound (Γ := [] :: Γ) ps).subst₀ fun x =>
          (Subst₀.liftN ps.length (Subst₀.single t) x).subst₀ ts.toSubst₀) = _
    rw [← Args.subst₀_subst₀_of (fun _ => rfl), Args.bound_subst₀, Args.bound_toSubst₀ ts]
    erw [Term.subst₀_var]
    show Args.cons ((Val.subst₀ ts.toSubst₀
        (Subst₀.liftN ps.length (Subst₀.single t) (Var.weakenN ps.length .zero))).apply _) ts = _
    rw [Subst₀.liftN_weakenN]
    show Args.cons ((t.rename (Ren.weakenN ps.length)).subst₀ ts.toSubst₀) ts = _
    rw [Term.subst₀_rename_of (ρ := Ren.weakenN ps.length) (σ' := Subst₀.id)
      (Args.toSubst₀_weakenN ts), Term.subst₀_id]

/-- `(x̄. x[x̄])[t̄ / x̄] = x[t̄]`. -/
theorem Var.eta_instantiate {Γ : Scope} {ps : List Grade} (x : Var Γ ps) (ts : Args k Γ ps) :
    (Var.eta x).instantiate ts = .var x ts := by
  rw [Term.instantiate_eq_subst₀, Var.eta, Term.subst₀_var, Args.toSubst₀_weakenN,
    Args.bound_toSubst₀]
  rfl

theorem Subst₀.lift_comm_of {Γ Δ Ξ Ψ : Scope} {b : List Grade} {σ₁ : Subst₀ k Δ Ξ}
    {σ₂ : Subst₀ k Γ Δ} {σ₃ : Subst₀ k Ψ Ξ} {σ₄ : Subst₀ k Γ Ψ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).subst₀ σ₂ = (σ₃ x).subst₀ σ₄) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst₀.lift σ₁ x).subst₀ (Subst₀.lift σ₂) = (Subst₀.lift σ₃ x).subst₀ (Subst₀.lift σ₄)
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ₁ x).rename Ren.weaken).subst₀ _ = ((σ₃ x).rename Ren.weaken).subst₀ _
    rw [Val.rename_weaken_subst₀_lift, Val.rename_weaken_subst₀_lift, h x]

theorem Subst₀.liftN_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₁ : Subst₀ k Δ Ξ} {σ₂ : Subst₀ k Γ Δ} {σ₃ : Subst₀ k Ψ Ξ} {σ₄ : Subst₀ k Γ Ψ},
      (∀ {a} (x : Var Ξ a), (σ₁ x).subst₀ σ₂ = (σ₃ x).subst₀ σ₄) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ₁ x).subst₀ (Subst₀.liftN n σ₂) =
          (Subst₀.liftN n σ₃ x).subst₀ (Subst₀.liftN n σ₄)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.liftN_comm_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ)
      (Ψ := [] :: Ψ) n (Subst₀.lift_comm_of h)

/-- Two pairs of substitutions of the first order whose compositions agree on every variable
agree on every term. -/
theorem Term.subst₀_comm_of {Γ Δ Ξ Ψ : Scope} {σ₁ : Subst₀ k Δ Ξ} {σ₂ : Subst₀ k Γ Δ}
    {σ₃ : Subst₀ k Ψ Ξ} {σ₄ : Subst₀ k Γ Ψ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).subst₀ σ₂ = (σ₃ x).subst₀ σ₄) (t : Term k Ξ) :
    (t.subst₀ σ₁).subst₀ σ₂ = (t.subst₀ σ₃).subst₀ σ₄ :=
  (Term.subst₀_subst₀_of (fun _ => rfl) t).trans
    (Term.subst₀_subst₀_of (fun x => (h x).symm) t).symm

/-- The substitution of `t` for the last variable, then `σ`, is `σ` under it, then the substitution of
`t[σ]`. -/
theorem Subst₀.single_comm {Γ Δ : Scope} (t : Term k Δ) (σ : Subst₀ k Γ Δ) :
    ∀ {a} (x : Var ([] :: Δ) a),
      (Subst₀.single t x).subst₀ σ = (Subst₀.lift σ x).subst₀ (Subst₀.single (t.subst₀ σ))
  | _, .zero => rfl
  | _, .succ x => by
    show σ x = ((σ x).rename Ren.weaken).subst₀ _
    rw [Val.subst₀_rename_of (σ := Subst₀.single (t.subst₀ σ)) (ρ := Ren.weaken) (σ' := Subst₀.id)
      (fun _ => rfl), Val.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl)]

-- ADE: `singleSubstLift`, in `Definition/Untyped/Properties.agda`.
/-- `B[t̄ / x̄][σ] = B[σ⇑][t̄[σ] / x̄]`. -/
theorem Term.instantiate_subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) :
    {ps : List Grade} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).subst₀ σ = (B.subst₀ (Subst₀.liftN ps.length σ)).instantiate (ts.subst₀ σ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).subst₀ σ =
      Term.instantiate ((B.subst₀ (Subst₀.liftN ps.length (Subst₀.lift σ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.subst₀ σ)))) (ts.subst₀ σ)
    rw [Term.instantiate_subst₀ σ]
    congr 1
    exact Term.subst₀_comm_of (Subst₀.liftN_comm_of ps.length (Subst₀.single_comm t σ)) B

theorem Subst₀.lift_rename_comm_of {Γ Δ Ξ Ψ : Scope} {b : List Grade} {σ₁ : Subst₀ k Δ Ξ}
    {ρ₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {ρ₂ : Ren Ψ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename ρ₁ = σ₂ (ρ₂ x)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst₀.lift σ₁ x).rename (Ren.lift ρ₁) = Subst₀.lift σ₂ (Ren.lift ρ₂ x)
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ₁ x).rename Ren.weaken).rename (Ren.lift ρ₁) = (σ₂ (ρ₂ x)).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (ρ₁ := Ren.lift ρ₁) (ρ₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (ρ₁ := Ren.weaken) (ρ₂ := ρ₁) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₁ : Subst₀ k Δ Ξ} {ρ₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {ρ₂ : Ren Ψ Ξ},
      (∀ {a} (x : Var Ξ a), (σ₁ x).rename ρ₁ = σ₂ (ρ₂ x)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ₁ x).rename (Ren.liftN n ρ₁) = Subst₀.liftN n σ₂ (Ren.liftN n ρ₂ x)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.liftN_rename_comm_of (Γ := [] :: Γ) (Δ := [] :: Δ)
      (Ξ := [] :: Ξ) (Ψ := [] :: Ψ) n (Subst₀.lift_rename_comm_of h)

-- ADE: `wk-β`, in `Definition/Untyped/Properties.agda`.
/-- `B[t̄ / x̄][ρ] = B[ρ⇑][t̄[ρ] / x̄]`. -/
theorem Term.instantiate_rename {Γ Δ : Scope} (ρ : Ren Γ Δ) :
    {ps : List Grade} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).rename ρ = (B.rename (Ren.liftN ps.length ρ)).instantiate (ts.rename ρ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).rename ρ =
      Term.instantiate ((B.rename (Ren.liftN ps.length (Ren.lift ρ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.rename ρ)))) (ts.rename ρ)
    rw [Term.instantiate_rename ρ]
    congr 1
    exact (Term.rename_subst₀_of (fun _ => rfl) B).trans ((Term.subst₀_congr
      (Subst₀.liftN_rename_comm_of ps.length (σ₂ := Subst₀.single (t.rename ρ)) (ρ₂ := Ren.lift ρ)
        fun x => by cases x <;> rfl) B).trans (Term.subst₀_rename_of (fun _ => rfl) B).symm)

/-! ### Substitutions of the Second Order after Renamings -/

theorem Subst.lift_rename_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst.lift σ (Ren.lift ρ x) = Subst.lift σ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (fun t => Term.rename (Ren.liftN _ Ren.weaken) t) (h x)

theorem Subst.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst k Γ Δ} {ρ : Ren Δ Ξ} {σ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst.liftN n σ (Ren.liftN n ρ x) = Subst.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ) n
      (Subst.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Renaming by `ρ` then substituting by `σ` is substituting by their composition `σ'`. -/
theorem Term.subst_rename_of {Γ Δ Ξ : Scope} {σ : Subst k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (t : Term k Ξ) → (t.rename ρ).subst σ = t.subst σ'
  | .var x ts => by rw [Term.rename, Term.subst, Term.subst, h x, Args.subst_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as]

theorem Args.subst_rename_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (ts : Args k Ξ a) → (ts.rename ρ).subst σ = ts.subst σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst, Args.subst, Term.subst_rename_of h t, Args.subst_rename_of h ts]

theorem InstanceArgs.subst_rename_of {Γ Δ Ξ Ψ : Scope} {σ : Subst k Γ Δ} {ρ : Ren Δ Ξ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ρ x) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ρ).subst σ = as.subst σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.subst_rename_of h as, Term.subst_rename_of (Subst.liftN_rename_of _ h) B]

end

/-! ### Renamings after Substitutions of the Second Order -/

/-- `(x̄. x[x̄])[ρ] = x̄. ρ(x)[x̄]`. -/
theorem Var.eta_rename {Γ Δ : Scope} {ps : List Grade} (ρ : Ren Γ Δ) (x : Var Δ ps) :
    (Var.eta (k := k) x).rename (Ren.liftN ps.length ρ) = Var.eta (ρ x) := by
  rw [Var.eta, Term.rename, Ren.liftN_weakenN, Args.bound_rename]
  rfl

theorem Subst.lift_rename_after_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst k Δ Ξ}
    {ρ : Ren Γ Δ} {σ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ x).rename (Ren.liftN a.length ρ) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst.lift σ x).rename (Ren.liftN a.length (Ren.lift ρ)) = Subst.lift σ' x
  | _, .zero => Var.eta_rename _ _
  | a, .succ x => by
    show ((σ x).rename (Ren.liftN a.length Ren.weaken)).rename (Ren.liftN a.length (Ren.lift ρ)) =
      (σ' x).rename (Ren.liftN a.length Ren.weaken)
    rw [← h x, Term.rename_rename_of (Ren.liftN_comp_of _ (ρ₁ := Ren.lift ρ) (ρ₂ := Ren.weaken)
        (ρ₃ := fun y => (ρ y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (ρ₁ := Ren.weaken) (ρ₂ := ρ)
        (ρ₃ := fun y => (ρ y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst k Δ Ξ} {ρ : Ren Γ Δ} {σ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).rename (Ren.liftN a.length ρ) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst.liftN n σ x).rename (Ren.liftN a.length (Ren.liftN n ρ)) = Subst.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_after_of (Γ := [] :: Γ) (Δ := [] :: Δ)
      (Ξ := [] :: Ξ) n (Subst.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substituting by `σ` then renaming by `ρ` is substituting by their composition `σ'`, which renames
each abstraction under its variables. -/
theorem Term.rename_subst_of {Γ Δ Ξ : Scope} {σ : Subst k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename (Ren.liftN a.length ρ) = σ' x) :
    (t : Term k Ξ) → (t.subst σ).rename ρ = t.subst σ'
  | .var x ts => by
    rw [Term.subst, Term.subst, Term.instantiate_rename, h x, Args.rename_subst_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as]

theorem Args.rename_subst_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename (Ren.liftN a.length ρ) = σ' x) :
    (ts : Args k Ξ a) → (ts.subst σ).rename ρ = ts.subst σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.rename, Args.subst, Term.rename_subst_of h t, Args.rename_subst_of h ts]

theorem InstanceArgs.rename_subst_of {Γ Δ Ξ Ψ : Scope} {σ : Subst k Δ Ξ} {ρ : Ren Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename (Ren.liftN a.length ρ) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst σ).rename ρ = as.subst σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.rename, InstanceArgs.subst,
      InstanceArgs.rename_subst_of h as, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) B]

end

/-! ### Substitutions of the Second Order after Substitutions of the First Order -/

/-- Substituting by `σ₀` then by `σ` is substituting by `σ'` then by `σ₀'`, variable by variable:
a variable that `σ₀` renames to `y` becomes `σ y` either way, and a variable that `σ₀` replaces by
`u` becomes `u[σ]`. -/
def Subst₀.Swaps {Γ Δ Ξ Ψ : Scope} (σ₀ : Subst₀ k Δ Ξ) (σ : Subst k Γ Δ) (σ' : Subst k Ψ Ξ)
    (σ₀' : Subst₀ k Γ Ψ) : Prop :=
  (∀ {a} (x : Var Ξ a) (y : Var Δ a), σ₀ x = .var y →
    (σ' x).subst₀ (Subst₀.liftN a.length σ₀') = σ y) ∧
  ∀ (x : Var Ξ []) (u : Term k Δ), σ₀ x = .term u → (σ' x).subst₀ σ₀' = u.subst σ

/-- `(x̄. x[x̄])[σ⇑] = x̄. y[x̄]`, when `σ` renames `x` to `y`. -/
theorem Var.eta_subst₀_of {Γ Δ : Scope} {ps : List Grade} {σ : Subst₀ k Γ Δ} {x : Var Δ ps}
    {y : Var Γ ps} (h : σ x = .var y) :
    (Var.eta (k := k) x).subst₀ (Subst₀.liftN ps.length σ) = Var.eta y := by
  rw [Var.eta, Term.subst₀_var, Subst₀.liftN_weakenN, h, Args.bound_subst₀]
  rfl

/-- A term under a new entry, substituted under it, is the term substituted, under the entry. -/
theorem Term.rename_weaken_subst₀_lift {Γ Δ : Scope} {b : List Grade} (σ : Subst₀ k Γ Δ)
    (t : Term k Δ) :
    (t.rename Ren.weaken).subst₀ (Subst₀.lift (qs := b) σ) = (t.subst₀ σ).rename Ren.weaken :=
  (Term.subst₀_rename_of (fun _ => rfl) t).trans (Term.rename_subst₀_of (fun _ => rfl) t).symm

theorem Subst₀.Swaps.lift {Γ Δ Ξ Ψ : Scope} {b : List Grade} {σ₀ : Subst₀ k Δ Ξ}
    {σ : Subst k Γ Δ} {σ' : Subst k Ψ Ξ} {σ₀' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ₀ σ σ' σ₀') :
    Subst₀.Swaps (Subst₀.lift (qs := b) σ₀) (Subst.lift σ) (Subst.lift σ') (Subst₀.lift σ₀') := by
  refine ⟨fun x y e => ?_, fun x u e => ?_⟩
  · cases x with
    | zero =>
      cases e
      exact Var.eta_subst₀_of rfl
    | succ x =>
      change (σ₀ x).rename Ren.weaken = _ at e
      generalize e₀ : σ₀ x = v at e
      cases v with
      | term => cases e
      | var y' =>
        cases e
        show ((σ' x).rename (Ren.liftN _ Ren.weaken)).subst₀ _ =
          (σ y').rename (Ren.liftN _ Ren.weaken)
        refine Eq.trans ?_ (congrArg (Term.rename (Ren.liftN _ Ren.weaken)) (h.1 x y' e₀))
        exact (Term.subst₀_rename_of (fun _ => rfl) _).trans ((Term.subst₀_congr
          (fun z => (Subst₀.liftN_rename_comm_of _ (fun _ => rfl) z).symm) _).trans
          (Term.rename_subst₀_of (fun _ => rfl) _).symm)
  · cases x with
    | zero => cases e
    | succ x =>
      change (σ₀ x).rename Ren.weaken = _ at e
      generalize e₀ : σ₀ x = v at e
      cases v with
      | var => cases e
      | term u' =>
        cases e
        show ((σ' x).rename Ren.weaken).subst₀ (Subst₀.lift σ₀') = (u'.rename Ren.weaken).subst _
        exact (Term.rename_weaken_subst₀_lift σ₀' (σ' x)).trans
          ((congrArg (Term.rename Ren.weaken) (h.2 x u' e₀)).trans
            ((Term.rename_subst_of (fun _ => rfl) u').trans (Term.subst_rename_of (σ := Subst.lift (qs := b) σ) (ρ := Ren.weaken)
              (σ' := fun x => (σ x).rename (Ren.liftN _ Ren.weaken)) (fun _ => rfl) u').symm))

theorem Subst₀.Swaps.liftN {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₀ : Subst₀ k Δ Ξ} {σ : Subst k Γ Δ} {σ' : Subst k Ψ Ξ} {σ₀' : Subst₀ k Γ Ψ},
      Subst₀.Swaps σ₀ σ σ' σ₀' →
      Subst₀.Swaps (Subst₀.liftN n σ₀) (Subst.liftN n σ) (Subst.liftN n σ') (Subst₀.liftN n σ₀')
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.Swaps.liftN (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ)
      (Ψ := [] :: Ψ) n h.lift

mutual

/-- A substitution of the first order then one of the second order swap, as `Subst₀.Swaps` says. -/
theorem Term.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ₀ : Subst₀ k Δ Ξ} {σ : Subst k Γ Δ}
    {σ' : Subst k Ψ Ξ} {σ₀' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ₀ σ σ' σ₀') :
    (t : Term k Ξ) → (t.subst₀ σ₀).subst σ = (t.subst σ').subst₀ σ₀'
  | .var x ts => by
    rw [Term.subst₀_var, Term.subst, Term.instantiate_subst₀, ← Args.subst_subst₀_of h ts]
    generalize e : σ₀ x = v
    cases v with
    | var y => rw [h.1 x y e]; rfl
    | term u => cases ts; exact (h.2 x u e).symm
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as]

theorem Args.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {a : List Grade} {σ₀ : Subst₀ k Δ Ξ}
    {σ : Subst k Γ Δ} {σ' : Subst k Ψ Ξ} {σ₀' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ₀ σ σ' σ₀') :
    (ts : Args k Ξ a) → (ts.subst₀ σ₀).subst σ = (ts.subst σ').subst₀ σ₀'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.subst, Args.subst, Args.subst₀, Term.subst_subst₀_of h t,
      Args.subst_subst₀_of h ts]

theorem InstanceArgs.subst_subst₀_of {Γ Δ Ξ Ψ Φ : Scope} {σ₀ : Subst₀ k Δ Ξ}
    {σ : Subst k Γ Δ} {σ' : Subst k Ψ Ξ} {σ₀' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ₀ σ σ' σ₀') :
    (as : InstanceArgs k Ξ Φ) → (as.subst₀ σ₀).subst σ = (as.subst σ').subst₀ σ₀'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst₀,
      InstanceArgs.subst_subst₀_of h as, Term.subst_subst₀_of (Subst₀.Swaps.liftN _ h) B]

end

/-- The substitution of an argument swaps with a substitution of the second order. -/
theorem Subst₀.Swaps.single {Γ Δ : Scope} (t : Term k Δ) (σ : Subst k Γ Δ) :
    Subst₀.Swaps (Subst₀.single t) σ (Subst.lift σ) (Subst₀.single (t.subst σ)) := by
  refine ⟨fun x y e => ?_, fun x u e => ?_⟩
  · cases x with
    | zero => cases e
    | succ x =>
      cases e
      exact (Term.subst₀_rename_of (σ := Subst₀.liftN _ (Subst₀.single (t.subst σ)))
        (ρ := Ren.liftN _ Ren.weaken) (σ' := Subst₀.liftN _ Subst₀.id)
        (Subst₀.liftN_rename_of _ fun _ => rfl) _).trans
        (Term.subst₀_id_of (Subst₀.liftN_id_of _ fun _ => rfl) _)
  · cases x with
    | zero => cases e; rfl
    | succ x => cases e

-- ADE: `singleSubstLift`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- `B[t̄ / x̄][σ] = B[σ⇑][t̄[σ] / x̄]`, for a substitution of the second order. -/
theorem Term.instantiate_subst {Γ Δ : Scope} (σ : Subst k Γ Δ) :
    {ps : List Grade} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).subst σ = (B.subst (Subst.liftN ps.length σ)).instantiate (ts.subst σ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).subst σ =
      Term.instantiate ((B.subst (Subst.liftN ps.length (Subst.lift σ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.subst σ)))) (ts.subst σ)
    rw [Term.instantiate_subst σ]
    congr 1
    exact Term.subst_subst₀_of (Subst₀.Swaps.liftN _ (Subst₀.Swaps.single t σ)) B

/-! ### Substitutions of the Second Order after Substitutions of the Second Order -/

-- ADE: `substVar-to-subst`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substitutions of the second order that agree on every variable agree on every term. -/
theorem Term.subst_congr {Γ Δ : Scope} {σ σ' : Subst k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), σ x = σ' x) (t : Term k Δ) : t.subst σ = t.subst σ' := by
  rw [← Term.subst_rename_of (ρ := fun x => x) h t, Term.rename_id]

/-- A substitution of the second order under new variables gives an old variable what it gives it
without them, under them. -/
theorem Subst.liftN_weakenN {Γ Δ : Scope} {a : List Grade} :
    ∀ (n : Nat) (σ : Subst k Γ Δ) (x : Var Δ a),
      Subst.liftN n σ (x.weakenN n) = (σ x).rename (Ren.liftN a.length (Ren.weakenN n))
  | 0, σ, x => (Term.rename_id_of (Ren.liftN_id_of _ fun _ => rfl) (σ x)).symm
  | n + 1, σ, x => by
    show Subst.liftN n (Subst.lift σ) (x.succ.weakenN n) = _
    rw [Subst.liftN_weakenN (Γ := [] :: Γ) (Δ := [] :: Δ) n]
    exact Term.rename_rename_of (Ren.liftN_comp_of _ fun _ => rfl) (σ x)

/-- A substitution of the second order under the new variables keeps them. -/
theorem Args.bound_subst {Γ Δ : Scope} :
    ∀ (ps : List Grade) (σ : Subst k Γ Δ),
      (Args.bound (Γ := Δ) ps).subst (Subst.liftN ps.length σ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, σ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst
          (Subst.liftN ps.length (Subst.lift σ)))
        ((Args.bound (Γ := [] :: Δ) ps).subst (Subst.liftN ps.length (Subst.lift σ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := [] :: Γ) ps)
    rw [Args.bound_subst ps (Subst.lift σ), Term.subst, Subst.liftN_weakenN]
    rfl

/-- `(x̄. X[x̄])[σ⇑⇑]`, for the last variable `X`, is itself. -/
theorem Var.eta_subst_lift {Γ Δ : Scope} {ps : List Grade} (σ : Subst k Γ Δ) :
    (Var.eta (k := k) (.zero : Var (ps :: Δ) ps)).subst (Subst.liftN ps.length (Subst.lift σ)) =
      Var.eta .zero := by
  rw [Var.eta, Term.subst, Subst.liftN_weakenN, Args.bound_subst]
  show ((Var.eta .zero).rename (Ren.liftN ps.length (Ren.weakenN ps.length))).instantiate _ = _
  rw [Var.eta_rename, Var.eta_instantiate]
  rfl

theorem Subst.lift_rename_comm_of {Γ Δ Ξ Ψ : Scope} {b : List Grade} {σ₁ : Subst k Γ Δ}
    {ρ₁ : Ren Δ Ξ} {σ₂ : Subst k Ψ Ξ} {ρ₂ : Ren Γ Ψ}
    (h : ∀ {a} (x : Var Ξ a), σ₁ (ρ₁ x) = (σ₂ x).rename (Ren.liftN a.length ρ₂)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      Subst.lift σ₁ (Ren.lift ρ₁ x) = (Subst.lift σ₂ x).rename (Ren.liftN a.length (Ren.lift ρ₂))
  | _, .zero => (Var.eta_rename (Ren.lift ρ₂) .zero).symm
  | a, .succ x => by
    show (σ₁ (ρ₁ x)).rename (Ren.liftN a.length Ren.weaken) =
      ((σ₂ x).rename (Ren.liftN a.length Ren.weaken)).rename (Ren.liftN a.length (Ren.lift ρ₂))
    rw [h x, Term.rename_rename_of (Ren.liftN_comp_of _ (ρ₁ := Ren.weaken) (ρ₂ := ρ₂)
        (ρ₃ := fun y => (ρ₂ y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (ρ₁ := Ren.lift ρ₂) (ρ₂ := Ren.weaken)
        (ρ₃ := fun y => (ρ₂ y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₁ : Subst k Γ Δ} {ρ₁ : Ren Δ Ξ} {σ₂ : Subst k Ψ Ξ} {ρ₂ : Ren Γ Ψ},
      (∀ {a} (x : Var Ξ a), σ₁ (ρ₁ x) = (σ₂ x).rename (Ren.liftN a.length ρ₂)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        Subst.liftN n σ₁ (Ren.liftN n ρ₁ x) =
          (Subst.liftN n σ₂ x).rename (Ren.liftN a.length (Ren.liftN n ρ₂))
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst.liftN_rename_comm_of (Γ := [] :: Γ) (Δ := [] :: Δ)
      (Ξ := [] :: Ξ) (Ψ := [] :: Ψ) n (Subst.lift_rename_comm_of h)

theorem Subst.lift_subst_of {Γ Δ Ξ : Scope} {b : List Grade} {σ : Subst k Δ Ξ} {τ : Subst k Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst (Subst.liftN a.length τ) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst.lift σ x).subst (Subst.liftN a.length (Subst.lift τ)) = Subst.lift σ' x
  | _, .zero => Var.eta_subst_lift τ
  | a, .succ x => by
    show ((σ x).rename (Ren.liftN a.length Ren.weaken)).subst _ =
      (σ' x).rename (Ren.liftN a.length Ren.weaken)
    rw [← h x]
    exact (Term.subst_rename_of (fun _ => rfl) _).trans ((Term.subst_congr
      (Subst.liftN_rename_comm_of _ (σ₂ := τ) (ρ₂ := Ren.weaken) fun _ => rfl) _).trans
      (Term.rename_subst_of (fun _ => rfl) _).symm)

theorem Subst.liftN_subst_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst k Δ Ξ} {τ : Subst k Γ Δ} {σ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).subst (Subst.liftN a.length τ) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst.liftN n σ x).subst (Subst.liftN a.length (Subst.liftN n τ)) = Subst.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_subst_of (Γ := [] :: Γ) (Δ := [] :: Δ) (Ξ := [] :: Ξ) n
      (Subst.lift_subst_of h)

mutual

-- ADE: `substCompEq`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substituting by `σ` then by `τ` is substituting by their composition `σ'`, which substitutes
each abstraction under its variables. -/
theorem Term.subst_subst_of {Γ Δ Ξ : Scope} {σ : Subst k Δ Ξ} {τ : Subst k Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst (Subst.liftN a.length τ) = σ' x) :
    (t : Term k Ξ) → (t.subst σ).subst τ = t.subst σ'
  | .var x ts => by
    rw [Term.subst, Term.subst, Term.instantiate_subst, h x, Args.subst_subst_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as]

theorem Args.subst_subst_of {Γ Δ Ξ : Scope} {a : List Grade} {σ : Subst k Δ Ξ}
    {τ : Subst k Γ Δ} {σ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ x).subst (Subst.liftN a.length τ) = σ' x) :
    (ts : Args k Ξ a) → (ts.subst σ).subst τ = ts.subst σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.subst, Args.subst, Term.subst_subst_of h t, Args.subst_subst_of h ts]

theorem InstanceArgs.subst_subst_of {Γ Δ Ξ Ψ : Scope} {σ : Subst k Δ Ξ} {τ : Subst k Γ Δ}
    {σ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst (Subst.liftN a.length τ) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst σ).subst τ = as.subst σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.subst_subst_of h as, Term.subst_subst_of (Subst.liftN_subst_of _ h) B]

end

/-! ## Levels -/

/-- The value of a level whose variables are replaced is its value under the values of the levels
that replace them. -/
theorem Level.value_subst {k k' : Nat} (σ : Fin k → Level k') (ρ : Fin k' → Nat) :
    ∀ l : Level k, (l.subst σ).value ρ = l.value fun i => (σ i).value ρ
  | .zero => rfl
  | .succ l => congrArg (· + 1) (Level.value_subst σ ρ l)
  | .max l₁ l₂ => by
    simp only [Level.subst, Level.value, Level.value_subst σ ρ l₁, Level.value_subst σ ρ l₂]
  | .var _ => rfl

/-! ## Examples

The instantiation of the RFC: a second-order variable `X : (x : A ⊢ B)` instantiated with the
abstraction `x. D x`, where `D` is a declared type with one parameter, replaces each application
`X[t]` by `D t`, and the arguments of an instance are substituted for its parameters. -/

/-- The abstraction `x. D x`. -/
def exampleAbstraction : Term 0 (Scope.extend [] 1) :=
  .inst "D" [] [] [] (.snoc .nil (.var₀ .zero) : InstanceArgs 0 _ [[]])

/-- The constant `c`. -/
def exampleConstant {Γ : Scope} : Term 0 Γ := .const "c" [] [] []

example :
    (Term.var .zero (.cons exampleConstant .nil) : Term 0 [[Grade.one]]).subst
        (InstanceArgs.snoc .nil exampleAbstraction).toSubst =
      .inst "D" [] [] [] (.snoc .nil exampleConstant : InstanceArgs 0 _ [[]]) :=
  rfl

/-- The application `X[X[c]]` instantiates `X` in its argument too. -/
example :
    (Term.var .zero (.cons (.var .zero (.cons exampleConstant .nil)) .nil) : Term 0 [[Grade.one]]).subst
        (InstanceArgs.snoc .nil exampleAbstraction).toSubst =
      .inst "D" [] [] []
        (.snoc .nil (.inst "D" [] [] [] (.snoc .nil exampleConstant : InstanceArgs 0 _ [[]])) :
          InstanceArgs 0 _ [[]]) :=
  rfl

/-- The arguments of a telescope are substituted in order: in `B[t₁, t₂ / x₁, x₂]`, the first
variable `x₁` is the deepest of the two. -/
example :
    (Term.instantiate (Γ := []) (ps := [Grade.one, Grade.one]) (.inst "E" [] [] []
        (.snoc (.snoc .nil (.var₀ (.succ .zero))) (.var₀ .zero) : InstanceArgs 0 _ [[], []]))
      (.cons exampleConstant (.cons (.const "d" [] [] []) .nil))) =
      .inst "E" [] [] [] (.snoc (.snoc .nil exampleConstant) (.const "d" [] [] []) :
        InstanceArgs 0 _ [[], []]) :=
  rfl

end Sic.Core
