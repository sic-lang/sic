module

public import Sic.Core.Syntax

/-!
# Substitution

The substitutions of annex 09 of RFC 36: the substitutions of the first order, among them the
substitution `B[t̄ / Θ]` of the arguments of a telescope for its variables, the substitutions of the
second order, which replace each application `X[t̄]` by `B[t̄ / x̄]` where `x̄. B` is the
abstraction given to `X`, among them the substitution `[ā / Δ]` of the arguments of an instance for
its parameters, the closed substitutions, and the instantiation `[l̄' / l̄]` of the level
variables.

A substitution of the second order replaces a second-order variable by an abstraction, so that it
substitutes the arguments of each application in the abstraction, which is not a subterm of the
term.
It is therefore built on a substitution of the first order, `subst₀`, which replaces each variable
either by a variable with the same telescope or, when it has none, by a term, and which recurses on
the term alone.
The RFC names the variables, so that a substitution of the first order leaves the variables with a
telescope; with de Bruijn indices, it renames them, as the lifts under binders need.
The renamings and the substitutions of both orders compose, and the substitution `B[t̄ / Θ]` commutes
with each of them, as the laws of composition below state.

ADE substitute terms for variables of the first order only, in `Definition/Untyped.agda`.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat}

/-! ## Renamings -/

-- ADE: `Wk`, in `Definition/Untyped/NotParametrised.agda`.
/-- A renaming of the scope `Δ` in the scope `Γ`, which keeps the entry of each variable. -/
abbrev Ren (Γ Δ : Scope) : Type := ∀ {e : Scope.Entry}, Var Δ e → Var Γ e

namespace Ren

/-- The renaming `ξ` under a new entry. -/
def lift {Γ Δ : Scope} {e : Scope.Entry} (ξ : Ren Γ Δ) : Ren (e :: Γ) (e :: Δ) := fun x =>
  match x with
  | .zero => .zero
  | .succ x => .succ (ξ x)

/-- The renaming `ξ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Ren Γ Δ → Ren (Γ.extend n) (Δ.extend n)
  | 0, ξ => ξ
  | n + 1, ξ => liftN n (lift ξ)

/-- The renaming that skips a new entry. -/
def weaken {Γ : Scope} {e : Scope.Entry} : Ren (e :: Γ) Γ := fun x => .succ x

end Ren

/-- The variable `x` in the scope extended by `n` new variables. -/
def Var.weakenN {Γ : Scope} {e : Scope.Entry} : (n : Nat) → Var Γ e → Var (Γ.extend n) e
  | 0, x => x
  | n + 1, x => Var.weakenN n (.succ x)

mutual

-- ADE: `wk`, in `Definition/Untyped.agda`.
/-- The term `t` renamed by `ξ`. -/
def Term.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : Term k Δ → Term k Γ
  | .var x ts => .var (ξ x) (ts.rename ξ)
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.rename ξ)
  | .ctor D qs ls ps as c ts => .ctor D qs ls ps (as.rename ξ) c (ts.rename ξ)
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs ls ps (as.rename ξ) (t.rename ξ) (Cs.rename ξ) (us.rename ξ)

/-- The arguments `t̄` renamed by `ξ`. -/
def Args.rename {Γ Δ : Scope} {a : List Parameter} (ξ : Ren Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.rename ξ) (ts.rename ξ)

/-- The arguments `ā` renamed by `ξ`, under the variables of each abstraction. -/
def InstanceArgs.rename {Γ Δ Ξ : Scope} (ξ : Ren Γ Δ) : InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.rename ξ) (B.rename (Ren.liftN _ ξ))

/-- The terms `t̄` renamed by `ξ`. -/
def Terms.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : Terms k Δ → Terms k Γ
  | .nil => .nil
  | .cons t ts => .cons (t.rename ξ) (ts.rename ξ)

/-- The motives `C̄` renamed by `ξ`, under the variables of each motive. -/
def Motives.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : Motives k Δ → Motives k Γ
  | .nil => .nil
  | .cons n C Cs => .cons n (C.rename (Ren.liftN _ ξ)) (Cs.rename ξ)

/-- The branches `ū` renamed by `ξ`, under the variables of each branch. -/
def Branches.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : Branches k Δ → Branches k Γ
  | .nil => .nil
  | .cons n m u us => .cons n m (u.rename (Ren.liftN _ ξ)) (us.rename ξ)

end

/-- The arguments `(x₁, …, xₐ)`: the new variables of the scope `Γ.extend a`, in order, for a
telescope whose entries have the parameters `ps`. -/
def Args.bound {Γ : Scope} : (ps : List Parameter) → Args k (Γ.extend ps.length) ps
  | [] => .nil
  | _ :: ps => .cons (.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := .var :: Γ) ps)

/-- `x̄. x[x̄]`: the variable `x` as an abstraction over a variable for each entry of its telescope,
which the identity of the second order gives `x`.
RFC: `\mathsf{identity}_\theta` -/
def Var.eta {Γ : Scope} {e : Scope.Entry} (x : Var Γ e) : Term k (Γ.extend e.params.length) :=
  .var (x.weakenN e.params.length) (Args.bound e.params)

/-! ## Substitutions of the First Order -/

/-- What a substitution of the first order gives a variable whose entry is `e`: a variable with the
same entry, or a term for a variable. -/
inductive Val (k : Nat) (Γ : Scope) : Scope.Entry → Type where
  /-- A variable. -/
  | var {e : Scope.Entry} (x : Var Γ e) : Val k Γ e
  /-- A term, for a variable. -/
  | term (t : Term k Γ) : Val k Γ .var

/-- The value `v` renamed by `ξ`. -/
def Val.rename {Γ Δ : Scope} {a : Scope.Entry} (ξ : Ren Γ Δ) : Val k Δ a → Val k Γ a
  | .var x => .var (ξ x)
  | .term t => .term (t.rename ξ)

-- ADE: `Subst`, in `Definition/Untyped.agda`.
/-- A substitution of the first order of the scope `Δ` in the scope `Γ`. -/
abbrev Subst₀ (k : Nat) (Γ Δ : Scope) : Type := ∀ {e : Scope.Entry}, Var Δ e → Val k Γ e

namespace Subst₀

/-- The identity, which gives each variable itself.
RFC: `\mathsf{identity}_\sigma` -/
def id {Γ : Scope} : Subst₀ k Γ Γ := fun x => .var x

/-- The substitution `σ` under a new entry. -/
def lift {Γ Δ : Scope} {e : Scope.Entry} (σ : Subst₀ k Γ Δ) : Subst₀ k (e :: Γ) (e :: Δ) :=
  fun x =>
  match x with
  | .zero => .var .zero
  | .succ x => (σ x).rename Ren.weaken

/-- The substitution `σ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Subst₀ k Γ Δ → Subst₀ k (Γ.extend n) (Δ.extend n)
  | 0, σ => σ
  | n + 1, σ => liftN n (lift σ)

-- ADE: `sgSubst`, in `Definition/Untyped.agda`.
/-- `[t / x]`: the substitution of `t` for the last variable, which gives each other variable
itself.
RFC: `\mathsf{single}_\sigma` -/
def single {Γ : Scope} (t : Term k Γ) : Subst₀ k Γ (.var :: Γ) := fun x =>
  match x with
  | .zero => .term t
  | .succ x => .var x

end Subst₀

mutual

-- ADE: `_[_]`, in `Definition/Untyped.agda`.
/-- The term `t` substituted by `σ`.
RFC: `\mathsf{subst}_\sigma.t` -/
def Term.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Term k Δ → Term k Γ
  | .var x ts =>
    match σ x, ts.subst₀ σ with
    | .var y, us => .var y us
    | .term t, _ => t
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.subst₀ σ)
  | .ctor D qs ls ps as c ts => .ctor D qs ls ps (as.subst₀ σ) c (ts.subst₀ σ)
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs ls ps (as.subst₀ σ) (t.subst₀ σ) (Cs.subst₀ σ) (us.subst₀ σ)

/-- The arguments `t̄` substituted by `σ`.
RFC: `\mathsf{subst}_\sigma.\bar t` -/
def Args.subst₀ {Γ Δ : Scope} {a : List Parameter} (σ : Subst₀ k Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.subst₀ σ) (ts.subst₀ σ)

/-- The arguments `ā` substituted by `σ`, under the variables of each abstraction.
RFC: `\mathsf{subst}_\sigma.\bar a` -/
def InstanceArgs.subst₀ {Γ Δ Ξ : Scope} (σ : Subst₀ k Γ Δ) :
    InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.subst₀ σ) (B.subst₀ (Subst₀.liftN _ σ))

/-- The terms `t̄` substituted by `σ`.
RFC: `\mathsf{subst}_\sigma.\bar t` -/
def Terms.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Terms k Δ → Terms k Γ
  | .nil => .nil
  | .cons t ts => .cons (t.subst₀ σ) (ts.subst₀ σ)

/-- The motives `C̄` substituted by `σ`, under the variables of each motive.
RFC: `\mathsf{subst}_\sigma.\bar C` -/
def Motives.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Motives k Δ → Motives k Γ
  | .nil => .nil
  | .cons n C Cs => .cons n (C.subst₀ (Subst₀.liftN _ σ)) (Cs.subst₀ σ)

/-- The branches `ū` substituted by `σ`, under the variables of each branch.
RFC: `\mathsf{subst}_\sigma.\bar u` -/
def Branches.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Branches k Δ → Branches k Γ
  | .nil => .nil
  | .cons n m u us => .cons n m (u.subst₀ (Subst₀.liftN _ σ)) (us.subst₀ σ)

end

/--
`B[t̄ / Θ]`: the term `B`, over the new variables of a telescope, in which the arguments `t̄`
are substituted for these variables, the first one first.
RFC: `\mathsf{subst}_\Theta`
-/
def Term.instantiate {Γ : Scope} :
    {ps : List Parameter} → Term k (Γ.extend ps.length) → Args k Γ ps → Term k Γ
  | [], B, .nil => B
  | _ :: ps, B, .cons t ts =>
    Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts

/-- `B[t̄ / x̄]`, for the terms `t̄` of the fields of a constructor, which do not carry the parameters
of their entries: each new variable of the scope becomes its term, when there are as many terms as
new variables, as `Term.instantiate` does for the arguments of a telescope. -/
def Term.instantiateTerms {Γ : Scope} :
    {n : Nat} → Term k (Γ.extend n) → Terms k Γ → Option (Term k Γ)
  | 0, B, .nil => some B
  | n + 1, B, .cons t ts =>
    Term.instantiateTerms (B.subst₀ (Subst₀.liftN n (Subst₀.single t))) ts
  | _, _, _ => none

/-! ## Substitutions of the Second Order -/

/-- A substitution of the second order of the scope `Δ` in the scope `Γ`, which gives each variable an
abstraction over a variable for each entry of its telescope.
A closed substitution is one in the empty scope, `Subst k [] Δ`, whose abstractions are in the empty
scope extended by their variables.
RFC: `\mathsf{closedness}_\theta` -/
abbrev Subst (k : Nat) (Γ Δ : Scope) : Type :=
  ∀ {e : Scope.Entry}, Var Δ e → Term k (Γ.extend e.params.length)

namespace Subst

/-- The substitution `θ` under a new entry. -/
def lift {Γ Δ : Scope} {e : Scope.Entry} (θ : Subst k Γ Δ) : Subst k (e :: Γ) (e :: Δ) := fun x =>
  match x with
  | .zero => Var.eta .zero
  | .succ x => (θ x).rename (Ren.liftN _ Ren.weaken)

/-- The substitution `θ` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Subst k Γ Δ → Subst k (Γ.extend n) (Δ.extend n)
  | 0, θ => θ
  | n + 1, θ => liftN n (lift θ)

end Subst

mutual

/-- The term `t` substituted by `θ`: an application `x[t̄]` becomes `B[t̄' / x̄]`, where `x̄. B` is what
`θ` gives `x`, and `t̄'` are the arguments substituted.
RFC: `\mathsf{subst}_\theta.t` -/
def Term.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : Term k Δ → Term k Γ
  | .var x ts => (θ x).instantiate (ts.subst θ)
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.subst θ)
  | .ctor D qs ls ps as c ts => .ctor D qs ls ps (as.subst θ) c (ts.subst θ)
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs ls ps (as.subst θ) (t.subst θ) (Cs.subst θ) (us.subst θ)

/-- The arguments `t̄` substituted by `θ`.
RFC: `\mathsf{subst}_\theta.\bar t` -/
def Args.subst {Γ Δ : Scope} {a : List Parameter} (θ : Subst k Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.subst θ) (ts.subst θ)

/-- The arguments `ā` substituted by `θ`, under the variables of each abstraction.
RFC: `\mathsf{subst}_\theta.\bar a` -/
def InstanceArgs.subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) :
    InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.subst θ) (B.subst (Subst.liftN _ θ))

/-- The terms `t̄` substituted by `θ`.
RFC: `\mathsf{subst}_\theta.\bar t` -/
def Terms.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : Terms k Δ → Terms k Γ
  | .nil => .nil
  | .cons t ts => .cons (t.subst θ) (ts.subst θ)

/-- The motives `C̄` substituted by `θ`, under the variables of each motive.
RFC: `\mathsf{subst}_\theta.\bar C` -/
def Motives.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : Motives k Δ → Motives k Γ
  | .nil => .nil
  | .cons n C Cs => .cons n (C.subst (Subst.liftN _ θ)) (Cs.subst θ)

/-- The branches `ū` substituted by `θ`, under the variables of each branch.
RFC: `\mathsf{subst}_\theta.\bar u` -/
def Branches.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : Branches k Δ → Branches k Γ
  | .nil => .nil
  | .cons n m u us => .cons n m (u.subst (Subst.liftN _ θ)) (us.subst θ)

end

/-- `[ā / Δ]`: the substitution that gives each parameter of `Δ` its argument in `ā`.
RFC: `\mathsf{params}_\theta` -/
def InstanceArgs.toSubst {Γ : Scope} : {Δ : Scope} → InstanceArgs k Γ Δ → Subst k Γ Δ
  | _, .snoc _ B, _, .zero => B
  | _, .snoc as _, _, .succ x => as.toSubst x

/-! ## Instantiation of the Level Variables -/

/-- `l[l̄' / l̄]`: the level `l` in which the level `ls' i` replaces the variable `i`.
RFC: `\mathsf{subst}_l` -/
def Level.subst {k k' : Nat} (ls' : Fin k → Level k') : Level k → Level k'
  | .zero => .zero
  | .succ l => .succ (l.subst ls')
  | .max l₁ l₂ => .max (l₁.subst ls') (l₂.subst ls')
  | .var i => ls' i

/-- The sort `κ` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\kappa` -/
def Universe.substLevels {k k' : Nat} (ls' : Fin k → Level k') (κ : Universe k) : Universe k' :=
  ⟨κ.quality, κ.level.subst ls'⟩

mutual

/-- `t[l̄' / l̄]`: the term `t` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.t` -/
def Term.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') : Term k Γ → Term k' Γ
  | .var x ts => .var x (ts.substLevels ls')
  | .sort κ => .sort (κ.substLevels ls')
  | .const c qs ls ps => .const c qs (ls.map (Level.subst ls')) ps
  | .inst D qs ls ps as => .inst D qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
  | .ctor D qs ls ps as c ts =>
    .ctor D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') c (ts.substLevels ls')
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') (t.substLevels ls')
      (Cs.substLevels ls') (us.substLevels ls')

/-- The arguments `t̄` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar t` -/
def Args.substLevels {k' : Nat} {Γ : Scope} {a : List Parameter} (ls' : Fin k → Level k') :
    Args k Γ a → Args k' Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.substLevels ls') (ts.substLevels ls')

/-- The arguments `ā` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar a` -/
def InstanceArgs.substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') :
    InstanceArgs k Γ Δ → InstanceArgs k' Γ Δ
  | .nil => .nil
  | .snoc as B => .snoc (as.substLevels ls') (B.substLevels ls')

/-- The terms `t̄` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar t` -/
def Terms.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') : Terms k Γ → Terms k' Γ
  | .nil => .nil
  | .cons t ts => .cons (t.substLevels ls') (ts.substLevels ls')

/-- The motives `C̄` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar C` -/
def Motives.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    Motives k Γ → Motives k' Γ
  | .nil => .nil
  | .cons n C Cs => .cons n (C.substLevels ls') (Cs.substLevels ls')

/-- The branches `ū` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar u` -/
def Branches.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    Branches k Γ → Branches k' Γ
  | .nil => .nil
  | .cons n m u us => .cons n m (u.substLevels ls') (us.substLevels ls')

end

/-! ## Telescopes and Contexts -/

/-- The telescope `Θ` renamed by `ξ`. -/
def Telescope.rename {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.rename ξ) (Θ.rename (Ren.lift ξ))

/-- `Θ[σ]`: the telescope `Θ` substituted by `σ`.
RFC: `\mathsf{subst}_\sigma.\Theta` -/
def Telescope.subst₀ {Γ Δ : Scope} {ps : List Parameter} (σ : Subst₀ k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst₀ σ) (Θ.subst₀ (Subst₀.lift σ))

/-- `Θ[θ]`: the telescope `Θ` substituted by `θ`.
RFC: `\mathsf{subst}_\theta.\Theta` -/
def Telescope.subst {Γ Δ : Scope} {ps : List Parameter} (θ : Subst k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst θ) (Θ.subst (Subst.lift θ))

/-- The telescope `Θ` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\Theta` -/
def Telescope.substLevels {k' : Nat} {Γ : Scope} {ps : List Parameter} (ls' : Fin k → Level k') :
    Telescope k Γ ps → Telescope k' Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.substLevels ls') (Θ.substLevels ls')

/-- The context `Γ` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\Gamma` -/
def Context.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    Context k Γ → Context k' Γ
  | .empty => .empty
  | .var ctx A => .var (ctx.substLevels ls') (A.substLevels ls')
  | .secondOrder ctx Θ A ψ => .secondOrder (ctx.substLevels ls')
      (Θ.substLevels ls') (A.substLevels ls') ψ

/-- `Γ, Θ`: the context `Γ` extended by the entries of the telescope `Θ`, whose grades and parameters
it ignores.
RFC: `\mathsf{append}_\Gamma` -/
def Context.append : {Γ : Scope} → {ps : List Parameter} → Context k Γ → Telescope k Γ ps →
    Context k (Γ.extend ps.length)
  | _, [], ctx, .nil => ctx
  | _, _ :: _, ctx, .cons _ _ A Θ => Context.append (Γ := .var :: _) (ctx.var A) Θ

/-- `Θ_c[T]`: the fields of the constructor `c` at the instance `I` of the sort and grade variables,
the levels `ls` and the arguments `ā` of the parameters, in the scope `Γ` of the arguments.
RFC: `\mathsf{inst}_T` -/
def Constructor.fieldsAt {j g k' : Nat} {Γ Δ : Scope} (c : Constructor j g k' Δ) (I : Instance j g)
    (ls : Fin k' → Level k) (as : InstanceArgs k Γ Δ) : Telescope k Γ (c.params I) :=
  ((c.fields I).substLevels ls).subst as.toSubst

/-- A closed term in the scope `Γ`, which it does not use. -/
def Term.weakenClosed {Γ : Scope} (t : Term k []) : Term k Γ := t.rename fun x => by cases x

/-! ## Properties

The renamings and the substitutions of the first order that give each variable itself change
nothing, under the new variables of every abstraction. -/

theorem Ren.lift_id_of {Γ : Scope} {b : Scope.Entry} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    ∀ {a} (x : Var (b :: Γ) a), Ren.lift ξ x = x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {ξ : Ren Γ Γ}, (∀ {a} (x : Var Γ a), ξ x = x) →
      ∀ {a} (x : Var (Γ.extend n) a), Ren.liftN n ξ x = x
  | 0, _, h => h
  | n + 1, _, h => Ren.liftN_id_of (Γ := .var :: Γ) n (Ren.lift_id_of h)

mutual

theorem Term.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (t : Term k Γ) → t.rename ξ = t
  | .var x ts => by rw [Term.rename, h x, Args.rename_id_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by rw [Term.rename, InstanceArgs.rename_id_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, InstanceArgs.rename_id_of h as, Terms.rename_id_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, InstanceArgs.rename_id_of h as, Term.rename_id_of h t,
      Motives.rename_id_of h Cs, Branches.rename_id_of h us]

theorem Args.rename_id_of {Γ : Scope} {a : List Parameter} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (ts : Args k Γ a) → ts.rename ξ = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.rename, Term.rename_id_of h t, Args.rename_id_of h ts]

theorem InstanceArgs.rename_id_of {Γ Ξ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (as : InstanceArgs k Γ Ξ) → as.rename ξ = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename_id_of h as,
      Term.rename_id_of (Ren.liftN_id_of _ h) B]

theorem Terms.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (ts : Terms k Γ) → ts.rename ξ = ts
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.rename_id_of h ts, Term.rename_id_of h t]

theorem Motives.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (Cs : Motives k Γ) → Cs.rename ξ = Cs
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.rename_id_of h Cs, Term.rename_id_of (Ren.liftN_id_of _ h) C]

theorem Branches.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (us : Branches k Γ) → us.rename ξ = us
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.rename, Branches.rename_id_of h us, Term.rename_id_of (Ren.liftN_id_of _ h) u]

end

/-- Renaming each variable to itself changes nothing. -/
theorem Term.rename_id {Γ : Scope} (t : Term k Γ) : t.rename (fun x => x) = t :=
  Term.rename_id_of (fun _ => rfl) t

theorem Subst₀.lift_id_of {Γ : Scope} {b : Scope.Entry} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) :
    ∀ {a} (x : Var (b :: Γ) a), Subst₀.lift σ x = .var x
  | _, .zero => rfl
  | _, .succ x => by rw [Subst₀.lift, h x]; rfl

theorem Subst₀.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Γ}, (∀ {a} (x : Var Γ a), σ x = .var x) →
      ∀ {a} (x : Var (Γ.extend n) a), Subst₀.liftN n σ x = .var x
  | 0, _, h => h
  | n + 1, _, h => Subst₀.liftN_id_of (Γ := .var :: Γ) n (Subst₀.lift_id_of h)

mutual

/-- A substitution of the first order that renames each variable to itself changes no term.
RFC: `\mathsf{id}_\sigma.t` -/
theorem Term.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ} (h : ∀ {a} (x : Var Γ a), σ x = .var x) :
    (t : Term k Γ) → t.subst₀ σ = t
  | .var x ts => by unfold Term.subst₀; simp only [h x, Args.subst₀_id_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by rw [Term.subst₀, InstanceArgs.subst₀_id_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst₀, InstanceArgs.subst₀_id_of h as, Terms.subst₀_id_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst₀, InstanceArgs.subst₀_id_of h as, Term.subst₀_id_of h t,
      Motives.subst₀_id_of h Cs, Branches.subst₀_id_of h us]

theorem Args.subst₀_id_of {Γ : Scope} {a : List Parameter} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (ts : Args k Γ a) → ts.subst₀ σ = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.subst₀, Term.subst₀_id_of h t, Args.subst₀_id_of h ts]

theorem InstanceArgs.subst₀_id_of {Γ Ξ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (as : InstanceArgs k Γ Ξ) → as.subst₀ σ = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst₀_id_of h as,
      Term.subst₀_id_of (Subst₀.liftN_id_of _ h) B]

theorem Terms.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (ts : Terms k Γ) → ts.subst₀ σ = ts
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.subst₀_id_of h ts, Term.subst₀_id_of h t]

theorem Motives.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (Cs : Motives k Γ) → Cs.subst₀ σ = Cs
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.subst₀_id_of h Cs, Term.subst₀_id_of (Subst₀.liftN_id_of _ h) C]

theorem Branches.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (us : Branches k Γ) → us.subst₀ σ = us
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst₀, Branches.subst₀_id_of h us, Term.subst₀_id_of (Subst₀.liftN_id_of _ h) u]

end

/-- The identity substitution of the first order changes nothing. -/
theorem Term.subst₀_id {Γ : Scope} (t : Term k Γ) : t.subst₀ Subst₀.id = t :=
  Term.subst₀_id_of (fun _ => rfl) t

/-- The renaming that skips `n` new variables. -/
def Ren.weakenN {Γ : Scope} (n : Nat) : Ren (Γ.extend n) Γ := fun x => x.weakenN n

/-- The value `v` substituted by `σ`. -/
def Val.subst₀ {Γ Δ : Scope} {a : Scope.Entry} (σ : Subst₀ k Γ Δ) : Val k Δ a → Val k Γ a
  | .var x => σ x
  | .term t => .term (t.subst₀ σ)

/-- The application of a value to arguments: a variable applied to them, or the term itself. -/
def Val.apply {Γ : Scope} {a : Scope.Entry} : Val k Γ a → Args k Γ a.params → Term k Γ
  | .var y, us => .var y us
  | .term t, _ => t

/-- A substitution of the first order applies to `x[t̄]` what it gives `x`. -/
theorem Term.subst₀_var {Γ Δ : Scope} {a : Scope.Entry} (σ : Subst₀ k Γ Δ) (x : Var Δ a)
    (ts : Args k Δ a.params) : (Term.var x ts).subst₀ σ = (σ x).apply (ts.subst₀ σ) := by
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

theorem Ren.lift_comp_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    ∀ {a} (x : Var (b :: Ξ) a), Ren.lift ξ₁ (Ren.lift ξ₂ x) = Ren.lift ξ₃ x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_comp_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ} {ξ₃ : Ren Γ Ξ},
      (∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Ren.liftN n ξ₁ (Ren.liftN n ξ₂ x) = Ren.liftN n ξ₃ x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Ren.liftN_comp_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Ren.lift_comp_of h)

mutual

-- ADE: `wk-comp`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `ξ₂` then by `ξ₁` is renaming by their composition `ξ₃`. -/
theorem Term.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ} {ξ₃ : Ren Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (t : Term k Ξ) → (t.rename ξ₂).rename ξ₁ = t.rename ξ₃
  | .var x ts => by rw [Term.rename, Term.rename, Term.rename, h x, Args.rename_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as,
      Terms.rename_rename_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as,
      Term.rename_rename_of h t, Motives.rename_rename_of h Cs, Branches.rename_rename_of h us]

theorem Args.rename_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (ts : Args k Ξ a) → (ts.rename ξ₂).rename ξ₁ = ts.rename ξ₃
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.rename, Args.rename, Term.rename_rename_of h t, Args.rename_rename_of h ts]

theorem InstanceArgs.rename_rename_of {Γ Δ Ξ Ψ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ξ₂).rename ξ₁ = as.rename ξ₃
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename, InstanceArgs.rename,
      InstanceArgs.rename_rename_of h as, Term.rename_rename_of (Ren.liftN_comp_of _ h) B]

theorem Terms.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (ts : Terms k Ξ) → (ts.rename ξ₂).rename ξ₁ = ts.rename ξ₃
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.rename, Terms.rename,
      Terms.rename_rename_of h ts, Term.rename_rename_of h t]

theorem Motives.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (Cs : Motives k Ξ) → (Cs.rename ξ₂).rename ξ₁ = Cs.rename ξ₃
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.rename, Motives.rename,
      Motives.rename_rename_of h Cs, Term.rename_rename_of (Ren.liftN_comp_of _ h) C]

theorem Branches.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (us : Branches k Ξ) → (us.rename ξ₂).rename ξ₁ = us.rename ξ₃
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.rename, Branches.rename, Branches.rename,
      Branches.rename_rename_of h us, Term.rename_rename_of (Ren.liftN_comp_of _ h) u]

end

/-- Renaming a value by `ξ₂` then by `ξ₁` is renaming it by their composition `ξ₃`. -/
theorem Val.rename_rename_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (v : Val k Ξ a) → (v.rename ξ₂).rename ξ₁ = v.rename ξ₃
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_rename_of h t)

/-- Renaming each variable to itself changes no value. -/
theorem Val.rename_id_of {Γ : Scope} {a : Scope.Entry} {ξ : Ren Γ Γ}
    (h : ∀ {a} (x : Var Γ a), ξ x = x) : (v : Val k Γ a) → v.rename ξ = v
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_id_of h t)

/-! ### Substitutions after Renamings -/

theorem Subst₀.lift_rename_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst₀.lift σ (Ren.lift ξ x) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (Val.rename Ren.weaken) (h x)

theorem Subst₀.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst₀.liftN n σ (Ren.liftN n ξ x) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst₀.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `ξ` then substituting by `σ` is substituting by their composition `σ'`. -/
theorem Term.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (t : Term k Ξ) → (t.rename ξ).subst₀ σ = t.subst₀ σ'
  | .var x ts => by
    rw [Term.rename, Term.subst₀_var, Term.subst₀_var, h x, Args.subst₀_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as,
      Terms.subst₀_rename_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as,
      Term.subst₀_rename_of h t, Motives.subst₀_rename_of h Cs, Branches.subst₀_rename_of h us]

theorem Args.subst₀_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (ts : Args k Ξ a) → (ts.rename ξ).subst₀ σ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst₀, Args.subst₀, Term.subst₀_rename_of h t,
      Args.subst₀_rename_of h ts]

theorem InstanceArgs.subst₀_rename_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ξ).subst₀ σ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst₀, InstanceArgs.subst₀,
      InstanceArgs.subst₀_rename_of h as, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) B]

theorem Terms.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (ts : Terms k Ξ) → (ts.rename ξ).subst₀ σ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst₀, Terms.subst₀,
      Terms.subst₀_rename_of h ts, Term.subst₀_rename_of h t]

theorem Motives.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (Cs : Motives k Ξ) → (Cs.rename ξ).subst₀ σ = Cs.subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst₀, Motives.subst₀,
      Motives.subst₀_rename_of h Cs, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) C]

theorem Branches.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (us : Branches k Ξ) → (us.rename ξ).subst₀ σ = us.subst₀ σ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.rename, Branches.subst₀, Branches.subst₀,
      Branches.subst₀_rename_of h us, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) u]

end

/-- Renaming a value by `ξ` then substituting it by `σ` is substituting it by their composition
`σ'`. -/
theorem Val.subst₀_rename_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (v : Val k Ξ a) → (v.rename ξ).subst₀ σ = v.subst₀ σ'
  | .var x => h x
  | .term t => congrArg Val.term (Term.subst₀_rename_of h t)

/-! ### Renamings after Substitutions -/

theorem Subst₀.lift_rename_after_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {σ : Subst₀ k Δ Ξ}
    {ξ : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), (Subst₀.lift σ x).rename (Ren.lift ξ) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ x).rename Ren.weaken).rename (Ren.lift ξ) = (σ' x).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := ξ) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ x).rename (Ren.liftN n ξ) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_after_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) n (Subst₀.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`.
/-- Substituting by `σ` then renaming by `ξ` is substituting by their composition `σ'`. -/
theorem Term.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (t : Term k Ξ) → (t.subst₀ σ).rename ξ = t.subst₀ σ'
  | .var x ts => by
    rw [Term.subst₀_var, Term.subst₀_var, ← h x, ← Args.rename_subst₀_of h ts]
    cases σ x <;> rfl
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as,
      Terms.rename_subst₀_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as,
      Term.rename_subst₀_of h t, Motives.rename_subst₀_of h Cs, Branches.rename_subst₀_of h us]

theorem Args.rename_subst₀_of {Γ Δ Ξ : Scope} {a : List Parameter} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (ts : Args k Ξ a) → (ts.subst₀ σ).rename ξ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.rename, Args.subst₀, Term.rename_subst₀_of h t,
      Args.rename_subst₀_of h ts]

theorem InstanceArgs.rename_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst₀ σ).rename ξ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.rename, InstanceArgs.subst₀,
      InstanceArgs.rename_subst₀_of h as,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) B]

theorem Terms.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (ts : Terms k Ξ) → (ts.subst₀ σ).rename ξ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.rename, Terms.subst₀,
      Terms.rename_subst₀_of h ts,
      Term.rename_subst₀_of h t]

theorem Motives.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (Cs : Motives k Ξ) → (Cs.subst₀ σ).rename ξ = Cs.subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.rename, Motives.subst₀,
      Motives.rename_subst₀_of h Cs,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) C]

theorem Branches.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (us : Branches k Ξ) → (us.subst₀ σ).rename ξ = us.subst₀ σ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst₀, Branches.rename, Branches.subst₀,
      Branches.rename_subst₀_of h us,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) u]

end

/-- Substituting a value by `σ` then renaming it by `ξ` is substituting it by their composition
`σ'`. -/
theorem Val.rename_subst₀_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (v : Val k Ξ a) → (v.subst₀ σ).rename ξ = v.subst₀ σ'
  | .var x => h x
  | .term t => congrArg Val.term (Term.rename_subst₀_of h t)

/-- A value under a new entry, substituted under it, is the value substituted, under the entry. -/
theorem Val.rename_weaken_subst₀_lift {Γ Δ : Scope} {a b : Scope.Entry} (σ : Subst₀ k Γ Δ)
    (v : Val k Δ a) :
    (v.rename Ren.weaken).subst₀ (Subst₀.lift (e := b) σ) = (v.subst₀ σ).rename Ren.weaken :=
  (Val.subst₀_rename_of (fun _ => rfl) v).trans (Val.rename_subst₀_of (fun _ => rfl) v).symm

/-! ### Substitutions after Substitutions -/

theorem Subst₀.lift_subst₀_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {σ : Subst₀ k Δ Ξ}
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
  | n + 1, _, _, _, h => Subst₀.liftN_subst₀_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst₀.lift_subst₀_of h)

mutual

-- ADE: `substCompEq`, in `Definition/Untyped/Properties.agda`.
/-- Substituting by `σ` then by `τ` is substituting by their composition `σ'`.
RFC: `\mathsf{comp}_\sigma` -/
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
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst₀, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_subst₀_of h as,
      Terms.subst₀_subst₀_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst₀, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_subst₀_of h as,
      Term.subst₀_subst₀_of h t, Motives.subst₀_subst₀_of h Cs, Branches.subst₀_subst₀_of h us]

theorem Args.subst₀_subst₀_of {Γ Δ Ξ : Scope} {a : List Parameter} {σ : Subst₀ k Δ Ξ}
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

theorem Terms.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (ts : Terms k Ξ) → (ts.subst₀ σ).subst₀ τ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.subst₀, Terms.subst₀,
      Terms.subst₀_subst₀_of h ts, Term.subst₀_subst₀_of h t]

theorem Motives.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (Cs : Motives k Ξ) → (Cs.subst₀ σ).subst₀ τ = Cs.subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.subst₀, Motives.subst₀,
      Motives.subst₀_subst₀_of h Cs, Term.subst₀_subst₀_of (Subst₀.liftN_subst₀_of _ h) C]

theorem Branches.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (us : Branches k Ξ) → (us.subst₀ σ).subst₀ τ = us.subst₀ σ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst₀, Branches.subst₀, Branches.subst₀,
      Branches.subst₀_subst₀_of h us, Term.subst₀_subst₀_of (Subst₀.liftN_subst₀_of _ h) u]

end

/-! ### Weakenings and New Variables -/

/-- A renaming under new variables renames an old variable as it does without them. -/
theorem Ren.liftN_weakenN {Γ Δ : Scope} {a : Scope.Entry} :
    ∀ (n : Nat) (ξ : Ren Γ Δ) (x : Var Δ a), Ren.liftN n ξ (x.weakenN n) = (ξ x).weakenN n
  | 0, _, _ => rfl
  | n + 1, ξ, x => Ren.liftN_weakenN (Γ := .var :: Γ) (Δ := .var :: Δ) n (Ren.lift ξ) x.succ

/-- A substitution under new variables gives an old variable what it gives it without them,
under them. -/
theorem Subst₀.liftN_weakenN {Γ Δ : Scope} {a : Scope.Entry} :
    ∀ (n : Nat) (σ : Subst₀ k Γ Δ) (x : Var Δ a),
      Subst₀.liftN n σ (x.weakenN n) = (σ x).rename (Ren.weakenN n)
  | 0, σ, x => (Val.rename_id_of (fun _ => rfl) (σ x)).symm
  | n + 1, σ, x => by
    rw [Var.weakenN, Subst₀.liftN, Subst₀.liftN_weakenN (Γ := .var :: Γ) (Δ := .var :: Δ) n]
    exact Val.rename_rename_of (fun _ => rfl) (σ x)

/-- A renaming under the new variables keeps them. -/
theorem Args.bound_rename {Γ Δ : Scope} :
    ∀ (ps : List Parameter) (ξ : Ren Γ Δ),
      (Args.bound (k := k) (Γ := Δ) ps).rename (Ren.liftN ps.length ξ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, ξ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).rename (Ren.liftN ps.length (Ren.lift ξ)))
        ((Args.bound (Γ := .var :: Δ) ps).rename (Ren.liftN ps.length (Ren.lift ξ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := .var :: Γ) ps)
    rw [Args.bound_rename ps (Ren.lift ξ), Term.rename, Ren.liftN_weakenN]
    rfl

/-- A substitution of the first order under the new variables keeps them. -/
theorem Args.bound_subst₀ {Γ Δ : Scope} :
    ∀ (ps : List Parameter) (σ : Subst₀ k Γ Δ),
      (Args.bound (Γ := Δ) ps).subst₀ (Subst₀.liftN ps.length σ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, σ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst₀
          (Subst₀.liftN ps.length (Subst₀.lift σ)))
        ((Args.bound (Γ := .var :: Δ) ps).subst₀ (Subst₀.liftN ps.length (Subst₀.lift σ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := .var :: Γ) ps)
    rw [Args.bound_subst₀ ps (Subst₀.lift σ), Term.subst₀_var, Subst₀.liftN_weakenN]
    rfl

/-- Substituting each variable by itself changes no value. -/
theorem Val.subst₀_id_of {Γ : Scope} {a : Scope.Entry} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (v : Val k Γ a) → v.subst₀ σ = v
  | .var x => h x
  | .term t => congrArg Val.term (Term.subst₀_id_of h t)

-- ADE: `substVar-to-subst`, in `Definition/Untyped/Properties.agda`.
/-- Substitutions of the first order that agree on every variable agree on every term. -/
theorem Term.subst₀_congr {Γ Δ : Scope} {σ σ' : Subst₀ k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), σ x = σ' x) (t : Term k Δ) : t.subst₀ σ = t.subst₀ σ' :=
  by rw [← Term.subst₀_rename_of (ξ := fun x => x) h t, Term.rename_id]

/-! ### Instantiation -/

/-- The substitution of the first order that `B[t̄ / Θ]` applies at once: each new variable of the
scope becomes its argument. -/
def Args.toSubst₀ {Γ : Scope} : {ps : List Parameter} → Args k Γ ps → Subst₀ k Γ (Γ.extend ps.length)
  | [], .nil => Subst₀.id
  | _ :: ps, .cons t ts => fun x => (Subst₀.liftN ps.length (Subst₀.single t) x).subst₀ ts.toSubst₀

/-- `B[t̄ / Θ]` is the substitution `Args.toSubst₀`. -/
theorem Term.instantiate_eq_subst₀ {Γ : Scope} :
    {ps : List Parameter} → (B : Term k (Γ.extend ps.length)) → (ts : Args k Γ ps) →
      B.instantiate ts = B.subst₀ ts.toSubst₀
  | [], B, .nil => (Term.subst₀_id B).symm
  | _ :: _, B, .cons _ ts =>
    (Term.instantiate_eq_subst₀ _ ts).trans (Term.subst₀_subst₀_of (fun _ => rfl) B)

/-- `Args.toSubst₀` keeps the old variables. -/
theorem Args.toSubst₀_weakenN {Γ : Scope} {a : Scope.Entry} :
    {ps : List Parameter} → (ts : Args k Γ ps) → (y : Var Γ a) →
      ts.toSubst₀ (y.weakenN ps.length) = .var y
  | [], .nil, _ => rfl
  | _ :: ps, .cons t ts, y => by
    show (Subst₀.liftN ps.length (Subst₀.single t) (y.succ.weakenN ps.length)).subst₀ ts.toSubst₀ = _
    rw [Subst₀.liftN_weakenN]
    exact Args.toSubst₀_weakenN ts y

/-- `Args.toSubst₀ t̄` gives the new variables the arguments `t̄`. -/
theorem Args.bound_toSubst₀ {Γ : Scope} :
    {ps : List Parameter} → (ts : Args k Γ ps) → (Args.bound ps).subst₀ ts.toSubst₀ = ts
  | [], .nil => rfl
  | _ :: ps, .cons t ts => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst₀ (Args.toSubst₀ (.cons t ts)))
        ((Args.bound (Γ := .var :: Γ) ps).subst₀ fun x =>
          (Subst₀.liftN ps.length (Subst₀.single t) x).subst₀ ts.toSubst₀) = _
    rw [← Args.subst₀_subst₀_of (fun _ => rfl), Args.bound_subst₀, Args.bound_toSubst₀ ts]
    erw [Term.subst₀_var]
    show Args.cons ((Val.subst₀ ts.toSubst₀
        (Subst₀.liftN ps.length (Subst₀.single t) (Var.weakenN ps.length .zero))).apply _) ts = _
    rw [Subst₀.liftN_weakenN]
    show Args.cons ((t.rename (Ren.weakenN ps.length)).subst₀ ts.toSubst₀) ts = _
    rw [Term.subst₀_rename_of (ξ := Ren.weakenN ps.length) (σ' := Subst₀.id)
      (Args.toSubst₀_weakenN ts), Term.subst₀_id]

/-- `(x̄. x[x̄])[t̄ / x̄] = x[t̄]`. -/
theorem Var.eta_instantiate {Γ : Scope} {e : Scope.Entry} (x : Var Γ e) (ts : Args k Γ e.params) :
    (Var.eta x).instantiate ts = .var x ts := by
  rw [Term.instantiate_eq_subst₀, Var.eta, Term.subst₀_var, Args.toSubst₀_weakenN,
    Args.bound_toSubst₀]
  rfl

theorem Subst₀.lift_comm_of {Γ Δ Ξ Ψ : Scope} {b : Scope.Entry} {σ₁ : Subst₀ k Δ Ξ}
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
  | n + 1, _, _, _, _, h => Subst₀.liftN_comm_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ)
      (Ψ := .var :: Ψ) n (Subst₀.lift_comm_of h)

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
    ∀ {a} (x : Var (.var :: Δ) a),
      (Subst₀.single t x).subst₀ σ = (Subst₀.lift σ x).subst₀ (Subst₀.single (t.subst₀ σ))
  | _, .zero => rfl
  | _, .succ x => by
    show σ x = ((σ x).rename Ren.weaken).subst₀ _
    rw [Val.subst₀_rename_of (σ := Subst₀.single (t.subst₀ σ)) (ξ := Ren.weaken) (σ' := Subst₀.id)
      (fun _ => rfl), Val.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl)]

-- ADE: `singleSubstLift`, in `Definition/Untyped/Properties.agda`.
/-- `B[t̄ / x̄][σ] = B[σ⇑][t̄[σ] / x̄]`.
RFC: `\mathsf{inst}_\sigma` -/
theorem Term.instantiate_subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) :
    {ps : List Parameter} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).subst₀ σ = (B.subst₀ (Subst₀.liftN ps.length σ)).instantiate (ts.subst₀ σ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).subst₀ σ =
      Term.instantiate ((B.subst₀ (Subst₀.liftN ps.length (Subst₀.lift σ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.subst₀ σ)))) (ts.subst₀ σ)
    rw [Term.instantiate_subst₀ σ]
    congr 1
    exact Term.subst₀_comm_of (Subst₀.liftN_comm_of ps.length (Subst₀.single_comm t σ)) B

theorem Subst₀.lift_rename_comm_of {Γ Δ Ξ Ψ : Scope} {b : Scope.Entry} {σ₁ : Subst₀ k Δ Ξ}
    {ξ₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {ξ₂ : Ren Ψ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename ξ₁ = σ₂ (ξ₂ x)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst₀.lift σ₁ x).rename (Ren.lift ξ₁) = Subst₀.lift σ₂ (Ren.lift ξ₂ x)
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ₁ x).rename Ren.weaken).rename (Ren.lift ξ₁) = (σ₂ (ξ₂ x)).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (ξ₁ := Ren.lift ξ₁) (ξ₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := ξ₁) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₁ : Subst₀ k Δ Ξ} {ξ₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {ξ₂ : Ren Ψ Ξ},
      (∀ {a} (x : Var Ξ a), (σ₁ x).rename ξ₁ = σ₂ (ξ₂ x)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ₁ x).rename (Ren.liftN n ξ₁) = Subst₀.liftN n σ₂ (Ren.liftN n ξ₂ x)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.liftN_rename_comm_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) (Ψ := .var :: Ψ) n (Subst₀.lift_rename_comm_of h)

-- ADE: `wk-β`, in `Definition/Untyped/Properties.agda`.
/-- `B[t̄ / x̄][ξ] = B[ξ⇑][t̄[ξ] / x̄]`. -/
theorem Term.instantiate_rename {Γ Δ : Scope} (ξ : Ren Γ Δ) :
    {ps : List Parameter} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).rename ξ = (B.rename (Ren.liftN ps.length ξ)).instantiate (ts.rename ξ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).rename ξ =
      Term.instantiate ((B.rename (Ren.liftN ps.length (Ren.lift ξ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.rename ξ)))) (ts.rename ξ)
    rw [Term.instantiate_rename ξ]
    congr 1
    exact (Term.rename_subst₀_of (fun _ => rfl) B).trans ((Term.subst₀_congr
      (Subst₀.liftN_rename_comm_of ps.length (σ₂ := Subst₀.single (t.rename ξ)) (ξ₂ := Ren.lift ξ)
        fun x => by cases x <;> rfl) B).trans (Term.subst₀_rename_of (fun _ => rfl) B).symm)

/-! ### Substitutions of the Second Order after Renamings -/

theorem Subst.lift_rename_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst.lift θ (Ren.lift ξ x) = Subst.lift θ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (fun t => Term.rename (Ren.liftN _ Ren.weaken) t) (h x)

theorem Subst.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ} {θ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst.liftN n θ (Ren.liftN n ξ x) = Subst.liftN n θ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Renaming by `ξ` then substituting by `θ` is substituting by their composition `θ'`. -/
theorem Term.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (t : Term k Ξ) → (t.rename ξ).subst θ = t.subst θ'
  | .var x ts => by rw [Term.rename, Term.subst, Term.subst, h x, Args.subst_rename_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as,
      Terms.subst_rename_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as,
      Term.subst_rename_of h t, Motives.subst_rename_of h Cs, Branches.subst_rename_of h us]

theorem Args.subst_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (ts : Args k Ξ a) → (ts.rename ξ).subst θ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst, Args.subst, Term.subst_rename_of h t, Args.subst_rename_of h ts]

theorem InstanceArgs.subst_rename_of {Γ Δ Ξ Ψ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename ξ).subst θ = as.subst θ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.subst_rename_of h as, Term.subst_rename_of (Subst.liftN_rename_of _ h) B]

theorem Terms.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (ts : Terms k Ξ) → (ts.rename ξ).subst θ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst, Terms.subst,
      Terms.subst_rename_of h ts, Term.subst_rename_of h t]

theorem Motives.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (Cs : Motives k Ξ) → (Cs.rename ξ).subst θ = Cs.subst θ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst, Motives.subst,
      Motives.subst_rename_of h Cs, Term.subst_rename_of (Subst.liftN_rename_of _ h) C]

theorem Branches.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (us : Branches k Ξ) → (us.rename ξ).subst θ = us.subst θ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.rename, Branches.subst, Branches.subst,
      Branches.subst_rename_of h us, Term.subst_rename_of (Subst.liftN_rename_of _ h) u]

end

/-! ### Renamings after Substitutions of the Second Order -/

/-- `(x̄. x[x̄])[ξ] = x̄. ξ(x)[x̄]`. -/
theorem Var.eta_rename {Γ Δ : Scope} {e : Scope.Entry} (ξ : Ren Γ Δ) (x : Var Δ e) :
    (Var.eta (k := k) x).rename (Ren.liftN e.params.length ξ) = Var.eta (ξ x) := by
  rw [Var.eta, Term.rename, Ren.liftN_weakenN, Args.bound_rename]
  rfl

theorem Subst.lift_rename_after_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {θ : Subst k Δ Ξ}
    {ξ : Ren Γ Δ} {θ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst.lift θ x).rename (Ren.liftN a.params.length (Ren.lift ξ)) = Subst.lift θ' x
  | _, .zero => Var.eta_rename _ _
  | a, .succ x => by
    show ((θ x).rename (Ren.liftN a.params.length Ren.weaken)).rename (Ren.liftN a.params.length (Ren.lift ξ)) =
      (θ' x).rename (Ren.liftN a.params.length Ren.weaken)
    rw [← h x, Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
        (ξ₃ := fun y => (ξ y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.weaken) (ξ₂ := ξ)
        (ξ₃ := fun y => (ξ y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ} {θ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst.liftN n θ x).rename (Ren.liftN a.params.length (Ren.liftN n ξ)) = Subst.liftN n θ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_after_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) n (Subst.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substituting by `θ` then renaming by `ξ` is substituting by their composition `θ'`, which renames
each abstraction under its variables. -/
theorem Term.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (t : Term k Ξ) → (t.subst θ).rename ξ = t.subst θ'
  | .var x ts => by
    rw [Term.subst, Term.subst, Term.instantiate_rename, h x, Args.rename_subst_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as,
      Terms.rename_subst_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as,
      Term.rename_subst_of h t, Motives.rename_subst_of h Cs, Branches.rename_subst_of h us]

theorem Args.rename_subst_of {Γ Δ Ξ : Scope} {a : List Parameter} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (ts : Args k Ξ a) → (ts.subst θ).rename ξ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.rename, Args.subst, Term.rename_subst_of h t, Args.rename_subst_of h ts]

theorem InstanceArgs.rename_subst_of {Γ Δ Ξ Ψ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst θ).rename ξ = as.subst θ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.rename, InstanceArgs.subst,
      InstanceArgs.rename_subst_of h as, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) B]

theorem Terms.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (ts : Terms k Ξ) → (ts.subst θ).rename ξ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst, Terms.rename, Terms.subst,
      Terms.rename_subst_of h ts, Term.rename_subst_of h t]

theorem Motives.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (Cs : Motives k Ξ) → (Cs.subst θ).rename ξ = Cs.subst θ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst, Motives.rename, Motives.subst,
      Motives.rename_subst_of h Cs, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) C]

theorem Branches.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (us : Branches k Ξ) → (us.subst θ).rename ξ = us.subst θ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst, Branches.rename, Branches.subst,
      Branches.rename_subst_of h us, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) u]

end

/-! ### Substitutions of the Second Order after Substitutions of the First Order -/

/-- Substituting by `σ` then by `θ₁` is substituting by `θ₂` then by `σ'`, variable by variable:
a variable that `σ` renames to `y` becomes `θ₁ y` either way, and a variable that `σ` replaces by
`u` becomes `u[θ₁]`. -/
def Subst₀.Swaps {Γ Δ Ξ Ψ : Scope} (σ : Subst₀ k Δ Ξ) (θ₁ : Subst k Γ Δ) (θ₂ : Subst k Ψ Ξ)
    (σ' : Subst₀ k Γ Ψ) : Prop :=
  (∀ {a} (x : Var Ξ a) (y : Var Δ a), σ x = .var y →
    (θ₂ x).subst₀ (Subst₀.liftN a.params.length σ') = θ₁ y) ∧
  ∀ (x : Var Ξ .var) (u : Term k Δ), σ x = .term u → (θ₂ x).subst₀ σ' = u.subst θ₁

/-- `(x̄. x[x̄])[σ⇑] = x̄. y[x̄]`, when `σ` renames `x` to `y`. -/
theorem Var.eta_subst₀_of {Γ Δ : Scope} {e : Scope.Entry} {σ : Subst₀ k Γ Δ} {x : Var Δ e}
    {y : Var Γ e} (h : σ x = .var y) :
    (Var.eta (k := k) x).subst₀ (Subst₀.liftN e.params.length σ) = Var.eta y := by
  rw [Var.eta, Term.subst₀_var, Subst₀.liftN_weakenN, h, Args.bound_subst₀]
  rfl

/-- A term under a new entry, substituted under it, is the term substituted, under the entry. -/
theorem Term.rename_weaken_subst₀_lift {Γ Δ : Scope} {b : Scope.Entry} (σ : Subst₀ k Γ Δ)
    (t : Term k Δ) :
    (t.rename Ren.weaken).subst₀ (Subst₀.lift (e := b) σ) = (t.subst₀ σ).rename Ren.weaken :=
  (Term.subst₀_rename_of (fun _ => rfl) t).trans (Term.rename_subst₀_of (fun _ => rfl) t).symm

theorem Subst₀.Swaps.lift {Γ Δ Ξ Ψ : Scope} {b : Scope.Entry} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    Subst₀.Swaps (Subst₀.lift (e := b) σ) (Subst.lift θ₁) (Subst.lift θ₂) (Subst₀.lift σ') := by
  refine ⟨fun x y e => ?_, fun x u e => ?_⟩
  · cases x with
    | zero =>
      cases e
      exact Var.eta_subst₀_of rfl
    | succ x =>
      change (σ x).rename Ren.weaken = _ at e
      generalize e₀ : σ x = v at e
      cases v with
      | term => cases e
      | var y' =>
        cases e
        show ((θ₂ x).rename (Ren.liftN _ Ren.weaken)).subst₀ _ =
          (θ₁ y').rename (Ren.liftN _ Ren.weaken)
        refine Eq.trans ?_ (congrArg (Term.rename (Ren.liftN _ Ren.weaken)) (h.1 x y' e₀))
        exact (Term.subst₀_rename_of (fun _ => rfl) _).trans ((Term.subst₀_congr
          (fun z => (Subst₀.liftN_rename_comm_of _ (fun _ => rfl) z).symm) _).trans
          (Term.rename_subst₀_of (fun _ => rfl) _).symm)
  · cases x with
    | zero => cases e
    | succ x =>
      change (σ x).rename Ren.weaken = _ at e
      generalize e₀ : σ x = v at e
      cases v with
      | var => cases e
      | term u' =>
        cases e
        show ((θ₂ x).rename Ren.weaken).subst₀ (Subst₀.lift σ') = (u'.rename Ren.weaken).subst _
        exact (Term.rename_weaken_subst₀_lift σ' (θ₂ x)).trans
          ((congrArg (Term.rename Ren.weaken) (h.2 x u' e₀)).trans
            ((Term.rename_subst_of (fun _ => rfl) u').trans (Term.subst_rename_of (θ := Subst.lift (e := b) θ₁) (ξ := Ren.weaken)
              (θ' := fun x => (θ₁ x).rename (Ren.liftN _ Ren.weaken)) (fun _ => rfl) u').symm))

theorem Subst₀.Swaps.liftN {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ},
      Subst₀.Swaps σ θ₁ θ₂ σ' →
      Subst₀.Swaps (Subst₀.liftN n σ) (Subst.liftN n θ₁) (Subst.liftN n θ₂) (Subst₀.liftN n σ')
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.Swaps.liftN (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ)
      (Ψ := .var :: Ψ) n h.lift

mutual

/-- A substitution of the first order then one of the second order swap, as `Subst₀.Swaps` says. -/
theorem Term.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ}
    {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (t : Term k Ξ) → (t.subst₀ σ).subst θ₁ = (t.subst θ₂).subst₀ σ'
  | .var x ts => by
    rw [Term.subst₀_var, Term.subst, Term.instantiate_subst₀, ← Args.subst_subst₀_of h ts]
    generalize e : σ x = v
    cases v with
    | var y => rw [h.1 x y e]; rfl
    | term u => cases ts; exact (h.2 x u e).symm
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as,
      Terms.subst_subst₀_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as,
      Term.subst_subst₀_of h t, Motives.subst_subst₀_of h Cs, Branches.subst_subst₀_of h us]

theorem Args.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {a : List Parameter} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (ts : Args k Ξ a) → (ts.subst₀ σ).subst θ₁ = (ts.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.subst, Args.subst, Args.subst₀, Term.subst_subst₀_of h t,
      Args.subst_subst₀_of h ts]

theorem InstanceArgs.subst_subst₀_of {Γ Δ Ξ Ψ Φ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (as : InstanceArgs k Ξ Φ) → (as.subst₀ σ).subst θ₁ = (as.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst₀,
      InstanceArgs.subst_subst₀_of h as, Term.subst_subst₀_of (Subst₀.Swaps.liftN _ h) B]

theorem Terms.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (ts : Terms k Ξ) → (ts.subst₀ σ).subst θ₁ = (ts.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.subst, Terms.subst, Terms.subst₀,
      Terms.subst_subst₀_of h ts, Term.subst_subst₀_of h t]

theorem Motives.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (Cs : Motives k Ξ) → (Cs.subst₀ σ).subst θ₁ = (Cs.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.subst, Motives.subst, Motives.subst₀,
      Motives.subst_subst₀_of h Cs, Term.subst_subst₀_of (Subst₀.Swaps.liftN _ h) C]

theorem Branches.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (us : Branches k Ξ) → (us.subst₀ σ).subst θ₁ = (us.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst₀, Branches.subst, Branches.subst, Branches.subst₀,
      Branches.subst_subst₀_of h us, Term.subst_subst₀_of (Subst₀.Swaps.liftN _ h) u]

end

/-- The substitution of an argument swaps with a substitution of the second order. -/
theorem Subst₀.Swaps.single {Γ Δ : Scope} (t : Term k Δ) (θ : Subst k Γ Δ) :
    Subst₀.Swaps (Subst₀.single t) θ (Subst.lift θ) (Subst₀.single (t.subst θ)) := by
  refine ⟨fun x y e => ?_, fun x u e => ?_⟩
  · cases x with
    | zero => cases e
    | succ x =>
      cases e
      exact (Term.subst₀_rename_of (σ := Subst₀.liftN _ (Subst₀.single (t.subst θ)))
        (ξ := Ren.liftN _ Ren.weaken) (σ' := Subst₀.liftN _ Subst₀.id)
        (Subst₀.liftN_rename_of _ fun _ => rfl) _).trans
        (Term.subst₀_id_of (Subst₀.liftN_id_of _ fun _ => rfl) _)
  · cases x with
    | zero => cases e; rfl
    | succ x => cases e

-- ADE: `singleSubstLift`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- `B[t̄ / x̄][θ] = B[θ⇑][t̄[θ] / x̄]`, for a substitution of the second order.
RFC: `\mathsf{inst}_\theta` -/
theorem Term.instantiate_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {ps : List Parameter} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).subst θ = (B.subst (Subst.liftN ps.length θ)).instantiate (ts.subst θ)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).subst θ =
      Term.instantiate ((B.subst (Subst.liftN ps.length (Subst.lift θ))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.subst θ)))) (ts.subst θ)
    rw [Term.instantiate_subst θ]
    congr 1
    exact Term.subst_subst₀_of (Subst₀.Swaps.liftN _ (Subst₀.Swaps.single t θ)) B

/-! ### Substitutions of the Second Order after Substitutions of the Second Order -/

-- ADE: `substVar-to-subst`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substitutions of the second order that agree on every variable agree on every term. -/
theorem Term.subst_congr {Γ Δ : Scope} {θ θ' : Subst k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), θ x = θ' x) (t : Term k Δ) : t.subst θ = t.subst θ' := by
  rw [← Term.subst_rename_of (ξ := fun x => x) h t, Term.rename_id]

/-- A substitution of the second order under new variables gives an old variable what it gives it
without them, under them. -/
theorem Subst.liftN_weakenN {Γ Δ : Scope} {a : Scope.Entry} :
    ∀ (n : Nat) (θ : Subst k Γ Δ) (x : Var Δ a),
      Subst.liftN n θ (x.weakenN n) = (θ x).rename (Ren.liftN a.params.length (Ren.weakenN n))
  | 0, θ, x => (Term.rename_id_of (Ren.liftN_id_of _ fun _ => rfl) (θ x)).symm
  | n + 1, θ, x => by
    show Subst.liftN n (Subst.lift θ) (x.succ.weakenN n) = _
    rw [Subst.liftN_weakenN (Γ := .var :: Γ) (Δ := .var :: Δ) n]
    exact Term.rename_rename_of (Ren.liftN_comp_of _ fun _ => rfl) (θ x)

/-- A substitution of the second order under the new variables keeps them. -/
theorem Args.bound_subst {Γ Δ : Scope} :
    ∀ (ps : List Parameter) (θ : Subst k Γ Δ),
      (Args.bound (Γ := Δ) ps).subst (Subst.liftN ps.length θ) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, θ => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst
          (Subst.liftN ps.length (Subst.lift θ)))
        ((Args.bound (Γ := .var :: Δ) ps).subst (Subst.liftN ps.length (Subst.lift θ))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := .var :: Γ) ps)
    rw [Args.bound_subst ps (Subst.lift θ), Term.subst, Subst.liftN_weakenN]
    rfl

/-- `(x̄. X[x̄])[θ⇑⇑]`, for the last variable `X`, is itself. -/
theorem Var.eta_subst_lift {Γ Δ : Scope} {e : Scope.Entry} (θ : Subst k Γ Δ) :
    (Var.eta (k := k) (.zero : Var (e :: Δ) e)).subst (Subst.liftN e.params.length (Subst.lift θ)) =
      Var.eta .zero := by
  rw [Var.eta, Term.subst, Subst.liftN_weakenN, Args.bound_subst]
  show ((Var.eta .zero).rename (Ren.liftN e.params.length (Ren.weakenN e.params.length))).instantiate _ = _
  rw [Var.eta_rename, Var.eta_instantiate]
  rfl

theorem Subst.lift_rename_comm_of {Γ Δ Ξ Ψ : Scope} {b : Scope.Entry} {θ₁ : Subst k Γ Δ}
    {ξ₁ : Ren Δ Ξ} {θ₂ : Subst k Ψ Ξ} {ξ₂ : Ren Γ Ψ}
    (h : ∀ {a} (x : Var Ξ a), θ₁ (ξ₁ x) = (θ₂ x).rename (Ren.liftN a.params.length ξ₂)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      Subst.lift θ₁ (Ren.lift ξ₁ x) = (Subst.lift θ₂ x).rename (Ren.liftN a.params.length (Ren.lift ξ₂))
  | _, .zero => (Var.eta_rename (Ren.lift ξ₂) .zero).symm
  | a, .succ x => by
    show (θ₁ (ξ₁ x)).rename (Ren.liftN a.params.length Ren.weaken) =
      ((θ₂ x).rename (Ren.liftN a.params.length Ren.weaken)).rename (Ren.liftN a.params.length (Ren.lift ξ₂))
    rw [h x, Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.weaken) (ξ₂ := ξ₂)
        (ξ₃ := fun y => (ξ₂ y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (ξ₁ := Ren.lift ξ₂) (ξ₂ := Ren.weaken)
        (ξ₃ := fun y => (ξ₂ y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {θ₁ : Subst k Γ Δ} {ξ₁ : Ren Δ Ξ} {θ₂ : Subst k Ψ Ξ} {ξ₂ : Ren Γ Ψ},
      (∀ {a} (x : Var Ξ a), θ₁ (ξ₁ x) = (θ₂ x).rename (Ren.liftN a.params.length ξ₂)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        Subst.liftN n θ₁ (Ren.liftN n ξ₁ x) =
          (Subst.liftN n θ₂ x).rename (Ren.liftN a.params.length (Ren.liftN n ξ₂))
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst.liftN_rename_comm_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) (Ψ := .var :: Ψ) n (Subst.lift_rename_comm_of h)

theorem Subst.lift_subst_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst.lift θ₁ x).subst (Subst.liftN a.params.length (Subst.lift θ₂)) = Subst.lift θ₃ x
  | _, .zero => Var.eta_subst_lift θ₂
  | a, .succ x => by
    show ((θ₁ x).rename (Ren.liftN a.params.length Ren.weaken)).subst _ =
      (θ₃ x).rename (Ren.liftN a.params.length Ren.weaken)
    rw [← h x]
    exact (Term.subst_rename_of (fun _ => rfl) _).trans ((Term.subst_congr
      (Subst.liftN_rename_comm_of _ (θ₂ := θ₂) (ξ₂ := Ren.weaken) fun _ => rfl) _).trans
      (Term.rename_subst_of (fun _ => rfl) _).symm)

theorem Subst.liftN_subst_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ} {θ₃ : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst.liftN n θ₁ x).subst (Subst.liftN a.params.length (Subst.liftN n θ₂)) = Subst.liftN n θ₃ x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_subst_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst.lift_subst_of h)

mutual

-- ADE: `substCompEq`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substituting by `θ₁` then by `θ₂` is substituting by their composition `θ₃`, which substitutes
each abstraction under its variables.
RFC: `\mathsf{comp}_\theta.t` -/
theorem Term.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (t : Term k Ξ) → (t.subst θ₁).subst θ₂ = t.subst θ₃
  | .var x ts => by
    rw [Term.subst, Term.subst, Term.instantiate_subst, h x, Args.subst_subst_of h ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as,
      Terms.subst_subst_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as,
      Term.subst_subst_of h t, Motives.subst_subst_of h Cs, Branches.subst_subst_of h us]

theorem Args.subst_subst_of {Γ Δ Ξ : Scope} {a : List Parameter} {θ₁ : Subst k Δ Ξ}
    {θ₂ : Subst k Γ Δ} {θ₃ : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (ts : Args k Ξ a) → (ts.subst θ₁).subst θ₂ = ts.subst θ₃
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.subst, Args.subst, Term.subst_subst_of h t, Args.subst_subst_of h ts]

theorem InstanceArgs.subst_subst_of {Γ Δ Ξ Ψ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst θ₁).subst θ₂ = as.subst θ₃
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.subst_subst_of h as, Term.subst_subst_of (Subst.liftN_subst_of _ h) B]

theorem Terms.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (ts : Terms k Ξ) → (ts.subst θ₁).subst θ₂ = ts.subst θ₃
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst, Terms.subst, Terms.subst,
      Terms.subst_subst_of h ts, Term.subst_subst_of h t]

theorem Motives.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (Cs : Motives k Ξ) → (Cs.subst θ₁).subst θ₂ = Cs.subst θ₃
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst, Motives.subst, Motives.subst,
      Motives.subst_subst_of h Cs, Term.subst_subst_of (Subst.liftN_subst_of _ h) C]

theorem Branches.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (us : Branches k Ξ) → (us.subst θ₁).subst θ₂ = us.subst θ₃
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst, Branches.subst, Branches.subst,
      Branches.subst_subst_of h us, Term.subst_subst_of (Subst.liftN_subst_of _ h) u]

end

-- ADE: none.
/-- `[ā / Δ][θ] = [ā[θ] / Δ]`: the substitution of the arguments of an instance, then by `θ`, is the
substitution of the arguments substituted by `θ`, each under the variables of its abstraction. -/
theorem InstanceArgs.toSubst_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Ψ : Scope} → (as : InstanceArgs k Δ Ψ) → ∀ {a} (x : Var Ψ a),
      (as.toSubst x).subst (Subst.liftN a.params.length θ) = (as.subst θ).toSubst x
  | _, .snoc _ _, _, .zero => rfl
  | _, .snoc as _, _, .succ x => InstanceArgs.toSubst_subst θ as x

/-! ### Identity and Telescopes -/

theorem Subst.lift_id_of {Γ : Scope} {b : Scope.Entry} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) :
    ∀ {a} (x : Var (b :: Γ) a), Subst.lift θ x = Var.eta x
  | _, .zero => rfl
  | _, .succ x => by
    show (θ x).rename (Ren.liftN _ Ren.weaken) = _
    rw [h x, Var.eta_rename]
    rfl

theorem Subst.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {θ : Subst k Γ Γ}, (∀ {a} (x : Var Γ a), θ x = Var.eta x) →
      ∀ {a} (x : Var (Γ.extend n) a), Subst.liftN n θ x = Var.eta x
  | 0, _, h => h
  | n + 1, _, h => Subst.liftN_id_of (Γ := .var :: Γ) n (Subst.lift_id_of h)

mutual

-- ADE: `subst-id`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- A substitution of the second order that gives each variable `x̄. x[x̄]` changes nothing.
RFC: `\mathsf{id}_\theta` -/
theorem Term.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ} (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) :
    (t : Term k Γ) → t.subst θ = t
  | .var x ts => by rw [Term.subst, h x, Args.subst_id_of h ts, Var.eta_instantiate]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by rw [Term.subst, InstanceArgs.subst_id_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst, InstanceArgs.subst_id_of h as, Terms.subst_id_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst, InstanceArgs.subst_id_of h as, Term.subst_id_of h t, Motives.subst_id_of h Cs,
      Branches.subst_id_of h us]

theorem Args.subst_id_of {Γ : Scope} {a : List Parameter} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (ts : Args k Γ a) → ts.subst θ = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.subst, Term.subst_id_of h t, Args.subst_id_of h ts]

theorem InstanceArgs.subst_id_of {Γ Ξ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (as : InstanceArgs k Γ Ξ) → as.subst θ = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.subst_id_of h as,
      Term.subst_id_of (Subst.liftN_id_of _ h) B]

theorem Terms.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (ts : Terms k Γ) → ts.subst θ = ts
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst, Terms.subst_id_of h ts, Term.subst_id_of h t]

theorem Motives.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (Cs : Motives k Γ) → Cs.subst θ = Cs
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst, Motives.subst_id_of h Cs, Term.subst_id_of (Subst.liftN_id_of _ h) C]

theorem Branches.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (us : Branches k Γ) → us.subst θ = us
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst, Branches.subst_id_of h us, Term.subst_id_of (Subst.liftN_id_of _ h) u]

end

/-- Renaming a telescope by `ξ` then substituting it by `θ` is substituting it by their composition
`θ'`. -/
theorem Telescope.subst_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter} :
    {θ : Subst k Γ Δ} → {ξ : Ren Δ Ξ} → {θ' : Subst k Γ Ξ} → (∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) →
      (Θ : Telescope k Ξ ps) → (Θ.rename ξ).subst θ = Θ.subst θ'
  | _, _, _, _, .nil => rfl
  | _, _, _, h, .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst, Telescope.subst, Term.subst_rename_of h A,
      Telescope.subst_rename_of (Subst.lift_rename_of h) Θ]

/-- Substituting a telescope by `θ₁` then by `θ₂` is substituting it by their composition `θ₃`.
RFC: `\mathsf{comp}_\theta.\Theta` -/
theorem Telescope.subst_subst_of {Γ Δ Ξ : Scope} {ps : List Parameter} :
    {θ₁ : Subst k Δ Ξ} → {θ₂ : Subst k Γ Δ} → {θ₃ : Subst k Γ Ξ} →
      (∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) →
      (Θ : Telescope k Ξ ps) → (Θ.subst θ₁).subst θ₂ = Θ.subst θ₃
  | _, _, _, _, .nil => rfl
  | _, _, _, h, .cons q p A Θ => by
    rw [Telescope.subst, Telescope.subst, Telescope.subst, Term.subst_subst_of h A,
      Telescope.subst_subst_of (Subst.lift_subst_of h) Θ]

/-- A substitution of the first order that renames each variable to itself changes no telescope.
RFC: `\mathsf{id}_\sigma.\Theta` -/
theorem Telescope.subst₀_id_of {Γ : Scope} {ps : List Parameter} :
    {σ : Subst₀ k Γ Γ} → (∀ {a} (x : Var Γ a), σ x = .var x) →
      (Θ : Telescope k Γ ps) → Θ.subst₀ σ = Θ
  | _, _, .nil => rfl
  | _, h, .cons q p A Θ => by
    rw [Telescope.subst₀, Term.subst₀_id_of h A, Telescope.subst₀_id_of (Subst₀.lift_id_of h) Θ]

-- ADE: none.
/-- A substitution of the second order that gives each variable its own eta-expansion changes no
telescope. -/
theorem Telescope.subst_id_of {Γ : Scope} {ps : List Parameter} :
    {θ : Subst k Γ Γ} → (∀ {a} (x : Var Γ a), θ x = Var.eta x) →
      (Θ : Telescope k Γ ps) → Θ.subst θ = Θ
  | _, _, .nil => rfl
  | _, h, .cons q p A Θ => by
    rw [Telescope.subst, Term.subst_id_of h A, Telescope.subst_id_of (Subst.lift_id_of h) Θ]

/-- A substitution of the first order then one of the second order swap on a telescope, as
`Subst₀.Swaps` says. -/
theorem Telescope.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {ps : List Parameter} :
    {σ : Subst₀ k Δ Ξ} → {θ₁ : Subst k Γ Δ} → {θ₂ : Subst k Ψ Ξ} → {σ' : Subst₀ k Γ Ψ} →
      Subst₀.Swaps σ θ₁ θ₂ σ' →
      (Θ : Telescope k Ξ ps) → (Θ.subst₀ σ).subst θ₁ = (Θ.subst θ₂).subst₀ σ'
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, h, .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.subst, Telescope.subst, Telescope.subst₀,
      Term.subst_subst₀_of h A, Telescope.subst_subst₀_of h.lift Θ]

-- ADE: none.
/-- A substitution `σ` of the first order then one `θ₁` of the second order are the substitution
`θ₂` of the second order that gives each variable what `σ` gives it, substituted by `θ₁`: `u[θ₁]`
when `σ` gives it a term `u`, and `θ₁(y)` when `σ` renames it to `y`, which the RFC, whose variables
are named, writes `θ₁(x)`.
RFC: `\mathsf{comp}_{\sigma\theta}.t` -/
theorem Term.subst_subst₀ {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ}
    {θ₂ : Subst k Γ Ξ} (hterm : ∀ (x : Var Ξ .var) (u : Term k Δ), σ x = .term u → θ₂ x = u.subst θ₁)
    (hvar : ∀ {a} (x : Var Ξ a) (y : Var Δ a), σ x = .var y → θ₂ x = θ₁ y) (t : Term k Ξ) :
    (t.subst₀ σ).subst θ₁ = t.subst θ₂ :=
  (Term.subst_subst₀_of (σ' := Subst₀.id) (swaps_id hterm hvar) t).trans (Term.subst₀_id _)
where
  /-- The hypotheses make `σ`, `θ₁`, `θ₂` and the identity swap. -/
  swaps_id {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Γ Ξ}
      (hterm : ∀ (x : Var Ξ .var) (u : Term k Δ), σ x = .term u → θ₂ x = u.subst θ₁)
      (hvar : ∀ {a} (x : Var Ξ a) (y : Var Δ a), σ x = .var y → θ₂ x = θ₁ y) :
      Subst₀.Swaps σ θ₁ θ₂ Subst₀.id :=
    ⟨fun x y e => (Term.subst₀_id_of (Subst₀.liftN_id_of _ fun _ => rfl) _).trans (hvar x y e),
      fun x u e => (Term.subst₀_id _).trans (hterm x u e)⟩

-- ADE: none.
/-- A substitution of the first order then one of the second order are one substitution of the
second order on a telescope, as `Term.subst_subst₀` states on a term.
RFC: `\mathsf{comp}_{\sigma\theta}.\Theta` -/
theorem Telescope.subst_subst₀ {Γ Δ Ξ : Scope} {ps : List Parameter} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Γ Ξ}
    (hterm : ∀ (x : Var Ξ .var) (u : Term k Δ), σ x = .term u → θ₂ x = u.subst θ₁)
    (hvar : ∀ {a} (x : Var Ξ a) (y : Var Δ a), σ x = .var y → θ₂ x = θ₁ y)
    (Θ : Telescope k Ξ ps) : (Θ.subst₀ σ).subst θ₁ = Θ.subst θ₂ :=
  (Telescope.subst_subst₀_of (Term.subst_subst₀.swaps_id hterm hvar) Θ).trans
    (Telescope.subst₀_id_of (fun _ => rfl) _)

/-! ## Closed Substitutions -/

/-- The renaming of the empty scope, which has no variable. -/
def Ren.empty {Γ : Scope} : Ren Γ [] := fun x => nomatch x

/-- Where a variable of the scope `Γ` extended by `n` variables comes from: a variable `y` of `Γ`,
which is `y.weakenN n`, or one of the new variables, a variable of the empty scope extended by
them. -/
def Var.split {Γ : Scope} {e : Scope.Entry} :
    (n : Nat) → Var (Γ.extend n) e → Var Γ e ⊕ Var (Scope.extend [] n) e
  | 0, x => .inl x
  | n + 1, x =>
    match Var.split (Γ := .var :: Γ) n x with
    | .inl .zero => .inr (Var.weakenN n .zero)
    | .inl (.succ y) => .inl y
    | .inr z => .inr (Ren.liftN n Ren.empty z)

/-- `(θ₁, θ₂)`: the closed substitution `θ₁` of the scope `Γ` followed by the closed substitution
`θ₂` of `n` new variables, which gives each variable of `Γ` what `θ₁` gives it, and each new
variable what `θ₂` gives it.
RFC: `\mathsf{pair}_\theta` -/
def Subst.append {Γ : Scope} {n : Nat} (θ₁ : Subst k [] Γ) (θ₂ : Subst k [] (Scope.extend [] n)) :
    Subst k [] (Γ.extend n) := fun x =>
  match x.split n with
  | .inl y => θ₁ y
  | .inr y => θ₂ y

/-- A variable of the scope `Γ` extended by `n` variables is a variable of `Γ` or a new one. -/
theorem Var.cases_extend {Γ : Scope} {e : Scope.Entry} :
    (n : Nat) → (x : Var (Γ.extend n) e) →
      (∃ y : Var Γ e, x = y.weakenN n) ∨
        ∃ z : Var (Scope.extend [] n) e, x = Ren.liftN n Ren.empty z
  | 0, x => .inl ⟨x, rfl⟩
  | n + 1, x => by
    rcases Var.cases_extend (Γ := .var :: Γ) n x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · cases y with
      | zero =>
        refine .inr ⟨Var.weakenN n .zero, ?_⟩
        exact (Ren.liftN_weakenN n (Ren.lift Ren.empty) .zero).symm
      | succ y => exact .inl ⟨y, rfl⟩
    · refine .inr ⟨Ren.liftN n Ren.empty z, ?_⟩
      exact (Ren.liftN_comp_of n (ξ₃ := Ren.empty) (fun y => nomatch y) z).symm

/-- A variable of `Γ` comes from `Γ`. -/
theorem Var.split_weakenN {Γ : Scope} {e : Scope.Entry} :
    (n : Nat) → (y : Var Γ e) → (y.weakenN n).split n = .inl y
  | 0, _ => rfl
  | n + 1, y => by
    rw [Var.split]
    rw [show Var.weakenN (n + 1) y = Var.weakenN n y.succ from rfl,
      Var.split_weakenN (Γ := .var :: Γ) n y.succ]
    rfl

/-- A new variable is a new variable. -/
theorem Var.split_liftN_empty {Γ : Scope} {e : Scope.Entry} :
    (n : Nat) → (z : Var (Scope.extend [] n) e) →
      (Ren.liftN n (Ren.empty (Γ := Γ)) z).split n = .inr z
  | 0, z => nomatch z
  | n + 1, z => by
    rcases Var.cases_extend (Γ := [.var]) n z with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · cases y with
      | zero =>
        rw [Var.split]
        rw [show Ren.liftN (n + 1) (Ren.empty (Γ := Γ)) (Var.weakenN n .zero) =
          Ren.liftN n (Ren.lift Ren.empty) (Var.weakenN n .zero) from rfl,
          Ren.liftN_weakenN, Var.split_weakenN]
        rfl
      | succ y => nomatch y
    · rw [Var.split]
      rw [show Ren.liftN (n + 1) (Ren.empty (Γ := Γ)) (Ren.liftN n Ren.empty z) =
          Ren.liftN n (Ren.lift Ren.empty) (Ren.liftN n Ren.empty z) from rfl,
        Ren.liftN_comp_of n (ξ₃ := Ren.empty) (fun y => nomatch y) z,
        Var.split_liftN_empty (Γ := .var :: Γ) n z]

/-- `(θ₁, θ₂)` gives the variables of `Γ` what `θ₁` gives them. -/
theorem Subst.append_weakenN {Γ : Scope} {n : Nat} (θ₁ : Subst k [] Γ)
    (θ₂ : Subst k [] (Scope.extend [] n)) {a : Scope.Entry} (y : Var Γ a) :
    Subst.append θ₁ θ₂ (y.weakenN n) = θ₁ y := by
  simp only [Subst.append, Var.split_weakenN]

/-- `(θ₁, θ₂)` gives the new variables what `θ₂` gives them. -/
theorem Subst.append_liftN_empty {Γ : Scope} {n : Nat} (θ₁ : Subst k [] Γ)
    (θ₂ : Subst k [] (Scope.extend [] n)) {a : Scope.Entry} (z : Var (Scope.extend [] n) a) :
    Subst.append θ₁ θ₂ (Ren.liftN n Ren.empty z) = θ₂ z := by
  simp only [Subst.append, Var.split_liftN_empty]

/-- `[t / x]`: the closed substitution of one variable by the closed term `t`. -/
def Subst.closedSingle (t : Term k []) : Subst k [] [.var] := fun x =>
  match x with
  | .zero => t
  | .succ x => nomatch x

/-- `[t̄ / x̄]`: the closed substitution that gives the variables of a telescope the closed arguments
`t̄`, the first one first.
RFC: `\mathsf{args}_\theta` -/
def Args.toSubst : {ps : List Parameter} → Args k [] ps → Subst k [] (Scope.extend [] ps.length)
  | [], .nil => fun x => nomatch x
  | _ :: _, .cons t ts => Subst.append (Subst.closedSingle t) ts.toSubst

/-- A variable of a scope whose entries are variables is a variable, under new variables. -/
theorem Var.extend_var {Γ : Scope} (hΓ : ∀ {b}, Var Γ b → b = .var) :
    (n : Nat) → {b : Scope.Entry} → Var (Γ.extend n) b → b = .var
  | 0, _, x => hΓ x
  | n + 1, _, x => Var.extend_var (Γ := .var :: Γ)
      (fun y => match y with
        | .zero => rfl
        | .succ y => hΓ y) n x

/-- A substitution of the empty scope changes no term, under new variables. -/
theorem Term.subst_liftN_empty {a : Nat} (θ : Subst k [] []) (t : Term k (Scope.extend [] a)) :
    t.subst (Subst.liftN a θ) = t :=
  Term.subst_id_of (Subst.liftN_id_of a fun x => by cases x) t

/-- `(θ₁, θ₂)` gives each variable what `θ₁` under the new variables gives it, substituted by
`θ₂`. -/
theorem Subst.append_eq_liftN {Γ : Scope} {n : Nat} (θ₁ : Subst k [] Γ)
    (θ₂ : Subst k [] (Scope.extend [] n)) {a : Scope.Entry} (x : Var (Γ.extend n) a) :
    Subst.append θ₁ θ₂ x = (Subst.liftN n θ₁ x).subst (Subst.liftN a.params.length θ₂) := by
  rcases Var.cases_extend n x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Subst.append_weakenN, Subst.liftN_weakenN, Term.subst_rename_of (Subst.liftN_rename_of
      a.params.length (ξ := Ren.weakenN n) (θ' := fun y => θ₂ (y.weakenN n)) fun _ => rfl)]
    exact (Term.subst_liftN_empty _ _).symm
  · obtain rfl := Var.extend_var (fun y => by cases y) n z
    rw [Subst.append_liftN_empty]
    show _ = (Subst.liftN n θ₁ (Ren.liftN n Ren.empty z)).subst (Subst.liftN 0 θ₂)
    rw [Subst.liftN_rename_of n (θ' := fun y => θ₁ (Ren.empty y)) (fun _ => rfl),
      Subst.liftN_id_of n (fun y => by cases y)]
    rfl

-- ADE: none.
/-- Substituting a closed term `t` for a variable is the same with the substitution `[t / x]` of the
first order as with the closed substitution `[t / x]` of the second order. -/
theorem Subst₀.Swaps.closedSingle (t : Term k []) :
    Subst₀.Swaps (Subst₀.single t) (fun x => nomatch x : Subst k [] []) (Subst.closedSingle t)
      Subst₀.id := by
  refine ⟨fun x y e => ?_, fun x u e => ?_⟩
  · cases x with
    | zero => cases e
    | succ x => cases x
  · cases x with
    | zero =>
      cases e
      exact (Term.subst₀_id t).trans (Term.subst_id_of (fun x => by cases x) t).symm
    | succ x => cases x

/-- `B[t / x]`, for a closed term `t`, is the same under `n` new variables with both
substitutions. -/
theorem Term.subst₀_liftN_single_closed (n : Nat) (t : Term k [])
    (B : Term k (Scope.extend [.var] n)) :
    B.subst₀ (Subst₀.liftN n (Subst₀.single t)) = B.subst (Subst.liftN n (Subst.closedSingle t)) :=
  (Term.subst_id_of (Subst.liftN_id_of n fun x => by cases x) _).symm.trans
    ((Term.subst_subst₀_of (Subst₀.Swaps.liftN n (Subst₀.Swaps.closedSingle t)) B).trans
      (Term.subst₀_id_of (Subst₀.liftN_id_of n fun _ => rfl) _))

-- ADE: none.
/-- `B[t̄ / Θ]`, for closed arguments `t̄`, is `B` substituted by the closed substitution `[t̄ / x̄]` of
these arguments.
RFC: `\mathsf{closed}_\theta` -/
theorem Term.instantiate_eq_subst :
    {ps : List Parameter} → (B : Term k (Scope.extend [] ps.length)) → (ts : Args k [] ps) →
      B.instantiate ts = B.subst ts.toSubst
  | [], B, .nil => (Term.subst_id_of (fun x => by cases x) B).symm
  | _ :: ps, B, .cons t ts =>
    (Term.instantiate_eq_subst (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).trans
      ((congrArg (fun u => Term.subst ts.toSubst u)
        (Term.subst₀_liftN_single_closed ps.length t B)).trans
        (Term.subst_subst_of (fun x =>
          (Subst.append_eq_liftN (Subst.closedSingle t) ts.toSubst x).symm) B))

-- ADE: none.
/-- A closed term weakened to the empty scope is itself. -/
theorem Term.weakenClosed_nil (t : Term k []) : (t.weakenClosed : Term k []) = t :=
  Term.rename_id_of (fun x => by cases x) t

-- ADE: none.
/-- A closed term weakened to a scope, then substituted by a closed substitution, is itself. -/
theorem Term.subst_weakenClosed {Γ : Scope} (σ : Subst k [] Γ) (t : Term k []) :
    (t.weakenClosed : Term k Γ).subst σ = t :=
  (Term.subst_rename_of (θ' := fun x => Var.eta x) (fun x => by cases x) t).trans
    (Term.subst_id_of (fun _ => rfl) t)

-- ADE: none.
/-- `Θ[σ⇑][v / x] = Θ[σ, v]`: a telescope under a new variable, substituted by a closed
substitution `σ` of the context, then by a closed term `v` for this variable, is substituted by `σ`
followed by `v`. -/
theorem Telescope.subst_lift_single {Γ : Scope} {ps : List Parameter} (σ : Subst k [] Γ)
    (v : Term k []) (Θ : Telescope k (.var :: Γ) ps) :
    (Θ.subst (Subst.lift σ)).subst₀ (Subst₀.single v) =
      Θ.subst (Subst.append (n := 1) σ (Subst.closedSingle v)) :=
  (Telescope.subst_id_of (fun x => by cases x) _).symm.trans
    ((Telescope.subst_subst₀_of (Subst₀.Swaps.closedSingle v) _).trans
      ((Telescope.subst₀_id_of (fun _ => rfl) _).trans
        (Telescope.subst_subst_of
          (fun x => (Subst.append_eq_liftN (n := 1) σ (Subst.closedSingle v) x).symm) Θ)))

-- ADE: none.
/-- `C[σ⇑][v / x] = C[σ, v]`: a term under a new variable, substituted by a closed substitution `σ`
of the context, then by a closed term `v` for this variable, is substituted by `σ` followed by
`v`. -/
theorem Term.subst_lift_single {Γ : Scope} (σ : Subst k [] Γ) (v : Term k [])
    (C : Term k (.var :: Γ)) :
    (C.subst (Subst.lift σ)).subst₀ (Subst₀.single v) =
      C.subst (Subst.append (n := 1) σ (Subst.closedSingle v)) :=
  (Term.subst_id_of (fun x => by cases x) _).symm.trans
    ((Term.subst_subst₀_of (Subst₀.Swaps.closedSingle v) _).trans
      ((Term.subst₀_id_of (fun _ => rfl) _).trans
        (Term.subst_subst_of
          (fun x => (Subst.append_eq_liftN (n := 1) σ (Subst.closedSingle v) x).symm) C)))

/-! ## Levels

The instantiation of the level variables replaces levels only, so that it commutes with the
renamings and the substitutions, and the instantiations compose. -/

/-- The value of a level whose variables are replaced is its value under the values of the levels
that replace them.
RFC: `\mathsf{instance}_l` -/
theorem Level.value_subst {k k' : Nat} (ls' : Fin k → Level k') (ρ : Fin k' → Nat) :
    ∀ l : Level k, (l.subst ls').value ρ = l.value fun i => (ls' i).value ρ
  | .zero => rfl
  | .succ l => congrArg (· + 1) (Level.value_subst ls' ρ l)
  | .max l₁ l₂ => by
    simp only [Level.subst, Level.value, Level.value_subst ls' ρ l₁, Level.value_subst ls' ρ l₂]
  | .var _ => rfl

/-- The value `v` in which the levels `ls'` replace the level variables. -/
def Val.substLevels {k' : Nat} {Γ : Scope} {a : Scope.Entry} (ls' : Fin k → Level k') :
    Val k Γ a → Val k' Γ a
  | .var x => .var x
  | .term t => .term (t.substLevels ls')

/-- Replacing the level variables by `ls₁` then by `ls₂` is replacing them by their composition.
RFC: `\mathsf{comp}_l.l` -/
theorem Level.subst_subst {k' k'' : Nat} (ls₁ : Fin k → Level k') (ls₂ : Fin k' → Level k'') :
    ∀ l : Level k, (l.subst ls₁).subst ls₂ = l.subst fun i => (ls₁ i).subst ls₂
  | .zero => rfl
  | .succ l => congrArg Level.succ (Level.subst_subst ls₁ ls₂ l)
  | .max l₁ l₂ => by rw [Level.subst, Level.subst, Level.subst, Level.subst_subst ls₁ ls₂ l₁,
      Level.subst_subst ls₁ ls₂ l₂]
  | .var _ => rfl

mutual

/-- The instantiation of the level variables commutes with the renamings. -/
theorem Term.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') (ξ : Ren Γ Δ) :
    (t : Term k Δ) → (t.rename ξ).substLevels ls' = (t.substLevels ls').rename ξ
  | .var x ts => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      Args.substLevels_rename ls' ξ ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' ξ as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' ξ as, Terms.substLevels_rename ls' ξ ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' ξ as, Term.substLevels_rename ls' ξ t,
      Motives.substLevels_rename ls' ξ Cs, Branches.substLevels_rename ls' ξ us]

theorem Args.substLevels_rename {k' : Nat} {Γ Δ : Scope} {a : List Parameter} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) : (ts : Args k Δ a) → (ts.rename ξ).substLevels ls'
      = (ts.substLevels ls').rename ξ
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.substLevels, Args.substLevels, Args.rename,
      Term.substLevels_rename ls' ξ t, Args.substLevels_rename ls' ξ ts]

theorem InstanceArgs.substLevels_rename {k' : Nat} {Γ Δ Ξ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (as : InstanceArgs k Δ Ξ) → (as.rename ξ).substLevels ls' = (as.substLevels ls').rename ξ
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.substLevels, InstanceArgs.substLevels,
      InstanceArgs.rename, InstanceArgs.substLevels_rename ls' ξ as, Term.substLevels_rename]

theorem Terms.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (ts : Terms k Δ) → (ts.rename ξ).substLevels ls' = (ts.substLevels ls').rename ξ
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.substLevels, Terms.substLevels, Terms.rename,
      Terms.substLevels_rename ls' ξ ts, Term.substLevels_rename]

theorem Motives.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (Cs : Motives k Δ) → (Cs.rename ξ).substLevels ls' = (Cs.substLevels ls').rename ξ
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.substLevels, Motives.substLevels, Motives.rename,
      Motives.substLevels_rename ls' ξ Cs, Term.substLevels_rename]

theorem Branches.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (us : Branches k Δ) → (us.rename ξ).substLevels ls' = (us.substLevels ls').rename ξ
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.rename, Branches.substLevels, Branches.substLevels, Branches.rename,
      Branches.substLevels_rename ls' ξ us, Term.substLevels_rename]

end

/-- The instantiation of the level variables of a value commutes with the renamings. -/
theorem Val.substLevels_rename {k' : Nat} {Γ Δ : Scope} {a : Scope.Entry} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) : (v : Val k Δ a) → (v.rename ξ).substLevels ls' = (v.substLevels ls').rename ξ
  | .var _ => rfl
  | .term t => congrArg Val.term (Term.substLevels_rename ls' ξ t)

theorem Subst₀.lift_substLevels_of {k' : Nat} {Γ Δ : Scope} {b : Scope.Entry}
    {ls' : Fin k → Level k'} {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    ∀ {a} (x : Var (b :: Δ) a), (Subst₀.lift σ x).substLevels ls' = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => (Val.substLevels_rename ls' _ (σ x)).trans (congrArg _ (h x))

theorem Subst₀.liftN_substLevels_of {k' : Nat} {Γ Δ : Scope} :
    ∀ (n : Nat) {ls' : Fin k → Level k'} {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ},
      (∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) →
      ∀ {a} (x : Var (Δ.extend n) a), (Subst₀.liftN n σ x).substLevels ls' = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_substLevels_of (Γ := .var :: Γ) (Δ := .var :: Δ) n
      (Subst₀.lift_substLevels_of h)

mutual

/-- The instantiation of the level variables commutes with the substitutions of the first order,
whose terms it instantiates.
RFC: `\mathsf{comm}_{l\sigma}.t` -/
theorem Term.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (t : Term k Δ) → (t.subst₀ σ).substLevels ls' = (t.substLevels ls').subst₀ σ'
  | .var x ts => by
    rw [Term.subst₀_var, Term.substLevels, Term.subst₀_var, ← h x,
      ← Args.substLevels_subst₀_of h ts]
    cases σ x <;> rfl
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst₀, Term.substLevels, Term.substLevels, Term.subst₀,
      InstanceArgs.substLevels_subst₀_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst₀, Term.substLevels, Term.substLevels, Term.subst₀,
      InstanceArgs.substLevels_subst₀_of h as, Terms.substLevels_subst₀_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst₀, Term.substLevels, Term.substLevels, Term.subst₀,
      InstanceArgs.substLevels_subst₀_of h as, Term.substLevels_subst₀_of h t,
      Motives.substLevels_subst₀_of h Cs, Branches.substLevels_subst₀_of h us]

theorem Args.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {a : List Parameter}
    {ls' : Fin k → Level k'} {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (ts : Args k Δ a) → (ts.subst₀ σ).substLevels ls' = (ts.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.substLevels, Args.substLevels, Args.subst₀,
      Term.substLevels_subst₀_of h t, Args.substLevels_subst₀_of h ts]

theorem InstanceArgs.substLevels_subst₀_of {k' : Nat} {Γ Δ Ξ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (as : InstanceArgs k Δ Ξ) → (as.subst₀ σ).substLevels ls' = (as.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.substLevels, InstanceArgs.substLevels,
      InstanceArgs.subst₀, InstanceArgs.substLevels_subst₀_of h as,
      Term.substLevels_subst₀_of (Subst₀.liftN_substLevels_of _ h) B]

theorem Terms.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (ts : Terms k Δ) → (ts.subst₀ σ).substLevels ls' = (ts.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.substLevels, Terms.substLevels,
      Terms.subst₀, Terms.substLevels_subst₀_of h ts,
      Term.substLevels_subst₀_of h t]

theorem Motives.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (Cs : Motives k Δ) → (Cs.subst₀ σ).substLevels ls' = (Cs.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.substLevels, Motives.substLevels,
      Motives.subst₀, Motives.substLevels_subst₀_of h Cs,
      Term.substLevels_subst₀_of (Subst₀.liftN_substLevels_of _ h) C]

theorem Branches.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (us : Branches k Δ) → (us.subst₀ σ).substLevels ls' = (us.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst₀, Branches.substLevels, Branches.substLevels,
      Branches.subst₀, Branches.substLevels_subst₀_of h us,
      Term.substLevels_subst₀_of (Subst₀.liftN_substLevels_of _ h) u]

end

/-- `B[t̄ / Θ][l̄' / l̄] = B[l̄' / l̄][t̄[l̄' / l̄] / Θ]`.
RFC: `\mathsf{comm}_l.\bar t` -/
theorem Term.substLevels_instantiate {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    {ps : List Parameter} → (B : Term k (Γ.extend ps.length)) → (ts : Args k Γ ps) →
      (B.instantiate ts).substLevels ls' = (B.substLevels ls').instantiate (ts.substLevels ls')
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t)))
        ts).substLevels ls' =
      Term.instantiate ((B.substLevels ls').subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.substLevels ls')))) (ts.substLevels ls')
    rw [Term.substLevels_instantiate ls']
    congr 1
    exact Term.substLevels_subst₀_of (Subst₀.liftN_substLevels_of ps.length (ls' := ls')
      (σ := Subst₀.single t) (σ' := Subst₀.single (t.substLevels ls'))
      fun x => by cases x <;> rfl) B

mutual

/-- Instantiating the level variables by `ls₁` then by `ls₂` is instantiating them by their
composition.
RFC: `\mathsf{comp}_l.t` -/
theorem Term.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (t : Term k Γ) → (t.substLevels ls₁).substLevels ls₂ = t.substLevels fun i => (ls₁ i).subst ls₂
  | .var x ts => by
    rw [Term.substLevels, Term.substLevels, Term.substLevels,
      Args.substLevels_substLevels ls₁ ls₂ ts]
  | .sort κ => by
    simp only [Term.substLevels, Universe.substLevels, Level.subst_subst]
  | .const c qs ls ps => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst]
  | .inst D qs ls ps as => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as]
  | .ctor D qs ls ps as c ts => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as, Terms.substLevels_substLevels ls₁ ls₂ ts]
  | .recursor r D qs ls ps as t Cs us => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as, Term.substLevels_substLevels ls₁ ls₂ t,
      Motives.substLevels_substLevels ls₁ ls₂ Cs, Branches.substLevels_substLevels ls₁ ls₂ us]

theorem Args.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} {a : List Parameter}
    (ls₁ : Fin k → Level k') (ls₂ : Fin k' → Level k'') :
    (ts : Args k Γ a) → (ts.substLevels ls₁).substLevels ls₂
      = ts.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons t ts => by
    rw [Args.substLevels, Args.substLevels, Args.substLevels,
      Term.substLevels_substLevels ls₁ ls₂ t,
      Args.substLevels_substLevels ls₁ ls₂ ts]

theorem InstanceArgs.substLevels_substLevels {k' k'' : Nat} {Γ Δ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (as : InstanceArgs k Γ Δ) →
      (as.substLevels ls₁).substLevels ls₂ = as.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.substLevels, InstanceArgs.substLevels, InstanceArgs.substLevels,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as, Term.substLevels_substLevels ls₁ ls₂ B]

theorem Terms.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (ts : Terms k Γ) →
      (ts.substLevels ls₁).substLevels ls₂ = ts.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.substLevels, Terms.substLevels, Terms.substLevels,
      Terms.substLevels_substLevels ls₁ ls₂ ts, Term.substLevels_substLevels ls₁ ls₂ t]

theorem Motives.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (Cs : Motives k Γ) →
      (Cs.substLevels ls₁).substLevels ls₂ = Cs.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.substLevels, Motives.substLevels, Motives.substLevels,
      Motives.substLevels_substLevels ls₁ ls₂ Cs, Term.substLevels_substLevels ls₁ ls₂ C]

theorem Branches.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (us : Branches k Γ) →
      (us.substLevels ls₁).substLevels ls₂ = us.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.substLevels, Branches.substLevels, Branches.substLevels,
      Branches.substLevels_substLevels ls₁ ls₂ us, Term.substLevels_substLevels ls₁ ls₂ u]

end

/-- Instantiating the level variables of a telescope by `ls₁` then by `ls₂` is instantiating them by
their composition.
RFC: `\mathsf{comp}_l.\Theta` -/
theorem Telescope.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} {ps : List Parameter}
    (ls₁ : Fin k → Level k') (ls₂ : Fin k' → Level k'') :
    (Θ : Telescope k Γ ps) →
      (Θ.substLevels ls₁).substLevels ls₂ = Θ.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.substLevels, Telescope.substLevels, Telescope.substLevels,
      Term.substLevels_substLevels ls₁ ls₂ A, Telescope.substLevels_substLevels ls₁ ls₂ Θ]

/-- Instantiating the level variables of a context by `ls₁` then by `ls₂` is instantiating them by
their composition.
RFC: `\mathsf{comp}_l.\Gamma` -/
theorem Context.substLevels_substLevels {k' k'' : Nat} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') : {Γ : Scope} → (ctx : Context k Γ) →
      (ctx.substLevels ls₁).substLevels ls₂ = ctx.substLevels fun i => (ls₁ i).subst ls₂
  | _, .empty => rfl
  | _, .var ctx A => by
    rw [Context.substLevels, Context.substLevels, Context.substLevels,
      Context.substLevels_substLevels ls₁ ls₂ ctx, Term.substLevels_substLevels ls₁ ls₂ A]
  | _, .secondOrder ctx Θ A ψ => by
    rw [Context.substLevels, Context.substLevels, Context.substLevels,
      Context.substLevels_substLevels ls₁ ls₂ ctx, Telescope.substLevels_substLevels ls₁ ls₂ Θ,
      Term.substLevels_substLevels ls₁ ls₂ A]

/-- Instantiating the level variables of a sort by `ls₁` then by `ls₂` is instantiating them by their
composition. -/
theorem Universe.substLevels_substLevels {k' k'' : Nat} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') (κ : Universe k) :
    (κ.substLevels ls₁).substLevels ls₂ = κ.substLevels fun i => (ls₁ i).subst ls₂ := by
  simp only [Universe.substLevels, Level.subst_subst]

/-- The instantiation of the level variables of a telescope commutes with the renamings. -/
theorem Telescope.substLevels_rename {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    (ls' : Fin k → Level k') :
    (ξ : Ren Γ Δ) → (Θ : Telescope k Δ ps)
      → (Θ.rename ξ).substLevels ls' = (Θ.substLevels ls').rename ξ
  | _, .nil => rfl
  | ξ, .cons q p A Θ => by
    rw [Telescope.rename, Telescope.substLevels, Telescope.substLevels, Telescope.rename,
      Term.substLevels_rename, Telescope.substLevels_rename ls' (Ren.lift ξ) Θ]

/-- The instantiation of the level variables of a telescope commutes with the substitutions of the
first order.
RFC: `\mathsf{comm}_{l\sigma}.\Theta` -/
theorem Telescope.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ls' : Fin k → Level k'} :
    {σ : Subst₀ k Γ Δ} → {σ' : Subst₀ k' Γ Δ}
      → (∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) →
      (Θ : Telescope k Δ ps) → (Θ.subst₀ σ).substLevels ls' = (Θ.substLevels ls').subst₀ σ'
  | _, _, _, .nil => rfl
  | _, _, h, .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.substLevels, Telescope.substLevels, Telescope.subst₀,
      Term.substLevels_subst₀_of h,
      Telescope.substLevels_subst₀_of (Subst₀.lift_substLevels_of h) Θ]

/-- `(Γ, Θ)[l̄' / l̄] = Γ[l̄' / l̄], Θ[l̄' / l̄]`.
RFC: `\mathsf{comm}_l.\Gamma` -/
theorem Context.substLevels_append {k' : Nat} (ls' : Fin k → Level k') :
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context k Γ) → (Θ : Telescope k Γ ps) →
      (ctx.append Θ).substLevels ls' = (ctx.substLevels ls').append (Θ.substLevels ls')
  | _, [], _, .nil => rfl
  | _, _ :: _, ctx, .cons _ _ A Θ => Context.substLevels_append ls' (ctx.var A) Θ

/-- Equal levels are equal once the same levels replace their variables. -/
theorem Level.subst_equal {k' : Nat} (ls' : Fin k → Level k') {l₁ l₂ : Level k} (h : l₁ ≈ l₂) :
    l₁.subst ls' ≈ l₂.subst ls' := fun ρ => by
  rw [Level.value_subst, Level.value_subst]
  exact h _

/-- A level below an other is below it once the same levels replace their variables. -/
theorem Level.subst_le {k' : Nat} (ls' : Fin k → Level k') {l₁ l₂ : Level k} (h : l₁ ≤ l₂) :
    l₁.subst ls' ≤ l₂.subst ls' := fun ρ => by
  rw [Level.value_subst, Level.value_subst]
  exact h _

/-- A sort that bounds an other bounds it once the same levels replace their level variables. -/
theorem Universe.substLevels_bounded {k' : Nat} (ls' : Fin k → Level k') {κ₁ κ₂ : Universe k}
    (h : κ₁ ≼ κ₂) : κ₁.substLevels ls' ≼ κ₂.substLevels ls' :=
  ⟨h.1, Level.subst_le ls' h.2⟩

/-- The new variables of a scope have no level to instantiate. -/
theorem Args.substLevels_bound {k' : Nat} (ls' : Fin k → Level k') :
    {Γ : Scope} → (ps : List Parameter) →
      (Args.bound (Γ := Γ) ps : Args k _ ps).substLevels ls' = Args.bound ps
  | _, [] => rfl
  | _, _ :: ps => congrArg (Args.cons _) (Args.substLevels_bound ls' (Γ := .var :: _) ps)

/-- A variable as an abstraction has no level to instantiate. -/
theorem Var.eta_substLevels {k' : Nat} {Γ : Scope} {e : Scope.Entry} (ls' : Fin k → Level k')
    (x : Var Γ e) : (Var.eta x : Term k _).substLevels ls' = Var.eta x := by
  rw [Var.eta, Term.substLevels, Args.substLevels_bound, Var.eta]

theorem Subst.lift_substLevels_of {k' : Nat} {Γ Δ : Scope} {b : Scope.Entry}
    {ls' : Fin k → Level k'} {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    ∀ {a} (x : Var (b :: Δ) a), (Subst.lift θ x).substLevels ls' = Subst.lift θ' x
  | _, .zero => Var.eta_substLevels ls' _
  | _, .succ x => (Term.substLevels_rename ls' _ (θ x)).trans (congrArg _ (h x))

theorem Subst.liftN_substLevels_of {k' : Nat} {Γ Δ : Scope} :
    ∀ (n : Nat) {ls' : Fin k → Level k'} {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ},
      (∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) →
      ∀ {a} (x : Var (Δ.extend n) a), (Subst.liftN n θ x).substLevels ls' = Subst.liftN n θ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_substLevels_of (Γ := .var :: Γ) (Δ := .var :: Δ) n
      (Subst.lift_substLevels_of h)

mutual

/-- The instantiation of the level variables commutes with the substitutions of the second order,
whose abstractions it instantiates.
RFC: `\mathsf{comm}_{l\theta}.t` -/
theorem Term.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (t : Term k Δ) → (t.subst θ).substLevels ls' = (t.substLevels ls').subst θ'
  | .var x ts => by
    rw [Term.subst, Term.substLevels_instantiate, h x, Args.substLevels_subst_of h ts,
      Term.substLevels, Term.subst]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.subst, Term.substLevels, Term.substLevels, Term.subst,
      InstanceArgs.substLevels_subst_of h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.subst, Term.substLevels, Term.substLevels, Term.subst,
      InstanceArgs.substLevels_subst_of h as, Terms.substLevels_subst_of h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.subst, Term.substLevels, Term.substLevels, Term.subst,
      InstanceArgs.substLevels_subst_of h as, Term.substLevels_subst_of h t,
      Motives.substLevels_subst_of h Cs, Branches.substLevels_subst_of h us]

theorem Args.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {a : List Parameter}
    {ls' : Fin k → Level k'} {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (ts : Args k Δ a) → (ts.subst θ).substLevels ls' = (ts.substLevels ls').subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.substLevels, Args.substLevels, Args.subst,
      Term.substLevels_subst_of h t, Args.substLevels_subst_of h ts]

theorem InstanceArgs.substLevels_subst_of {k' : Nat} {Γ Δ Ξ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (as : InstanceArgs k Δ Ξ) → (as.subst θ).substLevels ls' = (as.substLevels ls').subst θ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.substLevels, InstanceArgs.substLevels,
      InstanceArgs.subst, InstanceArgs.substLevels_subst_of h as,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ h) B]

theorem Terms.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (ts : Terms k Δ) → (ts.subst θ).substLevels ls' = (ts.substLevels ls').subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst, Terms.substLevels, Terms.substLevels,
      Terms.subst, Terms.substLevels_subst_of h ts,
      Term.substLevels_subst_of h t]

theorem Motives.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (Cs : Motives k Δ) → (Cs.subst θ).substLevels ls' = (Cs.substLevels ls').subst θ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst, Motives.substLevels, Motives.substLevels,
      Motives.subst, Motives.substLevels_subst_of h Cs,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ h) C]

theorem Branches.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (us : Branches k Δ) → (us.subst θ).substLevels ls' = (us.substLevels ls').subst θ'
  | .nil => rfl
  | .cons n m u us => by
    rw [Branches.subst, Branches.substLevels, Branches.substLevels,
      Branches.subst, Branches.substLevels_subst_of h us,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ h) u]

end

/-- The instantiation of the level variables of a telescope commutes with the substitutions of the
second order.
RFC: `\mathsf{comm}_{l\theta}.\Theta` -/
theorem Telescope.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ls' : Fin k → Level k'} :
    {θ : Subst k Γ Δ} → {θ' : Subst k' Γ Δ}
      → (∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) →
      (Θ : Telescope k Δ ps) → (Θ.subst θ).substLevels ls' = (Θ.substLevels ls').subst θ'
  | _, _, _, .nil => rfl
  | _, _, h, .cons q p A Θ => by
    rw [Telescope.subst, Telescope.substLevels, Telescope.substLevels, Telescope.subst,
      Term.substLevels_subst_of h, Telescope.substLevels_subst_of (Subst.lift_substLevels_of h) Θ]

/-- The substitution of the arguments of an instance for its parameters, with their levels
instantiated, gives each parameter its argument instantiated. -/
theorem InstanceArgs.toSubst_substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → ∀ {a} (x : Var Δ a),
      (as.toSubst x).substLevels ls' = (as.substLevels ls').toSubst x
  | _, .snoc _ _, _, .zero => rfl
  | _, .snoc as _, _, .succ x => InstanceArgs.toSubst_substLevels ls' as x

/-- The terms of substituted arguments are the terms of the arguments substituted. -/
theorem Args.terms_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {ps : List Parameter} → (ts : Args k Δ ps) → (ts.subst θ).terms = ts.terms.subst θ
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg _ (Args.terms_subst θ ts)

/-- The terms of arguments at instantiated levels are the terms of the arguments at these
levels. -/
theorem Args.terms_substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    {ps : List Parameter} → (ts : Args k Γ ps) → (ts.substLevels ls').terms = ts.terms.substLevels ls'
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg _ (Args.terms_substLevels ls' ts)

/-- The fields of a constructor at arguments of an instance, substituted, are its fields at the
arguments substituted. -/
theorem Constructor.fieldsAt_subst {j g k' : Nat} {Γ Δ Ξ : Scope} (c : Constructor j g k' Ξ)
    (I : Instance j g) (ls : Fin k' → Level k) (as : InstanceArgs k Δ Ξ) (θ : Subst k Γ Δ) :
    (c.fieldsAt I ls as).subst θ = c.fieldsAt I ls (as.subst θ) :=
  Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as) _

/-- The fields of a constructor at levels and arguments of an instance, at instantiated levels, are
its fields at the levels and the arguments at these levels. -/
theorem Constructor.fieldsAt_substLevels {j g k' k'' : Nat} {Γ Δ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) (ls : Fin k' → Level k) (as : InstanceArgs k Γ Δ) (ls' : Fin k → Level k'') :
    (c.fieldsAt I ls as).substLevels ls' =
      c.fieldsAt I (fun i => (ls i).subst ls') (as.substLevels ls') := by
  rw [Constructor.fieldsAt, Constructor.fieldsAt,
    Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels ls' as),
    Telescope.substLevels_substLevels]

/-! ## Motives at a Constructor -/

-- ADE: none.
/-- `C[T.c(x̄) / z]`: the motive `C`, over the term `z` it eliminates, at the constructor `c` of the
instance `T = D.{s̄; l̄; p̄} ā` applied to the new variables `x̄` of its fields, whose entries have the
parameters `fs`, the type of the branch of `c`. -/
def Term.atCtor {Γ Δ : Scope} (C : Term k (.var :: Γ)) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name)
    (fs : List Parameter) : Term k (Γ.extend fs.length) :=
  (C.rename (Ren.lift (Ren.weakenN fs.length))).subst₀
    (Subst₀.single (.ctor D qs ls ps (as.rename (Ren.weakenN fs.length)) c (Args.bound fs).terms))

/-- `B[t̄ / x̄]` for the terms of arguments is their instantiation. -/
theorem Term.instantiateTerms_terms {Γ : Scope} :
    {ps : List Parameter} → (B : Term k (Γ.extend ps.length)) → (ts : Args k Γ ps) →
      B.instantiateTerms ts.terms = some (B.instantiate ts)
  | [], _, .nil => rfl
  | _ :: _, B, .cons _ ts =>
    Term.instantiateTerms_terms (B.subst₀ (Subst₀.liftN _ (Subst₀.single _))) ts

/-! ## Motives and Branches at a Position -/

/-- The motive at a position of motives substituted is the motive substituted, under its
variables. -/
theorem Motives.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Cs : Motives k Δ} → {j n : Nat} → {C : Term k (Δ.extend (n + 1))} → Cs.get j = some ⟨n, C⟩ →
      (Cs.subst θ).get j = some ⟨n, C.subst (Subst.liftN (n + 1) θ)⟩
  | .nil, _, _, _, h => nomatch h
  | .cons .., 0, _, _, h => by cases h; rfl
  | .cons _ _ Cs, _ + 1, _, _, h => Motives.get_subst θ (Cs := Cs) h

/-- The branch at a position of branches substituted is the branch substituted, under its
variables. -/
theorem Branches.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {us : Branches k Δ} → {i n m : Nat} → {u : Term k (Δ.extend (n + m))} →
      us.get i = some ⟨n, m, u⟩ → (us.subst θ).get i = some ⟨n, m, u.subst (Subst.liftN (n + m) θ)⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ us, _ + 1, _, _, _, h => Branches.get_subst θ (us := us) h

/-- The motive at a position of motives whose levels are instantiated is a motive of the motives,
instantiated. -/
theorem Motives.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {Cs : Motives k Γ} → {j n : Nat} → {C : Term k' (Γ.extend (n + 1))} →
      (Cs.substLevels ls').get j = some ⟨n, C⟩ →
        ∃ C₀, Cs.get j = some ⟨n, C₀⟩ ∧ C = C₀.substLevels ls'
  | .nil, _, _, _, h => nomatch h
  | .cons .., 0, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ Cs, _ + 1, _, _, h => Motives.get_substLevels ls' (Cs := Cs) h

/-- The motive at a position of motives is there once their levels are instantiated. -/
theorem Motives.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {Cs : Motives k Γ} → {j n : Nat} → {C : Term k (Γ.extend (n + 1))} → Cs.get j = some ⟨n, C⟩ →
      (Cs.substLevels ls').get j = some ⟨n, C.substLevels ls'⟩
  | .nil, _, _, _, h => nomatch h
  | .cons .., 0, _, _, h => by cases h; rfl
  | .cons _ _ Cs, _ + 1, _, _, h => Motives.get_substLevels_of ls' (Cs := Cs) h

/-- The branch at a position of branches whose levels are instantiated is a branch of the branches,
instantiated. -/
theorem Branches.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {us : Branches k Γ} → {i n m : Nat} → {u : Term k' (Γ.extend (n + m))} →
      (us.substLevels ls').get i = some ⟨n, m, u⟩ →
        ∃ u₀, us.get i = some ⟨n, m, u₀⟩ ∧ u = u₀.substLevels ls'
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ us, _ + 1, _, _, _, h => Branches.get_substLevels ls' (us := us) h

/-- The branch at a position of branches is there once their levels are instantiated. -/
theorem Branches.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {us : Branches k Γ} → {i n m : Nat} → {u : Term k (Γ.extend (n + m))} →
      us.get i = some ⟨n, m, u⟩ → (us.substLevels ls').get i = some ⟨n, m, u.substLevels ls'⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ us, _ + 1, _, _, _, h => Branches.get_substLevels_of ls' (us := us) h

/-- Motives whose levels are instantiated are as many. -/
theorem Motives.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (Cs : Motives k Γ) → (Cs.substLevels ls').length = Cs.length
  | .nil => rfl
  | .cons _ _ Cs => congrArg (· + 1) (Motives.length_substLevels ls' Cs)

/-- Branches whose levels are instantiated are as many. -/
theorem Branches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (us : Branches k Γ) → (us.substLevels ls').length = us.length
  | .nil => rfl
  | .cons _ _ _ us => congrArg (· + 1) (Branches.length_substLevels ls' us)

/-! ## Motives at a Constructor -/

/-- The terms of arguments substituted are the terms of the arguments substituted. -/
theorem Args.terms_subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) :
    {ps : List Parameter} → (ts : Args k Δ ps) → (ts.subst₀ σ).terms = ts.terms.subst₀ σ
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg _ (Args.terms_subst₀ σ ts)

/-- `C[T.c(x̄) / z][t̄ / x̄] = C[T.c(t̄) / z]`: the motive at a constructor applied to the new variables
of its fields, instantiated by arguments of the fields, is the motive at the constructor applied to
them. -/
theorem Term.atCtor_instantiate {Γ Δ : Scope} (C : Term k (.var :: Γ)) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name)
    {fs : List Parameter} (ts : Args k Γ fs) :
    (C.atCtor D qs ls ps as c fs).instantiate ts =
      C.subst₀ (Subst₀.single (.ctor D qs ls ps as c ts.terms)) := by
  rw [Term.instantiate_eq_subst₀, Term.atCtor, Term.subst₀_subst₀_of (fun _ => rfl),
    Term.subst₀_rename_of]
  intro _ x
  cases x with
  | zero =>
    show Val.term ((Term.ctor D qs ls ps (as.rename (Ren.weakenN fs.length)) c
      (Args.bound fs).terms).subst₀ ts.toSubst₀) = _
    rw [Term.subst₀, InstanceArgs.subst₀_rename_of (ξ := Ren.weakenN fs.length) (σ' := Subst₀.id)
        (fun y => Args.toSubst₀_weakenN ts y),
      InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl), ← Args.terms_subst₀,
      Args.bound_toSubst₀]
    rfl
  | succ y => exact Args.toSubst₀_weakenN ts y

/-- The motive at a constructor, substituted under the variables of the fields, is the motive
substituted, at the constructor of the instance substituted. -/
theorem Term.atCtor_subst {Γ Γ' Δ : Scope} (θ : Subst k Γ' Γ) (C : Term k (.var :: Γ)) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name)
    (fs : List Parameter) :
    (C.atCtor D qs ls ps as c fs).subst (Subst.liftN fs.length θ) =
      (C.subst (Subst.lift θ)).atCtor D qs ls ps (as.subst θ) c fs := by
  rw [Term.atCtor, Term.atCtor, Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
  congr 1
  · have hX : (Term.ctor D qs ls ps (as.rename (Ren.weakenN fs.length)) c
          (Args.bound fs).terms).subst (Subst.liftN fs.length θ) =
        Term.ctor D qs ls ps ((as.subst θ).rename (Ren.weakenN fs.length)) c
          (Args.bound fs).terms := by
      rw [Term.subst, ← Args.terms_subst, Args.bound_subst,
        InstanceArgs.subst_rename_of (fun _ => rfl),
        InstanceArgs.rename_subst_of (θ' := fun y => Subst.liftN fs.length θ (y.weakenN fs.length))
          fun y => (Subst.liftN_weakenN _ θ y).symm]
      rfl
    rw [hX]
  · rw [Term.subst_rename_of (fun _ => rfl), Term.rename_subst_of (fun _ => rfl)]
    refine congrArg (fun θ' : Subst k _ _ => Term.subst θ' C) ?_
    funext _ x
    cases x with
    | zero => rfl
    | succ y =>
      show ((Subst.liftN fs.length θ) (y.weakenN fs.length)).rename (Ren.liftN _ Ren.weaken) =
        ((θ y).rename (Ren.liftN _ Ren.weaken)).rename (Ren.liftN _ (Ren.lift (Ren.weakenN _)))
      rw [Subst.liftN_weakenN, Term.rename_rename_of (Ren.liftN_comp_of _ fun _ => rfl),
        Term.rename_rename_of (Ren.liftN_comp_of _ fun _ => rfl)]
      rfl

/-- The motive at a constructor whose levels are instantiated is the motive instantiated, at the
constructor of the instance instantiated. -/
theorem Term.atCtor_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ Δ : Scope}
    (C : Term k (.var :: Γ)) (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ Δ) (c : Name) (fs : List Parameter) :
    (C.atCtor D qs ls ps as c fs).substLevels ls' =
      (C.substLevels ls').atCtor D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') c fs := by
  rw [Term.atCtor, Term.atCtor, Term.substLevels_subst₀_of (σ' := Subst₀.single
    ((Term.ctor D qs ls ps (as.rename (Ren.weakenN fs.length)) c (Args.bound fs).terms).substLevels
      ls')) (fun x => by cases x <;> rfl), Term.substLevels_rename]
  congr 2
  rw [Term.substLevels, InstanceArgs.substLevels_rename, ← Args.terms_substLevels,
    Args.substLevels_bound]

end Sic.Core
