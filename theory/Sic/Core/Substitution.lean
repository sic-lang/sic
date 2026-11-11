module

public import Sic.Core.Syntax

/-!
# Substitution

The substitutions of annex 09 of RFC 36: the substitutions of the first order, among them the
substitution `B[t̄ / Θ]` of the arguments of a telescope for its variables, the substitutions of the
second order, which replace each application `X[t̄]` by `B[t̄ / x̄]` where `x̄. B` is the
abstraction given to `X`, among them the substitution `[ā / Δ]` of the arguments of an instance for
its parameters and the substitution `[ā / Δ, t.T / d̄₁]`, which also gives the destructors before a
destructor the observations of a term by them, the closed substitutions, and the instantiation
`[l̄' / l̄]` of the level variables.

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

/-- The renaming that skips `n` new variables. -/
def Ren.weakenN {Γ : Scope} (n : Nat) : Ren (Γ.extend n) Γ := fun x => x.weakenN n

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
  | .obs D qs ls ps as t d bs => .obs D qs ls ps (as.rename ξ) (t.rename ξ) d (bs.rename ξ)
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs ls ps (as.rename ξ) (ss.rename ξ) (Ss.rename ξ) (vs.rename ξ)

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
  | .cons n m es u us => .cons n m es (u.rename (Ren.liftN m (Ren.liftN n ξ))) (us.rename ξ)

/-- The telescope `Θ` renamed by `ξ`. -/
def Telescope.rename {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.rename ξ) (Θ.rename (Ren.lift ξ))

/-- The states `Θ̄` renamed by `ξ`, under the variables of each state. -/
def States.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : States k Δ → States k Γ
  | .nil => .nil
  | .cons n S κs Ss => .cons n (S.rename (Ren.liftN _ ξ)) κs (Ss.rename ξ)

/-- The branches `ḡ` of a corecursor renamed by `ξ`, under the variables of each branch. -/
def CorecBranches.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) : CorecBranches k Δ → CorecBranches k Γ
  | .nil => .nil
  | .cons n m a v vs =>
    .cons n m a (v.rename (Ren.liftN a (Ren.liftN m (Ren.liftN n ξ)))) (vs.rename ξ)

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

-- ADE: none.
/-- `x̄_Δ`: the parameters `Δ` themselves, as the arguments of an instance in their own scope, each
one an abstraction over its telescope. -/
def InstanceArgs.identity : (Δ : Scope) → InstanceArgs k Δ Δ
  | [] => .nil
  | _ :: Δ => .snoc ((InstanceArgs.identity Δ).rename Ren.weaken) (Var.eta .zero)

-- ADE: none.
/-- `D.{s̄; l̄; p̄} ā`: the type `D` of the block of the type declaration `decl` at the instance `ι`
of its sort and grade variables, at its level variables and at the arguments `ā`, the type of a
recursive field when `ā` are the parameters themselves. -/
def TypeDeclaration.blockInstance {Γ : Scope} (decl : TypeDeclaration)
    (ι : Instance decl.sorts decl.grades) (D : Name) (as : InstanceArgs decl.levels Γ decl.scope) :
    Term decl.levels Γ :=
  .inst D (List.ofFn ι.sorts) (List.ofFn Level.var) (List.ofFn ι.grades) as

/-- A renamed term is the instance of the same type of a block. -/
theorem Term.blockName_rename {Γ Δ : Scope} (names : List Name) (ξ : Ren Γ Δ) :
    (A : Term k Δ) → (A.rename ξ).blockName names = A.blockName names
  | .var .. | .sort _ | .const .. | .inst .. | .ctor .. | .recursor .. | .obs .. | .corec .. => rfl

/-- A renamed telescope has its recursive fields at the same positions. -/
theorem Telescope.recursion_rename {Γ Δ : Scope} (names : List Name) :
    {ps : List Parameter} → (ξ : Ren Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.rename ξ).recursion names = Θ.recursion names
  | [], _, .nil => rfl
  | _ :: _, ξ, .cons _ _ A Θ => by
    rw [Telescope.rename, Telescope.recursion, Telescope.recursion, Term.blockName_rename,
      Telescope.recursion_rename names (Ren.lift ξ) Θ]

/-- The destructors `d̄` renamed by `ξ`, the arguments and the result of each under the destructors
before it, and the result under its arguments. -/
def Destructors.rename {Γ Δ : Scope} (ξ : Ren Γ Δ) :
    {ns : List Name} → Destructors k Δ ns → Destructors k Γ ns
  | _, .nil => .nil
  | _, .cons p q Θ B ψ ds =>
    .cons p q (Θ.rename ξ) (B.rename (Ren.liftN _ ξ)) ψ (ds.rename (Ren.lift ξ))

/-- Renamed destructors have their recursive destructors at the same positions. -/
theorem Destructors.recursion_rename {Γ Δ : Scope} (names : List Name) :
    {ns : List Name} → (ξ : Ren Γ Δ) → (ds : Destructors k Δ ns) →
      (ds.rename ξ).recursion names = ds.recursion names
  | _, _, .nil => rfl
  | _, ξ, .cons _ _ _ B _ ds => by
    rw [Destructors.rename, Destructors.recursion, Destructors.recursion, Term.blockName_rename,
      Destructors.recursion_rename names (Ren.lift ξ) ds]

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
  | .obs D qs ls ps as t d bs => .obs D qs ls ps (as.subst₀ σ) (t.subst₀ σ) d (bs.subst₀ σ)
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs ls ps (as.subst₀ σ) (ss.subst₀ σ) (Ss.subst₀ σ) (vs.subst₀ σ)

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
  | .cons n m es u us => .cons n m es (u.subst₀ (Subst₀.liftN m (Subst₀.liftN n σ))) (us.subst₀ σ)

/-- `Θ[σ]`: the telescope `Θ` substituted by `σ`.
RFC: `\mathsf{subst}_\sigma.\Theta` -/
def Telescope.subst₀ {Γ Δ : Scope} {ps : List Parameter} (σ : Subst₀ k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst₀ σ) (Θ.subst₀ (Subst₀.lift σ))

/-- The states `Θ̄` substituted by `σ`, under the variables of each state.
RFC: `\mathsf{subst}_\sigma.\bar\Theta` -/
def States.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : States k Δ → States k Γ
  | .nil => .nil
  | .cons n S κs Ss => .cons n (S.subst₀ (Subst₀.liftN _ σ)) κs (Ss.subst₀ σ)

/-- The branches `ḡ` of a corecursor substituted by `σ`, under the variables of each branch.
RFC: `\mathsf{subst}_\sigma.\bar g` -/
def CorecBranches.subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : CorecBranches k Δ → CorecBranches k Γ
  | .nil => .nil
  | .cons n m a v vs =>
    .cons n m a (v.subst₀ (Subst₀.liftN a (Subst₀.liftN m (Subst₀.liftN n σ)))) (vs.subst₀ σ)

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

/-- `g[t̄ / ȳ, ū / z̄]`, for the branch `g` of a corecursor, over the new variables `ȳ` of a state
and then `z̄` of the arguments of a destructor: the terms `t̄` are substituted for `ȳ` and `ū` for
`z̄`, when there are as many terms as variables, the variables `z̄` first, at the terms `ū` in the
scope of `ȳ`. -/
def Term.instantiateTerms₂ {Γ : Scope} {m a : Nat} (g : Term k ((Γ.extend m).extend a))
    (ts us : Terms k Γ) : Option (Term k Γ) :=
  (g.instantiateTerms (us.rename (Ren.weakenN m))).bind (·.instantiateTerms ts)

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
  | .obs D qs ls ps as t d bs => .obs D qs ls ps (as.subst θ) (t.subst θ) d (bs.subst θ)
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs ls ps (as.subst θ) (ss.subst θ) (Ss.subst θ) (vs.subst θ)

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
  | .cons n m es u us => .cons n m es (u.subst (Subst.liftN m (Subst.liftN n θ))) (us.subst θ)

/-- `Θ[θ]`: the telescope `Θ` substituted by `θ`.
RFC: `\mathsf{subst}_\theta.\Theta` -/
def Telescope.subst {Γ Δ : Scope} {ps : List Parameter} (θ : Subst k Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.subst θ) (Θ.subst (Subst.lift θ))

/-- The states `Θ̄` substituted by `θ`, under the variables of each state.
RFC: `\mathsf{subst}_\theta.\bar\Theta` -/
def States.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : States k Δ → States k Γ
  | .nil => .nil
  | .cons n S κs Ss => .cons n (S.subst (Subst.liftN _ θ)) κs (Ss.subst θ)

/-- The branches `ḡ` of a corecursor substituted by `θ`, under the variables of each branch.
RFC: `\mathsf{subst}_\theta.\bar g` -/
def CorecBranches.subst {Γ Δ : Scope} (θ : Subst k Γ Δ) : CorecBranches k Δ → CorecBranches k Γ
  | .nil => .nil
  | .cons n m a v vs =>
    .cons n m a (v.subst (Subst.liftN a (Subst.liftN m (Subst.liftN n θ)))) (vs.subst θ)

end

/-- `[ā / Δ]`: the substitution that gives each parameter of `Δ` its argument in `ā`.
RFC: `\mathsf{params}_\theta` -/
def InstanceArgs.toSubst {Γ : Scope} : {Δ : Scope} → InstanceArgs k Γ Δ → Subst k Γ Δ
  | _, .snoc _ B, _, .zero => B
  | _, .snoc as _, _, .succ x => as.toSubst x

/-- `(θ, x̄. B)`: the substitution `θ` of the scope `Δ` followed by the abstraction `x̄. B` for a new
entry. -/
def Subst.snoc {Γ Δ : Scope} {e : Scope.Entry} (θ : Subst k Γ Δ)
    (B : Term k (Γ.extend e.params.length)) : Subst k Γ (e :: Δ) := fun x =>
  match x with
  | .zero => B
  | .succ x => θ x

/-- `x̄. t.(T.d)(x̄)`: the observation of the term `t` of the instance `T = D.{s̄; l̄; p̄} ā` by the
destructor `d`, as an abstraction over a variable for each of its arguments, whose parameters are
`ps'`. -/
def Term.observation {Γ Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (t : Term k Γ) (d : Name) (ps' : List Parameter) :
    Term k (Γ.extend ps'.length) :=
  .obs D qs ls ps (as.rename (Ren.weakenN ps'.length)) (t.rename (Ren.weakenN ps'.length)) d
    (Args.bound ps').terms

/-- `[ā / Δ, t.T / d̄₁]`: at the position of a destructor `d` in the destructors `d̄ = (d̄₁ | d | d̄₂)`
of the scope `Δ`, the substitution `θ = [ā / Δ]` of the scope, followed by the observation
`o d' = x̄. t.(T.d')(x̄)` of a term for each destructor `d'` of `d̄₁`, in the scope of the telescope
and of the result of `d`.
RFC: `\mathsf{obs}_\theta` -/
def Destructors.Pos.obsSubst {k' : Nat} {Γ' : Scope} {d : Name} {p q : Grade}
    {ps : List Parameter} (o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → Destructors.Pos d p q ds Ξ Θ B ψ → Subst k Γ' Γ →
        Subst k Γ' Ξ
  | _, _, _, _, _, _, _, .here, θ => θ
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') h, θ =>
    h.obsSubst o (Subst.snoc (e := .secondOrder ps' _) θ (o d' ps'))

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
  | .obs D qs ls ps as t d bs =>
    .obs D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') (t.substLevels ls') d
      (bs.substLevels ls')
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') (ss.substLevels ls')
      (Ss.substLevels ls') (vs.substLevels ls')

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
  | .cons n m es u us => .cons n m es (u.substLevels ls') (us.substLevels ls')

/-- The telescope `Θ` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\Theta` -/
def Telescope.substLevels {k' : Nat} {Γ : Scope} {ps : List Parameter} (ls' : Fin k → Level k') :
    Telescope k Γ ps → Telescope k' Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.substLevels ls') (Θ.substLevels ls')

/-- The states `Θ̄` in which the levels `ls'` replace the level variables, under the variables of
each state.
RFC: `\mathsf{inst}_l.\bar\Theta` -/
def States.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') : States k Γ → States k' Γ
  | .nil => .nil
  | .cons n S κs Ss =>
    .cons n (S.substLevels ls') (κs.map (Universe.substLevels ls')) (Ss.substLevels ls')

/-- The branches `ḡ` of a corecursor in which the levels `ls'` replace the level variables, under
the variables of each branch.
RFC: `\mathsf{inst}_l.\bar g` -/
def CorecBranches.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    CorecBranches k Γ → CorecBranches k' Γ
  | .nil => .nil
  | .cons n m a v vs => .cons n m a (v.substLevels ls') (vs.substLevels ls')

end

/-! ## Telescopes and Contexts -/

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

/-- The destructors `d̄` in which the levels `ls'` replace the level variables.
RFC: `\mathsf{inst}_l.\bar d` -/
def Destructors.substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    {ns : List Name} → Destructors k Γ ns → Destructors k' Γ ns
  | _, .nil => .nil
  | _, .cons p q Θ B ψ ds =>
    .cons p q (Θ.substLevels ls') (B.substLevels ls') ψ (ds.substLevels ls')

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, InstanceArgs.rename_id_of h as, Term.rename_id_of h t,
      Terms.rename_id_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, InstanceArgs.rename_id_of h as, Terms.rename_id_of h ss,
      States.rename_id_of h Ss, CorecBranches.rename_id_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.rename, Branches.rename_id_of h us, Term.rename_id_of (Ren.liftN_id_of _ (Ren.liftN_id_of _ h)) u]


theorem Telescope.rename_id_of {Γ : Scope} {ps : List Parameter}
    {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (Θ : Telescope k Γ ps) → Θ.rename ξ = Θ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.rename_id_of (Ren.lift_id_of h) Θ, Term.rename_id_of h A]

theorem States.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (Ss : States k Γ) → Ss.rename ξ = Ss
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.rename_id_of h Ss, Telescope.rename_id_of (Ren.liftN_id_of _ h) S]

theorem CorecBranches.rename_id_of {Γ : Scope} {ξ : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), ξ x = x) :
    (vs : CorecBranches k Γ) → vs.rename ξ = vs
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.rename_id_of h vs,
      Term.rename_id_of (Ren.liftN_id_of _ (Ren.liftN_id_of _ (Ren.liftN_id_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst₀, InstanceArgs.subst₀_id_of h as, Term.subst₀_id_of h t,
      Terms.subst₀_id_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst₀, InstanceArgs.subst₀_id_of h as, Terms.subst₀_id_of h ss,
      States.subst₀_id_of h Ss, CorecBranches.subst₀_id_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.subst₀_id_of h us, Term.subst₀_id_of (Subst₀.liftN_id_of _ (Subst₀.liftN_id_of _ h)) u]

/-- A substitution of the first order that renames each variable to itself changes no telescope.
RFC: `\mathsf{id}_\sigma.\Theta` -/
theorem Telescope.subst₀_id_of {Γ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Γ Γ} (h : ∀ {a} (x : Var Γ a), σ x = .var x) :
    (Θ : Telescope k Γ ps) → Θ.subst₀ σ = Θ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.subst₀_id_of (Subst₀.lift_id_of h) Θ, Term.subst₀_id_of h A]

theorem States.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (Ss : States k Γ) → Ss.subst₀ σ = Ss
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.subst₀_id_of h Ss, Telescope.subst₀_id_of (Subst₀.liftN_id_of _ h) S]

theorem CorecBranches.subst₀_id_of {Γ : Scope} {σ : Subst₀ k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), σ x = .var x) : (vs : CorecBranches k Γ) → vs.subst₀ σ = vs
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.subst₀_id_of h vs,
      Term.subst₀_id_of (Subst₀.liftN_id_of _ (Subst₀.liftN_id_of _ (Subst₀.liftN_id_of _ h))) v]

end

/-- The identity substitution of the first order changes nothing. -/
theorem Term.subst₀_id {Γ : Scope} (t : Term k Γ) : t.subst₀ Subst₀.id = t :=
  Term.subst₀_id_of (fun _ => rfl) t

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as,
      Term.rename_rename_of h t, Terms.rename_rename_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.rename, Term.rename, InstanceArgs.rename_rename_of h as,
      Terms.rename_rename_of h ss, States.rename_rename_of h Ss,
      CorecBranches.rename_rename_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.rename, Branches.rename, Branches.rename,
      Branches.rename_rename_of h us, Term.rename_rename_of (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ h)) u]


theorem Telescope.rename_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ} {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename ξ₂).rename ξ₁ = Θ.rename ξ₃
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.rename, Telescope.rename,
      Telescope.rename_rename_of (Ren.lift_comp_of h) Θ, Term.rename_rename_of h A]

theorem States.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (Ss : States k Ξ) → (Ss.rename ξ₂).rename ξ₁ = Ss.rename ξ₃
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.rename, States.rename,
      States.rename_rename_of h Ss, Telescope.rename_rename_of (Ren.liftN_comp_of _ h) S]

theorem CorecBranches.rename_rename_of {Γ Δ Ξ : Scope} {ξ₁ : Ren Γ Δ} {ξ₂ : Ren Δ Ξ}
    {ξ₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), ξ₁ (ξ₂ x) = ξ₃ x) :
    (vs : CorecBranches k Ξ) → (vs.rename ξ₂).rename ξ₁ = vs.rename ξ₃
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.rename, CorecBranches.rename,
      CorecBranches.rename_rename_of h vs,
      Term.rename_rename_of
        (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as,
      Term.subst₀_rename_of h t, Terms.subst₀_rename_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_rename_of h as,
      Terms.subst₀_rename_of h ss, States.subst₀_rename_of h Ss,
      CorecBranches.subst₀_rename_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst₀, Branches.subst₀,
      Branches.subst₀_rename_of h us, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ h)) u]


theorem Telescope.subst₀_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename ξ).subst₀ σ = Θ.subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst₀, Telescope.subst₀,
      Telescope.subst₀_rename_of (Subst₀.lift_rename_of h) Θ, Term.subst₀_rename_of h A]

theorem States.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (Ss : States k Ξ) → (Ss.rename ξ).subst₀ σ = Ss.subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst₀, States.subst₀,
      States.subst₀_rename_of h Ss, Telescope.subst₀_rename_of (Subst₀.liftN_rename_of _ h) S]

theorem CorecBranches.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (ξ x) = σ' x) :
    (vs : CorecBranches k Ξ) → (vs.rename ξ).subst₀ σ = vs.subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.subst₀, CorecBranches.subst₀,
      CorecBranches.subst₀_rename_of h vs,
      Term.subst₀_rename_of
        (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as,
      Term.rename_subst₀_of h t, Terms.rename_subst₀_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst₀, Term.rename, Term.subst₀, InstanceArgs.rename_subst₀_of h as,
      Terms.rename_subst₀_of h ss, States.rename_subst₀_of h Ss,
      CorecBranches.rename_subst₀_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.rename, Branches.subst₀,
      Branches.rename_subst₀_of h us,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ (Subst₀.liftN_rename_after_of _ h)) u]


theorem Telescope.rename_subst₀_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst₀ σ).rename ξ = Θ.subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.rename, Telescope.subst₀,
      Telescope.rename_subst₀_of (Subst₀.lift_rename_after_of h) Θ,
      Term.rename_subst₀_of h A]

theorem States.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (Ss : States k Ξ) → (Ss.subst₀ σ).rename ξ = Ss.subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.rename, States.subst₀,
      States.rename_subst₀_of h Ss,
      Telescope.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) S]

theorem CorecBranches.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {ξ : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename ξ = σ' x) :
    (vs : CorecBranches k Ξ) → (vs.subst₀ σ).rename ξ = vs.subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.rename, CorecBranches.subst₀,
      CorecBranches.rename_subst₀_of h vs,
      Term.rename_subst₀_of
        (Subst₀.liftN_rename_after_of _ (Subst₀.liftN_rename_after_of _
          (Subst₀.liftN_rename_after_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst₀, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_subst₀_of h as,
      Term.subst₀_subst₀_of h t, Terms.subst₀_subst₀_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst₀, Term.subst₀, Term.subst₀, InstanceArgs.subst₀_subst₀_of h as,
      Terms.subst₀_subst₀_of h ss, States.subst₀_subst₀_of h Ss,
      CorecBranches.subst₀_subst₀_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.subst₀, Branches.subst₀,
      Branches.subst₀_subst₀_of h us, Term.subst₀_subst₀_of (Subst₀.liftN_subst₀_of _ (Subst₀.liftN_subst₀_of _ h)) u]


theorem Telescope.subst₀_subst₀_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ} {σ' : Subst₀ k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst₀ σ).subst₀ τ = Θ.subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.subst₀, Telescope.subst₀,
      Telescope.subst₀_subst₀_of (Subst₀.lift_subst₀_of h) Θ, Term.subst₀_subst₀_of h A]

theorem States.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (Ss : States k Ξ) → (Ss.subst₀ σ).subst₀ τ = Ss.subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.subst₀, States.subst₀,
      States.subst₀_subst₀_of h Ss, Telescope.subst₀_subst₀_of (Subst₀.liftN_subst₀_of _ h) S]

theorem CorecBranches.subst₀_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {τ : Subst₀ k Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).subst₀ τ = σ' x) :
    (vs : CorecBranches k Ξ) → (vs.subst₀ σ).subst₀ τ = vs.subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.subst₀, CorecBranches.subst₀,
      CorecBranches.subst₀_subst₀_of h vs, Term.subst₀_subst₀_of
        (Subst₀.liftN_subst₀_of _ (Subst₀.liftN_subst₀_of _ (Subst₀.liftN_subst₀_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as,
      Term.subst_rename_of h t, Terms.subst_rename_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.subst, Term.subst, InstanceArgs.subst_rename_of h as,
      Terms.subst_rename_of h ss, States.subst_rename_of h Ss, CorecBranches.subst_rename_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst, Branches.subst,
      Branches.subst_rename_of h us, Term.subst_rename_of (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ h)) u]


theorem Telescope.subst_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ} {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename ξ).subst θ = Θ.subst θ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst, Telescope.subst,
      Telescope.subst_rename_of (Subst.lift_rename_of h) Θ, Term.subst_rename_of h A]

theorem States.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (Ss : States k Ξ) → (Ss.rename ξ).subst θ = Ss.subst θ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst, States.subst,
      States.subst_rename_of h Ss, Telescope.subst_rename_of (Subst.liftN_rename_of _ h) S]

theorem CorecBranches.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (ξ x) = θ' x) :
    (vs : CorecBranches k Ξ) → (vs.rename ξ).subst θ = vs.subst θ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.subst, CorecBranches.subst,
      CorecBranches.subst_rename_of h vs,
      Term.subst_rename_of
        (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as,
      Term.rename_subst_of h t, Terms.rename_subst_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst, Term.rename, Term.subst, InstanceArgs.rename_subst_of h as,
      Terms.rename_subst_of h ss, States.rename_subst_of h Ss, CorecBranches.rename_subst_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst, Branches.rename, Branches.subst,
      Branches.rename_subst_of h us, Term.rename_subst_of (Subst.liftN_rename_after_of _ (Subst.liftN_rename_after_of _ h)) u]


theorem Telescope.rename_subst_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ} {θ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst θ).rename ξ = Θ.subst θ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst, Telescope.rename, Telescope.subst,
      Telescope.rename_subst_of (Subst.lift_rename_after_of h) Θ, Term.rename_subst_of h A]

theorem States.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (Ss : States k Ξ) → (Ss.subst θ).rename ξ = Ss.subst θ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst, States.rename, States.subst,
      States.rename_subst_of h Ss, Telescope.rename_subst_of (Subst.liftN_rename_after_of _ h) S]

theorem CorecBranches.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {ξ : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length ξ) = θ' x) :
    (vs : CorecBranches k Ξ) → (vs.subst θ).rename ξ = vs.subst θ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst, CorecBranches.rename, CorecBranches.subst,
      CorecBranches.rename_subst_of h vs,
      Term.rename_subst_of
        (Subst.liftN_rename_after_of _ (Subst.liftN_rename_after_of _
          (Subst.liftN_rename_after_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as,
      Term.subst_subst₀_of h t, Terms.subst_subst₀_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst₀, Term.subst, Term.subst, Term.subst₀, InstanceArgs.subst_subst₀_of h as,
      Terms.subst_subst₀_of h ss, States.subst_subst₀_of h Ss, CorecBranches.subst_subst₀_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.subst, Branches.subst, Branches.subst₀,
      Branches.subst_subst₀_of h us, Term.subst_subst₀_of (Subst₀.Swaps.liftN _ (Subst₀.Swaps.liftN _ h)) u]


theorem Telescope.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ}
    (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (Θ : Telescope k Ξ ps) → (Θ.subst₀ σ).subst θ₁ = (Θ.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.subst, Telescope.subst, Telescope.subst₀,
      Telescope.subst_subst₀_of (Subst₀.Swaps.lift h) Θ, Term.subst_subst₀_of h A]

theorem States.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (Ss : States k Ξ) → (Ss.subst₀ σ).subst θ₁ = (Ss.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.subst, States.subst, States.subst₀,
      States.subst_subst₀_of h Ss, Telescope.subst_subst₀_of (Subst₀.Swaps.liftN _ h) S]

theorem CorecBranches.subst_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ}
    {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Ψ Ξ} {σ' : Subst₀ k Γ Ψ} (h : Subst₀.Swaps σ θ₁ θ₂ σ') :
    (vs : CorecBranches k Ξ) → (vs.subst₀ σ).subst θ₁ = (vs.subst θ₂).subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.subst, CorecBranches.subst, CorecBranches.subst₀,
      CorecBranches.subst_subst₀_of h vs,
      Term.subst_subst₀_of
        (Subst₀.Swaps.liftN _ (Subst₀.Swaps.liftN _ (Subst₀.Swaps.liftN _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as,
      Term.subst_subst_of h t, Terms.subst_subst_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst, Term.subst, Term.subst, InstanceArgs.subst_subst_of h as,
      Terms.subst_subst_of h ss, States.subst_subst_of h Ss, CorecBranches.subst_subst_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst, Branches.subst, Branches.subst,
      Branches.subst_subst_of h us, Term.subst_subst_of (Subst.liftN_subst_of _ (Subst.liftN_subst_of _ h)) u]

/-- Substituting a telescope by `θ₁` then by `θ₂` is substituting it by their composition `θ₃`.
RFC: `\mathsf{comp}_\theta.\Theta` -/
theorem Telescope.subst_subst_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ} {θ₃ : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst θ₁).subst θ₂ = Θ.subst θ₃
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst, Telescope.subst, Telescope.subst,
      Telescope.subst_subst_of (Subst.lift_subst_of h) Θ, Term.subst_subst_of h A]

theorem States.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (Ss : States k Ξ) → (Ss.subst θ₁).subst θ₂ = Ss.subst θ₃
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst, States.subst, States.subst,
      States.subst_subst_of h Ss, Telescope.subst_subst_of (Subst.liftN_subst_of _ h) S]

theorem CorecBranches.subst_subst_of {Γ Δ Ξ : Scope} {θ₁ : Subst k Δ Ξ} {θ₂ : Subst k Γ Δ}
    {θ₃ : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ₁ x).subst (Subst.liftN a.params.length θ₂) = θ₃ x) :
    (vs : CorecBranches k Ξ) → (vs.subst θ₁).subst θ₂ = vs.subst θ₃
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst, CorecBranches.subst, CorecBranches.subst,
      CorecBranches.subst_subst_of h vs,
      Term.subst_subst_of
        (Subst.liftN_subst_of _ (Subst.liftN_subst_of _ (Subst.liftN_subst_of _ h))) v]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst, InstanceArgs.subst_id_of h as, Term.subst_id_of h t, Terms.subst_id_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst, InstanceArgs.subst_id_of h as, Terms.subst_id_of h ss, States.subst_id_of h Ss,
      CorecBranches.subst_id_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst, Branches.subst_id_of h us, Term.subst_id_of (Subst.liftN_id_of _ (Subst.liftN_id_of _ h)) u]


theorem Telescope.subst_id_of {Γ : Scope} {ps : List Parameter}
    {θ : Subst k Γ Γ} (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) :
    (Θ : Telescope k Γ ps) → Θ.subst θ = Θ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst, Telescope.subst_id_of (Subst.lift_id_of h) Θ, Term.subst_id_of h A]

theorem States.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (Ss : States k Γ) → Ss.subst θ = Ss
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst, States.subst_id_of h Ss, Telescope.subst_id_of (Subst.liftN_id_of _ h) S]

theorem CorecBranches.subst_id_of {Γ : Scope} {θ : Subst k Γ Γ}
    (h : ∀ {a} (x : Var Γ a), θ x = Var.eta x) : (vs : CorecBranches k Γ) → vs.subst θ = vs
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst, CorecBranches.subst_id_of h vs,
      Term.subst_id_of (Subst.liftN_id_of _ (Subst.liftN_id_of _ (Subst.liftN_id_of _ h))) v]

end

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
theorem Telescope.subst_subst₀ {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Δ Ξ} {θ₁ : Subst k Γ Δ} {θ₂ : Subst k Γ Ξ}
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

/-! ### Variables for Variables

A substitution of the first order that gives each variable a variable, as a variable or as a term
for a variable, is the renaming that these variables make, which shows that the arguments `x̄` of the
new variables instantiate a term renamed under them as itself, so that `(x̄. x[x̄])[θ] = θ(x)`. -/

/-- The value `v` is the variable `y`, as a variable, or as a term for a variable. -/
inductive Val.IsVar {Γ : Scope} : {a : Scope.Entry} → Var Γ a → Val k Γ a → Prop where
  /-- The variable `y`. -/
  | var {a : Scope.Entry} (y : Var Γ a) : Val.IsVar y (.var y)
  /-- The term `y[]`. -/
  | term (y : Var Γ .var) : Val.IsVar y (.term (.var y .nil))

theorem Subst₀.lift_isVar {Γ Δ : Scope} {b : Scope.Entry} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) :
    ∀ {a} (x : Var (b :: Δ) a), (Subst₀.lift σ x).IsVar (Ren.lift ξ x)
  | _, .zero => .var _
  | _, .succ x => by
    show ((σ x).rename Ren.weaken).IsVar (Var.succ (ξ x))
    have hx := h x
    revert hx
    generalize σ x = v
    intro hx
    cases hx with
    | var => exact .var _
    | term => exact .term _

theorem Subst₀.liftN_isVar {Γ Δ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}, (∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) →
      ∀ {a} (x : Var (Δ.extend n) a), (Subst₀.liftN n σ x).IsVar (Ren.liftN n ξ x)
  | 0, _, _, h => h
  | n + 1, _, _, h => Subst₀.liftN_isVar (Γ := .var :: Γ) (Δ := .var :: Δ) n (Subst₀.lift_isVar h)

mutual

/-- A substitution that gives each variable a variable renames by them. -/
theorem Term.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (t : Term k Δ) → t.subst₀ σ = t.rename ξ
  | .var x ts => by
    rw [Term.subst₀_var, Term.rename]
    have hx := h x
    revert hx
    generalize σ x = v
    intro hx
    cases hx with
    | var => rw [Args.subst₀_isVar h ts]; rfl
    | term => cases ts; rfl
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.subst₀, InstanceArgs.subst₀_isVar h as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.subst₀, InstanceArgs.subst₀_isVar h as, Terms.subst₀_isVar h ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.subst₀, InstanceArgs.subst₀_isVar h as, Term.subst₀_isVar h t,
      Motives.subst₀_isVar h Cs, Branches.subst₀_isVar h us]
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.subst₀, InstanceArgs.subst₀_isVar h as, Term.subst₀_isVar h t,
      Terms.subst₀_isVar h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.subst₀, InstanceArgs.subst₀_isVar h as, Terms.subst₀_isVar h ss,
      States.subst₀_isVar h Ss, CorecBranches.subst₀_isVar h vs]

theorem Args.subst₀_isVar {Γ Δ : Scope} {a : List Parameter} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (ts : Args k Δ a) → ts.subst₀ σ = ts.rename ξ
  | .nil => rfl
  | .cons t ts => by rw [Args.rename, Args.subst₀, Term.subst₀_isVar h t, Args.subst₀_isVar h ts]

theorem InstanceArgs.subst₀_isVar {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) :
    (as : InstanceArgs k Δ Ξ) → as.subst₀ σ = as.rename ξ
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst₀, InstanceArgs.subst₀_isVar h as,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ h) B]

theorem Terms.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (ts : Terms k Δ) → ts.subst₀ σ = ts.rename ξ
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst₀, Terms.subst₀_isVar h ts, Term.subst₀_isVar h t]

theorem Motives.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (Cs : Motives k Δ) → Cs.subst₀ σ = Cs.rename ξ
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst₀, Motives.subst₀_isVar h Cs,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ h) C]

theorem Branches.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (us : Branches k Δ) → us.subst₀ σ = us.rename ξ
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst₀, Branches.subst₀_isVar h us,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ (Subst₀.liftN_isVar _ h)) u]

theorem Telescope.subst₀_isVar {Γ Δ : Scope} {ps : List Parameter} {σ : Subst₀ k Γ Δ}
    {ξ : Ren Γ Δ} (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) :
    (Θ : Telescope k Δ ps) → Θ.subst₀ σ = Θ.rename ξ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst₀, Telescope.subst₀_isVar (Subst₀.lift_isVar h) Θ,
      Term.subst₀_isVar h A]

theorem States.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) : (Ss : States k Δ) → Ss.subst₀ σ = Ss.rename ξ
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst₀, States.subst₀_isVar h Ss,
      Telescope.subst₀_isVar (Subst₀.liftN_isVar _ h) S]

theorem CorecBranches.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (ξ x)) :
    (vs : CorecBranches k Δ) → vs.subst₀ σ = vs.rename ξ
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.subst₀, CorecBranches.subst₀_isVar h vs,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ (Subst₀.liftN_isVar _ (Subst₀.liftN_isVar _ h))) v]

end

/-- A substitution of the first order under `n` new variables gives the new variables themselves. -/
theorem Subst₀.liftN_empty {Γ : Scope} :
    ∀ (n : Nat) (σ : Subst₀ k Γ []) {a : Scope.Entry} (z : Var (Scope.extend [] n) a),
      Subst₀.liftN n σ z = .var (Ren.liftN n Ren.empty z)
  | 0, _, _, z => nomatch z
  | n + 1, σ, _, z => by
    rcases Var.cases_extend (Γ := [.var]) n z with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · cases y with
      | zero =>
        show Subst₀.liftN n (Subst₀.lift σ) (Var.weakenN n .zero) =
          .var (Ren.liftN n (Ren.lift Ren.empty) (Var.weakenN n .zero))
        rw [Subst₀.liftN_weakenN, Ren.liftN_weakenN]
        rfl
      | succ y => nomatch y
    · show Subst₀.liftN n (Subst₀.lift σ) (Ren.liftN n Ren.empty z) =
        .var (Ren.liftN n (Ren.lift Ren.empty) (Ren.liftN n Ren.empty z))
      rw [Subst₀.liftN_rename_of n (σ' := fun y => Subst₀.lift σ (Ren.empty y)) (fun _ => rfl),
        Subst₀.liftN_empty (Γ := .var :: Γ) n _ z,
        Ren.liftN_comp_of n (ξ₃ := Ren.empty) (fun y => nomatch y) z]

/-- The arguments `x̄` of the new variables give, under them, the variable of a term renamed under
them. -/
theorem Args.bound_toSubst₀_isVar :
    (ps : List Parameter) → {Γ : Scope} → ∀ {a} (x : Var (Γ.extend ps.length) a),
      ((Args.bound (k := k) (Γ := Γ) ps).toSubst₀
        (Ren.liftN ps.length (Ren.weakenN ps.length) x)).IsVar x
  | [], _, _, _ => .var _
  | _ :: ps, Γ, a, x => by
    have key : ∀ x : Var (Scope.extend (.var :: Γ) ps.length) a,
        (Val.subst₀ (Args.bound (k := k) (Γ := .var :: Γ) ps).toSubst₀
          (Subst₀.liftN ps.length (Subst₀.single (.var₀ (Var.weakenN ps.length .zero)))
            (Ren.liftN ps.length (Ren.lift (Ren.weakenN (Γ := Γ) (ps.length + 1))) x))).IsVar x := by
      intro x
      rcases Var.cases_extend (Γ := .var :: Γ) ps.length x with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · erw [Ren.liftN_weakenN, Subst₀.liftN_weakenN]
        cases y with
        | zero =>
          have hv : Val.subst₀ (Args.bound (k := k) (Γ := .var :: Γ) ps).toSubst₀
              (Val.rename (Ren.weakenN ps.length)
                (Subst₀.single (Term.var₀ (Var.weakenN ps.length .zero))
                  (Ren.lift (Ren.weakenN (Γ := Γ) (ps.length + 1)) .zero))) =
              .term (.var (Var.weakenN ps.length .zero) .nil) := by
            show Val.term (((Term.var₀ (Var.weakenN ps.length .zero)).rename
              (Ren.weakenN ps.length)).subst₀ _) = _
            rw [Term.var₀, Term.rename, Term.subst₀_var, Ren.weakenN, Args.toSubst₀_weakenN]
            rfl
          rw [hv]
          exact .term _
        | succ y =>
          have hv : Val.subst₀ (Args.bound (k := k) (Γ := .var :: Γ) ps).toSubst₀
              (Val.rename (Ren.weakenN ps.length)
                (Subst₀.single (Term.var₀ (Var.weakenN ps.length .zero))
                  (Ren.lift (Ren.weakenN (Γ := Γ) (ps.length + 1)) (.succ y)))) =
              .var (Var.weakenN ps.length (Var.succ y)) := by
            show (Args.bound (k := k) (Γ := .var :: Γ) ps).toSubst₀
              (Var.weakenN ps.length (Var.weakenN ps.length (Var.succ y))) = _
            rw [Args.toSubst₀_weakenN]
          rw [hv]
          exact .var _
      · have hz : Ren.liftN ps.length (Ren.lift (Ren.weakenN (Γ := Γ) (ps.length + 1)))
            (Ren.liftN ps.length (Ren.empty (Γ := .var :: Γ)) z) =
            Ren.liftN ps.length Ren.empty z :=
          Ren.liftN_comp_of ps.length (ξ₃ := Ren.empty) (fun y => nomatch y) z
        erw [hz, Subst₀.liftN_rename_of ps.length
          (σ' := fun y => Subst₀.single (.var₀ (Var.weakenN ps.length .zero)) (Ren.empty y))
          (fun _ => rfl), Subst₀.liftN_empty]
        have := (Args.bound_toSubst₀_isVar ps (Γ := .var :: Γ) : _)
          (Ren.liftN ps.length Ren.empty z)
        rwa [Ren.liftN_comp_of ps.length (ξ₃ := Ren.empty) (fun y => nomatch y) z] at this
    exact key x

/-- `B[ξ⇑][x̄ / x̄] = B`: a term renamed under new variables, then instantiated by them, is itself. -/
theorem Term.instantiate_bound_rename {Γ : Scope} (ps : List Parameter)
    (B : Term k (Γ.extend ps.length)) :
    (B.rename (Ren.liftN ps.length (Ren.weakenN ps.length))).instantiate (Args.bound ps) = B := by
  rw [Term.instantiate_eq_subst₀, Term.subst₀_rename_of (fun _ => rfl),
    Term.subst₀_isVar (ξ := fun x => x) (Args.bound_toSubst₀_isVar ps), Term.rename_id]

/-- `(x̄. x[x̄])[θ⇑] = θ(x)`: the variable `x`, as an abstraction, substituted by `θ`, is what `θ` gives
it. -/
theorem Var.eta_subst {Γ Δ : Scope} {e : Scope.Entry} (θ : Subst k Γ Δ) (x : Var Δ e) :
    (Var.eta x).subst (Subst.liftN e.params.length θ) = θ x := by
  rw [Var.eta, Term.subst, Subst.liftN_weakenN, Args.bound_subst, Term.instantiate_bound_rename]

/-- `[x̄_Δ / Δ][θ]`: the parameters themselves, substituted by `θ`, give each parameter what `θ`
gives it. -/
theorem InstanceArgs.identity_subst {Γ : Scope} :
    {Δ : Scope} → (θ : Subst k Γ Δ) → ∀ {a} (x : Var Δ a),
      ((InstanceArgs.identity Δ).subst θ).toSubst x = θ x
  | _ :: _, θ, _, .zero => Var.eta_subst θ .zero
  | _ :: _, θ, _, .succ x => by
    show (((InstanceArgs.identity _).rename Ren.weaken).subst θ).toSubst x = θ x.succ
    rw [InstanceArgs.subst_rename_of (ξ := Ren.weaken) (θ' := fun y => θ y.succ) (fun _ => rfl)]
    exact InstanceArgs.identity_subst (fun y => θ y.succ) x

/-- Arguments of an instance with the same substitution are the same. -/
theorem InstanceArgs.toSubst_inj {Γ : Scope} :
    {Δ : Scope} → {as₁ as₂ : InstanceArgs k Γ Δ} → (∀ {a} (x : Var Δ a), as₁.toSubst x = as₂.toSubst x) →
      as₁ = as₂
  | [], .nil, .nil, _ => rfl
  | _ :: _, .snoc as₁ B₁, .snoc as₂ B₂, h => by
    have h₀ : B₁ = B₂ := h .zero
    rw [h₀, InstanceArgs.toSubst_inj fun x => h (.succ x)]

/-- `x̄_Δ[ā / Δ] = ā`: the parameters themselves, substituted by the arguments of an instance, are
these arguments. -/
theorem InstanceArgs.identity_subst_toSubst {Γ Δ : Scope} (as : InstanceArgs k Γ Δ) :
    (InstanceArgs.identity Δ).subst as.toSubst = as :=
  InstanceArgs.toSubst_inj fun x => InstanceArgs.identity_subst as.toSubst x

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
theorem Telescope.subst_lift_single {Γ : Scope} {ps : List Parameter}
    (σ : Subst k [] Γ) (v : Term k []) (Θ : Telescope k (.var :: Γ) ps) :
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
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' ξ as, Term.substLevels_rename ls' ξ t,
      Terms.substLevels_rename ls' ξ bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' ξ as, Terms.substLevels_rename ls' ξ ss,
      States.substLevels_rename ls' ξ Ss, CorecBranches.substLevels_rename ls' ξ vs]

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
  | .cons n m es u us => by
    rw [Branches.rename, Branches.substLevels, Branches.substLevels, Branches.rename,
      Branches.substLevels_rename ls' ξ us, Term.substLevels_rename]


theorem Telescope.substLevels_rename {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    (ls' : Fin k → Level k') (ξ : Ren Γ Δ) :
    (Θ : Telescope k Δ ps) → (Θ.rename ξ).substLevels ls' = (Θ.substLevels ls').rename ξ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.substLevels, Telescope.substLevels, Telescope.rename,
      Telescope.substLevels_rename ls' (Ren.lift ξ) Θ, Term.substLevels_rename]

/-- The levels of renamed destructors are instantiated as those of the destructors. -/
theorem Destructors.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    {ns : List Name} → (ds : Destructors k Δ ns) →
      (ds.rename ξ).substLevels ls' = (ds.substLevels ls').rename ξ
  | _, .nil => rfl
  | _, .cons p q Θ B ψ ds => by
    rw [Destructors.rename, Destructors.substLevels, Destructors.substLevels, Destructors.rename,
      Destructors.substLevels_rename ls' (Ren.lift ξ) ds, Telescope.substLevels_rename,
      Term.substLevels_rename]

theorem States.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (Ss : States k Δ) → (Ss.rename ξ).substLevels ls' = (Ss.substLevels ls').rename ξ
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.substLevels, States.substLevels, States.rename,
      States.substLevels_rename ls' ξ Ss, Telescope.substLevels_rename]

theorem CorecBranches.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (ξ : Ren Γ Δ) :
    (vs : CorecBranches k Δ) → (vs.rename ξ).substLevels ls' = (vs.substLevels ls').rename ξ
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.substLevels, CorecBranches.substLevels,
      CorecBranches.rename,
      CorecBranches.substLevels_rename ls' ξ vs, Term.substLevels_rename]

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst₀, Term.substLevels, Term.substLevels, Term.subst₀,
      InstanceArgs.substLevels_subst₀_of h as, Term.substLevels_subst₀_of h t,
      Terms.substLevels_subst₀_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst₀, Term.substLevels, Term.substLevels, Term.subst₀,
      InstanceArgs.substLevels_subst₀_of h as, Terms.substLevels_subst₀_of h ss,
      States.substLevels_subst₀_of h Ss, CorecBranches.substLevels_subst₀_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.substLevels, Branches.substLevels,
      Branches.subst₀, Branches.substLevels_subst₀_of h us,
      Term.substLevels_subst₀_of (Subst₀.liftN_substLevels_of _ (Subst₀.liftN_substLevels_of _ h)) u]

/-- The instantiation of the level variables of a telescope commutes with the substitutions of the
first order.
RFC: `\mathsf{comm}_{l\sigma}.\Theta` -/
theorem Telescope.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ls' : Fin k → Level k'} {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (Θ : Telescope k Δ ps) → (Θ.subst₀ σ).substLevels ls' = (Θ.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.substLevels, Telescope.substLevels,
      Telescope.subst₀, Telescope.substLevels_subst₀_of (Subst₀.lift_substLevels_of h) Θ,
      Term.substLevels_subst₀_of h A]

theorem States.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (Ss : States k Δ) → (Ss.subst₀ σ).substLevels ls' = (Ss.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.substLevels, States.substLevels,
      States.subst₀, States.substLevels_subst₀_of h Ss,
      Telescope.substLevels_subst₀_of (Subst₀.liftN_substLevels_of _ h) S]

theorem CorecBranches.substLevels_subst₀_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {σ : Subst₀ k Γ Δ} {σ' : Subst₀ k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).substLevels ls' = σ' x) :
    (vs : CorecBranches k Δ) → (vs.subst₀ σ).substLevels ls' = (vs.substLevels ls').subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.substLevels, CorecBranches.substLevels,
      CorecBranches.subst₀, CorecBranches.substLevels_subst₀_of h vs,
      Term.substLevels_subst₀_of
        (Subst₀.liftN_substLevels_of _ (Subst₀.liftN_substLevels_of _
          (Subst₀.liftN_substLevels_of _ h))) v]

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

/-- Instantiating the level variables of a sort by `ls₁` then by `ls₂` is instantiating them by their
composition. -/
theorem Universe.substLevels_substLevels {k' k'' : Nat} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') (κ : Universe k) :
    (κ.substLevels ls₁).substLevels ls₂ = κ.substLevels fun i => (ls₁ i).subst ls₂ := by
  simp only [Universe.substLevels, Level.subst_subst]

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
  | .obs D qs ls ps as t d bs => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as, Term.substLevels_substLevels ls₁ ls₂ t,
      Terms.substLevels_substLevels ls₁ ls₂ bs]
  | .corec r D qs ls ps as ss Ss vs => by
    simp only [Term.substLevels, List.map_map, Function.comp_def, Level.subst_subst,
      InstanceArgs.substLevels_substLevels ls₁ ls₂ as, Terms.substLevels_substLevels ls₁ ls₂ ss,
      States.substLevels_substLevels ls₁ ls₂ Ss, CorecBranches.substLevels_substLevels ls₁ ls₂ vs]

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
  | .cons n m es u us => by
    rw [Branches.substLevels, Branches.substLevels, Branches.substLevels,
      Branches.substLevels_substLevels ls₁ ls₂ us, Term.substLevels_substLevels ls₁ ls₂ u]

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
      Telescope.substLevels_substLevels ls₁ ls₂ Θ, Term.substLevels_substLevels ls₁ ls₂ A]

theorem States.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (Ss : States k Γ) →
      (Ss.substLevels ls₁).substLevels ls₂ = Ss.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.substLevels, States.substLevels, States.substLevels,
      States.substLevels_substLevels ls₁ ls₂ Ss, Telescope.substLevels_substLevels ls₁ ls₂ S,
      List.map_map]
    simp only [Function.comp_def, Universe.substLevels_substLevels]

theorem CorecBranches.substLevels_substLevels {k' k'' : Nat} {Γ : Scope} (ls₁ : Fin k → Level k')
    (ls₂ : Fin k' → Level k'') :
    (vs : CorecBranches k Γ) →
      (vs.substLevels ls₁).substLevels ls₂ = vs.substLevels fun i => (ls₁ i).subst ls₂
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.substLevels, CorecBranches.substLevels, CorecBranches.substLevels,
      CorecBranches.substLevels_substLevels ls₁ ls₂ vs, Term.substLevels_substLevels ls₁ ls₂ v]

end

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

/-- The parameters themselves have no level. -/
theorem InstanceArgs.identity_substLevels {k' : Nat} (ls' : Fin k → Level k') :
    (Δ : Scope) → (InstanceArgs.identity (k := k) Δ).substLevels ls' = InstanceArgs.identity Δ
  | [] => rfl
  | _ :: Δ => by
    rw [InstanceArgs.identity, InstanceArgs.substLevels, InstanceArgs.substLevels_rename,
      InstanceArgs.identity_substLevels ls' Δ, Var.eta_substLevels]
    rfl

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
  | .obs D qs ls ps as t d bs => by
    rw [Term.subst, Term.substLevels, Term.substLevels, Term.subst,
      InstanceArgs.substLevels_subst_of h as, Term.substLevels_subst_of h t,
      Terms.substLevels_subst_of h bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.subst, Term.substLevels, Term.substLevels, Term.subst,
      InstanceArgs.substLevels_subst_of h as, Terms.substLevels_subst_of h ss,
      States.substLevels_subst_of h Ss, CorecBranches.substLevels_subst_of h vs]

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
  | .cons n m es u us => by
    rw [Branches.subst, Branches.substLevels, Branches.substLevels,
      Branches.subst, Branches.substLevels_subst_of h us,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ (Subst.liftN_substLevels_of _ h)) u]

/-- The instantiation of the level variables of a telescope commutes with the substitutions of the
second order.
RFC: `\mathsf{comm}_{l\theta}.\Theta` -/
theorem Telescope.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {ls' : Fin k → Level k'} {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (Θ : Telescope k Δ ps) → (Θ.subst θ).substLevels ls' = (Θ.substLevels ls').subst θ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst, Telescope.substLevels, Telescope.substLevels,
      Telescope.subst, Telescope.substLevels_subst_of (Subst.lift_substLevels_of h) Θ,
      Term.substLevels_subst_of h A]

theorem States.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (Ss : States k Δ) → (Ss.subst θ).substLevels ls' = (Ss.substLevels ls').subst θ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst, States.substLevels, States.substLevels,
      States.subst, States.substLevels_subst_of h Ss,
      Telescope.substLevels_subst_of (Subst.liftN_substLevels_of _ h) S]

theorem CorecBranches.substLevels_subst_of {k' : Nat} {Γ Δ : Scope} {ls' : Fin k → Level k'}
    {θ : Subst k Γ Δ} {θ' : Subst k' Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (θ x).substLevels ls' = θ' x) :
    (vs : CorecBranches k Δ) → (vs.subst θ).substLevels ls' = (vs.substLevels ls').subst θ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst, CorecBranches.substLevels, CorecBranches.substLevels,
      CorecBranches.subst, CorecBranches.substLevels_subst_of h vs,
      Term.substLevels_subst_of
        (Subst.liftN_substLevels_of _ (Subst.liftN_substLevels_of _
          (Subst.liftN_substLevels_of _ h))) v]

end

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

/-- A constructor applied to arguments, substituted, is the constructor applied to the arguments
substituted. -/
theorem Term.ctor_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ) (c : Name)
    {ps' : List Parameter} (ts : Args k Δ ps') :
    (Term.ctor D qs ls ps as c ts.terms).subst θ = .ctor D qs ls ps (as.subst θ) c (ts.subst θ).terms := by
  rw [Args.terms_subst]
  rfl

/-- An observation applied to arguments, substituted, is the observation of the term substituted
applied to the arguments substituted. -/
theorem Term.obs_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ) (t : Term k Δ) (d : Name)
    {ps' : List Parameter} (bs : Args k Δ ps') :
    (Term.obs D qs ls ps as t d bs.terms).subst θ =
      .obs D qs ls ps (as.subst θ) (t.subst θ) d (bs.subst θ).terms := by
  rw [Args.terms_subst]
  rfl

/-- A corecursor from a state, substituted, is the corecursor substituted from the state
substituted. -/
theorem Term.corec_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    {ps' : List Parameter} (ss : Args k Δ ps') (Ss : States k Δ) (gs : CorecBranches k Δ) :
    (Term.corec r D qs ls ps as ss.terms Ss gs).subst θ =
      .corec r D qs ls ps (as.subst θ) (ss.subst θ).terms (Ss.subst θ) (gs.subst θ) := by
  rw [Args.terms_subst]
  rfl

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

-- ADE: none.
/-- `corec_r T from ȳ return Θ̄ with ḡ`: the corecursor of the instance `T = D.{s̄; l̄; p̄} ā` at the
new variables `ȳ` of a state, whose entries have the parameters `ps`, as its state, the term whose
observations the types of the branches of the type `D` observe. -/
def Term.corecAt {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (Ss : States k Γ) (gs : CorecBranches k Γ)
    (ps' : List Parameter) : Term k (Γ.extend ps'.length) :=
  .corec r D qs ls ps (as.rename (Ren.weakenN ps'.length)) (Args.bound ps').terms
    (Ss.rename (Ren.weakenN ps'.length)) (gs.rename (Ren.weakenN ps'.length))

/-! ## Recursive Results -/

-- ADE: none.
/-- `res_C̄(x̄)`: the recursive results of the fields `x̄`, whose entries have the parameters `ps` and
whose recursive fields the types `rs` of the block whose names are `names` mark, a variable
`y : C_D[x / z]` for each recursive field `x` of the type `D`, at the motive `C_D` of `D` in `C̄`,
in order, if `C̄` has a motive without non-uniform parameters for each of these types.
RFC: `\mathsf{results}` -/
def Motives.results (names : List Name) : {Δ : Scope} → Motives k Δ → (rs : List (Option Name)) →
    {ps : List Parameter} → Terms k Δ → Option (Telescope k Δ (Telescope.resultParams rs ps))
  | _, Cs, some D :: rs, p :: ps, .cons x xs =>
    match Cs.get (names.idxOf D) with
    | some ⟨0, C⟩ => (Motives.results names (Cs.rename Ren.weaken) rs (ps := ps)
        (xs.rename Ren.weaken)).map (Telescope.cons Grade.zero p (C.subst₀ (Subst₀.single x)))
    | _ => none
  | _, Cs, none :: rs, _ :: ps, .cons _ xs => Motives.results names Cs rs (ps := ps) xs
  | _, _, some _ :: _, _ :: _, .nil | _, _, none :: _, _ :: _, .nil => none
  | _, _, [], _, _ | _, _, some _ :: _, [], _ | _, _, none :: _, [], _ => some .nil

-- ADE: none.
/-- `f(D, t̄)`: the term `f D t` for each term `t` of a recursive field of the type `D` that the types
`rs` of the block mark, in order: the recursive results of a recursor at the terms of the fields of
a constructor, `f D t` being the recursor on `t` at the type `D`.
RFC: `\mathsf{results}_t` -/
def Terms.results {Γ : Scope} (f : Name → Term k Γ → Term k Γ) : List (Option Name) → Terms k Γ → Terms k Γ
  | some D :: rs, .cons t ts => .cons (f D t) (Terms.results f rs ts)
  | none :: rs, .cons _ ts => Terms.results f rs ts
  | [], _ | _ :: _, .nil => .nil

-- ADE: none.
/-- `f(D, t̄)` for the arguments `t̄` of a telescope whose entries have the parameters `ps`: the
arguments of the recursive results, as `Terms.results` gives their terms. -/
def Args.results {Γ : Scope} (f : Name → Term k Γ → Term k Γ) :
    (rs : List (Option Name)) → {ps : List Parameter} → Args k Γ ps →
      Args k Γ (Telescope.resultParams rs ps)
  | some D :: rs, _ :: _, .cons t ts => .cons (f D t) (Args.results f rs ts)
  | none :: rs, _ :: _, .cons _ ts => Args.results f rs ts
  | [], _, _ | some _ :: _, [], .nil | none :: _, [], .nil => .nil

/-- The terms of the arguments of the recursive results are the recursive results of the terms. -/
theorem Args.results_terms {Γ : Scope} (f : Name → Term k Γ → Term k Γ) :
    (rs : List (Option Name)) → {ps : List Parameter} → (ts : Args k Γ ps) →
      (Args.results f rs ts).terms = Terms.results f rs ts.terms
  | some _ :: rs, _ :: _, .cons _ ts => congrArg _ (Args.results_terms f rs ts)
  | none :: rs, _ :: _, .cons _ ts => Args.results_terms f rs ts
  | [], [], .nil | [], _ :: _, .cons _ _ | some _ :: _, [], .nil | none :: _, [], .nil => rfl

-- ADE: none.
/-- `res_C̄(Θ_c)`: the recursive results of the fields of the constructor `c` at the instance `I`, in
a block whose types have the names `names`, in the scope `Γ` extended by its fields, for the motives
`C̄` in `Γ`. -/
def Constructor.results {j g k' : Nat} {Δ Γ : Scope} (c : Constructor j g k' Δ) (I : Instance j g)
    (names : List Name) (Cs : Motives k Γ) :
    Option (Telescope k (Γ.extend (c.params I).length) (c.resultParams I names)) :=
  Motives.results names (Cs.rename (Ren.weakenN _)) ((c.fields I).recursion names)
    (Args.bound (Γ := Γ) (c.params I)).terms

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
    {us : Branches k Δ} → {i n m : Nat} → {u : Term k ((Δ.extend n).extend m)} →
      us.get i = some ⟨n, m, u⟩ →
        (us.subst θ).get i = some ⟨n, m, u.subst (Subst.liftN m (Subst.liftN n θ))⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ us, _ + 1, _, _, _, h => Branches.get_subst θ (us := us) h

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
    {us : Branches k Γ} → {i n m : Nat} → {u : Term k' ((Γ.extend n).extend m)} →
      (us.substLevels ls').get i = some ⟨n, m, u⟩ →
        ∃ u₀, us.get i = some ⟨n, m, u₀⟩ ∧ u = u₀.substLevels ls'
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ us, _ + 1, _, _, _, h => Branches.get_substLevels ls' (us := us) h

/-- The branch at a position of branches is there once their levels are instantiated. -/
theorem Branches.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {us : Branches k Γ} → {i n m : Nat} → {u : Term k ((Γ.extend n).extend m)} →
      us.get i = some ⟨n, m, u⟩ → (us.substLevels ls').get i = some ⟨n, m, u.substLevels ls'⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ us, _ + 1, _, _, _, h => Branches.get_substLevels_of ls' (us := us) h

/-! ## Recursive Results Substituted -/

/-- A term renamed under a new entry, substituted under it, is the term substituted, renamed under
it. -/
theorem Term.subst_lift_rename_weaken {Γ Δ : Scope} {e : Scope.Entry} (θ : Subst k Γ Δ)
    (t : Term k Δ) :
    (t.rename (Ren.weaken (e := e))).subst (Subst.lift θ) = (t.subst θ).rename Ren.weaken :=
  (Term.subst_rename_of (fun _ => rfl) t).trans (Term.rename_subst_of (fun _ => rfl) t).symm

/-- A telescope renamed under a new entry, substituted under it, is the telescope substituted,
renamed under it. -/
theorem Telescope.subst_lift_rename_weaken {Γ Δ : Scope} {e : Scope.Entry} {ps : List Parameter}
    (θ : Subst k Γ Δ) (Θ : Telescope k Δ ps) :
    (Θ.rename (Ren.weaken (e := e))).subst (Subst.lift θ) = (Θ.subst θ).rename Ren.weaken :=
  (Telescope.subst_rename_of (fun _ => rfl) Θ).trans
    (Telescope.rename_subst_of (fun _ => rfl) Θ).symm

/-- A term renamed under a new entry before `n` variables, substituted under them, is the term
substituted, renamed under them. -/
theorem Term.subst_liftN_lift_rename_weaken {Γ Δ : Scope} {e : Scope.Entry} (n : Nat)
    (θ : Subst k Γ Δ) (t : Term k (Δ.extend n)) :
    (t.rename (Ren.liftN n (Ren.weaken (e := e)))).subst (Subst.liftN n (Subst.lift θ)) =
      (t.subst (Subst.liftN n θ)).rename (Ren.liftN n Ren.weaken) :=
  (Term.subst_rename_of (Subst.liftN_rename_comm_of n (θ₁ := Subst.lift θ) (ξ₁ := Ren.weaken)
    (θ₂ := θ) (ξ₂ := Ren.weaken) fun _ => rfl) t).trans
    (Term.rename_subst_of (fun _ => rfl) t).symm

/-- Motives renamed under a new variable, substituted under it, are the motives substituted, renamed
under it. -/
theorem Motives.subst_lift_rename_weaken {Γ Δ : Scope} (θ : Subst k Γ Δ) (Cs : Motives k Δ) :
    (Cs.rename (Ren.weaken (e := .var))).subst (Subst.lift θ) = (Cs.subst θ).rename Ren.weaken :=
  (Motives.subst_rename_of (fun _ => rfl) Cs).trans (Motives.rename_subst_of (fun _ => rfl) Cs).symm

/-- Terms renamed under a new variable, substituted under it, are the terms substituted, renamed
under it. -/
theorem Terms.subst_lift_rename_weaken {Γ Δ : Scope} (θ : Subst k Γ Δ) (ts : Terms k Δ) :
    (ts.rename (Ren.weaken (e := .var))).subst (Subst.lift θ) = (ts.subst θ).rename Ren.weaken :=
  (Terms.subst_rename_of (fun _ => rfl) ts).trans (Terms.rename_subst_of (fun _ => rfl) ts).symm

/-- The recursive results of terms, substituted, are those of the terms substituted, at the motives
substituted. -/
theorem Motives.results_subst (names : List Name) :
    {Γ Δ : Scope} → (θ : Subst k Γ Δ) → {Cs : Motives k Δ} → (rs : List (Option Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} → {R : Telescope k Δ (Telescope.resultParams rs ps)} →
      Motives.results names Cs rs xs = some R →
        Motives.results names (Cs.subst θ) rs (xs.subst θ) = some (R.subst θ)
  | _, _, θ, Cs, some D :: rs, p :: ps, .cons x xs, R, h => by
    unfold Motives.results at h
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at h; cases h
    | some a =>
      obtain ⟨n, C⟩ := a
      cases n with
      | succ => simp only [hC] at h; cases h
      | zero =>
        simp only [hC] at h
        obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 h
        have ih := Motives.results_subst names (Subst.lift θ) rs hR'
        rw [Motives.subst_lift_rename_weaken, Terms.subst_lift_rename_weaken] at ih
        unfold Motives.results
        simp only [Terms.subst, Motives.get_subst θ hC]
        simp only [ih, Telescope.subst]
        rw [Term.subst_subst₀_of (Subst₀.Swaps.single x θ) C]
        rfl
  | _, _, θ, Cs, none :: rs, _ :: ps, .cons _ xs, R, h => by
    unfold Motives.results at h ⊢
    exact Motives.results_subst names θ rs h
  | _, _, _, _, some _ :: _, _ :: _, .nil, _, h | _, _, _, _, none :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, _, _, [], _, _, R, h | _, _, _, _, some _ :: _, [], _, R, h
  | _, _, _, _, none :: _, [], _, R, h => by
    unfold Motives.results at h ⊢
    cases h
    rfl

/-- The recursive results of terms whose levels are instantiated are those of the terms, at the
motives, instantiated. -/
theorem Motives.results_substLevels {k' : Nat} (ls' : Fin k → Level k') (names : List Name) :
    {Δ : Scope} → {Cs : Motives k Δ} → (rs : List (Option Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} → {R : Telescope k Δ (Telescope.resultParams rs ps)} →
      Motives.results names Cs rs xs = some R →
        Motives.results names (Cs.substLevels ls') rs (xs.substLevels ls') =
          some (R.substLevels ls')
  | _, Cs, some D :: rs, p :: ps, .cons x xs, R, h => by
    unfold Motives.results at h
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at h; cases h
    | some a =>
      obtain ⟨n, C⟩ := a
      cases n with
      | succ => simp only [hC] at h; cases h
      | zero =>
        simp only [hC] at h
        obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 h
        have ih := Motives.results_substLevels ls' names rs hR'
        rw [Motives.substLevels_rename, Terms.substLevels_rename] at ih
        unfold Motives.results
        simp only [Terms.substLevels, Motives.get_substLevels_of ls' hC]
        simp only [ih, Telescope.substLevels]
        rw [Term.substLevels_subst₀_of (σ := Subst₀.single x)
          (σ' := Subst₀.single (x.substLevels ls')) (fun y => by cases y <;> rfl) C]
        rfl
  | _, Cs, none :: rs, _ :: ps, .cons _ xs, R, h => by
    unfold Motives.results at h ⊢
    exact Motives.results_substLevels ls' names rs h
  | _, _, some _ :: _, _ :: _, .nil, _, h | _, _, none :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, [], _, _, R, h | _, _, some _ :: _, [], _, R, h
  | _, _, none :: _, [], _, R, h => by
    unfold Motives.results at h ⊢
    cases h
    rfl

/-- The arguments of recursive results whose levels are instantiated are those of the arguments
instantiated, by functions that commute with the instantiation. -/
theorem Args.results_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {f : Name → Term k Γ → Term k Γ} {f' : Name → Term k' Γ → Term k' Γ}
    (hf : ∀ D t, (f D t).substLevels ls' = f' D (t.substLevels ls')) :
    (rs : List (Option Name)) → {ps : List Parameter} → (ts : Args k Γ ps) →
      (ts.results f rs).substLevels ls' = (ts.substLevels ls').results f' rs
  | some D :: rs, _ :: _, .cons t ts => by
    show Args.cons ((f D t).substLevels ls') ((ts.results f rs).substLevels ls') = _
    rw [hf, Args.results_substLevels ls' hf rs ts]
    rfl
  | none :: rs, _ :: _, .cons _ ts => Args.results_substLevels ls' hf rs ts
  | [], [], .nil | [], _ :: _, .cons _ _ | some _ :: _, [], .nil | none :: _, [], .nil => rfl

/-- Recursive results of terms whose levels are instantiated, at the motives instantiated, are those
of the terms, instantiated. -/
theorem Motives.results_substLevels_inv {k' : Nat} (ls' : Fin k → Level k') (names : List Name) :
    {Δ : Scope} → {Cs : Motives k Δ} → (rs : List (Option Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} →
      {R' : Telescope k' Δ (Telescope.resultParams rs ps)} →
      Motives.results names (Cs.substLevels ls') rs (xs.substLevels ls') = some R' →
        ∃ R, Motives.results names Cs rs xs = some R ∧ R' = R.substLevels ls'
  | _, Cs, some D :: rs, p :: ps, .cons x xs, R', h => by
    unfold Motives.results at h
    simp only [Terms.substLevels] at h
    cases hC' : (Cs.substLevels ls').get (names.idxOf D) with
    | none => simp only [hC'] at h; cases h
    | some a =>
      obtain ⟨n, C'⟩ := a
      cases n with
      | succ => simp only [hC'] at h; cases h
      | zero =>
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        simp only [hC'] at h
        obtain ⟨R'', hR'', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [← Motives.substLevels_rename, ← Terms.substLevels_rename] at hR''
        obtain ⟨R₀, hR₀, rfl⟩ := Motives.results_substLevels_inv ls' names rs hR''
        refine ⟨.cons Grade.zero p (C₀.subst₀ (Subst₀.single x)) R₀, ?_, ?_⟩
        · unfold Motives.results
          simp only [hC₀, hR₀]
          rfl
        · show Telescope.cons Grade.zero p _ _ = Telescope.cons Grade.zero p _ _
          rw [Term.substLevels_subst₀_of (σ := Subst₀.single x)
            (σ' := Subst₀.single (x.substLevels ls')) (fun y => by cases y <;> rfl) C₀]
          rfl
  | _, Cs, none :: rs, _ :: ps, .cons _ xs, R', h => by
    unfold Motives.results at h ⊢
    exact Motives.results_substLevels_inv ls' names rs h
  | _, _, some _ :: _, _ :: _, .nil, _, h | _, _, none :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, [], _, _, R', h | _, _, some _ :: _, [], _, R', h
  | _, _, none :: _, [], _, R', h => by
    unfold Motives.results at h
    cases h
    exact ⟨.nil, by unfold Motives.results; rfl, rfl⟩

/-- The recursive results of a constructor at motives whose levels are instantiated are its
recursive results at the motives, instantiated. -/
theorem Constructor.results_substLevels_inv {k' : Nat} (ls' : Fin k → Level k') {j g k'' : Nat}
    {Δ Γ : Scope} {c : Constructor j g k'' Δ} {I : Instance j g} {names : List Name}
    {Cs : Motives k Γ} {R' : Telescope k' (Γ.extend (c.params I).length) (c.resultParams I names)}
    (h : c.results I names (Cs.substLevels ls') = some R') :
    ∃ R, c.results I names Cs = some R ∧ R' = R.substLevels ls' := by
  unfold Constructor.results at h ⊢
  rw [← Motives.substLevels_rename, ← Args.substLevels_bound ls' (c.params I),
    Args.terms_substLevels] at h
  exact Motives.results_substLevels_inv ls' names _ h

/-- Motives whose levels are instantiated are as many. -/
theorem Motives.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (Cs : Motives k Γ) → (Cs.substLevels ls').length = Cs.length
  | .nil => rfl
  | .cons _ _ Cs => congrArg (· + 1) (Motives.length_substLevels ls' Cs)

/-- Branches whose levels are instantiated are as many. -/
theorem Branches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (us : Branches k Γ) → (us.substLevels ls').length = us.length
  | .nil => rfl
  | .cons _ _ _ _ us => congrArg (· + 1) (Branches.length_substLevels ls' us)

/-- The branch at a position of the branches of a corecursor substituted is the branch
substituted, under its variables. -/
theorem CorecBranches.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {vs : CorecBranches k Δ} → {i n m a : Nat} → {v : Term k (((Δ.extend n).extend m).extend a)} →
      vs.get i = some ⟨n, m, a, v⟩ →
        (vs.subst θ).get i =
          some ⟨n, m, a, v.subst (Subst.liftN a (Subst.liftN m (Subst.liftN n θ)))⟩
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => CorecBranches.get_subst θ (vs := vs) h

/-- The state at a position of states substituted is the state substituted, under its
variables. -/
theorem States.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Ss : States k Δ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k (Δ.extend n) ps} →
      Ss.get j = some ⟨n, ps, S⟩ → (Ss.subst θ).get j = some ⟨n, ps, S.subst (Subst.liftN n θ)⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_subst θ (Ss := Ss) h

/-- The branch at a position of the branches of a corecursor whose levels are instantiated is a
branch of the branches, instantiated. -/
theorem CorecBranches.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {vs : CorecBranches k Γ} → {i n m a : Nat} → {v : Term k' (((Γ.extend n).extend m).extend a)} →
      (vs.substLevels ls').get i = some ⟨n, m, a, v⟩ →
        ∃ v₀, vs.get i = some ⟨n, m, a, v₀⟩ ∧ v = v₀.substLevels ls'
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => CorecBranches.get_substLevels ls' (vs := vs) h

/-- The branch at a position of the branches of a corecursor is there once their levels are
instantiated. -/
theorem CorecBranches.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {vs : CorecBranches k Γ} → {i n m a : Nat} → {v : Term k (((Γ.extend n).extend m).extend a)} →
      vs.get i = some ⟨n, m, a, v⟩ → (vs.substLevels ls').get i = some ⟨n, m, a, v.substLevels ls'⟩
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => CorecBranches.get_substLevels_of ls' (vs := vs) h

/-- The state at a position of states whose levels are instantiated is a state of the states,
instantiated. -/
theorem States.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {Ss : States k Γ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k' (Γ.extend n) ps} →
      (Ss.substLevels ls').get j = some ⟨n, ps, S⟩ →
        ∃ S₀, Ss.get j = some ⟨n, ps, S₀⟩ ∧ S = S₀.substLevels ls'
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_substLevels ls' (Ss := Ss) h

/-- The state at a position of states is there once their levels are instantiated. -/
theorem States.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {Ss : States k Γ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k (Γ.extend n) ps} →
      Ss.get j = some ⟨n, ps, S⟩ → (Ss.substLevels ls').get j = some ⟨n, ps, S.substLevels ls'⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_substLevels_of ls' (Ss := Ss) h

/-- The branches of a corecursor whose levels are instantiated are as many. -/
theorem CorecBranches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (vs : CorecBranches k Γ) → (vs.substLevels ls').length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (CorecBranches.length_substLevels ls' vs)

/-- The states of a corecursor whose levels are instantiated are as many. -/
theorem States.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (Ss : States k Γ) → (Ss.substLevels ls').length = Ss.length
  | .nil => rfl
  | .cons _ _ _ Ss => congrArg (· + 1) (States.length_substLevels ls' Ss)

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

/-! ## Observations -/

/-- The observation of a term, substituted under the variables of its arguments, is the observation
of the term substituted. -/
theorem Term.observation_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ) (t : Term k Δ) (d : Name)
    (ps' : List Parameter) :
    (t.observation D qs ls ps as d ps').subst (Subst.liftN ps'.length θ) =
      (t.subst θ).observation D qs ls ps (as.subst θ) d ps' := by
  have h : ∀ {a} (x : Var Δ a), Subst.liftN ps'.length θ (Ren.weakenN ps'.length x) =
      (θ x).rename (Ren.liftN a.params.length (Ren.weakenN ps'.length)) :=
    fun x => Subst.liftN_weakenN _ θ x
  simp only [Term.observation, Term.subst, ← Args.terms_subst, Args.bound_subst]
  rw [Term.subst_rename_of h, InstanceArgs.subst_rename_of h,
    Term.rename_subst_of (fun _ => rfl), InstanceArgs.rename_subst_of (fun _ => rfl)]

/-- The observation of a term, at arguments, is the observation by the destructor applied to them. -/
theorem Term.observation_instantiate {Γ Δ : Scope} (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (t : Term k Γ) (d : Name)
    {ps' : List Parameter} (ts : Args k Γ ps') :
    (t.observation D qs ls ps as d ps').instantiate ts = .obs D qs ls ps as t d ts.terms := by
  rw [Term.instantiate_eq_subst₀, Term.observation, Term.subst₀,
    InstanceArgs.subst₀_rename_of (ξ := Ren.weakenN ps'.length) (σ' := Subst₀.id)
      (fun y => Args.toSubst₀_weakenN ts y),
    InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    Term.subst₀_rename_of (ξ := Ren.weakenN ps'.length) (σ' := Subst₀.id)
      (fun y => Args.toSubst₀_weakenN ts y),
    Term.subst₀_id, ← Args.terms_subst₀, Args.bound_toSubst₀]

/-- A position of a destructor in destructors, at instantiated levels. -/
def Destructors.Pos.substLevels {k' : Nat} (ls' : Fin k → Level k') {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → Destructors.Pos d p q ds Ξ Θ B ψ →
        Destructors.Pos d p q (ds.substLevels ls') Ξ (Θ.substLevels ls') (B.substLevels ls') ψ
  | _, _, _, _, _, _, _, .here => .here
  | _, _, _, _, _, _, _, .there h => .there (h.substLevels ls')

/-- The substitution of the destructors before a position is the same at instantiated levels, since
it reads only the scopes. -/
theorem Destructors.Pos.obsSubst_posSubstLevels {k' k'' : Nat} {Γ' : Scope}
    (ls' : Fin k' → Level k'')
    (o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
      (θ : Subst k Γ' Γ) → ∀ {a} (x : Var Ξ a),
        (hd.substLevels ls').obsSubst o θ x = hd.obsSubst o θ x
  | _, _, _, _, _, _, _, .here, _, _, _ => rfl
  | _, _, _, _, _, _, _, .there h, _, _, x => h.obsSubst_posSubstLevels ls' o _ x

/-- The observation of a term, at instantiated levels, is the observation of the term at these
levels. -/
theorem Term.observation_substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (t : Term k Γ) (d : Name) (ps' : List Parameter) :
    (t.observation D qs ls ps as d ps').substLevels ls' =
      (t.substLevels ls').observation D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') d
        ps' := by
  simp only [Term.observation, Term.substLevels, ← Args.terms_substLevels, Args.substLevels_bound,
    Term.substLevels_rename, InstanceArgs.substLevels_rename]

/-! ## Corecursors at Their State -/

/-- The corecursor at the variables of a state, substituted under these variables, is the
corecursor substituted, at the variables of the state. -/
theorem Term.corecAt_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (Ss : States k Δ) (gs : CorecBranches k Δ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').subst (Subst.liftN ps'.length θ) =
      Term.corecAt r D qs ls ps (as.subst θ) (Ss.subst θ) (gs.subst θ) ps' := by
  have h : ∀ {a} (x : Var Δ a), Subst.liftN ps'.length θ (Ren.weakenN ps'.length x) =
      (θ x).rename (Ren.liftN a.params.length (Ren.weakenN ps'.length)) :=
    fun x => Subst.liftN_weakenN _ θ x
  simp only [Term.corecAt, Term.subst, ← Args.terms_subst, Args.bound_subst]
  rw [InstanceArgs.subst_rename_of h, States.subst_rename_of h, CorecBranches.subst_rename_of h,
    InstanceArgs.rename_subst_of (fun _ => rfl), States.rename_subst_of (fun _ => rfl),
    CorecBranches.rename_subst_of (fun _ => rfl)]

/-- `(corec_r T from ȳ return Θ̄ with ḡ)[t̄ / ȳ] = corec_r T from t̄ return Θ̄ with ḡ`: the corecursor at
the variables of a state, instantiated by arguments of the state, is the corecursor from them. -/
theorem Term.corecAt_instantiate {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (Ss : States k Γ)
    (gs : CorecBranches k Γ) {ps' : List Parameter} (ss : Args k Γ ps') :
    (Term.corecAt r D qs ls ps as Ss gs ps').instantiate ss = .corec r D qs ls ps as ss.terms Ss gs := by
  have h : ∀ {a} (y : Var Γ a), ss.toSubst₀ (Ren.weakenN ps'.length y) = Subst₀.id y :=
    fun y => Args.toSubst₀_weakenN ss y
  rw [Term.instantiate_eq_subst₀, Term.corecAt, Term.subst₀,
    InstanceArgs.subst₀_rename_of (σ' := Subst₀.id) h,
    InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    States.subst₀_rename_of (σ' := Subst₀.id) h, States.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    CorecBranches.subst₀_rename_of (σ' := Subst₀.id) h,
    CorecBranches.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl), ← Args.terms_subst₀,
    Args.bound_toSubst₀]

/-- The corecursor at the variables of a state, at instantiated levels, is the corecursor at these
levels, at the variables of the state. -/
theorem Term.corecAt_substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') (r : Grade)
    (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (Ss : States k Γ) (gs : CorecBranches k Γ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').substLevels ls' =
      Term.corecAt r D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') (Ss.substLevels ls')
        (gs.substLevels ls') ps' := by
  simp only [Term.corecAt, Term.substLevels, ← Args.terms_substLevels, Args.substLevels_bound,
    InstanceArgs.substLevels_rename, States.substLevels_rename, CorecBranches.substLevels_rename]

/-- The substitution of the destructors before a position, then by `σ`, is the substitution of the
destructors before it by the observations substituted, when the substitution of the scope and the
observations commute with `σ`. -/
theorem Destructors.Pos.obsSubst_subst {k' : Nat} {Γ' Γ'' : Scope} (σ : Subst k Γ'' Γ')
    {o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)}
    {o' : Name → (ps' : List Parameter) → Term k (Γ''.extend ps'.length)}
    (ho : ∀ d ps', (o d ps').subst (Subst.liftN ps'.length σ) = o' d ps') {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {θ : Subst k Γ' Γ} → {θ' : Subst k Γ'' Γ} →
      (∀ {a} (x : Var Γ a), (θ x).subst (Subst.liftN a.params.length σ) = θ' x) →
      ∀ {a} (x : Var Ξ a),
        ((hd.obsSubst o θ) x).subst (Subst.liftN a.params.length σ) = hd.obsSubst o' θ' x
  | _, _, _, _, _, _, _, .here, _, _, h => h
  | _, _, _, _, _, _, _, .there h', _, _, h => h'.obsSubst_subst σ ho fun x =>
    match x with
    | .zero => ho _ _
    | .succ x => h x

/-- The substitution of the destructors before a position, at instantiated levels, is the
substitution of the destructors before it by the observations at these levels, when the
substitution of the scope and the observations commute with the instantiation. -/
theorem Destructors.Pos.obsSubst_substLevels {k' k'' : Nat} {Γ' : Scope} (ls' : Fin k → Level k'')
    {o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)}
    {o' : Name → (ps' : List Parameter) → Term k'' (Γ'.extend ps'.length)}
    (ho : ∀ d ps', (o d ps').substLevels ls' = o' d ps') {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {θ : Subst k Γ' Γ} → {θ' : Subst k'' Γ' Γ} →
      (∀ {a} (x : Var Γ a), (θ x).substLevels ls' = θ' x) →
      ∀ {a} (x : Var Ξ a), ((hd.obsSubst o θ) x).substLevels ls' = hd.obsSubst o' θ' x
  | _, _, _, _, _, _, _, .here, _, _, h => h
  | _, _, _, _, _, _, _, .there h', _, _, h => h'.obsSubst_substLevels ls' ho fun x =>
    match x with
    | .zero => ho _ _
    | .succ x => h x

/-! ## Substitutions under New Variables

A term renamed under new variables, substituted under them, is the term substituted, renamed under
them. -/

theorem Term.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ) (t : Term k Δ) :
    (t.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (t.subst θ).rename (Ren.weakenN n) := by
  rw [Term.subst_rename_of (ξ := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Term.rename_subst_of (fun _ => rfl)]

theorem States.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (Ss : States k Δ) :
    (Ss.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (Ss.subst θ).rename (Ren.weakenN n) := by
  rw [States.subst_rename_of (ξ := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), States.rename_subst_of (fun _ => rfl)]

theorem Args.subst_liftN_rename_weakenN {Γ Δ : Scope} {ps : List Parameter} (n : Nat) (θ : Subst k Γ Δ)
    (ts : Args k Δ ps) :
    (ts.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (ts.subst θ).rename (Ren.weakenN n) := by
  rw [Args.subst_rename_of (ξ := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Args.rename_subst_of (fun _ => rfl)]

theorem InstanceArgs.subst_liftN_rename_weakenN {Γ Δ Ξ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (as : InstanceArgs k Δ Ξ) :
    (as.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (as.subst θ).rename (Ren.weakenN n) := by
  rw [InstanceArgs.subst_rename_of (ξ := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x),
    InstanceArgs.rename_subst_of (fun _ => rfl)]

theorem Motives.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (Cs : Motives k Δ) :
    (Cs.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (Cs.subst θ).rename (Ren.weakenN n) := by
  rw [Motives.subst_rename_of (ξ := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Motives.rename_subst_of (fun _ => rfl)]

/-! ## Renamings as Substitutions

A renaming is the substitution of the second order that gives each variable the abstraction of its
image, so that the laws of the substitutions hold for the renamings. -/

/-- The renaming `ξ` as a substitution of the second order, which gives each variable `x` the
abstraction `ȳ. ξ(x)[ȳ]`. -/
def Ren.toSubst {Γ Δ : Scope} (ξ : Ren Γ Δ) : Subst k Γ Δ := fun x => Var.eta (ξ x)

/-- A substitution that gives each variable the abstraction of its image by a renaming does so
under a new entry. -/
theorem Subst.lift_eta_of {Γ Δ : Scope} {b : Scope.Entry} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) :
    ∀ {a} (x : Var (b :: Δ) a), Subst.lift θ x = Var.eta (Ren.lift ξ x)
  | _, .zero => rfl
  | _, .succ x => by
    show (θ x).rename (Ren.liftN _ Ren.weaken) = _
    rw [h x]
    exact Var.eta_rename Ren.weaken (ξ x)

/-- A substitution that gives each variable the abstraction of its image by a renaming does so
under new variables. -/
theorem Subst.liftN_eta_of {Γ Δ : Scope} :
    ∀ (n : Nat) {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}, (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
      ∀ {a} (x : Var (Δ.extend n) a), Subst.liftN n θ x = Var.eta (Ren.liftN n ξ x)
  | 0, _, _, h => h
  | n + 1, _, _, h => Subst.liftN_eta_of (Γ := .var :: Γ) (Δ := .var :: Δ) n (Subst.lift_eta_of h)

/-- An application of a variable that a substitution gives a variable is the application of this
variable. -/
theorem Term.var_subst_of {Γ Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ} {x : Var Δ e}
    {y : Var Γ e} (h : θ x = Var.eta y) (ts : Args k Δ e.params) :
    (Term.var x ts).subst θ = .var y (ts.subst θ) := by
  rw [Term.subst, h, Var.eta_instantiate]

/-- A term renamed is the term substituted by a substitution that gives each variable the
abstraction of its image. -/
theorem Term.rename_eq_subst_of {Γ Δ : Scope} {ξ : Ren Γ Δ} {θ : Subst k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) (t : Term k Δ) : t.rename ξ = t.subst θ :=
  (Term.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (t.rename ξ)).symm.trans
    (Term.subst_rename_of (fun x => (h x).symm) t)

/-- A telescope renamed is the telescope substituted by a substitution that gives each variable the
abstraction of its image. -/
theorem Telescope.rename_eq_subst_of {Γ Δ : Scope} {ps : List Parameter} {ξ : Ren Γ Δ}
    {θ : Subst k Γ Δ} (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) (Θ : Telescope k Δ ps) :
    Θ.rename ξ = Θ.subst θ :=
  (Telescope.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Θ.rename ξ)).symm.trans
    (Telescope.subst_rename_of (fun x => (h x).symm) Θ)

theorem Term.rename_eq_subst {Γ Δ : Scope} (ξ : Ren Γ Δ) (t : Term k Δ) :
    t.rename ξ = t.subst (Ren.toSubst ξ) :=
  (Term.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (t.rename ξ)).symm.trans
    (Term.subst_rename_of (fun _ => rfl) t)

theorem Args.rename_eq_subst {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ) (ts : Args k Δ ps) :
    ts.rename ξ = ts.subst (Ren.toSubst ξ) :=
  (Args.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (ts.rename ξ)).symm.trans
    (Args.subst_rename_of (fun _ => rfl) ts)

theorem InstanceArgs.rename_eq_subst {Γ Δ Ξ : Scope} (ξ : Ren Γ Δ) (as : InstanceArgs k Δ Ξ) :
    as.rename ξ = as.subst (Ren.toSubst ξ) :=
  (InstanceArgs.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (as.rename ξ)).symm.trans
    (InstanceArgs.subst_rename_of (fun _ => rfl) as)

theorem Telescope.rename_eq_subst {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ)
    (Θ : Telescope k Δ ps) : Θ.rename ξ = Θ.subst (Ren.toSubst ξ) :=
  (Telescope.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Θ.rename ξ)).symm.trans
    (Telescope.subst_rename_of (fun _ => rfl) Θ)

/-- A closed term weakened to a scope, substituted, is the closed term weakened to the other
scope. -/
theorem Term.weakenClosed_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) (t : Term k []) :
    (t.weakenClosed : Term k Δ).subst θ = t.weakenClosed := by
  rw [Term.weakenClosed, Term.weakenClosed, Term.subst_rename_of (fun _ => rfl),
    Term.rename_eq_subst]
  exact Term.subst_congr (fun x => by cases x) t

/-! ## Substitutions of the First Order as Substitutions of the Second Order

A substitution of the first order is the substitution of the second order that gives each variable
the term it gives it, or the abstraction of the variable it gives it, so that the laws of the
substitutions of the second order hold for it. -/

/-- The value `v` as an abstraction over the variables of the telescope of its entry: the term
itself, for a variable without telescope, or the abstraction `ȳ. y[ȳ]` of the variable `y`. -/
def Val.eta {Γ : Scope} {e : Scope.Entry} : Val k Γ e → Term k (Γ.extend e.params.length)
  | .var y => Var.eta y
  | .term t => t

/-- The substitution `σ` of the first order as a substitution of the second order, which gives each
variable the abstraction of its value. -/
def Subst₀.toSubst {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) : Subst k Γ Δ := fun x => (σ x).eta

/-- A substitution of the first order then the identity is the identity then the substitution as
one of the second order. -/
theorem Subst₀.Swaps.toSubst {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) :
    Subst₀.Swaps σ (fun x => Var.eta x) σ.toSubst Subst₀.id :=
  ⟨fun x y h => by
      have h' : σ x = .var y := h
      show (σ x).eta.subst₀ (Subst₀.liftN _ Subst₀.id) = Var.eta y
      rw [h', Val.eta]
      exact Term.subst₀_id_of (Subst₀.liftN_id_of _ fun _ => rfl) _,
    fun x u h => by
      have h' : σ x = .term u := h
      show (σ x).eta.subst₀ Subst₀.id = u.subst fun x => Var.eta x
      rw [h', Val.eta]
      exact (Term.subst₀_id u).trans (Term.subst_id_of (fun _ => rfl) u).symm⟩

/-- The identity, under new variables, gives each variable its abstraction. -/
theorem Subst.liftN_eta_id {Γ : Scope} (n : Nat) :
    ∀ {a} (x : Var (Γ.extend n) a), Subst.liftN n (fun x => Var.eta (k := k) x) x = Var.eta x :=
  fun x => (Subst.liftN_eta_of n (ξ := fun x => x) (fun _ => rfl) x).trans
    (congrArg Var.eta (Ren.liftN_id_of n (fun _ => rfl) x))

/-- A term substituted by a substitution of the first order under new variables is the term
substituted by it as one of the second order, under them. -/
theorem Term.subst₀_liftN_eq_subst {Γ Δ : Scope} (n : Nat) (σ : Subst₀ k Γ Δ)
    (t : Term k (Δ.extend n)) :
    t.subst₀ (Subst₀.liftN n σ) = t.subst (Subst.liftN n σ.toSubst) := by
  have h := Term.subst_subst₀_of ((Subst₀.Swaps.toSubst σ).liftN n) t
  rwa [Term.subst_id_of (Subst.liftN_eta_id n),
    Term.subst₀_id_of (σ := Subst₀.liftN n Subst₀.id) (Subst₀.liftN_id_of n fun _ => rfl)] at h

/-- A term substituted by a substitution of the first order is the term substituted by it as one of
the second order. -/
theorem Term.subst₀_eq_subst {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) (t : Term k Δ) :
    t.subst₀ σ = t.subst σ.toSubst := by
  have h := Term.subst_subst₀_of (Subst₀.Swaps.toSubst σ) t
  rwa [Term.subst_id_of fun _ => rfl, Term.subst₀_id_of (σ := Subst₀.id) fun _ => rfl] at h

/-- Arguments substituted by a substitution of the first order are the arguments substituted by it
as one of the second order. -/
theorem Args.subst₀_eq_subst {Γ Δ : Scope} {ps : List Parameter} (σ : Subst₀ k Γ Δ)
    (ts : Args k Δ ps) : ts.subst₀ σ = ts.subst σ.toSubst := by
  have h := Args.subst_subst₀_of (Subst₀.Swaps.toSubst σ) ts
  rwa [Args.subst_id_of fun _ => rfl, Args.subst₀_id_of (σ := Subst₀.id) fun _ => rfl] at h

/-- Arguments of an instance substituted by a substitution of the first order are the arguments
substituted by it as one of the second order. -/
theorem InstanceArgs.subst₀_eq_subst {Γ Δ Ξ : Scope} (σ : Subst₀ k Γ Δ)
    (as : InstanceArgs k Δ Ξ) : as.subst₀ σ = as.subst σ.toSubst := by
  have h := InstanceArgs.subst_subst₀_of (Subst₀.Swaps.toSubst σ) as
  rwa [InstanceArgs.subst_id_of fun _ => rfl, InstanceArgs.subst₀_id_of (σ := Subst₀.id) fun _ => rfl] at h

/-- A telescope substituted by a substitution of the first order is the telescope substituted by it
as one of the second order. -/
theorem Telescope.subst₀_eq_subst {Γ Δ : Scope} {ps : List Parameter} (σ : Subst₀ k Γ Δ)
    (Θ : Telescope k Δ ps) : Θ.subst₀ σ = Θ.subst σ.toSubst := by
  have h := Telescope.subst_subst₀_of (Subst₀.Swaps.toSubst σ) Θ
  rwa [Telescope.subst_id_of fun _ => rfl, Telescope.subst₀_id_of (σ := Subst₀.id) fun _ => rfl] at h

/-! ## Positions in Substituted Motives, Branches and States -/

/-- A motive at a position of motives substituted is a motive of the motives, substituted. -/
theorem Motives.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Cs : Motives k Δ} → {j n : Nat} → {C : Term k (Γ.extend (n + 1))} →
      (Cs.subst θ).get j = some ⟨n, C⟩ →
        ∃ C₀, Cs.get j = some ⟨n, C₀⟩ ∧ C = C₀.subst (Subst.liftN (n + 1) θ)
  | .nil, _, _, _, h => nomatch h
  | .cons .., 0, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ Cs, _ + 1, _, _, h => Motives.get_subst_inv θ (Cs := Cs) h

/-- A branch at a position of branches substituted is a branch of the branches, substituted. -/
theorem Branches.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {us : Branches k Δ} → {i n m : Nat} → {u : Term k ((Γ.extend n).extend m)} →
      (us.subst θ).get i = some ⟨n, m, u⟩ →
        ∃ u₀, us.get i = some ⟨n, m, u₀⟩ ∧ u = u₀.subst (Subst.liftN m (Subst.liftN n θ))
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ us, _ + 1, _, _, _, h => Branches.get_subst_inv θ (us := us) h

/-- A state at a position of states substituted is a state of the states, substituted. -/
theorem States.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Ss : States k Δ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k (Γ.extend n) ps} →
      (Ss.subst θ).get j = some ⟨n, ps, S⟩ →
        ∃ S₀, Ss.get j = some ⟨n, ps, S₀⟩ ∧ S = S₀.subst (Subst.liftN n θ)
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_subst_inv θ (Ss := Ss) h

/-- A branch at a position of the branches of a corecursor substituted is a branch of the branches,
substituted. -/
theorem CorecBranches.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {vs : CorecBranches k Δ} → {i n m a : Nat} → {v : Term k (((Γ.extend n).extend m).extend a)} →
      (vs.subst θ).get i = some ⟨n, m, a, v⟩ →
        ∃ v₀, vs.get i = some ⟨n, m, a, v₀⟩ ∧
          v = v₀.subst (Subst.liftN a (Subst.liftN m (Subst.liftN n θ)))
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => CorecBranches.get_subst_inv θ (vs := vs) h

/-- Motives substituted are as many. -/
theorem Motives.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Cs : Motives k Δ) → (Cs.subst θ).length = Cs.length
  | .nil => rfl
  | .cons _ _ Cs => congrArg (· + 1) (Motives.length_subst θ Cs)

/-- Branches substituted are as many. -/
theorem Branches.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (us : Branches k Δ) → (us.subst θ).length = us.length
  | .nil => rfl
  | .cons _ _ _ _ us => congrArg (· + 1) (Branches.length_subst θ us)

/-- The grades of the recursive results of a branch of branches substituted are those of the
branch. -/
theorem Branches.grades_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (us : Branches k Δ) → (i : Nat) → (us.subst θ).grades i = us.grades i
  | .nil, _ => rfl
  | .cons .., 0 => rfl
  | .cons _ _ _ _ us, i + 1 => Branches.grades_subst θ us i

/-- States substituted are as many. -/
theorem States.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Ss : States k Δ) → (Ss.subst θ).length = Ss.length
  | .nil => rfl
  | .cons _ _ _ Ss => congrArg (· + 1) (States.length_subst θ Ss)

/-- The sorts of a state of states substituted are the sorts of the state. -/
theorem States.sorts_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Ss : States k Δ) → (j : Nat) → (Ss.subst θ).sorts j = Ss.sorts j
  | .nil, _ => rfl
  | .cons .., 0 => rfl
  | .cons _ _ _ Ss, j + 1 => States.sorts_subst θ Ss j

/-- The sorts of a state of states whose levels are instantiated are the sorts of the state,
instantiated. -/
theorem States.sorts_substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k') :
    (Ss : States k Γ) → (j : Nat) →
      (Ss.substLevels ls').sorts j = (Ss.sorts j).map (Universe.substLevels ls')
  | .nil, _ => rfl
  | .cons .., 0 => rfl
  | .cons _ _ _ Ss, j + 1 => States.sorts_substLevels ls' Ss j

/-- Branches of a corecursor substituted are as many. -/
theorem CorecBranches.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (vs : CorecBranches k Δ) → (vs.subst θ).length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (CorecBranches.length_subst θ vs)

/-! ## Recursive Results of Substituted Motives -/

/-- Recursive results of terms substituted, at the motives substituted, are those of the terms,
substituted. -/
theorem Motives.results_subst_inv (names : List Name) :
    {Γ Δ : Scope} → (θ : Subst k Γ Δ) → {Cs : Motives k Δ} → (rs : List (Option Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} →
      {R' : Telescope k Γ (Telescope.resultParams rs ps)} →
      Motives.results names (Cs.subst θ) rs (xs.subst θ) = some R' →
        ∃ R, Motives.results names Cs rs xs = some R ∧ R' = R.subst θ
  | _, _, θ, Cs, some D :: rs, p :: ps, .cons x xs, R', h => by
    unfold Motives.results at h
    simp only [Terms.subst] at h
    cases hC' : (Cs.subst θ).get (names.idxOf D) with
    | none => simp only [hC'] at h; cases h
    | some a =>
      obtain ⟨n, C'⟩ := a
      cases n with
      | succ => simp only [hC'] at h; cases h
      | zero =>
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
        simp only [hC'] at h
        obtain ⟨R'', hR'', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [← Motives.subst_lift_rename_weaken, ← Terms.subst_lift_rename_weaken] at hR''
        obtain ⟨R₀, hR₀, rfl⟩ := Motives.results_subst_inv names (Subst.lift θ) rs hR''
        refine ⟨.cons Grade.zero p (C₀.subst₀ (Subst₀.single x)) R₀, ?_, ?_⟩
        · unfold Motives.results
          simp only [hC₀, hR₀]
          rfl
        · show Telescope.cons Grade.zero p _ _ = Telescope.cons Grade.zero p _ _
          rw [Term.subst_subst₀_of (Subst₀.Swaps.single x θ) C₀]
          rfl
  | _, _, θ, Cs, none :: rs, _ :: ps, .cons _ xs, R', h => by
    unfold Motives.results at h ⊢
    exact Motives.results_subst_inv names θ rs h
  | _, _, _, _, some _ :: _, _ :: _, .nil, _, h | _, _, _, _, none :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, _, _, [], _, _, R', h | _, _, _, _, some _ :: _, [], _, R', h
  | _, _, _, _, none :: _, [], _, R', h => by
    unfold Motives.results at h
    cases h
    exact ⟨.nil, by unfold Motives.results; rfl, rfl⟩

/-- The recursive results of a constructor at motives substituted are its recursive results at the
motives, substituted under its fields. -/
theorem Constructor.results_subst_inv {j g k'' : Nat} {Δ Γ Γ' : Scope} (θ : Subst k Γ' Γ)
    {c : Constructor j g k'' Δ} {I : Instance j g} {names : List Name} {Cs : Motives k Γ}
    {R' : Telescope k (Γ'.extend (c.params I).length) (c.resultParams I names)}
    (h : c.results I names (Cs.subst θ) = some R') :
    ∃ R, c.results I names Cs = some R ∧ R' = R.subst (Subst.liftN _ θ) := by
  unfold Constructor.results at h ⊢
  rw [← Args.bound_subst (c.params I) θ, Args.terms_subst, ← Motives.subst_liftN_rename_weakenN] at h
  exact Motives.results_subst_inv names _ _ h

/-- The substitution of the destructors before a position by the observations of a term, substituted,
is the substitution by the observations of the term substituted, at the arguments substituted. -/
theorem Destructors.Pos.obsSubst_observation_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ' Δ) (t : Term k Γ') {d : Name} {p q : Grade} {ps' : List Parameter}
    {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hd : Destructors.Pos d p q ds Ξ Θ B ψ) :
    ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
          (Subst.liftN a.params.length σ) =
        hd.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
  hd.obsSubst_subst σ (fun d ps' => Term.observation_subst σ D qs ls ps as t d ps')
    (InstanceArgs.toSubst_subst σ as)

/-- The substitution of the destructors before a position by the observations of a corecursor at
the variables of its state, substituted under them, is the substitution by the observations of the
corecursor substituted. -/
theorem Destructors.Pos.obsSubst_corecAt_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ' Δ) (Ss : States k Γ') (gs : CorecBranches k Γ')
    (ps'' : List Parameter) {d : Name} {p q : Grade} {ps' : List Parameter} {ns : List Name}
    {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hd : Destructors.Pos d p q ds Ξ Θ B ψ) :
    ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst ((Term.corecAt r D qs ls ps as Ss gs ps'').observation D qs ls ps
          (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst) x).subst
          (Subst.liftN a.params.length (Subst.liftN ps''.length σ)) =
        hd.obsSubst ((Term.corecAt r D qs ls ps (as.subst σ) (Ss.subst σ) (gs.subst σ) ps'').observation
          D qs ls ps ((as.subst σ).rename (Ren.weakenN ps''.length)))
          ((as.subst σ).rename (Ren.weakenN ps''.length)).toSubst x := by
  intro a x
  have h := hd.obsSubst_observation_subst (Subst.liftN ps''.length σ) D qs ls ps
    (as.rename (Ren.weakenN ps''.length)) (Term.corecAt r D qs ls ps as Ss gs ps'') x
  rw [Term.corecAt_subst, InstanceArgs.subst_liftN_rename_weakenN] at h
  exact h

/-- The arguments of recursive results, substituted, are those of the arguments substituted, by
functions that commute with the substitution. -/
theorem Args.results_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) {f : Name → Term k Δ → Term k Δ}
    {f' : Name → Term k Γ → Term k Γ} (hf : ∀ D t, (f D t).subst θ = f' D (t.subst θ)) :
    (rs : List (Option Name)) → {ps : List Parameter} → (ts : Args k Δ ps) →
      (ts.results f rs).subst θ = (ts.subst θ).results f' rs
  | some D :: rs, _ :: _, .cons t ts => by
    show Args.cons ((f D t).subst θ) ((ts.results f rs).subst θ) = _
    rw [hf, Args.results_subst θ hf rs ts]
    rfl
  | none :: rs, _ :: _, .cons _ ts => Args.results_subst θ hf rs ts
  | [], [], .nil | [], _ :: _, .cons _ _ | some _ :: _, [], .nil | none :: _, [], .nil => rfl

/-! ## Renamings as Substitutions -/

-- ADE: none.
/-- A substitution of the first order that gives each variable a variable renames. -/
theorem Term.subst₀_eq_rename_of {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), σ x = .var (ξ x)) (t : Term k Δ) : t.subst₀ σ = t.rename ξ := by
  rw [Term.subst₀_eq_subst, Term.rename_eq_subst_of (θ := σ.toSubst) (fun x => by
    show (σ x).eta = _
    rw [h x]
    rfl)]

-- ADE: none.
/-- A substitution of the first order that gives each variable a variable or the term of a
variable renames. -/
theorem Term.subst₀_eq_rename_of_eta {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).eta = Var.eta (ξ x)) (t : Term k Δ) :
    t.subst₀ σ = t.rename ξ := by
  rw [Term.subst₀_eq_subst, Term.rename_eq_subst_of (θ := σ.toSubst) h]

-- ADE: none.
/-- A substitution of the first order of a telescope that gives each variable a variable or the term
of a variable renames it. -/
theorem Telescope.subst₀_eq_rename_of_eta {Γ Δ : Scope} {ps : List Parameter} {σ : Subst₀ k Γ Δ}
    {ξ : Ren Γ Δ} (h : ∀ {a} (x : Var Δ a), (σ x).eta = Var.eta (ξ x)) (Θ : Telescope k Δ ps) :
    Θ.subst₀ σ = Θ.rename ξ := by
  rw [Telescope.subst₀_eq_subst, Telescope.rename_eq_subst_of (θ := σ.toSubst) h]

-- ADE: none.
/-- A term renamed then substituted by a substitution that gives each variable a variable or the
term of a variable is the term renamed. -/
theorem Term.subst₀_rename_eq_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {ξ : Ren Δ Ξ}
    {ρ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ (ξ x)).eta = Var.eta (ρ x)) (t : Term k Ξ) :
    (t.rename ξ).subst₀ σ = t.rename ρ :=
  (Term.subst₀_rename_of (σ' := fun x => σ (ξ x)) (fun _ => rfl) t).trans
    (Term.subst₀_eq_rename_of_eta h t)

-- ADE: none.
/-- Substituting then renaming is renaming then substituting, when the two agree on each variable. -/
theorem Term.subst₀_rename_comm_of {Γ Δ Ξ Ψ : Scope} {σ₁ : Subst₀ k Δ Ξ} {ξ₁ : Ren Γ Δ}
    {σ₂ : Subst₀ k Γ Ψ} {ξ₂ : Ren Ψ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename ξ₁ = σ₂ (ξ₂ x))
    (t : Term k Ξ) : (t.subst₀ σ₁).rename ξ₁ = (t.rename ξ₂).subst₀ σ₂ :=
  (Term.rename_subst₀_of (σ' := fun x => σ₂ (ξ₂ x)) h t).trans
    (Term.subst₀_rename_of (fun _ => rfl) t).symm

-- ADE: none.
/-- Substituting then renaming a telescope is renaming then substituting it, when the two agree on
each variable. -/
theorem Telescope.subst₀_rename_comm_of {Γ Δ Ξ Ψ : Scope} {ps : List Parameter}
    {σ₁ : Subst₀ k Δ Ξ} {ξ₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {ξ₂ : Ren Ψ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename ξ₁ = σ₂ (ξ₂ x)) (Θ : Telescope k Ξ ps) :
    (Θ.subst₀ σ₁).rename ξ₁ = (Θ.rename ξ₂).subst₀ σ₂ :=
  (Telescope.rename_subst₀_of (σ' := fun x => σ₂ (ξ₂ x)) h Θ).trans
    (Telescope.subst₀_rename_of (fun _ => rfl) Θ).symm

-- ADE: none.
/-- `X[x]` at the abstraction `x. B` is `B`. -/
theorem Term.subst₀_single_zero_rename_lift_weaken {Γ : Scope} (B : Term k (.var :: Γ)) :
    (B.rename (Ren.lift Ren.weaken)).subst₀ (Subst₀.single (.var₀ .zero)) = B := by
  rw [Term.subst₀_rename_of (σ' := fun x => Subst₀.single (.var₀ .zero) (Ren.lift Ren.weaken x))
    (fun _ => rfl), Term.subst₀_eq_subst]
  exact Term.subst_id_of (fun x => by cases x <;> rfl) B

-- ADE: `wk1-sgSubst`, in `Definition/Untyped/Properties.agda`.
/-- A motive that does not depend on the term it eliminates, at a term, is the motive. -/
theorem Term.subst₀_single_rename_weaken {Γ : Scope} (C t : Term k Γ) :
    (C.rename Ren.weaken).subst₀ (Subst₀.single t) = C :=
  (Term.subst₀_rename_of (σ := Subst₀.single t) (ξ := Ren.weaken) (σ' := Subst₀.id)
    (fun _ => rfl) C).trans (Term.subst₀_id C)

-- ADE: none.
/-- A motive that does not depend on the term it eliminates, at a constructor, is the motive under
the variables of the fields. -/
theorem Term.atCtor_rename_weaken {Γ Δ : Scope} (C : Term k Γ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name)
    (fs : List Parameter) :
    (C.rename Ren.weaken).atCtor D qs ls ps as c fs = C.rename (Ren.weakenN fs.length) := by
  rw [Term.atCtor, Term.rename_rename_of (ξ₁ := Ren.lift (Ren.weakenN fs.length))
    (ξ₂ := Ren.weaken) (ξ₃ := fun x => .succ (Ren.weakenN fs.length x)) (fun _ => rfl),
    Term.subst₀_rename_of (ξ := fun x => .succ (Ren.weakenN fs.length x))
      (σ' := fun x => .var (Ren.weakenN fs.length x)) (fun _ => rfl)]
  exact Term.subst₀_eq_rename_of (fun _ => rfl) C

end Sic.Core
