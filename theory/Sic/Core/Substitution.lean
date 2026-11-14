module

public import Sic.Core.Syntax

/-!
# Substitution

The substitutions of annex 09 of RFC 36: the substitutions of the first order, among them the
substitution `B[t̄ / Θ]` of the arguments of a telescope for its variables, the substitutions of the
second order, which replace each application `X[t̄]` by `B[t̄ / x̄]` where `x̄. B` is the
abstraction given to `X`, among them the substitution `[ā / Δ]` of the arguments of an instance for
its parameters and the substitution `[ā / Δ, t.T / d̄₁]`, which also gives the destructors before a
destructor the observations of a term by them, and the instantiation `[l̄' / l̄]` of the level
variables; the entries of the contexts, `x : A ∈ Γ` and `X : (Θ ⊢ A) ∈ Γ`, give the types of the
variables weakened to the scope of the context.

A substitution of the second order replaces a second-order variable by an abstraction, so that it
substitutes the arguments of each application in the abstraction, which is not a subterm of the
term.
It is therefore built on a substitution of the first order, `subst₀`, which replaces each variable
either by a variable with the same telescope or, when it has none, by a term, and which recurses on
the term alone.
The RFC names the variables, so that a substitution of the first order leaves the variables with a
telescope; with de Bruijn indices, it renames them, as the lifts under binders need.
The modules of `Sic/Core/Substitution/` give the composition of the renamings and of the
substitutions of both orders, the closed substitutions, the laws of the instantiation of the levels
and the substitutions that the rules build.

ADE substitute terms for variables of the first order only, in `Definition/Untyped.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Renamings -/

-- ADE: `Wk`, in `Definition/Untyped/NotParametrised.agda`.
/-- A renaming of the scope `Δ` in the scope `Γ`, which keeps the entry of each variable. -/
abbrev Ren (Γ Δ : Scope) : Type := ∀ {e : Scope.Entry}, Var Δ e → Var Γ e

namespace Ren

/-- The renaming `α` under a new entry. -/
def lift {Γ Δ : Scope} {e : Scope.Entry} (α : Ren Γ Δ) : Ren (e :: Γ) (e :: Δ) := fun x =>
  match x with
  | .zero => .zero
  | .succ x => .succ (α x)

/-- The renaming `α` under `n` new variables. -/
def liftN {Γ Δ : Scope} : (n : Nat) → Ren Γ Δ → Ren (Γ.extend n) (Δ.extend n)
  | 0, α => α
  | n + 1, α => liftN n (lift α)

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
/-- The term `t` renamed by `α`. -/
def Term.rename {Γ Δ : Scope} (α : Ren Γ Δ) : Term k Δ → Term k Γ
  | .var x ts => .var (α x) (ts.rename α)
  | .sort κ => .sort κ
  | .const c qs ls ps => .const c qs ls ps
  | .inst D qs ls ps as => .inst D qs ls ps (as.rename α)
  | .ctor D qs ls ps as c ts => .ctor D qs ls ps (as.rename α) c (ts.rename α)
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs ls ps (as.rename α) (t.rename α) (Cs.rename α) (us.rename α)
  | .obs D qs ls ps as t d bs => .obs D qs ls ps (as.rename α) (t.rename α) d (bs.rename α)
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs ls ps (as.rename α) (ss.rename α) (Ss.rename α) (vs.rename α)

/-- The arguments `t̄` renamed by `α`. -/
def Args.rename {Γ Δ : Scope} {a : List Parameter} (α : Ren Γ Δ) : Args k Δ a → Args k Γ a
  | .nil => .nil
  | .cons t ts => .cons (t.rename α) (ts.rename α)

/-- The arguments `ā` renamed by `α`, under the variables of each abstraction. -/
def InstanceArgs.rename {Γ Δ Ξ : Scope} (α : Ren Γ Δ) : InstanceArgs k Δ Ξ → InstanceArgs k Γ Ξ
  | .nil => .nil
  | .snoc as B => .snoc (as.rename α) (B.rename (Ren.liftN _ α))

/-- The terms `t̄` renamed by `α`. -/
def Terms.rename {Γ Δ : Scope} (α : Ren Γ Δ) : Terms k Δ → Terms k Γ
  | .nil => .nil
  | .cons t ts => .cons (t.rename α) (ts.rename α)

/-- The motives `C̄` renamed by `α`, under the variables of each motive. -/
def Motives.rename {Γ Δ : Scope} (α : Ren Γ Δ) : Motives k Δ → Motives k Γ
  | .nil => .nil
  | .cons n C Cs => .cons n (C.rename (Ren.liftN _ α)) (Cs.rename α)

/-- The branches `ū` renamed by `α`, under the variables of each branch. -/
def Branches.rename {Γ Δ : Scope} (α : Ren Γ Δ) : Branches k Δ → Branches k Γ
  | .nil => .nil
  | .cons n m es u us => .cons n m es (u.rename (Ren.liftN m (Ren.liftN n α))) (us.rename α)

/-- The telescope `Θ` renamed by `α`. -/
def Telescope.rename {Γ Δ : Scope} {ps : List Parameter} (α : Ren Γ Δ) :
    Telescope k Δ ps → Telescope k Γ ps
  | .nil => .nil
  | .cons q p A Θ => .cons q p (A.rename α) (Θ.rename (Ren.lift α))

/-- The states `Θ̄` renamed by `α`, under the variables of each state. -/
def States.rename {Γ Δ : Scope} (α : Ren Γ Δ) : States k Δ → States k Γ
  | .nil => .nil
  | .cons n S κs Ss => .cons n (S.rename (Ren.liftN _ α)) κs (Ss.rename α)

/-- The branches `ḡ` of a corecursor renamed by `α`, under the variables of each branch. -/
def CorecBranches.rename {Γ Δ : Scope} (α : Ren Γ Δ) : CorecBranches k Δ → CorecBranches k Γ
  | .nil => .nil
  | .cons n m a v vs =>
    .cons n m a (v.rename (Ren.liftN a (Ren.liftN m (Ren.liftN n α)))) (vs.rename α)

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
theorem Term.blockName_rename {Γ Δ : Scope} (names : List Name) (α : Ren Γ Δ) :
    (A : Term k Δ) → (A.rename α).blockName names = A.blockName names
  | .var .. | .sort _ | .const .. | .inst .. | .ctor .. | .recursor .. | .obs .. | .corec .. => rfl

/-- A renamed telescope has its recursive fields at the same positions. -/
theorem Telescope.recursion_rename {Γ Δ : Scope} (names : List Name) :
    {ps : List Parameter} → (α : Ren Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.rename α).recursion names = Θ.recursion names
  | [], _, .nil => rfl
  | _ :: _, α, .cons _ _ A Θ => by
    rw [Telescope.rename, Telescope.recursion, Telescope.recursion, Term.blockName_rename,
      Telescope.recursion_rename names (Ren.lift α) Θ]

/-- The destructors `d̄` renamed by `α`, the arguments and the result of each under the destructors
before it, and the result under its arguments. -/
def Destructors.rename {Γ Δ : Scope} (α : Ren Γ Δ) :
    {ns : List Name} → Destructors k Δ ns → Destructors k Γ ns
  | _, .nil => .nil
  | _, .cons p q χ Θ B ψ ds =>
    .cons p q χ (Θ.rename α) (B.rename (Ren.liftN _ α)) ψ (ds.rename (Ren.lift α))

/-- Renamed destructors have their recursive destructors at the same positions. -/
theorem Destructors.recursion_rename {Γ Δ : Scope} (names : List Name) :
    {ns : List Name} → (α : Ren Γ Δ) → (ds : Destructors k Δ ns) →
      (ds.rename α).recursion names = ds.recursion names
  | _, _, .nil => rfl
  | _, α, .cons _ _ _ _ B _ ds => by
    rw [Destructors.rename, Destructors.recursion, Destructors.recursion, Term.blockName_rename,
      Destructors.recursion_rename names (Ren.lift α) ds]

/-- Renamed destructors give each destructor the same grade. -/
theorem Destructors.grade_rename {Γ Δ : Scope} (d : Name) :
    {ns : List Name} → (α : Ren Γ Δ) → (ds : Destructors k Δ ns) →
      (ds.rename α).grade d = ds.grade d
  | _, _, .nil => rfl
  | _, α, .cons _ _ _ _ _ _ ds => by
    rw [Destructors.rename, Destructors.grade, Destructors.grade,
      Destructors.grade_rename d (Ren.lift α) ds]

/-! ## Substitutions of the First Order -/

/-- What a substitution of the first order gives a variable whose entry is `e`: a variable with the
same entry, or a term for a variable. -/
inductive Val (k : Nat) (Γ : Scope) : Scope.Entry → Type where
  /-- A variable. -/
  | var {e : Scope.Entry} (x : Var Γ e) : Val k Γ e
  /-- A term, for a variable. -/
  | term (t : Term k Γ) : Val k Γ .var

/-- The value `v` renamed by `α`. -/
def Val.rename {Γ Δ : Scope} {a : Scope.Entry} (α : Ren Γ Δ) : Val k Δ a → Val k Γ a
  | .var x => .var (α x)
  | .term t => .term (t.rename α)

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
def Destructors.Pos.obsSubst {k' : Nat} {Γ' : Scope} {d : Name} {p q χ : Grade}
    {ps : List Parameter} (o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → Destructors.Pos d p q χ ds Ξ Θ B ψ → Subst k Γ' Γ →
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

/-- The number of the entries of a context, those of the telescope of a second-order variable
included. -/
def Context.size {k : Nat} : {Γ : Scope} → Context k Γ → Nat
  | _, .empty => 0
  | _, .var ctx _ => ctx.size + 1
  | _, .secondOrder (ps := ps) ctx _ _ _ => ctx.size + ps.length + 1

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
  | _, .cons p q χ Θ B ψ ds =>
    .cons p q χ (Θ.substLevels ls') (B.substLevels ls') ψ (ds.substLevels ls')

/-- A closed term in the scope `Γ`, which it does not use. -/
def Term.weakenClosed {Γ : Scope} (t : Term k []) : Term k Γ := t.rename fun x => by cases x

/-! ## Entries of Contexts -/

/-- `x : A ∈ Γ`: the variable `x` is declared with the type `A` in the context, by the cases of the
last entry; the empty context, which has no variable, has no constructor, and the type is weakened
to the scope of the context. -/
inductive Context.VarIn {k : Nat} : {Γ : Scope} → Context k Γ → Var Γ .var → Term k Γ → Prop where
  /-- The last entry.
  RFC: `\in_\Gamma.x` -/
  | zero {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      VarIn (ctx.var A) .zero (A.rename Ren.weaken)
  /-- An entry before a variable.
  RFC: `\in_\Gamma.x,y` -/
  | succVar {Γ : Scope} {ctx : Context k Γ} {x : Var Γ .var} {A B : Term k Γ} (h : VarIn ctx x A) :
      VarIn (ctx.var B) x.succ (A.rename Ren.weaken)
  /-- An entry before a second-order variable.
  RFC: `\in_\Gamma.x,Y` -/
  | succSecondOrder {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length} {ctx : Context k Γ}
      {x : Var Γ .var} {A : Term k Γ} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)}
      (h : VarIn ctx x A) : VarIn (ctx.secondOrder Θ B ψ) x.succ (A.rename Ren.weaken)

/-- `X : (Θ ⊢ A) ∈ Γ`: the second-order variable `X` is declared with the telescope `Θ` and the
type `A` in the context, by the cases of the last entry; the empty context, which has no
second-order variable, has no constructor, and the telescope and the type are weakened to the scope
of the context. -/
inductive Context.SecondOrderIn {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    {ψ : ResultOwnership Grade ps.length} → Context k Γ → Var Γ (.secondOrder ps ψ) → Telescope k Γ ps →
    Term k (Γ.extend ps.length) → Prop where
  /-- The last entry.
  RFC: `\in_\Gamma.X` -/
  | zero {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
      SecondOrderIn (ctx.secondOrder Θ A ψ) .zero (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a variable.
  RFC: `\in_\Gamma.X,y` -/
  | succVar {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length} {ctx : Context k Γ}
      {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {B : Term k Γ} (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.var B) X.succ (Θ.rename Ren.weaken) (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a second-order variable.
  RFC: `\in_\Gamma.X,Y` -/
  | succSecondOrder {Γ : Scope} {ps qs : List Parameter} {ψ : ResultOwnership Grade ps.length} {ψ' : ResultOwnership Grade qs.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps}
      {A : Term k (Γ.extend ps.length)} {Θ' : Telescope k Γ qs} {B : Term k (Γ.extend qs.length)}
      (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.secondOrder Θ' B ψ') X.succ (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))

/-! ## Properties

The renamings and the substitutions of the first order that give each variable itself change
nothing, under the new variables of every abstraction. -/

theorem Ren.lift_id_of {Γ : Scope} {b : Scope.Entry} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    ∀ {a} (x : Var (b :: Γ) a), Ren.lift α x = x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_id_of {Γ : Scope} :
    ∀ (n : Nat) {α : Ren Γ Γ}, (∀ {a} (x : Var Γ a), α x = x) →
      ∀ {a} (x : Var (Γ.extend n) a), Ren.liftN n α x = x
  | 0, _, h => h
  | n + 1, _, h => Ren.liftN_id_of (Γ := .var :: Γ) n (Ren.lift_id_of h)

mutual

theorem Term.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (t : Term k Γ) → t.rename α = t
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

theorem Args.rename_id_of {Γ : Scope} {a : List Parameter} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (ts : Args k Γ a) → ts.rename α = ts
  | .nil => rfl
  | .cons t ts => by rw [Args.rename, Term.rename_id_of h t, Args.rename_id_of h ts]

theorem InstanceArgs.rename_id_of {Γ Ξ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (as : InstanceArgs k Γ Ξ) → as.rename α = as
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename_id_of h as,
      Term.rename_id_of (Ren.liftN_id_of _ h) B]

theorem Terms.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (ts : Terms k Γ) → ts.rename α = ts
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.rename_id_of h ts, Term.rename_id_of h t]

theorem Motives.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (Cs : Motives k Γ) → Cs.rename α = Cs
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.rename_id_of h Cs, Term.rename_id_of (Ren.liftN_id_of _ h) C]

theorem Branches.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (us : Branches k Γ) → us.rename α = us
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.rename_id_of h us, Term.rename_id_of (Ren.liftN_id_of _ (Ren.liftN_id_of _ h)) u]


theorem Telescope.rename_id_of {Γ : Scope} {ps : List Parameter}
    {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (Θ : Telescope k Γ ps) → Θ.rename α = Θ
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.rename_id_of (Ren.lift_id_of h) Θ, Term.rename_id_of h A]

theorem States.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (Ss : States k Γ) → Ss.rename α = Ss
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.rename_id_of h Ss, Telescope.rename_id_of (Ren.liftN_id_of _ h) S]

theorem CorecBranches.rename_id_of {Γ : Scope} {α : Ren Γ Γ} (h : ∀ {a} (x : Var Γ a), α x = x) :
    (vs : CorecBranches k Γ) → vs.rename α = vs
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

end Sic.Core
