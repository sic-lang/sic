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
