module

public import Sic.Core.Substitution.Composition

/-!
# Closed Substitutions

The closed substitutions of annex 09 of RFC 36: the substitution of closed terms for the variables
of a scope, built by appending substitutions, and the substitutions that give variables for
variables.

ADE have no closed substitutions: their substitutions are defined between any two contexts.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

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
      exact (Ren.liftN_comp_of n (α₃ := Ren.empty) (fun y => nomatch y) z).symm

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
        Ren.liftN_comp_of n (α₃ := Ren.empty) (fun y => nomatch y) z,
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

theorem Subst₀.lift_isVar {Γ Δ : Scope} {b : Scope.Entry} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) :
    ∀ {a} (x : Var (b :: Δ) a), (Subst₀.lift σ x).IsVar (Ren.lift α x)
  | _, .zero => .var _
  | _, .succ x => by
    show ((σ x).rename Ren.weaken).IsVar (Var.succ (α x))
    have hx := h x
    revert hx
    generalize σ x = v
    intro hx
    cases hx with
    | var => exact .var _
    | term => exact .term _

theorem Subst₀.liftN_isVar {Γ Δ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}, (∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) →
      ∀ {a} (x : Var (Δ.extend n) a), (Subst₀.liftN n σ x).IsVar (Ren.liftN n α x)
  | 0, _, _, h => h
  | n + 1, _, _, h => Subst₀.liftN_isVar (Γ := .var :: Γ) (Δ := .var :: Δ) n (Subst₀.lift_isVar h)

mutual

/-- A substitution that gives each variable a variable renames by them. -/
theorem Term.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (t : Term k Δ) → t.subst₀ σ = t.rename α
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

theorem Args.subst₀_isVar {Γ Δ : Scope} {a : List Parameter} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (ts : Args k Δ a) → ts.subst₀ σ = ts.rename α
  | .nil => rfl
  | .cons t ts => by rw [Args.rename, Args.subst₀, Term.subst₀_isVar h t, Args.subst₀_isVar h ts]

theorem InstanceArgs.subst₀_isVar {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) :
    (as : InstanceArgs k Δ Ξ) → as.subst₀ σ = as.rename α
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst₀, InstanceArgs.subst₀_isVar h as,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ h) B]

theorem Terms.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (ts : Terms k Δ) → ts.subst₀ σ = ts.rename α
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst₀, Terms.subst₀_isVar h ts, Term.subst₀_isVar h t]

theorem Motives.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (Cs : Motives k Δ) → Cs.subst₀ σ = Cs.rename α
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst₀, Motives.subst₀_isVar h Cs,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ h) C]

theorem Branches.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (us : Branches k Δ) → us.subst₀ σ = us.rename α
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst₀, Branches.subst₀_isVar h us,
      Term.subst₀_isVar (Subst₀.liftN_isVar _ (Subst₀.liftN_isVar _ h)) u]

theorem Telescope.subst₀_isVar {Γ Δ : Scope} {ps : List Parameter} {σ : Subst₀ k Γ Δ}
    {α : Ren Γ Δ} (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) :
    (Θ : Telescope k Δ ps) → Θ.subst₀ σ = Θ.rename α
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst₀, Telescope.subst₀_isVar (Subst₀.lift_isVar h) Θ,
      Term.subst₀_isVar h A]

theorem States.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) : (Ss : States k Δ) → Ss.subst₀ σ = Ss.rename α
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst₀, States.subst₀_isVar h Ss,
      Telescope.subst₀_isVar (Subst₀.liftN_isVar _ h) S]

theorem CorecBranches.subst₀_isVar {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).IsVar (α x)) :
    (vs : CorecBranches k Δ) → vs.subst₀ σ = vs.rename α
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
        Ren.liftN_comp_of n (α₃ := Ren.empty) (fun y => nomatch y) z]

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
          Ren.liftN_comp_of ps.length (α₃ := Ren.empty) (fun y => nomatch y) z
        erw [hz, Subst₀.liftN_rename_of ps.length
          (σ' := fun y => Subst₀.single (.var₀ (Var.weakenN ps.length .zero)) (Ren.empty y))
          (fun _ => rfl), Subst₀.liftN_empty]
        have := (Args.bound_toSubst₀_isVar ps (Γ := .var :: Γ) : _)
          (Ren.liftN ps.length Ren.empty z)
        rwa [Ren.liftN_comp_of ps.length (α₃ := Ren.empty) (fun y => nomatch y) z] at this
    exact key x

/-- `B[α⇑][x̄ / x̄] = B`: a term renamed under new variables, then instantiated by them, is itself. -/
theorem Term.instantiate_bound_rename {Γ : Scope} (ps : List Parameter)
    (B : Term k (Γ.extend ps.length)) :
    (B.rename (Ren.liftN ps.length (Ren.weakenN ps.length))).instantiate (Args.bound ps) = B := by
  rw [Term.instantiate_eq_subst₀, Term.subst₀_rename_of (fun _ => rfl),
    Term.subst₀_isVar (α := fun x => x) (Args.bound_toSubst₀_isVar ps), Term.rename_id]

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
    rw [InstanceArgs.subst_rename_of (α := Ren.weaken) (θ' := fun y => θ y.succ) (fun _ => rfl)]
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
      a.params.length (α := Ren.weakenN n) (θ' := fun y => θ₂ (y.weakenN n)) fun _ => rfl)]
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

end Sic.Core
