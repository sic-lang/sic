module

public import Sic.Core.Substitution

/-!
# Composition of the Substitutions

The composition of the substitutions of annex 09 of RFC 36: the renamings and the substitutions of
both orders compose, and the substitution `B[t̄ / Θ]` commutes with each of them; a renaming is a
substitution of the second order, and so is a substitution of the first order.

ADE compose substitutions of the first order only, in `Definition/Untyped/Properties.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

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

theorem Ren.lift_comp_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    ∀ {a} (x : Var (b :: Ξ) a), Ren.lift α₁ (Ren.lift α₂ x) = Ren.lift α₃ x
  | _, .zero => rfl
  | _, .succ x => congrArg Var.succ (h x)

theorem Ren.liftN_comp_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ} {α₃ : Ren Γ Ξ},
      (∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Ren.liftN n α₁ (Ren.liftN n α₂ x) = Ren.liftN n α₃ x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Ren.liftN_comp_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Ren.lift_comp_of h)

mutual

-- ADE: `wk-comp`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `α₂` then by `α₁` is renaming by their composition `α₃`. -/
theorem Term.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ} {α₃ : Ren Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (t : Term k Ξ) → (t.rename α₂).rename α₁ = t.rename α₃
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

theorem Args.rename_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (ts : Args k Ξ a) → (ts.rename α₂).rename α₁ = ts.rename α₃
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.rename, Args.rename, Term.rename_rename_of h t, Args.rename_rename_of h ts]

theorem InstanceArgs.rename_rename_of {Γ Δ Ξ Ψ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename α₂).rename α₁ = as.rename α₃
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.rename, InstanceArgs.rename,
      InstanceArgs.rename_rename_of h as, Term.rename_rename_of (Ren.liftN_comp_of _ h) B]

theorem Terms.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (ts : Terms k Ξ) → (ts.rename α₂).rename α₁ = ts.rename α₃
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.rename, Terms.rename,
      Terms.rename_rename_of h ts, Term.rename_rename_of h t]

theorem Motives.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (Cs : Motives k Ξ) → (Cs.rename α₂).rename α₁ = Cs.rename α₃
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.rename, Motives.rename,
      Motives.rename_rename_of h Cs, Term.rename_rename_of (Ren.liftN_comp_of _ h) C]

theorem Branches.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (us : Branches k Ξ) → (us.rename α₂).rename α₁ = us.rename α₃
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.rename, Branches.rename,
      Branches.rename_rename_of h us, Term.rename_rename_of (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ h)) u]


theorem Telescope.rename_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ} {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename α₂).rename α₁ = Θ.rename α₃
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.rename, Telescope.rename,
      Telescope.rename_rename_of (Ren.lift_comp_of h) Θ, Term.rename_rename_of h A]

theorem States.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (Ss : States k Ξ) → (Ss.rename α₂).rename α₁ = Ss.rename α₃
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.rename, States.rename,
      States.rename_rename_of h Ss, Telescope.rename_rename_of (Ren.liftN_comp_of _ h) S]

theorem CorecBranches.rename_rename_of {Γ Δ Ξ : Scope} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (vs : CorecBranches k Ξ) → (vs.rename α₂).rename α₁ = vs.rename α₃
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.rename, CorecBranches.rename,
      CorecBranches.rename_rename_of h vs,
      Term.rename_rename_of
        (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ (Ren.liftN_comp_of _ h))) v]

end

/-- Renaming a value by `α₂` then by `α₁` is renaming it by their composition `α₃`. -/
theorem Val.rename_rename_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {α₁ : Ren Γ Δ} {α₂ : Ren Δ Ξ}
    {α₃ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), α₁ (α₂ x) = α₃ x) :
    (v : Val k Ξ a) → (v.rename α₂).rename α₁ = v.rename α₃
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_rename_of h t)

/-- Renaming each variable to itself changes no value. -/
theorem Val.rename_id_of {Γ : Scope} {a : Scope.Entry} {α : Ren Γ Γ}
    (h : ∀ {a} (x : Var Γ a), α x = x) : (v : Val k Γ a) → v.rename α = v
  | .var x => congrArg Val.var (h x)
  | .term t => congrArg Val.term (Term.rename_id_of h t)

/-! ### Substitutions after Renamings -/

theorem Subst₀.lift_rename_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst₀.lift σ (Ren.lift α x) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (Val.rename Ren.weaken) (h x)

theorem Subst₀.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), σ (α x) = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst₀.liftN n σ (Ren.liftN n α x) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst₀.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`.
/-- Renaming by `α` then substituting by `σ` is substituting by their composition `σ'`. -/
theorem Term.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (t : Term k Ξ) → (t.rename α).subst₀ σ = t.subst₀ σ'
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

theorem Args.subst₀_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (ts : Args k Ξ a) → (ts.rename α).subst₀ σ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst₀, Args.subst₀, Term.subst₀_rename_of h t,
      Args.subst₀_rename_of h ts]

theorem InstanceArgs.subst₀_rename_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename α).subst₀ σ = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst₀, InstanceArgs.subst₀,
      InstanceArgs.subst₀_rename_of h as, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) B]

theorem Terms.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (ts : Terms k Ξ) → (ts.rename α).subst₀ σ = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst₀, Terms.subst₀,
      Terms.subst₀_rename_of h ts, Term.subst₀_rename_of h t]

theorem Motives.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (Cs : Motives k Ξ) → (Cs.rename α).subst₀ σ = Cs.subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst₀, Motives.subst₀,
      Motives.subst₀_rename_of h Cs, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ h) C]

theorem Branches.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (us : Branches k Ξ) → (us.rename α).subst₀ σ = us.subst₀ σ'
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst₀, Branches.subst₀,
      Branches.subst₀_rename_of h us, Term.subst₀_rename_of (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ h)) u]


theorem Telescope.subst₀_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename α).subst₀ σ = Θ.subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst₀, Telescope.subst₀,
      Telescope.subst₀_rename_of (Subst₀.lift_rename_of h) Θ, Term.subst₀_rename_of h A]

theorem States.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (Ss : States k Ξ) → (Ss.rename α).subst₀ σ = Ss.subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst₀, States.subst₀,
      States.subst₀_rename_of h Ss, Telescope.subst₀_rename_of (Subst₀.liftN_rename_of _ h) S]

theorem CorecBranches.subst₀_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (vs : CorecBranches k Ξ) → (vs.rename α).subst₀ σ = vs.subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.subst₀, CorecBranches.subst₀,
      CorecBranches.subst₀_rename_of h vs,
      Term.subst₀_rename_of
        (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ (Subst₀.liftN_rename_of _ h))) v]

end

/-- Renaming a value by `α` then substituting it by `σ` is substituting it by their composition
`σ'`. -/
theorem Val.subst₀_rename_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), σ (α x) = σ' x) :
    (v : Val k Ξ a) → (v.rename α).subst₀ σ = v.subst₀ σ'
  | .var x => h x
  | .term t => congrArg Val.term (Term.subst₀_rename_of h t)

/-! ### Renamings after Substitutions -/

theorem Subst₀.lift_rename_after_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {σ : Subst₀ k Δ Ξ}
    {α : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), (Subst₀.lift σ x).rename (Ren.lift α) = Subst₀.lift σ' x
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ x).rename Ren.weaken).rename (Ren.lift α) = (σ' x).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (α₁ := Ren.lift α) (α₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (α₁ := Ren.weaken) (α₂ := α) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ x).rename (Ren.liftN n α) = Subst₀.liftN n σ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst₀.liftN_rename_after_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) n (Subst₀.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`.
/-- Substituting by `σ` then renaming by `α` is substituting by their composition `σ'`. -/
theorem Term.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (t : Term k Ξ) → (t.subst₀ σ).rename α = t.subst₀ σ'
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

theorem Args.rename_subst₀_of {Γ Δ Ξ : Scope} {a : List Parameter} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (ts : Args k Ξ a) → (ts.subst₀ σ).rename α = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst₀, Args.rename, Args.subst₀, Term.rename_subst₀_of h t,
      Args.rename_subst₀_of h ts]

theorem InstanceArgs.rename_subst₀_of {Γ Δ Ξ Ψ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst₀ σ).rename α = as.subst₀ σ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.rename, InstanceArgs.subst₀,
      InstanceArgs.rename_subst₀_of h as,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) B]

theorem Terms.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (ts : Terms k Ξ) → (ts.subst₀ σ).rename α = ts.subst₀ σ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst₀, Terms.rename, Terms.subst₀,
      Terms.rename_subst₀_of h ts,
      Term.rename_subst₀_of h t]

theorem Motives.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (Cs : Motives k Ξ) → (Cs.subst₀ σ).rename α = Cs.subst₀ σ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst₀, Motives.rename, Motives.subst₀,
      Motives.rename_subst₀_of h Cs,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) C]

theorem Branches.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (us : Branches k Ξ) → (us.subst₀ σ).rename α = us.subst₀ σ'
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.subst₀, Branches.rename, Branches.subst₀,
      Branches.rename_subst₀_of h us,
      Term.rename_subst₀_of (Subst₀.liftN_rename_after_of _ (Subst₀.liftN_rename_after_of _ h)) u]


theorem Telescope.rename_subst₀_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ} {σ' : Subst₀ k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst₀ σ).rename α = Θ.subst₀ σ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst₀, Telescope.rename, Telescope.subst₀,
      Telescope.rename_subst₀_of (Subst₀.lift_rename_after_of h) Θ,
      Term.rename_subst₀_of h A]

theorem States.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (Ss : States k Ξ) → (Ss.subst₀ σ).rename α = Ss.subst₀ σ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst₀, States.rename, States.subst₀,
      States.rename_subst₀_of h Ss,
      Telescope.rename_subst₀_of (Subst₀.liftN_rename_after_of _ h) S]

theorem CorecBranches.rename_subst₀_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (vs : CorecBranches k Ξ) → (vs.subst₀ σ).rename α = vs.subst₀ σ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.subst₀, CorecBranches.rename, CorecBranches.subst₀,
      CorecBranches.rename_subst₀_of h vs,
      Term.rename_subst₀_of
        (Subst₀.liftN_rename_after_of _ (Subst₀.liftN_rename_after_of _
          (Subst₀.liftN_rename_after_of _ h))) v]

end

/-- Substituting a value by `σ` then renaming it by `α` is substituting it by their composition
`σ'`. -/
theorem Val.rename_subst₀_of {Γ Δ Ξ : Scope} {a : Scope.Entry} {σ : Subst₀ k Δ Ξ} {α : Ren Γ Δ}
    {σ' : Subst₀ k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ x).rename α = σ' x) :
    (v : Val k Ξ a) → (v.subst₀ σ).rename α = v.subst₀ σ'
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
    ∀ (n : Nat) (α : Ren Γ Δ) (x : Var Δ a), Ren.liftN n α (x.weakenN n) = (α x).weakenN n
  | 0, _, _ => rfl
  | n + 1, α, x => Ren.liftN_weakenN (Γ := .var :: Γ) (Δ := .var :: Δ) n (Ren.lift α) x.succ

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
    ∀ (ps : List Parameter) (α : Ren Γ Δ),
      (Args.bound (k := k) (Γ := Δ) ps).rename (Ren.liftN ps.length α) = Args.bound ps
  | [], _ => rfl
  | _ :: ps, α => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).rename (Ren.liftN ps.length (Ren.lift α)))
        ((Args.bound (Γ := .var :: Δ) ps).rename (Ren.liftN ps.length (Ren.lift α))) =
      Args.cons (Term.var₀ (Var.weakenN ps.length .zero)) (Args.bound (Γ := .var :: Γ) ps)
    rw [Args.bound_rename ps (Ren.lift α), Term.rename, Ren.liftN_weakenN]
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
  by rw [← Term.subst₀_rename_of (α := fun x => x) h t, Term.rename_id]

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
    rw [Term.subst₀_rename_of (α := Ren.weakenN ps.length) (σ' := Subst₀.id)
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
    rw [Val.subst₀_rename_of (σ := Subst₀.single (t.subst₀ σ)) (α := Ren.weaken) (σ' := Subst₀.id)
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
    {α₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {α₂ : Ren Ψ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename α₁ = σ₂ (α₂ x)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst₀.lift σ₁ x).rename (Ren.lift α₁) = Subst₀.lift σ₂ (Ren.lift α₂ x)
  | _, .zero => rfl
  | _, .succ x => by
    show ((σ₁ x).rename Ren.weaken).rename (Ren.lift α₁) = (σ₂ (α₂ x)).rename Ren.weaken
    rw [← h x, Val.rename_rename_of (α₁ := Ren.lift α₁) (α₂ := Ren.weaken) (fun _ => rfl),
      Val.rename_rename_of (α₁ := Ren.weaken) (α₂ := α₁) (fun _ => rfl)]
    rfl

theorem Subst₀.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {σ₁ : Subst₀ k Δ Ξ} {α₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {α₂ : Ren Ψ Ξ},
      (∀ {a} (x : Var Ξ a), (σ₁ x).rename α₁ = σ₂ (α₂ x)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst₀.liftN n σ₁ x).rename (Ren.liftN n α₁) = Subst₀.liftN n σ₂ (Ren.liftN n α₂ x)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => Subst₀.liftN_rename_comm_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) (Ψ := .var :: Ψ) n (Subst₀.lift_rename_comm_of h)

-- ADE: `wk-β`, in `Definition/Untyped/Properties.agda`.
/-- `B[t̄ / x̄][α] = B[α⇑][t̄[α] / x̄]`. -/
theorem Term.instantiate_rename {Γ Δ : Scope} (α : Ren Γ Δ) :
    {ps : List Parameter} → (B : Term k (Δ.extend ps.length)) → (ts : Args k Δ ps) →
      (B.instantiate ts).rename α = (B.rename (Ren.liftN ps.length α)).instantiate (ts.rename α)
  | [], _, .nil => rfl
  | _ :: ps, B, .cons t ts => by
    show (Term.instantiate (B.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) ts).rename α =
      Term.instantiate ((B.rename (Ren.liftN ps.length (Ren.lift α))).subst₀
        (Subst₀.liftN ps.length (Subst₀.single (t.rename α)))) (ts.rename α)
    rw [Term.instantiate_rename α]
    congr 1
    exact (Term.rename_subst₀_of (fun _ => rfl) B).trans ((Term.subst₀_congr
      (Subst₀.liftN_rename_comm_of ps.length (σ₂ := Subst₀.single (t.rename α)) (α₂ := Ren.lift α)
        fun x => by cases x <;> rfl) B).trans (Term.subst₀_rename_of (fun _ => rfl) B).symm)

/-! ### Substitutions of the Second Order after Renamings -/

theorem Subst.lift_rename_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    ∀ {a} (x : Var (b :: Ξ) a), Subst.lift θ (Ren.lift α x) = Subst.lift θ' x
  | _, .zero => rfl
  | _, .succ x => congrArg (fun t => Term.rename (Ren.liftN _ Ren.weaken) t) (h x)

theorem Subst.liftN_rename_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {θ : Subst k Γ Δ} {α : Ren Δ Ξ} {θ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), θ (α x) = θ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a), Subst.liftN n θ (Ren.liftN n α x) = Subst.liftN n θ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_of (Γ := .var :: Γ) (Δ := .var :: Δ) (Ξ := .var :: Ξ) n
      (Subst.lift_rename_of h)

mutual

-- ADE: `subst-wk`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Renaming by `α` then substituting by `θ` is substituting by their composition `θ'`. -/
theorem Term.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (t : Term k Ξ) → (t.rename α).subst θ = t.subst θ'
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

theorem Args.subst_rename_of {Γ Δ Ξ : Scope} {a : List Parameter} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (ts : Args k Ξ a) → (ts.rename α).subst θ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.subst, Args.subst, Term.subst_rename_of h t, Args.subst_rename_of h ts]

theorem InstanceArgs.subst_rename_of {Γ Δ Ξ Ψ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.rename α).subst θ = as.subst θ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.subst_rename_of h as, Term.subst_rename_of (Subst.liftN_rename_of _ h) B]

theorem Terms.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (ts : Terms k Ξ) → (ts.rename α).subst θ = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.subst, Terms.subst,
      Terms.subst_rename_of h ts, Term.subst_rename_of h t]

theorem Motives.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (Cs : Motives k Ξ) → (Cs.rename α).subst θ = Cs.subst θ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.subst, Motives.subst,
      Motives.subst_rename_of h Cs, Term.subst_rename_of (Subst.liftN_rename_of _ h) C]

theorem Branches.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (us : Branches k Ξ) → (us.rename α).subst θ = us.subst θ'
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.subst, Branches.subst,
      Branches.subst_rename_of h us, Term.subst_rename_of (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ h)) u]


theorem Telescope.subst_rename_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {θ : Subst k Γ Δ} {α : Ren Δ Ξ} {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.rename α).subst θ = Θ.subst θ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.subst, Telescope.subst,
      Telescope.subst_rename_of (Subst.lift_rename_of h) Θ, Term.subst_rename_of h A]

theorem States.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (Ss : States k Ξ) → (Ss.rename α).subst θ = Ss.subst θ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.subst, States.subst,
      States.subst_rename_of h Ss, Telescope.subst_rename_of (Subst.liftN_rename_of _ h) S]

theorem CorecBranches.subst_rename_of {Γ Δ Ξ : Scope} {θ : Subst k Γ Δ} {α : Ren Δ Ξ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), θ (α x) = θ' x) :
    (vs : CorecBranches k Ξ) → (vs.rename α).subst θ = vs.subst θ'
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.subst, CorecBranches.subst,
      CorecBranches.subst_rename_of h vs,
      Term.subst_rename_of
        (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ (Subst.liftN_rename_of _ h))) v]

end

/-! ### Renamings after Substitutions of the Second Order -/

/-- `(x̄. x[x̄])[α] = x̄. α(x)[x̄]`. -/
theorem Var.eta_rename {Γ Δ : Scope} {e : Scope.Entry} (α : Ren Γ Δ) (x : Var Δ e) :
    (Var.eta (k := k) x).rename (Ren.liftN e.params.length α) = Var.eta (α x) := by
  rw [Var.eta, Term.rename, Ren.liftN_weakenN, Args.bound_rename]
  rfl

theorem Subst.lift_rename_after_of {Γ Δ Ξ : Scope} {b : Scope.Entry} {θ : Subst k Δ Ξ}
    {α : Ren Γ Δ} {θ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    ∀ {a} (x : Var (b :: Ξ) a),
      (Subst.lift θ x).rename (Ren.liftN a.params.length (Ren.lift α)) = Subst.lift θ' x
  | _, .zero => Var.eta_rename _ _
  | a, .succ x => by
    show ((θ x).rename (Ren.liftN a.params.length Ren.weaken)).rename (Ren.liftN a.params.length (Ren.lift α)) =
      (θ' x).rename (Ren.liftN a.params.length Ren.weaken)
    rw [← h x, Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.lift α) (α₂ := Ren.weaken)
        (α₃ := fun y => (α y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := α)
        (α₃ := fun y => (α y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_after_of {Γ Δ Ξ : Scope} :
    ∀ (n : Nat) {θ : Subst k Δ Ξ} {α : Ren Γ Δ} {θ' : Subst k Γ Ξ},
      (∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        (Subst.liftN n θ x).rename (Ren.liftN a.params.length (Ren.liftN n α)) = Subst.liftN n θ' x
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Subst.liftN_rename_after_of (Γ := .var :: Γ) (Δ := .var :: Δ)
      (Ξ := .var :: Ξ) n (Subst.lift_rename_after_of h)

mutual

-- ADE: `wk-subst`, in `Definition/Untyped/Properties.agda`, for the first order.
/-- Substituting by `θ` then renaming by `α` is substituting by their composition `θ'`, which renames
each abstraction under its variables. -/
theorem Term.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (t : Term k Ξ) → (t.subst θ).rename α = t.subst θ'
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

theorem Args.rename_subst_of {Γ Δ Ξ : Scope} {a : List Parameter} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (ts : Args k Ξ a) → (ts.subst θ).rename α = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Args.subst, Args.rename, Args.subst, Term.rename_subst_of h t, Args.rename_subst_of h ts]

theorem InstanceArgs.rename_subst_of {Γ Δ Ξ Ψ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (as : InstanceArgs k Ξ Ψ) → (as.subst θ).rename α = as.subst θ'
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.rename, InstanceArgs.subst,
      InstanceArgs.rename_subst_of h as, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) B]

theorem Terms.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (ts : Terms k Ξ) → (ts.subst θ).rename α = ts.subst θ'
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.subst, Terms.rename, Terms.subst,
      Terms.rename_subst_of h ts, Term.rename_subst_of h t]

theorem Motives.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (Cs : Motives k Ξ) → (Cs.subst θ).rename α = Cs.subst θ'
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.subst, Motives.rename, Motives.subst,
      Motives.rename_subst_of h Cs, Term.rename_subst_of (Subst.liftN_rename_after_of _ h) C]

theorem Branches.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (us : Branches k Ξ) → (us.subst θ).rename α = us.subst θ'
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.subst, Branches.rename, Branches.subst,
      Branches.rename_subst_of h us, Term.rename_subst_of (Subst.liftN_rename_after_of _ (Subst.liftN_rename_after_of _ h)) u]


theorem Telescope.rename_subst_of {Γ Δ Ξ : Scope} {ps : List Parameter}
    {θ : Subst k Δ Ξ} {α : Ren Γ Δ} {θ' : Subst k Γ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (Θ : Telescope k Ξ ps) → (Θ.subst θ).rename α = Θ.subst θ'
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.subst, Telescope.rename, Telescope.subst,
      Telescope.rename_subst_of (Subst.lift_rename_after_of h) Θ, Term.rename_subst_of h A]

theorem States.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (Ss : States k Ξ) → (Ss.subst θ).rename α = Ss.subst θ'
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.subst, States.rename, States.subst,
      States.rename_subst_of h Ss, Telescope.rename_subst_of (Subst.liftN_rename_after_of _ h) S]

theorem CorecBranches.rename_subst_of {Γ Δ Ξ : Scope} {θ : Subst k Δ Ξ} {α : Ren Γ Δ}
    {θ' : Subst k Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (θ x).rename (Ren.liftN a.params.length α) = θ' x) :
    (vs : CorecBranches k Ξ) → (vs.subst θ).rename α = vs.subst θ'
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
            ((Term.rename_subst_of (fun _ => rfl) u').trans (Term.subst_rename_of (θ := Subst.lift (e := b) θ₁) (α := Ren.weaken)
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
        (α := Ren.liftN _ Ren.weaken) (σ' := Subst₀.liftN _ Subst₀.id)
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
  rw [← Term.subst_rename_of (α := fun x => x) h t, Term.rename_id]

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
    {α₁ : Ren Δ Ξ} {θ₂ : Subst k Ψ Ξ} {α₂ : Ren Γ Ψ}
    (h : ∀ {a} (x : Var Ξ a), θ₁ (α₁ x) = (θ₂ x).rename (Ren.liftN a.params.length α₂)) :
    ∀ {a} (x : Var (b :: Ξ) a),
      Subst.lift θ₁ (Ren.lift α₁ x) = (Subst.lift θ₂ x).rename (Ren.liftN a.params.length (Ren.lift α₂))
  | _, .zero => (Var.eta_rename (Ren.lift α₂) .zero).symm
  | a, .succ x => by
    show (θ₁ (α₁ x)).rename (Ren.liftN a.params.length Ren.weaken) =
      ((θ₂ x).rename (Ren.liftN a.params.length Ren.weaken)).rename (Ren.liftN a.params.length (Ren.lift α₂))
    rw [h x, Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := α₂)
        (α₃ := fun y => (α₂ y).succ) fun _ => rfl),
      Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.lift α₂) (α₂ := Ren.weaken)
        (α₃ := fun y => (α₂ y).succ) fun _ => rfl)]

theorem Subst.liftN_rename_comm_of {Γ Δ Ξ Ψ : Scope} :
    ∀ (n : Nat) {θ₁ : Subst k Γ Δ} {α₁ : Ren Δ Ξ} {θ₂ : Subst k Ψ Ξ} {α₂ : Ren Γ Ψ},
      (∀ {a} (x : Var Ξ a), θ₁ (α₁ x) = (θ₂ x).rename (Ren.liftN a.params.length α₂)) →
      ∀ {a} (x : Var (Ξ.extend n) a),
        Subst.liftN n θ₁ (Ren.liftN n α₁ x) =
          (Subst.liftN n θ₂ x).rename (Ren.liftN a.params.length (Ren.liftN n α₂))
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
      (Subst.liftN_rename_comm_of _ (θ₂ := θ₂) (α₂ := Ren.weaken) fun _ => rfl) _).trans
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

/-! ## Substitutions under New Variables

A term renamed under new variables, substituted under them, is the term substituted, renamed under
them. -/

theorem Term.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ) (t : Term k Δ) :
    (t.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (t.subst θ).rename (Ren.weakenN n) := by
  rw [Term.subst_rename_of (α := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Term.rename_subst_of (fun _ => rfl)]

theorem States.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (Ss : States k Δ) :
    (Ss.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (Ss.subst θ).rename (Ren.weakenN n) := by
  rw [States.subst_rename_of (α := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), States.rename_subst_of (fun _ => rfl)]

theorem Args.subst_liftN_rename_weakenN {Γ Δ : Scope} {ps : List Parameter} (n : Nat) (θ : Subst k Γ Δ)
    (ts : Args k Δ ps) :
    (ts.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (ts.subst θ).rename (Ren.weakenN n) := by
  rw [Args.subst_rename_of (α := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Args.rename_subst_of (fun _ => rfl)]

theorem InstanceArgs.subst_liftN_rename_weakenN {Γ Δ Ξ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (as : InstanceArgs k Δ Ξ) :
    (as.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (as.subst θ).rename (Ren.weakenN n) := by
  rw [InstanceArgs.subst_rename_of (α := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x),
    InstanceArgs.rename_subst_of (fun _ => rfl)]

theorem Motives.subst_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (Cs : Motives k Δ) :
    (Cs.rename (Ren.weakenN n)).subst (Subst.liftN n θ) = (Cs.subst θ).rename (Ren.weakenN n) := by
  rw [Motives.subst_rename_of (α := Ren.weakenN n)
    (θ' := fun x => (θ x).rename (Ren.liftN _ (Ren.weakenN n)))
    (fun x => Subst.liftN_weakenN n θ x), Motives.rename_subst_of (fun _ => rfl)]

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
  (Term.subst_rename_of (Subst.liftN_rename_comm_of n (θ₁ := Subst.lift θ) (α₁ := Ren.weaken)
    (θ₂ := θ) (α₂ := Ren.weaken) fun _ => rfl) t).trans
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

/-- The terms of arguments substituted are the terms of the arguments substituted. -/
theorem Args.terms_subst₀ {Γ Δ : Scope} (σ : Subst₀ k Γ Δ) :
    {ps : List Parameter} → (ts : Args k Δ ps) → (ts.subst₀ σ).terms = ts.terms.subst₀ σ
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg _ (Args.terms_subst₀ σ ts)

/-- `B[t̄ / x̄]` for the terms of arguments is their instantiation. -/
theorem Term.instantiateTerms_terms {Γ : Scope} :
    {ps : List Parameter} → (B : Term k (Γ.extend ps.length)) → (ts : Args k Γ ps) →
      B.instantiateTerms ts.terms = some (B.instantiate ts)
  | [], _, .nil => rfl
  | _ :: _, B, .cons _ ts =>
    Term.instantiateTerms_terms (B.subst₀ (Subst₀.liftN _ (Subst₀.single _))) ts

/-! ## Renamings as Substitutions

A renaming is the substitution of the second order that gives each variable the abstraction of its
image, so that the laws of the substitutions hold for the renamings. -/

/-- The renaming `α` as a substitution of the second order, which gives each variable `x` the
abstraction `ȳ. α(x)[ȳ]`. -/
def Ren.toSubst {Γ Δ : Scope} (α : Ren Γ Δ) : Subst k Γ Δ := fun x => Var.eta (α x)

/-- A substitution that gives each variable the abstraction of its image by a renaming does so
under a new entry. -/
theorem Subst.lift_eta_of {Γ Δ : Scope} {b : Scope.Entry} {θ : Subst k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) :
    ∀ {a} (x : Var (b :: Δ) a), Subst.lift θ x = Var.eta (Ren.lift α x)
  | _, .zero => rfl
  | _, .succ x => by
    show (θ x).rename (Ren.liftN _ Ren.weaken) = _
    rw [h x]
    exact Var.eta_rename Ren.weaken (α x)

/-- A substitution that gives each variable the abstraction of its image by a renaming does so
under new variables. -/
theorem Subst.liftN_eta_of {Γ Δ : Scope} :
    ∀ (n : Nat) {θ : Subst k Γ Δ} {α : Ren Γ Δ}, (∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) →
      ∀ {a} (x : Var (Δ.extend n) a), Subst.liftN n θ x = Var.eta (Ren.liftN n α x)
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
theorem Term.rename_eq_subst_of {Γ Δ : Scope} {α : Ren Γ Δ} {θ : Subst k Γ Δ}
    (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) (t : Term k Δ) : t.rename α = t.subst θ :=
  (Term.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (t.rename α)).symm.trans
    (Term.subst_rename_of (fun x => (h x).symm) t)

/-- A telescope renamed is the telescope substituted by a substitution that gives each variable the
abstraction of its image. -/
theorem Telescope.rename_eq_subst_of {Γ Δ : Scope} {ps : List Parameter} {α : Ren Γ Δ}
    {θ : Subst k Γ Δ} (h : ∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) (Θ : Telescope k Δ ps) :
    Θ.rename α = Θ.subst θ :=
  (Telescope.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Θ.rename α)).symm.trans
    (Telescope.subst_rename_of (fun x => (h x).symm) Θ)

theorem Term.rename_eq_subst {Γ Δ : Scope} (α : Ren Γ Δ) (t : Term k Δ) :
    t.rename α = t.subst (Ren.toSubst α) :=
  (Term.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (t.rename α)).symm.trans
    (Term.subst_rename_of (fun _ => rfl) t)

theorem Args.rename_eq_subst {Γ Δ : Scope} {ps : List Parameter} (α : Ren Γ Δ) (ts : Args k Δ ps) :
    ts.rename α = ts.subst (Ren.toSubst α) :=
  (Args.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (ts.rename α)).symm.trans
    (Args.subst_rename_of (fun _ => rfl) ts)

theorem InstanceArgs.rename_eq_subst {Γ Δ Ξ : Scope} (α : Ren Γ Δ) (as : InstanceArgs k Δ Ξ) :
    as.rename α = as.subst (Ren.toSubst α) :=
  (InstanceArgs.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (as.rename α)).symm.trans
    (InstanceArgs.subst_rename_of (fun _ => rfl) as)

theorem Telescope.rename_eq_subst {Γ Δ : Scope} {ps : List Parameter} (α : Ren Γ Δ)
    (Θ : Telescope k Δ ps) : Θ.rename α = Θ.subst (Ren.toSubst α) :=
  (Telescope.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Θ.rename α)).symm.trans
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
  fun x => (Subst.liftN_eta_of n (α := fun x => x) (fun _ => rfl) x).trans
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

/-! ## Substitutions of the First Order as Renamings -/

-- ADE: none.
/-- A substitution of the first order that gives each variable a variable renames. -/
theorem Term.subst₀_eq_rename_of {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), σ x = .var (α x)) (t : Term k Δ) : t.subst₀ σ = t.rename α := by
  rw [Term.subst₀_eq_subst, Term.rename_eq_subst_of (θ := σ.toSubst) (fun x => by
    show (σ x).eta = _
    rw [h x]
    rfl)]

-- ADE: none.
/-- A substitution of the first order that gives each variable a variable or the term of a
variable renames. -/
theorem Term.subst₀_eq_rename_of_eta {Γ Δ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Γ Δ}
    (h : ∀ {a} (x : Var Δ a), (σ x).eta = Var.eta (α x)) (t : Term k Δ) :
    t.subst₀ σ = t.rename α := by
  rw [Term.subst₀_eq_subst, Term.rename_eq_subst_of (θ := σ.toSubst) h]

-- ADE: none.
/-- A substitution of the first order of a telescope that gives each variable a variable or the term
of a variable renames it. -/
theorem Telescope.subst₀_eq_rename_of_eta {Γ Δ : Scope} {ps : List Parameter} {σ : Subst₀ k Γ Δ}
    {α : Ren Γ Δ} (h : ∀ {a} (x : Var Δ a), (σ x).eta = Var.eta (α x)) (Θ : Telescope k Δ ps) :
    Θ.subst₀ σ = Θ.rename α := by
  rw [Telescope.subst₀_eq_subst, Telescope.rename_eq_subst_of (θ := σ.toSubst) h]

-- ADE: none.
/-- A term renamed then substituted by a substitution that gives each variable a variable or the
term of a variable is the term renamed. -/
theorem Term.subst₀_rename_eq_rename_of {Γ Δ Ξ : Scope} {σ : Subst₀ k Γ Δ} {α : Ren Δ Ξ}
    {ρ : Ren Γ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ (α x)).eta = Var.eta (ρ x)) (t : Term k Ξ) :
    (t.rename α).subst₀ σ = t.rename ρ :=
  (Term.subst₀_rename_of (σ' := fun x => σ (α x)) (fun _ => rfl) t).trans
    (Term.subst₀_eq_rename_of_eta h t)

-- ADE: none.
/-- Substituting then renaming is renaming then substituting, when the two agree on each variable. -/
theorem Term.subst₀_rename_comm_of {Γ Δ Ξ Ψ : Scope} {σ₁ : Subst₀ k Δ Ξ} {α₁ : Ren Γ Δ}
    {σ₂ : Subst₀ k Γ Ψ} {α₂ : Ren Ψ Ξ} (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename α₁ = σ₂ (α₂ x))
    (t : Term k Ξ) : (t.subst₀ σ₁).rename α₁ = (t.rename α₂).subst₀ σ₂ :=
  (Term.rename_subst₀_of (σ' := fun x => σ₂ (α₂ x)) h t).trans
    (Term.subst₀_rename_of (fun _ => rfl) t).symm

-- ADE: none.
/-- Substituting then renaming a telescope is renaming then substituting it, when the two agree on
each variable. -/
theorem Telescope.subst₀_rename_comm_of {Γ Δ Ξ Ψ : Scope} {ps : List Parameter}
    {σ₁ : Subst₀ k Δ Ξ} {α₁ : Ren Γ Δ} {σ₂ : Subst₀ k Γ Ψ} {α₂ : Ren Ψ Ξ}
    (h : ∀ {a} (x : Var Ξ a), (σ₁ x).rename α₁ = σ₂ (α₂ x)) (Θ : Telescope k Ξ ps) :
    (Θ.subst₀ σ₁).rename α₁ = (Θ.rename α₂).subst₀ σ₂ :=
  (Telescope.rename_subst₀_of (σ' := fun x => σ₂ (α₂ x)) h Θ).trans
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
  (Term.subst₀_rename_of (σ := Subst₀.single t) (α := Ren.weaken) (σ' := Subst₀.id)
    (fun _ => rfl) C).trans (Term.subst₀_id C)

end Sic.Core
