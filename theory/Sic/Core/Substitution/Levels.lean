module

public import Sic.Core.Substitution
import Sic.Core.Substitution.Composition

/-!
# Instantiation of the Levels

The laws of the instantiation `[l̄' / l̄]` of the level variables of annex 09 of RFC 36: it replaces
levels only, so that it commutes with the renamings and the substitutions, and the instantiations
compose; the instance of a declaration of the signature at levels; a variable declared in a context
is declared, with its type instantiated, in the context instantiated.

ADE have no level variables.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

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
theorem Term.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') (α : Ren Γ Δ) :
    (t : Term k Δ) → (t.rename α).substLevels ls' = (t.substLevels ls').rename α
  | .var x ts => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      Args.substLevels_rename ls' α ts]
  | .sort _ => rfl
  | .const .. => rfl
  | .inst D qs ls ps as => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' α as]
  | .ctor D qs ls ps as c ts => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' α as, Terms.substLevels_rename ls' α ts]
  | .recursor r D qs ls ps as t Cs us => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' α as, Term.substLevels_rename ls' α t,
      Motives.substLevels_rename ls' α Cs, Branches.substLevels_rename ls' α us]
  | .obs D qs ls ps as t d bs => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' α as, Term.substLevels_rename ls' α t,
      Terms.substLevels_rename ls' α bs]
  | .corec r D qs ls ps as ss Ss vs => by
    rw [Term.rename, Term.substLevels, Term.substLevels, Term.rename,
      InstanceArgs.substLevels_rename ls' α as, Terms.substLevels_rename ls' α ss,
      States.substLevels_rename ls' α Ss, CorecBranches.substLevels_rename ls' α vs]

theorem Args.substLevels_rename {k' : Nat} {Γ Δ : Scope} {a : List Parameter} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) : (ts : Args k Δ a) → (ts.rename α).substLevels ls'
      = (ts.substLevels ls').rename α
  | .nil => rfl
  | .cons t ts => by
    rw [Args.rename, Args.substLevels, Args.substLevels, Args.rename,
      Term.substLevels_rename ls' α t, Args.substLevels_rename ls' α ts]

theorem InstanceArgs.substLevels_rename {k' : Nat} {Γ Δ Ξ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (as : InstanceArgs k Δ Ξ) → (as.rename α).substLevels ls' = (as.substLevels ls').rename α
  | .nil => rfl
  | .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.substLevels, InstanceArgs.substLevels,
      InstanceArgs.rename, InstanceArgs.substLevels_rename ls' α as, Term.substLevels_rename]

theorem Terms.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (ts : Terms k Δ) → (ts.rename α).substLevels ls' = (ts.substLevels ls').rename α
  | .nil => rfl
  | .cons t ts => by
    rw [Terms.rename, Terms.substLevels, Terms.substLevels, Terms.rename,
      Terms.substLevels_rename ls' α ts, Term.substLevels_rename]

theorem Motives.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (Cs : Motives k Δ) → (Cs.rename α).substLevels ls' = (Cs.substLevels ls').rename α
  | .nil => rfl
  | .cons n C Cs => by
    rw [Motives.rename, Motives.substLevels, Motives.substLevels, Motives.rename,
      Motives.substLevels_rename ls' α Cs, Term.substLevels_rename]

theorem Branches.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (us : Branches k Δ) → (us.rename α).substLevels ls' = (us.substLevels ls').rename α
  | .nil => rfl
  | .cons n m es u us => by
    rw [Branches.rename, Branches.substLevels, Branches.substLevels, Branches.rename,
      Branches.substLevels_rename ls' α us, Term.substLevels_rename]


theorem Telescope.substLevels_rename {k' : Nat} {Γ Δ : Scope} {ps : List Parameter}
    (ls' : Fin k → Level k') (α : Ren Γ Δ) :
    (Θ : Telescope k Δ ps) → (Θ.rename α).substLevels ls' = (Θ.substLevels ls').rename α
  | .nil => rfl
  | .cons q p A Θ => by
    rw [Telescope.rename, Telescope.substLevels, Telescope.substLevels, Telescope.rename,
      Telescope.substLevels_rename ls' (Ren.lift α) Θ, Term.substLevels_rename]

/-- The levels of renamed destructors are instantiated as those of the destructors. -/
theorem Destructors.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    {ns : List Name} → (ds : Destructors k Δ ns) →
      (ds.rename α).substLevels ls' = (ds.substLevels ls').rename α
  | _, .nil => rfl
  | _, .cons p q Θ B ψ ds => by
    rw [Destructors.rename, Destructors.substLevels, Destructors.substLevels, Destructors.rename,
      Destructors.substLevels_rename ls' (Ren.lift α) ds, Telescope.substLevels_rename,
      Term.substLevels_rename]

theorem States.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (Ss : States k Δ) → (Ss.rename α).substLevels ls' = (Ss.substLevels ls').rename α
  | .nil => rfl
  | .cons n S κs Ss => by
    rw [States.rename, States.substLevels, States.substLevels, States.rename,
      States.substLevels_rename ls' α Ss, Telescope.substLevels_rename]

theorem CorecBranches.substLevels_rename {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) :
    (vs : CorecBranches k Δ) → (vs.rename α).substLevels ls' = (vs.substLevels ls').rename α
  | .nil => rfl
  | .cons n m a v vs => by
    rw [CorecBranches.rename, CorecBranches.substLevels, CorecBranches.substLevels,
      CorecBranches.rename,
      CorecBranches.substLevels_rename ls' α vs, Term.substLevels_rename]

end

/-- The instantiation of the level variables of a value commutes with the renamings. -/
theorem Val.substLevels_rename {k' : Nat} {Γ Δ : Scope} {a : Scope.Entry} (ls' : Fin k → Level k')
    (α : Ren Γ Δ) : (v : Val k Δ a) → (v.rename α).substLevels ls' = (v.substLevels ls').rename α
  | .var _ => rfl
  | .term t => congrArg Val.term (Term.substLevels_rename ls' α t)

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

/-- `A[s̄' / s̄, l̄' / l̄, p̄' / p̄]`: the type or the body `A` of an entry of the signature at the
instance `ι` of its sort and grade variables, then at the levels `l̄'`, weakened from the empty scope
to the scope `Γ`.
RFC: `\mathsf{inst}_e` -/
def Signature.instanceType {k k' j g : Nat} {Γ : Scope} (A : Instance j g → Term k' [])
    (ι : Instance j g) (ls : Fin k' → Level k) : Term k Γ :=
  ((A ι).substLevels ls).weakenClosed

/-- An entry of the signature at the levels `ls`, then instantiated by `ls'`, is the entry at the
levels `ls` instantiated by `ls'`. -/
theorem Signature.instanceType_substLevels {k k' k'' j g : Nat} {Γ : Scope}
    (A : Instance j g → Term k' []) (ι : Instance j g) (ls : Fin k' → Level k)
    (ls' : Fin k → Level k'') :
    (Signature.instanceType A ι ls : Term k Γ).substLevels ls'
      = Signature.instanceType A ι fun i => (ls i).subst ls' := by
  rw [Signature.instanceType, Signature.instanceType, Term.weakenClosed, Term.weakenClosed,
    Term.substLevels_rename, Term.substLevels_substLevels]

/-! ## Entries of Contexts -/

/-- A variable declared in a context is declared, with its type instantiated, in the context
instantiated. -/
theorem Context.VarIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {x : Var Γ .var} {A : Term k Γ} :
    ctx.VarIn x A → (ctx.substLevels ls').VarIn x (A.substLevels ls')
  | .zero => by rw [Term.substLevels_rename]; exact .zero
  | .succVar h => by rw [Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by rw [Term.substLevels_rename]; exact .succSecondOrder (h.substLevels ls')

/-- A second-order variable declared in a context is declared, with its telescope and its type
instantiated, in the context instantiated. -/
theorem Context.SecondOrderIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)}
    {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
    ctx.SecondOrderIn X Θ A →
      (ctx.substLevels ls').SecondOrderIn X (Θ.substLevels ls') (A.substLevels ls')
  | .zero => by rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .zero
  | .succVar h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]
    exact .succSecondOrder (h.substLevels ls')

end Sic.Core
