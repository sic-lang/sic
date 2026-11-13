module

public import Sic.Core.Substitution
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels

/-!
# Substitutions of the Rules

The substitutions that the rules of annexes 14 and 18 of RFC 36 build: the motive `C[T.c(x̄) / z]` at
a constructor, the corecursor at the variables of its state, the recursive results of a branch, the
motives and the branches at a position and the observations, with their commutation with the
renamings, the substitutions and the instantiation of the levels.

ADE have none of them: their eliminators substitute their constructors in their motives directly,
and they have no codata types.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Motives, Branches and States at a Position -/

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

/-- Motives substituted are as many. -/
theorem Motives.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Cs : Motives k Δ) → (Cs.subst θ).length = Cs.length
  | .nil => rfl
  | .cons _ _ Cs => congrArg (· + 1) (Motives.length_subst θ Cs)

/-- Motives whose levels are instantiated are as many. -/
theorem Motives.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (Cs : Motives k Γ) → (Cs.substLevels ls').length = Cs.length
  | .nil => rfl
  | .cons _ _ Cs => congrArg (· + 1) (Motives.length_substLevels ls' Cs)

/-- Branches substituted are as many. -/
theorem Branches.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (us : Branches k Δ) → (us.subst θ).length = us.length
  | .nil => rfl
  | .cons _ _ _ _ us => congrArg (· + 1) (Branches.length_subst θ us)

/-- Branches whose levels are instantiated are as many. -/
theorem Branches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (us : Branches k Γ) → (us.substLevels ls').length = us.length
  | .nil => rfl
  | .cons _ _ _ _ us => congrArg (· + 1) (Branches.length_substLevels ls' us)

/-- The grades of the recursive results of a branch of branches substituted are those of the
branch. -/
theorem Branches.grades_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (us : Branches k Δ) → (i : Nat) → (us.subst θ).grades i = us.grades i
  | .nil, _ => rfl
  | .cons .., 0 => rfl
  | .cons _ _ _ _ us, i + 1 => Branches.grades_subst θ us i

/-- The grades of the recursive results of a branch of branches whose levels are instantiated are
those of the branch. -/
theorem Branches.grades_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (us : Branches k Γ) → (i : Nat) → (us.substLevels ls').grades i = us.grades i
  | .nil, _ => rfl
  | .cons .., 0 => rfl
  | .cons _ _ _ _ us, i + 1 => Branches.grades_substLevels ls' us i

/-- The state at a position of states substituted is the state substituted, under its
variables. -/
theorem States.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Ss : States k Δ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k (Δ.extend n) ps} →
      Ss.get j = some ⟨n, ps, S⟩ → (Ss.subst θ).get j = some ⟨n, ps, S.subst (Subst.liftN n θ)⟩
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; rfl
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_subst θ (Ss := Ss) h

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

/-- A state at a position of states substituted is a state of the states, substituted. -/
theorem States.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {Ss : States k Δ} → {j n : Nat} → {ps : List Parameter} → {S : Telescope k (Γ.extend n) ps} →
      (Ss.subst θ).get j = some ⟨n, ps, S⟩ →
        ∃ S₀, Ss.get j = some ⟨n, ps, S₀⟩ ∧ S = S₀.subst (Subst.liftN n θ)
  | .nil, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ Ss, _ + 1, _, _, _, h => States.get_subst_inv θ (Ss := Ss) h

/-- States substituted are as many. -/
theorem States.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Ss : States k Δ) → (Ss.subst θ).length = Ss.length
  | .nil => rfl
  | .cons _ _ _ Ss => congrArg (· + 1) (States.length_subst θ Ss)

/-- The states of a corecursor whose levels are instantiated are as many. -/
theorem States.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (Ss : States k Γ) → (Ss.substLevels ls').length = Ss.length
  | .nil => rfl
  | .cons _ _ _ Ss => congrArg (· + 1) (States.length_substLevels ls' Ss)

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

/-- Branches of a corecursor substituted are as many. -/
theorem CorecBranches.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (vs : CorecBranches k Δ) → (vs.subst θ).length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (CorecBranches.length_subst θ vs)

/-- The branches of a corecursor whose levels are instantiated are as many. -/
theorem CorecBranches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (vs : CorecBranches k Γ) → (vs.substLevels ls').length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (CorecBranches.length_substLevels ls' vs)

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
    rw [Term.subst₀, InstanceArgs.subst₀_rename_of (α := Ren.weakenN fs.length) (σ' := Subst₀.id)
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

-- ADE: none.
/-- A motive that does not depend on the term it eliminates, at a constructor, is the motive under
the variables of the fields. -/
theorem Term.atCtor_rename_weaken {Γ Δ : Scope} (C : Term k Γ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name)
    (fs : List Parameter) :
    (C.rename Ren.weaken).atCtor D qs ls ps as c fs = C.rename (Ren.weakenN fs.length) := by
  rw [Term.atCtor, Term.rename_rename_of (α₁ := Ren.lift (Ren.weakenN fs.length))
    (α₂ := Ren.weaken) (α₃ := fun x => .succ (Ren.weakenN fs.length x)) (fun _ => rfl),
    Term.subst₀_rename_of (α := fun x => .succ (Ren.weakenN fs.length x))
      (σ' := fun x => .var (Ren.weakenN fs.length x)) (fun _ => rfl)]
  exact Term.subst₀_eq_rename_of (fun _ => rfl) C

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
    InstanceArgs.subst₀_rename_of (α := Ren.weakenN ps'.length) (σ' := Subst₀.id)
      (fun y => Args.toSubst₀_weakenN ts y),
    InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    Term.subst₀_rename_of (α := Ren.weakenN ps'.length) (σ' := Subst₀.id)
      (fun y => Args.toSubst₀_weakenN ts y),
    Term.subst₀_id, ← Args.terms_subst₀, Args.bound_toSubst₀]

/-- A position of a destructor in destructors, at instantiated levels. -/
def Destructors.Pos.substLevels {k' : Nat} (ls' : Fin k → Level k') {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → Destructors.Pos d p q ds Ξ Θ B ψ →
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
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
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
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
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
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {θ : Subst k Γ' Γ} → {θ' : Subst k'' Γ' Γ} →
      (∀ {a} (x : Var Γ a), (θ x).substLevels ls' = θ' x) →
      ∀ {a} (x : Var Ξ a), ((hd.obsSubst o θ) x).substLevels ls' = hd.obsSubst o' θ' x
  | _, _, _, _, _, _, _, .here, _, _, h => h
  | _, _, _, _, _, _, _, .there h', _, _, h => h'.obsSubst_substLevels ls' ho fun x =>
    match x with
    | .zero => ho _ _
    | .succ x => h x

/-- The substitution of the destructors before a position by the observations of a term, substituted,
is the substitution by the observations of the term substituted, at the arguments substituted. -/
theorem Destructors.Pos.obsSubst_observation_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ' Δ) (t : Term k Γ') {d : Name} {p q : Grade} {ps' : List Parameter}
    {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
    (hd : Destructors.Pos d p q ds Ξ Θ B ψ) :
    ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
          (Subst.liftN a.params.length σ) =
        hd.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
  hd.obsSubst_subst σ (fun d ps' => Term.observation_subst σ D qs ls ps as t d ps')
    (InstanceArgs.toSubst_subst σ as)

/-! ## Corecursors at Their State -/

-- ADE: none.
/-- `corec_r T from ȳ return Θ̄ with ḡ`: the corecursor of the instance `T = D.{s̄; l̄; p̄} ā` at the
new variables `ȳ` of a state, whose entries have the parameters `ps`, as its state, the term whose
observations the types of the branches of the type `D` observe. -/
def Term.corecAt {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (Ss : States k Γ) (gs : CorecBranches k Γ)
    (ps' : List Parameter) : Term k (Γ.extend ps'.length) :=
  .corec r D qs ls ps (as.rename (Ren.weakenN ps'.length)) (Args.bound ps').terms
    (Ss.rename (Ren.weakenN ps'.length)) (gs.rename (Ren.weakenN ps'.length))

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

-- ADE: none.
/-- The corecursor from the variables of a state, renamed under the variables of the state, is the
corecursor from these variables of its instance, states and branches renamed. -/
theorem Term.corecAt_rename {Γ Δ Ξ : Scope} (α : Ren Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (Ss : States k Δ) (gs : CorecBranches k Δ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').rename (Ren.liftN ps'.length α) =
      Term.corecAt r D qs ls ps (as.rename α) (Ss.rename α) (gs.rename α) ps' := by
  rw [Term.rename_eq_subst_of (θ := Subst.liftN ps'.length (Ren.toSubst α))
      (Subst.liftN_eta_of ps'.length (fun _ => rfl)),
    Term.corecAt_subst, ← InstanceArgs.rename_eq_subst,
    (States.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Ss.rename α)).symm.trans
      (States.subst_rename_of (fun _ => rfl) Ss),
    (CorecBranches.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (gs.rename α)).symm.trans
      (CorecBranches.subst_rename_of (fun _ => rfl) gs)]
  rfl

/-- The substitution of the destructors before a position by the observations of a corecursor at
the variables of its state, substituted under them, is the substitution by the observations of the
corecursor substituted. -/
theorem Destructors.Pos.obsSubst_corecAt_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ' Δ) (Ss : States k Γ') (gs : CorecBranches k Γ')
    (ps'' : List Parameter) {d : Name} {p q : Grade} {ps' : List Parameter} {ns : List Name}
    {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
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

end Sic.Core
