module

public import Sic.Core.Substitution
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels

/-!
# Substitutions of the Rules

The substitutions that the rules of annexes 15 and 21 of RFC 36 build: the motive `C[T.c(x̄) / z]` at
a constructor, the corecursor at the variables of its state, the motives and the branches at a
position and the observations, with their commutation with the renamings, the substitutions and the
instantiation of the levels.

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

/-- The branch at a position of the branches of the destructors substituted is the branch
substituted, under its variables. -/
theorem DestructorBranches.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {vs : DestructorBranches k Δ} → {i n m a : Nat} →
    {v : Term k (((Δ.extend n).extend m).extend a)} →
      vs.get i = some ⟨n, m, a, v⟩ →
        (vs.subst θ).get i =
          some ⟨n, m, a, v.subst (Subst.liftN a (Subst.liftN m (Subst.liftN n θ)))⟩
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => DestructorBranches.get_subst θ (vs := vs) h

/-- The branch at a position of the branches of the destructors whose levels are instantiated is a
branch of the branches, instantiated. -/
theorem DestructorBranches.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {vs : DestructorBranches k Γ} → {i n m a : Nat} →
    {v : Term k' (((Γ.extend n).extend m).extend a)} →
      (vs.substLevels ls').get i = some ⟨n, m, a, v⟩ →
        ∃ v₀, vs.get i = some ⟨n, m, a, v₀⟩ ∧ v = v₀.substLevels ls'
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => DestructorBranches.get_substLevels ls' (vs := vs) h

/-- The branch at a position of the branches of the destructors is there once their levels are
instantiated. -/
theorem DestructorBranches.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {vs : DestructorBranches k Γ} → {i n m a : Nat} →
    {v : Term k (((Γ.extend n).extend m).extend a)} →
      vs.get i = some ⟨n, m, a, v⟩ → (vs.substLevels ls').get i = some ⟨n, m, a, v.substLevels ls'⟩
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; rfl
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => DestructorBranches.get_substLevels_of ls' (vs := vs) h

/-- A branch at a position of the branches of the destructors substituted is a branch of the
branches, substituted. -/
theorem DestructorBranches.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {vs : DestructorBranches k Δ} → {i n m a : Nat} →
    {v : Term k (((Γ.extend n).extend m).extend a)} →
      (vs.subst θ).get i = some ⟨n, m, a, v⟩ →
        ∃ v₀, vs.get i = some ⟨n, m, a, v₀⟩ ∧
          v = v₀.subst (Subst.liftN a (Subst.liftN m (Subst.liftN n θ)))
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons .., 0, _, _, _, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ _ _ _ vs, _ + 1, _, _, _, _, h => DestructorBranches.get_subst_inv θ (vs := vs) h

/-- Branches of the destructors substituted are as many. -/
theorem DestructorBranches.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (vs : DestructorBranches k Δ) → (vs.subst θ).length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (DestructorBranches.length_subst θ vs)

/-- The branches of the destructors whose levels are instantiated are as many. -/
theorem DestructorBranches.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (vs : DestructorBranches k Γ) → (vs.substLevels ls').length = vs.length
  | .nil => rfl
  | .cons _ _ _ _ vs => congrArg (· + 1) (DestructorBranches.length_substLevels ls' vs)

/-- The term at a position of terms substituted is the term substituted. -/
theorem Terms.get_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {ts : Terms k Δ} → {j : Nat} → {t : Term k Δ} → ts.get j = some t →
      (ts.subst θ).get j = some (t.subst θ)
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, h => by cases h; rfl
  | .cons _ ts, _ + 1, _, h => Terms.get_subst θ (ts := ts) h

/-- A term at a position of terms substituted is a term of the terms, substituted. -/
theorem Terms.get_subst_inv {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {ts : Terms k Δ} → {j : Nat} → {t : Term k Γ} → (ts.subst θ).get j = some t →
      ∃ t₀, ts.get j = some t₀ ∧ t = t₀.subst θ
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ ts, _ + 1, _, h => Terms.get_subst_inv θ (ts := ts) h

/-- Terms substituted are as many. -/
theorem Terms.length_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (ts : Terms k Δ) → (ts.subst θ).length = ts.length
  | .nil => rfl
  | .cons _ ts => congrArg (· + 1) (Terms.length_subst θ ts)

/-- The term at a position of terms is there once their levels are instantiated. -/
theorem Terms.get_substLevels_of {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {ts : Terms k Γ} → {j : Nat} → {t : Term k Γ} → ts.get j = some t →
      (ts.substLevels ls').get j = some (t.substLevels ls')
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, h => by cases h; rfl
  | .cons _ ts, _ + 1, _, h => Terms.get_substLevels_of ls' (ts := ts) h

/-- A term at a position of terms whose levels are instantiated is a term of the terms,
instantiated. -/
theorem Terms.get_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {ts : Terms k Γ} → {j : Nat} → {t : Term k' Γ} → (ts.substLevels ls').get j = some t →
      ∃ t₀, ts.get j = some t₀ ∧ t = t₀.substLevels ls'
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | .cons _ ts, _ + 1, _, h => Terms.get_substLevels ls' (ts := ts) h

/-- Terms whose levels are instantiated are as many. -/
theorem Terms.length_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    (ts : Terms k Γ) → (ts.substLevels ls').length = ts.length
  | .nil => rfl
  | .cons _ ts => congrArg (· + 1) (Terms.length_substLevels ls' ts)

/-! ## Motives at a Constructor -/

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

/-! ## Recursors at a Variable -/

/-- `z. rec_{r; ς; χ} T z return C̄ : κ with ū`: the recursor of the instance `T = D.{s̄; l̄; p̄} ā`
on a new variable `z`, the recursive result `f(D, z)` of a term `z` of the type `D` of the block
that the computation of a recursor gives. -/
def Term.recursorAt {Γ Δ : Scope} (r ς χ : Grade) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (κ : Universe k) (Cs : Motives k Γ)
    (us : Branches k Γ) (D : Name) : Term k (.var :: Γ) :=
  .recursor r ς χ D qs ls ps (as.rename Ren.weaken) (.var .zero .nil) κ (Cs.rename Ren.weaken)
    (us.rename Ren.weaken)

/-- `(z. rec T z return C̄ with ū)[t / z] = rec T t return C̄ with ū`: the recursor on a variable,
at a term, is the recursor on this term. -/
theorem Term.recursorAt_subst₀ {Γ Δ : Scope} (r ς χ : Grade) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (κ : Universe k)
    (Cs : Motives k Γ) (us : Branches k Γ) (D : Name) (t : Term k Γ) :
    (Term.recursorAt r ς χ qs ls ps as κ Cs us D).subst₀ (Subst₀.single t) =
      .recursor r ς χ D qs ls ps as t κ Cs us := by
  have h : ∀ {a} (y : Var Γ a), Subst₀.single t (Ren.weaken y) = Subst₀.id y := fun _ => rfl
  rw [Term.recursorAt, Term.subst₀, InstanceArgs.subst₀_rename_of (σ' := Subst₀.id) h,
    InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    Motives.subst₀_rename_of (σ' := Subst₀.id) h,
    Motives.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    Branches.subst₀_rename_of (σ' := Subst₀.id) h,
    Branches.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl)]
  rfl

/-- The recursor on a variable, substituted under this variable, is the recursor substituted, on
the variable. -/
theorem Term.recursorAt_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (r ς χ : Grade)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (κ : Universe k) (Cs : Motives k Δ) (us : Branches k Δ) (D : Name) :
    (Term.recursorAt r ς χ qs ls ps as κ Cs us D).subst (Subst.lift θ) =
      Term.recursorAt r ς χ qs ls ps (as.subst θ) κ (Cs.subst θ) (us.subst θ) D := by
  rw [Term.recursorAt, Term.subst, InstanceArgs.subst_rename_of (fun _ => rfl),
    Motives.subst_rename_of (fun _ => rfl), Branches.subst_rename_of (fun _ => rfl),
    Term.recursorAt, InstanceArgs.rename_subst_of (fun _ => rfl),
    Motives.rename_subst_of (fun _ => rfl), Branches.rename_subst_of (fun _ => rfl)]
  rfl

/-- The recursor on a variable, at instantiated levels, is the recursor at these levels, on the
variable. -/
theorem Term.recursorAt_substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (r ς χ : Grade) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ Δ) (κ : Universe k) (Cs : Motives k Γ) (us : Branches k Γ) (D : Name) :
    (Term.recursorAt r ς χ qs ls ps as κ Cs us D).substLevels ls' =
      Term.recursorAt r ς χ qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
        (κ.substLevels ls') (Cs.substLevels ls') (us.substLevels ls') D := by
  simp only [Term.recursorAt, Term.substLevels, InstanceArgs.substLevels_rename,
    Motives.substLevels_rename, Branches.substLevels_rename, Args.substLevels]

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

/-- The observation of a term, renamed under the variables of its arguments, is the observation of
the term renamed. -/
theorem Term.observation_rename {Γ Δ Ξ : Scope} (α : Ren Γ Δ) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ) (t : Term k Δ) (d : Name)
    (ps' : List Parameter) :
    (t.observation D qs ls ps as d ps').rename (Ren.liftN ps'.length α) =
      (t.rename α).observation D qs ls ps (as.rename α) d ps' := by
  rw [Term.rename_eq_subst_of (θ := Subst.liftN ps'.length (Ren.toSubst α))
      (Subst.liftN_eta_of ps'.length (fun _ => rfl)),
    Term.observation_subst, ← Term.rename_eq_subst, ← InstanceArgs.rename_eq_subst]

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
def Destructors.Pos.substLevels {k' : Nat} (ls' : Fin k → Level k') {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        Destructors.Pos d p q ς (ds.substLevels ls') Ξ (Θ.substLevels ls') (B.substLevels ls') ψ
  | _, _, _, _, _, _, _, .here => .here
  | _, _, _, _, _, _, _, .there h => .there (h.substLevels ls')

/-- The substitution of the destructors before a position is the same at instantiated levels, since
it reads only the scopes. -/
theorem Destructors.Pos.obsSubst_posSubstLevels {k' k'' : Nat} {Γ' : Scope}
    (ls' : Fin k' → Level k'')
    (o : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
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
    (ho : ∀ d ps', (o d ps').subst (Subst.liftN ps'.length σ) = o' d ps') {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
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
    (ho : ∀ d ps', (o d ps').substLevels ls' = o' d ps') {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {θ : Subst k Γ' Γ} → {θ' : Subst k'' Γ' Γ} →
      (∀ {a} (x : Var Γ a), (θ x).substLevels ls' = θ' x) →
      ∀ {a} (x : Var Ξ a), ((hd.obsSubst o θ) x).substLevels ls' = hd.obsSubst o' θ' x
  | _, _, _, _, _, _, _, .here, _, _, h => h
  | _, _, _, _, _, _, _, .there h', _, _, h => h'.obsSubst_substLevels ls' ho fun x =>
    match x with
    | .zero => ho _ _
    | .succ x => h x

/-- The substitution of the destructors before a position by the observations of a term, at
instantiated levels, is the substitution by the observations of the term at these levels, at the
arguments at these levels. -/
theorem Destructors.Pos.obsSubst_observation_substLevels {k' k'' : Nat} {Γ' Δ : Scope}
    (ls' : Fin k → Level k'') (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ' Δ) (t : Term k Γ') {d : Name} {p q ς : Grade}
    {ps' : List Parameter} {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope}
    {Θ : Telescope k' Ξ ps'} {B : Term k' (Ξ.extend ps'.length)}
    {ψ : ResultOwnership Grade ps'.length} (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) :
    ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst (t.observation D qs ls ps as) as.toSubst) x).substLevels ls' =
        hd.obsSubst ((t.substLevels ls').observation D qs (ls.map (Level.subst ls')) ps
          (as.substLevels ls')) (as.substLevels ls').toSubst x :=
  hd.obsSubst_substLevels ls' (fun d ps' => Term.observation_substLevels ls' D qs ls ps as t d ps')
    (InstanceArgs.toSubst_substLevels ls' as)

/-- The substitution of the destructors before a position by the observations of a term, substituted,
is the substitution by the observations of the term substituted, at the arguments substituted. -/
theorem Destructors.Pos.obsSubst_observation_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ' Δ) (t : Term k Γ') {d : Name} {p q ς : Grade} {ps' : List Parameter}
    {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
    (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) :
    ∀ {a} (x : Var Ξ a),
      ((hd.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
          (Subst.liftN a.params.length σ) =
        hd.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
  hd.obsSubst_subst σ (fun d ps' => Term.observation_subst σ D qs ls ps as t d ps')
    (InstanceArgs.toSubst_subst σ as)

/-- The substitution of the destructors before a position by the observations of a term, renamed,
is the substitution by the observations of the term renamed, at the arguments renamed. -/
theorem Destructors.Pos.obsSubst_observation_rename {k' : Nat} {Γ' Γ'' Δ : Scope}
    (α : Ren Γ'' Γ') (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ' Δ) (t : Term k Γ') {d : Name} {p q ς : Grade} {ps' : List Parameter}
    {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
    (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) {a : Scope.Entry} (x : Var Ξ a) :
    ((hd.obsSubst (t.observation D qs ls ps as) as.toSubst) x).rename
        (Ren.liftN a.params.length α) =
      hd.obsSubst ((t.rename α).observation D qs ls ps (as.rename α)) (as.rename α).toSubst x := by
  rw [Term.rename_eq_subst_of (θ := Subst.liftN a.params.length (Ren.toSubst α))
      (Subst.liftN_eta_of a.params.length (fun _ => rfl)),
    hd.obsSubst_observation_subst (Ren.toSubst α) D qs ls ps as t x, ← Term.rename_eq_subst,
    ← InstanceArgs.rename_eq_subst]

/-! ## Corecursors at Their State -/

/-- `corec_r T from ȳ return Θ̄ with ḡ`: the corecursor of the instance `T = D.{s̄; l̄; p̄} ā` at the
new variables `ȳ` of a state, whose entries have the parameters `ps`, as its state, the term whose
observations the types of the branches of the type `D` observe. -/
def Term.corecAt {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (Ss : States k Γ) (gs : DestructorBranches k Γ)
    (ps' : List Parameter) : Term k (Γ.extend ps'.length) :=
  .corec r D qs ls ps (as.rename (Ren.weakenN ps'.length)) (Args.bound ps').terms
    (Ss.rename (Ren.weakenN ps'.length)) (gs.rename (Ren.weakenN ps'.length))

/-- The corecursor at the variables of a state, substituted under these variables, is the
corecursor substituted, at the variables of the state. -/
theorem Term.corecAt_subst {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (Ss : States k Δ) (gs : DestructorBranches k Δ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').subst (Subst.liftN ps'.length θ) =
      Term.corecAt r D qs ls ps (as.subst θ) (Ss.subst θ) (gs.subst θ) ps' := by
  have h : ∀ {a} (x : Var Δ a), Subst.liftN ps'.length θ (Ren.weakenN ps'.length x) =
      (θ x).rename (Ren.liftN a.params.length (Ren.weakenN ps'.length)) :=
    fun x => Subst.liftN_weakenN _ θ x
  simp only [Term.corecAt, Term.subst, ← Args.terms_subst, Args.bound_subst]
  rw [InstanceArgs.subst_rename_of h, States.subst_rename_of h,
    DestructorBranches.subst_rename_of h,
    InstanceArgs.rename_subst_of (fun _ => rfl), States.rename_subst_of (fun _ => rfl),
    DestructorBranches.rename_subst_of (fun _ => rfl)]

/-- `(corec_r T from ȳ return Θ̄ with ḡ)[t̄ / ȳ] = corec_r T from t̄ return Θ̄ with ḡ`: the corecursor at
the variables of a state, instantiated by arguments of the state, is the corecursor from them. -/
theorem Term.corecAt_instantiate {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (Ss : States k Γ)
    (gs : DestructorBranches k Γ) {ps' : List Parameter} (ss : Args k Γ ps') :
    (Term.corecAt r D qs ls ps as Ss gs ps').instantiate ss = .corec r D qs ls ps as ss.terms Ss gs := by
  have h : ∀ {a} (y : Var Γ a), ss.toSubst₀ (Ren.weakenN ps'.length y) = Subst₀.id y :=
    fun y => Args.toSubst₀_weakenN ss y
  rw [Term.instantiate_eq_subst₀, Term.corecAt, Term.subst₀,
    InstanceArgs.subst₀_rename_of (σ' := Subst₀.id) h,
    InstanceArgs.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    States.subst₀_rename_of (σ' := Subst₀.id) h, States.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl),
    DestructorBranches.subst₀_rename_of (σ' := Subst₀.id) h,
    DestructorBranches.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl), ← Args.terms_subst₀,
    Args.bound_toSubst₀]

/-- The corecursor at the variables of a state, at instantiated levels, is the corecursor at these
levels, at the variables of the state. -/
theorem Term.corecAt_substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k') (r : Grade)
    (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (Ss : States k Γ) (gs : DestructorBranches k Γ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').substLevels ls' =
      Term.corecAt r D qs (ls.map (Level.subst ls')) ps (as.substLevels ls') (Ss.substLevels ls')
        (gs.substLevels ls') ps' := by
  simp only [Term.corecAt, Term.substLevels, ← Args.terms_substLevels, Args.substLevels_bound,
    InstanceArgs.substLevels_rename, States.substLevels_rename,
        DestructorBranches.substLevels_rename]

/-- The corecursor from the variables of a state, renamed under the variables of the state, is the
corecursor from these variables of its instance, states and branches renamed. -/
theorem Term.corecAt_rename {Γ Δ Ξ : Scope} (α : Ren Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (Ss : States k Δ) (gs : DestructorBranches k Δ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').rename (Ren.liftN ps'.length α) =
      Term.corecAt r D qs ls ps (as.rename α) (Ss.rename α) (gs.rename α) ps' := by
  rw [Term.rename_eq_subst_of (θ := Subst.liftN ps'.length (Ren.toSubst α))
      (Subst.liftN_eta_of ps'.length (fun _ => rfl)),
    Term.corecAt_subst, ← InstanceArgs.rename_eq_subst,
    (States.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Ss.rename α)).symm.trans
      (States.subst_rename_of (fun _ => rfl) Ss),
    (DestructorBranches.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl)
      (gs.rename α)).symm.trans
      (DestructorBranches.subst_rename_of (fun _ => rfl) gs)]
  rfl

/-- The substitution of the destructors before a position by the observations of a corecursor at
the variables of its state, substituted under them, is the substitution by the observations of the
corecursor substituted. -/
theorem Destructors.Pos.obsSubst_corecAt_subst {k' : Nat} {Γ' Γ'' Δ : Scope}
    (σ : Subst k Γ'' Γ') (r : Grade) (D : Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ' Δ) (Ss : States k Γ') (gs : DestructorBranches k Γ')
    (ps'' : List Parameter) {d : Name} {p q ς : Grade} {ps' : List Parameter} {ns : List Name}
    {ds : Destructors k' Δ ns} {Ξ : Scope} {Θ : Telescope k' Ξ ps'}
    {B : Term k' (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
    (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) :
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
