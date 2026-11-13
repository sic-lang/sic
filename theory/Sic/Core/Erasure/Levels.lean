module

public import Sic.Core.Erasure
public import Sic.Core.Substitution
import Sic.Core.Substitution.Levels

/-!
# Levels of the Erasure

The erasure of annex 16 of RFC 36 reads no level: it erases the sorts and the instances, keeps the
qualities and the grades of a constant without its levels, and reads of the states of a corecursor
only the parameters and the arity of each state, which the instantiation of the level variables
keeps, so that a term and its instance at other levels have the same erasure.

ADE have no level variables.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- The instantiation of the level variables keeps the arity of each state. -/
theorem States.arity_substLevels {k k' : Nat} {Γ : Scope} (ls' : Fin k → Level k')
    (Ss : States k Γ) (j : Nat) : (Ss.substLevels ls').arity j = Ss.arity j := by
  simp only [States.arity, States.get_substLevels_eq]
  cases Ss.get j with
  | none => rfl
  | some x => obtain ⟨n, ps, S⟩ := x; cases n <;> rfl

-- ADE: none.
/-- The instantiation of the level variables keeps the grades of the entries of the state of a
corecursor, which its parameters give. -/
theorem States.get_substLevels_elim {k k' : Nat} {Γ : Scope} {α : Type} (ls' : Fin k → Level k')
    (Ss : States k Γ) (o : Option Nat) (a : α) (f : List Parameter → α) :
    ((o.bind (Ss.substLevels ls').get).elim a fun x => f x.2.1)
      = ((o.bind Ss.get).elim a fun x => f x.2.1) := by
  cases o with
  | none => rfl
  | some j =>
    simp only [Option.bind_some, States.get_substLevels_eq]
    cases Ss.get j <;> rfl

mutual

-- ADE: none.
/-- A term instantiated at other levels has the same erasure. -/
theorem Term.erase_substLevels (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (t : Term k Γ) → (t.substLevels ls').erase sig S hΓ = t.erase sig S hΓ
  | .var (e := .var) .. => rfl
  | .var (e := .secondOrder ..) x _ => nomatch hΓ _ x.mem
  | .sort _ | .const .. | .inst .. => rfl
  | .ctor _ _ _ _ _ _ ts => by
    simp only [Term.substLevels, Term.erase, Terms.erase_substLevels sig S ls' hΓ ts]
  | .recursor _ _ _ _ _ _ t _ us => by
    simp only [Term.substLevels, Term.erase, Term.erase_substLevels sig S ls' hΓ t,
      Branches.erase_substLevels sig S ls' hΓ _ us]
  | .obs _ _ _ _ _ t _ bs => by
    simp only [Term.substLevels, Term.erase, Term.erase_substLevels sig S ls' hΓ t,
      Terms.erase_substLevels sig S ls' hΓ bs]
  | .corec r _ _ _ _ _ ss Ss vs => by
    simp only [Term.substLevels, Term.erase, Terms.erase_substLevels sig S ls' hΓ ss,
      CorecBranches.erase_substLevels sig S ls' hΓ vs,
      show (Ss.substLevels ls').arity = Ss.arity from funext (States.arity_substLevels ls' Ss)]
    rw [States.get_substLevels_elim ls' Ss _ [] fun ps => ps.map _]
    simp only [States.get_substLevels_eq]
    have h : ∀ j, ((Ss.get j).map fun x => (⟨x.1, x.2.1, x.2.2.substLevels ls'⟩ :
        Σ n ps, Telescope k' (Γ.extend n) ps)).elim []
          (fun x => x.2.1.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))
        = (Ss.get j).elim [] fun x => x.2.1.map fun p => ⟨r * p.usage, p.requirement⟩ :=
      fun j => by cases Ss.get j <;> rfl
    simp only [h]

-- ADE: none.
/-- Fields instantiated at other levels have the same erasure. -/
theorem Terms.erase_substLevels (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (ts : Terms k Γ) → (ps : List Parameter) →
      (ts.substLevels ls').erase sig S hΓ ps = ts.erase sig S hΓ ps
  | .nil, _ => rfl
  | .cons _ ts, [] => by
    simp only [Terms.substLevels, Terms.erase, Terms.erase_substLevels sig S ls' hΓ ts]
  | .cons t ts, _ :: ps => by
    simp only [Terms.substLevels, Terms.erase, Term.erase_substLevels sig S ls' hΓ t,
      Terms.erase_substLevels sig S ls' hΓ ts ps]

-- ADE: none.
/-- Branches of a recursor instantiated at other levels have the same erasure. -/
theorem Branches.erase_substLevels (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade) :
    (us : Branches k Γ) → (es : List (List Nat)) → (fs : List (List Parameter)) →
      (us.substLevels ls').erase sig S hΓ r es fs = us.erase sig S hΓ r es fs
  | .nil, _, _ => rfl
  | .cons a b _ u us, es, fs => by
    simp only [Branches.substLevels, Branches.erase,
      Term.erase_substLevels sig S ls' ((hΓ.extend a).extend b) u,
      Branches.erase_substLevels sig S ls' hΓ r us es.tail fs.tail]

-- ADE: none.
/-- Branches of a corecursor instantiated at other levels have the same erasure. -/
theorem CorecBranches.erase_substLevels (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (vs : CorecBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
      (pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length)) →
      (vs.substLevels ls').erase sig S hΓ ps ks pss = vs.erase sig S hΓ ps ks pss
  | .nil, _, _, _ => rfl
  | .cons 0 b c v vs, _ :: ps, ks, pss => by
    simp only [CorecBranches.substLevels, CorecBranches.erase,
      CorecBranches.erase_substLevels sig S ls' hΓ vs ps ks.tail pss.tail]
    erw [Term.erase_substLevels sig S ls' ((hΓ.extend b).extend c) v]
  | .cons 0 _ _ _ vs, [], ks, pss => by
    simp only [CorecBranches.substLevels, CorecBranches.erase,
      CorecBranches.erase_substLevels sig S ls' hΓ vs _ ks.tail pss.tail]
  | .cons (_ + 1) _ _ _ vs, ps, ks, pss => by
    simp only [CorecBranches.substLevels, CorecBranches.erase,
      CorecBranches.erase_substLevels sig S ls' hΓ vs _ ks.tail pss.tail]

end

end Sic.Core
