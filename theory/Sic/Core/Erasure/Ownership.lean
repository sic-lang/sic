module

public import Sic.Core.Erasure.Usage

/-!
# Ownership of the Target Language

The ownership of the target language of annex 16 of RFC 36, `Ω; φ ⊢ M ◀ o`: the value of the term
`M` has the ownership `o` at run time, a multiplicity, given the ownership `φ` of each variable and
the ownership `Ω` of each constant.
It follows the ownership of annex 13 on the run-time components that the target language keeps: the
requirements of the positions, the coefficients of the variables of the fields of the branches of
the recursors, the requirements of the variables of the branches of the corecursors, the ownerships
of the results of the destructors and the requirements of the destructors on the values that they
observe, so that the uniqueness at run time is stated on it.
`↯`, which the evaluation never reads, has every ownership, and a position satisfies its requirement
in every case: the erasure stores no position whose requirement the source does not check and whose
ownership a result reads.
ADE have no such judgment.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

mutual

-- ADE: none.
/-- `Ω; φ ⊢ M ◀ o`: the value of the term `M` of the target language has the ownership `o`, given
the ownership `φ` of each variable and the ownership `Ω` of each constant. -/
inductive Target.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → Multiplicity → Target n → Prop where
  /-- A variable has the ownership that `φ` gives it.
  RFC: `\mathsf{own}_M.x` -/
  | var {n : Nat} {φ : MultiplicityVector n} (x : Fin n) : Target.Ownership Ω φ (φ x) (.var x)
  /-- A constant has the ownership that `Ω` gives it.
  RFC: `\mathsf{own}_M.f` -/
  | const {n : Nat} {φ : MultiplicityVector n} (f : Name) (qs : List Quality) (ps : List Grade) :
      Target.Ownership Ω φ (Ω f) (.const f qs ps)
  /-- `↯`, which the evaluation never reads, has every ownership.
  RFC: `\mathsf{own}_M.\text{↯}` -/
  | erased {n : Nat} {φ : MultiplicityVector n} (o : Multiplicity) :
      Target.Ownership Ω φ o .erased
  /-- A constructor builds a new value, of the ownership `1`, whose fields satisfy the requirements
  of their positions.
  RFC: `\mathsf{own}_M.c` -/
  | ctor {n : Nat} {φ : MultiplicityVector n} {i : Nat} {Ms : Targets n} {os : List Multiplicity}
      (hMs : Targets.Ownership Ω φ os Ms) : Target.Ownership Ω φ .one (.ctor i Ms)
  /-- A recursor has the ownership `o'` of its branches, each checked with the ownership `o` of its
  term times the coefficient of each variable of a field, and `o'` times the multiplicity of each
  variable of a recursive result.
  RFC: `\mathsf{own}_M.\mathsf{rec}` -/
  | recursor {n : Nat} {φ : MultiplicityVector n} {ρ o o' : Multiplicity} {M : Target n}
      {Ns : TargetBranches n} (hM : Target.Ownership Ω φ o M)
      (hNs : TargetBranches.Ownership Ω φ o o' Ns) : Target.Ownership Ω φ o' (.recursor ρ M Ns)
  /-- An observation has the ownership `o` of its term times the value `v` of the ownership `ψ` of
  the result of its destructor, given the ownerships `os` of its arguments, which satisfy the
  requirements of their positions, and `o` satisfies the requirement `χ` of the destructor on the
  value that it observes.
  RFC: `\mathsf{own}_M.d` -/
  | obs {n : Nat} {φ : MultiplicityVector n} {M : Target n} {i c : Nat}
      {ψ : ResultOwnership Multiplicity c} {χ : Multiplicity} {Ms : Targets n} {o v : Multiplicity}
      {os : List Multiplicity} (hM : Target.Ownership Ω φ o M) (hMs : Targets.Ownership Ω φ os Ms)
      (hv : ψ.value os = some v) (hχ : χ ≤ o) : Target.Ownership Ω φ (o * v) (.obs M i ψ χ Ms)
  /-- A corecursor builds a new value, of the ownership `1`, whose state satisfies the requirements of
  its positions, and whose branches have the ownerships of the results of their destructors.
  RFC: `\mathsf{own}_M.\mathsf{corec}` -/
  | corec {n : Nat} {φ : MultiplicityVector n} {Ms : Targets n} {Ps : TargetCorecBranches n}
      {os : List Multiplicity} (hMs : Targets.Ownership Ω φ os Ms)
      (hPs : TargetCorecBranches.Ownership Ω φ Ps) : Target.Ownership Ω φ .one (.corec Ms Ps)
  /-- A term may be given an ownership lower than its own, which states less.
  RFC: `\mathsf{own}_M.\mathsf{sub}` -/
  | sub {n : Nat} {φ : MultiplicityVector n} {p q : Multiplicity} {M : Target n}
      (h : Target.Ownership Ω φ p M) (hle : q ≤ p) : Target.Ownership Ω φ q M

-- ADE: none.
/-- `Ω; φ ⊢ M̄ ◀ ō`: the terms `M̄` have the ownerships `ō`, each satisfying the requirement of its
position. -/
inductive Targets.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → List Multiplicity → Targets n → Prop where
  /-- No term has no ownership.
  RFC: `\mathsf{own}_{\bar M}.\varepsilon` -/
  | nil {n : Nat} {φ : MultiplicityVector n} : Targets.Ownership Ω φ [] .nil
  /-- The first term, whose ownership `o` satisfies the requirement `ϱ` of its position, and the
  others.
  RFC: `\mathsf{own}_{\bar M}.{,}` -/
  | cons {n : Nat} {φ : MultiplicityVector n} {π ϱ o : Multiplicity} {M : Target n}
      {Ms : Targets n} {os : List Multiplicity} (hM : Target.Ownership Ω φ o M) (hϱ : ϱ ≤ o)
      (hMs : Targets.Ownership Ω φ os Ms) : Targets.Ownership Ω φ (o :: os) (.cons π ϱ M Ms)

-- ADE: none.
/-- `Ω; φ ⊢ N̄ ◀ o; o'`: each branch of a recursor whose term has the ownership `o` has the
ownership `o'`, given the ownership `o · κ` of the variable of each field, of the coefficient `κ`,
and `o' · π'` of the variable of each recursive result, of the multiplicity `π'`. -/
inductive TargetBranches.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → Multiplicity → Multiplicity → TargetBranches n → Prop where
  /-- No branch.
  RFC: `\mathsf{own}_{\bar N}.\varepsilon` -/
  | nil {n : Nat} {φ : MultiplicityVector n} {o o' : Multiplicity} :
      TargetBranches.Ownership Ω φ o o' .nil
  /-- The first branch and the others.
  RFC: `\mathsf{own}_{\bar N}.{,}` -/
  | cons {n a b : Nat} {φ : MultiplicityVector n} {o o' : Multiplicity}
      {πs κs : Fin a → Multiplicity} {πs' : Fin b → Multiplicity} {ks : Fin b → Option Nat}
      {N : Target (n + (a + b))} {Ns : TargetBranches n}
      (hN : Target.Ownership Ω (φ.extendBinders (fun l => o * κs l) (fun j => o' * πs' j)) o' N)
      (hNs : TargetBranches.Ownership Ω φ o o' Ns) :
      TargetBranches.Ownership Ω φ o o' (.cons a b πs κs πs' ks N Ns)

-- ADE: none.
/-- `Ω; φ ⊢ P̄ ◀`: each branch of a corecursor has, for all the ownerships `ō` of its arguments that
satisfy their requirements, the value of the ownership `ψ` of the result of its destructor at `ō`,
or the ownership `1` of a new value when it resumes the corecursor, given the ownership `χ · ϱ · π`
of the variable of each entry of the state, of the requirement `χ` of the destructor on the value
that it observes, of the requirement `ϱ` and of the multiplicity `π`, and
`o · π'` of the variable of each argument, of the ownership `o` and the multiplicity `π'`. -/
inductive TargetCorecBranches.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → TargetCorecBranches n → Prop where
  /-- No branch.
  RFC: `\mathsf{own}_{\bar P}.\varepsilon` -/
  | nil {n : Nat} {φ : MultiplicityVector n} : TargetCorecBranches.Ownership Ω φ .nil
  /-- The first branch and the others.
  RFC: `\mathsf{own}_{\bar P}.{,}` -/
  | cons {n b c : Nat} {φ : MultiplicityVector n} {k : Resumption}
      {πs ϱs : Fin b → Multiplicity} {πs' ϱs' : Fin c → Multiplicity}
      {ψ : ResultOwnership Multiplicity c} {χ : Multiplicity} {P : Target (n + (b + c))}
      {Ps : TargetCorecBranches n}
      (hP : ∀ (os : Fin c → Multiplicity) (v : Multiplicity), (∀ l, ϱs' l ≤ os l) →
        (k = .none ∧ ψ.value (List.ofFn os) = some v ∨ k ≠ .none ∧ v = .one) →
        Target.Ownership Ω
          (φ.extendBinders (fun l => χ * ϱs l * πs l) (fun l => os l * πs' l)) v P)
      (hPs : TargetCorecBranches.Ownership Ω φ Ps) :
      TargetCorecBranches.Ownership Ω φ (.cons k b c πs ϱs πs' ϱs' ψ χ P Ps)

end

/-! ## Properties -/

-- ADE: none.
/-- The terms of a list, each of the ownership `1`, satisfy the requirement `ω` at which the list
stores them. -/
theorem Targets.ownership_ofList {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} :
    (Ms : List (Multiplicity × Target n)) → (∀ πM ∈ Ms, Target.Ownership Ω φ .one πM.2) →
      Targets.Ownership Ω φ (Ms.map fun _ => .one) (Targets.ofList Ms)
  | [], _ => .nil
  | πM :: Ms, h => .cons (h πM List.mem_cons_self) (show Multiplicity.omega ≤ .one by decide)
      (Targets.ownership_ofList Ms fun πM' hM' => h πM' (List.mem_cons_of_mem _ hM'))

-- ADE: none.
/-- The skeleton of a data type of a block has the ownership `1` of a new value. -/
theorem TypeDeclaration.skeleton_ownership {Ω : Name → Multiplicity} (decl : TypeDeclaration)
    (I : Instance decl.sorts decl.grades) {n : Nat} {φ : MultiplicityVector n} :
    (d : Nat) → (D : Name) → Target.Ownership Ω φ .one (decl.skeleton I d D)
  | 0, _ => .erased _
  | d + 1, D => by
    simp only [TypeDeclaration.skeleton]
    split
    · split
      · split
        · refine .ctor (Targets.ownership_ofList _ fun M hM => ?_)
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hM
          cases r with
          | some D' => exact decl.skeleton_ownership I d D'
          | none => exact .erased _
        · exact .erased _
      · exact .erased _
    · exact .erased _

-- ADE: none.
/-- The skeleton of a data type in a signature has the ownership `1` of a new value. -/
theorem Signature.skeleton_ownership {Ω : Name → Multiplicity} {n : Nat}
    {φ : MultiplicityVector n} (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade) :
    Target.Ownership Ω φ .one (sig.skeleton D qs ps) := by
  unfold Signature.skeleton
  induction sig with
  | nil => exact .erased _
  | cons e sig ih =>
    simp only [List.findSome?_cons]
    split
    · rename_i M hM
      simp only [Option.getD_some]
      cases e with
      | typeDeclaration decl =>
        simp only [Entry.skeleton] at hM
        split at hM
        · split at hM
          · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hM
            exact decl.skeleton_ownership _ _ _
          · exact nomatch hM
        · exact nomatch hM
      | _ => simp only [Entry.skeleton] at hM; exact nomatch hM
    · exact ih

end Sic.Core
