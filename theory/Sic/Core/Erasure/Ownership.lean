module

public import Sic.Core.Erasure.Usage

/-!
# Ownership of the Target Language

The ownership of the target language of annex 19 of RFC 36, `Ω; φ ⊢ M ◀ o`: the value of the term
`M` has the ownership `o` at run time, a multiplicity, given the ownership `φ` of each variable and
the ownership `Ω` of each constant.
It follows the ownership of annex 18 on the run-time components that the target language keeps: the
requirements of the positions, the coefficients of the variables of the fields of the branches of
the recursors, the requirements of the variables of the branches of the corecursors, the ownerships
of the results of the destructors and the requirements of the destructors on the values that they
observe, so that the uniqueness at run time is stated on it.
`↯`, which the evaluation never reads, has every ownership, and a position satisfies its requirement
in every case: the erasure stores no position whose requirement the source does not check and whose
ownership a result reads.
A recursor whose branches have nested results also gives them the ownership `ς` that the destructors
of the liftings require of the value that they observe, and the ownership `χ` of their results that
are motives: the corecursor of a nested result captures the scope, which its observations see at
`ς · φ`, and runs the recursor on the observations of the field, whose results have the ownership
`χ`, so that each branch is checked a second time with the scope at `ς · φ` and the ownership `χ`.
ADE have no such judgment.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- `own_{o'}(w)`: the ownership of the variable of a recursive result of the multiplicity `1` in a
branch of a recursor of the ownership `o'`: `1` for a nested result, the corecursor of a lifting, a
new value, and `o'` for the others, results of the recursor.
RFC: `\mathsf{own}_w` -/
def RecursiveResult.ownership (o' : Multiplicity) : RecursiveResult → Multiplicity
  | .nested .. => .one
  | .erased | .field _ => o'

mutual

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
  /-- A recursor of the multiplicity `ρ` has the ownership `o'` of its branches, each checked with
  the ownership `o` of its term times the requirement `ϱ` of the recursion of its block, which every
  level of the recursion has, times the coefficient of each variable of a field, and `o'` times the
  multiplicity of each variable of a recursive result.
  RFC: `\mathsf{own}_M.\mathsf{rec}` -/
  | recursor {n : Nat} {φ : MultiplicityVector n} {ρ ϱ o o' ς χ : Multiplicity} {M : Target n}
      {Ns : TargetBranches n} (hM : Target.Ownership Ω φ o M)
      (hNs : TargetBranches.Ownership Ω φ ρ (o * ϱ) o' ς χ Ns) :
      Target.Ownership Ω φ o' (.recursor ρ ϱ M Ns)
  /-- An observation has the ownership `o` of its term times the value `v` of the ownership `ψ` of
  the result of its destructor, given the ownerships `os` of its arguments, which satisfy the
  requirements of their positions, and `o` satisfies the requirement `ς` of the destructor on the
  value that it observes.
  RFC: `\mathsf{own}_M.d` -/
  | obs {n : Nat} {φ : MultiplicityVector n} {M : Target n} {i c : Nat}
      {ψ : ResultOwnership Multiplicity c} {ς : Multiplicity} {Ms : Targets n} {o v : Multiplicity}
      {os : List Multiplicity} (hM : Target.Ownership Ω φ o M) (hMs : Targets.Ownership Ω φ os Ms)
      (hv : ψ.value os = some v) (hς : ς ≤ o) : Target.Ownership Ω φ (o * v) (.obs M i ψ ς Ms)
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

/-- `Ω; φ ⊢ N̄ ◀ ρ; o; o'; ς; χ`: each branch of a recursor of the multiplicity `ρ` whose term has the
ownership `o` has the ownership `o'`, given the ownership `o · κ` of the variable of each field, of
the coefficient `κ`, and the ownership of each recursive result times its multiplicity `π'`, `o' · π'`
for a result of the recursor and `1 · π'` for a nested result, a new value; each branch has also the
ownership `χ` with the scope at `ς · φ` and the results of the recursor at `χ · π'`, as the
recursions run from a nested result see them, and the shape of each nested result has the
ownerships `ς` and `χ`, and, when `ρ` times its factor is not `0`, meets the requirements of the
recursions, and the variable of its field, seen at `ς`, keeps `o`: otherwise the corecursor of the
result observes the field on no path that the evaluation follows. -/
inductive TargetBranches.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → Multiplicity → Multiplicity → Multiplicity → Multiplicity →
      Multiplicity → TargetBranches n → Prop where
  /-- No branch.
  RFC: `\mathsf{own}_{\bar N}.\varepsilon` -/
  | nil {n : Nat} {φ : MultiplicityVector n} {ρ o o' ς χ : Multiplicity} :
      TargetBranches.Ownership Ω φ ρ o o' ς χ .nil
  /-- The first branch and the others.
  RFC: `\mathsf{own}_{\bar N}.{,}` -/
  | cons {n a b : Nat} {φ : MultiplicityVector n} {ρ o o' ς χ : Multiplicity}
      {πs κs : Fin a → Multiplicity} {πs' : Fin b → Multiplicity} {ks : Fin b → RecursiveResult}
      {N : Target (n + (a + b))} {Ns : TargetBranches n}
      (hN : Target.Ownership Ω
        (φ.extendBinders (fun l => o * κs l) (fun j => (ks j).ownership o' * πs' j)) o' N)
      (hN' : Target.Ownership Ω
        (MultiplicityVector.extendBinders (ς ·ᶜ φ) (fun l => o * κs l)
          (fun j => (ks j).ownership χ * πs' j)) χ N)
      (hks : ∀ (j : Fin b) (l : Fin a) (σ : Shape), ks j = .nested l σ →
        σ.Uniform ς χ ∧ (ρ * σ.factor ≠ .zero → σ.Requires o ς ∧ o ≤ ς * (o * κs l)))
      (hNs : TargetBranches.Ownership Ω φ ρ o o' ς χ Ns) :
      TargetBranches.Ownership Ω φ ρ o o' ς χ (.cons a b πs κs πs' ks N Ns)

/-- `Ω; φ ⊢ P̄ ◀`: each branch of a corecursor has, for all the ownerships `ō` of its arguments that
satisfy their requirements, the value of the ownership `ψ` of the result of its destructor at `ō`,
or the ownership `1` of a new value when it resumes the corecursor, given the ownership `ς · φ(x)`
of each variable `x` of the scope, `ς` times its own, the ownership `ς · ϱ · π` of the variable of
each entry of the state, of the requirement `ς` of the destructor on the value that it observes, of
the requirement `ϱ` and of the multiplicity `π`, and `o · π'` of the variable of each argument, of the
ownership `o` and the multiplicity `π'`; the ownership `ψ` of the result of a destructor whose branch
resumes the corecursor is a constant, which the term already built of its position requires. -/
inductive TargetCorecBranches.Ownership (Ω : Name → Multiplicity) :
    {n : Nat} → MultiplicityVector n → TargetCorecBranches n → Prop where
  /-- No branch.
  RFC: `\mathsf{own}_{\bar P}.\varepsilon` -/
  | nil {n : Nat} {φ : MultiplicityVector n} : TargetCorecBranches.Ownership Ω φ .nil
  /-- The first branch and the others.
  RFC: `\mathsf{own}_{\bar P}.{,}` -/
  | cons {n b c : Nat} {φ : MultiplicityVector n} {k : Resumption}
      {πs ϱs : Fin b → Multiplicity} {πs' ϱs' : Fin c → Multiplicity}
      {ψ : ResultOwnership Multiplicity c} {ς : Multiplicity} {P : Target (n + (b + c))}
      {Ps : TargetCorecBranches n}
      (hP : ∀ (os : Fin c → Multiplicity) (v : Multiplicity), (∀ l, ϱs' l ≤ os l) →
        (k = .none ∧ ψ.value (List.ofFn os) = some v ∨ k ≠ .none ∧ v = .one) →
        Target.Ownership Ω
          (MultiplicityVector.extendBinders (ς ·ᶜ φ) (fun l => ς * ϱs l * πs l) (fun l => os l * πs' l)) v P)
      (hψ : k ≠ .none → ∃ χ, ψ = ⟨some χ, fun _ => none⟩)
      (hPs : TargetCorecBranches.Ownership Ω φ Ps) :
      TargetCorecBranches.Ownership Ω φ (.cons k b c πs ϱs πs' ϱs' ψ ς P Ps)

end

/-! ## Properties -/

/-- The value of an ownership that is a constant is the constant, whatever the ownerships of the
arguments. -/
theorem ResultOwnership.value_const (χ : Multiplicity) : {n : Nat} → (os : List Multiplicity) →
    (⟨some χ, fun _ => none⟩ : ResultOwnership Multiplicity n).value os = some χ
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: os => by
    show Option.merge _ none
      ((⟨some χ, fun _ => none⟩ : ResultOwnership Multiplicity n).value os) = _
    rw [ResultOwnership.value_const χ (n := n) os]
    rfl

mutual

/-- The term that a skeleton stands for has the ownership `1` of a new value. -/
theorem Skeleton.ownership {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} :
    (k : Skeleton) → Target.Ownership Ω φ .one k.target
  | .empty => .erased _
  | .ctor _ ks => .ctor (Skeleton.ownership_targets ks)

/-- The terms that skeletons stand for have the ownership `1` of a new value, which satisfies the
requirement `ω` at which they are stored. -/
theorem Skeleton.ownership_targets {Ω : Name → Multiplicity} {n : Nat}
    {φ : MultiplicityVector n} :
    (ks : List Skeleton) →
      Targets.Ownership Ω φ (ks.map fun _ => .one) (Skeleton.targets ks)
  | [] => .nil
  | k :: ks => .cons k.ownership (show Multiplicity.omega ≤ .one by decide)
      (Skeleton.ownership_targets ks)

end

end Sic.Core
