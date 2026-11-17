module

public import Sic.Core.Erasure.Renaming

/-!
# Corecursors of the Nested Results

The corecursor that a nested result of a branch of a recursor of the target language of annex 16 of
RFC 36 gives at run time, `n.Ξ`: the evaluation builds its branches from the branches of the
recursor and from the shape `σ`, as the rule `(res_D)` of annex 21 builds the corecursor of the
lifting from the observations of the field, one branch for each destructor that the lifting keeps,
which observes the field by the destructor that it lifts and gives the result of this observation:
the recursor on it, or the corecursor of the next lifting.
The corecursor of `(res_D)` has no state and mentions the field, a variable of the scope of the
branch of the recursor; the corecursor built here has no state either, and its scope is the scope of
the recursor with the field, its variable `0`, so that the evaluation binds the field before it
captures this scope.
Each built branch observes a path from the field, the field itself or an observation of it at the
level before, and the branches of the recursor are shifted under the arguments of each built branch.
When the recursor is of the multiplicity `0`, its term is erased and the field of its skeleton is
`↯`: the recursor then runs on the skeleton of the motive instead of the observation, which is never
evaluated.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `(x̄ ▶ π̄ ◀ ϱ̄)`: the variables `xs` as terms, the first one first, each at the multiplicity and the
requirement of its position, and `↯` at a position of the multiplicity `0`, whose value is never
read, which holds a skeleton. -/
def Targets.ofVars {n : Nat} : {c : Nat} → (Fin c → Multiplicity) → (Fin c → Multiplicity) →
    (Fin c → Fin n) → Targets n
  | 0, _, _, _ => .nil
  | _ + 1, πs, ϱs, xs =>
    .cons (πs 0) (ϱs 0) (if πs 0 = .zero then .erased else .var (xs 0))
      (Targets.ofVars (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ))

-- ADE: none.
/-- The variable of the argument `k` of a built branch, over the `m` variables of its scope, no entry
of a state and the `c` arguments, the last one first. -/
def Shape.argVar (m c : Nat) (k : Fin c) : Fin (m + (0 + c)) :=
  ⟨c - 1 - k, by omega⟩

mutual

-- ADE: none.
/-- `branches_{ρ,ϱ}(Ξ, O, N̄)`: the branches built from the shape `Ξ` for the recursor
`rec_ρ · ◀ ϱ with N̄` on the observations of the term `O`, the path from the field: the branch of each
destructor, without state, binds its arguments and observes `O` by the destructor that it lifts, at
these arguments, then gives the result of this observation, or `↯` when the destructor is never
observed at run time; the term and the branches are shifted under the arguments, which the RFC
names by fresh variables instead.
RFC: `\mathsf{branches}_\Xi` -/
def Shape.branches {m : Nat} (ρ ϱ : Multiplicity) : Shape → Target m → TargetBranches m →
    TargetCorecBranches m
  | .nil, _, _ => .nil
  | .cons i c ρᵢ πs ϱs πs' ϱs' ψ ς ψ₀ ς₀ next rest, M, Ns =>
    .cons .none 0 c Fin.elim0 Fin.elim0 πs' ϱs' ψ ς
      (if ρᵢ = .zero then .erased else
        next.body ρ ϱ
          (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
            (Targets.ofVars πs ϱs (Shape.argVar m c)))
          (Ns.rename (TargetRen.shift m (0 + c))))
      (rest.branches ρ ϱ M Ns)

-- ADE: none.
/-- `body_{ρ,ϱ}(Υ, O, N̄)`: the result of the observation `O` of a field: the recursor
`rec_ρ O ◀ ϱ with N̄` for `⋆_M`, or `rec_0 M ◀ ϱ with N̄` on the skeleton `M` of the motive when `ρ` is `0`, as the erasure of a recursor
on an erased term, and the corecursor without state of the next lifting, whose branches observe `O`
in turn, for its shape.
RFC: `\mathsf{body}_\Upsilon` -/
def Shape.Next.body {m : Nat} (ρ ϱ : Multiplicity) : Shape.Next → Target m → TargetBranches m →
    Target m
  | .recursor K, O, Ns => .recursor ρ ϱ (if ρ = .zero then K.target else O) Ns
  | .lifting σ, O, Ns => .corec .nil (σ.branches ρ ϱ O Ns)

end

-- ADE: none.
/-- `nested_{ρ,ϱ}(x, Ξ, N̄)`, `n.Ξ` at run time: the corecursor without state of the shape `σ` for the recursor
`rec_ρ · ◀ ϱ with N̄`, over the variables of the scope of the recursor and the field, the variable
`0`, whose branches observe the field, as `(res_D)` builds the result of a nested field.
RFC: `\mathsf{nested}_\Xi` -/
def Target.nested {n : Nat} (ρ ϱ : Multiplicity) (σ : Shape) (Ns : TargetBranches n) :
    Target (n + 1) :=
  .corec .nil (σ.branches ρ ϱ (.var 0) (Ns.rename (TargetRen.shift n 1)))

end Sic.Core
