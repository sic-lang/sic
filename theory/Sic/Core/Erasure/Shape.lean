module

public import Sic.Core.Erasure.Skeleton
public import Sic.Core.Syntax

/-!
# Shapes of the Nested Results

The shape of a recursive result that a nested field gives, in a branch of a recursor of the target
language of annex 16 of RFC 36, `n.Ξ`: the result is the corecursor of a lifting, with a branch for
each destructor that the lifting keeps, and the shape `σ` gives the evaluation what it needs to build
these branches from the recursor, without the terms of the branches: the case of the destructor in its
block, the positions of its arguments in the observation and in the lifted destructor, the ownership
of its result and the ownership that it requires of the value that it observes, at run time, and the
shape of the result, which is the recursor itself or the next lifting, two levels of nesting deep or
more.
A destructor whose multiplicity at run time is `0` is never observed at run time, and its branch is
erased.

The shape reads the multiplicities and the skeletons only, so that the usage and the ownership of
the target language read it, with the factor that it gives the uses of the scope.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

mutual

-- ADE: none.
/-- `Ξ`: the shape of a lifting, one element for each destructor that it keeps, in order, which gives
the case `i` of the destructor in its block, its multiplicity `ρ` at run time, the positions
`π̄ ◀ ϱ̄` of its `c` arguments in the observation and `π̄' ◀ ϱ̄'` in the lifted destructor, the
ownership `ψ` of the result of the lifted destructor and the ownership `ς` that it requires of the
value that it observes, the same two ownerships `ψ₀` and `ς₀` of the destructor that it lifts, which
the observation of the field reads, and the shape `Υ` of its result.
RFC: `\mathsf{syntax}_\Xi` -/
inductive Shape : Type where
  /-- `()`. -/
  | nil : Shape
  /-- `((i, ρ, π̄ ◀ ϱ̄, π̄' ◀ ϱ̄', ψ, ς, ψ₀, ς₀, Υ), Ξ)`. -/
  | cons (case c : Nat) (ρ : Multiplicity) (πs ϱs πs' ϱs' : Fin c → Multiplicity)
      (ψ : ResultOwnership Multiplicity c) (ς : Multiplicity) (ψ₀ : ResultOwnership Multiplicity c)
      (ς₀ : Multiplicity) (next : Shape.Next) (rest : Shape) : Shape

-- ADE: none.
/-- `Υ`: the shape of the result of a lifted destructor, `⋆_M`, the recursor itself, when its type
lifted is a motive, with the skeleton `M` of this motive, which the recursor of the multiplicity `0`
runs on instead of the observation, or the shape of the next lifting, when it is an instance of a
lifting; a shape is a shape of a result in the RFC, and a case of its own here, since Lean has no
subtypes of inductive types.
RFC: `\mathsf{syntax}_\Upsilon` -/
inductive Shape.Next : Type where
  /-- `⋆_M`. -/
  | recursor (K : Skeleton) : Shape.Next
  /-- `Ξ`. -/
  | lifting (σ : Shape) : Shape.Next

end

/-- The shape `Ξ` from its destructor at the index `k` on, empty past its last destructor: the
element at the index `k` of the list that the RFC writes. -/
def Shape.drop : Nat → Shape → Shape
  | 0, σ => σ
  | _ + 1, .nil => .nil
  | k + 1, .cons _ _ _ _ _ _ _ _ _ _ _ _ rest => rest.drop k

mutual

-- ADE: none.
/-- `factor(Ξ)`: the factor of a shape, the multiplicity by which the uses of the scope by the
recursive result that it shapes are multiplied: the meet of the multiplicities at run time of its
destructors times the factors of their results, and `0` without destructor, which is never
observed.
RFC: `\mathsf{factor}_\Xi` -/
def Shape.factor : Shape → Multiplicity
  | .nil => .zero
  | .cons _ _ ρ _ _ _ _ _ _ _ _ next rest =>
    match rest with
    | .nil => ρ * next.factor
    | .cons .. => (ρ * next.factor) ⊓ rest.factor

-- ADE: none.
/-- `factor(Υ)`: the factor of the shape of a result, `1` for the recursor itself, and the factor of
the shape of the next lifting, which the RFC does not need to state.
RFC: `\mathsf{factor}_\Upsilon` -/
def Shape.Next.factor : Shape.Next → Multiplicity
  | .recursor _ => .one
  | .lifting σ => σ.factor

end

mutual

-- ADE: none.
/-- `Ξ fits ρ`: the shape fits the recursor of the multiplicity `ρ`: the multiplicity at run time of
each argument of each lifted destructor is within `ρ` times the multiplicity at run time of the
destructor times the factor of its result times the multiplicity of the argument in the observation,
at every depth, as the lifting scales the arguments of the destructors that it lifts, since the
observation by the lifted destructor reads its arguments as many times as the recursor reads the
observation that it builds, and a destructor never observed reads none.
RFC: `\mathsf{fits}_\Xi` -/
def Shape.Fits (ρ : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ _ ρᵢ πs _ πs' _ _ _ _ _ next rest =>
    (∀ k, πs' k ≤ ρ * (ρᵢ * next.factor) * πs k) ∧ next.Fits ρ ∧ rest.Fits ρ

-- ADE: none.
/-- The shape of a result fits the recursor of the multiplicity `ρ`: the recursor itself does, and
the next lifting when its shape does, which the RFC does not need to state.
RFC: `\mathsf{fits}_\Upsilon` -/
def Shape.Next.Fits (ρ : Multiplicity) : Shape.Next → Prop
  | .recursor _ => True
  | .lifting σ => σ.Fits ρ

end

end Sic.Core
