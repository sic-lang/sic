module

public import Sic.Core.Syntax
public import Sic.Grading.Multiplicity

/-!
# Shapes of the Nested Results

The shape of a recursive result that a nested field gives, in a branch of a recursor of the target
language of annex 16 of RFC 36, `l.σ`: the result is the corecursor of a lifting, with a branch for
each destructor that the lifting keeps, and the shape `σ` gives the evaluation what it needs to build
these branches from the recursor, without the terms of the branches: the case of the destructor in its
block, the positions of its arguments in the observation and in the lifted destructor, the ownership
of its result and the ownership that it requires of the value that it observes, at run time, and the
shape of the result, which is the recursor itself or the next lifting, two levels of nesting deep or
more.
A destructor whose multiplicity at run time is `0` is never observed at run time, and its branch is
erased.

The shape reads the multiplicities only, so that the usage and the ownership of the target language
read it, with the factor that it gives the uses of the scope.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

mutual

-- ADE: none.
/-- `σ`: the shape of a lifting, one element for each destructor that it keeps, in order, which gives
the case `i` of the destructor in its block, its multiplicity `ρ` at run time, the positions
`π̄ ◀ ϱ̄` of its `c` arguments in the observation and `π̄' ◀ ϱ̄'` in the lifted destructor, the
ownership `ψ` of its result and the ownership `ς` that it requires of the value that it observes, and
the shape `σ'` of its result. -/
inductive Shape : Type where
  /-- `()`. -/
  | nil : Shape
  /-- `((i, ρ, π̄ ◀ ϱ̄, π̄' ◀ ϱ̄', ψ, ς, σ'), σ)`. -/
  | cons (case c : Nat) (ρ : Multiplicity) (πs ϱs πs' ϱs' : Fin c → Multiplicity)
      (ψ : ResultOwnership Multiplicity c) (ς : Multiplicity) (next : Shape.Next) (rest : Shape) :
      Shape

-- ADE: none.
/-- `σ'`: the shape of the result of a lifted destructor, `⋆`, the recursor itself, when its type
lifted is a motive, or the shape of the next lifting, when it is an instance of a lifting. -/
inductive Shape.Next : Type where
  /-- `⋆`. -/
  | recursor : Shape.Next
  /-- `σ`. -/
  | lifting (σ : Shape) : Shape.Next

end

mutual

-- ADE: none.
/-- `factor(σ)`: the factor of a shape, the multiplicity by which the uses of the scope by the
recursive result that it shapes are multiplied: the meet of the multiplicities at run time of its
destructors times the factors of their results, and `0` without destructor, which is never
observed. -/
def Shape.factor : Shape → Multiplicity
  | .nil => .zero
  | .cons _ _ ρ _ _ _ _ _ _ next rest =>
    match rest with
    | .nil => ρ * next.factor
    | .cons .. => (ρ * next.factor) ⊓ rest.factor

-- ADE: none.
/-- `factor(σ')`: the factor of the shape of a result, `1` for the recursor itself. -/
def Shape.Next.factor : Shape.Next → Multiplicity
  | .recursor => .one
  | .lifting σ => σ.factor

end

mutual

-- ADE: none.
/-- `scope(σ)`: the ownership by which the corecursor of a shape multiplies that of the scope that it
captures, the product of the ownerships that its destructors require of the value that they observe,
and of the shapes of their results, which the recursions run from it see at every depth. -/
def Shape.scope : Shape → Multiplicity
  | .nil => .one
  | .cons _ _ _ _ _ _ _ _ ς next rest => (ς * next.scope) * rest.scope

-- ADE: none.
/-- `scope(σ')`: the scope of the shape of a result, `1` for the recursor itself. -/
def Shape.Next.scope : Shape.Next → Multiplicity
  | .recursor => .one
  | .lifting σ => σ.scope

end

end Sic.Core
