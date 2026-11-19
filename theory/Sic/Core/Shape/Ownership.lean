module

public import Sic.Core.Shape

/-!
# Ownerships of the Shapes

The ownerships that the shape of a nested result of annex 16 of RFC 36 carries, at run time: the
ownership of the result of a lifted destructor and the scale at which the observation that it builds
sees the arguments of its branch, read from the shape of its result, the ownerships `ς` and `χ`
that a shape has when its lifted destructors require `ς` of the value that they observe and give
their results that are motives the ownership `χ`, and the requirements of the recursions on the
observations of a field that a shape meets.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `own_χ(Υ)`: the ownership of the result of a lifted destructor whose result has the shape `Υ`,
`χ` for the recursor itself, and `1` for the corecursor of the next lifting, a new value.
RFC: `\mathsf{own}_\Upsilon` -/
def Shape.Next.ownership (χ : Multiplicity) : Shape.Next → Multiplicity
  | .recursor _ => χ
  | .lifting _ => .one

-- ADE: none.
/-- `scale_ς(Υ)`: the ownership by which the observation built for a destructor whose result has the
shape `Υ` sees the arguments of its branch: `1` when the recursor runs on it in the branch, and `ς`
when the corecursor of the next lifting captures it, whose observations see their scope at `ς`.
RFC: `\mathsf{scale}_\Upsilon` -/
def Shape.Next.scale (ς : Multiplicity) : Shape.Next → Multiplicity
  | .recursor _ => .one
  | .lifting _ => ς

mutual

-- ADE: none.
/-- `Ξ ◀ ς; χ`: the shape has the ownerships `ς` and `χ`: each lifted destructor requires `ς` of the
value that it observes, and its result has the ownership `own_χ(Υ)` of the shape `Υ` of its result,
whatever the ownerships of its arguments, as the lifting declares them.
RFC: `\mathsf{uniform}_\Xi` -/
def Shape.Uniform (ς χ : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ _ _ _ _ _ _ ψ ς' _ _ next rest =>
    ς' = ς ∧ ψ = ⟨some (next.ownership χ), fun _ => none⟩ ∧ next.Uniform ς χ ∧ rest.Uniform ς χ

-- ADE: none.
/-- `Υ ◀ ς; χ`: the shape of a result has the ownerships `ς` and `χ`: the recursor itself does, and
the next lifting when its shape does, which the RFC does not need to state.
RFC: `\mathsf{uniform}_\Upsilon` -/
def Shape.Next.Uniform (ς χ : Multiplicity) : Shape.Next → Prop
  | .recursor _ => True
  | .lifting σ => σ.Uniform ς χ

end

-- ADE: none.
/-- The ownerships of the arguments of the observation built for a lifted destructor, at the scale
`s`, given the ownerships `ō` of the arguments of its branch: the ownership of the variable of each
argument, `s · ō · π'`, and the requirement of its position in the observation when it is erased,
`↯` having every ownership. -/
def Shape.argOwnerships {c : Nat} (s : Multiplicity) (os πs ϱs πs' : Fin c → Multiplicity) :
    Fin c → Multiplicity :=
  fun k => if πs k = .zero then ϱs k else s * (os k * πs' k)

mutual

-- ADE: none.
/-- The shape meets the requirements of the observations of a field, whose branches see the term of
the recursor at the ownership `o`, the corecursors capturing the scope at `ς`: for each destructor
observed, the requirement `ς₀` of the destructor that it lifts on the value that it observes is
within `o`, and, for all the ownerships of the arguments of its branch that meet their requirements,
the arguments of the observation meet the requirements of their positions in it, and the value of
the ownership `ψ₀` of its result at them is defined; the requirement `r̂` of the recursion gives the
rest, that the value keeps `o`. -/
def Shape.Meets (o ς : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ ς₀ next rest =>
    (ρᵢ ≠ .zero → ς₀ ≤ o ∧ ∀ os : Fin c → Multiplicity, (∀ k, ϱs' k ≤ os k) →
      (∀ k, ϱs k ≤ Shape.argOwnerships (next.scale ς) os πs ϱs πs' k) ∧
      ∃ v, ψ₀.value (List.ofFn (Shape.argOwnerships (next.scale ς) os πs ϱs πs')) = some v) ∧
    next.Meets o ς ∧ rest.Meets o ς

-- ADE: none.
/-- The shape of a result meets the requirements of the observations: the recursor itself does,
and the next lifting when its shape does. -/
def Shape.Next.Meets (o ς : Multiplicity) : Shape.Next → Prop
  | .recursor _ => True
  | .lifting σ => σ.Meets o ς

end

mutual

-- ADE: none.
/-- The observations of a field keep the ownership `o` of the term of the recursor: for each
destructor observed, for all the ownerships of the arguments of its branch that meet their
requirements, the value of the ownership `ψ₀` of its result at them, when it is defined, keeps `o`,
which the requirement `r̂` of the recursion gives. -/
def Shape.Keeps (o ς : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ _ next rest =>
    (ρᵢ ≠ .zero → ∀ os : Fin c → Multiplicity, (∀ k, ϱs' k ≤ os k) → ∀ v,
      ψ₀.value (List.ofFn (Shape.argOwnerships (next.scale ς) os πs ϱs πs')) = some v →
        o ≤ o * v) ∧
    next.Keeps o ς ∧ rest.Keeps o ς

-- ADE: none.
/-- The observations from the shape of a result keep the ownership `o`: the recursor itself does,
and the next lifting when its shape does. -/
def Shape.Next.Keeps (o ς : Multiplicity) : Shape.Next → Prop
  | .recursor _ => True
  | .lifting σ => σ.Keeps o ς

end

-- ADE: none.
/-- `Ξ meets o; ς`: the shape meets the requirements of the recursions on the observations of a
field, whose branches see the term of the recursor at the ownership `o`, the corecursors capturing
the scope at `ς`: for each destructor observed at run time, the requirement `ς₀` of the destructor
that it lifts on the value that it observes is within `o`, and, for all the ownerships of the
arguments of its branch that meet their requirements, the arguments of the observation meet the
requirements of their positions in it, and the value of the ownership `ψ₀` of its result at them is
defined and keeps `o`, so that the observation has an ownership within `o`, as each level of the
recursion; the RFC writes the ownerships of the arguments of the observation `ō'`, which
`Shape.argOwnerships` gives. The source checks the first part, `Shape.Meets`, and its requirement of
the recursion gives the second, `Shape.Keeps`.
RFC: `\mathsf{meets}_\Xi` -/
def Shape.Requires (o ς : Multiplicity) (σ : Shape) : Prop :=
  σ.Meets o ς ∧ σ.Keeps o ς

-- ADE: none.
/-- `Υ meets o; ς`: the shape of a result meets the requirements of the recursions: the recursor
itself does, and the next lifting when its shape does, which the RFC does not need to state.
RFC: `\mathsf{meets}_\Upsilon` -/
def Shape.Next.Requires (o ς : Multiplicity) (next : Shape.Next) : Prop :=
  next.Meets o ς ∧ next.Keeps o ς

end Sic.Core
