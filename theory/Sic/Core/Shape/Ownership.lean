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
the ownership `ψ₀` of its result at them is defined, and the shape of its result meets them in turn;
a destructor never observed has the branch `↯`, which observes nothing; the requirement `r̂` of the
recursion gives the rest, that the value keeps `o`. -/
def Shape.Meets (o ς : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ ς₀ next rest =>
    (ρᵢ ≠ .zero → ς₀ ≤ o ∧ (∀ os : Fin c → Multiplicity, (∀ k, ϱs' k ≤ os k) →
      (∀ k, ϱs k ≤ Shape.argOwnerships (next.scale ς) os πs ϱs πs' k) ∧
      ∃ v, ψ₀.value (List.ofFn (Shape.argOwnerships (next.scale ς) os πs ϱs πs')) = some v) ∧
      next.Meets o ς) ∧
    rest.Meets o ς

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
and the observations from the shape of its result keep it in turn, which the requirement `r̂` of the
recursion gives along the prefixes of the paths of the destructors observed. -/
def Shape.Keeps (o ς : Multiplicity) : Shape → Prop
  | .nil => True
  | .cons _ c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ _ next rest =>
    (ρᵢ ≠ .zero → (∀ os : Fin c → Multiplicity, (∀ k, ϱs' k ≤ os k) → ∀ v,
      ψ₀.value (List.ofFn (Shape.argOwnerships (next.scale ς) os πs ϱs πs')) = some v →
        o ≤ o * v) ∧
      next.Keeps o ς) ∧
    rest.Keeps o ς

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
recursion, and the shape of its result meets the requirements in turn; a destructor never observed,
whose branch is `↯`, asks nothing; the RFC writes the ownerships of the arguments of the observation `ō'`, which
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

mutual

-- ADE: none.
/-- The products `a · ψ₁⁻ · … · ψ_h⁻` along the prefixes `d₁ … d_h` of the paths of the shape, other
than the empty one, after a prefix of the product `a`: each destructor observed extends the prefix,
whose product is then times the value `ψ⁻` of the ownership `ψ₀` of the result of the destructor
that it lifts at the least ownerships of the arguments of its branch, their requirements, or `1`
when this value is not defined, and the paths go on in the shape of its result; a destructor never
observed extends no path. -/
def Shape.prefixes (ς a : Multiplicity) : Shape → List Multiplicity
  | .nil => []
  | .cons _ _ ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ _ next rest =>
    (if ρᵢ = .zero then [] else
      let a' := a *
        (ψ₀.value (List.ofFn (Shape.argOwnerships (next.scale ς) ϱs' πs ϱs πs'))).getD .one
      a' :: next.prefixes ς a') ++ rest.prefixes ς a

-- ADE: none.
/-- The products along the prefixes of the paths of the shape of a result, after a prefix of the
product `a`: none for the recursor itself, where the paths end, and those of the next lifting. -/
def Shape.Next.prefixes (ς a : Multiplicity) : Shape.Next → List Multiplicity
  | .recursor _ => []
  | .lifting σ => σ.prefixes ς a

end

-- ADE: none.
/-- What the shape of a nested field gives the requirement of the recursion: for each prefix
`d₁ … d_h` of each of its paths, the empty one included, the product `ς · ψ₁⁻ · … · ψ_h⁻` of the
requirement `ς` of the corecursors on the values that they observe and of the values `ψ⁻` of the
ownerships of the results of the destructors of the prefix at the least ownerships of their
arguments, so that the field `x_l` of the requirement `r_l`, used with the grade `c_l`, gives the
pairs `c_l ◀ r_l · ς · ψ₁⁻ · … · ψ_h⁻`. -/
def Shape.recursion (ς : Multiplicity) (σ : Shape) : List Multiplicity :=
  ς :: σ.prefixes ς ς

/-! ## Properties -/

-- ADE: none.
/-- The value of the ownership `ψ` of a result is monotone in the ownerships of its arguments: it is
defined at the same ownerships, a meet of products of them, so that its least value, at the
requirements of the arguments, bounds its value at any ownerships that meet them, which the
requirement of the recursion reads. -/
theorem ResultOwnership.value_mono :
    {c : Nat} → (ψ : ResultOwnership Multiplicity c) → (os os' : Fin c → Multiplicity) →
      (∀ k, os k ≤ os' k) →
        Option.Rel (· ≤ ·) (ψ.value (List.ofFn os)) (ψ.value (List.ofFn os'))
  | 0, ψ, _, _, _ => by
    show Option.Rel _ ψ.constant ψ.constant
    cases ψ.constant with
    | none => exact .none
    | some c => exact .some ((by decide : ∀ a : Multiplicity, a ≤ a) c)
  | _ + 1, ψ, os, os', h => by
    have ih := ResultOwnership.value_mono ψ.tail (fun k => os k.succ) (fun k => os' k.succ)
      fun k => h k.succ
    rw [List.ofFn_succ, List.ofFn_succ]
    show Option.Rel _ (Option.merge _ ((ψ.coefficient 0).map (os 0 * ·)) (ψ.tail.value _))
      (Option.merge _ ((ψ.coefficient 0).map (os' 0 * ·)) (ψ.tail.value _))
    generalize ψ.tail.value (List.ofFn fun k => os k.succ) = x at ih ⊢
    generalize ψ.tail.value (List.ofFn fun k => os' k.succ) = y at ih ⊢
    have hm : ∀ a b c : Multiplicity, a ≤ b → a * c ≤ b * c := by decide
    cases ψ.coefficient 0 with
    | none =>
      cases ih with
      | none => exact .none
      | some h => exact .some h
    | some c =>
      cases ih with
      | none => exact .some (hm _ _ c (h 0))
      | some h' =>
        exact .some ((by decide : ∀ a b c d : Multiplicity, a ≤ b → c ≤ d → a ⊓ c ≤ b ⊓ d) _ _ _ _
          (hm _ _ c (h 0)) h')

end Sic.Core
