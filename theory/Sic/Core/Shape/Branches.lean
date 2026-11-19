module

public import Sic.Core.Shape

/-!
# Recursive Results of the Branches

The recursive results of the branches of a recursor of the target language of annex 19 of RFC 36,
`w`: what computes each recursive result of a branch, the recursor on a recursive field, the
corecursor of a lifting on a nested field, of the shape of annex 14 of the type of the field, or
nothing when the result is erased.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `k`: the recursive result of a branch of a recursor of the target language: `erased`, the RFC's
`⊥`, when the result is erased, `field l` when it is the recursor on the recursive field `l`, and
`nested l σ` when it is the corecursor of a lifting, of the shape `σ`, on the nested field `l`; the
positions are counted from `0`, while the RFC counts them from `1`.
RFC: `\mathsf{syntax}_w` -/
inductive RecursiveResult where
  /-- `⊥`. -/
  | erased
  /-- `l`. -/
  | field (l : Nat)
  /-- `n.Ξ`. -/
  | nested (l : Nat) (σ : Shape)

-- ADE: none.
/-- The result at the position `l` of a field, or erased when there is none: a recursive result
that the evaluation computes by the recursor. -/
def RecursiveResult.ofPosition : Option Nat → RecursiveResult
  | none => .erased
  | some l => .field l

-- ADE: none.
/-- The position of the field of a result that the recursor computes, if any: a nested result, which
the evaluation does not compute by the recursor, has none. -/
def RecursiveResult.position : RecursiveResult → Option Nat
  | .field l => some l
  | .erased | .nested .. => none

-- ADE: none.
/-- The position of the field on which a result recurses, by the recursor on the field itself or by
the recursors on its observations, if any. -/
def RecursiveResult.fieldPosition : RecursiveResult → Option Nat
  | .field l | .nested l _ => some l
  | .erased => none

-- ADE: none.
/-- The result is the corecursor of a lifting, on a nested field. -/
def RecursiveResult.IsNested : RecursiveResult → Prop
  | .nested .. => True
  | .erased | .field _ => False

-- ADE: none.
/-- The factor of a result, the multiplicity by which it multiplies the uses of the scope by the
recursion that computes it: `0` when it is erased, `1` for the recursor itself, and the factor of the
shape of a nested result.
RFC: `\mathsf{factor}_w` -/
def RecursiveResult.factor : RecursiveResult → Multiplicity
  | .erased => .zero
  | .field _ => .one
  | .nested _ σ => σ.factor

/-- A result that is not nested multiplies the uses by its multiplicity when the recursor computes it,
and by `0` when it does not. -/
theorem RecursiveResult.mul_factor {r : RecursiveResult} (h : ¬ r.IsNested) (π : Multiplicity) :
    π * r.factor = if r.position.isSome then π else .zero := by
  cases r with
  | erased => cases π <;> rfl
  | field _ => cases π <;> rfl
  | nested _ _ => exact absurd trivial h

/-- The result of a position is not nested. -/
theorem RecursiveResult.not_isNested_ofPosition (o : Option Nat) :
    ¬ (RecursiveResult.ofPosition o).IsNested := by
  cases o <;> exact id

/-- An erased result has no position. -/
@[simp]
theorem RecursiveResult.position_erased : RecursiveResult.erased.position = none := rfl

/-- A result of a position has this position. -/
@[simp]
theorem RecursiveResult.position_ofPosition (o : Option Nat) :
    (RecursiveResult.ofPosition o).position = o := by
  cases o <;> rfl

end Sic.Core
