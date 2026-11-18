module

public import Sic.Core.Erasure.Nested
public import Sic.Core.Evaluation

/-!
# Run Time of the Nested Results

The recursive result of a nested field at run time, `n.Ξ`: the corecursor without state whose
branches the evaluation builds from the shape `Ξ` and the branches of the recursor, one for each
destructor that the lifting keeps, each observing the field by the destructor that it lifts and
giving the recursor on this observation, or the corecursor of the next lifting.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Branches Built From a Shape -/

/-- The branch built at the index `k` from a shape is the branch of the element of the shape at this
index: without state, it binds the arguments of the lifted destructor and observes the term by the
destructor that it lifts, then gives the result of this observation, or `↯` when the destructor is
never observed at run time. -/
theorem Shape.branches_get {m : Nat} (ρ ϱ : Multiplicity) (M : Target m) (Ns : TargetBranches m) :
    (k : Nat) → (σ : Shape) → {i c : Nat} → {ρᵢ : Multiplicity} →
      {πs ϱs πs' ϱs' : Fin c → Multiplicity} → {ψ : ResultOwnership Multiplicity c} →
      {ς : Multiplicity} → {ψ₀ : ResultOwnership Multiplicity c} → {ς₀ : Multiplicity} →
      {next : Shape.Next} → {rest : Shape} →
      σ.drop k = .cons i c ρᵢ πs ϱs πs' ϱs' ψ ς ψ₀ ς₀ next rest →
      (σ.branches ρ ϱ M Ns).get k = some (.none, ⟨0, c, Fin.elim0, Fin.elim0, πs', ϱs', ψ, ς,
        if ρᵢ = .zero then .erased else
          next.body ρ ϱ
            (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
              (Targets.ofVars πs ϱs (Shape.argVar m c)))
            (Ns.rename (TargetRen.shift m (0 + c)))⟩)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by
    cases h
    rfl
  | _ + 1, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, h => nomatch h
  | k + 1, .cons .., _, _, _, _, _, _, _, _, _, _, _, _, _, h =>
    Shape.branches_get ρ ϱ M Ns k _ h

end Sic.Core
