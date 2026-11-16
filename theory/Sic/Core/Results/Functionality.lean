module

public import Sic.Core.Results
import Sic.Core.Lifting.Functionality

/-!
# Functionality of the Recursive Results

In a signature whose names are distinct, the fields of a constructor have one telescope of
recursive results at most: the nesting of a field tells which rule gives its result, the motive of
a type of the block is the one that the lifting of the block gives its name, and the type of a
nested field has one lifting at most.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

-- ADE: none.
/-- Fields have one telescope of recursive results at most, in a signature whose names are
distinct. -/
theorem Terms.ResultTypes.unique (hd : sig.Distinct) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps₁ ps₂ : List Parameter} → {R₁ : Telescope k Δ' ps₁} →
      {R₂ : Telescope k Δ' ps₂} → Terms.ResultTypes sig v ρ ns ps As xs R₁ →
        Terms.ResultTypes sig v ρ ns ps As xs R₂ →
          (⟨ps₁, R₁⟩ : (ps' : List Parameter) × Telescope k Δ' ps') = ⟨ps₂, R₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, .nil, h₂ => by
    cases h₂
    rfl
  | _, _, _, _, _, _, _, _, _, _, _, .plain h₁, h₂ => by
    cases h₂ with
    | plain h₂ => exact Terms.ResultTypes.unique hd h₁ h₂
  | _, _, _, _, _, _, _, _, _, _, _, .recursive hD₁ h₁, h₂ => by
    cases h₂ with
    | recursive hD₂ h₂ =>
      cases hD₁.symm.trans hD₂
      cases Terms.ResultTypes.unique hd h₁ h₂
      rfl
  | _, _, _, _, _, _, _, _, _, _, _, .nested hA₁ h₁, h₂ => by
    cases h₂ with
    | nested hA₂ h₂ =>
      obtain ⟨rfl, -⟩ := Term.Lifts.unique hd hA₁ hA₂
      cases Terms.ResultTypes.unique hd h₁ h₂
      rfl

end Sic.Core
