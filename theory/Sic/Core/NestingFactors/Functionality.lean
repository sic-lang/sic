module

public import Sic.Core.NestingFactors
import Sic.Core.Syntax.Signature

/-!
# Functionality of the Factors

The factors of annex 20 of RFC 36 are functions of the result of a destructor of a lifting, in a
signature whose names are distinct: a name has one declaration there, so that an instance of a
lifting reads one list of destructors, whose factors are unique by induction.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature}

mutual

-- ADE: none.
/-- The result of a destructor of a lifting has one factor at most, in a signature whose names are
distinct.
RFC: `\mathsf{unique}_{\mathsf{factor}}` -/
theorem Term.Factor.unique (hd : sig.Distinct) :
    {k : Nat} → {Γ : Scope} → {B : Term k Γ} → {π₁ π₂ : Grade} → Term.Factor sig B π₁ →
      Term.Factor sig B π₂ → π₁ = π₂
  | _, _, _, _, _, .var _ _, .var _ _ => rfl
  | _, _, _, _, _, .inst h₁ hq hp hds₁, .inst h₂ _ _ hds₂ => by
    obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h₁ h₂
    cases eq_of_heq hT
    rw [Destructors.Factor.unique hd hds₁ hds₂]

-- ADE: none.
/-- Destructors have one meet at most, in a signature whose names are distinct. -/
theorem Destructors.Factor.unique (hd : sig.Distinct) :
    {k : Nat} → {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} →
      {π₁ π₂ : Option Grade} → Destructors.Factor sig ds π₁ → Destructors.Factor sig ds π₂ →
        π₁ = π₂
  | _, _, _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, _, _, .cons hB₁ hds₁, .cons hB₂ hds₂ => by
    rw [Term.Factor.unique hd hB₁ hB₂, Destructors.Factor.unique hd hds₁ hds₂]

end

end Sic.Core
