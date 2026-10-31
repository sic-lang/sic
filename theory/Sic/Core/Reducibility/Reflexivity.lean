module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# Reflexivity

The interpretation of a reducible type equates it to itself.
The interpretation has no reflexivity of terms to prove: a term is reducible when the interpretation
equates it to itself.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/-- The interpretation of a reducible type equates the type to itself, at any level. -/
theorem LogRel.refl_eqType {lower : ∀ l' < l, Relation k} :
    LogRel l lower Γ A P → P.eqType A
  | .univ _ hA => ⟨_, hA, .refl _⟩
  | .ne hA hN hNN => ⟨_, hA, hN, hNN⟩
  | .pi hA hPi _ _ hF hG _ =>
    ⟨_, _, hA, hPi, fun hρ hΔ => (hF hρ hΔ).refl_eqType,
      fun hρ hΔ ha => (hG hρ hΔ ha).refl_eqType⟩

-- ADE: `reflEq`, in `Definition/LogicalRelation/Properties/Reflexivity.agda`.
-- Pujet: `reflEq`, in `Definition/LogicalRelation/Properties/Reflexivity.agda`.
/-- The interpretation of a reducible type equates the type to itself. -/
theorem LogicalRelation.refl_eqType (h : Γ ⊩⟨l⟩ A ▸ P) : P.eqType A :=
  (LogicalRelation.unfold ▸ h).refl_eqType

end Sic.Core.Reducibility
