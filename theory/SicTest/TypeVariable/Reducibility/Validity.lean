module

import Sic.Core.Reducibility.Validity
import all SicTest.Universe.Reducibility.Validity
import all SicTest.TypeVariable.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Uniqueness

/-!
# A Type Variable: Validity

The context `A : U_l` of a type variable is valid, and so is the type variable `A`, for every
equality relation.
-/

namespace SicTest.TypeVariable.Reducibility.Validity

open Sic.Core Sic.Core.Term Sic.Core.Reducibility SicTest.TypeVariable.Reducibility.LogicalRelation
open SicTest.Universe.Reducibility.Validity

variable [EqualityRelation]

/-- The context `A : U_l` is valid, since `U_l` is a valid type of the empty context. -/
theorem validCon_ΓA : ⊩ᵛ ΓA := by
  rw [ΓA, ValidCon.unfold_snoc]
  exact ⟨1, validTypeEq_univ (by rw [ValidCon.unfold_empty]; trivial)⟩

/--
The type variable `A` is a valid type at the level `0`: two reducibly equal substitutions replace it
by two reducibly equal terms of `U_l`, which are reducibly equal types at the level `0`.
-/
example : ΓA ⊩ᵛ⟨0⟩ var 0 ≡ var 0 := by
  rw [ValidTypeEq.unfold]
  refine ⟨validCon_ΓA, fun {_ Δ σ₁ σ₂} hσ => ?_⟩
  rw [ΓA, ReducibleSubstEq.unfold_snoc] at hσ
  have ⟨⟨_, _, _, hU, hA⟩, _⟩ := hσ
  -- The interpretation of `U_l` is the one that `LogRel.univ` gives it.
  have hU' : Δ ⊩⟨1⟩ univ (.var 0) ▸ _ := LogicalRelation.unfold ▸ LogRel.univ (L := .var 0)
    (by decide) (.refl (.univ (.univ hU.escape.wfCon)))
  rw [hU.unique hU'] at hA
  have ⟨_, _, _, _, _, _, _, _, hA₁, ⟨_, hA₂⟩, hA⟩ := hA
  exact ⟨_, _, hA₁, hA₂, hA⟩

end SicTest.TypeVariable.Reducibility.Validity
