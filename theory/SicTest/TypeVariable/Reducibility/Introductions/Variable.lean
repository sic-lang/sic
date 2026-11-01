module

public import SicTest.TypeVariable.Reducibility.Validity
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable
import SicTest.TypeVariable.Reducibility.LogicalRelation

/-!
# A Type Variable: Validity of the Variables

The validity of the variables gives the type variable `A` of the context `A : U_l` as a valid type,
at the level `0` that `SicTest.TypeVariable.Reducibility.Validity` finds by hand, and the variables
of the context `A : U_l, x : A, y : A` as valid terms of `A`, for every equality relation.
-/

@[expose] public section

namespace SicTest.TypeVariable.Reducibility.Introductions.Variable

open Sic.Core Sic.Core.Term Sic.Core.Reducibility SicTest.TypeVariable.Reducibility.LogicalRelation
open SicTest.TypeVariable.Reducibility.Validity

variable [EqualityRelation]

/--
The type variable `A` is a valid type at the level `0`: it is a valid term of `U_l`, whose terms are
valid types at the value of `l` when it is `0`.
-/
theorem validTypeEq_A : ΓA ⊩ᵛ⟨0⟩ var 0 ≡ var 0 :=
  have ⟨_, h⟩ := ValidTermEq.var validCon_ΓA 0
  ValidTermEq.toTypeEq (L := .var 0) h

/-- The context `A : U_l, x : A, y : A`. -/
def ΓAxy : Con 1 3 := ΓA ∙ var 0 ∙ var 1

/-- The context `A : U_l, x : A, y : A` is valid, since `A` is a valid type before `x` and `y`. -/
theorem validCon_ΓAxy : ⊩ᵛ ΓAxy := by
  rw [ΓAxy, ValidCon.unfold_snoc]
  exact ⟨0, validTypeEq_A.wk1 validTypeEq_A⟩

/--
The variable `x`, which is not the last one, is a valid term of `A`, so that it is a reducible term
of `A` under the identity substitution.
-/
example : ∃ l, ΓAxy ⊩⟨l⟩ var 1 ≡ var 1 : var 2 :=
  have ⟨l, h⟩ := ValidTermEq.var validCon_ΓAxy 1
  ⟨l, h.2 (ReducibleSubstEq.var validCon_ΓAxy)⟩

/-- The variable `y`, the last one, is a reducible term of `A` under the identity substitution. -/
example : ∃ l, ΓAxy ⊩⟨l⟩ var 0 ≡ var 0 : var 2 :=
  have ⟨l, h⟩ := ValidTermEq.var validCon_ΓAxy 0
  ⟨l, h.2 (ReducibleSubstEq.var validCon_ΓAxy)⟩

end SicTest.TypeVariable.Reducibility.Introductions.Variable
