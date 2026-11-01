module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# The Universes: Logical Relation

The universes are reducible at the levels above theirs.
-/

@[expose] public section

namespace SicTest.Universe.Reducibility.LogicalRelation

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility

/-- `LogRel.univ` does not interpret `U_l` at the level `0`, since `l` is bounded by `0`. -/
example : ¬ (0 : Nat) < (Level.var 0 : Level 1).bound := by decide

variable [EqualityRelation]

/-- The universe `U₀` is reducible at the level `1`, in the empty context. -/
example : ∃ P, (.empty : Con 0 0) ⊩⟨1⟩ univ .zero ▸ P :=
  ⟨_, LogicalRelation.unfold ▸ LogRel.univ (L := .zero) (by decide) (.refl (.univ (.univ .empty)))⟩

end SicTest.Universe.Reducibility.LogicalRelation
