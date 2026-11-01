module

import Sic.Core.TypedSubstitution
import SicTest.Combinators.Syntax
import SicTest.Combinators.Typing
import SicTest.Common.TypedSubstitution

/-!
# The Combinators K and S: Typed Substitution

The combinators moved to other contexts.
-/

@[expose] public section

namespace SicTest.Combinators.TypedSubstitution

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Combinators.Syntax SicTest.Combinators.Typing
  SicTest.Common.TypedSubstitution

/--
A closed term keeps its type in every well-formed context, by the substitution of the variables of
the empty context, as `K` does: the substitution leaves it unchanged.
-/
example (h : ⊢ Γ) : Γ ⊢ combinatorK : combinatorKType :=
  (hasType_combinatorK .empty).subst (σ := Fin.elim0) substWf_empty h

/-- `S K K` keeps the type of the identity of `A` after a new declaration `z : A`. -/
example : ΓA ∙ var 0 ⊢ skk.wk1 : pi 𝟙 𝟘 (var 1) (var 2) :=
  hasType_skk.wk (.step .id) (.snoc (.univ hasType_ΓA_var))

end SicTest.Combinators.TypedSubstitution
