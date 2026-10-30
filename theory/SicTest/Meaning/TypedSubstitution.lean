module

import Sic.Core.TypedSubstitution

/-!
# Meaning of the Typed Substitution

The identity substitution is a substitution of every well-formed context to itself.
-/

namespace SicTest.Meaning.TypedSubstitution

open Sic.Core Sic.Grade Sic.Core.Term

/-- Each variable replaced by itself is a substitution of every well-formed context to itself. -/
example (hΓ : ⊢ Γ) : Γ ⊢ˢ var : Γ := fun x => by
  rw [subst_var]
  exact .var hΓ

end SicTest.Meaning.TypedSubstitution
