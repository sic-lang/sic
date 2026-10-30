module

import Sic.Core.Substitution

/-!
# Common Laws of the Substitution

The laws of `Sic.Core.Substitution` that the reductions of the examples use.
-/

namespace SicTest.Common.Substitution

open Sic.Core Sic.Core.Term

/--
Instantiating the variable of a body under a substitution is substituting it with the substitution
extended by the argument, as `(β)` does when it applies an abstraction that a substitution moved.
-/
theorem subst_lift_instantiate (σ : Subst k m n) (t : Term k (n + 1)) (a : Term k m) :
    (t.subst σ.lift).instantiate a = t.subst (σ.cons a) := by
  rw [instantiate, subst_subst]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨x + 1, _⟩ =>
    show (Term.wk1 _).subst _ = _
    rw [subst_cons_wk1, subst_var]
    rfl

end SicTest.Common.Substitution
