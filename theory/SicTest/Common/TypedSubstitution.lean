module

import Sic.Core.TypedSubstitution

/-!
# Common Substitutions

The substitutions of `Sic.Core.TypedSubstitution` that the reductions of the examples build.
-/

namespace SicTest.Common.TypedSubstitution

open Sic.Core Sic.Core.Term

/-- Every substitution replaces the variables of the empty context, which has none. -/
theorem substWf_empty : Δ ⊢ˢ σ : Con.empty := fun x => x.elim0

/-- A substitution extended by a term of the type of a new declaration. -/
theorem substWf_cons (hσ : Δ ⊢ˢ σ : Γ) (ha : Δ ⊢ a : A.subst σ) : Δ ⊢ˢ σ.cons a : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ a : A.wk1.subst _
    rw [subst_cons_wk1]
    exact ha
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ σ _ : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst _
    rw [Con.get_succ, subst_cons_wk1]
    exact hσ _

end SicTest.Common.TypedSubstitution
