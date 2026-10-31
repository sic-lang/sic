module

import Sic.Core.Reduction
import Sic.Core.WellFormed
import all SicTest.Common.WellFormed

/-!
# Common Reductions

The reductions of the closed terms of the examples, applied to their arguments, which prove their
equalities.
Each step applies an abstraction that the previous steps moved by a substitution of their arguments,
which `termRed_beta_subst` reduces from the typing of the body of the abstraction before the
substitution: the bodies of a closed term, one under each of its binders, are typed in the context
of the domains of its type, `contextAt`.
-/

namespace SicTest.Common.Reduction

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Common.WellFormed

/--
`(β)` for an abstraction moved by the substitution `σ`, from the typing of its body alone: its
argument replaces its variable, and `σ` the others.
-/
theorem termRed_beta_subst (ht : Γ ∙ A ⊢ t : B) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ)
    (ha : Δ ⊢ a : A.subst σ) :
    Δ ⊢ app p ((lam p A t).subst σ) a ⇒ t.subst (σ.cons a) : B.subst (σ.cons a) := by
  have ⟨_, hA⟩ := wfCon_snoc_inv ht.wfCon
  have ⟨_, hB⟩ := ht.wfType.sort
  have hPi' := (HasType.pi (p := p) (q := 𝟘) hA hB).subst hσ hΔ
  have ⟨_, hA'⟩ := hPi'.inv_pi.1
  have hΔ' : ⊢ Δ ∙ A.subst σ := .snoc (.univ hA')
  have h := TermRed.beta (.univ hPi') (ht.subst (hσ.lift hΔ') hΔ') ha
  rwa [subst_lift_instantiate, subst_lift_instantiate] at h

/-- The body of an abstraction, or the term itself, moved, for any other term. -/
def body : Term k n → Term k (n + 1)
  | lam _ _ t => t
  | t => t.wk1

/-- The codomain of a type of functions, or the term itself, moved, for any other term. -/
def codomain : Term k n → Term k (n + 1)
  | pi _ _ _ B => B
  | t => t.wk1

/-- The domain of a type of functions, or the term itself, for any other term. -/
def domain : Term k n → Term k n
  | pi _ _ A _ => A
  | t => t

/-- The body of the closed term `t` under its first `j` binders. -/
def bodyAt : (j : Nat) → Term k 0 → Term k j
  | 0, t => t
  | j + 1, t => body (bodyAt j t)

/-- The codomain of the closed type `T` after its first `j` domains. -/
def codomainAt : (j : Nat) → Term k 0 → Term k j
  | 0, T => T
  | j + 1, T => codomain (codomainAt j T)

/-- The context of the first `j` domains of the closed type `T`. -/
def contextAt (T : Term k 0) : (j : Nat) → Con k j
  | 0 => .empty
  | j + 1 => contextAt T j ∙ domain (codomainAt j T)

end SicTest.Common.Reduction
