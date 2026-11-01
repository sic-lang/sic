module

public import Sic.Core.Reduction
public import SicTest.Omega.Syntax

/-!
# The Divergent Term Ω: Reduction

`Ω` reduces only to itself, by `(β)`, and is not a weak head normal form, so that no sequence of
reductions from it ends at one.
-/

@[expose] public section

namespace SicTest.Omega.Reduction

open Sic.Core Sic.Core.Term SicTest.Omega.Syntax

/--
`Ω` reduces in one step only to itself: its function `ω` is an abstraction, which does not reduce,
so that the step is `(β)`, which substitutes `ω` for the variable of `x ∘_p x`.
-/
theorem termRed_omega (h : Γ ⊢ omega p A ⇒ u : B) : u = omega p A := by
  generalize e : omega p A = t at h
  induction h with
  | conv _ _ ih => exact ih e
  | app h _ => cases e; nomatch Whnf.not_termRed .lam h
  | beta => cases e; rfl

/-- `Ω` is not a weak head normal form: it applies an abstraction, so that it is not neutral. -/
theorem not_whnf_omega : ¬ Whnf (omega p A : Term k n) := by
  rintro (_ | _ | _ | (_ | ⟨(_ | _)⟩))

/-- No sequence of reductions from `Ω` ends at a weak head normal form. -/
theorem not_termRedWhnf_omega : ¬ Γ ⊢ omega p A ↘ u : B := by
  rintro ⟨h, hu⟩
  generalize e : omega p A = t at h
  induction h with
  | refl => exact not_whnf_omega (e ▸ hu)
  | step h₁ _ ih => subst e; exact ih hu (termRed_omega h₁).symm

end SicTest.Omega.Reduction
