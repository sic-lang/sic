module

public import Sic.Core.Reduction
import Sic.Core.Injectivity
import Sic.Core.Inversion
import Sic.Core.Normalization
import Sic.Core.WellFormed

/-!
# Canonicity

A closed term of a type reduces to a weak head normal form of the head of its type, as in the
formalizations of ADE and of Pujet: a closed term of a type of functions reduces to an abstraction,
with the grade of the type, and a closed term of a universe reduces to a universe or to a type of
functions.
No closed term is neutral, since a neutral term has a variable at its head, and the weak head normal
form of a term has a type of the same head as its own, by the inversion of its typing and the
injectivity of the types.

## Correspondence with the Formalizations of ADE and of Pujet

The closed neutral terms of ADE have a definition at their head, which `closed-ne` allows, and the
one of Pujet is typed.
ADE and Pujet state the canonicity of the natural numbers, `canonicity`: a closed term of `ℕ` is
equal to a numeral, which the core of RFC 24 does not have.
Their proofs read the interpretation of the type, while the proofs here invert the typing of the
weak head normal form, which `HasType.whnf` gives.
-/

@[expose] public section

namespace Sic.Core

open Term

-- ADE: `closed-ne`, in `Definition/Untyped/Neutral.agda`.
-- Pujet: `noNe`, in `Definition/Typed/Properties.agda`.
/-- No closed term is neutral: the variable at its head would be in the empty context. -/
theorem Neutral.not_closed {t : Term k 0} (h : Neutral t) : False := by
  induction h with
  | var => rename_i x; exact x.elim0
  | app _ ih => exact ih

-- ADE: none.
-- Pujet: none.
/-- A closed term of a type of functions reduces to an abstraction with the grade of the type. -/
theorem HasType.canonical_pi (h : .empty ⊢ t : Term.pi p q A B) :
    ∃ A' u, .empty ⊢ t ↘ Term.lam p A' u : Term.pi p q A B := by
  have ⟨w, hw⟩ := h.whnf
  have ⟨_, hw', _⟩ := hw.1.termEq.wf
  cases hw.2 with
  | univ => have ⟨_, e, _⟩ := (TypeEq.symm hw'.inv_univ).inv_univ .pi; cases e
  | pi => have ⟨_, _, _, _, hC⟩ := hw'.inv_pi_univ; have ⟨_, e, _⟩ := hC.symm.inv_univ .pi; cases e
  | lam =>
    have ⟨_, _, _, _, hC⟩ := hw'.inv_lam
    cases hC.pi_inj.1
    exact ⟨_, _, hw⟩
  | ne hN => exact hN.not_closed.elim

-- ADE: none.
-- Pujet: none.
/-- A closed term of a universe reduces to a universe or to a type of functions. -/
theorem HasType.canonical_univ (h : .empty ⊢ t : Term.univ l) :
    (∃ l', .empty ⊢ t ↘ Term.univ l' : Term.univ l) ∨
      ∃ p q A B, .empty ⊢ t ↘ Term.pi p q A B : Term.univ l := by
  have ⟨w, hw⟩ := h.whnf
  have ⟨_, hw', _⟩ := hw.1.termEq.wf
  cases hw.2 with
  | univ => exact .inl ⟨_, hw⟩
  | pi => exact .inr ⟨_, _, _, _, hw⟩
  | lam => have ⟨_, _, _, _, hC⟩ := hw'.inv_lam; have ⟨_, e, _⟩ := hC.inv_univ .pi; cases e
  | ne hN => exact hN.not_closed.elim

end Sic.Core
