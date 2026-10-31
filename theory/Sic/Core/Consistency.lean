module

public import Sic.Core.Typing
import Sic.Core.Canonicity
import Sic.Core.Injectivity
import Sic.Core.Inversion
import Sic.Core.Normalization
import Sic.Core.TypedSubstitution
import Sic.Core.WellFormed

/-!
# Consistency

The type `Π^q_p (X : U_l). X`, which is the empty type `∀X. X` of System F in
[Girard, Lafont and Taylor](https://www.paultaylor.eu/stable/prot.pdf), has no closed term, so that
not every type has one, as in the formalizations of ADE and of Pujet.

A closed term of it reduces to an abstraction, by the canonicity, whose body `b` has the type `X` in
the context `X : U_l`.
The weak head normal form of `b` has a type of its head, which is not `X`: a universe and a type of
functions have a universe, an abstraction has a type of functions, and a neutral term has the
variable `X` at its head, the only one of the context, so that it is `X` itself, of the type `U_l`,
since an application of `X` would make `U_l` a type of functions.

## Correspondence with the Formalizations of ADE and of Pujet

ADE state that their empty type has no closed term, and Pujet that zero and one are not equal, while
the core of RFC 24 has neither an empty type nor the natural numbers.
Their proofs read the interpretation of the type, while the proof here inverts the typing of the
weak head normal form, which `HasType.whnf` gives.
-/

@[expose] public section

namespace Sic.Core

open Term

/-- A neutral term in the context `X : U_l` has only the types equal to `U_l`. -/
private theorem Neutral.typeEq_univ {t : Term k 1} (hN : Neutral t)
    (h : .empty ∙ univ l ⊢ t : C) : .empty ∙ univ l ⊢ C ≡ univ l := by
  induction hN generalizing C with
  | var => rename_i x; cases x using Fin.cases with
    | zero => exact h.inv_var
    | succ x => exact x.elim0
  | app _ ih =>
    have ⟨_, _, _, ht, _, _⟩ := h.inv_app
    have ⟨_, e, _⟩ := (ih ht).symm.inv_univ .pi
    cases e

/-- No term has the type `X` in the context `X : U_l`. -/
private theorem not_hasType_var_zero (h : .empty ∙ univ l ⊢ t : var 0) : False := by
  have ⟨w, hw⟩ := h.whnf
  have ⟨_, hw', _⟩ := hw.1.termEq.wf
  have not_univ {l'} (hC : .empty ∙ univ l ⊢ var 0 ≡ univ l') : False := by
    have ⟨_, e, _⟩ := hC.symm.inv_univ (.ne .var)
    cases e
  cases hw.2 with
  | univ => exact not_univ hw'.inv_univ
  | pi => have ⟨_, _, _, _, hC⟩ := hw'.inv_pi_univ; exact not_univ hC
  | lam =>
    have ⟨_, _, _, _, hC⟩ := hw'.inv_lam
    have ⟨_, _, e, _⟩ := hC.symm.inv_pi (.ne .var)
    cases e
  | ne hN => exact not_univ (hN.typeEq_univ hw')

-- ADE: `¬Empty`, in `Definition/Typed/Consequences/Canonicity.agda`.
-- Pujet: `zero≢one`, in `Definition/Typed/Consequences/Consistency.agda`.
/-- The type `Π^q_p (X : U_l). X` has no closed term. -/
theorem not_hasType_forall : ¬ .empty ⊢ t : pi p q (univ l) (var 0) := fun h => by
  have ⟨_, _, ht, _⟩ := h.canonical_pi
  have ⟨_, hLam, _⟩ := ht.termEq.wf
  have ⟨_, _, _, hb, hC⟩ := hLam.inv_lam
  have ⟨_, _, hA, hB⟩ := hC.pi_inj
  exact not_hasType_var_zero ((hb.conv_last hA.symm (.univ (.univ .empty))).conv hB.symm)

end Sic.Core
