module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.WellFormed

/-!
# Neutral Terms

The interpretation of a reducible type equates two neutral terms that the equality of neutral terms
equates at that type, so that a neutral term equal to itself, such as a variable, is reducible.

## Correspondence with the Formalizations of ADE and of Pujet

A reducible term is a term that the interpretation equates to itself, so that the theorem also
covers their `neuTerm`.
Their `neu` and `neuEq`, which make the neutral types reducible, are not here, since no proof uses
them yet: the proof here builds the neutral types of a universe with `LogRel.ne`.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open EqualityRelation

variable [EqualityRelation]

-- ADE: `neuTerm` and `neuEqTerm`, in `Definition/LogicalRelation/Properties/Neutral.agda`.
-- Pujet: `neuTerm` and `neuEqTerm`, in `Definition/LogicalRelation/Properties/Neutral.agda`.
/--
The interpretation of a reducible type equates two neutral terms that the equality of neutral terms
equates at that type.

Two neutral terms are weak head normal forms, which reduce to themselves.
Two neutral terms of a universe are also neutral types, reducible at the level of the universe,
which their equality equates.
Two neutral functions applied to two equal arguments are neutral terms equal by the congruence of
the application, which the induction equates.
-/
theorem LogicalRelation.neutral_eqTerm (h : Γ ⊩⟨l⟩ A ▸ P) (ht : Neutral t) (hu : Neutral u)
    (htu : Γ ⊢ t ~ u : A) : P.eqTerm t u := by
  rw [LogicalRelation.unfold] at h
  induction h with
  | univ _ hA =>
    have htu := convNeutral htu hA.typeEq
    have ⟨ht', hu', _⟩ := (termEq (ofNeutral htu)).wf
    exact ⟨_, _, ⟨.refl ht', .ne ht⟩, ⟨.refl hu', .ne hu⟩, .ne ht, .ne hu, ofNeutral htu, _,
      unfold.mpr (.ne (.refl (.univ ht')) ht
        (ofUniv (ofNeutral (transNeutral htu (symmNeutral htu))))),
      ⟨_, unfold.mpr (.ne (.refl (.univ hu')) hu
        (ofUniv (ofNeutral (transNeutral (symmNeutral htu) htu))))⟩,
      _, .refl (.univ hu'), hu, ofUniv (ofNeutral htu)⟩
  | ne hA =>
    have htu := convNeutral htu hA.typeEq
    have ⟨ht', hu', _⟩ := (termEq (ofNeutral htu)).wf
    exact ⟨_, _, .refl ht', .refl hu', ht, hu, htu⟩
  | pi hA _ _ _ hF _ _ _ ihG =>
    have htu := convNeutral htu hA.typeEq
    have ⟨ht', hu', _⟩ := (termEq (ofNeutral htu)).wf
    exact ⟨_, _, ⟨.refl ht', .ne ht⟩, ⟨.refl hu', .ne hu⟩, ofNeutral htu,
      fun hρ hΔ ha _ hab => ihG hρ hΔ ha (.app (ht.wk _)) (.app (hu.wk _))
        (app (wkNeutral htu hρ hΔ) ((hF hρ hΔ).escape_eq hab))⟩

end Sic.Core.Reducibility
