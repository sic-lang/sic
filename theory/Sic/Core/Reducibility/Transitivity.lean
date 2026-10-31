module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Conversion

/-!
# Transitivity

The interpretations of reducible types are transitive: a type that the interpretation of a reducible
type `B` equates to `B` is equated to every reducible type whose interpretation equates it to `B`,
and the interpretation of a type equates two terms that it equates to the same term.

## Correspondence with the Formalizations of ADE and of Pujet

ADE and Pujet also take a proof that the third type is reducible, which the proof here does not
use.
ADE prove both theorems at each level from the theorems at the smaller levels, in their `transKit`,
while here the transitivity of the types does not use the transitivity of the terms, so that it
holds at every level before the transitivity of the terms of a universe uses it.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

-- ADE: `transEq`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
-- Pujet: `transEq`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
/--
A type `C` that the interpretation of a reducible type `B` equates to `B` is equated to every
reducible type `A`, at any level, whose interpretation equates it to `B`.

The three types reduce to weak head normal forms with the same constructor, since the reduction of
`B` is deterministic, which are equal by transitivity.
For three types of functions, an argument of the domain of `A` is an argument of the domain of `B`,
by conversion, where the induction gives the transitivity of the codomains.
-/
theorem LogicalRelation.trans_eqType (hA : Γ ⊩⟨l₁⟩ A ▸ P) (hB : Γ ⊩⟨l₂⟩ B ▸ Q)
    (hAB : P.eqType B) (hBC : Q.eqType C) : P.eqType C := by
  rw [LogicalRelation.unfold] at hA hB
  induction hA generalizing l₂ with
  | univ _ hA =>
    obtain ⟨_, hB', hL⟩ := hAB
    cases hB with
    | univ _ hB =>
      cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .univ⟩
      obtain ⟨_, hC, hL'⟩ := hBC
      exact ⟨_, hC, hL.trans hL'⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB => nomatch TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .pi⟩
  | ne hA hN =>
    obtain ⟨_, hB', hM, hNM⟩ := hAB
    cases hB with
    | univ _ hB => cases TypeRedWhnf.det ⟨hB, .univ⟩ ⟨hB', .ne hM⟩; nomatch hM
    | ne hB hM' =>
      cases TypeRedWhnf.det ⟨hB', .ne hM⟩ ⟨hB, .ne hM'⟩
      obtain ⟨_, hC, hM'', hMM'⟩ := hBC
      exact ⟨_, hC, hM'', EqualityRelation.transType hNM hMM'⟩
    | pi hB => cases TypeRedWhnf.det ⟨hB, .pi⟩ ⟨hB', .ne hM⟩; nomatch hM
  | pi hA _ _ _ hF _ _ ihF ihG =>
    obtain ⟨_, _, hB', hPi, hFB, hGB⟩ := hAB
    cases hB with
    | univ _ hB => nomatch TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .univ⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB _ _ _ hF' hG' =>
      cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .pi⟩
      obtain ⟨_, _, hC, hPi', hFC, hGC⟩ := hBC
      refine ⟨_, _, hC, EqualityRelation.transType hPi hPi',
        fun hρ hΔ => ihF hρ hΔ (hF' hρ hΔ) (hFB hρ hΔ) (hFC hρ hΔ), fun hρ hΔ ha => ?_⟩
      have ha' := (conv_eqTerm (unfold.mpr (hF hρ hΔ)) (unfold.mpr (hF' hρ hΔ)) (hFB hρ hΔ)).mp ha
      exact ihG hρ hΔ ha (hG' hρ hΔ ha') (hGB hρ hΔ ha) (hGC hρ hΔ ha')

-- ADE: `transEqTerm`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
-- Pujet: `transEqTerm`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
/--
The interpretation of a reducible type equates two terms that it equates to the same term.

The weak head normal forms of the common term are the same, since its reduction is deterministic,
so that the weak head normal forms of the two terms are equal by transitivity.
Two types of a universe are equated by the transitivity of the types at the level of the universe.
Two functions applied to two equal arguments `a` and `b` give, by the induction, the application of
the first to `a` and of the third to `b`, since the common function applied to `a` is equal to both.
-/
theorem LogicalRelation.trans_eqTerm (hA : Γ ⊩⟨l⟩ A ▸ P) (htu : P.eqTerm t u)
    (huv : P.eqTerm u v) : P.eqTerm t v := by
  rw [LogicalRelation.unfold] at hA
  induction hA with
  | univ =>
    obtain ⟨_, _, ht, hu, hA', _, hAB, _, hP, _, hPu⟩ := htu
    obtain ⟨_, _, hu', hv, _, hC', hBC, _, hQ, hR, hQv⟩ := huv
    cases TermRedWhnf.det hu hu'
    exact ⟨_, _, ht, hv, hA', hC', EqualityRelation.trans hAB hBC, _, hP, hR,
      LogicalRelation.trans_eqType hP hQ hPu hQv⟩
  | ne =>
    obtain ⟨_, _, ht, hu, ht', hu', htu⟩ := htu
    obtain ⟨_, _, hu₂, hv, hu₂', hv', huv⟩ := huv
    cases TermRedWhnf.det ⟨hu, .ne hu'⟩ ⟨hu₂, .ne hu₂'⟩
    exact ⟨_, _, ht, hv, ht', hv', EqualityRelation.transNeutral htu huv⟩
  | pi _ _ _ _ _ _ _ _ ihG =>
    obtain ⟨_, _, hf, hg, hfg, happ⟩ := htu
    obtain ⟨_, _, hg', hh, hgh, happ'⟩ := huv
    cases TermRedWhnf.det hg hg'
    exact ⟨_, _, hf, hh, EqualityRelation.trans hfg hgh, fun hρ hΔ ha hb hab =>
      ihG hρ hΔ ha (happ hρ hΔ ha ha ha) (happ' hρ hΔ ha hb hab)⟩

end Sic.Core.Reducibility
