module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Conversion

/-!
# Symmetry

The interpretations of reducible types are symmetric: two reducible types that the interpretation of
the first equates are equated by the interpretation of the second, and two terms that the
interpretation of a type equates are equated in the other order.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Properties/Symmetry.agda` | Of Pujet, in `Definition/LogicalRelation/Properties/Symmetry.agda` |
| --- | --- | --- |
| `LogicalRelation.symm_eqType` | `symEq` | the same |
| `LogicalRelation.symm_eqTerm` | `symEqTerm` | the same |

ADE prove both theorems at each level from the theorems at the smaller levels, in their `symKit`,
while here the symmetry of the types does not use the symmetry of the terms, so that it holds at
every level before the symmetry of the terms of a universe uses it.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/--
Two reducible types, at any two levels, that the interpretation of the first equates, are equated
by the interpretation of the second.

Both types reduce to weak head normal forms with the same constructor, which are equal in the other
order.
For two types of functions, an argument of the domain of the second is an argument of the domain of
the first, by conversion, where the induction gives the symmetry of the codomains.
-/
theorem LogicalRelation.symm_eqType (hA : Γ ⊩⟨l₁⟩ A ▸ P) (hB : Γ ⊩⟨l₂⟩ B ▸ Q)
    (hAB : P.eqType B) : Q.eqType A := by
  rw [LogicalRelation.unfold] at hA hB
  induction hA generalizing l₂ with
  | univ _ hA =>
    obtain ⟨_, hB', hL⟩ := hAB
    cases hB with
    | univ _ hB => cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .univ⟩; exact ⟨_, hA, hL.symm⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB => nomatch TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .pi⟩
  | ne hA hN =>
    obtain ⟨_, hB', hM, hNM⟩ := hAB
    cases hB with
    | univ _ hB => cases TypeRedWhnf.det ⟨hB, .univ⟩ ⟨hB', .ne hM⟩; nomatch hM
    | ne hB hM' =>
      cases TypeRedWhnf.det ⟨hB', .ne hM⟩ ⟨hB, .ne hM'⟩
      exact ⟨_, hA, hN, EqualityRelation.symmType hNM⟩
    | pi hB => cases TypeRedWhnf.det ⟨hB, .pi⟩ ⟨hB', .ne hM⟩; nomatch hM
  | pi hA _ _ _ hF _ _ ihF ihG =>
    obtain ⟨_, _, hB', hPi, hFB, hGB⟩ := hAB
    cases hB with
    | univ _ hB => nomatch TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .univ⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB _ _ _ hF' hG' =>
      cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .pi⟩
      refine ⟨_, _, hA, EqualityRelation.symmType hPi,
        fun hρ hΔ => ihF hρ hΔ (hF' hρ hΔ) (hFB hρ hΔ), fun hρ hΔ ha => ?_⟩
      have ha' := (conv_eqTerm (unfold.mpr (hF hρ hΔ)) (unfold.mpr (hF' hρ hΔ)) (hFB hρ hΔ)).mpr ha
      exact ihG hρ hΔ ha' (hG' hρ hΔ ha) (hGB hρ hΔ ha')

/--
Two terms that the interpretation of a reducible type equates are equated in the other order.

Their weak head normal forms are equal in the other order.
Two types of a universe are equated by the interpretation of the second, by the symmetry of the
types at the level of the universe.
Two functions applied to two equal arguments `a` and `b` give, by the induction, the applications
to `b` and `a` in the other order, at the codomain instantiated at `b`, which conversion moves to
the codomain instantiated at `a`.
-/
theorem LogicalRelation.symm_eqTerm (hA : Γ ⊩⟨l⟩ A ▸ P) (htu : P.eqTerm t u) : P.eqTerm u t := by
  rw [LogicalRelation.unfold] at hA
  induction hA with
  | univ =>
    obtain ⟨_, _, ht, hu, hA', hB', hAB, _, hP, ⟨_, hQ⟩, hPu⟩ := htu
    exact ⟨_, _, hu, ht, hB', hA', EqualityRelation.symm hAB, _, hQ, ⟨_, hP⟩,
      LogicalRelation.symm_eqType hP hQ hPu⟩
  | ne =>
    obtain ⟨_, _, ht, hu, ht', hu', htu⟩ := htu
    exact ⟨_, _, hu, ht, hu', ht', EqualityRelation.symmNeutral htu⟩
  | pi _ _ _ _ _ hG hGext ihF ihG =>
    obtain ⟨_, _, hf, hg, hfg, happ⟩ := htu
    refine ⟨_, _, hg, hf, EqualityRelation.symm hfg, fun hρ hΔ ha hb hab => ?_⟩
    have hba := ihF hρ hΔ hab
    exact (conv_eqTerm (unfold.mpr (hG hρ hΔ hb)) (unfold.mpr (hG hρ hΔ ha))
      (hGext hρ hΔ hb ha hba)).mp (ihG hρ hΔ hb (happ hρ hΔ hb ha hba))

end Sic.Core.Reducibility
