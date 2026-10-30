module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# Conversion

Two reducible types that the interpretation of the first equates have the same equal terms, whatever
the levels of the logical relation that prove their reducibility.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorems of ADE, in `Definition/LogicalRelation/Properties/Conversion.agda` | Of Pujet, in `Definition/LogicalRelation/Properties/Conversion.agda` |
| --- | --- | --- |
| `LogicalRelation.conv_eqTerm` | `convEqTerm₁`, `convEqTerm₂` | `convEqTerm₁`, `convEqTerm₂` |

ADE and Pujet prove each direction in its own theorem, by a mutual induction, where an equivalence
states both.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/--
Two reducible types, at any two levels, that the interpretation of the first equates, have the same
equal terms.

Both types reduce to weak head normal forms with the same constructor, since the reduction of the
second is deterministic, and the terms move between their interpretations by the conversion of
their reductions and of their equalities.
The elements of two equal universes are interpreted by the relation at the same level, since equal
levels have the same value.
For two types of functions, the induction moves the arguments from the domain of the second to the
domain of the first, and the applications from the codomain of the first to the codomain of the
second, which is why it proves both directions at once.
-/
theorem LogicalRelation.conv_eqTerm (hA : Γ ⊩⟨l₁⟩ A ▸ P) (hB : Γ ⊩⟨l₂⟩ B ▸ Q)
    (hAB : P.eqType B) : P.eqTerm t u ↔ Q.eqTerm t u := by
  rw [LogicalRelation.unfold] at hA hB
  induction hA generalizing l₂ with
  | univ _ hA =>
    obtain ⟨L', hB', hL⟩ := hAB
    cases hB with
    | univ _ hB =>
      cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .univ⟩
      have hU := TypeEq.univ (.univ hA.typeEq.wfCon hL)
      have hb : Level.bound _ = L'.bound := hL _
      constructor
      · rintro ⟨A', B', ht, hu, hA', hB', hAB', P', hP', hQ', hP'u⟩
        exact ⟨A', B', ht.conv hU, hu.conv hU, hA', hB', EqualityRelation.conv hAB' hU, P',
          hb ▸ hP', hb ▸ hQ', hP'u⟩
      · rintro ⟨A', B', ht, hu, hA', hB', hAB', P', hP', hQ', hP'u⟩
        exact ⟨A', B', ht.conv hU.symm, hu.conv hU.symm, hA', hB',
          EqualityRelation.conv hAB' hU.symm, P', hb ▸ hP', hb ▸ hQ', hP'u⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB => nomatch TypeRedWhnf.det ⟨hB', .univ⟩ ⟨hB, .pi⟩
  | ne _ hN =>
    obtain ⟨M, hB', hM, hNM⟩ := hAB
    cases hB with
    | univ _ hB => cases TypeRedWhnf.det ⟨hB, .univ⟩ ⟨hB', .ne hM⟩; nomatch hM
    | ne hB hM' =>
      cases TypeRedWhnf.det ⟨hB', .ne hM⟩ ⟨hB, .ne hM'⟩
      have hNM := EqualityRelation.typeEq hNM
      constructor
      · rintro ⟨t', u', ht, hu, ht', hu', htu⟩
        exact ⟨t', u', ht.conv hNM, hu.conv hNM, ht', hu', EqualityRelation.convNeutral htu hNM⟩
      · rintro ⟨t', u', ht, hu, ht', hu', htu⟩
        exact ⟨t', u', ht.conv hNM.symm, hu.conv hNM.symm, ht', hu',
          EqualityRelation.convNeutral htu hNM.symm⟩
    | pi hB => cases TypeRedWhnf.det ⟨hB, .pi⟩ ⟨hB', .ne hM⟩; nomatch hM
  | pi _ _ PF PG _ _ _ ihF ihG =>
    obtain ⟨F', G', hB', hPi, hFB, hGB⟩ := hAB
    cases hB with
    | univ _ hB => nomatch TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .univ⟩
    | ne hB hN => cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .ne hN⟩; nomatch hN
    | pi hB _ PF' PG' hF' hG' =>
      cases TypeRedWhnf.det ⟨hB', .pi⟩ ⟨hB, .pi⟩
      have hPi := EqualityRelation.typeEq hPi
      have hPF : ∀ {m} {ρ : Wk m _} {Δ}, ρ ∷ Δ ⊇ _ → ⊢ Δ →
          ∀ {a b}, (PF ρ Δ).eqTerm a b ↔ (PF' ρ Δ).eqTerm a b :=
        fun hρ hΔ => ihF hρ hΔ (hF' hρ hΔ) (hFB hρ hΔ)
      have hPG : ∀ {m} {ρ : Wk m _} {Δ a}, ρ ∷ Δ ⊇ _ → ⊢ Δ → (PF ρ Δ).eqTerm a a →
          ∀ {t u}, (PG ρ Δ a).eqTerm t u ↔ (PG' ρ Δ a).eqTerm t u :=
        fun hρ hΔ ha => ihG hρ hΔ ha (hG' hρ hΔ ((hPF hρ hΔ).mp ha)) (hGB hρ hΔ ha)
      constructor
      · rintro ⟨f, g, hf, hg, hfg, happ⟩
        refine ⟨f, g, hf.conv hPi, hg.conv hPi, EqualityRelation.conv hfg hPi,
          fun hρ hΔ ha hb hab => ?_⟩
        have ha := (hPF hρ hΔ).mpr ha
        exact (hPG hρ hΔ ha).mp
          (happ hρ hΔ ha ((hPF hρ hΔ).mpr hb) ((hPF hρ hΔ).mpr hab))
      · rintro ⟨f, g, hf, hg, hfg, happ⟩
        refine ⟨f, g, hf.conv hPi.symm, hg.conv hPi.symm, EqualityRelation.conv hfg hPi.symm,
          fun hρ hΔ ha hb hab => ?_⟩
        exact (hPG hρ hΔ ha).mpr
          (happ hρ hΔ ((hPF hρ hΔ).mp ha) ((hPF hρ hΔ).mp hb) ((hPF hρ hΔ).mp hab))

end Sic.Core.Reducibility
