module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.Reducibility.Uniqueness

/-!
# Weakening

A reducible type stays reducible, at the same level, in every well-formed context that contains its
own, and the types and the terms that its interpretation equates stay equated by the interpretation
of the weakened type, whatever the proof of its reducibility.

## Correspondence with the Formalizations of ADE and of Pujet

ADE and Pujet state the transports for the proof of reducibility that their weakening builds, while
the transports here hold for every proof of the reducibility of the weakened type, at any level, by
the uniqueness of its interpretation.
A reducible term is a term that the interpretation equates to itself, so that the transport of the
equal terms also covers their `wkTerm`.
-/

@[expose] public section

namespace Sic.Core.Reducibility

open Term

variable [EqualityRelation]

/-!
The proof builds the weakened proof of reducibility and transports the equalities of its
interpretation at once, so that both read the same interpretation.
The domain and the codomain of a type of functions are reducible in every context that contains its
own, so that their weakening only composes the weakenings, while the elements of a universe are
weakened at the level of the universe, smaller, which the recursion on the level allows.
-/

private theorem LogicalRelation.wkStrong (h : Γ ⊩⟨l⟩ A ▸ P) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    ∃ Q, (Δ ⊩⟨l⟩ A.wk ρ ▸ Q) ∧ (∀ {B}, P.eqType B → Q.eqType (B.wk ρ)) ∧
      ∀ {t u}, P.eqTerm t u → Q.eqTerm (t.wk ρ) (u.wk ρ) := by
  rw [LogicalRelation.unfold] at h
  cases h with
  | univ hL hA =>
    refine ⟨_, unfold.mpr (.univ hL (hA.wk hρ hΔ)), ?_, ?_⟩
    · rintro _ ⟨_, hB, hLL⟩
      exact ⟨_, hB.wk hρ hΔ, hLL⟩
    · rintro _ _ ⟨_, _, ht, hu, hA', hB', hAB, _, hP, ⟨_, hQ⟩, hPu⟩
      obtain ⟨_, hP', hPT, _⟩ := wkStrong hP hρ hΔ
      obtain ⟨_, hQ', _⟩ := wkStrong hQ hρ hΔ
      exact ⟨_, _, ht.wk hρ hΔ, hu.wk hρ hΔ, hA'.wk ρ, hB'.wk ρ,
        EqualityRelation.wk hAB hρ hΔ, _, hP', ⟨_, hQ'⟩, hPT hPu⟩
  | ne hA hN hNN =>
    refine ⟨_, unfold.mpr (.ne (hA.wk hρ hΔ) (hN.wk ρ) (EqualityRelation.wkType hNN hρ hΔ)), ?_, ?_⟩
    · rintro _ ⟨_, hB, hM, hNM⟩
      exact ⟨_, hB.wk hρ hΔ, hM.wk ρ, EqualityRelation.wkType hNM hρ hΔ⟩
    · rintro _ _ ⟨_, _, ht, hu, ht', hu', htu⟩
      exact ⟨_, _, ht.wk hρ hΔ, hu.wk hρ hΔ, ht'.wk ρ, hu'.wk ρ,
        EqualityRelation.wkNeutral htu hρ hΔ⟩
  | pi hA hPi PF PG hF hG hGext =>
    refine ⟨_, unfold.mpr (.pi (hA.wk hρ hΔ) (EqualityRelation.wkType hPi hρ hΔ)
      (fun ρ' Δ' => PF (ρ'.comp ρ) Δ') (fun ρ' Δ' => PG (ρ'.comp ρ) Δ')
      (fun hρ' hΔ' => by rw [wk_comp]; exact hF (hρ'.comp hρ) hΔ')
      (fun hρ' hΔ' ha => by rw [wk_comp]; exact hG (hρ'.comp hρ) hΔ' ha)
      (fun hρ' hΔ' ha hb hab => by rw [wk_comp]; exact hGext (hρ'.comp hρ) hΔ' ha hb hab)),
      ?_, ?_⟩
    · rintro _ ⟨_, _, hB, hPiB, hFB, hGB⟩
      exact ⟨_, _, hB.wk hρ hΔ, EqualityRelation.wkType hPiB hρ hΔ,
        fun hρ' hΔ' => by rw [wk_comp]; exact hFB (hρ'.comp hρ) hΔ',
        fun hρ' hΔ' ha => by rw [wk_comp]; exact hGB (hρ'.comp hρ) hΔ' ha⟩
    · rintro _ _ ⟨_, _, hf, hg, hfg, happ⟩
      exact ⟨_, _, hf.wk hρ hΔ, hg.wk hρ hΔ, EqualityRelation.wk hfg hρ hΔ,
        fun hρ' hΔ' ha hb hab => by
          rw [wk_comp, wk_comp]; exact happ (hρ'.comp hρ) hΔ' ha hb hab⟩
termination_by l

-- ADE: `wk`, in `Definition/LogicalRelation/Weakening.agda`.
-- Pujet: `wk`, in `Definition/LogicalRelation/Weakening.agda`.
/--
A reducible type stays reducible, at the same level, in every well-formed context that contains its
own.
-/
theorem LogicalRelation.wk (h : Γ ⊩⟨l⟩ A ▸ P) (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) :
    ∃ Q, Δ ⊩⟨l⟩ A.wk ρ ▸ Q :=
  let ⟨Q, hQ, _⟩ := h.wkStrong hρ hΔ
  ⟨Q, hQ⟩

-- ADE: `wkEq`, in `Definition/LogicalRelation/Weakening.agda`.
-- Pujet: `wkEq`, in `Definition/LogicalRelation/Weakening.agda`.
/--
A type that the interpretation of a reducible type equates to it, weakened, is equated to the
weakened type by its interpretation, whatever the proof of its reducibility.
-/
theorem LogicalRelation.wk_eqType (h : Γ ⊩⟨l⟩ A ▸ P) (h' : Δ ⊩⟨l'⟩ A.wk ρ ▸ Q)
    (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) (hB : P.eqType B) : Q.eqType (B.wk ρ) :=
  let ⟨_, hQ, hT, _⟩ := h.wkStrong hρ hΔ
  h'.unique hQ ▸ hT hB

-- ADE: `wkTerm` and `wkEqTerm`, in `Definition/LogicalRelation/Weakening.agda`.
-- Pujet: `wkTerm` and `wkEqTerm`, in `Definition/LogicalRelation/Weakening.agda`.
/--
Two terms that the interpretation of a reducible type equates, weakened, are equated by the
interpretation of the weakened type, whatever the proof of its reducibility.
-/
theorem LogicalRelation.wk_eqTerm (h : Γ ⊩⟨l⟩ A ▸ P) (h' : Δ ⊩⟨l'⟩ A.wk ρ ▸ Q)
    (hρ : ρ ∷ Δ ⊇ Γ) (hΔ : ⊢ Δ) (htu : P.eqTerm t u) : Q.eqTerm (t.wk ρ) (u.wk ρ) :=
  let ⟨_, hQ, _, hT⟩ := h.wkStrong hρ hΔ
  h'.unique hQ ▸ hT htu

end Sic.Core.Reducibility
