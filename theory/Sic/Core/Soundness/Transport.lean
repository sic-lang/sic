module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution

/-!
# Soundness of the Rules of the Transport

The rules `(transp)`, `(transp_≡)` and `(transp_same)` of annex 15 of RFC 36 keep the meaning of
annex 21, as `Rules` proves it of the other rules.
A transport reduces to its term by `(transp_⟶)`, whatever its motive, so that the meaning sees only
the term: at two equal closed substitutions, the proof makes the equality of the two terms of the
transport true, which `(ty_∼)` makes their equality as terms of their type, so that the motive gives
equal types at them, and the term, a term of the motive at the first, is one of the motive at the
second.

ADE transport by their eliminator `J`, whose motive also binds the proof, and which computes only
on the reflexivity, in `Definition/LogicalRelation/Substitution/Introductions/Identity.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

-- ADE: none.
/-- A proof of the equality of two terms of a type of a sort makes them, at a closed substitution,
equal terms of the type: the equality is a proposition, by `(∼)`, whose closed terms are equal
proofs only when it is true, and `(ty_∼)` makes its truth the equality of the terms. -/
theorem ValidTermΓ.equality_eq {Γ : Scope} {ctx : Context 0 Γ} {s : Quality} {l : Level 0}
    {A t₁ t₂ t : Term 0 Γ} (hA : ValidTermΓ sig ι ctx A (.sort ⟨s, l⟩))
    (ht₁ : ValidTermΓ sig ι ctx t₁ A) (ht₂ : ValidTermΓ sig ι ctx t₂ A)
    (ht : ValidTermΓ sig ι ctx t (.equality s l A t₁ t₂)) {σ : Subst 0 [] Γ}
    (hσ : EqSubst sig ι ctx σ σ) : ValidEqTerm₀ sig ι (t₁.subst σ) (t₂.subst σ) (A.subst σ) := by
  have hd := hA.1.1.distinct
  -- The equality computes to itself, a proposition whose truth is `b`.
  obtain ⟨-, hcl, -⟩ := (ValidEqTermΓ.equality hA ht₁ ht₂ (Level.equivalence.refl l)).2 σ σ hσ
  obtain ⟨A₀, v, w, R, hc, hv, -, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  obtain ⟨n, b, hb⟩ := hR.prop_isProp hvw
  cases Computesι.det hd hv ⟨.refl _, .equality ..⟩
  -- The proof is a proof of it, so that it is true.
  obtain ⟨v', R', hv', hR', htt⟩ := (ht.2 σ σ hσ).2.2 ⟨_, hv, n, b, hb⟩
  cases Computesι.det hd hv' hv
  have htrue : b := (hR'.unique hd (.prop n b hb fun _ _ => .rfl) _ _).1 htt
  exact ⟨(ht₁.2 σ σ hσ).1, (levelRel_prop_equality hd hb).1 htrue⟩

-- ADE: `J-congᵛ` and `Jᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/Identity.agda`.
/-- `(transp_≡)` keeps the meaning, and `(transp)` with it: at two equal substitutions, the two
transports step to their terms, by `(transp_⟶)`, which are equal terms of the motive at the first of
the two terms of the equality; the proof makes these two terms equal, so that the motive gives equal
types at them, at the first substitution, and the terms are equal terms of the motive at the
second. -/
theorem ValidEqTermΓ.transp {Γ : Scope} {ctx : Context 0 Γ} {s : Quality} {l : Level 0}
    {κ : Universe 0} {A A' t₁ t₁' t₂ t₂' t t' u u' : Term 0 Γ} {C C' : Term 0 (.var :: Γ)}
    (hA : ValidEqTermΓ sig ι ctx A A' (.sort ⟨s, l⟩)) (ht₁ : ValidEqTermΓ sig ι ctx t₁ t₁' A)
    (ht₂ : ValidEqTermΓ sig ι ctx t₂ t₂' A) (hC : ValidEqTermΓ sig ι (ctx.var A) C C' (.sort κ))
    (ht : ValidEqTermΓ sig ι ctx t t' (.equality s l A t₁ t₂))
    (hu : ValidEqTermΓ sig ι ctx u u' (C.subst₀ (Subst₀.single t₁))) :
    ValidEqTermΓ sig ι ctx (.transp A t₁ t₂ C t u) (.transp A' t₁' t₂' C' t' u')
      (C.subst₀ (Subst₀.single t₂)) := by
  have hctx := hA.1.1
  have hd := hctx.distinct
  have hCv : ValidTermΓ sig ι (ctx.var A) C (.sort κ) := hC.trans hC.symm
  have ht₂v : ValidTermΓ sig ι ctx t₂ A := ht₂.trans ht₂.symm
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
      Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
    exact hCv.motive hσ (ht₂v.2 σ₁ σ₂ hσ)
  have hσ₁ := hσ.left hctx
  have h₁₂ := ValidTermΓ.equality_eq (hA.trans hA.symm) (ht₁.trans ht₁.symm) ht₂v
    (ht.trans ht.symm) hσ₁
  have hu' := hu.2 σ₁ σ₂ hσ
  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _)] at hu' ⊢
  refine (ValidEqTerm₀.red_iff hd .transp).2 ?_
  exact ((ValidEqTerm₀.red_iff hd .transp).2 (hu'.conv (hCv.motive hσ₁ h₁₂)).symm).symm

-- ADE: none.
/-- `(transp_same)` keeps the meaning: the term is a term of the motive at the second of the two
terms of the equality, since the two instances of the motive are equal types, and at two equal
substitutions the transport steps to it, by `(transp_⟶)`.
The proof of the equality, the type and the motive play no part: the meaning removes the transport
whatever they are. -/
theorem ValidEqTermΓ.transpSame {Γ : Scope} {ctx : Context 0 Γ} {κ : Universe 0}
    {A t₁ t₂ t u : Term 0 Γ} {C : Term 0 (.var :: Γ)}
    (hu : ValidTermΓ sig ι ctx u (C.subst₀ (Subst₀.single t₁)))
    (hCC : ValidEqTermΓ sig ι ctx (C.subst₀ (Subst₀.single t₁)) (C.subst₀ (Subst₀.single t₂))
      (.sort κ)) :
    ValidEqTermΓ sig ι ctx (.transp A t₁ t₂ C t u) u (C.subst₀ (Subst₀.single t₂)) := by
  have hCT :
      ValidEqTypeΓ sig ι ctx (C.subst₀ (Subst₀.single t₁)) (C.subst₀ (Subst₀.single t₂)) := by
    obtain ⟨q, l⟩ := κ
    cases q
    · exact hCC.univType
    · exact hCC.propType
  have hu₂ := hu.conv hCT
  exact ⟨hu₂.1, fun σ₁ σ₂ hσ => (ValidEqTerm₀.red_iff hu.1.1.distinct .transp).2 (hu₂.2 σ₁ σ₂ hσ)⟩

end

end Sic.Core
