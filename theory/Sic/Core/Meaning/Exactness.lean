module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness

/-!
# Exactness of the Meaning

The exactness of the meaning of annex 18 of RFC 36 for the proofs: a meaningful signature has
distinct names, a sort computes to itself and only to itself, and a sort is not a proposition, so
that the propositions are told apart from the types.

ADE have no propositions.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Exactness of the Proofs -/

/-- The names of a meaningful signature are distinct.
RFC: `\mathsf{distinct}_{\vDash\Sigma}` -/
theorem ValidSig.distinct {ι : Interpretation} {sig : Signature} (h : ValidSig ι sig) :
    sig.Distinct :=
  h.1

/-- A sort computes to itself. -/
theorem Computes.sort (sig : Signature) (κ : Universe 0) : Computes sig (.sort κ) (.sort κ) :=
  ⟨.refl _, .sort κ⟩

/-- A sort computes to nothing else than itself. -/
theorem Computes.sort_inv {sig : Signature} {κ : Universe 0} {v : Term 0 []} :
    Computes sig (.sort κ) v → v = .sort κ
  | ⟨.refl _, _⟩ => rfl
  | ⟨.step h _, _⟩ => nomatch h

/-- The terms that the universe of propositions `Ω_l` relates are propositions. -/
theorem HasEq.prop_isProp {sig : Signature} {ι : Interpretation} {l : Level 0} {R : TermRel}
    {v w : Term 0 []} (hR : HasEq sig ι (.sort ⟨.prop, l⟩) R) (hvw : R v w) : IsProp sig ι v := by
  cases hR with
  | univ n h =>
    cases levelRel_univ_iff.1 h with
    | prop _ hk =>
      obtain ⟨b, _, hb, -⟩ := hvw
      exact ⟨_, b, hb⟩
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop _ _ h _ =>
    cases levelRel_prop_iff.1 h with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv

/-- A sort is not a proposition. -/
theorem not_isProp_sort {sig : Signature} {ι : Interpretation} {κ : Universe 0} :
    ¬ IsProp sig ι (.sort κ) := fun ⟨_, _, h⟩ => by
  cases levelRel_prop_iff.1 h with
  | data _ _ _ _ hv => cases hv
  | codata _ _ _ _ hv => cases hv

/-- A sort does not compute to a proposition. -/
theorem not_computesToProp_sort {sig : Signature} {ι : Interpretation} {κ : Universe 0} :
    ¬ ComputesToProp sig ι (.sort κ) := fun ⟨_, hc, hp⟩ => by
  cases hc.sort_inv
  exact not_isProp_sort hp

/-- `(exact_Ω)`: two closed terms are equal proofs of a proposition exactly when each of them is a
proof of it.
RFC: `\mathsf{exact}_\Omega` -/
theorem exact_prop {sig : Signature} {ι : Interpretation} {A t u : Term 0 []} {l : Level 0}
    (hA : ValidTerm₀ sig ι A (.sort ⟨.prop, l⟩)) :
    ValidEqTerm₀ sig ι t u A ↔ ValidTerm₀ sig ι t A ∧ ValidTerm₀ sig ι u A := by
  obtain ⟨⟨hd, -⟩, hcl, -⟩ := hA
  obtain ⟨A₀, v, w, R, hc, hv, -, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  have hvp := hR.prop_isProp hvw
  have hP : ComputesToProp sig ι A := ⟨v, hv, hvp⟩
  constructor
  · rintro ⟨hTA, -, hcl'⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htu⟩ := hcl' hP
    have hper := hR₁.isPer hd
    exact ⟨⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans htu (hper.symm htu)⟩⟩,
      ⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans (hper.symm htu) htu⟩⟩⟩
  · rintro ⟨⟨hTA, -, hclt⟩, -⟩
    refine ⟨hTA, fun h => absurd hP h, fun _ => ?_⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htt⟩ := hclt hP
    cases Computesι.det hd hA₁ hv
    obtain ⟨k, b, hb⟩ := hvp
    have hRb : ∀ t u, R₁ t u ↔ b := fun t u => hR₁.unique hd (.prop k b hb fun _ _ => .rfl) t u
    exact ⟨v, R₁, hA₁, hR₁, (hRb t u).2 ((hRb t t).1 htt)⟩

end Sic.Core
