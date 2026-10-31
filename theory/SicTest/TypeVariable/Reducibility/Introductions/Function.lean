module

import Sic.Core.Reducibility.Introductions.Function
import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable
import Sic.Core.Reducibility.Uniqueness
import all SicTest.TypeVariable.Reducibility.LogicalRelation
import all SicTest.TypeVariable.Reducibility.Validity

/-!
# A Type Variable: Validity of the Functions

The identity of the types of `U_l`, `λ_p (X : U_l). X`, applied to the type variable `A` of the
context `A : U_l`, is validly equal to `A`, by `(β)`, so that the validity equates the type
`(λ_p (X : U_l). X) ∘_p A` to `A` and not to the type of functions `Π^p'_q' (x : A). A`, for every
equality relation.
-/

namespace SicTest.TypeVariable.Reducibility.Introductions.Function

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility
open SicTest.TypeVariable.Reducibility.LogicalRelation SicTest.TypeVariable.Reducibility.Validity

variable [EqualityRelation]

/-- `(λ_p (X : U_l). X) ∘_p A`, the identity of the types of `U_l` applied to `A`. -/
def idA (p : Sic.Grade) : Term 1 1 := app p (lam p (univ (.var 0)) (var 0)) (var 0)

/--
`(λ_p (X : U_l). X) ∘_p A` is validly equal to `A` as a term of `U_l`, at the level `1` of the type
of functions `Π^p_𝟘 (X : U_l). U_l` of the identity, by `(β)`: the body `X` is a valid term of
`U_l` in the context `A : U_l, X : U_l`, and the argument `A` a valid term of `U_l`.
-/
theorem validTermEq_idA : ΓA ⊩ᵛ⟨1⟩ idA p ≡ var 0 : univ (.var 0) := by
  have hU := ValidTermEq.univ validCon_ΓA (.refl (.var 0))
  have hΓAX : ⊩ᵛ ΓA ∙ univ (.var 0) := by
    rw [ValidCon.unfold_snoc]
    exact ⟨_, hU.toTypeEq⟩
  have hPi := (ValidTermEq.pi (p := p) (q := 𝟘) hU (ValidTermEq.univ hΓAX (.refl (.var 0)))).toTypeEq
  have ⟨_, hX⟩ := ValidTermEq.var hΓAX 0
  have ⟨_, hA⟩ := ValidTermEq.var validCon_ΓA 0
  exact ValidTermEq.beta hPi hX hA

/-- `(λ_p (X : U_l). X) ∘_p A` is a valid type, equal to `A`, at the level `0` of `A`. -/
example : ΓA ⊩ᵛ⟨0⟩ idA p ≡ var 0 :=
  ValidTermEq.toTypeEq (L := .var 0) validTermEq_idA

/--
`(λ_p (X : U_l). X) ∘_p A` is equal to the neutral type `A`, so that its interpretation is the one
of a neutral type, which does not equate it to the type of functions `Π^p'_q' (x : A). A`, since
that type reduces to itself, which is not neutral: the interpretation of the application, whatever
it is, rules out every case.
-/
theorem not_validTypeEq_idA_pi : ¬ ΓA ⊩ᵛ⟨l⟩ idA p ≡ pi p' q' (var 0) (var 1) := by
  intro h
  have ⟨_, _, hI, hPi, hIPi⟩ := h.reducible
  have ⟨_, _, hI', _, hIA⟩ :=
    (ValidTermEq.toTypeEq (L := .var 0) (validTermEq_idA (p := p))).reducible
  rw [hI'.unique hI] at hIA
  have hA : ΓA ⊢ var 0 := .univ (.var wfCon_ΓA)
  rw [LogicalRelation.unfold] at hI
  cases hI with
  | univ =>
    have ⟨_, hB, _⟩ := hIA
    nomatch TypeRedWhnf.det ⟨hB, .univ⟩ ⟨.refl hA, .ne .var⟩
  | ne =>
    have ⟨_, hB, hM, _⟩ := hIPi
    cases TypeRedWhnf.det ⟨hB, .ne hM⟩ ⟨.refl hPi.escape, .pi⟩
    nomatch hM
  | pi =>
    have ⟨_, _, hB, _⟩ := hIA
    nomatch TypeRedWhnf.det ⟨hB, .pi⟩ ⟨.refl hA, .ne .var⟩

end SicTest.TypeVariable.Reducibility.Introductions.Function
