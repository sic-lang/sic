module

public import SicTest.TypeVariable.Reducibility.Introductions.Variable
import Sic.Core.Reducibility.Introductions.Pi
import Sic.Core.Reducibility.Introductions.Universe
import Sic.Core.Reducibility.Introductions.Variable
import SicTest.TypeVariable.Reducibility.LogicalRelation
import SicTest.TypeVariable.Reducibility.Validity

/-!
# A Type Variable: Validity of the Types of Functions

The type of functions `Π^p_q (x : A). A` of the context `A : U_l` is a valid term of `U_{l ⊔ l}`,
and only equal to the types of functions of the same grades: the validity equates it neither to `A`
nor to `Π^𝟘_q (x : A). A` when `p` is `𝟙`, for every equality relation.
-/

@[expose] public section

namespace SicTest.TypeVariable.Reducibility.Introductions.Pi

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility
open SicTest.TypeVariable.Reducibility.LogicalRelation SicTest.TypeVariable.Reducibility.Validity
open SicTest.TypeVariable.Reducibility.Introductions.Variable

variable [EqualityRelation]

/--
The type of functions `Π^p_q (x : A). A` is a valid term of `U_{l ⊔ l}`, at the level `1`: its
domain `A` is a valid term of `U_l`, and so is its codomain, `A` weakened, in the context
`A : U_l, x : A`.
-/
theorem validTermEq_piAA :
    ΓA ⊩ᵛ⟨1⟩ pi p q (var 0) (var 1) ≡ pi p q (var 0) (var 1) : univ (.var 0 ⊔ .var 0) := by
  have hΓAx : ⊩ᵛ ΓA ∙ var 0 := by
    rw [ValidCon.unfold_snoc]
    exact ⟨0, validTypeEq_A⟩
  have ⟨_, hA⟩ := ValidTermEq.var validCon_ΓA 0
  have ⟨_, hA'⟩ := ValidTermEq.var hΓAx 1
  exact ValidTermEq.pi (L₁ := .var 0) (L₂ := .var 0) hA hA'

/--
The type of functions `Π^p_q (x : A). A` reduces to itself, which is not the neutral type `A` that
an equal type must reduce to, so that the validity does not equate them.
-/
example : ¬ ΓA ⊩ᵛ⟨l⟩ pi p q (var 0) (var 1) ≡ var 0 := by
  intro h
  have ⟨_, _, hPi, _, hPiA⟩ := h.reducible
  have hA : ΓA ⊢ var 0 := .univ (.var wfCon_ΓA)
  have hPi' := validTermEq_piAA (p := p) (q := q) |>.toTypeEq
  have ⟨_, _, hPi'', _⟩ := hPi'.reducible
  rw [LogicalRelation.unfold] at hPi hPi''
  cases hPi with
  | pi =>
    have ⟨_, _, hB, _⟩ := hPiA
    nomatch TypeRedWhnf.det ⟨hB, .pi⟩ ⟨.refl hA, .ne .var⟩
  | univ _ hU => nomatch TypeRedWhnf.det ⟨hU, .univ⟩ ⟨.refl hPi''.escape, .pi⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hPi''.escape, .pi⟩; nomatch hN'

/--
The types of functions `Π^𝟙_q (x : A). A` and `Π^𝟘_q (x : A). A` differ in the grade of their
argument, which the interpretation of an equal type keeps, so that the validity does not equate
them.
-/
example : ¬ ΓA ⊩ᵛ⟨l⟩ pi 𝟙 q (var 0) (var 1) ≡ pi 𝟘 q (var 0) (var 1) := by
  intro h
  have ⟨_, _, hPi₁, _, hPi₁₂⟩ := h.reducible
  have ⟨_, _, hPi₁', hPi₂, _⟩ := (validTermEq_piAA (p := 𝟙) (q := q)).toTypeEq.reducible
  have ⟨_, _, hPi₂', _⟩ := (validTermEq_piAA (p := 𝟘) (q := q)).toTypeEq.reducible
  rw [LogicalRelation.unfold] at hPi₁ hPi₁' hPi₂'
  cases hPi₁ with
  | pi hA =>
    have ⟨_, _, hB, _⟩ := hPi₁₂
    injection TypeRedWhnf.det ⟨hA, .pi⟩ ⟨.refl hPi₁'.escape, .pi⟩ with _ hp₁
    injection TypeRedWhnf.det ⟨hB, .pi⟩ ⟨.refl hPi₂'.escape, .pi⟩ with _ hp₂
    exact absurd (hp₁.symm.trans hp₂) (by decide)
  | univ _ hU => nomatch TypeRedWhnf.det ⟨hU, .univ⟩ ⟨.refl hPi₁'.escape, .pi⟩
  | ne hN hN' => cases TypeRedWhnf.det ⟨hN, .ne hN'⟩ ⟨.refl hPi₁'.escape, .pi⟩; nomatch hN'

end SicTest.TypeVariable.Reducibility.Introductions.Pi
