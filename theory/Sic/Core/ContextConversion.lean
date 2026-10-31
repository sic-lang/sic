module

public import Sic.Core.TypedSubstitution
import Sic.Core.WellFormed

/-!
# Context Conversion

The judgments of `Sic.Core.Typing` in a context whose declarations get equal types, as the section
Admissible Properties of RFC 24 states: a judgment still holds when the type of any declaration of
its context is replaced by an equal type.
Each variable replaced by itself is then a substitution from the new context to the old one, which
converts the type of each variable, so that the substitution of the judgments moves them to the new
context.

## Correspondence with the Formalization of ADE

`HasType.conv_last`, of `Sic.Core.TypedSubstitution`, is the case of the last declaration, which
`Sic.Core.WellFormed` uses before this module, and which the proof here uses at each declaration.
-/

@[expose] public section

namespace Sic.Core

open Term

set_option hygiene false in
/-- `⊢ Γ ≡ Δ`: the contexts `Γ` and `Δ` declare equal types, each in the declarations before it. -/
notation:40 "⊢ " Γ:41 " ≡ " Δ:41 => ConEq Γ Δ

-- ADE: `_»⊢_≡_`, in `Definition/Typed/Stability/Primitive.agda`.
/-- `⊢ Γ ≡ Δ`: the contexts `Γ` and `Δ` declare equal types, each in the declarations before it. -/
inductive ConEq {k : Nat} : {n : Nat} → Con k n → Con k n → Prop where
  /-- The empty contexts are equal. -/
  | empty : ⊢ .empty ≡ .empty
  /-- Two equal contexts extended by equal types are equal. -/
  | snoc : ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Δ ∙ B

-- ADE: `contextConvSubst`, in `Definition/Typed/Stability.agda`.
/--
The second of two equal contexts is well formed, and each variable replaced by itself is a
substitution from it to the first, by induction on the declarations: the type of the last
declaration is equal in the second context, by the substitution of the declarations before it, and
converts the type of its variable.
-/
theorem ConEq.substWf : ⊢ Γ ≡ Δ → (⊢ Δ) ∧ Δ ⊢ˢ var : Γ
  | .empty => ⟨.empty, fun x => x.elim0⟩
  | .snoc hΓΔ hAB => by
    have ⟨hΔ, hσ⟩ := hΓΔ.substWf
    -- The two types of the last declaration are equal in the second context.
    have hAB' := hAB.subst hσ hΔ
    rw [subst_var, subst_var] at hAB'
    have ⟨hA, hB⟩ := hAB'.wf
    -- The variables of the second context extended by the first type, converted to the second.
    have hσ' := hσ.lift (by rw [subst_var]; exact .snoc hA)
    rw [Subst.lift_var, subst_var] at hσ'
    exact ⟨.snoc hB, fun x => (hσ' x).conv_last hAB' hB⟩

-- ADE: `stability-⊢`, in `Definition/Typed/Stability/Primitive.agda`.
/-- A type stays a type in an equal context. -/
theorem IsType.conv_con (h : Γ ⊢ A) (hΓΔ : ⊢ Γ ≡ Δ) : Δ ⊢ A := by
  have ⟨hΔ, hσ⟩ := hΓΔ.substWf
  have := h.subst hσ hΔ
  rwa [subst_var] at this

-- ADE: `stability-⊢≡`, in `Definition/Typed/Stability/Primitive.agda`.
/-- Two equal types stay equal in an equal context. -/
theorem TypeEq.conv_con (h : Γ ⊢ A ≡ B) (hΓΔ : ⊢ Γ ≡ Δ) : Δ ⊢ A ≡ B := by
  have ⟨hΔ, hσ⟩ := hΓΔ.substWf
  have := h.subst hσ hΔ
  rwa [subst_var, subst_var] at this

-- ADE: `stability-⊢∷`, in `Definition/Typed/Stability/Primitive.agda`.
/-- A term keeps its type in an equal context. -/
theorem HasType.conv_con (h : Γ ⊢ t : A) (hΓΔ : ⊢ Γ ≡ Δ) : Δ ⊢ t : A := by
  have ⟨hΔ, hσ⟩ := hΓΔ.substWf
  have := h.subst hσ hΔ
  rwa [subst_var, subst_var] at this

-- ADE: `stability-⊢≡∷`, in `Definition/Typed/Stability/Primitive.agda`.
/-- Two equal terms stay equal in an equal context. -/
theorem TermEq.conv_con (h : Γ ⊢ t ≡ u : A) (hΓΔ : ⊢ Γ ≡ Δ) : Δ ⊢ t ≡ u : A := by
  have ⟨hΔ, hσ⟩ := hΓΔ.substWf
  have := h.subst hσ hΔ
  rwa [subst_var, subst_var, subst_var] at this

end Sic.Core
