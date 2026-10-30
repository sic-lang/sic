module

import Sic.Core.TypedSubstitution
import all Sic.Core.Typing.Validation

/-!
# Validation of the Typed Substitution

The weakening and the substitutions of `Sic.Core.TypedSubstitution` checked against the
formalization of ADE, on the constant function of RFC 24, and on the combinators `K` and `S`.

| Definition or theorem | Definition or theorem of ADE |
| --- | --- |
| `WkCon` | `_∷_⊇_`, in `Definition/Typed/Weakening.agda` |
| `SubstWf`, with `⊢ Δ` | `_⊢ˢʷ_∷_`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |
| `HasType.wk`, `TermEq.wk` | `wkTerm`, `wkEqTerm`, in `Definition/Typed/Weakening.agda` |
| `SubstWf.lift`, `SubstWf.instantiate` | `⊢ˢʷ∷-⇑`, `⊢ˢʷ∷-sgSubst`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |
| `HasType.subst`, `TermEq.subst` | `subst-⊢∷`, `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |
| `HasType.conv_last` | `stability-⊢∷`, for contexts that only differ by their last type, in `Definition/Typed/Stability/Primitive.agda` |
| `SubstEq`, with `⊢ Δ` and `Δ ⊢ˢ σ : Γ` | `_⊢ˢʷ_≡_∷_`, which also types `τ`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |
| `SubstEq.lift`, `SubstEq.instantiate` | `⊢ˢʷ≡∷-⇑`, `⊢ˢʷ≡∷-sgSubst`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |
| `HasType.substEq` | `subst-⊢∷→⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |

ADE prove the weakening and the substitutions by induction on the size of the derivations, which
their judgments, in `Set`, have, while those of `Sic.Core.Typing` are propositions: each proof here
proves a stronger statement instead, which the module explains.
-/

namespace Sic.Core.TypedSubstitution.Validation

open Grade Syntax.Validation Term Typing.Validation

/--
The constant function keeps its type after a new declaration `x : A`, where `A` is `var 1`, at the
end of its context `A : U₀, B : U₀`: each variable of the function and of its type moves past `x`,
to the next index.
-/
example : Γ₂ ∙ var 1 ⊢ constant.wk1 : constantType.wk1 :=
  hasType_constant.wk (.step .id) (.snoc (.var wfCon_Γ₂))

/-- Each variable replaced by itself is a substitution of every well-formed context to itself. -/
example (hΓ : ⊢ Γ) : Γ ⊢ˢ var : Γ := fun x => by
  rw [subst_var]
  exact .var hΓ

/-- Every substitution replaces the variables of the empty context, which has none. -/
theorem substWf_empty : Δ ⊢ˢ σ : Con.empty := fun x => x.elim0

/-- A substitution extended by a term of the type of a new declaration. -/
theorem substWf_cons (hσ : Δ ⊢ˢ σ : Γ) (ha : Δ ⊢ a : A.subst σ) : Δ ⊢ˢ σ.cons a : Γ ∙ A
  | ⟨0, _⟩ => by
    show _ ⊢ a : A.wk1.subst _
    rw [subst_cons_wk1]
    exact ha
  | ⟨x + 1, hx⟩ => by
    show _ ⊢ σ _ : (Con.get _ (Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩)).subst _
    rw [Con.get_succ, subst_cons_wk1]
    exact hσ _

/--
A closed term keeps its type in every well-formed context, by the substitution of the variables of
the empty context, as `K` does: the substitution leaves it unchanged.
-/
example (h : ⊢ Γ) : Γ ⊢ combinatorK : combinatorKType :=
  (hasType_combinatorK .empty).subst (σ := Fin.elim0) substWf_empty h

/-- `S K K` keeps the type of the identity of `A` after a new declaration `z : A`. -/
example : ΓA ∙ var 0 ⊢ skk.wk1 : pi 𝟙 𝟘 (var 1) (var 2) :=
  hasType_skk.wk (.step .id) (.snoc hasType_ΓA_var)

end Sic.Core.TypedSubstitution.Validation
