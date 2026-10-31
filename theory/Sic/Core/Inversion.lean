module

public import Sic.Core.Typing
import Sic.Core.WellFormed

/-!
# Inversion

The inversion of the typing of the terms: a typed universe, type of functions, variable, abstraction
or application has the premises of its rule, and a type equal to the one of its rule, as in the
formalization of ADE.
The inversion of the types of functions that the syntactic validity uses, `HasType.inv_pi`, is in
`Sic.Core.Typing`, and `HasType.inv_pi_univ` adds the type of the type of functions.

## Correspondence with the Formalization of ADE

| Theorem | Theorem of ADE, in `Definition/Typed/Inversion.agda` or `Inversion/Primitive.agda` |
| --- | --- |
| `HasType.inv_univ` | `inversion-U` |
| `HasType.inv_pi_univ` | `inversion-ΠΣ-U` |
| `HasType.inv_var` | `inversion-var` |
| `HasType.inv_lam` | `inversion-lam` |
| `HasType.inv_app` | `inversion-app` |

The variables of ADE have their types through a relation `x ∷ B ∈ Γ`, which `HasType.inv_var`
replaces by the function `Con.get`.

Each proof generalizes the term of the judgment to any term equal to the one of the rule, since an
induction on a judgment of the mutual types of the judgments cannot fix its term, as the proof of
`HasType.inv_pi`: `(conv)` composes the equality of the types, and the rule of the term gives its
own premises, with the type of its conclusion equal to itself.
-/

@[expose] public section

namespace Sic.Core

open Term

private theorem HasType.inv_univ_aux : Γ ⊢ s : C → s = Term.univ l →
    Γ ⊢ C ≡ Term.univ l.succ
  | .conv h hC, e => (TypeEq.symm hC).trans (h.inv_univ_aux e)
  | .univ h, e => by cases e; exact .refl (.univ (.univ h))
  | .var _, e | .pi .., e | .lam .., e | .app .., e => by cases e

/-- A universe has only the types equal to the universe just above it. -/
theorem HasType.inv_univ (h : Γ ⊢ Term.univ l : C) : Γ ⊢ C ≡ Term.univ l.succ :=
  h.inv_univ_aux rfl

private theorem HasType.inv_pi_univ_aux : Γ ⊢ s : C → s = Term.pi p q A B →
    ∃ l₁ l₂, (Γ ⊢ A : Term.univ l₁) ∧ (Γ ∙ A ⊢ B : Term.univ l₂) ∧ Γ ⊢ C ≡ Term.univ (l₁ ⊔ l₂)
  | .conv h hC, e =>
    have ⟨_, _, hA, hB, hC'⟩ := h.inv_pi_univ_aux e
    ⟨_, _, hA, hB, (TypeEq.symm hC).trans hC'⟩
  | .pi hA hB, e => by cases e; exact ⟨_, _, hA, hB, .refl (.univ (.univ hA.wfCon))⟩
  | .var _, e | .univ _, e | .lam .., e | .app .., e => by cases e

/--
A type of functions has only the types equal to the universe of the larger level of a universe of
its domain and of a universe of its codomain.
-/
theorem HasType.inv_pi_univ (h : Γ ⊢ Term.pi p q A B : C) :
    ∃ l₁ l₂, (Γ ⊢ A : Term.univ l₁) ∧ (Γ ∙ A ⊢ B : Term.univ l₂) ∧ Γ ⊢ C ≡ Term.univ (l₁ ⊔ l₂) :=
  h.inv_pi_univ_aux rfl

private theorem HasType.inv_var_aux : Γ ⊢ s : C → s = Term.var x → Γ ⊢ C ≡ Γ.get x
  | .conv h hC, e => (TypeEq.symm hC).trans (h.inv_var_aux e)
  | .var h, e => by cases e; exact .refl (h.get _)
  | .univ _, e | .pi .., e | .lam .., e | .app .., e => by cases e

/-- A variable has only the types equal to the type of its declaration. -/
theorem HasType.inv_var (h : Γ ⊢ Term.var x : C) : Γ ⊢ C ≡ Γ.get x :=
  h.inv_var_aux rfl

private theorem HasType.inv_lam_aux : Γ ⊢ s : C → s = Term.lam p A t →
    ∃ q B, (Γ ⊢ Term.pi p q A B) ∧ (Γ ∙ A ⊢ t : B) ∧ Γ ⊢ C ≡ Term.pi p q A B
  | .conv h hC, e =>
    have ⟨_, _, hPi, ht, hC'⟩ := h.inv_lam_aux e
    ⟨_, _, hPi, ht, (TypeEq.symm hC).trans hC'⟩
  | .lam hPi ht, e => by cases e; exact ⟨_, _, hPi, ht, .refl hPi⟩
  | .var _, e | .univ _, e | .pi .., e | .app .., e => by cases e

/--
An abstraction has a type of functions, with its grade and the type of its argument, whose codomain
types its body, and only the types equal to it.
-/
theorem HasType.inv_lam (h : Γ ⊢ Term.lam p A t : C) :
    ∃ q B, (Γ ⊢ Term.pi p q A B) ∧ (Γ ∙ A ⊢ t : B) ∧ Γ ⊢ C ≡ Term.pi p q A B :=
  h.inv_lam_aux rfl

private theorem HasType.inv_app_aux : Γ ⊢ s : C → s = Term.app p t a →
    ∃ q A B, (Γ ⊢ t : Term.pi p q A B) ∧ (Γ ⊢ a : A) ∧ Γ ⊢ C ≡ B.instantiate a
  | .conv h hC, e =>
    have ⟨_, _, _, ht, ha, hC'⟩ := h.inv_app_aux e
    ⟨_, _, _, ht, ha, (TypeEq.symm hC).trans hC'⟩
  | .app ht ha, e => by cases e; exact ⟨_, _, _, ht, ha, .refl (HasType.app ht ha).wfType⟩
  | .var _, e | .univ _, e | .pi .., e | .lam .., e => by cases e

/--
The function of an application has a type of functions, with the grade of the application, whose
domain types the argument, and the application has only the types equal to the codomain at the
argument.
-/
theorem HasType.inv_app (h : Γ ⊢ Term.app p t a : C) :
    ∃ q A B, (Γ ⊢ t : Term.pi p q A B) ∧ (Γ ⊢ a : A) ∧ Γ ⊢ C ≡ B.instantiate a :=
  h.inv_app_aux rfl

end Sic.Core
