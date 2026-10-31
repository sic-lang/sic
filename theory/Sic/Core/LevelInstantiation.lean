module

public import Sic.Core.Typing

/-!
# Level Instantiation

The judgments of `Sic.Core.Typing` with their level variables replaced by levels, as RFC 24
requires of its prenex universe polymorphism: a definition checked once with its level variables
holds at each of its uses, whatever levels instantiate them.
The proofs only need that instantiating the levels commutes with the operations on terms, and that
two equal levels stay equal once instantiated, `Level.Equiv.subst`.

## Correspondence with the Formalization of ADE

| Definition or theorem | Definition or theorem of ADE |
| --- | --- |
| `Con.substLevels` | `_[_]` on contexts, in `Definition/Untyped.agda` |
| `WfCon.substLevels`, `IsType.substLevels`, `TypeEq.substLevels`, `HasType.substLevels`, `TermEq.substLevels` | `subst-⊢`, `subst-⊢≡`, `subst-⊢∷`, `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda` |

The levels of ADE are terms of a type of levels, so that a level variable is a variable of the
context, instantiated by their substitution of terms.
The level variables of RFC 24 are not in the context, so that their instantiation is an operation
of its own, which keeps the context as it is, but instantiates the levels of its types.
-/

@[expose] public section

namespace Sic.Core

open Term

/-- The context `Γ` whose level variables are replaced by the levels `σ`, in each of its types. -/
def Con.substLevels (σ : Fin k → Level j) : Con k n → Con j n
  | empty => empty
  | snoc Γ A => snoc (Γ.substLevels σ) (A.substLevels σ)

/-- Instantiating the levels commutes with taking the type of a variable. -/
theorem Con.substLevels_get (σ : Fin k → Level j) :
    ∀ (Γ : Con k n) (x : Fin n), (Γ.get x).substLevels σ = (Γ.substLevels σ).get x
  | snoc _ A, ⟨0, _⟩ => substLevels_wk σ _ A
  | snoc Γ _, ⟨x + 1, h⟩ => by
    rw [← Fin.succ_mk _ _ (Nat.lt_of_succ_lt_succ h), Con.get_succ, substLevels_wk,
      substLevels_get σ Γ]
    rfl

/-- Instantiating the levels commutes with instantiating a binder. -/
theorem Term.substLevels_instantiate (σ : Fin k → Level j) (t : Term k (n + 1)) (a : Term k n) :
    (t.instantiate a).substLevels σ = (t.substLevels σ).instantiate (a.substLevels σ) := by
  rw [instantiate, substLevels_subst, instantiate]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-!
Every judgment holds with its level variables instantiated, by induction on its derivation: each
rule instantiated is the same rule, at the instantiated levels, once the operations of its
conclusion are commuted with the instantiation.
-/

variable (σ : Fin k → Level j)

mutual

theorem WfCon.substLevels : ⊢ Γ → ⊢ Γ.substLevels σ
  | .empty => .empty
  | .snoc h => .snoc (h.substLevels)

theorem IsType.substLevels : Γ ⊢ A → Γ.substLevels σ ⊢ A.substLevels σ
  | .univ h => .univ (h.substLevels)

theorem TypeEq.substLevels : Γ ⊢ A ≡ B → Γ.substLevels σ ⊢ A.substLevels σ ≡ B.substLevels σ
  | .univ h => .univ (h.substLevels)
  | .refl h => .refl (h.substLevels)
  | .symm h => .symm (h.substLevels)
  | .trans h₁ h₂ => .trans (h₁.substLevels) (h₂.substLevels)

theorem HasType.substLevels : Γ ⊢ t : A → Γ.substLevels σ ⊢ t.substLevels σ : A.substLevels σ
  | .var h => by
    rw [Con.substLevels_get]
    exact .var (h.substLevels)
  | .conv h hA => .conv (h.substLevels) (hA.substLevels)
  | .univ h => .univ (h.substLevels)
  | .pi hA hB => .pi (hA.substLevels) (hB.substLevels)
  | .lam hT ht => .lam (hT.substLevels) (ht.substLevels)
  | .app ht ha => by
    rw [substLevels_instantiate]
    exact .app (ht.substLevels) (ha.substLevels)

theorem TermEq.substLevels :
    Γ ⊢ t ≡ u : A → Γ.substLevels σ ⊢ t.substLevels σ ≡ u.substLevels σ : A.substLevels σ
  | .refl h => .refl (h.substLevels)
  | .symm h => .symm (h.substLevels)
  | .trans h₁ h₂ => .trans (h₁.substLevels) (h₂.substLevels)
  | .conv h hA => .conv (h.substLevels) (hA.substLevels)
  | .univ h hl => .univ (h.substLevels) (hl.subst σ)
  | .pi hA hB => .pi (hA.substLevels) (hB.substLevels)
  | .lam hT hA ht => .lam (hT.substLevels) (hA.substLevels) (ht.substLevels)
  | .app ht ha => by
    rw [substLevels_instantiate]
    exact .app (ht.substLevels) (ha.substLevels)
  | .beta hT ht ha => by
    rw [substLevels_instantiate, substLevels_instantiate]
    exact .beta (hT.substLevels) (ht.substLevels) (ha.substLevels)
  | .eta (t := t) h => by
    have e : (t.wk1).substLevels σ = (t.substLevels σ).wk1 := substLevels_wk σ _ t
    simp only [Term.substLevels, e]
    exact .eta (h.substLevels)

end

end Sic.Core
