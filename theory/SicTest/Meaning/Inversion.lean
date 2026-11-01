module

import Sic.Core.Inversion

/-!
# Meaning of the Inversion

Each inversion of `Sic.Core.Inversion` is an equivalence: its conclusion gives back the judgment by
the rule of the term and `(conv)`, so that it states exactly the premises of the rule, and the types
of the term, no more and no less.
-/

@[expose] public section

namespace SicTest.Meaning.Inversion

open Sic.Core Sic.Core.Term

/-- A universe has exactly the types equal to the universe just above it. -/
example : (Γ ⊢ univ l : C) ↔ (Γ ⊢ C ≡ univ l.succ) :=
  ⟨HasType.inv_univ, fun hC => .conv (.univ hC.wfCon) (TypeEq.symm hC)⟩

/--
A type of functions has exactly the types equal to the universe of the larger level of a universe of
its domain and of a universe of its codomain.
-/
example : (Γ ⊢ pi p q A B : C) ↔
    ∃ l₁ l₂, (Γ ⊢ A : univ l₁) ∧ (Γ ∙ A ⊢ B : univ l₂) ∧ Γ ⊢ C ≡ univ (l₁ ⊔ l₂) :=
  ⟨HasType.inv_pi_univ, fun ⟨_, _, hA, hB, hC⟩ => .conv (.pi hA hB) (TypeEq.symm hC)⟩

/-- A variable has exactly the types equal to the type of its declaration. -/
example : (Γ ⊢ var x : C) ↔ (Γ ⊢ C ≡ Γ.get x) :=
  ⟨HasType.inv_var, fun hC => .conv (.var hC.wfCon) (TypeEq.symm hC)⟩

/-- An abstraction has exactly the types equal to a type of functions that types its body. -/
example : (Γ ⊢ lam p A t : C) ↔
    ∃ q B, (Γ ⊢ pi p q A B) ∧ (Γ ∙ A ⊢ t : B) ∧ Γ ⊢ C ≡ pi p q A B :=
  ⟨HasType.inv_lam, fun ⟨_, _, hPi, ht, hC⟩ => .conv (.lam hPi ht) (TypeEq.symm hC)⟩

/-- An application has exactly the types equal to the codomain of its function at the argument. -/
example : (Γ ⊢ app p t a : C) ↔
    ∃ q A B, (Γ ⊢ t : pi p q A B) ∧ (Γ ⊢ a : A) ∧ Γ ⊢ C ≡ B.instantiate a :=
  ⟨HasType.inv_app, fun ⟨_, _, _, ht, ha, hC⟩ => .conv (.app ht ha) (TypeEq.symm hC)⟩

end SicTest.Meaning.Inversion
