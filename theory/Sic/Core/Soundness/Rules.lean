module

public import Sic.Core.Soundness.Levels
public import Sic.Core.Soundness.Signature
public import Sic.Core.Soundness.Substitution

/-!
# Soundness of the Rules

Each rule of annex 12 of RFC 36 keeps the meaning of annex 15: when its premises are meaningful, in
the context of the rule at levels without variables, so is its conclusion.
The proofs take the premises at two equal closed substitutions `σ₁` and `σ₂` of the context, and
draw the conclusion from the closed judgments, whose properties `Closed` gives; the symmetry and the
transitivity of `eq(Γ)` move a premise from one substitution to the other.

A rule whose conclusion is that of an other judgment of the same meaning has no proof of its own: the
reflexivity of types and terms is the meaning of their premise, as `Σ; Γ ⊨ A` is `Σ; Γ ⊨ A ≡ A` and
`Σ; Γ ⊨ t : A` is `Σ; Γ ⊨ t ≡ t : A`, and the proof of a rule of equality gives that of the rule of
typing of the same name, such as `(conv)` from `(conv_≡)`.

ADE prove the validity of each rule in `Definition/LogicalRelation/Substitution/Introductions/`,
for their judgments with a context of definitions and without levels.
-/

@[expose] public section

namespace Sic.Core

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Equality of Types and of Terms -/

-- ADE: `sym-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(sym_type)` keeps the meaning. -/
theorem ValidEqTypeΓ.symm {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidEqTypeΓ sig ι ctx B A :=
  ⟨h.1, fun _ _ hσ => (h.2 _ _ (hσ.symm h.1)).symm⟩

-- ADE: `trans-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(trans_type)` keeps the meaning. -/
theorem ValidEqTypeΓ.trans {Γ : Scope} {ctx : Context 0 Γ} {A₁ A₂ A₃ : Term 0 Γ}
    (h₁ : ValidEqTypeΓ sig ι ctx A₁ A₂) (h₂ : ValidEqTypeΓ sig ι ctx A₂ A₃) :
    ValidEqTypeΓ sig ι ctx A₁ A₃ :=
  ⟨h₁.1, fun _ _ hσ => (h₁.2 _ _ hσ).trans (h₂.2 _ _ (hσ.right h₁.1))⟩

-- ADE: `wf-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `Σ; Γ ⊨ A ≡ B` gives `Σ; Γ ⊨ A`. -/
theorem ValidEqTypeΓ.left {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidTypeΓ sig ι ctx A :=
  h.trans h.symm

-- ADE: `wf-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `Σ; Γ ⊨ A ≡ B` gives `Σ; Γ ⊨ B`. -/
theorem ValidEqTypeΓ.right {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidTypeΓ sig ι ctx B :=
  h.symm.trans h

-- ADE: `sym-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(sym)` keeps the meaning: the equality at the substitutions swapped is at the type of the
second, which the type converts back to the first. -/
theorem ValidEqTermΓ.symm {Γ : Scope} {ctx : Context 0 Γ} {t u A : Term 0 Γ}
    (h : ValidEqTermΓ sig ι ctx t u A) : ValidEqTermΓ sig ι ctx u t A :=
  ⟨h.1, fun _ _ hσ =>
    (h.2 _ _ (hσ.symm h.1.1)).symm.conv (h.1.2 _ _ (hσ.symm h.1.1))⟩

-- ADE: `trans-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(trans)` keeps the meaning: the second equality, at the second substitution twice, is at its
type, which the type converts to that of the first. -/
theorem ValidEqTermΓ.trans {Γ : Scope} {ctx : Context 0 Γ} {t₁ t₂ t₃ A : Term 0 Γ}
    (h₁ : ValidEqTermΓ sig ι ctx t₁ t₂ A) (h₂ : ValidEqTermΓ sig ι ctx t₂ t₃ A) :
    ValidEqTermΓ sig ι ctx t₁ t₃ A :=
  ⟨h₁.1, fun _ _ hσ => (h₁.2 _ _ hσ).trans
    ((h₂.2 _ _ (hσ.right h₁.1.1)).conv (h₁.1.2 _ _ (hσ.symm h₁.1.1)))⟩

-- ADE: `conv-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(conv_≡)` keeps the meaning, and `(conv)` with it. -/
theorem ValidEqTermΓ.conv {Γ : Scope} {ctx : Context 0 Γ} {t u A B : Term 0 Γ}
    (h : ValidEqTermΓ sig ι ctx t u A) (hA : ValidEqTypeΓ sig ι ctx A B) :
    ValidEqTermΓ sig ι ctx t u B :=
  ⟨hA.right, fun _ _ hσ => (h.2 _ _ hσ).conv (hA.2 _ _ (hσ.left h.1.1))⟩

end

end Sic.Core
