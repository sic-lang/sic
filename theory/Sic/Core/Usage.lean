module

public import Sic.Core.Syntax
public import Sic.GradeVector
public import Sic.Mode

/-!
# Usage

The judgment of usage of RFC 24 for the terms of `Sic.Core.Syntax`: checked in the mode `m`, the
term `t` uses each variable of its context as the grade that the vector `γ` gives it allows,
`γ ▶[m] t`, which RFC 24 writes `γ ▶_m t`.
Usage reads the term alone, whose binders carry their grades: it has no context of types, and is
separate from the typing of `Sic.Core.Typing`.
Each rule has the name of the RFC, and the inversions, at the end, recover the premises of the rule
of each construct from any derivation of its usage, whatever uses of `(sub)` it makes.

The rules cover the universes and the functions of RFC 24, so far.

## Correspondence with the Formalization of ADE

ADE have the same rules for the variables and the functions, over their two modes `𝟘ᵐ` and `𝟙ᵐ`,
which are `𝟘𝟘ᵐ` and `𝟙𝟙ᵐ` here.
Their rule for a universe has a premise on the usage of its level, which is a term of theirs, while
the levels here are not terms and use no variable.
-/

@[expose] public section

namespace Sic.Core

open Grade GradeVector Mode Term

set_option hygiene false in
/-- `γ ▶[m] t`: checked in the mode `m`, the term `t` uses its variables as `γ` allows. -/
notation:40 γ:41 " ▶[" m "] " t:41 => Usage γ m t

-- ADE: `_▸[_]_`, in `Graded/Usage.agda`.
/-- `γ ▶[m] t`: checked in the mode `m`, the term `t` uses its variables as `γ` allows. -/
inductive Usage {k : Nat} : {n : Nat} → GradeVector n → Mode → Term k n → Prop where
  -- ADE: `sub` of `_▸[_]_`, in `Graded/Usage.agda`.
  /-- `(sub)`: a term may be given grades lower than its uses. -/
  | sub : γ ▶[m] t → δ ≤ γ → δ ▶[m] t
  -- ADE: `var` of `_▸[_]_`, in `Graded/Usage.agda`.
  /-- `(var_m)`: a variable uses itself with the grade of the mode, and nothing else. -/
  | var : (𝟘ᶜ, x ≔ ⌜m⌝) ▶[m] var x
  -- ADE: `Uₘ` of `_▸[_]_`, in `Graded/Usage.agda`.
  /-- `(U_m)`: a universe uses no variable. -/
  | univ : 𝟘ᶜ ▶[m] univ l
  -- ADE: `ΠΣₘ` of `_▸[_]_`, in `Graded/Usage.agda`.
  /--
  `(Π_m)`: the type of functions uses the variables of its domain as many times as the argument is
  used, and its codomain uses the argument with the grade `q`.
  -/
  | pi : γ ▶[m ⊙ p] A → δ ∙ (⌜m⌝ * q) ▶[m] B → (p • γ) + δ ▶[m] pi p q A B
  -- ADE: `lamₘ` of `_▸[_]_`, in `Graded/Usage.agda`.
  /-- `(λ_m)`: the body of an abstraction uses its argument with the grade `p`. -/
  | lam : γ ∙ (⌜m⌝ * p) ▶[m] t → γ ▶[m] lam p A t
  -- ADE: `_∘ₘ_` of `_▸[_]_`, in `Graded/Usage.agda`.
  /-- `(∘_m)`: an application uses its argument as many times as the function does. -/
  | app : γ ▶[m] t → δ ▶[m ⊙ p] a → γ + (p • δ) ▶[m] app p t a

/-!
## Inversions

Each inversion follows the derivation down to the rule of the construct, through the uses of
`(sub)`, whose bounds compose by transitivity.
-/

private theorem Usage.inv_var_aux {γ : GradeVector n} {s : Term k n} :
    γ ▶[m] s → s = Term.var x → γ ≤ (𝟘ᶜ, x ≔ ⌜m⌝)
  | .sub h hγ, e => GradeVector.le_trans hγ (h.inv_var_aux e)
  | .var, e => by cases e; exact GradeVector.le_refl _
  | .univ, e | .pi .., e | .lam _, e | .app .., e => by cases e

-- ADE: `inv-usage-var`, in `Graded/Usage/Inversion.agda`.
/-- A variable uses at most itself, with the grade of the mode. -/
theorem Usage.inv_var {γ : GradeVector n} (h : γ ▶[m] (Term.var x : Term k n)) :
    γ ≤ (𝟘ᶜ, x ≔ ⌜m⌝) :=
  h.inv_var_aux rfl

private theorem Usage.inv_univ_aux : γ ▶[m] s → s = Term.univ l → γ ≤ 𝟘ᶜ
  | .sub h hγ, e => GradeVector.le_trans hγ (h.inv_univ_aux e)
  | .univ, _ => GradeVector.le_refl _
  | .var, e | .pi .., e | .lam _, e | .app .., e => by cases e

-- ADE: `inv-usage-U`, in `Graded/Usage/Inversion.agda`.
/-- A universe uses no variable. -/
theorem Usage.inv_univ (h : γ ▶[m] Term.univ l) : γ ≤ 𝟘ᶜ :=
  h.inv_univ_aux rfl

private theorem Usage.inv_pi_aux : γ ▶[m] s → s = Term.pi p q A B →
    ∃ δ η, (δ ▶[m ⊙ p] A) ∧ (η ∙ (⌜m⌝ * q) ▶[m] B) ∧ γ ≤ (p • δ) + η
  | .sub h hγ, e =>
    have ⟨_, _, hA, hB, hγ'⟩ := h.inv_pi_aux e
    ⟨_, _, hA, hB, GradeVector.le_trans hγ hγ'⟩
  | .pi hA hB, e => by cases e; exact ⟨_, _, hA, hB, GradeVector.le_refl _⟩
  | .var, e | .univ, e | .lam _, e | .app .., e => by cases e

-- ADE: `inv-usage-ΠΣ`, in `Graded/Usage/Inversion.agda`.
/-- The type of functions uses at most the variables of the premises of `(Π_m)`. -/
theorem Usage.inv_pi (h : γ ▶[m] Term.pi p q A B) :
    ∃ δ η, (δ ▶[m ⊙ p] A) ∧ (η ∙ (⌜m⌝ * q) ▶[m] B) ∧ γ ≤ (p • δ) + η :=
  h.inv_pi_aux rfl

private theorem Usage.inv_lam_aux : γ ▶[m] s → s = Term.lam p A t →
    ∃ δ, (δ ∙ (⌜m⌝ * p) ▶[m] t) ∧ γ ≤ δ
  | .sub h hγ, e =>
    have ⟨_, ht, hγ'⟩ := h.inv_lam_aux e
    ⟨_, ht, GradeVector.le_trans hγ hγ'⟩
  | .lam ht, e => by cases e; exact ⟨_, ht, GradeVector.le_refl _⟩
  | .var, e | .univ, e | .pi .., e | .app .., e => by cases e

-- ADE: `inv-usage-lam`, in `Graded/Usage/Inversion.agda`.
/-- An abstraction uses at most the variables that its body uses besides its argument. -/
theorem Usage.inv_lam (h : γ ▶[m] Term.lam p A t) : ∃ δ, (δ ∙ (⌜m⌝ * p) ▶[m] t) ∧ γ ≤ δ :=
  h.inv_lam_aux rfl

private theorem Usage.inv_app_aux : γ ▶[m] s → s = Term.app p t a →
    ∃ δ η, (δ ▶[m] t) ∧ (η ▶[m ⊙ p] a) ∧ γ ≤ δ + (p • η)
  | .sub h hγ, e =>
    have ⟨_, _, ht, ha, hγ'⟩ := h.inv_app_aux e
    ⟨_, _, ht, ha, GradeVector.le_trans hγ hγ'⟩
  | .app ht ha, e => by cases e; exact ⟨_, _, ht, ha, GradeVector.le_refl _⟩
  | .var, e | .univ, e | .pi .., e | .lam _, e => by cases e

-- ADE: `inv-usage-app`, in `Graded/Usage/Inversion.agda`.
/-- An application uses at most the variables of the premises of `(∘_m)`. -/
theorem Usage.inv_app (h : γ ▶[m] Term.app p t a) :
    ∃ δ η, (δ ▶[m] t) ∧ (η ▶[m ⊙ p] a) ∧ γ ≤ δ + (p • η) :=
  h.inv_app_aux rfl

end Sic.Core
