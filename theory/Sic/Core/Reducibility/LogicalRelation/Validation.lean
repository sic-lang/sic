module

import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.WellFormed

/-!
# Validation of the Logical Relation

The logical relation of `Sic.Core.Reducibility.LogicalRelation` checked against the formalizations
of ADE and of Pujet, and on the types of the context of a type variable, for every equality
relation.

| Definition or theorem | Definition or theorem of ADE, in `Definition/LogicalRelation.agda` | Of Pujet, in `Definition/LogicalRelation.agda` |
| --- | --- | --- |
| `Interpretation.eqType`, `Interpretation.eqTerm` | `_⊩⟨_⟩_≡_/_`, `_⊩⟨_⟩_≡_∷_/_` | the second and fourth predicates of `_⊩LR_▸_▸_▸_` |
| `LogRel`, with `lower` | `LogRel`, with `rec` | `_⊩LR_▸_▸_▸_`, with `rec` |
| `LogRel.univ` | `Uᵣ`, with `_⊩₁U_`, `_⊩₁U≡_/_`, `_⊩₁U_≡_∷U/_` | `LRU` |
| `LogRel.ne` | `ne`, with `_⊩ne_`, `_⊩ne_≡_/_`, `_⊩neNf_≡_∷_` | `LRne` |
| `LogRel.pi` | `Bᵣ`, with `_⊩ₗB⟨_⟩_`, `_⊩ₗB⟨_⟩_≡_/_`, `_⊩ₗΠ_≡_∷_/_` | `LRΠ` |
| `LogicalRelation` | `_⊩⟨_⟩_`, with `kit` | `_⊩⟨_⟩_`, with `kit` |
| `Level.bound` | `↑ᵘ`, which sends the neutral levels to `0` | none, with a single universe |
| `LogRel.escape`, `LogRel.escape_eqType`, `LogRel.escape_eqTerm` | `escape`, `escapeEq`, `escapeTermEq`, in `Definition/LogicalRelation/Properties/Escape.agda` | the same |

Pujet's relation is a predicate of a type and of its interpretation, as here, where ADE's relation
computes the interpretation from a proof of reducibility.
Both have a constructor `emb`, which moves a reducible type to a larger level, while the relation at
a level here interprets each universe at its own level: a reducible type stays reducible at the
larger levels, a lemma instead of a constructor, so that each weak head normal form has one
constructor.
ADE reduce the types with a reduction of their own, which a reduction of a term in a universe
replaces here, and their relation also covers their other types, levels and definitions.
-/

namespace Sic.Core.Reducibility.LogicalRelation.Validation

open Grade Term

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def ΓA : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_ΓA : ⊢ ΓA := .snoc (.univ .empty)

/-- `LogRel.univ` does not interpret `U_l` at the level `0`, since `l` is bounded by `0`. -/
example : ¬ (0 : Nat) < (Level.var 0 : Level 1).bound := by decide

variable [EqualityRelation]

/-- The universe `U₀` is reducible at the level `1`, in the empty context. -/
example : ∃ P, (.empty : Con 0 0) ⊩⟨1⟩ univ .zero ▸ P :=
  ⟨_, LogicalRelation.unfold ▸ LogRel.univ (L := .zero) (by decide) (.refl (.univ .empty))⟩

/-- The interpretation of a neutral type `N` of the universe `U_L`, as `LogRel.ne` writes it. -/
def neutral (Γ : Con k n) (N : Term k n) (L : Level k) : Interpretation k n where
  eqType B := ∃ M, (Γ ⊢ B ⇒* M : univ L) ∧ Neutral M ∧ (Γ ⊢ N ≅ M : univ L)
  eqTerm t u := ∃ t' u', (Γ ⊢ t ⇒* t' : N) ∧ (Γ ⊢ u ⇒* u' : N) ∧ Neutral t' ∧ Neutral u' ∧
    (Γ ⊢ t' ~ u' : N)

/--
A variable of a universe is a reducible type, at every level, in every context where it has that
type: it is neutral, and equal to itself since the equality relation equates each variable to
itself.
-/
theorem logRel_var {lower : ∀ l' < l, Relation 1} {Γ : Con 1 n} {x : Fin n}
    (h : Γ ⊢ var x : univ (.var 0)) : LogRel l lower Γ (var x) (neutral Γ (var x) (.var 0)) :=
  .ne (.refl h) .var (EqualityRelation.ofNeutral (EqualityRelation.var h))

/-- The type variable `A` is reducible at every level. -/
example : ΓA ⊩⟨l⟩ var 0 ▸ neutral ΓA (var 0) (.var 0) :=
  LogicalRelation.unfold ▸ logRel_var (.var wfCon_ΓA)

/--
The type `Π^𝟘_𝟙 (x : A). A` of the functions of `A` is reducible at every level: its domain `A` is
reducible in every context that contains `ΓA`, where it is a variable, and so is its codomain `A`,
at every argument, since it does not use it.
-/
example : ∃ P, ΓA ⊩⟨l⟩ pi 𝟙 𝟘 (var 0) (var 1) ▸ P := by
  have hA : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA
  have hA' : ΓA ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  -- `A`, moved by a weakening `ρ`, is the variable `ρ.var 0`, of the universe `U_l`.
  have hF {m} {ρ : Wk m 1} {Δ : Con 1 m} (hρ : ρ ∷ Δ ⊇ ΓA) (hΔ : ⊢ Δ) :
      Δ ⊢ var (ρ.var 0) : univ (.var 0) := hA.wk hρ hΔ
  refine ⟨_, LogicalRelation.unfold ▸ LogRel.pi (L := .var 0 ⊔ .var 0) (.refl (.pi hA hA'))
    (EqualityRelation.pi (EqualityRelation.ofNeutral (EqualityRelation.var hA))
      (EqualityRelation.ofNeutral (EqualityRelation.var hA')))
    (fun ρ Δ => neutral Δ (var (ρ.var 0)) (.var 0))
    (fun ρ Δ _ => neutral Δ (var (ρ.var 0)) (.var 0))
    (fun hρ hΔ => logRel_var (hF hρ hΔ)) (fun hρ hΔ _ => logRel_var (hF hρ hΔ))
    (fun hρ hΔ _ _ _ => ⟨_, .refl (hF hρ hΔ), .var,
      EqualityRelation.ofNeutral (EqualityRelation.var (hF hρ hΔ))⟩)⟩

/-- A variable of the type variable `A` is a reducible term of `A`: it is equal to itself. -/
example : (neutral (ΓA ∙ var 0) (var 1) (.var 0)).eqTerm (var 0) (var 0) :=
  have hx : ΓA ∙ var 0 ⊢ var 0 : var 1 := .var (.snoc (.var wfCon_ΓA))
  ⟨_, _, .refl hx, .refl hx, .var, .var, EqualityRelation.var hx⟩

end Sic.Core.Reducibility.LogicalRelation.Validation
