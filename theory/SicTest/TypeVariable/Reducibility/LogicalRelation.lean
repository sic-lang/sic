module

public import Sic.Core.Reducibility.LogicalRelation
import Sic.Core.WellFormed

/-!
# A Type Variable: Logical Relation

The types of the context `A : U_l` of a type variable are reducible, for every equality relation.
-/

@[expose] public section

namespace SicTest.TypeVariable.Reducibility.LogicalRelation

open Sic.Core Sic.Grade Sic.Core.Term Sic.Core.Reducibility

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def ΓA : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_ΓA : ⊢ ΓA := .snoc (.univ (.univ .empty))

variable [EqualityRelation]

/-- The interpretation of a neutral type `N`, as `LogRel.ne` writes it. -/
def neutral (Γ : Con k n) (N : Term k n) : Interpretation k n where
  eqType B := ∃ M, (Γ ⊢ B ⇒* M) ∧ Neutral M ∧ (Γ ⊢ N ≅ M)
  eqTerm t u := ∃ t' u', (Γ ⊢ t ⇒* t' : N) ∧ (Γ ⊢ u ⇒* u' : N) ∧ Neutral t' ∧ Neutral u' ∧
    (Γ ⊢ t' ~ u' : N)

/--
A variable of a universe is a reducible type, at every level, in every context where it has that
type: it is neutral, and equal to itself since the equality relation equates each variable to
itself.
-/
theorem logRel_var {lower : ∀ l' < l, Relation 1} {Γ : Con 1 n} {x : Fin n}
    (h : Γ ⊢ var x : univ (.var 0)) : LogRel l lower Γ (var x) (neutral Γ (var x)) :=
  .ne (.refl (.univ h)) .var
    (EqualityRelation.ofUniv (EqualityRelation.ofNeutral (EqualityRelation.var h)))

/-- The type variable `A` is reducible at every level. -/
example : ΓA ⊩⟨l⟩ var 0 ▸ neutral ΓA (var 0) :=
  LogicalRelation.unfold ▸ logRel_var (.var wfCon_ΓA)

/--
The type `Π^𝟘_𝟙 (x : A). A` of the functions of `A` is reducible at every level: its domain `A` is
reducible in every context that contains `ΓA`, where it is a variable, and so is its codomain `A`,
at every argument, since it does not use it.
-/
example : ∃ P, ΓA ⊩⟨l⟩ pi 𝟙 𝟘 (var 0) (var 1) ▸ P := by
  have hA : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA
  have hA' : ΓA ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc (.univ hA))
  -- `A`, moved by a weakening `ρ`, is the variable `ρ.var 0`, of the universe `U_l`.
  have hF {m} {ρ : Wk m 1} {Δ : Con 1 m} (hρ : ρ ∷ Δ ⊇ ΓA) (hΔ : ⊢ Δ) :
      Δ ⊢ var (ρ.var 0) : univ (.var 0) := hA.wk hρ hΔ
  refine ⟨_, LogicalRelation.unfold ▸ LogRel.pi (.refl (.univ (.pi hA hA')))
    (EqualityRelation.ofUniv (EqualityRelation.pi
      (EqualityRelation.ofNeutral (EqualityRelation.var hA))
      (EqualityRelation.ofNeutral (EqualityRelation.var hA'))))
    (fun ρ Δ => neutral Δ (var (ρ.var 0)))
    (fun ρ Δ _ => neutral Δ (var (ρ.var 0)))
    (fun hρ hΔ => logRel_var (hF hρ hΔ)) (fun hρ hΔ _ => logRel_var (hF hρ hΔ))
    (fun hρ hΔ _ _ _ => ⟨_, .refl (.univ (hF hρ hΔ)), .var,
      EqualityRelation.ofUniv (EqualityRelation.ofNeutral (EqualityRelation.var (hF hρ hΔ)))⟩)⟩

/-- A variable of the type variable `A` is a reducible term of `A`: it is equal to itself. -/
example : (neutral (ΓA ∙ var 0) (var 1)).eqTerm (var 0) (var 0) :=
  have hx : ΓA ∙ var 0 ⊢ var 0 : var 1 := .var (.snoc (.univ (.var wfCon_ΓA)))
  ⟨_, _, .refl hx, .refl hx, .var, .var, EqualityRelation.var hx⟩

end SicTest.TypeVariable.Reducibility.LogicalRelation
