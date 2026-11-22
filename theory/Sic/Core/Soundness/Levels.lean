module

public import Sic.Core.Meaning.Uniqueness.Levels
import Sic.Core.Soundness.Substitution

/-!
# Equal Substitutions at Levels by Their Values

Two equal substitutions of a context are equal substitutions of the context at levels of the same
values, which the meaning of the closed judgments does not tell apart: the soundness reads the
fields of a type declaration and the arguments of a destructor at the values of the levels of an
instance, while an instance gives them at its own levels.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- Two equal substitutions of a context are equal substitutions of a context equal to it up to its
levels: each type of the context changes for one equal to it up to its levels, which the meaning of
the closed judgments does not tell apart. -/
theorem EqSubst.levelEquiv {sig : Signature} {ι : Interpretation} : {Γ : Scope} →
    {ctx₁ ctx₂ : Context 0 Γ} → Context.LevelEquiv ctx₁ ctx₂ → {σ₁ σ₂ : Subst 0 [] Γ} →
      EqSubst sig ι ctx₁ σ₁ σ₂ → EqSubst sig ι ctx₂ σ₁ σ₂
  | _, _, _, .empty, _, _, hσ => hσ
  | _, _, _, .var h hA, _, _, hσ => by
    obtain ⟨hσ, ht⟩ := (EqSubst.var_iff _ _ _ _).1 hσ
    exact (EqSubst.var_iff _ _ _ _).2 ⟨EqSubst.levelEquiv h hσ,
      ht.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _)
        (hA.subst (Subst.LevelEquiv.refl _))⟩
  | _, _, _, .secondOrder ψ h hΘ hA, _, _, hσ => by
    obtain ⟨hσ, ht⟩ := (EqSubst.secondOrder_iff _ _ _ _ _ _).1 hσ
    refine (EqSubst.secondOrder_iff _ _ _ _ _ _).2 ⟨EqSubst.levelEquiv h hσ, fun τ₁ τ₂ hτ => ?_⟩
    have hτ' := EqSubst.levelEquiv
      (Context.LevelEquiv.empty.append (hΘ.symm.subst (Subst.LevelEquiv.refl _))) hτ
    exact (ht τ₁ τ₂ hτ').levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _)
      ((hA.subst (Subst.LevelEquiv.refl _)).subst (Subst.LevelEquiv.refl _))
termination_by _ ctx₁ => ctx₁.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

/-- Two closed substitutions are equal for a telescope at levels `L` without variables, substituted
by `τ`, if and only if they are equal for the telescope at the values of `L`, substituted by `τ'`
equal to `τ` up to its levels, as the arguments of a destructor of a codata type and the fields of
a constructor. -/
theorem EqSubst.substLevels_iff_atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    (L : Fin k → Level 0) {Ξ : Scope} {ps : List Parameter} (Θ : Telescope k Ξ ps)
    {τ τ' : Subst 0 [] Ξ} (hτ : Subst.LevelEquiv τ τ') {σ₁ σ₂ : Subst 0 [] _} :
    EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst τ)) σ₁ σ₂ ↔
      EqSubst sig ι (Context.empty.append ((Θ.atLevels fun i => (L i).closedValue).subst τ'))
        σ₁ σ₂ :=
  ⟨EqSubst.levelEquiv (Context.LevelEquiv.append .empty (Θ.closedValues_levelEquiv L hτ)),
    EqSubst.levelEquiv (Context.LevelEquiv.append .empty (Θ.closedValues_levelEquiv L hτ).symm)⟩

/-- Two closed substitutions equal for a context at levels `L` without variables are equal for it
at the values of `L`. -/
theorem EqSubst.atLevels_of_substLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    (L : Fin k → Level 0) {Γ : Scope} {ctx : Context k Γ} {σ₁ σ₂ : Subst 0 [] Γ}
    (h : EqSubst sig ι (ctx.substLevels L) σ₁ σ₂) :
    EqSubst sig ι (ctx.atLevels fun i => (L i).closedValue) σ₁ σ₂ :=
  EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun _ => Level.equivalence.symm (Level.ofNat_closedValue _)) _)
    h

end Sic.Core
