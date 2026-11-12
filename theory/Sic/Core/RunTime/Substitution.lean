module

public import Sic.Core.RunTime.Relation
import Sic.Core.Substitution.Closed

/-!
# Substitutions at Run Time

The closed substitutions of a context extended by a telescope at run time: a substitution of the
context and its addresses, as a vector of grades requires, followed by arguments of the telescope
related to their addresses at grades `g`, stand for the context extended by the telescope, its
variables at the grades `g`, the addresses of the arguments, the last one first, before those of the
context.
The branches of a recursor extend the context of the recursor by the fields of their constructor
and by their recursive results, at the grades of their variables.

ADE extend their substitutions one variable at a time, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-- `(σ, (t, t̄)) = ((σ, t), t̄)`: a closed substitution of a context followed by the arguments
`t, t̄` of a telescope is the substitution followed by `t`, then by `t̄`. -/
theorem Subst.append_cons {Γ : Scope} {p : Parameter} {ps : List Parameter} (σ : Subst k [] Γ)
    (t : Term k []) (ts : Args k [] ps) :
    @Eq (Subst k [] (Γ.extend (ps.length + 1)))
      (Subst.append σ (Args.toSubst (ps := p :: ps) (.cons t ts)))
      (Subst.append (Γ := .var :: Γ) (Subst.append (n := 1) σ (Subst.closedSingle t))
        ts.toSubst) := by
  funext a x
  rcases Var.cases_extend (Γ := .var :: Γ) ps.length x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine Eq.trans ?_ (Subst.append_weakenN (Γ := .var :: Γ) _ _ y).symm
    cases y with
    | zero =>
      have e : (Var.weakenN (Γ := .var :: Γ) ps.length (Var.zero (Γ := Γ)) :
          Var (Γ.extend (ps.length + 1)) .var) =
          Ren.liftN (ps.length + 1) (Ren.empty (Γ := Γ)) (Var.weakenN (Γ := [.var]) ps.length .zero) :=
        (Ren.liftN_weakenN (Γ := .var :: Γ) (Δ := [.var]) ps.length (Ren.lift Ren.empty) .zero).symm
      refine (congrArg (Subst.append (n := ps.length + 1) σ
        (Args.toSubst (ps := p :: ps) (.cons t ts))) e).trans ?_
      exact (Subst.append_liftN_empty (n := ps.length + 1) σ
        (Args.toSubst (ps := p :: ps) (.cons t ts)) (Var.weakenN (Γ := [.var]) ps.length .zero)).trans
        (Subst.append_weakenN (Subst.closedSingle t) ts.toSubst .zero)
    | succ y => exact Subst.append_weakenN (n := ps.length + 1) σ _ y
  · refine Eq.trans ?_ (Subst.append_liftN_empty (Γ := .var :: Γ) _ _ z).symm
    have e : (Ren.liftN ps.length (Ren.empty (Γ := .var :: Γ)) z :
        Var (Γ.extend (ps.length + 1)) a) =
        Ren.liftN (ps.length + 1) (Ren.empty (Γ := Γ)) (Ren.liftN ps.length (Ren.empty (Γ := [.var])) z) :=
      (Ren.liftN_comp_of ps.length (α₁ := Ren.lift Ren.empty) (α₂ := Ren.empty)
        (α₃ := Ren.empty) (fun y => nomatch y) z).symm
    refine (congrArg (Subst.append (n := ps.length + 1) σ
      (Args.toSubst (ps := p :: ps) (.cons t ts))) e).trans ?_
    exact (Subst.append_liftN_empty (n := ps.length + 1) σ
      (Args.toSubst (ps := p :: ps) (.cons t ts))
      (Ren.liftN ps.length (Ren.empty (Γ := [.var])) z)).trans
      (Subst.append_liftN_empty (Subst.closedSingle t) ts.toSubst z)

-- ADE: none.
/-- `(σ, E) ∈ ®_H(Γ, γ)` and `t̄ ®_H^{g} b̄ : Θ[σ]` give `((σ, t̄), b̄ʳ ++ E) ∈ ®_H(Γ, Θ; γ • g)`: a
closed substitution of a context, followed by arguments of a telescope related to their addresses at
the grades `g`, stands for the context extended by the telescope, its variables at the grades `g`,
with the addresses of the arguments, the last one first, before those of the context. -/
theorem RunsAsSubst.append {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap} :
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context 0 Γ) → (Θ : Telescope 0 Γ ps) →
      {γ : GradeVector Γ.length} → {g : Nat → Grade} → {σ : Subst 0 [] Γ} → {E : List Nat} →
      {ts : Args 0 [] ps} → {bs : List Nat} → RunsAsSubst sig ι P H ctx γ σ E →
      RunsAsArgs sig ι P H g ts bs (Θ.subst σ) →
      RunsAsSubst sig ι P H (ctx.append Θ) (γ.extendGrades g ps) (Subst.append σ ts.toSubst)
        (bs.reverse ++ E)
  | _, [], _, .nil, _, _, _, _, .nil, [], hσ, _ => hσ
  | _, [], _, .nil, _, _, _, _, .nil, _ :: _, _, h => (h : False).elim
  | _, _ :: _, _, .cons _ _ _ _, _, _, _, _, .cons _ _, [], _, h => (h : False).elim
  | Γ, p :: ps, ctx, .cons _ _ A Θ, γ, g, σ, E, .cons t ts, b :: bs, hσ, h => by
    obtain ⟨ht, hts⟩ := h
    have hσ₁ : RunsAsSubst sig ι P H (ctx.var A) (γ ∙ g 0)
        (Subst.append (n := 1) σ (Subst.closedSingle t)) (b :: E) :=
      ⟨b, E, rfl, hσ, ht⟩
    have hΘ := Telescope.subst_lift_single σ t Θ
    have ih := RunsAsSubst.append (ctx.var A) Θ hσ₁ (hΘ ▸ hts)
    rw [Subst.append_cons, List.reverse_cons, List.append_assoc]
    exact ih

end Sic.Core
