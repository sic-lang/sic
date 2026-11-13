module

public import Sic.Core.RunTime.Relation

/-!
# Subsumption of the Validity at Run Time

A term valid at run time with grades `γ` is valid with any grades `δ ≤ᶜ γ`, as the rule `sub` of the
usage gives a term the grades lower than its uses: a variable whose grade in `δ` is in `S^{11ᵐ}` has
its grade in `γ` in `S^{11ᵐ}` too, since this set holds every grade above one of its grades, so that
the addresses that stand for a substitution as `δ` requires stand for it as `γ` requires.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- Addresses that stand for a substitution as the grades `δ` require stand for it as any grades
`γ` require that count at run time only variables that `δ` counts. -/
theorem RunsAsSubst.of_counted {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap} :
    {Γ : Scope} → (ctx : Context 0 Γ) → {γ δ : GradeVector Γ.length} → {σ : Subst 0 [] Γ} →
    {E : List Nat} → (∀ x, γ x ∉ Mode.oneOne.erased → δ x ∉ Mode.oneOne.erased) →
    RunsAsSubst sig ι P H ctx δ σ E → RunsAsSubst sig ι P H ctx γ σ E
  | _, .empty, _, _, _, _, _, h => h
  | _, .var ctx _, _, _, _, _, hc, h => by
    obtain ⟨a, E', hE, hs, hx⟩ := h
    exact ⟨a, E', hE, RunsAsSubst.of_counted ctx (fun x => hc x.succ) hs, fun hγ => hx (hc 0 hγ)⟩
  | _, .secondOrder .., _, _, _, _, _, h => h

-- ADE: none.
/-- Arguments related to addresses at a telescope as the grades `g` require are related to them as
any grades `g'` require that count at run time only positions that `g` counts. -/
theorem RunsAsArgs.of_counted {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap} :
    {ps : List Parameter} → {g g' : Nat → Grade} → {ts : Args 0 [] ps} → {bs : List Nat} →
      {Θ : Telescope 0 [] ps} → (∀ l, g' l ∉ Mode.oneOne.erased → g l ∉ Mode.oneOne.erased) →
      RunsAsArgs sig ι P H g ts bs Θ → RunsAsArgs sig ι P H g' ts bs Θ
  | [], _, _, .nil, [], .nil, _, h => h
  | [], _, _, .nil, _ :: _, .nil, _, h => (h : False).elim
  | _ :: _, _, _, .cons _ _, [], .cons _ _ _ _, _, h => (h : False).elim
  | _ :: _, _, _, .cons _ _, _ :: _, .cons _ _ _ _, hg, h =>
    ⟨fun hg' => h.1 (hg 0 hg'), RunsAsArgs.of_counted (fun l => hg (l + 1)) h.2⟩

-- ADE: none, a step of `subsumption-▸⊩ʳ∷[]-≤`.
/-- Addresses that stand for a substitution as the grades `δ` require stand for it as any grades
`γ` above `δ` require. -/
theorem RunsAsSubst.of_le {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {Γ : Scope} (ctx : Context 0 Γ) {γ δ : GradeVector Γ.length} {σ : Subst 0 [] Γ}
    {E : List Nat} (hle : δ ≤ᶜ γ) : RunsAsSubst sig ι P H ctx δ σ E →
      RunsAsSubst sig ι P H ctx γ σ E :=
  RunsAsSubst.of_counted ctx fun x hγ hδ =>
    hγ ((Mode.erasesUncounted .oneOne).le _ _ (hle x) hδ)

-- ADE: `subsumption-▸⊩ʳ∷[]-≤`, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
/-- A term valid at run time with the grades `γ` is valid with any grades `δ ≤ᶜ γ`.
RFC: `\mathsf{sub}^{\circledR}` -/
theorem RunValid.sub {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ δ : GradeVector Γ.length} {t A : Term 0 Γ}
    (hle : δ ≤ᶜ γ) (h : RunValid sig ι P hΓ ctx γ t A) : RunValid sig ι P hΓ ctx δ t A :=
  fun κ σ H E V hσ hEV hV => h κ σ H E V hσ hEV (RunsAsSubst.of_le ctx hle hV)

end Sic.Core
