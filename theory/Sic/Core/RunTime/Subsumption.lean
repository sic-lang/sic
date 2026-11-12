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

-- ADE: none, a step of `subsumption-▸⊩ʳ∷[]-≤`.
/-- Addresses that stand for a substitution as the grades `δ` require stand for it as any grades
`γ` above `δ` require. -/
theorem RunsAsSubst.of_le {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap} :
    {Γ : Scope} → (ctx : Context 0 Γ) → {γ δ : GradeVector Γ.length} → {σ : Subst 0 [] Γ} →
    {E : List Nat} → δ ≤ᶜ γ → RunsAsSubst sig ι P H ctx δ σ E → RunsAsSubst sig ι P H ctx γ σ E
  | _, .empty, _, _, _, _, _, h => h
  | _, .var ctx _, _, _, _, _, hle, h => by
    obtain ⟨a, E', hE, hs, hx⟩ := h
    exact ⟨a, E', hE, RunsAsSubst.of_le ctx (fun x => hle x.succ) hs,
      fun hγ => hx fun hδ => hγ ((Mode.erasesUncounted .oneOne).le _ _ (hle 0) hδ)⟩
  | _, .secondOrder .., _, _, _, _, _, h => h

-- ADE: `subsumption-▸⊩ʳ∷[]-≤`, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
/-- A term valid at run time with the grades `γ` is valid with any grades `δ ≤ᶜ γ`.
RFC: `\mathsf{sub}^{\circledR}` -/
theorem RunValid.sub {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ δ : GradeVector Γ.length} {t A : Term 0 Γ}
    (hle : δ ≤ᶜ γ) (h : RunValid sig ι P hΓ ctx γ t A) : RunValid sig ι P hΓ ctx δ t A :=
  fun σ H E hσ hE => h σ H E hσ (RunsAsSubst.of_le ctx hle hE)

end Sic.Core
