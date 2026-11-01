module

public import Sic.Core.Reduction
public import Sic.Core.Usage
import Sic.Core.UsageSubstitution

/-!
# Usage Reduction

A reduction keeps every usage of the term it reduces: a term well used with the vector `γ` reduces
to a term well used with `γ`, so that the usage checked of a term still holds after each step of its
reduction.
The converse does not hold, since a reduction may drop an argument with its uses.

## Correspondence with the Formalization of ADE

ADE prove the same lemmas, for the reductions of their richer syntax, and their `(β)` reduces an
application of grade `p` of an abstraction of grade `p'` when `p = p'`, which the syntax of the
reduction requires here.
-/

@[expose] public section

namespace Sic.Core

open GradeVector

-- ADE: `usagePresTerm`, in `Graded/Reduction.agda`.
/--
A reduction keeps the usage of a term.

An application reduces its function, whose usage is kept by induction, and `(β)` instantiates the
variable of the body of the abstraction by the argument, which `Usage.instantiate` counts as
`(∘_m)` counts the argument.
-/
theorem Usage.termRed (ht : γ ▶[m] t) : Γ ⊢ t ⇒ u : A → γ ▶[m] u
  | .conv h _ => ht.termRed h
  | .app h _ =>
    have ⟨_, _, hf, ha, hγ⟩ := ht.inv_app
    .sub (.app (hf.termRed h) ha) hγ
  | .beta _ _ _ =>
    have ⟨_, _, hf, ha, hγ⟩ := ht.inv_app
    have ⟨_, hb, hδ⟩ := hf.inv_lam
    .sub (hb.instantiate ha) (le_trans hγ (add_mono hδ (le_refl _)))

-- ADE: `usagePres*Term`, in `Graded/Reduction.agda`.
/-- Any number of reductions keep the usage of a term. -/
theorem Usage.termRedStar (ht : γ ▶[m] t) : Γ ⊢ t ⇒* u : A → γ ▶[m] u
  | .refl _ => ht
  | .step h hs => (ht.termRed h).termRedStar hs

-- ADE: `usagePres`, in `Graded/Reduction.agda`.
/-- A reduction of a type keeps its usage. -/
theorem Usage.typeRed (hA : γ ▶[m] A) : Γ ⊢ A ⇒ B → γ ▶[m] B
  | .univ h => hA.termRed h

-- ADE: `usagePres*`, in `Graded/Reduction.agda`.
/-- Any number of reductions of a type keep its usage. -/
theorem Usage.typeRedStar (hA : γ ▶[m] A) : Γ ⊢ A ⇒* B → γ ▶[m] B
  | .refl _ => hA
  | .step h hs => (hA.typeRed h).typeRedStar hs

end Sic.Core
