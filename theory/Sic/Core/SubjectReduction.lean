module

public import Sic.Core.Reduction
import Sic.Core.Injectivity
import Sic.Core.Inversion

/-!
# Subject Reduction

A reduction keeps every type of the term it reduces, not only the type at which it is derived: a
term may have several types that are not equal, since an abstraction does not carry the grade of the
result of its type of functions, so that a reduction at one of them says nothing yet of the others.

## Correspondence with the Formalizations of ADE and of Pujet

The reductions of ADE and of Pujet, as those of `Sic.Core.Reduction`, are derived at a type, which
their proofs only use at that type.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
-- Pujet: none.
/--
A term that reduces at a type reduces to a term of each of its types.

An application reduces its function, which keeps the type of functions that the application gives
it, by induction, and `(β)` substitutes the argument in the body of the abstraction, whose type is
the codomain of every type of functions of the abstraction, by the injectivity of these types.
-/
theorem HasType.termRed (hB : Γ ⊢ t : B) : Γ ⊢ t ⇒ u : A → Γ ⊢ u : B
  | .conv h _ => hB.termRed h
  | .app h _ =>
    have ⟨_, _, _, ht, ha, hC⟩ := hB.inv_app
    .conv (.app (ht.termRed h) ha) hC.symm
  | .beta _ _ _ =>
    have ⟨_, _, _, hf, ha, hC⟩ := hB.inv_app
    have ⟨_, _, _, ht, hPi⟩ := hf.inv_lam
    have ⟨_, _, hA, hBody⟩ := hPi.symm.pi_inj
    have ha' := HasType.conv ha hA.symm
    .conv (ht.instantiate ha') ((hBody.subst (.instantiate ha') ha.wfCon).trans hC.symm)

-- ADE: none.
-- Pujet: none.
/-- A type that reduces is reduced to a term of each type of the type. -/
theorem HasType.typeRedStar (hC : Γ ⊢ A : C) : Γ ⊢ A ⇒* B → Γ ⊢ B : C
  | .refl _ => hC
  | .step (.univ h) hs => (hC.termRed h).typeRedStar hs

end Sic.Core
