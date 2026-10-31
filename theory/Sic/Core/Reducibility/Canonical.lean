module

public import Sic.Core.Reducibility.Hidden
import Sic.Core.Reducibility.Uniqueness

/-!
# Canonical Interpretation

The interpretation of a type that the hidden equalities describe: it equates a type to the type
when the interpretation of a proof of its reducibility does, and two terms of the type when they are
reducibly equal at it.
The interpretation of a reducible type is this canonical interpretation, since it is unique, so that
a proof that only shows that a type has some interpretation still gives its interpretation, as a
function of the type, which the constructor `LogRel.pi` asks for its domain and its codomain.

## Correspondence with the Formalizations of ADE and of Pujet

ADE and Pujet have no such interpretation: their proofs of reducibility are data, from which a
function computes the interpretation, where the existence of an interpretation is a proposition
here, from which Lean extracts no interpretation without the axiom of choice.
Since an interpretation is made of predicates, the uniqueness of the interpretation of a reducible
type is enough to define it without that axiom.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

/--
The canonical interpretation of the type `A` at the level `l`: the types that the interpretation of
a proof of its reducibility equates to it, and the terms reducibly equal at it.
-/
def Interpretation.canonical (Γ : Con k n) (l : Nat) (A : Term k n) : Interpretation k n where
  eqType B := ∃ P, (Γ ⊩⟨l⟩ A ▸ P) ∧ P.eqType B
  eqTerm t u := Γ ⊩⟨l⟩ t ≡ u : A

/-- The interpretation of a reducible type is its canonical interpretation. -/
theorem LogicalRelation.eq_canonical (h : Γ ⊩⟨l⟩ A ▸ P) :
    P = Interpretation.canonical Γ l A := by
  have hP : ∀ {Q}, (Γ ⊩⟨l⟩ A ▸ Q) → Q = P := fun hQ => hQ.unique h
  have hType : P.eqType = (Interpretation.canonical Γ l A).eqType :=
    funext fun _ => propext ⟨fun hB => ⟨_, h, hB⟩, fun ⟨_, hQ, hB⟩ => hP hQ ▸ hB⟩
  have hTerm : P.eqTerm = (Interpretation.canonical Γ l A).eqTerm :=
    funext fun _ => funext fun _ =>
      propext ⟨fun htu => ⟨_, h, htu⟩, fun ⟨_, hQ, htu⟩ => hP hQ ▸ htu⟩
  calc P = ⟨P.eqType, P.eqTerm⟩ := rfl
    _ = _ := by rw [hType, hTerm]

end Sic.Core.Reducibility
