module

public import Sic.Core.Reducibility.LogicalRelation

/-!
# Reduction

The logical relation is closed under weak head expansion: a type that reduces to a reducible type is
reducible, with the same interpretation, and the interpretation of a type equates the types and the
terms that reduce to the ones it equates.

## Correspondence with the Formalizations of ADE and of Pujet

| Theorem | Theorem of ADE, in `Definition/LogicalRelation/Properties/Reduction.agda` | Of Pujet, in `Definition/LogicalRelation/Properties/Reduction.agda` |
| --- | --- | --- |
| `LogicalRelation.expand` | `redSubst*` | the same |
| `LogicalRelation.expand_eqType` | none | none |
| `LogicalRelation.expand_eqTerm` | `redSubst*Term` | the same |

The interpretation of a type only mentions its weak head normal form, so that the expanded type
keeps the interpretation of its reduct, where ADE and Pujet build a new proof of reducibility and
show that it equates the two types, which `LogicalRelation.refl_eqType` gives here.
`LogicalRelation.expand_eqTerm` expands both terms of an equality, where ADE and Pujet expand a
reducible term to a term equal to it, the case of a term `u` that reduces to itself.
Their `redSubst` and `redSubstTerm`, for a single step, are the case of a reduction of one step.
-/

@[expose] public section

namespace Sic.Core.Reducibility

variable [EqualityRelation]

section

variable {l : Nat} {lower : ∀ l' < l, Relation k}

/-- A type that reduces to a reducible type is reducible, with the same interpretation. -/
theorem LogRel.expand (hAB : Γ ⊢ A ⇒* B) : LogRel l lower Γ B P → LogRel l lower Γ A P
  | .univ hL hB => .univ hL (hAB.trans hB)
  | .ne hB hN hNN => .ne (hAB.trans hB) hN hNN
  | .pi hB hPi PF PG hF hG hGext => .pi (hAB.trans hB) hPi PF PG hF hG hGext

/--
The interpretation of a reducible type equates to it the types that reduce to the types it equates.
-/
theorem LogRel.expand_eqType (h : LogRel l lower Γ A P) (hB : Γ ⊢ B ⇒* B') (hP : P.eqType B') :
    P.eqType B :=
  match h, hP with
  | .univ .., ⟨_, hB', hL⟩ => ⟨_, hB.trans hB', hL⟩
  | .ne .., ⟨_, hB', hM, hNM⟩ => ⟨_, hB.trans hB', hM, hNM⟩
  | .pi .., ⟨_, _, hB', hPi, hF, hG⟩ => ⟨_, _, hB.trans hB', hPi, hF, hG⟩

end

/-- A type that reduces to a reducible type is reducible, with the same interpretation. -/
theorem LogicalRelation.expand (hAB : Γ ⊢ A ⇒* B) (h : Γ ⊩⟨l⟩ B ▸ P) : Γ ⊩⟨l⟩ A ▸ P :=
  unfold.mpr ((unfold.mp h).expand hAB)

/--
The interpretation of a reducible type equates to it the types that reduce to the types it equates.
-/
theorem LogicalRelation.expand_eqType (h : Γ ⊩⟨l⟩ A ▸ P) (hB : Γ ⊢ B ⇒* B') (hP : P.eqType B') :
    P.eqType B :=
  (unfold.mp h).expand_eqType hB hP

/--
The interpretation of a reducible type equates two terms that reduce to two terms it equates.

Each reduction to a weak head normal form of the interpretation starts with the reduction of the
term, at the weak head normal form of the type, to which the type reduces.
Two types of a universe are also reducible and equated by the expansion of the types, at the level
of the universe.
-/
theorem LogicalRelation.expand_eqTerm (h : Γ ⊩⟨l⟩ A ▸ P) (ht : Γ ⊢ t ⇒* t' : A)
    (hu : Γ ⊢ u ⇒* u' : A) (htu : P.eqTerm t' u') : P.eqTerm t u := by
  rw [LogicalRelation.unfold] at h
  cases h with
  | univ _ hA =>
    obtain ⟨_, _, ht', hu', hA', hB', hAB, _, hP, ⟨_, hQ⟩, hPu⟩ := htu
    have ht := ht.conv hA.typeEq
    have hu := hu.conv hA.typeEq
    have hP := hP.expand ht.univ
    exact ⟨_, _, ⟨ht.trans ht'.1, ht'.2⟩, ⟨hu.trans hu'.1, hu'.2⟩, hA', hB', hAB, _, hP,
      ⟨_, hQ.expand hu.univ⟩, hP.expand_eqType hu.univ hPu⟩
  | ne hA =>
    obtain ⟨_, _, ht', hu', hN, hM, htu⟩ := htu
    exact ⟨_, _, (ht.conv hA.typeEq).trans ht', (hu.conv hA.typeEq).trans hu', hN, hM, htu⟩
  | pi hA =>
    obtain ⟨_, _, hf, hg, hfg, happ⟩ := htu
    exact ⟨_, _, ⟨(ht.conv hA.typeEq).trans hf.1, hf.2⟩, ⟨(hu.conv hA.typeEq).trans hg.1, hg.2⟩,
      hfg, happ⟩

end Sic.Core.Reducibility
