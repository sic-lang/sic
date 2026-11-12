module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.Levels

/-!
# Levels of the Relation of Run Time

The relation of run time of annex 20 of RFC 36 reads the levels of its type by their values, as the
meaning does: two types that differ only by levels of the same values compute to canonical types
that differ in the same way, which the graph of run time does not tell apart, so that a term related
to an address at one is related to it at the other, and so are the arguments of two telescopes that
differ in the same way.

ADE have levels as terms, and no counterpart is needed there.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- A term related to an address at a type is related to it at every type equal to it up to its
levels. -/
theorem RunsAs.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t : Term 0 []} {a : Nat} {A A' : Term 0 []} (hAA : Term.LevelEquiv A A') :
    RunsAs sig ι P H t a A → RunsAs sig ι P H t a A'
  | ⟨_, hA, h⟩ => by
    obtain ⟨v', hA', hv⟩ := Computes.levelEquiv hA hAA
    rcases h with hp | ⟨R, hR, ht⟩
    · exact ⟨v', hA', .inl (hp.levelEquiv hv)⟩
    · exact ⟨v', hA', .inr ⟨R, hR.levelEquiv hv, ht⟩⟩

-- ADE: none.
/-- Arguments related to addresses at a telescope are related to them at every telescope equal to
it up to its levels. -/
theorem RunsAsArgs.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap} :
    {ps : List Parameter} → {g : Nat → Grade} → {ts : Args 0 [] ps} → {bs : List Nat} →
    {Θ Θ' : Telescope 0 [] ps} → Telescope.LevelEquiv Θ Θ' → RunsAsArgs sig ι P H g ts bs Θ →
      RunsAsArgs sig ι P H g ts bs Θ'
  | [], _, .nil, [], .nil, .nil, .nil, h => h
  | _ :: _, _, .cons _ _, _ :: _, .cons _ _ _ _, .cons _ _ _ _, .cons _ _ hA hΘ, h => by
    obtain ⟨ht, hts⟩ := h
    exact ⟨fun hp => (ht hp).levelEquiv hA,
      RunsAsArgs.levelEquiv (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl _))) hts⟩

end Sic.Core
