module

public import Sic.Core.Evaluation.Heap

/-!
# Data at Run Time

The runs of the data of annex 19 of RFC 36, for the recursor on the term of a skeleton, which is
data: data evaluates in every environment and heap, reading no cell.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

mutual

/-- Data evaluates, at every weight, in every environment and heap, to a value in a heap that
extends it, reading no cell. -/
theorem Target.IsData.eval (P : Program) {n : Nat} {M : Target n} (h : M.IsData)
    (ϖ : Multiplicity) (H : Heap) (E : List Nat) :
    ∃ a H', Eval P ϖ H E M a H' [] ∧ H.Extends H' :=
  match h with
  | .erased => ⟨_, _, .erased, List.prefix_append _ _⟩
  | .ctor hs =>
    have ⟨_, _, hM, hH⟩ := Targets.IsData.eval P hs ϖ H E
    ⟨_, _, .ctor hM, hH.trans (List.prefix_append _ _)⟩

/-- Terms that are data evaluate, at every weight, in every environment and heap, to values in a
heap that extends it, reading no cell. -/
theorem Targets.IsData.eval (P : Program) {n : Nat} {Ms : Targets n} (h : Ms.IsData)
    (ϖ : Multiplicity) (H : Heap) (E : List Nat) :
    ∃ as H', EvalAll P ϖ H E Ms as H' [] ∧ H.Extends H' :=
  match h with
  | .nil => ⟨_, _, .nil, List.prefix_refl _⟩
  | .cons (π := π) hM hs =>
    have ⟨_, H₁, hM', hH₁⟩ := Target.IsData.eval P hM (ϖ * π) H E
    have ⟨_, _, hs', hH₂⟩ := Targets.IsData.eval P hs ϖ H₁ E
    ⟨_, _, .cons hM' hs', hH₁.trans hH₂⟩

end

end Sic.Core
