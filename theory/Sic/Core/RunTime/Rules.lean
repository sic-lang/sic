module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.RunTime.Properties
import Sic.Core.RunTime.Computation
import Sic.Core.Substitution.Closed

/-!
# Validity at Run Time of the Rules

The cases of the fundamental lemma of annex 20 of RFC 36 that need no induction on a declaration:
each lemma states that a term of the form of a rule of the typing is valid at run time,
`Σ; γ; Γ ⊨^® t : A`, from the meaning of its premises and from the validity at run time of its
subterms, so that the fundamental lemma, which reads the judgments, only puts them together.

A term of a sort, a type or a proposition, is erased, and related to every address, as the meaning
says, since its type computes to a sort; a constant is evaluated in the program, without the
addresses of the variables, as a closed term, so that the program that realizes its closed instances
realizes it in every context; and a term valid at run time at a type is valid at every type equal to
it, as the meaning of its typing says.

ADE prove these cases in `Graded/Erasure/LogicalRelation/Fundamental.agda` and in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, by recursion on the typing, with the validity of the
logical relation of the typing as an argument; the cases here are lemmas on the meaning, and the
recursion on the typing is in `Fundamental`, since the relation of run time reads no judgment.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Sorts -/

-- ADE: none.
/-- The relation of run time of a sort relates every term to every address. -/
theorem HasRun.sort {sig : Signature} {ι : Interpretation} {P : Program} (κ : Universe 0) :
    HasRun sig ι P (.sort κ) fun _ _ _ => True := by
  obtain ⟨q, l⟩ := κ
  cases q with
  | type => exact .univ (l.closedValue + 1) (levelRel_run_iff.2 (.univ rfl rfl))
  | prop => exact .univ (l.closedValue + 1) (levelRel_run_iff.2 (.prop rfl rfl))

-- ADE: `U/Levelᵣ`, the relation of the universes, in `Graded/Erasure/LogicalRelation.agda`.
/-- A closed term that computes is related to every address at a sort. -/
theorem RunsAs.sort {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t v : Term 0 []} {a : Nat} (κ : Universe 0) (ht : Computesι sig ι t v) :
    RunsAs sig ι P H t a (.sort κ) :=
  ⟨_, Computes.sort _ κ, .inr ⟨_, HasRun.sort κ, v, ht, trivial⟩⟩

-- ADE: `Uʳ`, in `Graded/Erasure/LogicalRelation/Fundamental/Universe.agda`, for the universes.
/-- A term of a sort that its erasure replaces by `↯` is valid at run time, at every grades: `↯` is
allocated, and the term, which computes as the meaning of its type says, is related to its address,
as every term of a sort. -/
theorem RunValid.erased {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ : GradeVector Γ.length} {t : Term 0 Γ}
    {κ : Universe 0} (ht : ValidTermΓ sig ι ctx t (.sort κ))
    (he : t.erase sig Mode.oneOne.erased hΓ = .erased) : RunValid sig ι P hΓ ctx γ t (.sort κ) := by
  intro σ H E hσ _
  obtain ⟨-, hcl, -⟩ := ht.2 σ σ hσ
  obtain ⟨_, v, -, -, hc, hv, -⟩ := hcl not_computesToProp_sort
  refine ⟨H.length, H ++ [.erased], he ▸ .erased, List.prefix_append _ _, RunsAs.sort κ hv⟩

/-! ## Constants -/

-- ADE: the case `defn` of `fundamental′`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- A constant valid at run time at a closed type in the empty context is valid at run time in every
context, at this type: its erasure evaluates its body in the program, without the addresses of the
variables. -/
theorem RunValid.const {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ : GradeVector Γ.length} {f : Name}
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} {γ₀ : GradeVector 0}
    {A : Term 0 []} (h : RunValid sig ι P .nil .empty γ₀ (.const f qs ls ps) A) :
    RunValid sig ι P hΓ ctx γ (.const f qs ls ps) A.weakenClosed := by
  intro σ H E _ _
  let σ₀ : Subst 0 [] [] := fun x => nomatch x
  have hσ₀ : ∀ t : Term 0 [], t.subst σ₀ = t := fun t => by
    have h := Term.subst_weakenClosed σ₀ t
    rwa [Term.weakenClosed_nil] at h
  obtain ⟨a, H', hev, hH, ht⟩ := h σ₀ H [] (by rw [EqSubst]; trivial) rfl
  rw [hσ₀, hσ₀] at ht
  cases hev with
  | const hP hM =>
    refine ⟨a, H', .const hP hM, hH, ?_⟩
    rw [Term.subst_weakenClosed]
    exact ht

/-! ## Conversion -/

-- ADE: `conv-▸⊩ʳ∷`, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
/-- A term valid at run time at a type is valid at run time at every type equal to it, when it is a
term of the type. -/
theorem RunValid.conv {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ : GradeVector Γ.length} {t A B : Term 0 Γ}
    (ht : ValidTermΓ sig ι ctx t A) (hAB : ValidEqTypeΓ sig ι ctx A B)
    (h : RunValid sig ι P hΓ ctx γ t A) : RunValid sig ι P hΓ ctx γ t B := by
  intro σ H E hσ hE
  obtain ⟨a, H', hev, hH, hrun⟩ := h σ H E hσ hE
  obtain ⟨hd, hAB'⟩ := hAB.2 σ σ hσ
  exact ⟨a, H', hev, hH, hrun.conv hd (ht.2 σ σ hσ).2 hAB'⟩

end Sic.Core
