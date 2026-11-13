module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.RunTime.Properties
import Sic.Core.RunTime.Computation
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Substitution

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
  intro σ H E _ hσ _ _
  obtain ⟨-, hcl, -⟩ := ht.2 σ σ hσ
  obtain ⟨_, v, -, -, hc, hv, -⟩ := hcl not_computesToProp_sort
  refine ⟨H.length, H ++ [.erased], [], he ▸ .erased, List.prefix_append _ _, RunsAs.sort κ hv⟩

/-! ## Variables -/

-- ADE: `®∷→®∷◂`, the substitutions at a variable, in `Graded/Erasure/LogicalRelation.agda`.
/-- The addresses `E` that stand for the closed substitution `σ` as the grades `γ` require give the
variable `x : A ∈ Γ`, when its grade is not in `S^{11ᵐ}`, an address to which `σ(x)` is related at
`A[σ]`. -/
theorem RunsAsSubst.varIn {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {Γ : Scope} {ctx : Context 0 Γ} {x : Var Γ .var} {A : Term 0 Γ} (hx : ctx.VarIn x A) :
    ∀ {γ : GradeVector Γ.length} {σ : Subst 0 [] Γ} {E : List Nat},
      RunsAsSubst sig ι P H ctx γ σ E → γ x.toFin ∉ Mode.oneOne.erased →
        ∃ a, E[(x.toFin : Nat)]? = some a ∧ RunsAs sig ι P H (σ x) a (A.subst σ) := by
  induction hx with
  | @zero _ ctx A =>
    intro γ σ E hE hγ
    obtain ⟨a, E', rfl, -, ha⟩ := hE
    rw [Term.subst_weaken]
    exact ⟨a, rfl, ha hγ⟩
  | @succVar _ ctx x A B _ ih =>
    intro γ σ E hE hγ
    obtain ⟨a, E', rfl, hE', -⟩ := hE
    rw [Term.subst_weaken]
    exact ih hE' hγ
  | succSecondOrder => intro _ _ _ hE; exact hE.elim

-- ADE: `fundamental′`, the case `var`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- `(var)` at run time: the variable `x : A ∈ Γ`, whose grade in `γ` is not in `S^{11ᵐ}`, is valid
at run time with the grades `γ`: its erasure is the variable, which reads the cell that the
environment gives it, whose address its closed term is related to. -/
theorem RunValid.var {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ : GradeVector Γ.length} {x : Var Γ .var}
    {A : Term 0 Γ} (hx : ctx.VarIn x A) (hγ : γ x.toFin ∉ Mode.oneOne.erased) :
    RunValid sig ι P hΓ ctx γ (.var₀ x) A := by
  intro σ H E V _ hEV hV
  obtain ⟨a, ha, hrun⟩ := hV.varIn hx hγ
  obtain ⟨c, π, hc, hcell⟩ := hEV.getElem? ha
  exact ⟨a, H, [c], .var hc hcell, List.prefix_refl H, hrun⟩

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
  intro σ H E _ _ _ _
  let σ₀ : Subst 0 [] [] := fun x => nomatch x
  have hσ₀ : ∀ t : Term 0 [], t.subst σ₀ = t := fun t => by
    have h := Term.subst_weakenClosed σ₀ t
    rwa [Term.weakenClosed_nil] at h
  obtain ⟨a, H', R, hev, hH, ht⟩ := h σ₀ H [] [] (by rw [EqSubst]; trivial) trivial rfl
  rw [hσ₀, hσ₀] at ht
  cases hev with
  | const hP hM =>
    refine ⟨a, H', R, .const hP hM, hH, ?_⟩
    rw [Term.subst_weakenClosed]
    exact ht

/-! ## Arguments of a Telescope

The arguments of a telescope are evaluated in order, each in the heap that the one before it leaves:
an argument of a grade in `S^{11ᵐ}` is erased, `↯` being allocated in its place, and the others are
valid at run time with the grades that they use, which the grades of the arguments count. -/

-- ADE: none.
/-- `(tel_ε▶)` at run time: no argument is valid at run time with the grades `𝟘ᶜ`. -/
theorem RunValidArgs.nil {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} :
    RunValidArgs sig ι P hΓ ctx 𝟘ᶜ (.nil : Args 0 Γ []) .nil :=
  fun _ H _ _ _ _ _ => ⟨[], H, [], .nil, List.prefix_refl H, trivial⟩

-- ADE: none.
/-- `(tel_,▶)` at run time: the arguments `t, t̄` of the telescope `x : A ▶ p, Θ` are valid at run
time with the grades `(p ·ᶜ δ) +ᶜ δ'`, when `t` is valid at run time at `A` with the grades `δ` if
`p` is not in `S^{11ᵐ}`, and `t̄` at `Θ[t / x]` with the grades `δ'`, in a signature whose names are
distinct: the addresses that stand for a substitution as these grades require stand for it as `δ`
requires, when `p` is not in `S^{11ᵐ}`, and as `δ'` requires. -/
theorem RunValidArgs.cons {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {δ δ' : GradeVector Γ.length} {ps : List Parameter}
    {q : Grade} {p : Parameter} {t A : Term 0 Γ} {ts : Args 0 Γ ps}
    {Θ : Telescope 0 (.var :: Γ) ps} (hd : sig.Distinct)
    (ht : p.usage ∉ Mode.oneOne.erased → RunValid sig ι P hΓ ctx δ t A)
    (hts : RunValidArgs sig ι P hΓ ctx δ' ts (Θ.subst₀ (Subst₀.single t))) :
    RunValidArgs sig ι P hΓ ctx ((p.usage ·ᶜ δ) +ᶜ δ') (.cons t ts) (.cons q p A Θ) := by
  intro σ H E V hσ hEV hE
  have hS := Mode.erasesUncounted .oneOne
  have hE' : RunsAsSubst sig ι P H ctx δ' σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  have hΘ := Telescope.subst_subst₀_of (Subst₀.Swaps.single t σ) Θ
  by_cases hp : p.usage ∈ Mode.oneOne.erased
  · obtain ⟨bs, H', R, hevs, hH', hruns⟩ := hts σ (H ++ [.erased]) E V hσ
      (hEV.mono (List.prefix_append _ _)) (hE'.mono hd (List.prefix_append _ _))
    refine ⟨H.length :: bs, H', [] ++ R, ?_, (List.prefix_append _ _).trans hH',
      fun h => absurd hp h, ?_⟩
    · show EvalAll P H E (.cons _ (if p.usage ∈ Mode.oneOne.erased then .erased else _) _) _ _ _
      rw [ite_eq_left hp]
      exact .cons .erased hevs
    · rw [← hΘ]
      exact hruns
  · have hδ : RunsAsSubst sig ι P H ctx δ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
      h (hS.mul _ _ hp (hS.add _ _ h'))) hE
    obtain ⟨a, H₁, R₁, hev, hH₁, hrun⟩ := ht hp σ H E V hσ hEV hδ
    obtain ⟨bs, H', R₂, hevs, hH', hruns⟩ := hts σ H₁ E V hσ (hEV.mono hH₁) (hE'.mono hd hH₁)
    refine ⟨a :: bs, H', R₁ ++ R₂, ?_, hH₁.trans hH', fun _ => hrun.mono hd hH', ?_⟩
    · show EvalAll P H E (.cons _ (if p.usage ∈ Mode.oneOne.erased then .erased else _) _) _ _ _
      rw [ite_eq_right hp]
      exact .cons hev hevs
    · rw [← hΘ]
      exact hruns

/-! ## Conversion -/

-- ADE: `conv-▸⊩ʳ∷`, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
/-- A term valid at run time at a type is valid at run time at every type equal to it, when it is a
term of the type. -/
theorem RunValid.conv {sig : Signature} {ι : Interpretation} {P : Program} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {γ : GradeVector Γ.length} {t A B : Term 0 Γ}
    (ht : ValidTermΓ sig ι ctx t A) (hAB : ValidEqTypeΓ sig ι ctx A B)
    (h : RunValid sig ι P hΓ ctx γ t A) : RunValid sig ι P hΓ ctx γ t B := by
  intro σ H E V hσ hEV hE
  obtain ⟨a, H', R, hev, hH, hrun⟩ := h σ H E V hσ hEV hE
  obtain ⟨hd, hAB'⟩ := hAB.2 σ σ hσ
  exact ⟨a, H', R, hev, hH, hrun.conv hd (ht.2 σ σ hσ).2 hAB'⟩

end Sic.Core
