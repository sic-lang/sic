module

public import Sic.Core.Usage

/-!
# Erasure

The erasure of RFC 24, which compiles a term to an untyped target language, removing the parts
without use: the extraction `t•` removes the positions whose grade has no use at run time,
`run(p) = 0`, and the ghost program `t°` those whose grade has no use at all, `p = 𝟘`.
The two erasures are one translation, parametrized by the grades it erases.
The target language has variables, the constants with their grades, `c.{p̄}`, and a value `↯` that
stands for what was erased; the kinds of declarations add the forms of their terms, and the
positions of their rules of usage.

The translation is defined on the terms in a scope of variables only, which the hypothesis
`Γ.FirstOrder` states: the programs are closed, and the binders of the kinds of declarations
declare variables, while a second-order variable only appears in the contexts in which the
declarations are checked.
A variable thus has no arguments, and the target language has no second-order variables.
The core has no position of its own: the terms that it gives are types, variables and constants.

ADE extract the terms of their type theory, in which the definitions are names, and replace each
erased part by `↯` or by a term that does not terminate, as its strictness requires.
-/

@[expose] public section

namespace Sic.Core

/-- The scope `Γ` declares variables only, whose telescopes are empty. -/
def Scope.FirstOrder (Γ : Scope) : Prop := ∀ ps ∈ Γ, ps = []

-- ADE: none.
/-- A scope of variables extended by a variable is a scope of variables. -/
theorem Scope.FirstOrder.cons {Γ : Scope} (hΓ : Γ.FirstOrder) : Scope.FirstOrder ([] :: Γ) := by
  intro ps hps
  cases hps with
  | head => rfl
  | tail _ h => exact hΓ ps h

-- ADE: `Term`, in `Graded/Erasure/Target.agda`.
/-- A term of the target language over `n` variables. -/
inductive Target (n : Nat) : Type where
  /-- A variable. -/
  | var (x : Fin n)
  /-- `c.{p̄}`: the definition or constant `c` at the grades `p̄`. -/
  | const (c : Name) (ps : List Grade)
  /-- `↯`, what was erased. -/
  | erased

-- ADE: `HasX`, in `Graded/Erasure/Target.agda`.
/-- The variable `x` occurs in the term of the target language. -/
inductive Target.Occurs {n : Nat} (x : Fin n) : Target n → Prop where
  /-- The variable `x` itself. -/
  | var : Occurs x (.var x)

-- ADE: `erase′`, in `Graded/Erasure/Extraction.agda`.
/--
The erasure of a term of a scope of variables, which erases the positions whose grade `p` has
`erases p`: `U_l`, `Ω_l` and the instances `T` are erased, a variable is kept, and a definition or a
constant `c.{s̄; l̄; p̄}` keeps its grades, `c.{p̄}`.
The core has no position, so that the grades it erases and the hypothesis `Γ.FirstOrder`, under
which the arguments of a variable are none, are used by the clauses of the kinds of declarations
only.
-/
def Term.erase (_erases : Grade → Bool) {k : Nat} {Γ : Scope} (_hΓ : Γ.FirstOrder) :
    Term k Γ → Target Γ.length
  | .var x _ => .var x.toFin
  | .sort _ => .erased
  | .const c _ _ ps => .const c ps
  | .inst .. => .erased

-- ADE: none.
/-- The erasure of a term of the target language, which erases the positions whose grade `p` has
`erases p`: the target language of the core has no position, so that it keeps every term. -/
def Target.erase (_erases : Grade → Bool) {n : Nat} : Target n → Target n
  | .var x => .var x
  | .const c ps => .const c ps
  | .erased => .erased

/-- The grades without use at run time, `run(p) = 0`, which the extraction erases. -/
def Grade.unusedAtRun (p : Grade) : Bool := decide (p.run = .zero)

/-- The grades without any use, `p = 𝟘`, which the ghost program erases. -/
def Grade.unused (p : Grade) : Bool := decide (p = Grade.zero)

-- ADE: `erase`, in `Graded/Erasure/Extraction.agda`.
/-- `t•`, the extraction of a term. -/
abbrev Term.extract {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (t : Term k Γ) : Target Γ.length :=
  t.erase Grade.unusedAtRun hΓ

-- ADE: none.
/-- `t°`, the ghost program of a term. -/
abbrev Term.ghost {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (t : Term k Γ) : Target Γ.length :=
  t.erase Grade.unused hΓ

/-! ## Properties -/

-- ADE: none.
/-- `(•_∘)`: the extraction of a term is the extraction of its ghost program. -/
theorem Term.extract_ghost {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (t : Term k Γ) :
    t.extract hΓ = (t.ghost hΓ).erase Grade.unusedAtRun := by
  cases t <;> rfl

/-- A grade below a grade that has a use at run time has a use at run time. -/
theorem Grade.run_zero_of_le : ∀ p q : Grade, p ≤ q → p.run = .zero → q.run = .zero := by decide

/-- A grade below a grade that has a use has a use. -/
theorem Grade.eq_zero_of_le : ∀ p q : Grade, p ≤ q → p = Grade.zero → q = Grade.zero := by decide

/-- A sum of grades without use at run time adds two grades without use at run time. -/
theorem Grade.run_zero_of_add : ∀ p q : Grade, (p + q).run = .zero → p.run = .zero := by decide

/-- A sum of grades without use adds two grades without use. -/
theorem Grade.eq_zero_of_add : ∀ p q : Grade, p + q = Grade.zero → p = Grade.zero := by decide

-- ADE: `erased-hasX`, in `Graded/Erasure/Extraction/Properties/Usage.agda`.
/--
`(absent_•)`: a variable without use at run time does not occur in the extraction of a term checked
in the mode `𝟙𝟙ᵐ` of run time; in an erased mode, the term itself has no use at run time, and a
variable `x` checked in the mode `𝟘𝟙ᵐ` uses itself with the grade `⌜𝟘𝟙ᵐ⌝`, without use at run time,
while `x• = x`.
-/
theorem Usage.absent_extract {sig : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length}
    {m : Mode} {t : Term k Γ} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    Usage sig γ m t → m = .oneOne → (γ x).run = .zero → ¬ (t.extract hΓ).Occurs x
  | .var (x := y) (δ := δ) _, hm, hx, ho => by
    cases ho
    subst hm
    have h := Grade.run_zero_of_add _ (δ y.toFin) (by
      simpa [GradeVector.add, GradeVector.update_self] using hx)
    exact absurd h (by decide)
  | .const .., _, _, ho => nomatch ho
  | .sort, _, _, ho => nomatch ho
  | .sub h hle, hm, hx, ho => h.absent_extract hΓ hm (Grade.run_zero_of_le _ _ (hle x) hx) ho

-- ADE: none.
/--
`(absent_∘)`: a variable without use does not occur in the ghost program of a term checked in a mode
other than `𝟘𝟘ᵐ`; in the mode `𝟘𝟘ᵐ`, a variable `x` uses itself with the grade `𝟘`, while `x° = x`.
-/
theorem Usage.absent_ghost {sig : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length}
    {m : Mode} {t : Term k Γ} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    Usage sig γ m t → m ≠ .zeroZero → γ x = Grade.zero → ¬ (t.ghost hΓ).Occurs x
  | .var (x := y) (δ := δ) _, hm, hx, ho => by
    cases ho
    have h := Grade.eq_zero_of_add _ (δ y.toFin) (by
      simpa [GradeVector.add, GradeVector.update_self] using hx)
    cases m <;> first | exact hm rfl | exact absurd h (by decide)
  | .const .., _, _, ho => nomatch ho
  | .sort, _, _, ho => nomatch ho
  | .sub h hle, hm, hx, ho => h.absent_ghost hΓ hm (Grade.eq_zero_of_le _ _ (hle x) hx) ho

end Sic.Core
