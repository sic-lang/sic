module

public import Sic.Core.Usage
public import Sic.Set

/-!
# Erasure

The erasure of annex 14 of RFC 36, which compiles a term to an untyped target language: `⌊t⌋_S`
replaces by `↯` the positions of `t` whose grade is in the set `S`, and the set `S^m` of the
grades that a term checked in the mode `m` does not count gives the extraction, `⌊t⌋_{S^{11ᵐ}}`, and
the program that the proofs see, `⌊t⌋_{S^{01ᵐ}}`.
The target language has variables, the constants with their grades, `f.{p̄}`, and a value `↯` that
stands for what was erased; the kinds of declarations add the forms of their terms, and the
positions of their rules of usage.

The translation is defined on the terms in a scope of variables only, which the hypothesis
`Γ.FirstOrder` states: the programs are closed, and the binders of the kinds of declarations
declare variables, while a second-order variable only appears in the contexts in which the
declarations are checked.
A variable thus has no arguments, and the target language has no second-order variables.
The core has no position of its own: the terms that it gives are types, variables and constants,
so that its clauses use neither `S` nor `Γ.FirstOrder`, which the kinds of declarations use.

ADE extract the terms of their type theory, in which the definitions are names, and replace each
erased part by `↯` or by a term that does not terminate, as its strictness requires; they erase the
grade `𝟘` only, in the mode `𝟙ᵐ`, while the erasure here is stated for every set of grades.
-/

@[expose] public section

namespace Sic.Mode

-- ADE: none.
/-- `S^m`: the grades of the positions that a term checked in the mode `m` checks in a more erased
mode, `m ⊙ p ≠ m`, and which it does not count. -/
def erased (m : Mode) : Set Grade := { p | m ⊙ p ≠ m }

instance (m : Mode) : DecidablePred (· ∈ m.erased) :=
  fun p => inferInstanceAs (Decidable (m ⊙ p ≠ m))

-- ADE: none.
/-- The three sets `S^m`: the mode `11ᵐ` of run time does not count the grades without use at run
time, the mode `01ᵐ` the grade `00ᵖ`, and the mode `00ᵐ`, which counts no use, erases nothing. -/
theorem erased_values :
    (∀ p, p ∈ oneOne.erased ↔ p.run = .zero) ∧
    (∀ p, p ∈ zeroOne.erased ↔ p = Grade.zero) ∧
    (∀ p, p ∉ zeroZero.erased) := by
  decide

end Sic.Mode

namespace Sic.Core

/-- The scope `Γ` declares variables only, and no second-order variable. -/
def Scope.FirstOrder (Γ : Scope) : Prop := ∀ e ∈ Γ, e = .var

-- ADE: `Term`, in `Graded/Erasure/Target.agda`.
/-- A term `M` of the target language over `n` variables. -/
inductive Target (n : Nat) : Type where
  /-- A variable. -/
  | var (x : Fin n)
  /-- `f.{p̄}`: the constant `f` at the grades `p̄`. -/
  | const (f : Name) (ps : List Grade)
  /-- `↯`, what was erased. -/
  | erased

-- ADE: `HasX`, in `Graded/Erasure/Target.agda`.
/-- The variable `x` occurs in the term of the target language. -/
inductive Target.Occurs {n : Nat} (x : Fin n) : Target n → Prop where
  /-- The variable `x` itself. -/
  | var : Occurs x (.var x)

-- ADE: none.
/-- `M ⊑ N`: the term `M` of the target language is `N` with some subterms replaced by `↯`. -/
inductive Target.LessDefined {n : Nat} : Target n → Target n → Prop where
  /-- `↯` is less defined than every term. -/
  | erased {N : Target n} : LessDefined .erased N
  /-- A variable is less defined than itself. -/
  | var {x : Fin n} : LessDefined (.var x) (.var x)
  /-- A constant is less defined than itself. -/
  | const {f : Name} {ps : List Grade} : LessDefined (.const f ps) (.const f ps)

@[inherit_doc] infix:50 " ⊑ " => Target.LessDefined

-- ADE: `erase′`, in `Graded/Erasure/Extraction.agda`.
/--
`⌊t⌋_S`: the erasure of a term of a scope of variables, which replaces by `↯` the positions whose
grade is in `S`: `U_l`, `Ω_l` and the instances `T` are erased, a variable is kept, and a constant
`f.{s̄; l̄; p̄}` keeps its grades, `f.{p̄}`.
-/
def Term.erase (_S : Set Grade) {k : Nat} {Γ : Scope} (_hΓ : Γ.FirstOrder) :
    Term k Γ → Target Γ.length
  | .var x _ => .var x.toFin
  | .sort _ => .erased
  | .const f _ _ ps => .const f ps
  | .inst .. => .erased

/-! ## Properties -/

-- ADE: none.
/-- A set `S` of grades erases only what a term checked in the mode `m` does not count, and
follows the rules of usage: a variable checked in the mode `m` uses itself with a grade outside
`S`, and a grade above a grade of `S`, or a part of a sum in `S`, is in `S`. -/
structure ErasesUncounted (m : Mode) (S : Set Grade) : Prop where
  /-- The grade `⌜m⌝` is not erased. -/
  grade : m.grade ∉ S
  /-- A grade above a grade of `S` is in `S`. -/
  le : ∀ p q : Grade, p ≤ q → p ∈ S → q ∈ S
  /-- The first part of a sum in `S` is in `S`. -/
  add : ∀ p q : Grade, p + q ∈ S → p ∈ S

-- ADE: none.
/-- The set `S^m` erases only what a term checked in the mode `m` does not count. -/
theorem Mode.erasesUncounted (m : Mode) : ErasesUncounted m m.erased where
  grade := by revert m; decide
  le := by revert m; decide
  add := by revert m; decide

-- ADE: `erased-hasX`, in `Graded/Erasure/Extraction/Properties/Usage.agda`, for `S^{𝟙ᵐ}`.
/--
A variable whose grade is in `S` does not occur in the erasure by `S` of a term checked in a mode
`m` whose uses `S` does not erase.
-/
theorem Usage.absent {sig : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length}
    {m : Mode} {t : Term k Γ} {S : Set Grade} (hS : ErasesUncounted m S) (hΓ : Γ.FirstOrder)
    {x : Fin Γ.length} : Usage sig γ m t → γ x ∈ S → ¬ (t.erase S hΓ).Occurs x
  | .var (x := y) (δ := δ) _, hx, ho => by
    cases ho
    have h : m.grade + δ y.toFin ∈ S := by
      simpa [GradeVector.add, GradeVector.update] using hx
    exact hS.grade (hS.add _ _ h)
  | .const .., _, ho => nomatch ho
  | .sort, _, ho => nomatch ho
  | .sub h hle, hx, ho => h.absent hS hΓ (hS.le _ _ (hle x) hx) ho

-- ADE: none.
/-- The erasure by a larger set of grades is less defined. -/
theorem Term.erase_lessDefined {S₁ S₂ : Set Grade} (_h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) (t : Term k Γ) : t.erase S₂ hΓ ⊑ t.erase S₁ hΓ := by
  cases t <;> constructor

end Sic.Core
