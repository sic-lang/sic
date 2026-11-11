module

public import Sic.Core.Syntax.Terms
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.Syntax.Signature

/-!
# Erasure

The erasure of annex 16 of RFC 36, which compiles a term to an untyped target language: `⌊t⌋_S`
replaces by `↯` the positions of `t` whose grade is in the set `S`, and the set of grades `S^m` of the
grades that a term checked in the mode `m` does not count gives the extraction, `⌊t⌋_{S^{11ᵐ}}`, and
the program that the proofs see, `⌊t⌋_{S^{01ᵐ}}`.
The target language has variables, the constants with their qualities and their grades, `f.{s̄; p̄}`,
a value `↯` that stands for what was erased, the constructors and the recursors of the data types,
and the observations and the corecursors of the codata types, whose fields, terms, arguments and
states are positions, erased by their grades.
It keeps only what its evaluation reads: a constructor and an observation keep the case of their
constructor and of their destructor in its block, which chooses a branch, since the names are only
distinct in their type; a branch of a recursor keeps the field of each of its recursive results, or
none when the result is erased, and a branch of a corecursor the number of the entries of the state
it resumes, when its destructor is recursive.

The translation is defined on the terms in a scope of variables only, which the hypothesis
`Γ.FirstOrder` states: the programs are closed, and the branches of a recursor or of a corecursor
bind variables, while a second-order variable only appears in the contexts in which the declarations
are checked.
A variable thus has no arguments, and the target language has no second-order variables: the
clause of a second-order variable discharges it by `Γ.FirstOrder`, so that the clauses are those of
the RFC.
The new variables of a branch extend the scope, whose length the target language counts, so that
the erasure of a branch casts its number of variables by `Scope.length_extend_extend`; the
non-uniform parameters of a branch of a corecursor, which the corecursors do not have yet, have no
variables in the target language.

ADE extract the terms of their type theory, in which the definitions are names, and replace each
erased part by `↯` or by a term that does not terminate, as its strictness requires; they erase the
grade `𝟘` only, in the mode `𝟙ᵐ`, while the erasure here is stated for every set of grades.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The scope `Γ` declares variables only, and no second-order variable. -/
def Scope.FirstOrder (Γ : Scope) : Prop := ∀ e ∈ Γ, e = .var

-- ADE: none.
/-- The entry of a variable is an entry of its scope. -/
theorem Var.mem {Γ : Scope} {e : Scope.Entry} : Var Γ e → e ∈ Γ
  | .zero => List.mem_cons_self
  | .succ x => List.mem_cons_of_mem _ x.mem

mutual

-- ADE: `Term`, in `Graded/Erasure/Target.agda`.
/-- A term `M` of the target language over `n` variables.
RFC: `\mathsf{syntax}_M` -/
inductive Target : Nat → Type where
  /-- A variable. -/
  | var {n : Nat} (x : Fin n) : Target n
  /-- `f.{s̄; p̄}`: the constant `f` at the qualities `s̄` and the grades `p̄`. -/
  | const {n : Nat} (f : Name) (qs : List Quality) (ps : List Grade) : Target n
  /-- `↯`, what was erased. -/
  | erased {n : Nat} : Target n
  /-- `cᵢ(M̄)`: the constructor of the case `i` of its block applied to a term for each of its
  fields. -/
  | ctor {n : Nat} (i : Nat) (Ms : Targets n) : Target n
  /-- `rec M with N̄`: the recursor on `M`, with a branch for each constructor, in order. -/
  | recursor {n : Nat} (M : Target n) (Ns : TargetBranches n) : Target n
  /-- `M.dᵢ(M̄)`: the observation of `M` by the destructor of the case `i` of its block, applied to
  a term for each of its arguments. -/
  | obs {n : Nat} (M : Target n) (i : Nat) (Ms : Targets n) : Target n
  /-- `corec from M̄ with P̄`: the corecursor from the state `M̄`, with a branch for each
  destructor, in order. -/
  | corec {n : Nat} (Ms : Targets n) (Ns : TargetCorecBranches n) : Target n

-- ADE: none.
/-- `M̄ = (M₁, …, Mₐ)`: terms of the target language, the first one first.
RFC: `\mathsf{syntax}_{\bar M}` -/
inductive Targets : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : Targets n
  /-- `(M, M̄)`. -/
  | cons {n : Nat} (M : Target n) (Ms : Targets n) : Targets n

-- ADE: none.
/-- `N̄`: the branches of a recursor of the target language, in order; the branch `(x̄; ȳ ← k̄). N`
is a term over a new variable for each of the `a` fields and of the `b` recursive results, and
`k̄` gives, for each recursive result, the position of its field, or `none`, the RFC's `⊥`, when
the result is erased; the positions are counted from `0`, while the RFC counts them from `1`.
RFC: `\mathsf{syntax}_{\bar N}` -/
inductive TargetBranches : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : TargetBranches n
  /-- `((x̄; ȳ ← k̄). N, N̄)`. -/
  | cons {n : Nat} (a b : Nat) (ks : Fin b → Option Nat) (N : Target (n + (a + b)))
      (Ns : TargetBranches n) : TargetBranches n

-- ADE: none.
/-- `P̄`: the branches of a corecursor of the target language, in order; the branch
`(ȳ; z̄ ↻ k). P` is a term over a new variable for each of the `b` entries of the state and of the
`c` arguments, and `k` gives, for a recursive destructor, the number of the entries of the state
that the branch resumes, or `none`, the RFC's `⊥`.
RFC: `\mathsf{syntax}_{\bar P}` -/
inductive TargetCorecBranches : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : TargetCorecBranches n
  /-- `((ȳ; z̄ ↻ k). P, P̄)`. -/
  | cons {n : Nat} (o : Option Nat) (b c : Nat) (N : Target (n + (b + c)))
      (Ns : TargetCorecBranches n) : TargetCorecBranches n

end

mutual

-- ADE: `HasX`, in `Graded/Erasure/Target.agda`.
/-- The variable `x` occurs in the term of the target language. -/
inductive Target.Occurs : {n : Nat} → Fin n → Target n → Prop where
  /-- The variable `x` itself.
  RFC: `\mathsf{occurs}_M.x` -/
  | var {n : Nat} {x : Fin n} : Target.Occurs x (.var x)
  /-- In a field of a constructor.
  RFC: `\mathsf{occurs}_M.c` -/
  | ctor {n : Nat} {x : Fin n} {i : Nat} {Ms : Targets n} (h : Targets.Occurs x Ms) :
      Target.Occurs x (.ctor i Ms)
  /-- In the term of a recursor.
  RFC: `\mathsf{occurs}_M.\mathsf{rec}` -/
  | recursor {n : Nat} {x : Fin n} {M : Target n} {Ns : TargetBranches n} (h : Target.Occurs x M) :
      Target.Occurs x (.recursor M Ns)
  /-- In a branch of a recursor.
  RFC: `\mathsf{occurs}_M.\mathsf{with}` -/
  | branch {n : Nat} {x : Fin n} {M : Target n} {Ns : TargetBranches n}
      (h : TargetBranches.Occurs x Ns) : Target.Occurs x (.recursor M Ns)
  /-- In the term of an observation.
  RFC: `\mathsf{occurs}_M.\mathsf{obs}` -/
  | obs {n : Nat} {x : Fin n} {M : Target n} {i : Nat} {Ms : Targets n} (h : Target.Occurs x M) :
      Target.Occurs x (.obs M i Ms)
  /-- In an argument of an observation.
  RFC: `\mathsf{occurs}_M.\mathsf{args}` -/
  | arg {n : Nat} {x : Fin n} {M : Target n} {i : Nat} {Ms : Targets n}
      (h : Targets.Occurs x Ms) : Target.Occurs x (.obs M i Ms)
  /-- In the state of a corecursor.
  RFC: `\mathsf{occurs}_M.\mathsf{from}` -/
  | corec {n : Nat} {x : Fin n} {Ms : Targets n} {Ns : TargetCorecBranches n}
      (h : Targets.Occurs x Ms) : Target.Occurs x (.corec Ms Ns)
  /-- In a branch of a corecursor.
  RFC: `\mathsf{occurs}_M.\mathsf{with}_{\bar P}` -/
  | cobranch {n : Nat} {x : Fin n} {Ms : Targets n} {Ns : TargetCorecBranches n}
      (h : TargetCorecBranches.Occurs x Ns) : Target.Occurs x (.corec Ms Ns)

-- ADE: none.
/-- The variable `x` occurs in one of the terms. -/
inductive Targets.Occurs : {n : Nat} → Fin n → Targets n → Prop where
  /-- In the first term.
  RFC: `\mathsf{occurs}_{\bar M}.M` -/
  | head {n : Nat} {x : Fin n} {M : Target n} {Ms : Targets n} (h : Target.Occurs x M) :
      Targets.Occurs x (.cons M Ms)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar M}.\bar M` -/
  | tail {n : Nat} {x : Fin n} {M : Target n} {Ms : Targets n} (h : Targets.Occurs x Ms) :
      Targets.Occurs x (.cons M Ms)

-- ADE: none.
/-- The variable `x` occurs in one of the branches, under their new variables, which shift it. -/
inductive TargetBranches.Occurs : {n : Nat} → Fin n → TargetBranches n → Prop where
  /-- In the first branch.
  RFC: `\mathsf{occurs}_{\bar N}.N` -/
  | head {n : Nat} {x : Fin n} {a b : Nat} {ks : Fin b → Option Nat}
      {N : Target (n + (a + b))} {Ns : TargetBranches n} (h : Target.Occurs (x.addNat (a + b)) N) :
      TargetBranches.Occurs x (.cons a b ks N Ns)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar N}.\bar N` -/
  | tail {n : Nat} {x : Fin n} {a b : Nat} {ks : Fin b → Option Nat}
      {N : Target (n + (a + b))} {Ns : TargetBranches n} (h : TargetBranches.Occurs x Ns) :
      TargetBranches.Occurs x (.cons a b ks N Ns)

-- ADE: none.
/-- The variable `x` occurs in one of the branches of a corecursor, under their new variables,
which shift it. -/
inductive TargetCorecBranches.Occurs : {n : Nat} → Fin n → TargetCorecBranches n → Prop where
  /-- In the first branch.
  RFC: `\mathsf{occurs}_{\bar P}.P` -/
  | head {n : Nat} {x : Fin n} {o : Option Nat} {b c : Nat} {N : Target (n + (b + c))}
      {Ns : TargetCorecBranches n} (h : Target.Occurs (x.addNat (b + c)) N) :
      TargetCorecBranches.Occurs x (.cons o b c N Ns)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar P}.\bar P` -/
  | tail {n : Nat} {x : Fin n} {o : Option Nat} {b c : Nat} {N : Target (n + (b + c))}
      {Ns : TargetCorecBranches n} (h : TargetCorecBranches.Occurs x Ns) :
      TargetCorecBranches.Occurs x (.cons o b c N Ns)

end

mutual

-- ADE: none.
/-- `M ⊑ N`: the term `M` of the target language is `N` with some subterms replaced by `↯`. -/
inductive Target.LessDefined : {n : Nat} → Target n → Target n → Prop where
  /-- `↯` is less defined than every term.
  RFC: `{\sqsubseteq}.\text{↯}` -/
  | erased {n : Nat} {N : Target n} : Target.LessDefined .erased N
  /-- A variable is less defined than itself.
  RFC: `{\sqsubseteq}.x` -/
  | var {n : Nat} {x : Fin n} : Target.LessDefined (.var x) (.var x)
  /-- A constant is less defined than itself.
  RFC: `{\sqsubseteq}.f` -/
  | const {n : Nat} {f : Name} {qs : List Quality} {ps : List Grade} :
      Target.LessDefined (n := n) (.const f qs ps) (.const f qs ps)
  /-- A constructor is less defined than the same constructor of more defined fields.
  RFC: `{\sqsubseteq}.c` -/
  | ctor {n : Nat} {i : Nat} {Ms Ns : Targets n} (h : Targets.LessDefined Ms Ns) :
      Target.LessDefined (.ctor i Ms) (.ctor i Ns)
  /-- A recursor is less defined than a recursor of a more defined term and branches.
  RFC: `{\sqsubseteq}.\mathsf{rec}` -/
  | recursor {n : Nat} {M N : Target n} {Ms Ns : TargetBranches n} (h : Target.LessDefined M N)
      (hs : TargetBranches.LessDefined Ms Ns) : Target.LessDefined (.recursor M Ms) (.recursor N Ns)
  /-- An observation is less defined than the same observation of a more defined term and
  arguments.
  RFC: `{\sqsubseteq}.d` -/
  | obs {n : Nat} {M N : Target n} {i : Nat} {Ms Ns : Targets n} (h : Target.LessDefined M N)
      (hs : Targets.LessDefined Ms Ns) : Target.LessDefined (.obs M i Ms) (.obs N i Ns)
  /-- A corecursor is less defined than a corecursor of a more defined state and branches.
  RFC: `{\sqsubseteq}.\mathsf{corec}` -/
  | corec {n : Nat} {Ms Ns : Targets n} {Ms' Ns' : TargetCorecBranches n}
      (h : Targets.LessDefined Ms Ns) (hs : TargetCorecBranches.LessDefined Ms' Ns') :
      Target.LessDefined (.corec Ms Ms') (.corec Ns Ns')

-- ADE: none.
/-- The terms are less defined, one by one. -/
inductive Targets.LessDefined : {n : Nat} → Targets n → Targets n → Prop where
  /-- `()`.
  RFC: `{\sqsubseteq}_{\bar M}.\varepsilon` -/
  | nil {n : Nat} : Targets.LessDefined (n := n) .nil .nil
  /-- `(M, M̄) ⊑ (N, N̄)`.
  RFC: `{\sqsubseteq}_{\bar M}.{,}` -/
  | cons {n : Nat} {M N : Target n} {Ms Ns : Targets n} (h : Target.LessDefined M N)
      (hs : Targets.LessDefined Ms Ns) : Targets.LessDefined (.cons M Ms) (.cons N Ns)

-- ADE: none.
/-- The branches are less defined, one by one. -/
inductive TargetBranches.LessDefined : {n : Nat} → TargetBranches n → TargetBranches n → Prop where
  /-- `()`.
  RFC: `{\sqsubseteq}_{\bar N}.\varepsilon` -/
  | nil {n : Nat} : TargetBranches.LessDefined (n := n) .nil .nil
  /-- `((x̄; ȳ ← k̄₁). M, M̄) ⊑ ((x̄; ȳ ← k̄₂). N, N̄)`, where each recursive result of `k̄₁` is not
  computed or has the field it has in `k̄₂`.
  RFC: `{\sqsubseteq}_{\bar N}.{,}` -/
  | cons {n a b : Nat} {ks₁ ks₂ : Fin b → Option Nat} {M N : Target (n + (a + b))}
      {Ms Ns : TargetBranches n} (hk : ∀ j : Fin b, ks₁ j = none ∨ ks₁ j = ks₂ j)
      (h : Target.LessDefined M N) (hs : TargetBranches.LessDefined Ms Ns) :
      TargetBranches.LessDefined (.cons a b ks₁ M Ms) (.cons a b ks₂ N Ns)

-- ADE: none.
/-- The branches of a corecursor are less defined, one by one. -/
inductive TargetCorecBranches.LessDefined :
    {n : Nat} → TargetCorecBranches n → TargetCorecBranches n → Prop where
  /-- `()`.
  RFC: `{\sqsubseteq}_{\bar P}.\varepsilon` -/
  | nil {n : Nat} : TargetCorecBranches.LessDefined (n := n) .nil .nil
  /-- `((ȳ; z̄ ↻ k). P₁, P̄₁) ⊑ ((ȳ; z̄ ↻ k). P₂, P̄₂)`.
  RFC: `{\sqsubseteq}_{\bar P}.{,}` -/
  | cons {n : Nat} {o : Option Nat} {b c : Nat} {M N : Target (n + (b + c))}
      {Ms Ns : TargetCorecBranches n} (h : Target.LessDefined M N)
      (hs : TargetCorecBranches.LessDefined Ms Ns) :
      TargetCorecBranches.LessDefined (.cons o b c M Ms) (.cons o b c N Ns)

end

@[inherit_doc] infix:50 " ⊑ " => Target.LessDefined

-- ADE: none.
/-- A scope of variables extended by variables is a scope of variables. -/
theorem Scope.FirstOrder.extend {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (a : Nat) → (Γ.extend a).FirstOrder
  | 0 => hΓ
  | a + 1 => Scope.FirstOrder.extend (Γ := .var :: Γ)
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact hΓ e he) a

-- ADE: none.
/-- The number of the entries of the state at the position `j` of the states of a corecursor, when it
has no non-uniform parameters. -/
def States.arity {k : Nat} {Γ : Scope} (Ss : States k Γ) (j : Nat) : Option Nat :=
  match Ss.get j with
  | some ⟨0, ps, _⟩ => some ps.length
  | _ => none

mutual

-- ADE: `erase′`, in `Graded/Erasure/Extraction.agda`.
/--
`⌊t⌋_S`: the erasure of a term of a scope of variables, which replaces by `↯` the positions whose
grade is in `S`: `U_l`, `Ω_l` and the instances `T` are erased, a variable is kept, a constant
`f.{s̄; l̄; p̄}` keeps its qualities and its grades, `f.{s̄; p̄}`, a constructor keeps its case and its
fields, each at the grade of its field, a recursor keeps its term, at its grade, and its branches,
without its instance and its motives, an observation keeps its term, the case of its destructor and
its arguments, each at the grade of its argument, and a corecursor keeps its state, each entry at
its grade times the grade of the corecursor, and its branches, without its instance and its
states; a second-order variable has no erasure, since the scope has none.
The cases, the grades of the fields, of the arguments and of the entries of the state, the fields of
the recursive results and the states that the branches resume are those of the declarations in the
signature `sig`; a constructor or an observation whose case the signature does not give, and a
field, an argument or an entry whose grade it does not give, in a term that no declaration types,
are erased.
Whether a grade is in `S` decides the erasure of its position, so that `S` is decidable, as the
sets `S^m` are.
RFC: `\mathsf{erase}_t`
-/
def Term.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : Term k Γ → Target Γ.length
  | .var (e := .var) x _ => .var x.toFin
  | .var (e := .secondOrder ..) x _ => nomatch hΓ _ x.mem
  | .sort _ => .erased
  | .const f qs _ ps => .const f qs ps
  | .inst .. => .erased
  | .ctor D qs _ ps _ c ts =>
    match sig.constructorCase D c with
    | some i => .ctor i (ts.erase sig S hΓ ((sig.fieldGrades D c qs ps).getD []))
    | none => .erased
  | .recursor r D qs _ ps _ t _ us =>
    .recursor (if r ∈ S then .erased else t.erase sig S hΓ)
      (us.erase sig S hΓ ((sig.recursiveFields D qs ps).getD []))
  | .obs D qs _ ps _ t d bs =>
    match sig.destructorCase D d with
    | some i =>
      .obs (t.erase sig S hΓ) i (bs.erase sig S hΓ ((sig.argumentGrades D d qs ps).getD []))
    | none => .erased
  | .corec r D qs _ ps _ ss Ss vs =>
    .corec (ss.erase sig S hΓ (((sig.position D).bind Ss.get).elim []
      fun ⟨_, ps, _⟩ => ps.map (r * ·.usage)))
      (vs.erase sig S hΓ ((sig.destructorGrades D qs ps).getD [])
        (((sig.resumedTypes D qs ps).getD []).map (·.bind Ss.arity)))

-- ADE: none.
/-- `⌊t̄⌋_{S, p̄}`: the erasure of the fields of a constructor, of the arguments of an observation
or of the state of a corecursor, each at its grade in `ps`, a term without grade being erased.
RFC: `\mathsf{erase}_{\bar t}` -/
def Terms.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : Terms k Γ → List Grade → Targets Γ.length
  | .nil, _ => .nil
  | .cons _ ts, [] => .cons .erased (ts.erase sig S hΓ [])
  | .cons t ts, p :: ps =>
    .cons (if p ∈ S then .erased else t.erase sig S hΓ) (ts.erase sig S hΓ ps)

-- ADE: none.
/-- `⌊ū⌋_{S, ē̄}`: the erasure of the branches of a recursor, under their new variables, each with
the field of each of its recursive results, in the positions `es` of the recursive fields of its
constructor, or `none` when the grade of the result is in `S`, so that the result is not computed.
RFC: `\mathsf{erase}_{\bar u}` -/
def Branches.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : Branches k Γ → List (List Nat) → TargetBranches Γ.length
  | .nil, _ => .nil
  | .cons a b gs u us, es =>
    .cons a b (fun j => if gs[j] ∈ S then none else (es.headD [])[(j : Nat)]?)
      (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b))
      (us.erase sig S hΓ es.tail)

-- ADE: none.
/-- `⌊ḡ⌋_{S, p̄, k̄}`: the erasure of the branches of a corecursor, under their new variables, each
at the grade of its destructor in `ps`, with the number of the entries of the state it resumes in
`ks`; a branch without grade, or with non-uniform parameters, which the corecursors do not have
yet, is erased.
RFC: `\mathsf{erase}_{\bar g}` -/
def CorecBranches.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) :
    CorecBranches k Γ → List Grade → List (Option Nat) → TargetCorecBranches Γ.length
  | .nil, _, _ => .nil
  | .cons 0 b c v vs, p :: ps, ks =>
    .cons (ks.headD none) b c (if p ∈ S then .erased else Scope.length_extend_extend Γ b c ▸
      v.erase sig S ((hΓ.extend b).extend c))
      (vs.erase sig S hΓ ps ks.tail)
  | .cons _ b c _ vs, ps, ks => .cons (ks.headD none) b c .erased (vs.erase sig S hΓ ps.tail ks.tail)

end

/-! ## Properties -/

/-- A term of the target language transported along an equality of the sizes of its scope has the
occurrences of the term, at the transported indices. -/
theorem Target.occurs_cast {n n' : Nat} (h : n = n') (M : Target n) (y : Fin n') :
    (h ▸ M).Occurs y → M.Occurs (y.cast h.symm) := by
  subst h
  exact id

/-- A variable occurs in the erasure of branches when it occurs, as an old variable of the scope
of a branch, in the erasure of the term of this branch. -/
theorem Branches.occurs_erase {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} : (us : Branches k Γ) →
      (es : List (List Nat)) → (us.erase sig S hΓ es).Occurs x → ∃ i a b u, us.get i = some ⟨a, b, u⟩ ∧
        (u.erase sig S ((hΓ.extend a).extend b)).Occurs
          ((x.addNat (a + b)).cast (Scope.length_extend_extend Γ a b).symm)
  | .nil, _, h => nomatch h
  | .cons a b _ u us, es, h => by
    cases h with
    | head h => exact ⟨0, a, b, u, rfl, Target.occurs_cast _ _ _ h⟩
    | tail h =>
      obtain ⟨i, a', b', u', hu, ho⟩ := Branches.occurs_erase hΓ us es.tail h
      exact ⟨i + 1, a', b', u', hu, ho⟩

/-- The branch at a position of branches is before their end. -/
theorem Branches.lt_length_of_get {k : Nat} {Γ : Scope} :
    {us : Branches k Γ} → {i : Nat} → {a : Σ n m, Term k ((Γ.extend n).extend m)} →
      us.get i = some a → i < us.length
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, _ => Nat.zero_lt_succ _
  | .cons _ _ _ _ us, _ + 1, _, h => Nat.succ_lt_succ (Branches.lt_length_of_get (us := us) h)

/-- The grades extended by the variables of a telescope give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_addNat {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendParams r ps ((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm) =
        γ x
  | [], _ => rfl
  | p :: ps, x => by
    have h := extendParams_addNat (Γ := .var :: Γ) (γ ∙ (r * p.usage)) r ps x.succ
    have he : ((x.addNat (p :: ps).length).cast (Scope.length_extend Γ (p :: ps).length).symm :
        Fin (Γ.extend (p :: ps).length).length) =
        (x.succ.addNat ps.length).cast (Scope.length_extend (.var :: Γ) ps.length).symm :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat, Fin.val_succ, List.length_cons]; omega)
    rw [he]
    exact h

/-- A variable occurs in the erasure of the branches of a corecursor when it occurs, as an old
variable of the scope of a branch whose grade is not erased, in the erasure of the term of this
branch. -/
theorem CorecBranches.occurs_erase {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    (vs : CorecBranches k Γ) → (ps : List Grade) → (ks : List (Option Nat)) →
      (vs.erase sig S hΓ ps ks).Occurs x →
        ∃ i b c v p, vs.get i = some ⟨0, b, c, v⟩ ∧ ps[i]? = some p ∧ p ∉ S ∧
          (v.erase sig S ((hΓ.extend b).extend c)).Occurs
            ((x.addNat (b + c)).cast (Scope.length_extend_extend Γ b c).symm)
  | .nil, _, _, h => nomatch h
  | .cons 0 b c v vs, p :: ps, ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h =>
      by_cases hp : p ∈ S
      · simp only [hp, ↓reduceIte] at h
        exact nomatch h
      · simp only [hp, ↓reduceIte] at h
        exact ⟨0, b, c, v, p, rfl, rfl, hp, Target.occurs_cast _ _ _ h⟩
    | tail h =>
      obtain ⟨i, b', c', v', p', hv, hp, hpS, ho⟩ := CorecBranches.occurs_erase hΓ vs ps ks.tail h
      exact ⟨i + 1, b', c', v', p', hv, hp, hpS, ho⟩
  | .cons 0 _ _ _ vs, [], ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h => exact nomatch h
    | tail h =>
      obtain ⟨_, _, _, _, _, _, hp, _⟩ := CorecBranches.occurs_erase hΓ vs [] ks.tail h
      simp at hp
  | .cons (_ + 1) _ _ _ vs, ps, ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h => exact nomatch h
    | tail h =>
      obtain ⟨i, b', c', v', p', hv, hp, hpS, ho⟩ := CorecBranches.occurs_erase hΓ vs _ ks.tail h
      rw [List.getElem?_tail] at hp
      exact ⟨i + 1, b', c', v', p', hv, hp, hpS, ho⟩

/-- The branch at a position of the branches of a corecursor is before their end. -/
theorem CorecBranches.lt_length_of_get {k : Nat} {Γ : Scope} :
    {vs : CorecBranches k Γ} → {i : Nat} →
      {a : Σ n m a, Term k (((Γ.extend n).extend m).extend a)} → vs.get i = some a →
        i < vs.length
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, _ => Nat.zero_lt_succ _
  | .cons _ _ _ _ vs, _ + 1, _, h =>
    Nat.succ_lt_succ (CorecBranches.lt_length_of_get (vs := vs) h)

/-- The grades extended by the variables of two telescopes, one after the other, give each old
variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_extendParams_addNat {Γ : Scope} (γ : GradeVector Γ.length)
    (r₁ r₂ : Grade) (ps₁ ps₂ : List Parameter) (x : Fin Γ.length) :
    (γ.extendParams r₁ ps₁).extendParams r₂ ps₂
        ((x.addNat (0 + ps₁.length + ps₂.length)).cast
          (Scope.length_extend_extend_extend Γ 0 ps₁.length ps₂.length).symm) = γ x := by
  have he : ((x.addNat (0 + ps₁.length + ps₂.length)).cast
      (Scope.length_extend_extend_extend Γ 0 ps₁.length ps₂.length).symm :
        Fin ((Γ.extend ps₁.length).extend ps₂.length).length) =
      ((((x.addNat ps₁.length).cast (Scope.length_extend Γ ps₁.length).symm).addNat
        ps₂.length).cast (Scope.length_extend (Γ.extend ps₁.length) ps₂.length).symm) :=
    Fin.ext (show x.val + (0 + ps₁.length + ps₂.length) = (x.val + ps₁.length) + ps₂.length by
      omega)
  rw [he, GradeVector.extendParams_addNat, GradeVector.extendParams_addNat]

/-- The grades extended by a grade for each variable of a telescope give each old variable its
grade. -/
theorem _root_.Sic.Grading.GradeVector.extendGrades_addNat {Γ : Scope} (γ : GradeVector Γ.length) (g : Nat → Grade) :
    (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendGrades g ps ((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm) =
        γ x
  | [], _ => rfl
  | p :: ps, x => by
    have h := extendGrades_addNat (Γ := .var :: Γ) (γ ∙ g 0) (fun l => g (l + 1)) ps
      x.succ
    have he : ((x.addNat (p :: ps).length).cast (Scope.length_extend Γ (p :: ps).length).symm :
        Fin (Γ.extend (p :: ps).length).length) =
        (x.succ.addNat ps.length).cast (Scope.length_extend (.var :: Γ) ps.length).symm :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat, Fin.val_succ, List.length_cons]; omega)
    rw [he]
    exact h

/-- The grades extended by a grade for each recursive result give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendResults_addNat {Γ : Scope} (γ : GradeVector Γ.length) (e : Nat → Grade) :
    (rs : List (Option Name)) → (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendResults e rs ps ((x.addNat (Telescope.resultParams rs ps).length).cast
        (Scope.length_extend Γ _).symm) = γ x
  | some D :: rs, p :: ps, x => by
    have h := extendResults_addNat (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) rs
      ps x.succ
    have he : ((x.addNat (Telescope.resultParams (some D :: rs) (p :: ps)).length).cast
        (Scope.length_extend Γ _).symm :
          Fin (Γ.extend (Telescope.resultParams (some D :: rs) (p :: ps)).length).length) =
        (x.succ.addNat (Telescope.resultParams rs ps).length).cast
          (Scope.length_extend (.var :: Γ) _).symm :=
      Fin.ext (show x.val + ((Telescope.resultParams rs ps).length + 1) =
        (x.val + 1) + (Telescope.resultParams rs ps).length by omega)
    rw [he]
    exact h
  | none :: rs, _ :: ps, x => extendResults_addNat γ (fun l => e (l + 1)) rs ps x
  | [], _, _ | some _ :: _, [], _ | none :: _, [], _ => rfl

/-- The grades extended by a grade for each field, then for each recursive result, as in the scope
of a branch of a recursor, give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendGrades_extendResults_addNat {Γ : Scope} (γ : GradeVector Γ.length)
    (g e : Nat → Grade) (rs : List (Option Name)) (ps : List Parameter) (x : Fin Γ.length) :
    (γ.extendGrades g ps).extendResults e rs ps
        ((x.addNat (ps.length + (Telescope.resultParams rs ps).length)).cast
          (Scope.length_extend_extend Γ _ _).symm) = γ x := by
  have he : ((x.addNat (ps.length + (Telescope.resultParams rs ps).length)).cast
      (Scope.length_extend_extend Γ _ _).symm :
        Fin ((Γ.extend ps.length).extend (Telescope.resultParams rs ps).length).length) =
      ((((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm).addNat
        (Telescope.resultParams rs ps).length).cast (Scope.length_extend _ _).symm) :=
    Fin.ext (show x.val + (ps.length + (Telescope.resultParams rs ps).length) =
      (x.val + ps.length) + (Telescope.resultParams rs ps).length by omega)
  rw [he, GradeVector.extendResults_addNat, GradeVector.extendGrades_addNat]

mutual

-- ADE: `erased-hasX`, in `Graded/Erasure/Extraction/Properties/Usage.agda`, for `S^{𝟙ᵐ}`.
/--
A variable whose grade is in `S` does not occur in the erasure by `S` of a term checked in a mode
`m` whose uses `S` does not erase, in a signature whose names are distinct, so that the usage and
the erasure of a constructor read the grades of its fields in the same declaration.
RFC: `\mathsf{absent}_S`
-/
theorem Usage.absent {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {γ : GradeVector Γ.length} {m : Mode} {t : Term k Γ} {S : Set Grade} [DecidablePred (· ∈ S)]
    (hS : ErasesUncounted m S) (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    Usage sig γ m t → γ x ∈ S → ¬ (t.erase sig S hΓ).Occurs x
  | .var (e := .secondOrder ..) (x := y) _, _, _ => nomatch hΓ _ y.mem
  | .var (e := .var) (x := y) (δ := δ) _, hx, ho => by
    simp only [Term.erase] at ho
    cases ho
    have h : m.grade + δ y.toFin ∈ S := by
      simpa [GradeVector.add, GradeVector.update] using hx
    exact hS.grade (hS.add _ _ h)
  | .const .., _, ho => nomatch ho
  | .sort, _, ho => nomatch ho
  | .ctor h hc hq hp hts, hx, ho => by
    simp only [Term.erase, hd.fieldGrades h hc hq hp, Option.getD_some] at ho
    split at ho
    · cases ho with
      | ctor ho => exact UsageArgs.absent hd hS hΓ hts hx ho
    · exact nomatch ho
  | .recursor (γ := γ₁) (χ := χ) (δs := δs) (r := r) _ _ _ _ ht hul hus hu _ hχ _, hx, ho => by
    have hx' : r * γ₁ x + χ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Term.erase] at ho
    cases ho with
    | recursor ho =>
      by_cases hr : r ∈ S
      · simp only [hr, ↓reduceIte] at ho
        exact nomatch ho
      · simp only [hr, ↓reduceIte] at ho
        have hS' : ErasesUncounted (m ⊙ r) S := (hS.mode _ hr).symm ▸ hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hr (hS.add _ _ hx')) ho
    | branch ho =>
      obtain ⟨i, a, b, u, hget, ho⟩ := Branches.occurs_erase hΓ _ _ ho
      have hi : i < _ := hul ▸ Branches.lt_length_of_get hget
      obtain ⟨⟨j, T', con⟩, hc⟩ : ∃ c, _ = some c := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨u', hu'⟩ := hus i j T' con hc
      cases Option.some.inj (hget.symm.trans hu')
      have hχx : χ x ∈ S := hS.add _ _ (Grade.modality.semiring.add_comm _ _ ▸ hx')
      have hδ : δs i x ∈ S := by
        have h' := hS.le _ _ (hχ i j T' con hc x) hχx
        simp only [GradeVector.add, GradeVector.smul] at h'
        exact hS.add _ _ h'
      exact Usage.absent hd hS ((hΓ.extend _).extend _) (hu i j T' con u' hc hu')
        (by rw [GradeVector.extendGrades_extendResults_addNat]; exact hδ) ho
  | .obs (γ := γ₁) (δ := δ) h hq hp hpos ht hbs _, hx, ho => by
    have hx' : γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add] using hx
    simp only [Term.erase, hd.argumentGrades h hq hp hpos, Option.getD_some] at ho
    split at ho
    · cases ho with
      | obs ho => exact Usage.absent hd hS hΓ ht (hS.add _ _ hx') ho
      | arg ho =>
        rw [Grade.modality.semiring.add_comm] at hx'
        exact UsageArgs.absent hd hS hΓ hbs (hS.add _ _ hx') ho
    · exact nomatch ho
  | .corec (decl := decl) (γ := γ₁) (δ := δ) (δs := δs) (r := r) (qs := qs) (ps := ps) h hq hp hh
      hS₀ _ hss hgl _
      hSs hgs hgu hδ _, hx, ho => by
    have hx' : r * γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    obtain ⟨gr, hgr, hgri⟩ := hd.destructorGrades h hq hp
    simp only [Term.erase, hd.position h hh, Option.bind_some, hS₀, Option.elim, hgr,
      Option.getD_some] at ho
    cases ho with
    | corec ho => exact UsageArgs.absent_mul hd hS hΓ rfl hss (hS.add _ _ hx') ho
    | cobranch ho =>
      obtain ⟨i, b, c, v, p', hget, hgi, hpS, ho⟩ := CorecBranches.occurs_erase hΓ _ _ _ ho
      have hi : i < _ := hgl ▸ CorecBranches.lt_length_of_get hget
      obtain ⟨⟨j, T', d⟩, hc⟩ : ∃ c, _ = some c := ⟨_, List.getElem?_eq_getElem hi⟩
      have hcm := List.mem_of_getElem? hc
      obtain ⟨hT', hdm⟩ := TypeDeclaration.mem_casesFrom hcm
      have hj : decl.codataTypes[j]? = some T' := by
        have := (TypeDeclaration.getElem?_of_mem_casesFrom hcm).2
        rwa [Nat.sub_zero] at this
      obtain ⟨ps'', S', hSj⟩ := hSs j T' hj
      obtain ⟨p, q, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos (T'.body _) hdm
      have hpg := hgri i j T' d hc p (hpos.grade (hd.destructors_nodup ⟨h.1, hT', rfl⟩))
      rw [Option.some.inj (hgi.symm.trans hpg)] at hpS
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S' hc hSj p q ps₁ Ξ Θ B ψ hpos
      cases Option.some.inj (hget.symm.trans hg)
      have hδx : δ x ∈ S := hS.add _ _ (Grade.modality.semiring.add_comm _ _ ▸ hx')
      have hpδ : p * δs i x ∈ S := hS.le _ _ (hδ i j T' d p q ps₁ Ξ Θ B ψ hc hpos x) hδx
      have hS' : ErasesUncounted (m ⊙ p) S := (hS.mode _ hpS).symm ▸ hS
      have hidx : ((x.addNat (ps''.length + ps₁.length)).cast
          (Scope.length_extend_extend Γ ps''.length ps₁.length).symm :
            Fin ((Γ.extend ps''.length).extend ps₁.length).length) =
          (x.addNat (0 + ps''.length + ps₁.length)).cast
            (Scope.length_extend_extend_extend Γ 0 ps''.length ps₁.length).symm :=
        Fin.ext (by simp)
      rw [hidx] at ho
      exact Usage.absent hd hS' _ (hgu i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hc hSj hpos hg)
        ((GradeVector.extendParams_extendParams_addNat (δs i) _ _ ps'' ps₁ x).symm ▸
          hS.mul _ _ hpS hpδ) ho
  | .sub h hle, hx, ho => Usage.absent hd hS hΓ h (hS.le _ _ (hle x) hx) ho

-- ADE: none.
/-- A variable whose grade is in `S` does not occur in the erasure by `S` of the arguments of a
telescope checked in a mode `m` whose uses `S` does not erase, each at the grade of its entry. -/
theorem UsageArgs.absent {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {m : Mode} {S : Set Grade} [DecidablePred (· ∈ S)] (hS : ErasesUncounted m S)
    (hΓ : Γ.FirstOrder) {x : Fin Γ.length} {ps : List Parameter} {γ : GradeVector Γ.length}
    {ts : Args k Γ ps} :
    UsageArgs sig γ m ts → γ x ∈ S → ¬ (ts.terms.erase sig S hΓ (ps.map (·.usage))).Occurs x
  | .nil, _, ho => nomatch ho
  | .cons (p := p) (γ := γ₁) (δ := δ) ht hts, hx, ho => by
    have hx' : p.usage * γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Args.terms, List.map_cons, Terms.erase] at ho
    cases ho with
    | head ho =>
      by_cases hp : p.usage ∈ S
      · simp only [hp, ↓reduceIte] at ho
        exact nomatch ho
      · simp only [hp, ↓reduceIte] at ho
        have hS' : ErasesUncounted (m ⊙ p.usage) S := (hS.mode _ hp).symm ▸ hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hp (hS.add _ _ hx')) ho
    | tail ho =>
      rw [Grade.modality.semiring.add_comm] at hx'
      exact UsageArgs.absent hd hS hΓ hts (hS.add _ _ hx') ho

-- ADE: none.
/-- A variable whose grade, times `r`, is in `S` does not occur in the erasure by `S` of the
arguments of a telescope checked in the mode `m ⊙ r`, where `S` does not erase the uses of the mode
`m`, each at the grade of its entry times `r`: the state of a corecursor. -/
theorem UsageArgs.absent_mul {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {m m' : Mode} {S : Set Grade} [DecidablePred (· ∈ S)] (hS : ErasesUncounted m S)
    (hΓ : Γ.FirstOrder) {x : Fin Γ.length} {r : Grade} (hm : m ⊙ r = m') {ps : List Parameter}
    {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m' ts → r * γ x ∈ S →
      ¬ (ts.terms.erase sig S hΓ (ps.map (r * ·.usage))).Occurs x
  | .nil, _, ho => nomatch ho
  | .cons (p := p) (γ := γ₁) (δ := δ) ht hts, hx, ho => by
    have hx' : r * (p.usage * γ₁ x + δ x) ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Args.terms, List.map_cons, Terms.erase] at ho
    cases ho with
    | head ho =>
      by_cases hp : r * p.usage ∈ S
      · simp only [hp, ↓reduceIte] at ho
        exact nomatch ho
      · simp only [hp, ↓reduceIte] at ho
        have hr : r ∉ S := fun hr => hp (hS.factor _ _ (.inl hr))
        have hpu : p.usage ∉ S := fun hpu => hp (hS.factor _ _ (.inr hpu))
        have hS' : ErasesUncounted (m' ⊙ p.usage) S := by
          rw [← hm, hS.mode _ hr, hS.mode _ hpu]
          exact hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hpu (hS.add _ _ (hS.mul _ _ hr hx'))) ho
    | tail ho =>
      have hδ : r * δ x ∈ S := by
        by_cases hr : r ∈ S
        · exact hS.factor _ _ (.inl hr)
        · have h₁ := hS.mul _ _ hr hx'
          rw [Grade.modality.semiring.add_comm] at h₁
          exact hS.factor _ _ (.inr (hS.add _ _ h₁))
      exact UsageArgs.absent_mul hd hS hΓ hm hts hδ ho

end

-- ADE: none.
/-- A cast of the number of variables keeps a term less defined than another. -/
theorem Target.LessDefined.cast {n n' : Nat} (h : n = n') {M N : Target n} (hMN : M ⊑ N) :
    (h ▸ M : Target n') ⊑ h ▸ N := by
  subst h
  exact hMN

mutual

-- ADE: none.
/-- The erasure by a larger set of grades is less defined.
RFC: `\sqsubseteq_S` -/
theorem Term.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade} [DecidablePred (· ∈ S₁)]
    [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (t : Term k Γ) → t.erase sig S₂ hΓ ⊑ t.erase sig S₁ hΓ
  | .var (e := .var) .. => by simp only [Term.erase]; constructor
  | .var (e := .secondOrder ..) x _ => nomatch hΓ _ x.mem
  | .sort _ | .inst .. => .erased
  | .const .. => .const
  | .ctor D _ _ _ _ c ts => by
    simp only [Term.erase]
    cases sig.constructorCase D c with
    | some _ => exact .ctor (Terms.erase_lessDefined sig h hΓ ts _)
    | none => exact .erased
  | .recursor r _ _ _ _ _ t _ us => by
    simp only [Term.erase]
    refine .recursor ?_ (Branches.erase_lessDefined sig h hΓ us _)
    by_cases h₂ : r ∈ S₂
    · simp only [h₂, ↓reduceIte]; exact .erased
    · have h₁ : r ∉ S₁ := fun h₁ => h₂ (h r h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact Term.erase_lessDefined sig h hΓ t
  | .obs D _ _ _ _ t d bs => by
    simp only [Term.erase]
    cases sig.destructorCase D d with
    | some _ => exact .obs (Term.erase_lessDefined sig h hΓ t) (Terms.erase_lessDefined sig h hΓ bs _)
    | none => exact .erased
  | .corec _ _ _ _ _ _ ss _ vs => .corec (Terms.erase_lessDefined sig h hΓ ss _)
      (CorecBranches.erase_lessDefined sig h hΓ vs _ _)

-- ADE: none.
/-- The erasure of fields by a larger set of grades is less defined. -/
theorem Terms.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade} [DecidablePred (· ∈ S₁)]
    [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (ts : Terms k Γ) → (ps : List Grade) →
      Targets.LessDefined (ts.erase sig S₂ hΓ ps) (ts.erase sig S₁ hΓ ps)
  | .nil, _ => .nil
  | .cons _ ts, [] => .cons .erased (Terms.erase_lessDefined sig h hΓ ts [])
  | .cons t ts, p :: ps => by
    simp only [Terms.erase]
    refine .cons ?_ (Terms.erase_lessDefined sig h hΓ ts ps)
    by_cases h₂ : p ∈ S₂
    · simp only [h₂, ↓reduceIte]; exact .erased
    · have h₁ : p ∉ S₁ := fun h₁ => h₂ (h p h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact Term.erase_lessDefined sig h hΓ t

-- ADE: none.
/-- The erasure of branches by a larger set of grades is less defined. -/
theorem Branches.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade}
    [DecidablePred (· ∈ S₁)] [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : (us : Branches k Γ) → (es : List (List Nat)) →
      TargetBranches.LessDefined (us.erase sig S₂ hΓ es) (us.erase sig S₁ hΓ es)
  | .nil, _ => .nil
  | .cons a b gs u us, es => .cons (fun j => by
      by_cases h₂ : gs[j] ∈ S₂
      · exact .inl (by simp only [h₂, ↓reduceIte])
      · have h₁ : gs[j] ∉ S₁ := fun h₁ => h₂ (h _ h₁)
        exact .inr (by simp only [h₁, h₂, ↓reduceIte]))
      (Target.LessDefined.cast _ (Term.erase_lessDefined sig h ((hΓ.extend a).extend b) u))
      (Branches.erase_lessDefined sig h hΓ us es.tail)

-- ADE: none.
/-- The erasure of the branches of a corecursor by a larger set of grades is less defined. -/
theorem CorecBranches.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade}
    [DecidablePred (· ∈ S₁)] [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : (vs : CorecBranches k Γ) → (ps : List Grade) → (ks : List (Option Nat)) →
      TargetCorecBranches.LessDefined (vs.erase sig S₂ hΓ ps ks) (vs.erase sig S₁ hΓ ps ks)
  | .nil, _, _ => .nil
  | .cons 0 b c v vs, p :: ps, ks => by
    simp only [CorecBranches.erase]
    refine .cons ?_ (CorecBranches.erase_lessDefined sig h hΓ vs ps ks.tail)
    by_cases h₂ : p ∈ S₂
    · simp only [h₂, ↓reduceIte]; exact .erased
    · have h₁ : p ∉ S₁ := fun h₁ => h₂ (h p h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact Target.LessDefined.cast _ (Term.erase_lessDefined sig h ((hΓ.extend b).extend c) v)
  | .cons 0 _ _ _ vs, [], ks | .cons (_ + 1) _ _ _ vs, _, ks => by
    simp only [CorecBranches.erase]
    exact .cons .erased (CorecBranches.erase_lessDefined sig h hΓ vs _ ks.tail)

end

end Sic.Core
