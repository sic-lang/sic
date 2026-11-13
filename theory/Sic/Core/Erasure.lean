module

public import Sic.Core.Syntax.Terms
public import Sic.Math.Set

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

-- ADE: none.
/-- `k`: the resumption of a branch of a corecursor of the target language: `none`, the RFC's `⊥`,
when its destructor is not recursive, `unpack n` when the branch resumes a state of `n` entries,
which it unpacks from the new state that its position packs, and `erased n`, the RFC's `↯ₙ`, when
the branch resumes a state of `n` entries that the erasure erases, the corecursor having a grade
in the erased set, so that its new state is not read.
RFC: `\mathsf{syntax}_k` -/
inductive Resumption where
  /-- `⊥`. -/
  | none
  /-- `n`. -/
  | unpack (n : Nat)
  /-- `↯ₙ`. -/
  | erased (n : Nat)

-- ADE: none.
/-- `k₁ ⊑ k₂`: a resumption is less defined than another, itself or, for an erased state, the
resumption that unpacks a state of as many entries. -/
def Resumption.LessDefined (k₁ k₂ : Resumption) : Prop :=
  k₁ = k₂ ∨ ∃ n, k₁ = .erased n ∧ k₂ = .unpack n

-- ADE: none.
/-- The resumption of a branch whose destructor resumes, when it is recursive, a state of `n`
entries, erased when `e` holds. -/
def Resumption.ofArity (e : Bool) : Option Nat → Resumption
  | .none => .none
  | .some n => if e then .erased n else .unpack n

/-- The first resumptions of two lists of resumptions less defined at each position are. -/
theorem Resumption.headD_lessDefined {ks₁ ks₂ : List Resumption}
    (hk : ∀ i, Resumption.LessDefined (ks₂.getD i .none) (ks₁.getD i .none)) :
    Resumption.LessDefined (ks₂.headD .none) (ks₁.headD .none) := by
  have h := hk 0
  cases ks₁ <;> cases ks₂ <;> exact h

/-- The other resumptions of two lists of resumptions less defined at each position are. -/
theorem Resumption.tail_lessDefined {ks₁ ks₂ : List Resumption}
    (hk : ∀ i, Resumption.LessDefined (ks₂.getD i .none) (ks₁.getD i .none)) :
    ∀ i, Resumption.LessDefined (ks₂.tail.getD i .none) (ks₁.tail.getD i .none) := fun i => by
  have h := hk (i + 1)
  cases ks₁ <;> cases ks₂ <;> exact h

/-- The resumption of a state erased by a larger set of grades is less defined. -/
theorem Resumption.ofArity_lessDefined {e₁ e₂ : Bool} (h : e₁ = true → e₂ = true) :
    (o : Option Nat) → Resumption.LessDefined (Resumption.ofArity e₂ o) (Resumption.ofArity e₁ o)
  | .none => .inl rfl
  | .some n => by
    cases e₂ <;> cases e₁
    · exact .inl rfl
    · exact absurd (h rfl) (by decide)
    · exact .inr ⟨n, rfl, rfl⟩
    · exact .inl rfl

/-- The resumptions of the same destructors, erased by a larger set of grades, are less defined. -/
theorem Resumption.map_ofArity_lessDefined {α : Type} {e₁ e₂ : Bool} (h : e₁ = true → e₂ = true)
    (f : α → Option Nat) : (os : List α) → ∀ i, Resumption.LessDefined
      ((os.map fun o => Resumption.ofArity e₂ (f o)).getD i .none)
      ((os.map fun o => Resumption.ofArity e₁ (f o)).getD i .none)
  | [], _ => .inl rfl
  | o :: _, 0 => Resumption.ofArity_lessDefined h (f o)
  | _ :: os, i + 1 => Resumption.map_ofArity_lessDefined h f os i

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
  fields, each at the multiplicity of its field. -/
  | ctor {n : Nat} (i : Nat) (Ms : Targets n) : Target n
  /-- `rec_ρ M with N̄`: the recursor of the multiplicity `ρ` on `M`, with a branch for each
  constructor, in order. -/
  | recursor {n : Nat} (ρ : Multiplicity) (M : Target n) (Ns : TargetBranches n) : Target n
  /-- `M.dᵢ(M̄) ◀ ψ`: the observation of `M` by the destructor of the case `i` of its block, applied
  to a term for each of its `c` arguments, each at the multiplicity and the requirement of its
  argument, with the ownership `ψ` of the result of the destructor, at run time. -/
  | obs {n : Nat} (M : Target n) (i : Nat) {c : Nat} (ψ : ResultOwnership Multiplicity c)
      (Ms : Targets n) : Target n
  /-- `corec from M̄ with P̄`: the corecursor from the state `M̄`, each entry at the multiplicity of
  its entry, with a branch for each destructor, in order. -/
  | corec {n : Nat} (Ms : Targets n) (Ns : TargetCorecBranches n) : Target n

-- ADE: none.
/-- `M̄ = (M₁ ▶ π₁ ◀ ϱ₁, …, Mₐ ▶ πₐ ◀ ϱₐ)`: terms of the target language, the first one first, each
stored at the multiplicity `π` of the position that holds its value, a field, an argument or an
entry of a state, which bounds the uses of the value through this position, and with the
requirement `ϱ` of the position on the ownership of the value, at run time.
RFC: `\mathsf{syntax}_{\bar M}` -/
inductive Targets : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : Targets n
  /-- `(M ▶ π ◀ ϱ, M̄)`. -/
  | cons {n : Nat} (π ϱ : Multiplicity) (M : Target n) (Ms : Targets n) : Targets n

-- ADE: none.
/-- `N̄`: the branches of a recursor of the target language, in order; the branch
`(x̄ ▶ π̄ ◀ κ̄; ȳ ▶ π̄' ← k̄). N` is a term over a new variable for each of the `a` fields and of the
`b` recursive results, of the multiplicities `π̄` and `π̄'` at run time, each variable of a field
with the coefficient `κ` of its ownership, which multiplies the ownership of the term of the
recursor, at run time, and `k̄` gives, for each recursive result, the position of its field, or
`none`, the RFC's `⊥`, when the result is erased; the positions are counted from `0`, while the RFC
counts them from `1`.
RFC: `\mathsf{syntax}_{\bar N}` -/
inductive TargetBranches : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : TargetBranches n
  /-- `((x̄ ▶ π̄ ◀ κ̄; ȳ ▶ π̄' ← k̄). N, N̄)`. -/
  | cons {n : Nat} (a b : Nat) (πs κs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity)
      (ks : Fin b → Option Nat) (N : Target (n + (a + b))) (Ns : TargetBranches n) :
      TargetBranches n

-- ADE: none.
/-- `P̄`: the branches of a corecursor of the target language, in order; the branch
`(ȳ ▶ π̄ ◀ ϱ̄; z̄ ▶ π̄' ◀ ϱ̄' ↻ k ◀ ψ). P` is a term over a new variable for each of the `b` entries
of the state and of the `c` arguments, of the multiplicities `π̄` and `π̄'` and of the requirements
`ϱ̄` and `ϱ̄'` of their entries at run time, `k` is its resumption and `ψ` the ownership of the result
of its destructor, at run time.
RFC: `\mathsf{syntax}_{\bar P}` -/
inductive TargetCorecBranches : Nat → Type where
  /-- `()`. -/
  | nil {n : Nat} : TargetCorecBranches n
  /-- `((ȳ ▶ π̄ ◀ ϱ̄; z̄ ▶ π̄' ◀ ϱ̄' ↻ k ◀ ψ). P, P̄)`. -/
  | cons {n : Nat} (o : Resumption) (b c : Nat) (πs ϱs : Fin b → Multiplicity)
      (πs' ϱs' : Fin c → Multiplicity) (ψ : ResultOwnership Multiplicity c)
      (N : Target (n + (b + c))) (Ns : TargetCorecBranches n) : TargetCorecBranches n

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
  | recursor {n : Nat} {x : Fin n} {ρ : Multiplicity} {M : Target n} {Ns : TargetBranches n}
      (h : Target.Occurs x M) : Target.Occurs x (.recursor ρ M Ns)
  /-- In a branch of a recursor.
  RFC: `\mathsf{occurs}_M.\mathsf{with}` -/
  | branch {n : Nat} {x : Fin n} {ρ : Multiplicity} {M : Target n} {Ns : TargetBranches n}
      (h : TargetBranches.Occurs x Ns) : Target.Occurs x (.recursor ρ M Ns)
  /-- In the term of an observation.
  RFC: `\mathsf{occurs}_M.\mathsf{obs}` -/
  | obs {n : Nat} {x : Fin n} {M : Target n} {i c : Nat} {ψ : ResultOwnership Multiplicity c}
      {Ms : Targets n} (h : Target.Occurs x M) : Target.Occurs x (.obs M i ψ Ms)
  /-- In an argument of an observation.
  RFC: `\mathsf{occurs}_M.\mathsf{args}` -/
  | arg {n : Nat} {x : Fin n} {M : Target n} {i c : Nat} {ψ : ResultOwnership Multiplicity c}
      {Ms : Targets n} (h : Targets.Occurs x Ms) : Target.Occurs x (.obs M i ψ Ms)
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
  | head {n : Nat} {x : Fin n} {π ϱ : Multiplicity} {M : Target n} {Ms : Targets n}
      (h : Target.Occurs x M) : Targets.Occurs x (.cons π ϱ M Ms)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar M}.\bar M` -/
  | tail {n : Nat} {x : Fin n} {π ϱ : Multiplicity} {M : Target n} {Ms : Targets n}
      (h : Targets.Occurs x Ms) : Targets.Occurs x (.cons π ϱ M Ms)

-- ADE: none.
/-- The variable `x` occurs in one of the branches, under their new variables, which shift it. -/
inductive TargetBranches.Occurs : {n : Nat} → Fin n → TargetBranches n → Prop where
  /-- In the first branch.
  RFC: `\mathsf{occurs}_{\bar N}.N` -/
  | head {n : Nat} {x : Fin n} {a b : Nat} {πs κs : Fin a → Multiplicity}
      {πs' : Fin b → Multiplicity} {ks : Fin b → Option Nat} {N : Target (n + (a + b))}
      {Ns : TargetBranches n} (h : Target.Occurs (x.addNat (a + b)) N) :
      TargetBranches.Occurs x (.cons a b πs κs πs' ks N Ns)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar N}.\bar N` -/
  | tail {n : Nat} {x : Fin n} {a b : Nat} {πs κs : Fin a → Multiplicity}
      {πs' : Fin b → Multiplicity} {ks : Fin b → Option Nat} {N : Target (n + (a + b))}
      {Ns : TargetBranches n} (h : TargetBranches.Occurs x Ns) :
      TargetBranches.Occurs x (.cons a b πs κs πs' ks N Ns)

-- ADE: none.
/-- The variable `x` occurs in one of the branches of a corecursor, under their new variables,
which shift it. -/
inductive TargetCorecBranches.Occurs : {n : Nat} → Fin n → TargetCorecBranches n → Prop where
  /-- In the first branch.
  RFC: `\mathsf{occurs}_{\bar P}.P` -/
  | head {n : Nat} {x : Fin n} {o : Resumption} {b c : Nat} {πs ϱs : Fin b → Multiplicity}
      {πs' ϱs' : Fin c → Multiplicity} {ψ : ResultOwnership Multiplicity c}
      {N : Target (n + (b + c))} {Ns : TargetCorecBranches n}
      (h : Target.Occurs (x.addNat (b + c)) N) :
      TargetCorecBranches.Occurs x (.cons o b c πs ϱs πs' ϱs' ψ N Ns)
  /-- In the others.
  RFC: `\mathsf{occurs}_{\bar P}.\bar P` -/
  | tail {n : Nat} {x : Fin n} {o : Resumption} {b c : Nat} {πs ϱs : Fin b → Multiplicity}
      {πs' ϱs' : Fin c → Multiplicity} {ψ : ResultOwnership Multiplicity c}
      {N : Target (n + (b + c))} {Ns : TargetCorecBranches n}
      (h : TargetCorecBranches.Occurs x Ns) :
      TargetCorecBranches.Occurs x (.cons o b c πs ϱs πs' ϱs' ψ N Ns)

end

mutual

-- ADE: none.
/-- The term of the target language is a skeleton: it is built of constructors and of `↯` only,
and has no variable. -/
inductive Target.IsSkeleton : {n : Nat} → Target n → Prop where
  /-- `↯` is a skeleton.
  RFC: `\mathsf{skeleton}_M.\text{↯}` -/
  | erased {n : Nat} : Target.IsSkeleton (n := n) .erased
  /-- A constructor whose fields are skeletons is a skeleton.
  RFC: `\mathsf{skeleton}_M.c` -/
  | ctor {n : Nat} {i : Nat} {Ms : Targets n} (h : Targets.IsSkeleton Ms) :
      Target.IsSkeleton (.ctor i Ms)

-- ADE: none.
/-- The terms are skeletons, one by one. -/
inductive Targets.IsSkeleton : {n : Nat} → Targets n → Prop where
  /-- `()`.
  RFC: `\mathsf{skeleton}_{\bar M}.\varepsilon` -/
  | nil {n : Nat} : Targets.IsSkeleton (n := n) .nil
  /-- `(M, M̄)`.
  RFC: `\mathsf{skeleton}_{\bar M}.{,}` -/
  | cons {n : Nat} {π ϱ : Multiplicity} {M : Target n} {Ms : Targets n}
      (h : Target.IsSkeleton M) (hs : Targets.IsSkeleton Ms) : Targets.IsSkeleton (.cons π ϱ M Ms)

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
  | recursor {n : Nat} {ρ : Multiplicity} {M N : Target n} {Ms Ns : TargetBranches n}
      (h : Target.LessDefined M N) (hs : TargetBranches.LessDefined Ms Ns) :
      Target.LessDefined (.recursor ρ M Ms) (.recursor ρ N Ns)
  /-- A recursor on a skeleton is less defined than a recursor on any term, of more defined
  branches: the skeleton holds nothing but what the type of the term already gives.
  RFC: `{\sqsubseteq}.\mathsf{rec}_{\mathsf{skeleton}}` -/
  | skeleton {n : Nat} {ρ : Multiplicity} {M N : Target n} {Ms Ns : TargetBranches n}
      (h : Target.IsSkeleton M) (hs : TargetBranches.LessDefined Ms Ns) :
      Target.LessDefined (.recursor ρ M Ms) (.recursor ρ N Ns)
  /-- An observation is less defined than the same observation of a more defined term and
  arguments.
  RFC: `{\sqsubseteq}.d` -/
  | obs {n : Nat} {M N : Target n} {i c : Nat} {ψ : ResultOwnership Multiplicity c}
      {Ms Ns : Targets n} (h : Target.LessDefined M N) (hs : Targets.LessDefined Ms Ns) :
      Target.LessDefined (.obs M i ψ Ms) (.obs N i ψ Ns)
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
  /-- `(M ▶ π ◀ ϱ, M̄) ⊑ (N ▶ π ◀ ϱ, N̄)`.
  RFC: `{\sqsubseteq}_{\bar M}.{,}` -/
  | cons {n : Nat} {π ϱ : Multiplicity} {M N : Target n} {Ms Ns : Targets n}
      (h : Target.LessDefined M N) (hs : Targets.LessDefined Ms Ns) :
      Targets.LessDefined (.cons π ϱ M Ms) (.cons π ϱ N Ns)

-- ADE: none.
/-- The branches are less defined, one by one. -/
inductive TargetBranches.LessDefined : {n : Nat} → TargetBranches n → TargetBranches n → Prop where
  /-- `()`.
  RFC: `{\sqsubseteq}_{\bar N}.\varepsilon` -/
  | nil {n : Nat} : TargetBranches.LessDefined (n := n) .nil .nil
  /-- `((x̄ ▶ π̄ ◀ κ̄; ȳ ▶ π̄' ← k̄₁). M, M̄) ⊑ ((x̄ ▶ π̄ ◀ κ̄; ȳ ▶ π̄' ← k̄₂). N, N̄)`, where each
  recursive result of `k̄₁` is not computed or has the field it has in `k̄₂`.
  RFC: `{\sqsubseteq}_{\bar N}.{,}` -/
  | cons {n a b : Nat} {πs κs : Fin a → Multiplicity} {πs' : Fin b → Multiplicity}
      {ks₁ ks₂ : Fin b → Option Nat} {M N : Target (n + (a + b))}
      {Ms Ns : TargetBranches n} (hk : ∀ j : Fin b, ks₁ j = none ∨ ks₁ j = ks₂ j)
      (h : Target.LessDefined M N) (hs : TargetBranches.LessDefined Ms Ns) :
      TargetBranches.LessDefined (.cons a b πs κs πs' ks₁ M Ms) (.cons a b πs κs πs' ks₂ N Ns)

-- ADE: none.
/-- The branches of a corecursor are less defined, one by one. -/
inductive TargetCorecBranches.LessDefined :
    {n : Nat} → TargetCorecBranches n → TargetCorecBranches n → Prop where
  /-- `()`.
  RFC: `{\sqsubseteq}_{\bar P}.\varepsilon` -/
  | nil {n : Nat} : TargetCorecBranches.LessDefined (n := n) .nil .nil
  /-- `((ȳ ▶ π̄ ◀ ϱ̄; z̄ ▶ π̄' ◀ ϱ̄' ↻ k₁ ◀ ψ). P₁, P̄₁) ⊑ ((ȳ ▶ π̄ ◀ ϱ̄; z̄ ▶ π̄' ◀ ϱ̄' ↻ k₂ ◀ ψ). P₂, P̄₂)`.
  RFC: `{\sqsubseteq}_{\bar P}.{,}` -/
  | cons {n : Nat} {o₁ o₂ : Resumption} {b c : Nat} {πs ϱs : Fin b → Multiplicity}
      {πs' ϱs' : Fin c → Multiplicity} {ψ : ResultOwnership Multiplicity c}
      {M N : Target (n + (b + c))} {Ms Ns : TargetCorecBranches n}
      (ho : Resumption.LessDefined o₁ o₂) (h : Target.LessDefined M N)
      (hs : TargetCorecBranches.LessDefined Ms Ns) :
      TargetCorecBranches.LessDefined (.cons o₁ b c πs ϱs πs' ϱs' ψ M Ms)
        (.cons o₂ b c πs ϱs πs' ϱs' ψ N Ns)

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

-- ADE: none.
/-- The terms `(M₁ ▶ π₁ ◀ ω, …, Mₐ ▶ πₐ ◀ ω)` of a list of terms and of their multiplicities, the
first one first, each at the requirement `ω`, which states nothing. -/
def Targets.ofList {n : Nat} : List (Multiplicity × Target n) → Targets n
  | [] => .nil
  | (π, M) :: Ms => .cons π .omega M (Targets.ofList Ms)

-- ADE: none.
/-- `π̄(M̄)`: the multiplicities at which the terms are stored, the first one first.
RFC: `\mathsf{multiplicities}_{\bar M}` -/
def Targets.multiplicities {n : Nat} : Targets n → List Multiplicity
  | .nil => []
  | .cons π _ _ Ms => π :: Ms.multiplicities

-- ADE: none.
/-- `ϱ̄(M̄)`: the requirements of the positions at which the terms are stored, the first one first.
RFC: `\mathsf{requirements}_{\bar M}` -/
def Targets.requirements {n : Nat} : Targets n → List Multiplicity
  | .nil => []
  | .cons _ ϱ _ Ms => ϱ :: Ms.requirements

-- ADE: none.
/-- The skeleton of the data type `D` of the block of the type declaration `decl`, at the instance
`I`, within the depth `d`: the constructor of its case applied to `↯` for each field that is not
recursive and to the skeleton of the type of each recursive field, each at the multiplicity `0`,
since a skeleton holds no value that a use at run time reads, and at the requirement `ω`, which
states nothing, when `D` has exactly one constructor, and `↯` when it has none or several, or when
the depth is reached. -/
def TypeDeclaration.skeleton (decl : TypeDeclaration) (I : Instance decl.sorts decl.grades)
    {n : Nat} : Nat → Name → Target n
  | 0, _ => .erased
  | d + 1, D =>
    match decl.dataTypes.find? (·.name == D) with
    | some T =>
      match T.constructors with
      | [con] =>
        match decl.cases.findIdx? (fun x => x.2.1.name == D && x.2.2.name == con.name) with
        | some i => .ctor i (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => (.zero, decl.skeleton I d D')
            | none => (.zero, .erased)))
        | none => .erased
      | _ => .erased
    | none => .erased

-- ADE: none.
/-- The skeleton of the data type `D` at the instance of the qualities `qs` and of the grades `ps`,
within the depth of the number of the types of its block, when the entry declares it. -/
def Entry.skeleton {n : Nat} (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (Target n)
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.dataTypes.find? (·.name == D)).map fun _ =>
          decl.skeleton (.ofLists qs ps hq hp) decl.names.length D
      else none
    else none
  | _ => none

-- ADE: none.
/-- The skeleton of the data type `D` at the instance of the qualities `qs` and of the grades `ps`,
in the last entry of the signature that declares it, and `↯` when the signature has no such entry,
which the erasure of a recursor on an erased term reads: in a block whose types have one
constructor at most, the type of a term gives its form, which the skeleton rebuilds, so that the
recursor runs its branches on it.
The depth of the number of the types of the block is reached only on a type without closed term:
along a path of a closed term of a type, no type of the block comes twice, since each type has one
constructor, so that the term would hold a term of the same form, without end.
RFC: `\mathsf{skeleton}_D` -/
def Signature.skeleton {n : Nat} (sig : Signature) (D : Name) (qs : List Quality)
    (ps : List Grade) : Target n :=
  (sig.findSome? (Entry.skeleton D qs ps)).getD .erased

-- ADE: none.
/-- `π_l`: the multiplicity at run time of the variable of a field of grade `p` in a branch of a
recursor of grade `r`, whose recursive result, when the field has one, has the grade `e`: the uses
at run time of the field that the recursor gives, `run(r · p)`, minus those of the recursion on the
field, `run(e · r)`, the least multiplicity that the usage allows the variable; a field without
grade, in a term that no declaration types, has `ω`, which states nothing.
RFC: `\mathsf{erase}_{\bar u}.\pi` -/
def _root_.Sic.Grading.Grade.fieldMultiplicity (r : Grade) : Option Grade → Option Grade → Multiplicity
  | some p, e => (r * p).run - ((e.getD .zero) * r).run
  | none, _ => .omega

-- ADE: none.
/-- `κ_l`: the coefficient at run time of the ownership of the variable of a field of the parameter
`p`, grade `q` and requirement `r'`, in a branch of a recursor of grade `r`, which multiplies the
ownership of the term of the recursor: the value that the field requires, `r'`, is used `r · q`
times through the variable, `run(r' · (r · q))`; a field without parameter, in a term that no
declaration types, has `ω`, which states nothing.
RFC: `\mathsf{erase}_{\bar u}.\kappa` -/
def _root_.Sic.Grading.Grade.fieldCoefficient (r : Grade) : Option Parameter → Multiplicity
  | some p => (p.requirement * (r * p.usage)).run
  | none => .omega

-- ADE: none.
/-- The ownership `ψ` of the result of a destructor read for `c` arguments: its constant, and the
coefficient of each of the first `c` variables of its telescope, none for an argument beyond them, in
a term that no declaration types. -/
def ResultOwnership.toArity {α : Type} {n : Nat} (ψ : ResultOwnership α n) (c : Nat) :
    ResultOwnership α c :=
  ⟨ψ.constant, fun j => if h : (j : Nat) < n then ψ.coefficient ⟨j, h⟩ else none⟩

/-- The parameters of no argument, and the ownership of a result that has no constant and no factor,
which a destructor that the signature does not give has. -/
def ResultOwnership.noArguments : Σ ps : List Parameter, ResultOwnership Grade ps.length :=
  ⟨[], ⟨none, fun _ => none⟩⟩

mutual

-- ADE: `erase′`, in `Graded/Erasure/Extraction.agda`.
/--
`⌊t⌋_S`: the erasure of a term of a scope of variables, which replaces by `↯` the positions whose
grade is in `S`: `U_l`, `Ω_l` and the instances `T` are erased, a variable is kept, a constant
`f.{s̄; l̄; p̄}` keeps its qualities and its grades, `f.{s̄; p̄}`, a constructor keeps its case and its
fields, each at the parameter of its field, a recursor keeps the multiplicity at run time of its
grade, its term, at its grade, or the skeleton of its type when its grade is erased, and its
branches, without its instance and its motives, an observation keeps its term, the case of its
destructor, the ownership at run time of its result and its arguments, each at the parameter of its
argument, and a corecursor keeps its state, each entry at its grade times the grade of the
corecursor, and its branches, without its instance and its states; a second-order variable has no
erasure, since the scope has none.
The cases, the parameters of the fields, of the arguments and of the entries of the state, the
ownerships of the results of the destructors, the fields of the recursive results and the states
that the branches resume are those of the declarations in the signature `sig`; a constructor or an
observation whose case the signature does not give, and a field, an argument or an entry whose
parameter it does not give, in a term that no declaration types, are erased.
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
    | some i => .ctor i (ts.erase sig S hΓ ((sig.fieldParams D c qs ps).getD []))
    | none => .erased
  | .recursor r D qs _ ps _ t _ us =>
    .recursor r.run (if r ∈ S then sig.skeleton D qs ps else t.erase sig S hΓ)
      (us.erase sig S hΓ r ((sig.recursiveFields D qs ps).getD [])
        ((sig.caseFieldParams D qs ps).getD []))
  | .obs D qs _ ps _ t d bs =>
    match sig.destructorCase D d with
    | some i =>
      .obs (t.erase sig S hΓ) i
        (((sig.argumentParams D d qs ps).getD ResultOwnership.noArguments).2.map Grade.run)
        (bs.erase sig S hΓ ((sig.argumentParams D d qs ps).getD ResultOwnership.noArguments).1)
    | none => .erased
  | .corec r D qs _ ps _ ss Ss vs =>
    .corec (ss.erase sig S hΓ (((sig.position D).bind Ss.get).elim []
      fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩))
      (vs.erase sig S hΓ ((sig.destructorGrades D qs ps).getD [])
        (((sig.resumedTypes D qs ps).getD []).map
          fun h => Resumption.ofArity (decide (r ∈ S)) (h.bind Ss.arity))
        (((sig.destructorArguments D qs ps).getD []).map fun ⟨j, as⟩ =>
          ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map fun p => ⟨r * p.usage, p.requirement⟩,
            as)))

-- ADE: none.
/-- `⌊t̄⌋_{S, p̄}`: the erasure of the fields of a constructor, of the arguments of an observation
or of the state of a corecursor, each at its parameter in `ps`, of grade `p` and requirement `r`,
stored at the multiplicity `run(p)` and the requirement `run(r)`; a term without parameter is
erased, and stored at `ω` and at the requirement `ω`, which state nothing.
RFC: `\mathsf{erase}_{\bar t}` -/
def Terms.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : Terms k Γ → List Parameter → Targets Γ.length
  | .nil, _ => .nil
  | .cons _ ts, [] => .cons .omega .omega .erased (ts.erase sig S hΓ [])
  | .cons t ts, p :: ps =>
    .cons p.usage.run p.requirement.run (if p.usage ∈ S then .erased else t.erase sig S hΓ)
      (ts.erase sig S hΓ ps)

-- ADE: none.
/-- `⌊ū⌋_{S, r, ē̄, p̄̄}`: the erasure of the branches of a recursor of grade `r`, under their new
variables, each with the field of each of its recursive results, in the positions `es` of the
recursive fields of its constructor, or `none` when the grade of the result is in `S`, so that the
result is not computed; the variable of a field of grade `p`, in the grades `fs` of the fields of
its constructor, has the multiplicity `run(r · p) - run(e · r)`, where `e` is the grade of its
recursive result, or `0` when it has none, and the coefficient of ownership `run(r' · (r · p))`,
where `r'` is the requirement of the field, and the variable of a recursive result of grade `e` the
multiplicity `run(e)`.
RFC: `\mathsf{erase}_{\bar u}` -/
def Branches.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) (r : Grade) :
    Branches k Γ → List (List Nat) → List (List Parameter) → TargetBranches Γ.length
  | .nil, _, _ => .nil
  | .cons a b gs u us, es, fs =>
    .cons a b
      (fun l => r.fieldMultiplicity (((fs.headD [])[(l : Nat)]?).map (·.usage))
        (((es.headD []).idxOf? (l : Nat)).bind fun j => gs.toList[j]?))
      (fun l => r.fieldCoefficient (fs.headD [])[(l : Nat)]?)
      (fun j => gs[j].run)
      (fun j => if gs[j] ∈ S then none else (es.headD [])[(j : Nat)]?)
      (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b))
      (us.erase sig S hΓ r es.tail fs.tail)

-- ADE: none.
/-- `⌊ḡ⌋_{S, p̄, k̄, q̄̄}`: the erasure of the branches of a corecursor, under their new variables,
each at the grade `p` of its destructor in `ps`, with its resumption in `ks`; the variable of an
entry of its state or of an argument whose parameter in `pss` has the grade `q` has the multiplicity
`run(⌜11ᵐ ⊙ p⌝ · q)`, the grade that the usage gives it at run time, which is `0` when `p` has no use
at run time, since no observation then runs the branch, and the requirement at run time of its
parameter, and `ω` for both when the parameter is not given, in a term that no declaration types;
the branch has the ownership at run time of the result of its destructor in `pss`; a branch without
grade, or with non-uniform parameters, which the corecursors do not have yet, is erased, and its
variables have the multiplicity and the requirement `ω`, and its result an ownership without
constant and without factor.
RFC: `\mathsf{erase}_{\bar g}` -/
def CorecBranches.erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) :
    CorecBranches k Γ → List Grade → List Resumption →
      List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length) →
      TargetCorecBranches Γ.length
  | .nil, _, _, _ => .nil
  | .cons 0 b c v vs, p :: ps, ks, pss =>
    .cons (ks.headD .none) b c
      (fun j => (((pss.headD ([], ResultOwnership.noArguments)).1[(j : Nat)]?).map
        fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)
      (fun j => (((pss.headD ([], ResultOwnership.noArguments)).1[(j : Nat)]?).map
        (·.requirement.run)).getD .omega)
      (fun j => (((pss.headD ([], ResultOwnership.noArguments)).2.1[(j : Nat)]?).map
        fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)
      (fun j => (((pss.headD ([], ResultOwnership.noArguments)).2.1[(j : Nat)]?).map
        (·.requirement.run)).getD .omega)
      (((pss.headD ([], ResultOwnership.noArguments)).2.2.toArity c).map Grade.run)
      (if p ∈ S then .erased else Scope.length_extend_extend Γ b c ▸
        v.erase sig S ((hΓ.extend b).extend c))
      (vs.erase sig S hΓ ps ks.tail pss.tail)
  | .cons _ b c _ vs, ps, ks, pss => .cons (ks.headD .none) b c (fun _ => .omega)
      (fun _ => .omega) (fun _ => .omega) (fun _ => .omega) ⟨none, fun _ => none⟩ .erased
      (vs.erase sig S hΓ ps.tail ks.tail pss.tail)

end

/-! ## Properties -/

-- ADE: none.
/-- A cast of the number of variables keeps a term less defined than another. -/
theorem Target.LessDefined.cast {n n' : Nat} (h : n = n') {M N : Target n} (hMN : M ⊑ N) :
    (h ▸ M : Target n') ⊑ h ▸ N := by
  subst h
  exact hMN

-- ADE: none.
/-- The terms of a list are stored at the multiplicities of the list. -/
theorem Targets.multiplicities_ofList {n : Nat} :
    (Ms : List (Multiplicity × Target n)) → (Targets.ofList Ms).multiplicities = Ms.map (·.1)
  | [] => rfl
  | _ :: Ms => congrArg (_ :: ·) (Targets.multiplicities_ofList Ms)

-- ADE: none.
/-- The terms of a list are stored at the requirement `ω`. -/
theorem Targets.requirements_ofList {n : Nat} :
    (Ms : List (Multiplicity × Target n)) →
      (Targets.ofList Ms).requirements = Ms.map fun _ => .omega
  | [] => rfl
  | _ :: Ms => congrArg (_ :: ·) (Targets.requirements_ofList Ms)

-- ADE: none.
/-- The erasure of the arguments of parameters, each at its parameter, stores each at the
multiplicity at run time of the grade of its parameter. -/
theorem Args.multiplicities_erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) :
    {ps : List Parameter} → (ts : Args k Γ ps) →
      (ts.terms.erase sig S hΓ ps).multiplicities = ps.map (·.usage.run)
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg (_ :: ·) (Args.multiplicities_erase sig S hΓ ts)

-- ADE: none.
/-- The erasure of the arguments of parameters, each at its parameter, stores each at the
requirement at run time of its parameter. -/
theorem Args.requirements_erase (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) :
    {ps : List Parameter} → (ts : Args k Γ ps) →
      (ts.terms.erase sig S hΓ ps).requirements = ps.map (·.requirement.run)
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg (_ :: ·) (Args.requirements_erase sig S hΓ ts)

-- ADE: none.
/-- The erasure of the arguments of parameters, each at its parameter whose grade is mapped by `f`,
stores each at the multiplicity at run time of this image. -/
theorem Args.multiplicities_erase_map (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (f : Grade → Grade) :
    {ps : List Parameter} → (ts : Args k Γ ps) →
      (ts.terms.erase sig S hΓ (ps.map fun p => ⟨f p.usage, p.requirement⟩)).multiplicities =
        ps.map fun p => (f p.usage).run
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg (_ :: ·) (Args.multiplicities_erase_map sig S hΓ f ts)

-- ADE: none.
/-- The erasure of the arguments of parameters, each at its parameter whose grade is mapped by `f`,
stores each at the requirement at run time of its parameter. -/
theorem Args.requirements_erase_map (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (f : Grade → Grade) :
    {ps : List Parameter} → (ts : Args k Γ ps) →
      (ts.terms.erase sig S hΓ (ps.map fun p => ⟨f p.usage, p.requirement⟩)).requirements =
        ps.map (·.requirement.run)
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg (_ :: ·) (Args.requirements_erase_map sig S hΓ f ts)

-- ADE: none.
/-- The ownership of a result read for as many arguments as its telescope has is itself. -/
theorem ResultOwnership.toArity_self {α : Type} {n : Nat} (ψ : ResultOwnership α n) :
    ψ.toArity n = ψ := by
  cases ψ
  simp only [ResultOwnership.toArity, Fin.is_lt, ↓reduceDIte]

-- ADE: none.
/-- The terms of a list of skeletons are skeletons. -/
theorem Targets.isSkeleton_ofList {n : Nat} :
    (Ms : List (Multiplicity × Target n)) → (∀ πM ∈ Ms, πM.2.IsSkeleton) →
      (Targets.ofList Ms).IsSkeleton
  | [], _ => .nil
  | πM :: Ms, h => .cons (h πM List.mem_cons_self)
      (Targets.isSkeleton_ofList Ms fun πM' hM' => h πM' (List.mem_cons_of_mem _ hM'))

-- ADE: none.
/-- The skeleton of a data type of a block is a skeleton. -/
theorem TypeDeclaration.skeleton_isSkeleton (decl : TypeDeclaration)
    (I : Instance decl.sorts decl.grades) {n : Nat} :
    (d : Nat) → (D : Name) → (decl.skeleton I d D : Target n).IsSkeleton
  | 0, _ => .erased
  | d + 1, D => by
    simp only [TypeDeclaration.skeleton]
    split
    · split
      · split
        · refine .ctor (Targets.isSkeleton_ofList _ fun M hM => ?_)
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hM
          cases r with
          | some D' => exact decl.skeleton_isSkeleton I d D'
          | none => exact .erased
        · exact .erased
      · exact .erased
    · exact .erased

-- ADE: none.
/-- The skeleton of a data type in a signature is a skeleton. -/
theorem Signature.skeleton_isSkeleton {n : Nat} (sig : Signature) (D : Name) (qs : List Quality)
    (ps : List Grade) : (sig.skeleton D qs ps : Target n).IsSkeleton := by
  unfold Signature.skeleton
  induction sig with
  | nil => exact .erased
  | cons e sig ih =>
    simp only [List.findSome?_cons]
    split
    · rename_i M hM
      simp only [Option.getD_some]
      cases e with
      | typeDeclaration decl =>
        simp only [Entry.skeleton] at hM
        split at hM
        · split at hM
          · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hM
            exact decl.skeleton_isSkeleton _ _ _
          · exact nomatch hM
        · exact nomatch hM
      | _ => simp only [Entry.skeleton] at hM; exact nomatch hM
    · exact ih

mutual

-- ADE: none.
/-- No variable occurs in a skeleton. -/
theorem Target.IsSkeleton.not_occurs {n : Nat} {x : Fin n} :
    {M : Target n} → M.IsSkeleton → ¬M.Occurs x
  | _, .erased, h => nomatch h
  | _, .ctor hs, .ctor h => Targets.IsSkeleton.not_occurs hs h

-- ADE: none.
/-- No variable occurs in skeletons. -/
theorem Targets.IsSkeleton.not_occurs {n : Nat} {x : Fin n} :
    {Ms : Targets n} → Ms.IsSkeleton → ¬Ms.Occurs x
  | _, .nil, h => nomatch h
  | _, .cons h _, .head ho => Target.IsSkeleton.not_occurs h ho
  | _, .cons _ hs, .tail ho => Targets.IsSkeleton.not_occurs hs ho

end

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
    by_cases h₂ : r ∈ S₂
    · simp only [h₂, ↓reduceIte]
      exact .skeleton (sig.skeleton_isSkeleton _ _ _) (Branches.erase_lessDefined sig h hΓ _ us _ _)
    · have h₁ : r ∉ S₁ := fun h₁ => h₂ (h r h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact .recursor (Term.erase_lessDefined sig h hΓ t) (Branches.erase_lessDefined sig h hΓ _ us _ _)
  | .obs D _ _ _ _ t d bs => by
    simp only [Term.erase]
    cases sig.destructorCase D d with
    | some _ => exact .obs (Term.erase_lessDefined sig h hΓ t) (Terms.erase_lessDefined sig h hΓ bs _)
    | none => exact .erased
  | .corec r _ _ _ _ _ ss _ vs => .corec (Terms.erase_lessDefined sig h hΓ ss _)
      (CorecBranches.erase_lessDefined sig h hΓ vs _ _ _ _
        (Resumption.map_ofArity_lessDefined
          (fun h₁ => decide_eq_true (h r (of_decide_eq_true h₁))) _ _))

-- ADE: none.
/-- The erasure of fields by a larger set of grades is less defined. -/
theorem Terms.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade} [DecidablePred (· ∈ S₁)]
    [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (ts : Terms k Γ) → (ps : List Parameter) →
      Targets.LessDefined (ts.erase sig S₂ hΓ ps) (ts.erase sig S₁ hΓ ps)
  | .nil, _ => .nil
  | .cons _ ts, [] => .cons .erased (Terms.erase_lessDefined sig h hΓ ts [])
  | .cons t ts, p :: ps => by
    simp only [Terms.erase]
    refine .cons ?_ (Terms.erase_lessDefined sig h hΓ ts ps)
    by_cases h₂ : p.usage ∈ S₂
    · simp only [h₂, ↓reduceIte]; exact .erased
    · have h₁ : p.usage ∉ S₁ := fun h₁ => h₂ (h _ h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact Term.erase_lessDefined sig h hΓ t

-- ADE: none.
/-- The erasure of branches by a larger set of grades is less defined. -/
theorem Branches.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade}
    [DecidablePred (· ∈ S₁)] [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) (r : Grade) : (us : Branches k Γ) → (es : List (List Nat)) →
      (fs : List (List Parameter)) →
      TargetBranches.LessDefined (us.erase sig S₂ hΓ r es fs) (us.erase sig S₁ hΓ r es fs)
  | .nil, _, _ => .nil
  | .cons a b gs u us, es, fs => .cons (fun j => by
      by_cases h₂ : gs[j] ∈ S₂
      · exact .inl (by simp only [h₂, ↓reduceIte])
      · have h₁ : gs[j] ∉ S₁ := fun h₁ => h₂ (h _ h₁)
        exact .inr (by simp only [h₁, h₂, ↓reduceIte]))
      (Target.LessDefined.cast _ (Term.erase_lessDefined sig h ((hΓ.extend a).extend b) u))
      (Branches.erase_lessDefined sig h hΓ r us es.tail fs.tail)

-- ADE: none.
/-- The erasure of the branches of a corecursor by a larger set of grades, at less defined
resumptions, is less defined. -/
theorem CorecBranches.erase_lessDefined (sig : Signature) {S₁ S₂ : Set Grade}
    [DecidablePred (· ∈ S₁)] [DecidablePred (· ∈ S₂)] (h : S₁ ⊆ S₂) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) : (vs : CorecBranches k Γ) → (ps : List Grade) →
      (pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length)) →
      (ks₁ ks₂ : List Resumption) →
      (∀ i, Resumption.LessDefined (ks₂.getD i .none) (ks₁.getD i .none)) →
      TargetCorecBranches.LessDefined (vs.erase sig S₂ hΓ ps ks₂ pss)
        (vs.erase sig S₁ hΓ ps ks₁ pss)
  | .nil, _, _, _, _, _ => .nil
  | .cons 0 b c v vs, p :: ps, pss, ks₁, ks₂, hk => by
    simp only [CorecBranches.erase]
    refine .cons (Resumption.headD_lessDefined hk) ?_
      (CorecBranches.erase_lessDefined sig h hΓ vs ps pss.tail ks₁.tail ks₂.tail
        (Resumption.tail_lessDefined hk))
    by_cases h₂ : p ∈ S₂
    · simp only [h₂, ↓reduceIte]; exact .erased
    · have h₁ : p ∉ S₁ := fun h₁ => h₂ (h p h₁)
      simp only [h₂, h₁, ↓reduceIte]
      exact Target.LessDefined.cast _ (Term.erase_lessDefined sig h ((hΓ.extend b).extend c) v)
  | .cons 0 _ _ _ vs, [], pss, ks₁, ks₂, hk | .cons (_ + 1) _ _ _ vs, _, pss, ks₁, ks₂, hk => by
    simp only [CorecBranches.erase]
    exact .cons (Resumption.headD_lessDefined hk) .erased
      (CorecBranches.erase_lessDefined sig h hΓ vs _ pss.tail ks₁.tail ks₂.tail
        (Resumption.tail_lessDefined hk))

end

end Sic.Core
