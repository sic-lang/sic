module

public import Sic.Core.GradeVector
public import Sic.Core.Universe
public import Sic.Grade
public import Sic.Mode

/-!
# Syntax

The syntax of annex 08 of RFC 36: the terms, their arguments, the telescopes, the contexts and the
entries of the signatures.
A variable is a de Bruijn index, as in the formalization of ADE: the number of entries between the
variable and its declaration, the last entry being `0`.
A variable `x : A` and a second-order variable `X : (Θ ⊢ A)` are both used applied to a term for
each entry of their telescope, `x[]` and `X[t̄]`.
A scope tells which of its entries are variables and which are second-order variables, and gives
each second-order variable its signature: for each entry of its telescope, the grade `p` with which
it uses its argument and the requirement on the ownership of this argument, and the ownership `ψ` of
its result; the usage and the ownership of `X[t̄]` read them in the scope, from the
binder of `X`, as the usage of the other terms reads its grades from their binders; a term only uses
the variables of its scope, each applied to an argument for each entry of its telescope.
A variable `x : A` and a second-order variable `X : (ε ⊢ A)` both have an empty telescope, and only
their entries tell them apart, in the scope as in the context.

The sort and grade variables of an entry of the signature are not part of the syntax: since an entry
is checked for each instance of them, its type, its body, its parameters and its sort are given for
each instance, as a function of the qualities and of the grades, so that the terms only carry
qualities and grades.
The level variables are part of the syntax, since an entry is checked once with them: a term over
`k` level variables uses levels over `k` variables.

ADE have no second-order variables, and their levels are terms; their definition contexts hold
definitions only, transparent or opaque, without sort, level or grade variables.
Their types, the functions, the pairs, the units, the empty type, the natural numbers and the
identity type, are built in, each with its own terms, while the types here are declared, and the
terms of the data types are the constructors and the recursor of every declaration; the binders of a
motive and of a branch of a recursor are counted by the indices, as the telescopes are.
-/

@[expose] public section

namespace Sic.Core

/-- The name of an entry of the signature, or of a type that a declaration declares. -/
abbrev Name : Type := String

-- ADE: none.
/--
What the terms see of an entry of a telescope: the grade `p` with which the entry is used, and the
requirement `r` on the ownership of its argument.
-/
structure Parameter where
  /-- The grade `p` with which the entry is used. -/
  usage : Grade
  /-- The requirement `r` on the ownership of the argument. -/
  requirement : Grade

-- ADE: none.
/--
`ψ = χ₀ ∧ x_{j₁} · χ_{j₁} ∧ … ∧ x_{jₙ} · χ_{jₙ}`: the ownership of the result of a second-order
variable whose telescope has `n` entries, the meet of its constant `χ₀` and of a factor `xⱼ · χⱼ`
for some variables `xⱼ` of the telescope, the constant and each factor being optional.
A function from the variables of the telescope gives each one factor at most, in their order.
RFC: `\mathsf{syntax}_\psi`
-/
structure ResultOwnership (n : Nat) where
  /-- The constant `χ₀`, if any. -/
  constant : Option Grade
  /-- The coefficient `χⱼ` of the variable `xⱼ`, if it has a factor. -/
  coefficient : Fin n → Option Grade

/-- An entry of a scope: a variable, or a second-order variable with the parameters of the entries of
its telescope and the ownership of its result. -/
inductive Scope.Entry where
  /-- A variable `x : A`. -/
  | var
  /-- A second-order variable `X : (Θ ⊢ A ◀ ψ)`, whose telescope has the parameters `ps`, and the
  ownership `ψ` of its result. -/
  | secondOrder (ps : List Parameter) (ψ : ResultOwnership ps.length)

/-- The parameters of the telescope of an entry, none for a variable. -/
@[reducible] def Scope.Entry.params : Scope.Entry → List Parameter
  | .var => []
  | .secondOrder ps _ => ps

/-- A scope, the entries of a context, the last entry first. -/
abbrev Scope : Type := List Scope.Entry

/-- The scope `Γ` extended by `a` variables, the variables of a telescope, the first of them first. -/
def Scope.extend (Γ : Scope) : Nat → Scope
  | 0 => Γ
  | a + 1 => Scope.extend (.var :: Γ) a

-- ADE: `Fin`, the de Bruijn indices of `Definition/Untyped.agda`, without telescopes.
/-- A variable of the scope `Γ` whose entry is `e`, by its de Bruijn index.
The RFC names the variables, and an object is the same whatever names its bound variables take;
the indices make this convention needless, and so the condition that the variable that extends a
context is fresh in it, since the new variable is `0` and the others are shifted.
RFC: `\notin_\Gamma` -/
inductive Var : Scope → Scope.Entry → Type where
  /-- The last entry of the scope. -/
  | zero {Γ : Scope} {e : Scope.Entry} : Var (e :: Γ) e
  /-- An entry before the last one. -/
  | succ {Γ : Scope} {e e' : Scope.Entry} (x : Var Γ e) : Var (e' :: Γ) e

mutual

-- ADE: `Term`, in `Definition/Untyped.agda`.
/--
A term over `k` level variables in the scope `Γ`.
The core names no type: the declared types come from the type declarations of the signature.
RFC: `\mathsf{syntax}_t`
-/
inductive Term (k : Nat) : Scope → Type where
  /-- `x[t̄]`: the variable `x` applied to arguments for the entries of its telescope, `x` alone
  when it is a variable. -/
  | var {Γ : Scope} {e : Scope.Entry} (x : Var Γ e) (ts : Args k Γ e.params) : Term k Γ
  /-- The sort `κ`, `U_l` or `Ω_l`. -/
  | sort {Γ : Scope} (κ : Universe k) : Term k Γ
  /-- `f.{s̄; l̄; p̄}`: the constant `f`, defined or declared, at an instance of its variables. -/
  | const {Γ : Scope} (f : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade) :
      Term k Γ
  /-- `D.{s̄; l̄; p̄} ā`: an instance of the declared type `D`. -/
  | inst {Γ : Scope} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k Γ Δ) : Term k Γ
  /-- `T.c(t̄)`: the constructor `c` of the data type of the instance `T = D.{s̄; l̄; p̄} ā`, applied
  to a term for each of its fields; the constructor carries its instance, so that the term determines
  its type. -/
  | ctor {Γ : Scope} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k Γ Δ) (c : Name) (ts : Terms k Γ) : Term k Γ
  /-- `rec_r T t return C̄ with ū`: the recursor, which uses the term `t` of the instance
  `T = D.{s̄; l̄; p̄} ā` with the grade `r`, with a motive `C_j` for each type of the block and a
  branch `u_ji` for each constructor of each type, in the order of the declaration; the recursor
  carries the instance of the term it eliminates, so that its usage and its ownership read the
  grades and the requirements of the fields at this instance. -/
  | recursor {Γ : Scope} {Δ : Scope} (r : Grade) (D : Name) (qs : List Quality)
      (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (t : Term k Γ)
      (Cs : Motives k Γ) (us : Branches k Γ) : Term k Γ
  /-- `t.(T.d)(t̄)`: the observation of the term `t` of the instance `T = D.{s̄; l̄; p̄} ā` by its
  destructor `d`, applied to a term for each of its arguments; the observation carries the instance
  of its term, so that its usage and its ownership read the grades and the requirements of the
  destructor at this instance. -/
  | obs {Γ : Scope} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k Γ Δ) (t : Term k Γ) (d : Name) (bs : Terms k Γ) :
      Term k Γ
  /-- `corec_r T from t̄ return Θ̄ with ḡ`: the corecursor, which builds a term of the instance
  `T = D.{s̄; l̄; p̄} ā` from the state `t̄`, used with the grade `r`, with a state `Θ_j` for each
  type of the block and a branch `g_ji` for each destructor of each type, in the order of the
  declaration; the corecursor carries its instance, so that the term determines its type. -/
  | corec {Γ : Scope} {Δ : Scope} (r : Grade) (D : Name) (qs : List Quality)
      (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (ss : Terms k Γ)
      (Ss : States k Γ) (vs : CorecBranches k Γ) : Term k Γ

/-- `t̄ = (t₁, …, tₐ)`: the arguments of a telescope whose entries have the parameters `ps`, the first
one first.
RFC: `\mathsf{syntax}_{\bar t}` -/
inductive Args (k : Nat) : Scope → List Parameter → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Args k Γ []
  /-- `(t, t̄)`, the argument `t` of an entry of parameter `p`. -/
  | cons {Γ : Scope} {p : Parameter} {ps : List Parameter} (t : Term k Γ) (ts : Args k Γ ps) :
      Args k Γ (p :: ps)

/--
`ā`: the arguments of an instance, one for each parameter of the scope `Δ`, the last one first: a
term for a variable, and an abstraction `x̄. B` for a second-order variable, a term over a new
variable for each entry of its telescope.
RFC: `\mathsf{syntax}_{\bar a}`
-/
inductive InstanceArgs (k : Nat) : Scope → Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : InstanceArgs k Γ []
  /-- `(ā, x̄. B)`, the argument `B` for a parameter whose entry is `e`. -/
  | snoc {Γ Δ : Scope} {e : Scope.Entry} (as : InstanceArgs k Γ Δ)
      (B : Term k (Γ.extend e.params.length)) : InstanceArgs k Γ (e :: Δ)

/-- `t̄ = (t₁, …, tₐ)`: the terms of the fields of a constructor, the first one first, the arguments
of the telescope of its fields, whose parameters the declaration gives rather than the term.
RFC: `\mathsf{syntax}_{\bar t}` -/
inductive Terms (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Terms k Γ
  /-- `(t, t̄)`. -/
  | cons {Γ : Scope} (t : Term k Γ) (ts : Terms k Γ) : Terms k Γ

/-- `C̄`: the motives of a recursor, one for each type of the block, in order; the motive
`(x̄_nu, z). C` is a term over a new variable for each non-uniform parameter and one for the
eliminated term, of which the indices only keep the number `n` of non-uniform parameters.
RFC: `\mathsf{syntax}_{\bar C}` -/
inductive Motives (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Motives k Γ
  /-- `((x̄_nu, z). C, C̄)`, with `n` non-uniform parameters. -/
  | cons {Γ : Scope} (n : Nat) (C : Term k (Γ.extend (n + 1))) (Cs : Motives k Γ) : Motives k Γ

/-- `ū`: the branches of a recursor, one for each constructor of each type of the block, in the
order of the declaration; the branch `c(x̄; ȳ ▶ ē) ⇒ u` is a term over a new variable for each field
and one for each recursive result, with the grade `e` of each recursive result, of which the indices
only keep the numbers `n` of fields and `m` of recursive results.
RFC: `\mathsf{syntax}_{\bar u}` -/
inductive Branches (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Branches k Γ
  /-- `(c(x̄; ȳ ▶ ē) ⇒ u, ū)`, with `n` fields and `m` recursive results of grades `es`. -/
  | cons {Γ : Scope} (n m : Nat) (es : Vector Grade m) (u : Term k ((Γ.extend n).extend m))
      (us : Branches k Γ) : Branches k Γ

-- ADE: none.
/--
`Θ = (x₁ : A₁ ▶ p₁; q₁ ◀ r₁, …, xₐ : Aₐ ▶ pₐ; qₐ ◀ rₐ)`: a telescope in the scope `Γ`, whose
entries have the parameters `ps`, each type in the scope of the entries before it; the entry
`x : A ▶ p; q ◀ r` is used with the grade `p`, requires the ownership `r` of its argument, and its
variable is used with the grade `q` by the types after it.
RFC: `\mathsf{syntax}_\Theta`
-/
inductive Telescope (k : Nat) : Scope → List Parameter → Type where
  /-- `ε`. -/
  | nil {Γ : Scope} : Telescope k Γ []
  /-- `(x : A ▶ p; q ◀ r, Θ)`. -/
  | cons {Γ : Scope} {ps : List Parameter} (q : Grade) (p : Parameter) (A : Term k Γ)
      (Θ : Telescope k (.var :: Γ) ps) : Telescope k Γ (p :: ps)

/-- `Θ̄`: the states of a corecursor, one for each type of the block, in order; the state
`x̄. Θ : κ̄` is a telescope over a new variable for each non-uniform parameter, of which the indices
only keep the number `n` of non-uniform parameters, with the sorts `κ̄` of its entries, which its
packing reads.
RFC: `\mathsf{syntax}_{\bar\Theta}` -/
inductive States (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : States k Γ
  /-- `(x̄. Θ : κ̄, Θ̄)`, with `n` non-uniform parameters, a telescope `Θ` whose entries have the
  parameters `ps`, and the sorts `κ̄` of its entries. -/
  | cons {Γ : Scope} (n : Nat) {ps : List Parameter} (S : Telescope k (Γ.extend n) ps)
      (κs : List (Universe k)) (Ss : States k Γ) : States k Γ

/-- `ḡ`: the branches of a corecursor, one for each destructor of each type of the block, in the
order of the declaration; the branch `D.d(x̄; ȳ; z̄) ⇒ g` is a term over a new variable for each
non-uniform parameter, for each entry of the state and for each argument of the destructor, of which
the indices only keep the numbers `n` of non-uniform parameters, `m` of entries of the state and
`a` of arguments.
RFC: `\mathsf{syntax}_{\bar g}` -/
inductive CorecBranches (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : CorecBranches k Γ
  /-- `((x̄; ȳ; z̄). g, ḡ)`, with `n` non-uniform parameters, `m` entries of the state and
  `a` arguments. -/
  | cons {Γ : Scope} (n m a : Nat) (v : Term k (((Γ.extend n).extend m).extend a))
      (vs : CorecBranches k Γ) :
      CorecBranches k Γ

end

/-- The terms `t̄` of the arguments of a telescope, without the parameters of its entries, which the
fields of a constructor take from the declaration. -/
def Args.terms {k : Nat} {Γ : Scope} : {ps : List Parameter} → Args k Γ ps → Terms k Γ
  | [], .nil => .nil
  | _ :: _, .cons t ts => .cons t ts.terms

/-- Arguments with the same terms are the same arguments. -/
theorem Args.terms_inj {k : Nat} {Γ : Scope} :
    {ps : List Parameter} → {ts us : Args k Γ ps} → ts.terms = us.terms → ts = us
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
    simp only [Args.terms, Terms.cons.injEq] at h
    obtain ⟨rfl, h₂⟩ := h
    rw [Args.terms_inj h₂]

-- ADE: none.
/-- The type of the block whose names are `names` that the type `A` of a field, or of the result of a
destructor, is an instance of, if any: the field or the destructor is then recursive.
RFC: `\mathsf{recursive}_A` -/
def Term.blockName {k : Nat} {Γ : Scope} (names : List Name) : Term k Γ → Option Name
  | .inst D _ _ _ _ => if D ∈ names then some D else none
  | _ => none

-- ADE: none.
/-- The types of the block whose names are `names` that the types of the entries of a telescope are
instances of, in order: `some D` for a recursive field of the type `D`, `none` for the others.
RFC: `\mathsf{recursive}_\Theta` -/
def Telescope.recursion {k : Nat} {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → Telescope k Γ ps → List (Option Name)
  | [], .nil => []
  | _ :: _, .cons _ _ A Θ => A.blockName names :: Θ.recursion names

/-- The type `D` of the block whose names are `names` of the recursive field at each position of
the telescope `Θ`, the first one at `0`, and none at the other positions. -/
def Telescope.recursionAt {k : Nat} {Γ : Scope} {ps : List Parameter} (names : List Name)
    (Θ : Telescope k Γ ps) : Nat → Option Name :=
  fun i => ((Θ.recursion names)[i]?).join

-- ADE: none.
/-- The parameters of the recursive results of the fields whose entries have the parameters `ps`,
those of the recursive fields, which the types `rs` of the block mark, in order: each result has the
parameter of its field, which no judgment reads. -/
def Telescope.resultParams : List (Option Name) → List Parameter → List Parameter
  | some _ :: rs, p :: ps => p :: Telescope.resultParams rs ps
  | none :: rs, _ :: ps => Telescope.resultParams rs ps
  | [], _ | some _ :: _, [] | none :: _, [] => []

/-- Fields without recursive fields have no recursive results. -/
theorem Telescope.resultParams_of_none : {rs : List (Option Name)} → {ps : List Parameter} →
    (∀ R ∈ rs, R = none) → Telescope.resultParams rs ps = []
  | [], _, _ | some _ :: _, [], _ | none :: _, [], _ => rfl
  | some _ :: _, _ :: _, h => by cases h _ List.mem_cons_self
  | none :: rs, _ :: ps, h =>
    Telescope.resultParams_of_none (rs := rs) (ps := ps) fun R hR => h R (List.mem_cons_of_mem _ hR)

/-- The type that the type of a recursive field is an instance of is a type of the block. -/
theorem Term.blockName_mem {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {A : Term k Γ} → A.blockName names = some D → D ∈ names
  | .inst D' _ _ _ _, h => by
    by_cases hm : D' ∈ names
    · simp only [Term.blockName, hm, ↓reduceIte, Option.some.injEq] at h
      exact h ▸ hm
    · simp only [Term.blockName, hm, ↓reduceIte, reduceCtorEq] at h
  | .var .., h | .sort _, h | .const .., h | .ctor .., h | .recursor .., h | .obs .., h
  | .corec .., h => by cases h

/-- The type of a recursive field of a telescope is a type of the block. -/
theorem Telescope.recursionAt_mem {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → {Θ : Telescope k Γ ps} → {i : Nat} → Θ.recursionAt names i = some D →
      D ∈ names
  | [], .nil, _, h => by simp [Telescope.recursionAt, Telescope.recursion] at h
  | _ :: _, .cons _ _ A _, 0, h => Term.blockName_mem (by simpa [Telescope.recursionAt,
      Telescope.recursion] using h)
  | _ :: _, .cons _ _ _ Θ, i + 1, h => Telescope.recursionAt_mem (Θ := Θ) (i := i)
      (by simpa [Telescope.recursionAt, Telescope.recursion] using h)

/-- A telescope has a type of the block or none for each of its entries. -/
theorem Telescope.length_recursion {k : Nat} {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (Θ.recursion names).length = ps.length
  | [], .nil => rfl
  | _ :: _, .cons _ _ _ Θ => congrArg (· + 1) (Telescope.length_recursion names Θ)

/-- The types of the recursive fields of a telescope are types of the block. -/
theorem Telescope.mem_recursion {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → {Θ : Telescope k Γ ps} → some D ∈ Θ.recursion names → D ∈ names
  | [], .nil, h => nomatch h
  | _ :: _, .cons _ _ A Θ, h => by
    rcases List.mem_cons.1 h with h | h
    · exact Term.blockName_mem h.symm
    · exact Telescope.mem_recursion h

/-- The number of the motives `C̄`. -/
def Motives.length {k : Nat} {Γ : Scope} : Motives k Γ → Nat
  | .nil => 0
  | .cons _ _ Cs => Cs.length + 1

/-- The motive at the position `j` of the motives `C̄`, the first one at `0`, with its number of
non-uniform parameters. -/
def Motives.get {k : Nat} {Γ : Scope} : Motives k Γ → Nat → Option (Σ n, Term k (Γ.extend (n + 1)))
  | .nil, _ => none
  | .cons n C _, 0 => some ⟨n, C⟩
  | .cons _ _ Cs, j + 1 => Cs.get j

/-- The number of the branches `ū`. -/
def Branches.length {k : Nat} {Γ : Scope} : Branches k Γ → Nat
  | .nil => 0
  | .cons _ _ _ _ us => us.length + 1

/-- The branch at the position `i` of the branches `ū`, the first one at `0`, with its numbers of
fields and of recursive results. -/
def Branches.get {k : Nat} {Γ : Scope} :
    Branches k Γ → Nat → Option (Σ n m, Term k ((Γ.extend n).extend m))
  | .nil, _ => none
  | .cons n m _ u _, 0 => some ⟨n, m, u⟩
  | .cons _ _ _ _ us, i + 1 => us.get i

/-- The branch at a position of branches is one term. -/
theorem Branches.get_inj {k : Nat} {Γ : Scope} {us : Branches k Γ} {i n m : Nat}
    {u₁ u₂ : Term k ((Γ.extend n).extend m)} (h₁ : us.get i = some ⟨n, m, u₁⟩)
    (h₂ : us.get i = some ⟨n, m, u₂⟩) : u₁ = u₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- The grades `ē` of the recursive results of the branch at the position `i` of the branches `ū`,
the first one at `0`, in order, and none when there is no branch at `i`. -/
def Branches.grades {k : Nat} {Γ : Scope} : Branches k Γ → Nat → List Grade
  | .nil, _ => []
  | .cons _ _ es _ _, 0 => es.toList
  | .cons _ _ _ _ us, i + 1 => us.grades i

/-- The number of the branches `ḡ` of a corecursor. -/
def CorecBranches.length {k : Nat} {Γ : Scope} : CorecBranches k Γ → Nat
  | .nil => 0
  | .cons _ _ _ _ vs => vs.length + 1

/-- The branch at the position `i` of the branches `ḡ` of a corecursor, the first one at `0`, with
its numbers of non-uniform parameters, of entries of the state and of arguments. -/
def CorecBranches.get {k : Nat} {Γ : Scope} :
    CorecBranches k Γ → Nat → Option (Σ n m a, Term k (((Γ.extend n).extend m).extend a))
  | .nil, _ => none
  | .cons n m a v _, 0 => some ⟨n, m, a, v⟩
  | .cons _ _ _ _ vs, i + 1 => vs.get i

/-- The branch at a position of the branches of a corecursor is one term. -/
theorem CorecBranches.get_inj {k : Nat} {Γ : Scope} {vs : CorecBranches k Γ} {i n m a : Nat}
    {v₁ v₂ : Term k (((Γ.extend n).extend m).extend a)} (h₁ : vs.get i = some ⟨n, m, a, v₁⟩)
    (h₂ : vs.get i = some ⟨n, m, a, v₂⟩) : v₁ = v₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- The number of the states `Θ̄` of a corecursor. -/
def States.length {k : Nat} {Γ : Scope} : States k Γ → Nat
  | .nil => 0
  | .cons _ _ _ Ss => Ss.length + 1

/-- The state at a position of states, with its number of non-uniform parameters and the
parameters of its entries. -/
def States.get {k : Nat} {Γ : Scope} :
    States k Γ → Nat → Option (Σ n, Σ ps : List Parameter, Telescope k (Γ.extend n) ps)
  | .nil, _ => none
  | .cons n S _ _, 0 => some ⟨n, _, S⟩
  | .cons _ _ _ Ss, j + 1 => Ss.get j

/-- The sorts `κ̄` of the entries of the state at a position of states, none past the last state. -/
def States.sorts {k : Nat} {Γ : Scope} : States k Γ → Nat → List (Universe k)
  | .nil, _ => []
  | .cons _ _ κs _, 0 => κs
  | .cons _ _ _ Ss, j + 1 => Ss.sorts j

/-- The variable `x`, applied to no argument. -/
abbrev Term.var₀ {k : Nat} {Γ : Scope} (x : Var Γ .var) : Term k Γ := .var x .nil

-- ADE: `Con`, in `Definition/Untyped.agda`.
/-- A context whose scope is `Γ`, the last entry first.
RFC: `\mathsf{syntax}_\Gamma` -/
inductive Context (k : Nat) : Scope → Type where
  /-- `ε`. -/
  | empty : Context k []
  /-- `Γ, x : A`. -/
  | var {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ) : Context k (.var :: Γ)
  /-- `Γ, X : (Θ ⊢ A ◀ ψ)`, a second-order variable, whose telescope has the parameters `ps`, and the
  ownership of whose result is `ψ`. -/
  | secondOrder {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps)
      (A : Term k (Γ.extend ps.length)) (ψ : ResultOwnership ps.length) :
      Context k (.secondOrder ps ψ :: Γ)

/-! ## Signatures

An entry of the signature has sort, level and grade variables, the qualities and the grades of an
instance being given to its type, its body, its parameters and its sort. -/

/-- An instance of `j` sort variables and `g` grade variables. -/
structure Instance (j g : Nat) where
  /-- The quality of each sort variable. -/
  sorts : Fin j → Quality
  /-- The grade of each grade variable. -/
  grades : Fin g → Grade

-- ADE: none.
/-- `f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`, a constant definition, which defines the constant `f`. -/
structure ConstantDefinition where
  /-- The name `f`. -/
  name : Name
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The mode `m` in which the body is checked. -/
  mode : Mode
  /-- The ownership `p` of its value, which the body provides. -/
  ownership : Grade
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []
  /-- The body `t`, for each instance. -/
  body : Instance sorts grades → Term levels []

-- ADE: none.
/-- `f.{s̄; l̄; p̄} : A ▶ m ◀ p`, a constant declaration, which declares the constant `f`, without
body. -/
structure ConstantDeclaration where
  /-- The name `f`. -/
  name : Name
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The mode `m` of its uses. -/
  mode : Mode
  /-- The ownership `p` of its value, which the declaration states. -/
  ownership : Grade
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []

-- ADE: none.
/-- `c : Θ`, a constructor of a data type, over `j` sort variables, `g` grade variables and `k`
level variables, whose fields `Θ` are a telescope in the scope `Δ` of the parameters of the
declaration, for each instance, since their grades may be grade variables. -/
structure Constructor (j g k : Nat) (Δ : Scope) where
  /-- The name `c`. -/
  name : Name
  /-- The parameters of the fields, for each instance. -/
  params : Instance j g → List Parameter
  /-- The fields `Θ`, for each instance. -/
  fields : (I : Instance j g) → Telescope k Δ (params I)

/-- The parameters of the recursive results of the constructor `c` at the instance `I`, in a block
whose types have the names `names`. -/
abbrev Constructor.resultParams {j g k' : Nat} {Δ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) (names : List Name) : List Parameter :=
  Telescope.resultParams ((c.fields I).recursion names) (c.params I)

-- ADE: none.
/-- `D ▶ ζ ≔ c₁ : Θ₁ | … | cₙ : Θₙ`, a data type of a declaration, the grades `ζ` with which it uses
the parameters `Δ`, and its constructors, in order. -/
structure DataType (j g k : Nat) (Δ : Scope) where
  /-- The name `D`. -/
  name : Name
  /-- The grades `ζ` with which the type uses the parameters, for each instance. -/
  usage : Instance j g → GradeVector Δ.length
  /-- The constructors `c₁ : Θ₁, …, cₙ : Θₙ`. -/
  constructors : List (Constructor j g k Δ)

-- ADE: none.
/--
`d₁ : (Θ₁ ⊢ B₁ ◀ ψ₁) ▶ p₁; q₁ | … | dₙ : (Θₙ ⊢ Bₙ ◀ ψₙ) ▶ pₙ; qₙ`: the destructors of a codata type,
in the scope `Γ`, whose names are `ns`, in order.
The destructor `d : (Θ ⊢ B ◀ ψ) ▶ p; q` has the telescope `Θ` of its arguments and its result type
`B`, in the scope extended by them; its result has the ownership `ψ`, is used with the grade `p`,
and the destructor is used with the grade `q` by the types of the destructors after it, in whose
scope it is a second-order variable `d : (Θ ⊢ B ◀ ψ)`.
-/
inductive Destructors (k : Nat) : Scope → List Name → Type where
  /-- No destructor. -/
  | nil {Γ : Scope} : Destructors k Γ []
  /-- `d : (Θ ⊢ B ◀ ψ) ▶ p; q`, followed by the destructors after it. -/
  | cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} (p q : Grade)
      (Θ : Telescope k Γ ps) (B : Term k (Γ.extend ps.length)) (ψ : ResultOwnership ps.length)
      (ds : Destructors k (.secondOrder ps ψ :: Γ) ns) : Destructors k Γ (d :: ns)

-- ADE: none.
/--
`d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q | d̄₂)`: a position of the destructor `d` in the destructors `d̄` of
the scope `Γ`, as the rules of the observations decompose them, whose telescope `Θ` and result `B`
are in the scope `Ξ`, the scope `Γ` extended by the destructors `d̄₁` before it, as second-order
variables.
The position is a datum rather than a proposition, as a variable is, so that the substitution of the
destructors before it is defined on it.
-/
inductive Destructors.Pos {k : Nat} (d : Name) (p q : Grade) {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → (Ξ : Scope) → Telescope k Ξ ps →
      Term k (Ξ.extend ps.length) → ResultOwnership ps.length → Type where
  /-- `d̄ = (d : (Θ ⊢ B ◀ ψ) ▶ p; q | d̄₂)`: the first destructor. -/
  | here {Γ : Scope} {ns : List Name} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)}
      {ψ : ResultOwnership ps.length} {ds : Destructors k (.secondOrder ps ψ :: Γ) ns} :
      Destructors.Pos d p q (.cons (d := d) p q Θ B ψ ds) Γ Θ B ψ
  /-- `d̄ = (d' : (Θ' ⊢ B' ◀ ψ') ▶ p'; q' | d̄')`, where `d` is in `d̄'`. -/
  | there {Γ : Scope} {d' : Name} {ns : List Name} {ps' : List Parameter} {p' q' : Grade}
      {Θ' : Telescope k Γ ps'} {B' : Term k (Γ.extend ps'.length)} {ψ' : ResultOwnership ps'.length}
      {ds : Destructors k (.secondOrder ps' ψ' :: Γ) ns} {Ξ : Scope} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership ps.length}
      (h : Destructors.Pos d p q ds Ξ Θ B ψ) :
      Destructors.Pos d p q (.cons (d := d') p' q' Θ' B' ψ' ds) Ξ Θ B ψ

-- ADE: none.
/-- The types of the block whose names are `names` that the results of the destructors are instances
of, in order: `some D` for a recursive destructor of the type `D`, `none` for the others.
RFC: `\mathsf{recursive}_{\bar d}` -/
def Destructors.recursion {k : Nat} (names : List Name) :
    {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → List (Option Name)
  | _, _, .nil => []
  | _, _, .cons _ _ _ B _ ds => B.blockName names :: ds.recursion names

/-- The type `D` of the block whose names are `names` of the recursive destructor at each position
of the destructors `d̄`, the first one at `0`, and none at the other positions. -/
def Destructors.recursionAt {k : Nat} {Γ : Scope} {ns : List Name} (names : List Name)
    (ds : Destructors k Γ ns) : Nat → Option Name :=
  fun i => ((ds.recursion names)[i]?).join

/-- The type of the result of a recursive destructor is a type of the block. -/
theorem Destructors.recursionAt_mem {k : Nat} {names : List Name} {D : Name} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {i : Nat} →
      ds.recursionAt names i = some D → D ∈ names
  | _, _, .nil, _, h => by simp [Destructors.recursionAt, Destructors.recursion] at h
  | _, _, .cons _ _ _ B _ _, 0, h => Term.blockName_mem (A := B) (by
      simpa [Destructors.recursionAt, Destructors.recursion] using h)
  | _, _, .cons _ _ _ _ _ ds, i + 1, h => Destructors.recursionAt_mem (ds := ds) (i := i)
      (by simpa [Destructors.recursionAt, Destructors.recursion] using h)

-- ADE: none.
/-- `D ▶ ζ ≔ d₁ : … | … | dₙ : …`, a codata type of a declaration, the grades `ζ` with which it uses
the parameters `Δ`, and its destructors, in order. -/
structure CodataType (j g k : Nat) (Δ : Scope) where
  /-- The name `D`. -/
  name : Name
  /-- The grades `ζ` with which the type uses the parameters, for each instance. -/
  usage : Instance j g → GradeVector Δ.length
  /-- The names `d₁, …, dₙ` of the destructors. -/
  destructors : List Name
  /-- The destructors `d₁ : …, …, dₙ : …`, for each instance, since their grades may be grade
  variables. -/
  body : Instance j g → Destructors k Δ destructors

-- ADE: none.
/-- The types of a type declaration: a block of data types, or a block of codata types, so that a
block is homogeneous.
RFC: `\mathsf{syntax}_{\mathcal{D}}` -/
inductive TypeDeclaration.Body (j g k : Nat) (Δ : Scope) where
  /-- The data types `D₁ ≔ …; …; Dₙ ≔ …` of a block of data types. -/
  | data (types : List (DataType j g k Δ))
  /-- The codata types `D₁ ≔ …; …; Dₙ ≔ …` of a block of codata types. -/
  | codata (types : List (CodataType j g k Δ))

-- ADE: none.
/--
A type declaration, `data.{s̄; l̄; p̄ | C} Δ : κ where D₁ ≔ …; …; Dₙ ≔ …` or
`codata.{s̄; l̄; p̄ | C} Δ : κ where D₁ ≔ …; …; Dₙ ≔ …`, a block of data types or of codata types
declared together, with the constraint `C` on its instances, their parameters `Δ` and their sort `κ`.
-/
structure TypeDeclaration where
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The constraint `C` on the instances of the sort and grade variables, which gives those at which
  the declared types exist. -/
  constraint : Instance sorts grades → Prop
  /-- The scope of the parameters. -/
  scope : Scope
  /-- The parameters `Δ`, for each instance. -/
  params : Instance sorts grades → Context levels scope
  /-- The sort `κ` of the declared types, for each instance. -/
  sort : Instance sorts grades → Universe levels
  /-- The types `D₁ ≔ …; …; Dₙ ≔ …` of the block. -/
  body : TypeDeclaration.Body sorts grades levels scope

/-- The data types of a type declaration, none for a block of codata types. -/
def TypeDeclaration.dataTypes (decl : TypeDeclaration) :
    List (DataType decl.sorts decl.grades decl.levels decl.scope) :=
  match decl.body with
  | .data Ts => Ts
  | .codata _ => []

/-- The codata types of a type declaration, none for a block of data types. -/
def TypeDeclaration.codataTypes (decl : TypeDeclaration) :
    List (CodataType decl.sorts decl.grades decl.levels decl.scope) :=
  match decl.body with
  | .data _ => []
  | .codata Ts => Ts

/-- The names `D₁, …, Dₙ` of the declared types. -/
def TypeDeclaration.names (decl : TypeDeclaration) : List Name :=
  match decl.body with
  | .data Ts => Ts.map (·.name)
  | .codata Ts => Ts.map (·.name)

/-- The elements `f T` of the types `Ts`, the first type at the position `i`, each with the position
of its type and its type, in the order of the declaration: the constructors of data types, or the
destructors of codata types. -/
def TypeDeclaration.casesFrom {α β : Type} (f : α → List β) : Nat → List α → List (Nat × α × β)
  | _, [] => []
  | i, T :: Ts => (f T).map (fun c => (i, T, c)) ++ TypeDeclaration.casesFrom f (i + 1) Ts

/-- The cases of a recursor on a block: the constructors of its types, each with the position of
its type and its type, in the order of the declaration, which is that of the branches. -/
def TypeDeclaration.cases (decl : TypeDeclaration) :
    List (Nat × DataType decl.sorts decl.grades decl.levels decl.scope ×
      Constructor decl.sorts decl.grades decl.levels decl.scope) :=
  TypeDeclaration.casesFrom DataType.constructors 0 decl.dataTypes

/-- The cases of a corecursor on a block: the names of the destructors of its types, each with the
position of its type and its type, in the order of the declaration, which is that of the
branches. -/
def TypeDeclaration.codataCases (decl : TypeDeclaration) :
    List (Nat × CodataType decl.sorts decl.grades decl.levels decl.scope × Name) :=
  TypeDeclaration.casesFrom CodataType.destructors 0 decl.codataTypes

/-- An entry of the signature.
RFC: `\mathsf{syntax}_e` -/
inductive Entry where
  /-- A constant definition. -/
  | constantDefinition (d : ConstantDefinition)
  /-- A constant declaration. -/
  | constantDeclaration (c : ConstantDeclaration)
  /-- A type declaration. -/
  | typeDeclaration (decl : TypeDeclaration)

/-- The names that an entry introduces.
RFC: `\mathsf{names}_e` -/
def Entry.names : Entry → List Name
  | .constantDefinition d => [d.name]
  | .constantDeclaration c => [c.name]
  | .typeDeclaration decl => decl.names

-- ADE: `DCon`, in `Definition/Untyped/NotParametrised.agda`, which holds definitions only.
/-- A signature, its entries in order, the last entry first, so that `Σ, e` is `e :: Σ`.
The membership of the lists, `e ∈ Σ`, is the one of the signatures.
RFC: `\mathsf{syntax}_\Sigma`
RFC: `\in_\Sigma.e`
RFC: `\in_\Sigma.e,e` -/
abbrev Signature : Type := List Entry

/--
`f.{s̄; l̄; p̄} : A ▶ m ◀ p ∈ Σ`: the signature has a constant `f`, with `j` sort, `k` level and `g` grade
variables, the mode `m`, the ownership `p` and the type `A`, which the rules of the defined and of
the declared constants share.
RFC: `\in_f`
-/
inductive Signature.HasConstant (sig : Signature) :
    Name → (j k g : Nat) → Mode → Grade → (Instance j g → Term k []) → Prop where
  /-- A constant definition. -/
  | constantDefinition {d : ConstantDefinition} (h : .constantDefinition d ∈ sig) :
      HasConstant sig d.name d.sorts d.levels d.grades d.mode d.ownership d.type
  /-- A constant declaration. -/
  | constantDeclaration {c : ConstantDeclaration} (h : .constantDeclaration c ∈ sig) :
      HasConstant sig c.name c.sorts c.levels c.grades c.mode c.ownership c.type

-- ADE: none.
/--
`D.{s̄; l̄; p̄ | C} Δ : κ ▶ ζ ∈ Σ`: the signature has the declared type `D`, a data type or a codata
type of the type declaration `decl`, whose variables, constraint, parameters and sort are those of `D`, and whose grades
`ζ` are those of `D`, which the rules of the instances share.
RFC: `\in_D`
-/
def Signature.HasDeclaredType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length) : Prop :=
  .typeDeclaration decl ∈ sig ∧
    ((∃ T ∈ decl.dataTypes, T.name = D ∧ T.usage = ζ) ∨
      ∃ T ∈ decl.codataTypes, T.name = D ∧ T.usage = ζ)

-- ADE: none.
/--
`(data.{s̄; l̄; p̄ | C} Δ : κ where …; D ▶ ζ ≔ …; …) ∈ Σ`: the signature has the data type `T`, named
`D`, of the type declaration `decl`, which the rules of the constructors and of the recursors share.
-/
def Signature.HasDataType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (T : DataType decl.sorts decl.grades decl.levels decl.scope) : Prop :=
  .typeDeclaration decl ∈ sig ∧ T ∈ decl.dataTypes ∧ T.name = D

-- ADE: none.
/--
`(codata.{s̄; l̄; p̄ | C} Δ : κ where …; D ▶ ζ ≔ …; …) ∈ Σ`: the signature has the codata type `T`, named
`D`, of the type declaration `decl`, which the meaning of its instances reads.
-/
def Signature.HasCodataType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (T : CodataType decl.sorts decl.grades decl.levels decl.scope) : Prop :=
  .typeDeclaration decl ∈ sig ∧ T ∈ decl.codataTypes ∧ T.name = D

/-- A data type of the signature is one of its declared types. -/
theorem Signature.HasDataType.hasDeclaredType {sig : Signature} {D : Name} {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasDataType D decl T) :
    sig.HasDeclaredType D decl T.usage :=
  ⟨h.1, .inl ⟨T, h.2.1, h.2.2, rfl⟩⟩

/-- A codata type of the signature is one of its declared types. -/
theorem Signature.HasCodataType.hasDeclaredType {sig : Signature} {D : Name}
    {decl : TypeDeclaration} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) : sig.HasDeclaredType D decl T.usage :=
  ⟨h.1, .inr ⟨T, h.2.1, h.2.2, rfl⟩⟩

/-- The names of a type declaration are those of its data types and of its codata types, one of
which is empty. -/
theorem TypeDeclaration.names_eq (decl : TypeDeclaration) :
    decl.names = decl.dataTypes.map (·.name) ++ decl.codataTypes.map (·.name) := by
  simp only [TypeDeclaration.names, TypeDeclaration.dataTypes, TypeDeclaration.codataTypes]
  split <;> simp

/-- A data type of a type declaration is named by the declaration. -/
theorem TypeDeclaration.name_mem_names {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes) :
    T.name ∈ decl.names :=
  decl.names_eq ▸ List.mem_append_left _ (List.mem_map_of_mem hT)

/-- A name of a type declaration with a data type is the name of one of its data types. -/
theorem TypeDeclaration.mem_names_of_dataTypes {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {D : Name} (hD : D ∈ decl.names) : ∃ T' ∈ decl.dataTypes, T'.name = D := by
  unfold TypeDeclaration.dataTypes at hT ⊢
  unfold TypeDeclaration.names at hD
  split at hT
  · rename_i heq
    rw [heq] at hD
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hD
    exact ⟨T', hT', rfl⟩
  · cases hT

/-- A name of a type declaration with a codata type is the name of one of its codata types. -/
theorem TypeDeclaration.mem_names_of_codataTypes {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    {D : Name} (hD : D ∈ decl.names) : ∃ T' ∈ decl.codataTypes, T'.name = D := by
  unfold TypeDeclaration.codataTypes at hT ⊢
  unfold TypeDeclaration.names at hD
  split at hT
  · cases hT
  · rename_i heq
    rw [heq] at hD
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hD
    exact ⟨T', hT', rfl⟩

/-- The data types of a type declaration whose names are distinct have distinct names. -/
theorem TypeDeclaration.dataTypes_nodup {decl : TypeDeclaration} (h : decl.names.Nodup) :
    (decl.dataTypes.map (·.name)).Nodup :=
  (List.nodup_append.1 (decl.names_eq ▸ h)).1

/-- The type at a position of the data types of a declaration whose names are distinct is at the
same position of its names. -/
theorem TypeDeclaration.idxOf_dataTypes {decl : TypeDeclaration} (h : decl.names.Nodup) {j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hj : decl.dataTypes[j]? = some T) :
    decl.names.idxOf T.name = j := by
  obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.1 hj
  have hl : j < decl.names.length := by
    rw [decl.names_eq, List.length_append, List.length_map]
    omega
  have hn : decl.names[j] = T.name := by
    have hm : j < (decl.dataTypes.map (·.name)).length := by rw [List.length_map]; exact hj'
    simp only [decl.names_eq]
    rw [List.getElem_append_left hm, List.getElem_map, he]
  rw [← hn]
  exact h.idxOf_getElem j hl

/-- The constructors of each data type and the destructors of each codata type that an entry
declares have distinct names. -/
def Entry.ConstructorsDistinct : Entry → Prop
  | .typeDeclaration decl => (∀ T ∈ decl.dataTypes, (T.constructors.map (·.name)).Nodup) ∧
      ∀ T ∈ decl.codataTypes, T.destructors.Nodup
  | _ => True

/-- The names of a signature are distinct: each entry introduces distinct names, which no entry
before it does, and the constructors or the destructors of each type it declares have distinct
names.
RFC: `\mathsf{names}_\Sigma` -/
def Signature.Distinct : Signature → Prop
  | [] => True
  | e :: sig => Signature.Distinct sig ∧ e.names.Nodup ∧
      (∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names) ∧ e.ConstructorsDistinct

/-- In a signature whose names are distinct, a name is introduced by one entry at most.
RFC: `\mathsf{unique}_\Sigma` -/
theorem Signature.Distinct.entry_unique : {sig : Signature} → sig.Distinct → {e₁ e₂ : Entry} →
    {n : Name} → e₁ ∈ sig → e₂ ∈ sig → n ∈ e₁.names → n ∈ e₂.names → e₁ = e₂ := by
  intro sig
  induction sig with
  | nil => intro _ _ _ _ h₁; cases h₁
  | cons e sig ih =>
    intro hd e₁ e₂ n h₁ h₂ hn₁ hn₂
    obtain ⟨h, -, hfresh, -⟩ := hd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact absurd hn₂ (hfresh _ h₂' n hn₁)
    · exact absurd hn₁ (hfresh _ h₁' n hn₂)
    · exact ih h h₁' h₂' hn₁ hn₂

/-- The names that an entry of a signature whose names are distinct introduces are distinct. -/
theorem Signature.Distinct.nodup : {sig : Signature} → sig.Distinct → {e : Entry} → e ∈ sig →
    e.names.Nodup
  | [], _, _, h => nomatch h
  | _ :: _, ⟨h, hn, _, _⟩, _, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact hn
    · exact h.nodup he

/-- Two elements of a list whose images by `f` are distinct, which have the same image, are equal. -/
theorem _root_.List.eq_of_nodup_map {α β : Type} {f : α → β} :
    {l : List α} → (l.map f).Nodup → {a b : α} → a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | _ :: _, h, _, _, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (by rw [hab]; exact List.mem_map_of_mem hb') h.1
    · exact absurd (by rw [← hab]; exact List.mem_map_of_mem ha') h.1
    · exact List.eq_of_nodup_map h.2 ha' hb' hab

/-- In a signature whose names are distinct, a declared type is one data type of one type
declaration. -/
theorem Signature.Distinct.hasDataType_unique {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl₁ decl₂ : TypeDeclaration} {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : DataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDataType D decl₁ T₁) (h₂ : sig.HasDataType D decl₂ T₂) :
    decl₁ = decl₂ ∧ HEq T₁ T₂ := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.name_mem_names hT₂)
  injection he with he
  subst he
  exact ⟨rfl, heq_of_eq (List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hm₁)) hT₁
    hT₂ (hn₁.trans hn₂.symm))⟩

/-- In a signature whose names are distinct, the constructors of a declared type have distinct
names. -/
theorem Signature.Distinct.constructors_nodup : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → (T.constructors.map (·.name)).Nodup
  | [], _, _, _, _, h => nomatch h.1
  | _ :: _, ⟨hd, _, _, hc⟩, _, _, _, ⟨he, hT, hn⟩ => by
    rcases List.mem_cons.1 he with he | he
    · subst he; exact hc.1 _ hT
    · exact hd.constructors_nodup ⟨he, hT, hn⟩

/-- A codata type of a type declaration is named by the declaration. -/
theorem TypeDeclaration.codata_name_mem_names {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes) :
    T.name ∈ decl.names :=
  decl.names_eq ▸ List.mem_append_right _ (List.mem_map_of_mem hT)

/-- The codata types of a type declaration whose names are distinct have distinct names. -/
theorem TypeDeclaration.codataTypes_nodup {decl : TypeDeclaration} (h : decl.names.Nodup) :
    (decl.codataTypes.map (·.name)).Nodup :=
  (List.nodup_append.1 (decl.names_eq ▸ h)).2.1

/-- A type declaration has no data type or no codata type. -/
theorem TypeDeclaration.dataTypes_codataTypes (decl : TypeDeclaration) :
    decl.dataTypes = [] ∨ decl.codataTypes = [] := by
  simp only [TypeDeclaration.dataTypes, TypeDeclaration.codataTypes]
  split <;> simp

/-- The element at a position of a list whose elements are distinct has the position as its first
index. -/
theorem List.idxOf?_of_getElem? {α : Type} [BEq α] [LawfulBEq α] :
    {l : List α} → {j : Nat} → {a : α} → l.Nodup → l[j]? = some a → l.idxOf? a = some j
  | _ :: _, 0, _, _, h => by
    cases h
    rw [List.idxOf?_cons, beq_self_eq_true]
    rfl
  | x :: xs, _ + 1, a, hn, h => by
    have hne : (x == a) = false :=
      beq_false_of_ne fun e => (List.nodup_cons.1 hn).1 (e ▸ List.mem_of_getElem? h)
    rw [List.idxOf?_cons, hne, List.idxOf?_of_getElem? (List.nodup_cons.1 hn).2 h]
    rfl

/-- The codata type at a position of the codata types of a declaration whose names are distinct is
at the same position of its names. -/
theorem TypeDeclaration.idxOf?_codataTypes {decl : TypeDeclaration} (h : decl.names.Nodup)
    {j : Nat} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.codataTypes[j]? = some T) : decl.names.idxOf? T.name = some j := by
  have hD : decl.dataTypes = [] := by
    rcases decl.dataTypes_codataTypes with h' | h'
    · exact h'
    · rw [h'] at hj; cases hj
  have hn : decl.names = decl.codataTypes.map (·.name) := by
    rw [decl.names_eq, hD, List.map_nil, List.nil_append]
  refine List.idxOf?_of_getElem? h ?_
  rw [hn, List.getElem?_map, hj]
  rfl

/-- In a signature whose names are distinct, a codata type is one codata type of one type
declaration. -/
theorem Signature.Distinct.hasCodataType_unique {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl₁ decl₂ : TypeDeclaration}
    {T₁ : CodataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasCodataType D decl₁ T₁) (h₂ : sig.HasCodataType D decl₂ T₂) :
    decl₁ = decl₂ ∧ HEq T₁ T₂ := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.codata_name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.codata_name_mem_names hT₂)
  injection he with he
  subst he
  exact ⟨rfl, heq_of_eq (List.eq_of_nodup_map (TypeDeclaration.codataTypes_nodup (hd.nodup hm₁))
    hT₁ hT₂ (hn₁.trans hn₂.symm))⟩

/-- In a signature whose names are distinct, a declared type is not both a data type and a codata
type. -/
theorem Signature.Distinct.not_hasDataType_hasCodataType {sig : Signature} (hd : sig.Distinct)
    {D : Name} {decl₁ decl₂ : TypeDeclaration}
    {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDataType D decl₁ T₁) (h₂ : sig.HasCodataType D decl₂ T₂) : False := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.codata_name_mem_names hT₂)
  injection he with he
  subst he
  rcases decl₁.dataTypes_codataTypes with h | h
  · rw [h] at hT₁; exact nomatch hT₁
  · rw [h] at hT₂; exact nomatch hT₂

/-- In a signature whose names are distinct, the destructors of a codata type have distinct
names. -/
theorem Signature.Distinct.destructors_nodup : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → T.destructors.Nodup
  | [], _, _, _, _, h => nomatch h.1
  | _ :: _, ⟨hd, _, _, hc⟩, _, _, _, ⟨he, hT, hn⟩ => by
    rcases List.mem_cons.1 he with he | he
    · subst he; exact hc.2 _ hT
    · exact hd.destructors_nodup ⟨he, hT, hn⟩

/-- Two positions of a list whose images by `f` are distinct, which hold elements with the same
image, are equal. -/
theorem _root_.List.getElem?_inj_of_nodup_map {α β : Type} {f : α → β} :
    {l : List α} → (l.map f).Nodup → {i i' : Nat} → {a b : α} → l[i]? = some a →
      l[i']? = some b → f a = f b → i = i'
  | [], _, _, _, _, _, ha, _, _ => nomatch ha
  | _ :: l, h, i, i', _, _, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    match i, i', ha, hb with
    | 0, 0, _, _ => rfl
    | 0, i' + 1, ha, hb =>
      cases ha
      exact absurd (hab ▸ List.mem_map_of_mem (List.mem_of_getElem? hb)) h.1
    | i + 1, 0, ha, hb =>
      cases hb
      exact absurd (hab.symm ▸ List.mem_map_of_mem (List.mem_of_getElem? ha)) h.1
    | i + 1, i' + 1, ha, hb => exact congrArg (· + 1) (List.getElem?_inj_of_nodup_map h.2 ha hb hab)

/-- A case of the types `Ts` is an element of one of them. -/
theorem TypeDeclaration.mem_casesFrom {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {x : Nat × α × β} →
      x ∈ TypeDeclaration.casesFrom f i Ts → x.2.1 ∈ Ts ∧ x.2.2 ∈ f x.2.1
  | _, [], _, h => nomatch h
  | _, _ :: _, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact ⟨List.mem_cons_self, hc⟩
    · obtain ⟨h₁, h₂⟩ := TypeDeclaration.mem_casesFrom h
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩

/-- A case of the types `Ts`, the first one at the position `i`, holds the position of its type. -/
theorem TypeDeclaration.getElem?_of_mem_casesFrom {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {j' : Nat} → {T : α} → {c : β} →
      (j', T, c) ∈ TypeDeclaration.casesFrom f i Ts → i ≤ j' ∧ Ts[j' - i]? = some T
  | _, [], _, _, _, h => nomatch h
  | i, _ :: Ts, j', _, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨_, _, he⟩ := List.mem_map.1 h
      cases he
      exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨hle, hT⟩ := TypeDeclaration.getElem?_of_mem_casesFrom h
      refine ⟨Nat.le_of_succ_le hle, ?_⟩
      have he : j' - i = (j' - (i + 1)) + 1 := by omega
      rw [he, List.getElem?_cons_succ]
      exact hT

/-- An element of the type at the position `j'` of the types `Ts` is a case of them. -/
theorem TypeDeclaration.mem_casesFrom_of {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {j' : Nat} → {T : α} → {c : β} → Ts[j']? = some T → c ∈ f T →
      (i + j', T, c) ∈ TypeDeclaration.casesFrom f i Ts
  | _, [], _, _, _, h, _ => nomatch h
  | i, _ :: Ts, 0, _, _, h, hc => by
    cases h
    exact List.mem_append_left _ (List.mem_map_of_mem hc)
  | i, _ :: Ts, j' + 1, _, _, h, hc => by
    have he : i + (j' + 1) = (i + 1) + j' := by omega
    rw [he]
    exact List.mem_append_right _ (TypeDeclaration.mem_casesFrom_of h hc)

/-- The cases of types with distinct names, whose elements have distinct names, have distinct
names of types and of elements. -/
theorem TypeDeclaration.casesFrom_nodup {α β : Type} {f : α → List β} {nα : α → Name}
    {nβ : β → Name} :
    {i : Nat} → {Ts : List α} → (Ts.map nα).Nodup → (∀ T ∈ Ts, ((f T).map nβ).Nodup) →
        ((TypeDeclaration.casesFrom f i Ts).map fun x => (nα x.2.1, nβ x.2.2)).Nodup
  | _, [], _, _ => List.nodup_nil
  | i, T :: Ts, hn, hc => by
    rw [List.map_cons, List.nodup_cons] at hn
    have he : (TypeDeclaration.casesFrom f i (T :: Ts)).map (fun x => (nα x.2.1, nβ x.2.2)) =
        ((f T).map nβ).map (Prod.mk (nα T)) ++
          (TypeDeclaration.casesFrom f (i + 1) Ts).map (fun x => (nα x.2.1, nβ x.2.2)) := by
      simp only [TypeDeclaration.casesFrom, List.map_append, List.map_map]
      rfl
    rw [he]
    refine List.nodup_append.2 ⟨(hc T List.mem_cons_self).map (Prod.mk (nα T))
      (fun _ _ hab he => hab (Prod.mk.inj he).2),
      TypeDeclaration.casesFrom_nodup hn.2 fun T hT => hc T (List.mem_cons_of_mem _ hT), ?_⟩
    intro a ha b hb hab
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    have hn' : nα T = nα x.2.1 := congrArg Prod.fst hab
    exact hn.1 (hn' ▸ List.mem_map_of_mem (TypeDeclaration.mem_casesFrom hx).1)

/-- In a signature whose names are distinct, the cases of a type declaration have distinct names of
types and of constructors. -/
theorem Signature.Distinct.cases_nodup {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (h : .typeDeclaration decl ∈ sig) :
    (decl.cases.map fun x => (x.2.1.name, x.2.2.name)).Nodup :=
  TypeDeclaration.casesFrom_nodup (TypeDeclaration.dataTypes_nodup (hd.nodup h)) fun _ hT => hd.constructors_nodup ⟨h, hT, rfl⟩

/-- In a signature whose names are distinct, the cases of a corecursor on a type declaration have
distinct names of types and of destructors. -/
theorem Signature.Distinct.codataCases_nodup {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (h : .typeDeclaration decl ∈ sig) :
    (decl.codataCases.map fun x => (x.2.1.name, x.2.2)).Nodup :=
  TypeDeclaration.casesFrom_nodup (nβ := id) (TypeDeclaration.codataTypes_nodup (hd.nodup h))
    fun _ hT => by rw [List.map_id]; exact hd.destructors_nodup ⟨h, hT, rfl⟩

/-- The `n` elements of a list of length `n`, numbered. -/
def _root_.List.getFin {α : Type} (l : List α) {n : Nat} (h : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

/-- The elements of a list mapped by `f` are the elements of the list mapped by `f`. -/
theorem _root_.List.getFin_map {α β : Type} (f : α → β) (l : List α) {n : Nat}
    (h : (l.map f).length = n) :
    (l.map f).getFin h = fun i => f (l.getFin ((List.length_map f).symm.trans h) i) := by
  funext i
  simp [List.getFin]

/-- The numbered elements of a list are the list. -/
theorem _root_.List.ofFn_getFin {α : Type} :
    (l : List α) → {n : Nat} → (h : l.length = n) → List.ofFn (l.getFin h) = l
  | [], _, h => by subst h; rfl
  | a :: l, _, h => by
    subst h
    rw [List.ofFn_succ]
    exact congrArg (a :: ·) (List.ofFn_getFin l rfl)

/-- The instance that gives the sort variables the sorts `qs` and the grade variables the grades
`ps`. -/
def Instance.ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (hq : qs.length = j)
    (hp : ps.length = g) : Instance j g :=
  ⟨qs.getFin hq, ps.getFin hp⟩

-- ADE: none.
/-- The grades `p` of the fields of the constructor `c` of the declared type `D` at the instance of
the qualities `qs` and of the grades `ps`, when the entry declares them. -/
def Entry.fieldGrades (D c : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Grade)
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.dataTypes.find? (·.name == D)).bind fun T =>
          (T.constructors.find? (·.name == c)).map fun con =>
            (con.params (.ofLists qs ps hq hp)).map (·.usage)
      else none
    else none
  | _ => none

-- ADE: none.
/-- The grades `p` of the fields of the constructor `c` of the declared type `D` at the instance of
the qualities `qs` and of the grades `ps`, in the last entry of the signature that declares them,
which the erasure of a constructor reads.
RFC: `\mathsf{grades}_c` -/
def Signature.fieldGrades (sig : Signature) (D c : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Grade) :=
  sig.findSome? (Entry.fieldGrades D c qs ps)

/-- The parameters of the arguments of the destructor `d`, when the destructors have one. -/
def Destructors.arguments {k : Nat} : {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Name →
    Option (List Parameter)
  | _, [], .nil, _ => none
  | _, d' :: _, .cons (ps := ps) _ _ _ _ _ ds, d => if d' = d then some ps else ds.arguments d

-- ADE: none.
/-- The grades `p` of the arguments of the destructor `d` of the declared type `D` at the instance
of the qualities `qs` and of the grades `ps`, when the entry declares them. -/
def Entry.argumentGrades (D d : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Grade)
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.codataTypes.find? (·.name == D)).bind fun T =>
          ((T.body (.ofLists qs ps hq hp)).arguments d).map fun ps' => ps'.map (·.usage)
      else none
    else none
  | _ => none

-- ADE: none.
/-- The grades `p` of the arguments of the destructor `d` of the declared type `D` at the instance
of the qualities `qs` and of the grades `ps`, in the last entry of the signature that declares
them, which the erasure of an observation reads.
RFC: `\mathsf{grades}_d` -/
def Signature.argumentGrades (sig : Signature) (D d : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Grade) :=
  sig.findSome? (Entry.argumentGrades D d qs ps)

/-- The grade `p` of the destructor `d`, when the destructors have one. -/
def Destructors.grade {k : Nat} : {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Name →
    Option Grade
  | _, [], .nil, _ => none
  | _, d' :: _, .cons p _ _ _ _ ds, d => if d' = d then some p else ds.grade d

/-- The type of the block whose names are `names` that the result of the destructor `d` is an
instance of, when the destructors have `d` and its result is one. -/
def Destructors.resultName {k : Nat} (names : List Name) : {Γ : Scope} → {ns : List Name} →
    Destructors k Γ ns → Name → Option Name
  | _, [], .nil, _ => none
  | _, d' :: _, .cons _ _ _ B _ ds, d => if d' = d then B.blockName names else ds.resultName names d

/-- The constant `χ₀` of the ownership of the result of the destructor `d`, when the destructors have
`d` and the ownership has one. -/
def Destructors.resultConstant {k : Nat} : {Γ : Scope} → {ns : List Name} →
    Destructors k Γ ns → Name → Option Grade
  | _, [], .nil, _ => none
  | _, d' :: _, .cons _ _ _ _ ψ ds, d => if d' = d then ψ.constant else ds.resultConstant d

-- ADE: none.
/-- The grades `p` of the destructors of the cases of the block of the declared type `D`, in the
order of the declaration, at the instance of the qualities `qs` and of the grades `ps`, when the
entry declares them. -/
def Entry.destructorGrades (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Grade)
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.codataTypes.find? (·.name == D)).bind fun _ =>
          decl.codataCases.mapM fun c => (c.2.1.body (.ofLists qs ps hq hp)).grade c.2.2
      else none
    else none
  | _ => none

-- ADE: none.
/-- The grades `p` of the destructors of the cases of the block of the declared type `D`, in the
order of the declaration, at the instance of the qualities `qs` and of the grades `ps`, in the last
entry of the signature that declares them, which the erasure of a corecursor reads.
RFC: `\mathsf{grades}_{\bar g}` -/
def Signature.destructorGrades (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Grade) :=
  sig.findSome? (Entry.destructorGrades D qs ps)

-- ADE: none.
/-- The position of the declared type `D` in the block of the entry, when the entry declares it. -/
def Entry.position (D : Name) : Entry → Option Nat
  | .typeDeclaration decl => decl.names.idxOf? D
  | _ => none

-- ADE: none.
/-- The position of the declared type `D` in its block, in the last entry of the signature that
declares it, which the erasure of a corecursor reads to find the state of `D`; the positions are
counted from `0`, as the indices of the lists, while the RFC counts them from `1`.
RFC: `\mathsf{position}_D` -/
def Signature.position (sig : Signature) (D : Name) : Option Nat :=
  sig.findSome? (Entry.position D)

/-- An element of a list whose images by `f` are distinct is the first one with its image. -/
theorem _root_.List.find?_of_nodup_map {α : Type} {f : α → Name} :
    {l : List α} → (l.map f).Nodup → {a : α} → a ∈ l → l.find? (f · == f a) = some a
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact List.find?_cons_of_pos (beq_iff_eq.2 rfl)
    · have hne : ¬ (fun x => f x == f a) b = true := fun hb => h.1 (beq_iff_eq.1 hb ▸
        List.mem_map_of_mem ha')
      rw [List.find?_cons_of_neg (p := fun x => f x == f a) (l := l) hne]
      exact List.find?_of_nodup_map h.2 ha'

/-- A type declaration gives the grades of the fields of a constructor of one of its types, whose
types and constructors have distinct names, at the instance. -/
theorem Entry.fieldGrades_of_mem {decl : TypeDeclaration}
    (hn : (decl.dataTypes.map (·.name)).Nodup)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (hc : (T.constructors.map (·.name)).Nodup)
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope} (hcon : con ∈ T.constructors)
    {qs : List Quality} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) :
    Entry.fieldGrades T.name con.name qs ps (.typeDeclaration decl) =
      some ((con.params (.ofLists qs ps hq hp)).map (·.usage)) := by
  simp only [Entry.fieldGrades]
  split
  · try split
    all_goals first
      | contradiction
      | rw [List.find?_of_nodup_map hn hT, Option.bind_some, List.find?_of_nodup_map hc hcon,
          Option.map_some]
  · contradiction

/-- An entry that does not introduce the name `D` gives the grades of the fields of no constructor
of `D`. -/
theorem Entry.fieldGrades_of_not_mem {D c : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.fieldGrades D c qs ps e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.dataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.name_mem_names hT)
    simp only [Entry.fieldGrades]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.bind_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- In a signature whose names are distinct, the grades of the fields of a constructor of a declared
type are those of its telescope at the instance. -/
theorem Signature.Distinct.fieldGrades : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {con : Constructor decl.sorts decl.grades decl.levels decl.scope} →
    con ∈ T.constructors → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.fieldGrades D con.name qs ps = some ((con.params (.ofLists qs ps hq hp)).map (·.usage))
  | [], _, _, _, _, h, _, _, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, con, hcon, qs, ps, hq, hp => by
    unfold Signature.fieldGrades
    rcases List.mem_cons.1 he with rfl | he'
    · have hg := Entry.fieldGrades_of_mem (TypeDeclaration.dataTypes_nodup hn) hT (hc.1 T hT) hcon
        hq hp
      rw [hD] at hg
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.fieldGrades_of_not_mem hDe]; rfl)]
      exact hd.fieldGrades ⟨he', hT, hD⟩ hcon hq hp

/-- The destructor at a position in destructors is named by them. -/
theorem Destructors.Pos.mem {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → Destructors.Pos d p q ds Ξ Θ B ψ → d ∈ ns
  | _, _, _, _, _, _, _, .here => List.mem_cons_self
  | _, _, _, _, _, _, _, .there h => List.mem_cons_of_mem _ h.mem

/-- Destructors with distinct names give the destructor at a position the parameters of its
arguments. -/
theorem Destructors.Pos.arguments {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → ns.Nodup → Destructors.Pos d p q ds Ξ Θ B ψ →
        ds.arguments d = some ps
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.arguments]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.arguments, hne, ↓reduceIte]
    exact h.arguments (List.nodup_cons.1 hn).2

/-- A type declaration gives the grades of the arguments of a destructor of one of its codata types,
whose types and destructors have distinct names, at the instance. -/
theorem Entry.argumentGrades_of_mem {decl : TypeDeclaration}
    (hn : (decl.codataTypes.map (·.name)).Nodup)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    (hc : T.destructors.Nodup) {qs : List Quality} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership ps'.length} (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) :
    Entry.argumentGrades T.name d qs ps (.typeDeclaration decl) = some (ps'.map (·.usage)) := by
  simp only [Entry.argumentGrades]
  split
  · try split
    all_goals first
      | contradiction
      | rw [List.find?_of_nodup_map hn hT, Option.bind_some, hd.arguments hc, Option.map_some]
  · contradiction

/-- An entry that does not introduce the name `D` gives the grades of the arguments of no destructor
of `D`. -/
theorem Entry.argumentGrades_of_not_mem {D d : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.argumentGrades D d qs ps e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.codataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.codata_name_mem_names hT)
    simp only [Entry.argumentGrades]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.bind_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- In a signature whose names are distinct, the grades of the arguments of a destructor of a
declared type are those of its telescope at the instance. -/
theorem Signature.Distinct.argumentGrades : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) → {d : Name} → {p q : Grade} →
    {ps' : List Parameter} → {Ξ : Scope} → {Θ : Telescope decl.levels Ξ ps'} →
    {B : Term decl.levels (Ξ.extend ps'.length)} → {ψ : ResultOwnership ps'.length} →
    (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
    sig.argumentGrades D d qs ps = some (ps'.map (·.usage))
  | [], _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp, _, _, _, _, _, _, _,
      _, hpos => by
    unfold Signature.argumentGrades
    rcases List.mem_cons.1 he with rfl | he'
    · have hg := Entry.argumentGrades_of_mem (TypeDeclaration.codataTypes_nodup hn) hT
        (hc.2 T hT) hq hp hpos
      rw [hD] at hg
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.argumentGrades_of_not_mem hDe]; rfl)]
      exact hd.argumentGrades ⟨he', hT, hD⟩ hq hp hpos

/-- Destructors with distinct names give the destructor at a position its grade. -/
theorem Destructors.Pos.grade {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → ns.Nodup → Destructors.Pos d p q ds Ξ Θ B ψ →
        ds.grade d = some p
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.grade]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.grade, hne, ↓reduceIte]
    exact h.grade (List.nodup_cons.1 hn).2

/-- The destructor at a position of destructors whose names are distinct has the result there. -/
theorem Destructors.Pos.resultName {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter}
    (names : List Name) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → ns.Nodup → Destructors.Pos d p q ds Ξ Θ B ψ →
        ds.resultName names d = B.blockName names
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.resultName]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.resultName, hne, ↓reduceIte]
    exact h.resultName names (List.nodup_cons.1 hn).2

/-- The destructor at a position of destructors whose names are distinct has the ownership of its
result there. -/
theorem Destructors.Pos.resultConstant {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → ns.Nodup → Destructors.Pos d p q ds Ξ Θ B ψ →
        ds.resultConstant d = ψ.constant
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.resultConstant]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.resultConstant, hne, ↓reduceIte]
    exact h.resultConstant (List.nodup_cons.1 hn).2

/-- The position of a destructor in the destructors, as a number, the first one at `0`. -/
def Destructors.Pos.index {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → Destructors.Pos d p q ds Ξ Θ B ψ → Nat
  | _, _, _, _, _, _, _, .here => 0
  | _, _, _, _, _, _, _, .there h => h.index + 1

/-- The destructor at a position is recursive, of the type of the block that its result names, at
the number of the position. -/
theorem Destructors.Pos.recursionAt_index {k : Nat} {d : Name} {p q : Grade} {ps : List Parameter}
    (names : List Name) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hpos : Destructors.Pos d p q ds Ξ Θ B ψ) →
        ds.recursionAt names hpos.index = B.blockName names
  | _, _, _, _, _, _, _, .here => by
    simp [Destructors.Pos.index, Destructors.recursionAt, Destructors.recursion]
  | _, _, _, _, _, _, _, .there h => by
    simp only [Destructors.Pos.index, Destructors.recursionAt, Destructors.recursion,
      List.getElem?_cons_succ]
    exact h.recursionAt_index names

/-- A destructor named by destructors has a position in them. -/
theorem Destructors.exists_pos {k : Nat} {d : Name} :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) → d ∈ ns →
      ∃ (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k Ξ ps)
        (B : Term k (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length),
        Nonempty (Destructors.Pos d p q ds Ξ Θ B ψ)
  | _, _, .nil, h => nomatch h
  | _, d' :: _, .cons p q Θ B ψ ds, h => by
    by_cases he : d' = d
    · subst he
      exact ⟨p, q, _, _, Θ, B, ψ, ⟨.here⟩⟩
    · have h' : d ∈ _ := (List.mem_cons.1 h).resolve_left fun h'' => he h''.symm
      obtain ⟨p', q', ps', Ξ, Θ', B', ψ', ⟨hpos⟩⟩ := Destructors.exists_pos ds h'
      exact ⟨p', q', ps', Ξ, Θ', B', ψ', ⟨.there hpos⟩⟩

/-- The results of a function at the elements of a list, all defined, are at the same positions as
the elements. -/
theorem _root_.List.getElem?_of_mapM {α β : Type} {f : α → Option β} :
    {l : List α} → {l' : List β} → l.mapM f = some l' → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, f a = some b ∧ l'[i]? = some b
  | [], _, _, _, _, ha => nomatch ha
  | a :: l, l', h, i, a', ha => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          cases ha
          exact ⟨b, hfa, rfl⟩
        | succ i => exact List.getElem?_of_mapM hl ha

/-- A function defined at every element of a list is defined at the list. -/
theorem _root_.List.exists_mapM_eq_some {α β : Type} {f : α → Option β} :
    {l : List α} → (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := List.exists_mapM_eq_some (l := l) fun a' ha' =>
      h a' (List.mem_cons_of_mem _ ha')
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-- Destructors with distinct names, at their names, all have a grade. -/
theorem Destructors.isSome_grade {k : Nat} :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) → ns.Nodup → ∀ d ∈ ns,
      ∃ p, ds.grade d = some p := fun ds hn d hd => by
  obtain ⟨p, q, ps, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos ds hd
  exact ⟨p, hpos.grade hn⟩

/-- A type declaration gives the grades of the destructors of the cases of its block, whose types
and destructors have distinct names, at the instance: the grade of the destructor of each case. -/
theorem Entry.destructorGrades_of_mem {decl : TypeDeclaration}
    (hn : (decl.codataTypes.map (·.name)).Nodup)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    (hc : ∀ T ∈ decl.codataTypes, T.destructors.Nodup) {qs : List Quality} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades) :
    ∃ gs, Entry.destructorGrades T.name qs ps (.typeDeclaration decl) = some gs ∧
      ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name),
        decl.codataCases[i]? = some (j, T', d) → ∀ p, (T'.body (.ofLists qs ps hq hp)).grade d = some p →
          gs[i]? = some p := by
  have hall : ∀ c ∈ decl.codataCases, ∃ p, (c.2.1.body (.ofLists qs ps hq hp)).grade c.2.2 = some p :=
    fun c hcm => by
      obtain ⟨hT', hd⟩ := TypeDeclaration.mem_casesFrom hcm
      exact Destructors.isSome_grade _ (hc _ hT') _ hd
  obtain ⟨gs, hgs⟩ := List.exists_mapM_eq_some hall
  refine ⟨gs, ?_, fun i j T' d hi p hpg => ?_⟩
  · simp only [Entry.destructorGrades]
    split
    · try split
      all_goals first
        | contradiction
        | rw [List.find?_of_nodup_map hn hT, Option.bind_some, hgs]
    · contradiction
  · obtain ⟨b, hb, hgi⟩ := List.getElem?_of_mapM hgs hi
    rw [hpg] at hb
    cases hb
    exact hgi

/-- An entry that does not introduce the name `D` gives the grades of the destructors of no block
of `D`. -/
theorem Entry.destructorGrades_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.destructorGrades D qs ps e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.codataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.codata_name_mem_names hT)
    simp only [Entry.destructorGrades]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.bind_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- In a signature whose names are distinct, the grades of the destructors of the cases of the
block of a codata type are those of its declaration, at the instance. -/
theorem Signature.Distinct.destructorGrades : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    ∃ gs, sig.destructorGrades D qs ps = some gs ∧
      ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name),
        decl.codataCases[i]? = some (j, T', d) → ∀ p, (T'.body (.ofLists qs ps hq hp)).grade d = some p →
          gs[i]? = some p
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    unfold Signature.destructorGrades
    rcases List.mem_cons.1 he with rfl | he'
    · obtain ⟨gs, hg, hgs⟩ := Entry.destructorGrades_of_mem (TypeDeclaration.codataTypes_nodup hn)
        hT (hc.2) hq hp
      rw [hD] at hg
      exact ⟨gs, by rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg], hgs⟩
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.destructorGrades_of_not_mem hDe]; rfl)]
      exact hd.destructorGrades ⟨he', hT, hD⟩ hq hp

/-- The index of the image of an element in the images of a list, distinct, is its position. -/
theorem _root_.List.idxOf?_map_of_nodup {α : Type} {f : α → Name} :
    {l : List α} → (l.map f).Nodup → {i : Nat} → {a : α} → l[i]? = some a →
      (l.map f).idxOf? (f a) = some i
  | [], _, _, _, ha => nomatch ha
  | b :: l, hn, i, a, ha => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero =>
      cases ha
      rw [List.map_cons, List.idxOf?_cons, beq_iff_eq.2 rfl, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    | succ i =>
      have hne : f b ≠ f a := fun he => hn.1 (he ▸ List.mem_map_of_mem (List.mem_of_getElem? ha))
      rw [List.map_cons, List.idxOf?_cons, beq_eq_false_iff_ne.2 hne,
        ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true), List.idxOf?_map_of_nodup hn.2 ha]
      rfl

/-- In a signature whose names are distinct, the position of a codata type is its position in the
block of its declaration. -/
theorem Signature.Distinct.position : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {h' : Nat} → decl.codataTypes[h']? = some T →
    sig.position D = some h'
  | [], _, _, _, _, h, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, h', hh => by
    unfold Signature.position
    rcases List.mem_cons.1 he with rfl | he'
    · have hc : decl.names = decl.codataTypes.map (·.name) := by
        rw [decl.names_eq]
        rcases decl.dataTypes_codataTypes with h | h
        · rw [h]; rfl
        · rw [h] at hT; exact nomatch hT
      have hp : Entry.position D (.typeDeclaration decl) = some h' := by
        simp only [Entry.position, hc, ← hD]
        exact List.idxOf?_map_of_nodup (TypeDeclaration.codataTypes_nodup hn) hh
      rw [List.findSome?_cons_of_isSome (by rw [hp]; rfl), hp]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      have hp : Entry.position D e = none := by
        cases e with
        | typeDeclaration decl' =>
          simp only [Entry.position]
          exact List.idxOf?_eq_none_iff.2 hDe
        | _ => rfl
      rw [List.findSome?_cons_of_isNone (by rw [hp]; rfl)]
      exact hd.position ⟨he', hT, hD⟩ hh

/-- The length of the scope `Γ` extended by `a` variables. -/
theorem Scope.length_extend (Γ : Scope) : (a : Nat) → (Γ.extend a).length = Γ.length + a
  | 0 => rfl
  | a + 1 => (Scope.length_extend (.var :: Γ) a).trans (Nat.succ_add _ _)

/-- The length of the scope `Γ` extended by `a`, then `b` variables, as the scope of a branch of a
recursor is. -/
theorem Scope.length_extend_extend (Γ : Scope) (a b : Nat) :
    ((Γ.extend a).extend b).length = Γ.length + (a + b) := by
  rw [Scope.length_extend, Scope.length_extend]
  omega

/-- The length of the scope `Γ` extended by `a`, then `b`, then `c` variables, as the scope of a
branch of a corecursor is. -/
theorem Scope.length_extend_extend_extend (Γ : Scope) (a b c : Nat) :
    (((Γ.extend a).extend b).extend c).length = Γ.length + (a + b + c) := by
  rw [Scope.length_extend, Scope.length_extend, Scope.length_extend]
  omega

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {e : Scope.Entry} : Var Γ e → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
