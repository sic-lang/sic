module

public import Sic.Core.Universe
public import Sic.Grading.GradeVector
public import Sic.Grading.Mode
public import Sic.Math.List

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

open Sic.Grading

/-! ## Terms -/

/-- The name of an entry of the signature, or of a type that a declaration declares: a name that
a declaration gives, or the name of the lifting of a type at positions of its parameters, which
this type and these positions determine and which no declaration gives. -/
inductive Name : Type where
  /-- A name that a declaration gives. -/
  | base (s : String)
  /-- `D^Π`: the name of the lifting of the type `D` at the set `Π` of its parameters at the
  positions `S`, in order. -/
  | lifting (D : Name) (S : List Nat)
  deriving DecidableEq

/-- A string is the name that a declaration gives. -/
instance : Coe String Name := ⟨.base⟩

/--
What the terms see of an entry of a telescope: the grade `p` with which the entry is used, and the
requirement `r` on the ownership of its argument.
-/
structure Parameter where
  /-- The grade `p` with which the entry is used. -/
  usage : Grade
  /-- The requirement `r` on the ownership of the argument. -/
  requirement : Grade

/--
`ψ = χ₀ ∧ x_{j₁} · χ_{j₁} ∧ … ∧ x_{jₙ} · χ_{jₙ}`: the ownership of the result of a second-order
variable whose telescope has `n` entries, the meet of its constant `χ₀` and of a factor `xⱼ · χⱼ`
for some variables `xⱼ` of the telescope, the constant and each factor being optional.
A function from the variables of the telescope gives each one factor at most, in their order.
The constant and the coefficients are elements of `α`: grades in a term, and their multiplicities at
run time in the target language of the erasure.
RFC: `\mathsf{syntax}_\psi`
-/
structure ResultOwnership (α : Type) (n : Nat) where
  /-- The constant `χ₀`, if any. -/
  constant : Option α
  /-- The coefficient `χⱼ` of the variable `xⱼ`, if it has a factor. -/
  coefficient : Fin n → Option α

/-- The ownership `ψ` of a result whose constant and coefficients are mapped by `f`, such as the
multiplicities at run time of grades. -/
def ResultOwnership.map {α β : Type} {n : Nat} (f : α → β) (ψ : ResultOwnership α n) :
    ResultOwnership β n :=
  ⟨ψ.constant.map f, fun j => (ψ.coefficient j).map f⟩

/-- `ψ'`: the ownership `ψ` of the result of a second-order variable without the factor of the first
variable of its telescope, over the variables after it. -/
def ResultOwnership.tail {α : Type} {n : Nat} (ψ : ResultOwnership α (n + 1)) : ResultOwnership α n :=
  ⟨ψ.constant, fun i => ψ.coefficient i.succ⟩

/-- `ψ[ō / x̄]`: the value of the ownership `ψ` of the result of a second-order variable, given the
ownerships `os` of its arguments: the meet of its constant `ψ` and of the ownership `oⱼ` of each
argument scaled by the coefficient `χⱼ` of its variable, over the factors present, and none if no
factor is.
RFC: `\mathsf{value}_\psi` -/
def ResultOwnership.value {α : Type} [Mul α] [Min α] : {n : Nat} → ResultOwnership α n → List α →
    Option α
  | _ + 1, ψ, o :: os => Option.merge (· ⊓ ·) ((ψ.coefficient 0).map (o * ·)) (ψ.tail.value os)
  | _, ψ, _ => ψ.constant

/-- An entry of a scope: a variable, or a second-order variable with the parameters of the entries of
its telescope and the ownership of its result. -/
inductive Scope.Entry where
  /-- A variable `x : A`. -/
  | var
  /-- A second-order variable `X : (Θ ⊢ A ◀ ψ)`, whose telescope has the parameters `ps`, and the
  ownership `ψ` of its result. -/
  | secondOrder (ps : List Parameter) (ψ : ResultOwnership Grade ps.length)

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

/-- The position of a variable in its scope, the first entry being `0`, by which a type declares
the parameters in which it is strictly positive. -/
def Var.level : {Γ : Scope} → {e : Scope.Entry} → Var Γ e → Nat
  | _ :: Γ, _, .zero => Γ.length
  | _, _, .succ x => x.level

mutual

-- ADE: `Term`, in `Definition/Untyped.agda`.
/--
A term over `k` level variables in the scope `Γ`.
The core names no type but the sorts and the equality: the declared types come from the type
declarations of the signature.
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
  /-- `rec_{r; ς; χ} T t return C̄ : κ with ū`: the recursor, which uses the term `t` of the
  instance `T = D.{s̄; l̄; p̄} ā` with the grade `r`, with a motive `C_j` of the sort `κ` for each
  type of the block and a branch `u_ji` for each constructor of each type, in the order of the
  declaration; the recursor carries the instance of the term it eliminates, so that its usage and
  its ownership read the grades and the requirements of the fields at this instance, and the sort
  of its motives with the ownerships of the results of its nested fields, `ς` that their observation
  requires of them and `χ` of what it gives, so that its computation writes these results. -/
  | recursor {Γ : Scope} {Δ : Scope} (r ς χ : Grade) (D : Name) (qs : List Quality)
      (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ) (t : Term k Γ)
      (κ : Universe k) (Cs : Motives k Γ) (us : Branches k Γ) : Term k Γ
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
      (Ss : States k Γ) (vs : DestructorBranches k Γ) : Term k Γ
  /-- `t ∼.{s; l}_A u`: the equality of the terms `t` and `u` of the type `A`, whose sort has the
  quality `s` and the level `l`; the equality carries the type of its terms and the quality and the
  level of the sort of this type, so that the term determines its type and its sort. -/
  | equality {Γ : Scope} (s : Quality) (l : Level k) (A t u : Term k Γ) : Term k Γ
  /-- `refl.{s; l}_A(t)`: the proof of the equality `t ∼.{s; l}_A t` of the term `t` of the type `A`
  with itself; the proof carries the type of its term and the quality and the level of the sort of
  this type, so that the term determines its type. -/
  | refl {Γ : Scope} (s : Quality) (l : Level k) (A t : Term k Γ) : Term k Γ
  /-- `transp(A, t₁, t₂, x. C, t, u)`: the transport of the term `u` of `C[t₁ / x]` along the proof
  `t` of `t₁ ∼ t₂` at the type `A`, with the motive `x. C` over a new variable; the transport
  carries the type and the two terms of the equality, so that the term determines its type,
  `C[t₂ / x]`. -/
  | transp {Γ : Scope} (A t₁ t₂ : Term k Γ) (C : Term k (Γ.extend 1)) (t u : Term k Γ) : Term k Γ
  /-- `propext.{l}(A, B, x. t, y. u)`: the proof of the equality of the propositions `A` and `B` of
  `Ω_l` from the two implications, a proof `t` of `B` from a proof `x` of `A` and a proof `u` of `A`
  from a proof `y` of `B`; the proof carries the level and the two propositions, so that the term
  determines its type, and the two implications are terms over a new variable, the hypothesis. -/
  | propExt {Γ : Scope} (l : Level k) (A B : Term k Γ) (t u : Term k (Γ.extend 1)) : Term k Γ
  /-- `coind(T, t₁, t₂, (x₁, x₂). Ā, t, ḡ)`: the proof by coinduction of the equality of the terms
  `t₁` and `t₂` of the instance `T = D.{s̄; l̄; p̄} ā` of a codata type, with a relation `A_j` for
  each type of the block, a proposition over two new variables, the two terms it relates, the proof
  `t` that the relation of `T` relates `t₁` and `t₂`, and a branch `g_ji` for each destructor of
  each type, in the order of the declaration, over the two terms, the hypothesis that they are
  related and the arguments of the destructor; the proof carries its instance and its two terms, so
  that the term determines its type. -/
  | coind {Γ : Scope} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k Γ Δ) (t₁ t₂ : Term k Γ) (As : Terms k (Γ.extend 2))
      (t : Term k Γ) (gs : DestructorBranches k Γ) : Term k Γ

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

/-- `ḡ`: the branches of the destructors: one for each destructor of each type of a block, in the
order of the declaration; for a corecursor, the branch `D.d(x̄; ȳ; z̄) ⇒ g` is a term over a new
variable for each non-uniform parameter, for each entry of the state and for each argument of the
destructor; for a proof by coinduction, over no variable of the first group, a variable for each of
two terms of the type of the destructor and one for the hypothesis that the relation of this type
relates them, then a variable for each argument of the destructor; the indices only keep the numbers
`n`, `m` and `a` of variables of the three groups.
RFC: `\mathsf{syntax}_{\bar g}` -/
inductive DestructorBranches (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : DestructorBranches k Γ
  /-- `((x̄; ȳ; z̄). g, ḡ)`, with `n` non-uniform parameters, `m` entries of the state and
  `a` arguments. -/
  | cons {Γ : Scope} (n m a : Nat) (v : Term k (((Γ.extend n).extend m).extend a))
      (vs : DestructorBranches k Γ) :
      DestructorBranches k Γ

end

/-- The terms `t̄` of the arguments of a telescope, without the parameters of its entries, which the
fields of a constructor take from the declaration. -/
def Args.terms {k : Nat} {Γ : Scope} : {ps : List Parameter} → Args k Γ ps → Terms k Γ
  | [], .nil => .nil
  | _ :: _, .cons t ts => .cons t ts.terms

/-- The type of the block whose names are `names` that the type `A` of a field, or of the result of a
destructor, is an instance of, if any: the field or the destructor is then recursive.
RFC: `\mathsf{recursive}_A` -/
def Term.blockName {k : Nat} {Γ : Scope} (names : List Name) : Term k Γ → Option Name
  | .inst D _ _ _ _ => if D ∈ names then some D else none
  | _ => none

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

/-- The term at the position `j` of the terms `t̄`, the first one at `0`. -/
def Terms.get {k : Nat} {Γ : Scope} : Terms k Γ → Nat → Option (Term k Γ)
  | .nil, _ => none
  | .cons t _, 0 => some t
  | .cons _ ts, j + 1 => ts.get j

/-- The number of the terms `t̄`. -/
def Terms.length {k : Nat} {Γ : Scope} : Terms k Γ → Nat
  | .nil => 0
  | .cons _ ts => ts.length + 1

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

/-- The grades `ē` of the recursive results of the branch at the position `i` of the branches `ū`,
the first one at `0`, in order, and none when there is no branch at `i`. -/
def Branches.grades {k : Nat} {Γ : Scope} : Branches k Γ → Nat → List Grade
  | .nil, _ => []
  | .cons _ _ es _ _, 0 => es.toList
  | .cons _ _ _ _ us, i + 1 => us.grades i

/-- The number of the branches `ḡ` of the destructors. -/
def DestructorBranches.length {k : Nat} {Γ : Scope} : DestructorBranches k Γ → Nat
  | .nil => 0
  | .cons _ _ _ _ vs => vs.length + 1

/-- The branch at the position `i` of the branches `ḡ` of the destructors, the first one at `0`,
with its numbers of non-uniform parameters, of entries of the state and of arguments. -/
def DestructorBranches.get {k : Nat} {Γ : Scope} :
    DestructorBranches k Γ → Nat → Option (Σ n m a, Term k (((Γ.extend n).extend m).extend a))
  | .nil, _ => none
  | .cons n m a v _, 0 => some ⟨n, m, a, v⟩
  | .cons _ _ _ _ vs, i + 1 => vs.get i

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
      (A : Term k (Γ.extend ps.length)) (ψ : ResultOwnership Grade ps.length) :
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

/-- `D ▶ ζ ⊕ Π ≔ c₁ : Θ₁ | … | cₙ : Θₙ`, a data type of a declaration, the grades `ζ` with which it
uses the parameters `Δ`, those `Π` of the parameters in which it is strictly positive, and its
constructors, in order. -/
structure DataType (j g k : Nat) (Δ : Scope) where
  /-- The name `D`. -/
  name : Name
  /-- The grades `ζ` with which the type uses the parameters, for each instance. -/
  usage : Instance j g → GradeVector Δ.length
  /-- The parameters `Π` in which the type is strictly positive, by their positions in `Δ`, the
  first parameter at `0`. -/
  positive : Nat → Bool
  /-- The constructors `c₁ : Θ₁, …, cₙ : Θₙ`. -/
  constructors : List (Constructor j g k Δ)

/--
`d₁ : (Θ₁ ⊢ B₁ ◀ ψ₁) ▶ p₁; q₁ ◀ ς₁ | … | dₙ : (Θₙ ⊢ Bₙ ◀ ψₙ) ▶ pₙ; qₙ ◀ ςₙ`: the destructors of a
codata type, in the scope `Γ`, whose names are `ns`, in order.
The destructor `d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς` has the telescope `Θ` of its arguments and its result
type `B`, in the scope extended by them; its result has the ownership `ψ`, is used with the grade
`p`, the destructor is used with the grade `q` by the types of the destructors after it, in whose
scope it is a second-order variable `d : (Θ ⊢ B ◀ ψ)`, and requires the ownership `ς` of the value
that it observes.
-/
inductive Destructors (k : Nat) : Scope → List Name → Type where
  /-- No destructor. -/
  | nil {Γ : Scope} : Destructors k Γ []
  /-- `d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς`, followed by the destructors after it. -/
  | cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} (p q ς : Grade)
      (Θ : Telescope k Γ ps) (B : Term k (Γ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
      (ds : Destructors k (.secondOrder ps ψ :: Γ) ns) : Destructors k Γ (d :: ns)

/--
`d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)`: a position of the destructor `d` in the
destructors `d̄` of the scope `Γ`, as the rules of the observations decompose them, whose telescope
`Θ` and result `B` are in the scope `Ξ`, the scope `Γ` extended by the destructors `d̄₁` before it,
as second-order variables.
The position is a datum rather than a proposition, as a variable is, so that the substitution of the
destructors before it is defined on it.
-/
inductive Destructors.Pos {k : Nat} (d : Name) (p q ς : Grade) {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → (Ξ : Scope) → Telescope k Ξ ps →
      Term k (Ξ.extend ps.length) → ResultOwnership Grade ps.length → Type where
  /-- `d̄ = (d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)`: the first destructor. -/
  | here {Γ : Scope} {ns : List Name} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)}
      {ψ : ResultOwnership Grade ps.length} {ds : Destructors k (.secondOrder ps ψ :: Γ) ns} :
      Destructors.Pos d p q ς (.cons (d := d) p q ς Θ B ψ ds) Γ Θ B ψ
  /-- `d̄ = (d' : (Θ' ⊢ B' ◀ ψ') ▶ p'; q' ◀ ς' | d̄')`, where `d` is in `d̄'`. -/
  | there {Γ : Scope} {d' : Name} {ns : List Name} {ps' : List Parameter} {p' q' ς' : Grade}
      {Θ' : Telescope k Γ ps'} {B' : Term k (Γ.extend ps'.length)} {ψ' : ResultOwnership Grade ps'.length}
      {ds : Destructors k (.secondOrder ps' ψ' :: Γ) ns} {Ξ : Scope} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      (h : Destructors.Pos d p q ς ds Ξ Θ B ψ) :
      Destructors.Pos d p q ς (.cons (d := d') p' q' ς' Θ' B' ψ' ds) Ξ Θ B ψ

/-- The types of the block whose names are `names` that the results of the destructors are instances
of, in order: `some D` for a recursive destructor of the type `D`, `none` for the others.
RFC: `\mathsf{recursive}_{\bar d}` -/
def Destructors.recursion {k : Nat} (names : List Name) :
    {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → List (Option Name)
  | _, _, .nil => []
  | _, _, .cons _ _ _ _ B _ ds => B.blockName names :: ds.recursion names

/-- The type `D` of the block whose names are `names` of the recursive destructor at each position
of the destructors `d̄`, the first one at `0`, and none at the other positions. -/
def Destructors.recursionAt {k : Nat} {Γ : Scope} {ns : List Name} (names : List Name)
    (ds : Destructors k Γ ns) : Nat → Option Name :=
  fun i => ((ds.recursion names)[i]?).join

/-- `D ▶ ζ ⊕ Π ≔ d₁ : … | … | dₙ : …`, a codata type of a declaration, the grades `ζ` with which it
uses the parameters `Δ`, those `Π` of the parameters in which it is strictly positive, and its
destructors, in order. -/
structure CodataType (j g k : Nat) (Δ : Scope) where
  /-- The name `D`. -/
  name : Name
  /-- The grades `ζ` with which the type uses the parameters, for each instance. -/
  usage : Instance j g → GradeVector Δ.length
  /-- The parameters `Π` in which the type is strictly positive, by their positions in `Δ`, the
  first parameter at `0`. -/
  positive : Nat → Bool
  /-- The names `d₁, …, dₙ` of the destructors. -/
  destructors : List Name
  /-- The destructors `d₁ : …, …, dₙ : …`, for each instance, since their grades may be grade
  variables. -/
  body : Instance j g → Destructors k Δ destructors

/-- The types of a type declaration: a block of data types, or a block of codata types, so that a
block is homogeneous.
RFC: `\mathsf{syntax}_{\mathcal{D}}` -/
inductive TypeDeclaration.Body (j g k : Nat) (Δ : Scope) where
  /-- The data types `D₁ ≔ …; …; Dₙ ≔ …` of a block of data types. -/
  | data (types : List (DataType j g k Δ))
  /-- The codata types `D₁ ≔ …; …; Dₙ ≔ …` of a block of codata types. -/
  | codata (types : List (CodataType j g k Δ))

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

/-- The positions of the recursive fields of each constructor of the block, the first field at `0`,
at the instance `I`, in the order of the cases. -/
def TypeDeclaration.recursivePositions (decl : TypeDeclaration)
    (I : Instance decl.sorts decl.grades) : List (List Nat) :=
  decl.cases.map fun x =>
    ((x.2.2.fields I).recursion decl.names).zipIdx.filterMap fun y => y.1.map fun _ => y.2

/-- The requirement of the recursion on one axis, the uses at run time or all the uses: the meet of
`1` and of the coefficient `ϱ · π` of each recursive field of the requirement `ϱ` that the recursor
uses with the multiplicity `π`, on this axis, other than `0`, a field that it does not use being
eliminated by no recursion. -/
def Parameter.recursionAxis : List (Multiplicity × Multiplicity) → Multiplicity
  | [] => .one
  | (ϱ, π) :: xs =>
    if π = .zero then Parameter.recursionAxis xs else (ϱ * π) ⊓ Parameter.recursionAxis xs

/-- The requirement of the recursion on an axis is never `0`. -/
theorem Parameter.recursionAxis_ne_zero :
    (xs : List (Multiplicity × Multiplicity)) → Parameter.recursionAxis xs ≠ .zero
  | [] => by decide
  | (ϱ, π) :: xs => by
    have ih := Parameter.recursionAxis_ne_zero xs
    simp only [Parameter.recursionAxis]
    split
    · exact ih
    · exact (by decide : ∀ x y : Multiplicity, y ≠ .zero → x ⊓ y ≠ .zero) _ _ ih

/-- `r̂`: the requirement of the recursion of a recursor that uses its term with the grade `c`, on
a block whose constructors have, in order, the recursive fields at the positions `es` and the
parameters `fs` of their fields, and whose nested fields give on each axis `ax` the pairs
`nested ax`: the meet, on each axis, of `11ᵖ`, of the coefficient `r · (c · q)` of each recursive
field of the requirement `r` and of the grade `q` that the recursor uses on this axis, the
coefficient of the variable of the field, a field without parameter, in a term that no declaration
types, having the coefficient `ωωᵖ`, which states nothing, and of the product `ϱ · π` of each pair
`π ◀ ϱ` of a nested field whose multiplicity `π` is not `0`: each recursion of a recursor is a use
of a recursive field, whose ownership is the ownership of its value times this coefficient, or of
an observation of a nested field, whose ownership the pair bounds, so that the branches, which run
at each level of the recursion, see the term of the recursor at its ownership times `r̂`, which
every level has, since the grades are idempotent; the pairs of the nested fields are read from
their shapes on each axis, which the syntax does not give.
RFC: `\mathsf{recursion}_p` -/
def Parameter.recursion (c : Grade) (es : List (List Nat)) (fs : List (List Parameter))
    (nested : (Grade → Multiplicity) → List (Multiplicity × Multiplicity)) : Grade :=
  let xs : List (Grade × Grade) := (List.zipWith (fun e f => e.map fun l =>
    ((f[l]?).map fun p => (p.requirement, c * p.usage)).getD
      (.unrestrictedUnrestricted, .linearLinear)) es fs).flatten
  { run := Parameter.recursionAxis (xs.map (fun x => (x.1.run, x.2.run)) ++ nested Grade.run)
    total := Parameter.recursionAxis (xs.map (fun x => (x.1.total, x.2.total)) ++ nested Grade.total)
    run_zero := fun h => absurd h (Parameter.recursionAxis_ne_zero _) }

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

/--
`(data.{s̄; l̄; p̄ | C} Δ : κ where …; D ▶ ζ ≔ …; …) ∈ Σ`: the signature has the data type `T`, named
`D`, of the type declaration `decl`, which the rules of the constructors and of the recursors share.
-/
def Signature.HasDataType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (T : DataType decl.sorts decl.grades decl.levels decl.scope) : Prop :=
  .typeDeclaration decl ∈ sig ∧ T ∈ decl.dataTypes ∧ T.name = D

/--
`(codata.{s̄; l̄; p̄ | C} Δ : κ where …; D ▶ ζ ≔ …; …) ∈ Σ`: the signature has the codata type `T`, named
`D`, of the type declaration `decl`, which the meaning of its instances reads.
-/
def Signature.HasCodataType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (T : CodataType decl.sorts decl.grades decl.levels decl.scope) : Prop :=
  .typeDeclaration decl ∈ sig ∧ T ∈ decl.codataTypes ∧ T.name = D

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

/-- The instance that gives the sort variables the sorts `qs` and the grade variables the grades
`ps`. -/
def Instance.ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (hq : qs.length = j)
    (hp : ps.length = g) : Instance j g :=
  ⟨qs.getFin hq, ps.getFin hp⟩

/-- `s̄', p̄'` as many as `s̄, p̄`: the qualities `qs` and the grades `ps` are as many as `j` sort
variables and `g` grade variables, those of an entry of the signature or of a lifting. -/
structure Instance.AsMany (j g : Nat) (qs : List Quality) (ps : List Grade) : Prop where
  /-- As many qualities as sort variables. -/
  sorts : qs.length = j
  /-- As many grades as grade variables. -/
  grades : ps.length = g

/-- `[s̄' / s̄, p̄' / p̄]`: the instance that gives the sort variables the qualities `qs` and the
grade variables the grades `ps`, as many as them. -/
abbrev Instance.AsMany.inst {j g : Nat} {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany j g qs ps) : Instance j g :=
  .ofLists qs ps hqp.sorts hqp.grades

/-- The instance that the qualities `qs` give gives each sort variable the quality at its position in
`qs`. -/
theorem Instance.AsMany.sorts_inst {j g : Nat} {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany j g qs ps) (i : Fin j) :
    hqp.inst.sorts i = qs[(i : Nat)]'(by rw [hqp.sorts]; exact i.isLt) :=
  rfl

/-- The instance that the grades `ps` give gives each grade variable the grade at its position in
`ps`. -/
theorem Instance.AsMany.grades_inst {j g : Nat} {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany j g qs ps) (i : Fin g) :
    hqp.inst.grades i = ps[(i : Nat)]'(by rw [hqp.grades]; exact i.isLt) :=
  rfl

/-- The instance that the qualities and the grades of an instance give is this instance. -/
theorem Instance.AsMany.inst_ofFn {j g : Nat} (ι : Instance j g)
    (hqp : Instance.AsMany j g (List.ofFn ι.sorts) (List.ofFn ι.grades)) : hqp.inst = ι := by
  unfold Instance.AsMany.inst Instance.ofLists
  rw [List.getFin_ofFn, List.getFin_ofFn]

/-- The qualities of the sort variables at the instance that the qualities `qs` give are `qs`. -/
theorem Instance.AsMany.ofFn_inst_sorts {j g : Nat} {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany j g qs ps) : List.ofFn hqp.inst.sorts = qs :=
  List.ofFn_getFin qs hqp.sorts

/-- The grades of the grade variables at the instance that the grades `ps` give are `ps`. -/
theorem Instance.AsMany.ofFn_inst_grades {j g : Nat} {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany j g qs ps) : List.ofFn hqp.inst.grades = ps :=
  List.ofFn_getFin ps hqp.grades

/-- Whether the qualities `qs` and the grades `ps` are as many as `j` sort variables and `g` grade
variables, which the lookups of a declared type at an instance decide. -/
instance Instance.AsMany.decidable (j g : Nat) (qs : List Quality) (ps : List Grade) :
    Decidable (Instance.AsMany j g qs ps) :=
  if hq : qs.length = j then
    if hp : ps.length = g then .isTrue ⟨hq, hp⟩ else .isFalse fun hqp => hp hqp.grades
  else .isFalse fun hqp => hq hqp.sorts

/-- The value `f decl` that the type declaration `decl` of an entry gives, when the entry is a type
declaration that introduces the name `D`, and `none` otherwise: what the lookups of the declared
type `D` read of the entry that declares it. -/
def Entry.lookup {α : Type} (D : Name) (f : TypeDeclaration → Option α) : Entry → Option α
  | .typeDeclaration decl => if D ∈ decl.names then f decl else none
  | _ => none

/-- An entry that does not introduce the name `D` gives nothing to a lookup of `D`. -/
theorem Entry.lookup_of_not_mem {α : Type} {D : Name} {f : TypeDeclaration → Option α} :
    {e : Entry} → D ∉ e.names → Entry.lookup D f e = none
  | .typeDeclaration _, hD => by
    simp only [Entry.lookup]
    simp only [Entry.names] at hD
    simp only [hD, ↓reduceIte]
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- A type declaration that introduces the name `D` gives a lookup of `D` its value. -/
theorem Entry.lookup_typeDeclaration {α : Type} {D : Name} {f : TypeDeclaration → Option α}
    {decl : TypeDeclaration} (hD : D ∈ decl.names) :
    Entry.lookup D f (.typeDeclaration decl) = f decl := by
  simp only [Entry.lookup, hD, ↓reduceIte]

/-- A signature none of whose entries introduces the name `D` gives nothing to a lookup of `D`. -/
theorem Signature.findSome?_lookup_of_not_mem {α : Type} {D : Name}
    {f : TypeDeclaration → Option α} :
    {sig : Signature} → (∀ e ∈ sig, D ∉ e.names) → sig.findSome? (Entry.lookup D f) = none
  | [], _ => rfl
  | e :: sig, h => by
    rw [List.findSome?_cons_of_isNone
      (by rw [Entry.lookup_of_not_mem (h e List.mem_cons_self)]; rfl)]
    exact Signature.findSome?_lookup_of_not_mem fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- The entries of a suffix of a signature whose names are distinct have distinct names. -/
theorem Signature.Distinct.suffix {sig₂ : Signature} :
    (pre : Signature) → (pre ++ sig₂).Distinct → sig₂.Distinct
  | [], h => h
  | _ :: pre, h => Signature.Distinct.suffix pre h.1

/-- In a signature whose names are distinct, the first value that `f` gives an entry is the value
that it gives the entry that has the name `n`, when `f` gives none to the entries without it. -/
theorem Signature.Distinct.findSome?_eq {β : Type} {f : Entry → Option β} {n : Name} :
    {sig : Signature} → sig.Distinct → {e₀ : Entry} → e₀ ∈ sig → n ∈ e₀.names →
      (∀ e ∈ sig, (f e).isSome → n ∈ e.names) → sig.findSome? f = f e₀
  | [], _, _, h, _, _ => nomatch h
  | e :: sig, ⟨hd, _, hfresh, _⟩, e₀, he₀, hn₀, hf => by
    rcases List.mem_cons.1 he₀ with rfl | he₀'
    · cases hfe : f e₀ with
      | some b => exact List.findSome?_cons_of_isSome (by rw [hfe]; rfl) |>.trans hfe
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hfe]; rfl), List.findSome?_eq_none_iff]
        intro e' he'
        cases hfe' : f e' with
        | none => rfl
        | some _ =>
          exact absurd (hf e' (List.mem_cons_of_mem _ he') (by rw [hfe']; rfl))
            (hfresh e' he' n hn₀)
    · have hfe : f e = none := by
        cases hfe : f e with
        | none => rfl
        | some _ =>
          exact absurd hn₀ (hfresh e₀ he₀' n (hf e List.mem_cons_self (by rw [hfe]; rfl)))
      rw [List.findSome?_cons_of_isNone (by rw [hfe]; rfl)]
      exact hd.findSome?_eq he₀' hn₀ fun e' he' => hf e' (List.mem_cons_of_mem _ he')

/-- In a signature whose names are distinct, a lookup of a name that a type declaration of the
signature introduces gives the value that this declaration gives, the only entry that introduces
the name. -/
theorem Signature.Distinct.findSome?_lookup {α : Type} {D : Name}
    {f : TypeDeclaration → Option α} {decl : TypeDeclaration} {sig : Signature}
    (hd : sig.Distinct) (he : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names) :
    sig.findSome? (Entry.lookup D f) = f decl :=
  (hd.findSome?_eq he hD fun _ _ h => Decidable.byContradiction fun hn => by
    rw [Entry.lookup_of_not_mem hn] at h
    exact Bool.false_ne_true h).trans (Entry.lookup_typeDeclaration hD)

/-- The parameters, grade `p` and requirement `r`, of the fields of the constructor `c` of the
declared type `D` at the instance of the qualities `qs` and of the grades `ps`, when the entry
declares them. -/
def Entry.fieldParams (D c : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Parameter) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.dataTypes.find? (·.name == D)).bind fun T =>
        (T.constructors.find? (·.name == c)).map fun con => con.params hqp.inst
    else none

/-- The parameters, grade `p` and requirement `r`, of the fields of the constructor `c` of the
declared type `D` at the instance of the qualities `qs` and of the grades `ps`, in the last entry of
the signature that declares them, which the erasure of a constructor reads.
RFC: `\mathsf{parameters}_c` -/
def Signature.fieldParams (sig : Signature) (D c : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Parameter) :=
  sig.findSome? (Entry.fieldParams D c qs ps)

/-- The parameters of the arguments of the destructor `d`, the ownership of its result and the
ownership that it requires of the value that it observes, when the destructors have one. -/
def Destructors.arguments {k : Nat} : {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Name →
    Option (Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)
  | _, [], .nil, _ => none
  | _, d' :: _, .cons (ps := ps) _ _ ς _ _ ψ ds, d =>
    if d' = d then some ⟨ps, ψ, ς⟩ else ds.arguments d

/-- The parameters, grade `p` and requirement `r`, of the arguments of the destructor `d` of the
declared type `D` at the instance of the qualities `qs` and of the grades `ps`, the ownership `ψ` of
its result and the ownership `ς` that it requires of the value that it observes, when the entry
declares them. -/
def Entry.argumentParams (D d : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.codataTypes.find? (·.name == D)).bind fun T =>
        (T.body hqp.inst).arguments d
    else none

/-- The parameters, grade `p` and requirement `r`, of the arguments of the destructor `d` of the
declared type `D` at the instance of the qualities `qs` and of the grades `ps`, the ownership `ψ` of
its result and the ownership `ς` that it requires of the value that it observes, in the last entry
of the signature that declares them, which the erasure of an observation reads.
RFC: `\mathsf{parameters}_d` -/
def Signature.argumentParams (sig : Signature) (D d : Name) (qs : List Quality) (ps : List Grade) :
    Option (Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade) :=
  sig.findSome? (Entry.argumentParams D d qs ps)

/-- The grade `p` of the destructor `d`, when the destructors have one. -/
def Destructors.grade {k : Nat} : {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Name →
    Option Grade
  | _, [], .nil, _ => none
  | _, d' :: _, .cons p _ _ _ _ _ ds, d => if d' = d then some p else ds.grade d

/-- The type of the block whose names are `names` that the result of the destructor `d` is an
instance of, when the destructors have `d` and its result is one. -/
def Destructors.resultName {k : Nat} (names : List Name) : {Γ : Scope} → {ns : List Name} →
    Destructors k Γ ns → Name → Option Name
  | _, [], .nil, _ => none
  | _, d' :: _, .cons _ _ _ _ B _ ds, d => if d' = d then B.blockName names else ds.resultName names d

/-- The constant `χ₀` of the ownership of the result of the destructor `d`, when the destructors have
`d` and the ownership has one. -/
def Destructors.resultConstant {k : Nat} : {Γ : Scope} → {ns : List Name} →
    Destructors k Γ ns → Name → Option Grade
  | _, [], .nil, _ => none
  | _, d' :: _, .cons _ _ _ _ _ ψ ds, d => if d' = d then ψ.constant else ds.resultConstant d

/-- The grades `p` of the destructors of the cases of the block of the declared type `D`, in the
order of the declaration, at the instance of the qualities `qs` and of the grades `ps`, when the
entry declares them. -/
def Entry.destructorGrades (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Grade) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.codataTypes.find? (·.name == D)).bind fun _ =>
        decl.codataCases.mapM fun c => (c.2.1.body hqp.inst).grade c.2.2
    else none

/-- The grades `p` of the destructors of the cases of the block of the declared type `D`, in the
order of the declaration, at the instance of the qualities `qs` and of the grades `ps`, in the last
entry of the signature that declares them, which the erasure of a corecursor reads.
RFC: `\mathsf{grades}_{\bar g}` -/
def Signature.destructorGrades (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Grade) :=
  sig.findSome? (Entry.destructorGrades D qs ps)

/-- The position of the declared type `D` in the block of the entry, when the entry declares it. -/
def Entry.position (D : Name) : Entry → Option Nat :=
  Entry.lookup D fun decl =>
    decl.names.idxOf? D

/-- The position of the declared type `D` in its block, in the last entry of the signature that
declares it, which the erasure of a corecursor reads to find the state of `D`; the positions are
counted from `0`, as the indices of the lists, while the RFC counts them from `1`.
RFC: `\mathsf{position}_D` -/
def Signature.position (sig : Signature) (D : Name) : Option Nat :=
  sig.findSome? (Entry.position D)

/-- The case of the constructor `c` of the data type `D` in its block, when the entry declares
them. -/
def Entry.constructorCase (D c : Name) : Entry → Option Nat :=
  Entry.lookup D fun decl =>
    decl.cases.findIdx? fun x => x.2.1.name == D && x.2.2.name == c

/-- The case `i` of the constructor `c` of the data type `D` in its block, in the order of the
declaration, which is that of the branches of a recursor, in the last entry of the signature that
declares them, which the erasure of a constructor reads; the cases are counted from `0`, as the
indices of the lists, while the RFC counts them from `1`.
RFC: `\mathsf{case}_c` -/
def Signature.constructorCase (sig : Signature) (D c : Name) : Option Nat :=
  sig.findSome? (Entry.constructorCase D c)

/-- The case of the destructor `d` of the codata type `D` in its block, when the entry declares
them. -/
def Entry.destructorCase (D d : Name) : Entry → Option Nat :=
  Entry.lookup D fun decl =>
    decl.codataCases.findIdx? fun x => x.2.1.name == D && x.2.2 == d

/-- The case `i` of the destructor `d` of the codata type `D` in its block, in the order of the
declaration, which is that of the branches of a corecursor, in the last entry of the signature that
declares them, which the erasure of an observation reads; the cases are counted from `0`.
RFC: `\mathsf{case}_d` -/
def Signature.destructorCase (sig : Signature) (D d : Name) : Option Nat :=
  sig.findSome? (Entry.destructorCase D d)

/-- The position in the block of the type of the result of each destructor of the block of the codata
type `D`, at the instance of the qualities `qs` and of the grades `ps`, in the order of the
declaration, `none` for a destructor that is not recursive, when the entry declares them. -/
def Entry.resumedTypes (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List (Option Nat)) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.codataTypes.find? (·.name == D)).map fun _ =>
        decl.codataCases.map fun x =>
          ((x.2.1.body hqp.inst).resultName decl.names x.2.2).bind
            decl.names.idxOf?
    else none

/-- The position in the block of the type of the result of each destructor of the block of the
codata type `D`, at the instance of the qualities `qs` and of the grades `ps`, in the order of the
declaration, which is that of the branches of a corecursor, `none` for a destructor that is not
recursive, in the last entry of the signature that declares them, which the erasure of a
corecursor reads to find the state that a branch resumes.
RFC: `\mathsf{resumed}_d` -/
def Signature.resumedTypes (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade) :
    Option (List (Option Nat)) :=
  sig.findSome? (Entry.resumedTypes D qs ps)

/-- The parameters, grade and requirement, of the fields of each constructor of the block of the data
type `D`, at the instance of the qualities `qs` and of the grades `ps`, in the order of the
declaration, when the entry declares them. -/
def Entry.caseFieldParams (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List (List Parameter)) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.dataTypes.find? (·.name == D)).map fun _ =>
        decl.cases.map fun x => x.2.2.params hqp.inst
    else none

/-- The parameters, grade and requirement, of the fields of each constructor of the block of the data
type `D`, at the instance of the qualities `qs` and of the grades `ps`, in the order of the
declaration, which is that of the branches of a recursor, in the last entry of the signature that
declares them, which the erasure of a recursor reads to give the variables of the fields their
multiplicities and their coefficients of ownership.
RFC: `\mathsf{parameters}_{\bar u}` -/
def Signature.caseFieldParams (sig : Signature) (D : Name) (qs : List Quality) (ps : List Grade) :
    Option (List (List Parameter)) :=
  sig.findSome? (Entry.caseFieldParams D qs ps)

/-- The position in the block of the type of each destructor of the block of the codata type `D`,
the parameters of its arguments, the ownership of its result and the ownership that it requires of
the value that it observes, at the instance of the qualities `qs` and of the grades `ps`, in the
order of the declaration, when the entry declares them. -/
def Entry.destructorArguments (D : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List (Nat × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)) :=
  Entry.lookup D fun decl =>
    if hqp : Instance.AsMany decl.sorts decl.grades qs ps then
      (decl.codataTypes.find? (·.name == D)).map fun _ =>
        decl.codataCases.map fun x =>
          (x.1, ((x.2.1.body hqp.inst).arguments x.2.2).getD
            ⟨[], ⟨none, fun _ => none⟩, .unrestrictedUnrestricted⟩)
    else none

/-- The position in the block of the type of each destructor of the block of the codata type `D`,
whose state the branch of the destructor binds, the parameters of its arguments, the ownership of
its result and the ownership that it requires of the value that it observes, at the instance of the
qualities `qs` and of the grades `ps`, in the order of the declaration, which is that of the
branches of a corecursor, in the last entry of the signature that declares them, which the erasure
of a corecursor reads to give the variables of the branches their multiplicities and their
ownerships.
RFC: `\mathsf{arguments}_{\bar g}` -/
def Signature.destructorArguments (sig : Signature) (D : Name) (qs : List Quality)
    (ps : List Grade) :
    Option (List (Nat × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)) :=
  sig.findSome? (Entry.destructorArguments D qs ps)

/-- The position of a destructor in the destructors, as a number, the first one at `0`. -/
def Destructors.Pos.index {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → Destructors.Pos d p q ς ds Ξ Θ B ψ → Nat
  | _, _, _, _, _, _, _, .here => 0
  | _, _, _, _, _, _, _, .there h => h.index + 1

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {e : Scope.Entry} : Var Γ e → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
