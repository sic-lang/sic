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
it uses its argument and the ownership signature of this argument, and the constant `χ₀` of the
ownership of its result; the usage and the ownership of `X[t̄]` read them in the scope, from the
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
ownership signature of its argument, the requirement `r` on the ownership of the argument and, if
the result can be an alias of the argument, the coefficient `χ` by which the ownership of the
argument counts in the ownership of the result.
-/
structure Parameter where
  /-- The grade `p` with which the entry is used. -/
  usage : Grade
  /-- The requirement `r` on the ownership of the argument. -/
  requirement : Grade
  /-- The coefficient `χ` of the ownership of the argument in the ownership of the result, if any.
  RFC: `\mathsf{syntax}_\psi` -/
  coefficient : Option Grade

/-- An entry of a scope: a variable, or a second-order variable with the parameters of the entries of
its telescope and the constant `χ₀` of the ownership of its result. -/
inductive Scope.Entry where
  /-- A variable `x : A`. -/
  | var
  /-- A second-order variable `X : (Θ ⊢ A ◀ ψ)`, whose telescope has the parameters `ps`, and the
  ownership `ψ` of whose result the constant `χ₀`, if any.
  RFC: `\mathsf{syntax}_\psi` -/
  | secondOrder (ps : List Parameter) (χ₀ : Option Grade)

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
  /-- `rec_r t return C̄ with ū`: the recursor, which uses the term `t` with the grade `r`, with a
  motive `C_j` for each type of the block and a branch `u_ji` for each constructor of each type, in
  the order of the declaration. -/
  | recursor {Γ : Scope} (r : Grade) (t : Term k Γ) (Cs : Motives k Γ) (us : Branches k Γ) :
      Term k Γ

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
order of the declaration; the branch `c(x̄; ȳ) ⇒ u` is a term over a new variable for each field and
one for each recursive result, of which the indices only keep the numbers `n` of fields and `m` of
recursive results.
RFC: `\mathsf{syntax}_{\bar u}` -/
inductive Branches (k : Nat) : Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Branches k Γ
  /-- `(c(x̄; ȳ) ⇒ u, ū)`, with `n` fields and `m` recursive results. -/
  | cons {Γ : Scope} (n m : Nat) (u : Term k (Γ.extend (n + m))) (us : Branches k Γ) :
      Branches k Γ

end

/-- The variable `x`, applied to no argument. -/
abbrev Term.var₀ {k : Nat} {Γ : Scope} (x : Var Γ .var) : Term k Γ := .var x .nil

-- ADE: none.
/--
`Θ = (x₁ : A₁ ▶ p₁; q₁ ◀ r₁, …, xₐ : Aₐ ▶ pₐ; qₐ ◀ rₐ)`: a telescope in the scope `Γ`, whose
entries have the parameters `ps`, each type in the scope of the entries before it; the entry
`x : A ▶ p; q ◀ r` is used with the grade `p`, requires the ownership `r` of its argument, and its
variable is used with the grade `q` by the types after it; its parameter also holds the coefficient
`χ` of `x` in the ownership `ψ` of the result of the second-order variable whose telescope it is.
RFC: `\mathsf{syntax}_\Theta`
-/
inductive Telescope (k : Nat) : Scope → List Parameter → Type where
  /-- `ε`. -/
  | nil {Γ : Scope} : Telescope k Γ []
  /-- `(x : A ▶ p; q ◀ r, Θ)`. -/
  | cons {Γ : Scope} {ps : List Parameter} (q : Grade) (p : Parameter) (A : Term k Γ)
      (Θ : Telescope k (.var :: Γ) ps) : Telescope k Γ (p :: ps)

-- ADE: `Con`, in `Definition/Untyped.agda`.
/-- A context whose scope is `Γ`, the last entry first.
RFC: `\mathsf{syntax}_\Gamma` -/
inductive Context (k : Nat) : Scope → Type where
  /-- `ε`. -/
  | empty : Context k []
  /-- `Γ, x : A`. -/
  | var {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ) : Context k (.var :: Γ)
  /-- `Γ, X : (Θ ⊢ A ◀ ψ)`, a second-order variable, whose telescope has the parameters `ps`, and the
  ownership `ψ` of whose result has the constant `χ₀`, if any, and the coefficients of `ps`. -/
  | secondOrder {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps)
      (A : Term k (Γ.extend ps.length)) (χ₀ : Option Grade) : Context k (.secondOrder ps χ₀ :: Γ)

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
A type declaration, `data.{s̄; l̄; p̄} Δ : κ where D₁ ≔ …; …; Dₙ ≔ …`, a block of data types declared
together, with their parameters `Δ` and their sort `κ`.
-/
structure TypeDeclaration where
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The scope of the parameters. -/
  scope : Scope
  /-- The parameters `Δ`, for each instance. -/
  params : Instance sorts grades → Context levels scope
  /-- The sort `κ` of the declared types, for each instance. -/
  sort : Instance sorts grades → Universe levels
  /-- The data types `D₁ ≔ …; …; Dₙ ≔ …` of the block. -/
  types : List (DataType sorts grades levels scope)

/-- The names `D₁, …, Dₙ` of the declared types. -/
def TypeDeclaration.names (decl : TypeDeclaration) : List Name :=
  decl.types.map (·.name)

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
RFC: `\mathsf{syntax}_\Sigma`, `\in_\Sigma.e`, `\in_\Sigma.e,e` -/
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
`D.{s̄; l̄; p̄} Δ : κ ▶ ζ ∈ Σ`: the signature has the declared type `D`, the data type `T` of the type
declaration `decl`, whose variables, parameters and sort are those of `D`, and whose grades `ζ` are
those of `T`, which the rules of the declared types share.
RFC: `\in_D`
-/
def Signature.HasDeclaredType (sig : Signature) (D : Name) (decl : TypeDeclaration)
    (T : DataType decl.sorts decl.grades decl.levels decl.scope) : Prop :=
  .typeDeclaration decl ∈ sig ∧ T ∈ decl.types ∧ T.name = D

/-- The names of a signature are distinct: each entry introduces distinct names, which no entry
before it does.
RFC: `\mathsf{names}_\Sigma` -/
def Signature.Distinct : Signature → Prop
  | [] => True
  | e :: sig => Signature.Distinct sig ∧ e.names.Nodup ∧ ∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names

/-- In a signature whose names are distinct, a name is introduced by one entry at most.
RFC: `\mathsf{unique}_\Sigma` -/
theorem Signature.Distinct.entry_unique : {sig : Signature} → sig.Distinct → {e₁ e₂ : Entry} →
    {n : Name} → e₁ ∈ sig → e₂ ∈ sig → n ∈ e₁.names → n ∈ e₂.names → e₁ = e₂ := by
  intro sig
  induction sig with
  | nil => intro _ _ _ _ h₁; cases h₁
  | cons e sig ih =>
    intro hd e₁ e₂ n h₁ h₂ hn₁ hn₂
    obtain ⟨h, -, hfresh⟩ := hd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact absurd hn₂ (hfresh _ h₂' n hn₁)
    · exact absurd hn₁ (hfresh _ h₁' n hn₂)
    · exact ih h h₁' h₂' hn₁ hn₂

/-- The `n` elements of a list of length `n`, numbered. -/
def _root_.List.getFin {α : Type} (l : List α) {n : Nat} (h : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

/-- The elements of a list mapped by `f` are the elements of the list mapped by `f`. -/
theorem _root_.List.getFin_map {α β : Type} (f : α → β) (l : List α) {n : Nat}
    (h : (l.map f).length = n) :
    (l.map f).getFin h = fun i => f (l.getFin ((List.length_map f).symm.trans h) i) := by
  funext i
  simp [List.getFin]

/-- The instance that gives the sort variables the sorts `qs` and the grade variables the grades
`ps`. -/
def Instance.ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (hq : qs.length = j)
    (hp : ps.length = g) : Instance j g :=
  ⟨qs.getFin hq, ps.getFin hp⟩

-- ADE: none.
/-- The grades `p` of the fields of the constructor `c` of the declared type `D` at the instance of
the qualities `qs` and of the grades `ps`, when the signature declares them, which the erasure of a
constructor reads.
RFC: `\mathsf{grades}_c` -/
def Signature.fieldGrades (sig : Signature) (D c : Name) (qs : List Quality) (ps : List Grade) :
    Option (List Grade) :=
  sig.findSome? fun
    | .typeDeclaration decl =>
      if hq : qs.length = decl.sorts then
        if hp : ps.length = decl.grades then
          (decl.types.find? (·.name == D)).bind fun T =>
            (T.constructors.find? (·.name == c)).map fun con =>
              (con.params (.ofLists qs ps hq hp)).map (·.usage)
        else none
      else none
    | _ => none

/-- The length of the scope `Γ` extended by `a` variables. -/
theorem Scope.length_extend (Γ : Scope) : (a : Nat) → (Γ.extend a).length = Γ.length + a
  | 0 => rfl
  | a + 1 => (Scope.length_extend (.var :: Γ) a).trans (Nat.succ_add _ _)

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {e : Scope.Entry} : Var Γ e → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
