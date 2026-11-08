module

public import Sic.Core.Universe
public import Sic.Grade
public import Sic.Mode

/-!
# Syntax

The syntax of annex 07 of RFC 36: the terms, their arguments, the telescopes, the contexts and the
entries of the signatures.
A variable is a de Bruijn index, as in the formalization of ADE: the number of entries between the
variable and its declaration, the last entry being `0`.
A variable `x : A` and a second-order variable `X : (Θ ⊢ A)` are both used applied to a term for
each entry of their telescope, `x[]` and `X[t̄]`.
A scope tells which of its entries are variables and which are second-order variables, and gives
each second-order variable its signature: for each entry of its telescope, the grade `p` with which
it uses its argument and the ownership signature of this argument, and the constant `c₀` of the
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
-/

@[expose] public section

namespace Sic.Core

/-- The name of an entry of the signature, or of a type that a declaration declares. -/
abbrev Name : Type := String

-- ADE: none.
/--
What the terms see of an entry of a telescope: the grade `p` with which the entry is used, and the
ownership signature of its argument, the requirement `r` on the ownership of the argument and, if
the result can be an alias of the argument, the coefficient `c` by which the ownership of the
argument counts in the ownership of the result.
-/
structure Parameter where
  /-- The grade `p` with which the entry is used. -/
  usage : Grade
  /-- The requirement `r` on the ownership of the argument. -/
  requirement : Grade
  /-- The coefficient `c` of the ownership of the argument in the ownership of the result, if any. -/
  coefficient : Option Grade

/-- An entry of a scope: a variable, or a second-order variable with the parameters of the entries of
its telescope and the constant `c₀` of the ownership of its result. -/
inductive Scope.Entry where
  /-- A variable `x : A`. -/
  | var
  /-- A second-order variable `X : (Θ ⊢ A)`, whose telescope has the parameters `ps`, and the result
  the constant `c₀` of its ownership, if any. -/
  | secondOrder (ps : List Parameter) (c₀ : Option Grade)

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

end

/-- The variable `x`, applied to no argument. -/
abbrev Term.var₀ {k : Nat} {Γ : Scope} (x : Var Γ .var) : Term k Γ := .var x .nil

-- ADE: none.
/--
`Θ = (x₁ :^{q₁}_{p₁} A₁, …, xₐ :^{qₐ}_{pₐ} Aₐ)`: a telescope in the scope `Γ`, whose entries have
the parameters `ps = (p₁, …, pₐ)`, each type in the scope of the entries before it; the entry
`x :^q_p A` is used with the grade of `p`, which also gives the ownership signature of its argument,
and its variable with the grade `q` by the types after it.
RFC: `\mathsf{syntax}_\Theta`
-/
inductive Telescope (k : Nat) : Scope → List Parameter → Type where
  /-- `ε`. -/
  | nil {Γ : Scope} : Telescope k Γ []
  /-- `(x :^q_p A, Θ)`. -/
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
  /-- `Γ, X : (Θ ⊢ A)`, a second-order variable, whose telescope has the parameters `ps`, and whose
  result has the constant `c₀` of its ownership, if any. -/
  | secondOrder {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps)
      (A : Term k (Γ.extend ps.length)) (c₀ : Option Grade) : Context k (.secondOrder ps c₀ :: Γ)

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
/-- `f.{s̄; l̄; p̄} :_m A ≔ t`, a constant definition, which defines the constant `f`. -/
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
  /-- The ownership `c₀` of its value, which the body provides. -/
  ownership : Grade
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []
  /-- The body `t`, for each instance. -/
  body : Instance sorts grades → Term levels []

-- ADE: none.
/-- `f.{s̄; l̄; p̄} :_m A`, a constant declaration, which declares the constant `f`, without
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
  /-- The ownership `c₀` of its value, which the declaration states. -/
  ownership : Grade
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []

-- ADE: none.
/--
The header of a type declaration, `𝒦.{s̄; l̄; p̄} Δ : κ where D₁ ≔ …; …; Dₙ ≔ …`, which is all that
the system knows of it: the names of the declared types, the parameters `Δ` and the sort `κ`; the
kind `𝒦` gives the bodies.
-/
structure TypeDeclaration where
  /-- The names `D₁, …, Dₙ` of the declared types. -/
  names : List Name
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
`f.{s̄; l̄; p̄} :_m A ∈ Σ`: the signature has a constant `f`, with `j` sort, `k` level and `g` grade
variables, the mode `m`, the ownership `c₀` and the type `A`, which the rules of the defined and of
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
`D.{s̄; l̄; p̄} Δ : κ ∈ Σ`: the signature has the declared type `D`, of the type declaration `decl`,
whose variables, parameters and sort are those of `D`, which the rules of the declared types share.
RFC: `\in_D`
-/
def Signature.HasDeclaredType (sig : Signature) (D : Name) (decl : TypeDeclaration) : Prop :=
  .typeDeclaration decl ∈ sig ∧ D ∈ decl.names

/-- The names of a signature are distinct: each entry introduces names that no entry before it
does.
RFC: `\mathsf{names}_\Sigma` -/
def Signature.Distinct : Signature → Prop
  | [] => True
  | e :: sig => Signature.Distinct sig ∧ ∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names

/-- In a signature whose names are distinct, a name is introduced by one entry at most.
RFC: `\mathsf{unique}_\Sigma` -/
theorem Signature.Distinct.entry_unique : {sig : Signature} → sig.Distinct → {e₁ e₂ : Entry} →
    {n : Name} → e₁ ∈ sig → e₂ ∈ sig → n ∈ e₁.names → n ∈ e₂.names → e₁ = e₂ := by
  intro sig
  induction sig with
  | nil => intro _ _ _ _ h₁; cases h₁
  | cons e sig ih =>
    intro hd e₁ e₂ n h₁ h₂ hn₁ hn₂
    obtain ⟨h, hfresh⟩ := hd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact absurd hn₂ (hfresh _ h₂' n hn₁)
    · exact absurd hn₁ (hfresh _ h₁' n hn₂)
    · exact ih h h₁' h₂' hn₁ hn₂

/-- The `n` elements of a list of length `n`, numbered. -/
def _root_.List.getFin {α : Type} (l : List α) {n : Nat} (h : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

/-- The instance that gives the sort variables the sorts `qs` and the grade variables the grades
`ps`. -/
def Instance.ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (hq : qs.length = j)
    (hp : ps.length = g) : Instance j g :=
  ⟨qs.getFin hq, ps.getFin hp⟩

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {e : Scope.Entry} : Var Γ e → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
