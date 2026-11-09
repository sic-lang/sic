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

/-- The terms `t̄` of the arguments of a telescope, without the parameters of its entries, which the
fields of a constructor take from the declaration. -/
def Args.terms {k : Nat} {Γ : Scope} : {ps : List Parameter} → Args k Γ ps → Terms k Γ
  | [], .nil => .nil
  | _ :: _, .cons t ts => .cons t ts.terms

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
  | .cons _ _ _ us => us.length + 1

/-- The branch at the position `i` of the branches `ū`, the first one at `0`, with its numbers of
fields and of recursive results. -/
def Branches.get {k : Nat} {Γ : Scope} :
    Branches k Γ → Nat → Option (Σ n m, Term k (Γ.extend (n + m)))
  | .nil, _ => none
  | .cons n m u _, 0 => some ⟨n, m, u⟩
  | .cons _ _ _ us, i + 1 => us.get i

/-- The branch at a position of branches is one term. -/
theorem Branches.get_inj {k : Nat} {Γ : Scope} {us : Branches k Γ} {i n m : Nat}
    {u₁ u₂ : Term k (Γ.extend (n + m))} (h₁ : us.get i = some ⟨n, m, u₁⟩)
    (h₂ : us.get i = some ⟨n, m, u₂⟩) : u₁ = u₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- The variable `x`, applied to no argument. -/
abbrev Term.var₀ {k : Nat} {Γ : Scope} (x : Var Γ .var) : Term k Γ := .var x .nil

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

/-- The constructors of the data types `Ts`, the first type at the position `j`, each with the
position of its type and its type, in the order of the declaration. -/
def TypeDeclaration.casesFrom {j g k : Nat} {Δ : Scope} :
    Nat → List (DataType j g k Δ) → List (Nat × DataType j g k Δ × Constructor j g k Δ)
  | _, [] => []
  | i, T :: Ts => T.constructors.map (fun c => (i, T, c)) ++ TypeDeclaration.casesFrom (i + 1) Ts

/-- The cases of a recursor on a block: the constructors of its types, each with the position of
its type and its type, in the order of the declaration, which is that of the branches. -/
def TypeDeclaration.cases (decl : TypeDeclaration) :
    List (Nat × DataType decl.sorts decl.grades decl.levels decl.scope ×
      Constructor decl.sorts decl.grades decl.levels decl.scope) :=
  TypeDeclaration.casesFrom 0 decl.types

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

/-- The constructors of each type that an entry declares have distinct names. -/
def Entry.ConstructorsDistinct : Entry → Prop
  | .typeDeclaration decl => ∀ T ∈ decl.types, (T.constructors.map (·.name)).Nodup
  | _ => True

/-- The names of a signature are distinct: each entry introduces distinct names, which no entry
before it does, and the constructors of each type it declares have distinct names.
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
theorem Signature.Distinct.hasDeclaredType_unique {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl₁ decl₂ : TypeDeclaration} {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : DataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDeclaredType D decl₁ T₁) (h₂ : sig.HasDeclaredType D decl₂ T₂) :
    decl₁ = decl₂ ∧ HEq T₁ T₂ := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D)
    (by simp only [Entry.names, TypeDeclaration.names]; exact hn₁ ▸ List.mem_map_of_mem hT₁)
    (by simp only [Entry.names, TypeDeclaration.names]; exact hn₂ ▸ List.mem_map_of_mem hT₂)
  injection he with he
  subst he
  have hnodup := hd.nodup hm₁
  simp only [Entry.names, TypeDeclaration.names] at hnodup
  exact ⟨rfl, heq_of_eq (List.eq_of_nodup_map hnodup hT₁ hT₂ (hn₁.trans hn₂.symm))⟩

/-- In a signature whose names are distinct, the constructors of a declared type have distinct
names. -/
theorem Signature.Distinct.constructors_nodup : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDeclaredType D decl T → (T.constructors.map (·.name)).Nodup
  | [], _, _, _, _, h => nomatch h.1
  | _ :: _, ⟨hd, _, _, hc⟩, _, _, _, ⟨he, hT, hn⟩ => by
    rcases List.mem_cons.1 he with he | he
    · subst he; exact hc _ hT
    · exact hd.constructors_nodup ⟨he, hT, hn⟩

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

/-- A case of the types `Ts` is a constructor of one of them. -/
theorem TypeDeclaration.mem_casesFrom {j g k : Nat} {Δ : Scope} :
    {i : Nat} → {Ts : List (DataType j g k Δ)} → {x : Nat × DataType j g k Δ × Constructor j g k Δ} →
      x ∈ TypeDeclaration.casesFrom i Ts → x.2.1 ∈ Ts ∧ x.2.2 ∈ x.2.1.constructors
  | _, [], _, h => nomatch h
  | _, _ :: _, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact ⟨List.mem_cons_self, hc⟩
    · obtain ⟨h₁, h₂⟩ := TypeDeclaration.mem_casesFrom h
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩

/-- A case of the types `Ts`, the first one at the position `i`, holds the position of its type. -/
theorem TypeDeclaration.getElem?_of_mem_casesFrom {j g k : Nat} {Δ : Scope} :
    {i : Nat} → {Ts : List (DataType j g k Δ)} → {j' : Nat} → {T : DataType j g k Δ} →
      {c : Constructor j g k Δ} → (j', T, c) ∈ TypeDeclaration.casesFrom i Ts →
        i ≤ j' ∧ Ts[j' - i]? = some T
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

/-- A constructor of the type at the position `j'` of the types `Ts` is a case of them. -/
theorem TypeDeclaration.mem_casesFrom_of {j g k : Nat} {Δ : Scope} :
    {i : Nat} → {Ts : List (DataType j g k Δ)} → {j' : Nat} → {T : DataType j g k Δ} →
      {c : Constructor j g k Δ} → Ts[j']? = some T → c ∈ T.constructors →
        (i + j', T, c) ∈ TypeDeclaration.casesFrom i Ts
  | _, [], _, _, _, h, _ => nomatch h
  | i, _ :: Ts, 0, _, _, h, hc => by
    cases h
    exact List.mem_append_left _ (List.mem_map_of_mem hc)
  | i, _ :: Ts, j' + 1, _, _, h, hc => by
    have he : i + (j' + 1) = (i + 1) + j' := by omega
    rw [he]
    exact List.mem_append_right _ (TypeDeclaration.mem_casesFrom_of h hc)

/-- The cases of types with distinct names, whose constructors have distinct names, have distinct
names of types and of constructors. -/
theorem TypeDeclaration.casesFrom_nodup {j g k : Nat} {Δ : Scope} :
    {i : Nat} → {Ts : List (DataType j g k Δ)} → (Ts.map (·.name)).Nodup →
      (∀ T ∈ Ts, (T.constructors.map (·.name)).Nodup) →
        ((TypeDeclaration.casesFrom i Ts).map fun x => (x.2.1.name, x.2.2.name)).Nodup
  | _, [], _, _ => List.nodup_nil
  | i, T :: Ts, hn, hc => by
    rw [List.map_cons, List.nodup_cons] at hn
    have he : (TypeDeclaration.casesFrom i (T :: Ts)).map (fun x => (x.2.1.name, x.2.2.name)) =
        (T.constructors.map (·.name)).map (Prod.mk T.name) ++
          (TypeDeclaration.casesFrom (i + 1) Ts).map (fun x => (x.2.1.name, x.2.2.name)) := by
      simp only [TypeDeclaration.casesFrom, List.map_append, List.map_map]
      rfl
    rw [he]
    refine List.nodup_append.2 ⟨(hc T List.mem_cons_self).map (Prod.mk T.name)
      (fun _ _ hab he => hab (Prod.mk.inj he).2),
      TypeDeclaration.casesFrom_nodup hn.2 fun T hT => hc T (List.mem_cons_of_mem _ hT), ?_⟩
    intro a ha b hb hab
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    have hn' : T.name = x.2.1.name := congrArg Prod.fst hab
    exact hn.1 (hn' ▸ List.mem_map_of_mem (TypeDeclaration.mem_casesFrom hx).1)

/-- In a signature whose names are distinct, the cases of a type declaration have distinct names of
types and of constructors. -/
theorem Signature.Distinct.cases_nodup {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (h : .typeDeclaration decl ∈ sig) :
    (decl.cases.map fun x => (x.2.1.name, x.2.2.name)).Nodup :=
  TypeDeclaration.casesFrom_nodup (hd.nodup h) fun _ hT => hd.constructors_nodup ⟨h, hT, rfl⟩

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
the qualities `qs` and of the grades `ps`, when the entry declares them. -/
def Entry.fieldGrades (D c : Name) (qs : List Quality) (ps : List Grade) :
    Entry → Option (List Grade)
  | .typeDeclaration decl =>
    if hq : qs.length = decl.sorts then
      if hp : ps.length = decl.grades then
        (decl.types.find? (·.name == D)).bind fun T =>
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
    (hn : (decl.types.map (·.name)).Nodup)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.types)
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
    have hnone : decl.types.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ List.mem_map_of_mem hT)
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
    sig.HasDeclaredType D decl T → {con : Constructor decl.sorts decl.grades decl.levels decl.scope} →
    con ∈ T.constructors → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.fieldGrades D con.name qs ps = some ((con.params (.ofLists qs ps hq hp)).map (·.usage))
  | [], _, _, _, _, h, _, _, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, con, hcon, qs, ps, hq, hp => by
    unfold Signature.fieldGrades
    rcases List.mem_cons.1 he with rfl | he'
    · have hg := Entry.fieldGrades_of_mem hn hT (hc T hT) hcon hq hp
      rw [hD] at hg
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ List.mem_map_of_mem hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.fieldGrades_of_not_mem hDe]; rfl)]
      exact hd.fieldGrades ⟨he', hT, hD⟩ hcon hq hp

/-- The length of the scope `Γ` extended by `a` variables. -/
theorem Scope.length_extend (Γ : Scope) : (a : Nat) → (Γ.extend a).length = Γ.length + a
  | 0 => rfl
  | a + 1 => (Scope.length_extend (.var :: Γ) a).trans (Nat.succ_add _ _)

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {e : Scope.Entry} : Var Γ e → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
