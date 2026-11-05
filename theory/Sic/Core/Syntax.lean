module

public import Sic.Core.Universe
public import Sic.Grade
public import Sic.Mode

/-!
# Syntax

The terms of the core of RFC 24, its telescopes, its contexts and the entries of its signatures.
A variable is a de Bruijn index, as in the formalization of ADE: the number of entries between the
variable and its declaration, the last entry being `0`.
A variable `x : A` and a second-order variable `X : (Θ ⊢ A)` are both used applied to a term for
each entry of their telescope, `x[]` and `X[t̄]`.
A scope gives each of its entries the grades `p` of the entries of its telescope, none for a
variable, with which a second-order variable uses its arguments, so that the usage of `X[t̄]` reads
them in the scope, from the binder of `X`, as the usage of the other terms reads its grades from
their binders; a term only uses the variables of its scope, each applied to an argument for each of
these grades.
The context tells which entries are variables and which are second-order variables, so that the
rules `(var)` and `(var_X)` stay apart.

The sort and grade variables of an entry of the signature are not part of the syntax: since an entry
is checked for each instance of them, its type and its body are given for each instance, as a
function of the sorts and of the grades, so that the terms only carry sorts and grades.
The level variables are part of the syntax, since an entry is checked once with them: a term over
`k` level variables uses levels over `k` variables.

ADE have no second-order variables, and their levels are terms; their definition contexts hold
definitions only, transparent or opaque, without sort, level or grade variables.
-/

@[expose] public section

namespace Sic.Core

/-- The name of an entry of the signature, or of a type that a declaration declares. -/
abbrev Name : Type := String

/-- A scope, the grades `p` of the telescope of each entry of a context, the last entry first. -/
abbrev Scope : Type := List (List Grade)

/-- The scope `Γ` extended by `a` variables, the variables of a telescope, the first of them first. -/
def Scope.extend (Γ : Scope) : Nat → Scope
  | 0 => Γ
  | a + 1 => Scope.extend ([] :: Γ) a

-- ADE: `Fin`, the de Bruijn indices of `Definition/Untyped.agda`, without telescopes.
/-- A variable of the scope `Γ` whose telescope has the grades `ps`, by its de Bruijn index. -/
inductive Var : Scope → List Grade → Type where
  /-- The last entry of the scope. -/
  | zero {Γ : Scope} {ps : List Grade} : Var (ps :: Γ) ps
  /-- An entry before the last one. -/
  | succ {Γ : Scope} {ps qs : List Grade} (x : Var Γ ps) : Var (qs :: Γ) ps

mutual

-- ADE: `Term`, in `Definition/Untyped.agda`.
/--
A term over `k` level variables in the scope `Γ`.
The core names no type: the declared types come from the declarations of the signature.
-/
inductive Term (k : Nat) : Scope → Type where
  /-- `x[t̄]`: the variable `x` applied to arguments for the entries of its telescope, `x` alone
  when it is a variable. -/
  | var {Γ : Scope} {ps : List Grade} (x : Var Γ ps) (ts : Args k Γ ps) : Term k Γ
  /-- The sort `κ`, `U_l` or `Ω_l`. -/
  | sort {Γ : Scope} (κ : Universe k) : Term k Γ
  /-- `c.{s̄; l̄; p̄}`: the definition or constant `c` at an instance of its variables. -/
  | const {Γ : Scope} (c : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade) :
      Term k Γ
  /-- `D.{s̄; l̄; p̄} ā`: an instance of the declared type `D`. -/
  | inst {Γ : Scope} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k Γ Δ) : Term k Γ

/-- `t̄ = (t₁, …, tₐ)`: the arguments of a telescope whose entries have the grades `ps`, the first one
first. -/
inductive Args (k : Nat) : Scope → List Grade → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : Args k Γ []
  /-- `(t, t̄)`, the argument `t` of an entry of grade `p`. -/
  | cons {Γ : Scope} {p : Grade} {ps : List Grade} (t : Term k Γ) (ts : Args k Γ ps) :
      Args k Γ (p :: ps)

/--
`ā`: the arguments of an instance, one for each parameter of the scope `Δ`, the last one first: a
term for a variable, and an abstraction `x̄. B` for a second-order variable, a term over a new
variable for each entry of its telescope.
-/
inductive InstanceArgs (k : Nat) : Scope → Scope → Type where
  /-- `()`. -/
  | nil {Γ : Scope} : InstanceArgs k Γ []
  /-- `(ā, x̄. B)`, the argument `B` for a parameter whose telescope has the grades `ps`. -/
  | snoc {Γ Δ : Scope} {ps : List Grade} (as : InstanceArgs k Γ Δ)
      (B : Term k (Γ.extend ps.length)) : InstanceArgs k Γ (ps :: Δ)

end

/-- The variable `x`, applied to no argument. -/
abbrev Term.var₀ {k : Nat} {Γ : Scope} (x : Var Γ []) : Term k Γ := .var x .nil

-- ADE: none.
/--
`Θ = (x₁ :^{q₁}_{p₁} A₁, …, xₐ :^{qₐ}_{pₐ} Aₐ)`: a telescope in the scope `Γ`, whose entries have
the grades `ps = (p₁, …, pₐ)`, each
type in the scope of the entries before it; the entry `x :^q_p A` is used with the grade `p`, and its
variable with the grade `q` by the types after it.
-/
inductive Telescope (k : Nat) : Scope → List Grade → Type where
  /-- `ε`. -/
  | nil {Γ : Scope} : Telescope k Γ []
  /-- `(x :^q_p A, Θ)`. -/
  | cons {Γ : Scope} {ps : List Grade} (q p : Grade) (A : Term k Γ) (Θ : Telescope k ([] :: Γ) ps) :
      Telescope k Γ (p :: ps)

-- ADE: `Con`, in `Definition/Untyped.agda`.
/-- A context whose scope is `Γ`, the last entry first. -/
inductive Context (k : Nat) : Scope → Type where
  /-- `ε`. -/
  | empty : Context k []
  /-- `Γ, x : A`. -/
  | var {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ) : Context k ([] :: Γ)
  /-- `Γ, X : (Θ ⊢ A)`, a second-order variable whose telescope has the grades `ps`. -/
  | secondOrder {Γ : Scope} {ps : List Grade} (ctx : Context k Γ) (Θ : Telescope k Γ ps)
      (A : Term k (Γ.extend ps.length)) : Context k (ps :: Γ)

/-! ## Signatures

An entry of the signature has sort, level and grade variables, the sorts and the grades of an
instance being given to its type and its body. -/

/-- An instance of `j` sort variables and `g` grade variables. -/
structure Instance (j g : Nat) where
  /-- The sort of each sort variable. -/
  sorts : Fin j → Quality
  /-- The grade of each grade variable. -/
  grades : Fin g → Grade

-- ADE: none.
/-- `c.{s̄; l̄; p̄} :_m A ≔ t`, a definition. -/
structure Definition where
  /-- The name `c`. -/
  name : Name
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The mode `m` in which the body is checked. -/
  mode : Mode
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []
  /-- The body `t`, for each instance. -/
  body : Instance sorts grades → Term levels []

-- ADE: none.
/-- `c.{s̄; l̄; p̄} :_m A`, a constant, an entry without body. -/
structure Constant where
  /-- The name `c`. -/
  name : Name
  /-- The number of sort variables. -/
  sorts : Nat
  /-- The number of level variables. -/
  levels : Nat
  /-- The number of grade variables. -/
  grades : Nat
  /-- The mode `m` of its uses. -/
  mode : Mode
  /-- The type `A`, for each instance. -/
  type : Instance sorts grades → Term levels []

-- ADE: none.
/--
The header of a declaration, `kind.{s̄; l̄; p̄} Δ : κ where D₁ ≔ …; …; Dₙ ≔ …`, which is all that the
core knows of it: the names of the declared types, the parameters `Δ` and the sort `κ`; the kinds of
declarations give the bodies.
-/
structure Declaration where
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

/-- An entry of the signature. -/
inductive Entry where
  /-- A declaration `𝒟`. -/
  | declaration (decl : Declaration)
  /-- A definition. -/
  | definition (d : Definition)
  /-- A constant. -/
  | constant (c : Constant)

/-- The names that an entry introduces. -/
def Entry.names : Entry → List Name
  | .declaration decl => decl.names
  | .definition d => [d.name]
  | .constant c => [c.name]

-- ADE: `DCon`, in `Definition/Untyped/NotParametrised.agda`, which holds definitions only.
/-- A signature, its entries in order, the last entry first. -/
abbrev Signature : Type := List Entry

/--
`c.{s̄; l̄; p̄} :_m A ∈ Σ`: the signature has a definition or a constant named `c`, with `j` sort,
`k` level and `g` grade variables, the mode `m` and the type `A`, which the rules of the definitions
and of the constants share.
-/
inductive Signature.HasEntry (sig : Signature) :
    Name → (j k g : Nat) → Mode → (Instance j g → Term k []) → Prop where
  /-- A definition. -/
  | definition {d : Definition} (h : .definition d ∈ sig) :
      HasEntry sig d.name d.sorts d.levels d.grades d.mode d.type
  /-- A constant. -/
  | constant {c : Constant} (h : .constant c ∈ sig) :
      HasEntry sig c.name c.sorts c.levels c.grades c.mode c.type

/-- The names of a signature are distinct: each entry introduces names that no entry before it
does. -/
def Signature.Distinct : Signature → Prop
  | [] => True
  | e :: sig => Signature.Distinct sig ∧ ∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names

/-- In a signature whose names are distinct, a name is introduced by one entry at most. -/
theorem Signature.Distinct.entry_unique : {sig : Signature} → sig.Distinct → {e₁ e₂ : Entry} →
    {n : Name} → e₁ ∈ sig → e₂ ∈ sig → n ∈ e₁.names → n ∈ e₂.names → e₁ = e₂
  | _ :: _, ⟨h, hfresh⟩, _, _, n, h₁, h₂, hn₁, hn₂ => by
    cases h₁ with
    | head =>
      cases h₂ with
      | head => rfl
      | tail _ h₂ => exact absurd hn₂ (hfresh _ h₂ n hn₁)
    | tail _ h₁ =>
      cases h₂ with
      | head => exact absurd hn₁ (hfresh _ h₁ n hn₂)
      | tail _ h₂ => exact h.entry_unique h₁ h₂ hn₁ hn₂

/-- The `n` elements of a list of length `n`, numbered. -/
def _root_.List.getFin {α : Type} (l : List α) {n : Nat} (h : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

/-- The instance that gives the sort variables the sorts `qs` and the grade variables the grades
`ps`. -/
def Instance.ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (hq : qs.length = j)
    (hp : ps.length = g) : Instance j g :=
  ⟨qs.getFin hq, ps.getFin hp⟩

/-- The position of a variable in its scope, the last entry being `0`. -/
def Var.toFin {Γ : Scope} {ps : List Grade} : Var Γ ps → Fin Γ.length
  | .zero => ⟨0, Nat.zero_lt_succ _⟩
  | .succ x => x.toFin.succ

end Sic.Core
