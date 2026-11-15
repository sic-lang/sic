module

public import Sic.Core.Syntax

/-!
# Nesting

The nesting of annex 14 of RFC 36: the positions at which the types of a block occur in the type of
a field, as a tree, which is no position when none of them occurs, the type of the block when the
type is an instance of it, and, when the type is an instance of another declared type, the nesting
of each of its arguments.
A field is recursive when its nesting is a type of the block, and nested when its nesting is that
of an instance: the nestings of the fields of a constructor hold the names of the types of the
block.

The nesting reads the syntax alone, once, on the declaration: a substitution keeps the instances
of a type, and so its nesting, while it may bring a type of the block where the declaration has a
parameter, which is no position of the block.
It reads the instances only, and neither the terms nor the parameters in which a declared type is
strictly positive: the formation of a declaration checks them.

The RFC names the variables, so that one `Λ` gives their nestings to the variables it names, no
position to the others, and their objects to the types of the block; with de Bruijn indices, the
nestings of the variables of a scope are a function of its variables, extended by no position under
each variable that an abstraction binds, and the objects of the types of the block a function of
the names.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α : Type}

/-! ## Nestings -/

-- ADE: none.
/-- `⊥`, `h` or `(λ̄)`: the nesting of a type, the positions at which it holds what `α` gives for
the types of a block.
RFC: `\mathsf{syntax}_\lambda` -/
inductive Nest (α : Type) where
  /-- `⊥`: no position. -/
  | plain : Nest α
  /-- `h`: a position, which holds `a`. -/
  | direct (a : α) : Nest α
  /-- `(λ̄)`: an instance of a declared type, with the nesting of each of its arguments, the last
  one first, as the arguments are. -/
  | inst (ns : List (Nest α)) : Nest α

/-- The nesting has no position. -/
def Nest.isPlain : Nest α → Bool
  | .plain => true
  | _ => false

-- ADE: none.
/-- `nest(λ̄)`: the nesting of an instance whose arguments have the nestings `λ̄`: no position when
none of them has one.
RFC: `\mathsf{nest}_{\bar\lambda}` -/
def Nest.ofArgs (ns : List (Nest α)) : Nest α :=
  if ns.all Nest.isPlain then .plain else .inst ns

mutual

-- ADE: none.
/-- `λ ↦ h`: the nesting `λ` whose positions hold what `f` gives for the objects that those of
`λ` hold.
RFC: `\mathsf{map}_\lambda` -/
def Nest.map {β : Type} (f : α → β) : Nest α → Nest β
  | .plain => .plain
  | .direct a => .direct (f a)
  | .inst ns => .inst (Nest.mapList f ns)

/-- The nestings `λ̄` of the arguments of an instance, each mapped by `f`. -/
def Nest.mapList {β : Type} (f : α → β) : List (Nest α) → List (Nest β)
  | [] => []
  | n :: ns => n.map f :: Nest.mapList f ns

end

/-- The nestings of the variables of the scope `Γ`. -/
abbrev Nesting (α : Type) (Γ : Scope) : Type := ∀ {e : Scope.Entry}, Var Γ e → Nest α

namespace Nesting

/-- The nestings of the variables of a scope none of which has a position. -/
def plain {Γ : Scope} : Nesting α Γ := fun _ => .plain

/-- The nestings `ν` under a new entry, which has no position. -/
def lift {Γ : Scope} {e : Scope.Entry} (ν : Nesting α Γ) : Nesting α (e :: Γ) := fun x =>
  match x with
  | .zero => .plain
  | .succ x => ν x

/-- The nestings `ν` under `n` new variables. -/
def liftN {Γ : Scope} : (n : Nat) → Nesting α Γ → Nesting α (Γ.extend n)
  | 0, ν => ν
  | n + 1, ν => liftN n (lift ν)

-- ADE: none.
/-- `Δ ↦ λ̄`: the nestings of the parameters of a declared type at an instance whose arguments have
the nestings `λ̄`, the last one first.
RFC: `\mathsf{nest}_\Delta` -/
def ofArgs : {Δ : Scope} → List (Nest α) → Nesting α Δ
  | _ :: _, n :: _, _, .zero => n
  | _ :: _, _ :: ns, _, .succ x => ofArgs ns x
  | _, _, _, _ => .plain

end Nesting

/-! ## Nesting of a Type -/

mutual

-- ADE: none.
/-- `nest_Λ(A)`: the nesting of the type `A`, where `mark` gives the types of the block what their
positions hold and `ν` the nestings of the variables: that of a variable applied to arguments is the nesting of the variable,
that of an instance of a type of the block is this type, and that of an instance of another
declared type is the nesting of its arguments.
RFC: `\mathsf{nest}_A` -/
def Term.nest {Γ : Scope} (mark : Name → Option α) (ν : Nesting α Γ) : Term k Γ → Nest α
  | .var x _ => ν x
  | .inst D _ _ _ as =>
    match mark D with
    | some a => .direct a
    | none => Nest.ofArgs (as.nest mark ν)
  | _ => .plain

-- ADE: none.
/-- `nest_Λ(ā)`: the nesting of each of the arguments `ā` of an instance, the last one first,
under the variables that its abstraction binds.
RFC: `\mathsf{nest}_{\bar a}` -/
def InstanceArgs.nest {Γ Δ : Scope} (mark : Name → Option α) (ν : Nesting α Γ) :
    InstanceArgs k Γ Δ → List (Nest α)
  | .nil => []
  | .snoc as B => B.nest mark (ν.liftN _) :: as.nest mark ν

end

/-! ## Nesting of the Fields of a Block -/

-- ADE: none.
/-- `nest_𝒟(A)`: the nesting of the type `A` of a field of a block whose types are named `names`,
whose positions hold the names of these types, and whose variables have no position.
RFC: `\mathsf{nest}_{\mathcal{D}}` -/
def Term.blockNest {Γ : Scope} (names : List Name) (A : Term k Γ) : Nest Name :=
  A.nest (fun D => if D ∈ names then some D else none) Nesting.plain

-- ADE: none.
/-- `nest_𝒟(Θ)`: the nesting of the type of each entry of a telescope, in order.
RFC: `\mathsf{nest}_\Theta` -/
def Telescope.nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → Telescope k Γ ps → List (Nest Name)
  | [], .nil => []
  | _ :: _, .cons _ _ A Θ => A.blockNest names :: Θ.nest names

/-- The nesting of the type of the entry at each position of the telescope `Θ`, the first one at
`0`, and no position after its entries. -/
def Telescope.nestAt {Γ : Scope} {ps : List Parameter} (names : List Name)
    (Θ : Telescope k Γ ps) : Nat → Nest Name :=
  fun i => ((Θ.nest names)[i]?).getD .plain

/-- The nesting of an instance is not a position. -/
theorem Nest.ofArgs_ne_direct (ns : List (Nest α)) (a : α) : Nest.ofArgs ns ≠ .direct a := by
  unfold Nest.ofArgs
  split <;> exact fun h => nomatch h

/-- The nesting of the type of a field is a position that holds a type of the block when the field
is recursive, of this type, and only then. -/
theorem Term.blockNest_eq_direct {Γ : Scope} {names : List Name} {D : Name} :
    (A : Term k Γ) → (A.blockNest names = .direct D ↔ A.blockName names = some D)
  | .inst D' _ _ _ as => by
    unfold Term.blockNest Term.blockName
    rw [Term.nest]
    by_cases hD : D' ∈ names
    · simp only [hD, ite_true, Nest.direct.injEq, Option.some.injEq]
    · simp only [hD, ite_false, reduceCtorEq, iff_false]
      exact Nest.ofArgs_ne_direct _ _
  | .var .. | .sort _ | .const .. | .ctor .. | .recursor .. | .obs .. | .corec .. =>
    ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- The nesting of the entry at a position of a telescope is a position that holds a type of the
block when the entry is a recursive field of this type, and only then. -/
theorem Telescope.nestAt_eq_direct {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (i : Nat) →
      (Θ.nestAt names i = .direct D ↔ Θ.recursionAt names i = some D)
  | [], .nil, _ => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | _ :: _, .cons _ _ A _, 0 => Term.blockNest_eq_direct A
  | _ :: _, .cons _ _ _ Θ, i + 1 => Telescope.nestAt_eq_direct Θ i

end Sic.Core
