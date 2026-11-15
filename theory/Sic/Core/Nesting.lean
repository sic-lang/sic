module

public import Sic.Core.Syntax

/-!
# Nesting

The nesting of annex 14 of RFC 36: the positions at which the types of a block occur in the type of
a field, as a tree, which is no position when none of them occurs, the type of the block when the
type is an instance of it, and, when the type is an instance of another declared type, the nesting
of each of its arguments.
A field is recursive when its nesting is a type of the block, and nested when its nesting is that
of an instance.

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

/-- The nesting of a field that is recursive, a position that holds `a`, or is not, no position. -/
def Nest.ofOption : Option α → Nest α
  | none => .plain
  | some a => .direct a

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

end Sic.Core
