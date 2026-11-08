module

public import Sic.Core.Syntax

/-!
# Ownership

The judgment of ownership `Σ; φ ⊢ t ◀ p; m`, which RFC 36 states beside the typing and the usage:
checked in the mode `m`, the value of the term `t` has the ownership `p`, a grade that counts the
paths to this value, at run time and in total, given the ownership `φ` of each variable of its scope.
The usage counts the uses of each variable in the future, and the ownership counts the paths to a
value, from its past as from its future.

A variable stands for a value, whose ownership `φ` gives; a second-order variable stands for a body,
evaluated at each of its applications, so that `φ` gives it none, and the ownership of the result of
an application is the one that its signature gives, from the ownerships of the arguments; a
constant has the ownership of its entry; a sort is no value at run time nor in a proof, and has the
least ownership, which states nothing.
Unlike the vector of the usage, which each premise computes and the conclusion adds, `φ` is the same
in every premise, as the context of the typing.
An argument is checked in the mode `m ⊙ p` of its grade `p`, as for the usage, and its ownership
must satisfy the requirement of its parameter unless this mode is `00ᵐ`, in which an occurrence is
no path.

The core gives the ownership of its variables, of its constants and of its sorts, and the rule
`(sub)`; the kinds of declarations will give the ownership of their terms, and couple it with their
usage at their binders.
The rules are formalized before RFC 36 states them, so that they name no formula yet.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- `c₀ ∧ ⋀ⱼ oⱼ · cⱼ`: the ownership of the result of a second-order variable whose telescope has
the parameters `ps` and whose result has the constant `c₀`, applied to arguments of the ownerships
`os`: the meet of `c₀` and of the ownership `oⱼ` of each argument scaled by the coefficient `cⱼ` of
its parameter, over the terms present, and none if no term is. -/
def Parameter.result (c₀ : Option Grade) : List Parameter → List Grade → Option Grade
  | p :: ps, o :: os =>
    Option.merge (· ⊓ ·) (p.coefficient.map (o * ·)) (Parameter.result c₀ ps os)
  | _, _ => c₀

mutual

-- ADE: none.
/-- `Σ; φ ⊢ t ◀ p; m`: checked in the mode `m`, the value of the term `t` has the ownership `p`, given
the ownership `φ` of each variable of its scope. -/
inductive Ownership (sig : Signature) : {k : Nat} → {Γ : Scope} → (Var Γ .var → Grade) → Mode →
    Grade → Term k Γ → Prop where
  /-- A variable has the ownership of its value. -/
  | var {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {x : Var Γ .var} :
      Ownership sig φ m (φ x) (.var₀ x : Term k Γ)
  /-- The application `X[t̄]` of a second-order variable has the ownership that the signature of
  `X` gives from the ownerships `os` of its arguments, when it gives one. -/
  | secondOrder {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {ps : List Parameter}
      {c₀ : Option Grade} {X : Var Γ (.secondOrder ps c₀)} {ts : Args k Γ ps} {os : List Grade}
      {p : Grade} (hts : OwnershipArgs sig φ m ts os) (hp : Parameter.result c₀ ps os = some p) :
      Ownership sig φ m p (.var X ts)
  /-- A constant, defined or declared, has the ownership `c₀` of its entry. -/
  | const {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m₁ m₂ : Mode} {f : Name} {j k' g : Nat}
      {c₀ : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (h : sig.HasConstant f j k' g m₂ c₀ A) :
      Ownership sig φ m₁ c₀ (.const f qs ls ps : Term k Γ)
  /-- A sort has the least ownership, `ωωᵖ`. -/
  | sort {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {κ : Universe k} :
      Ownership sig φ m .unrestrictedUnrestricted (.sort κ : Term k Γ)
  /-- A term may be given an ownership lower than its own, which states less on its paths. -/
  | sub {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p q : Grade} {t : Term k Γ}
      (h : Ownership sig φ m p t) (hle : q ≤ p) : Ownership sig φ m q t

-- ADE: none.
/-- `Σ; φ ⊢ t̄ ◀ ō; Θ; m`: checked in the mode `m`, the arguments `t̄` of a telescope whose entries
have the parameters `ps` have the ownerships `os`, each satisfying the requirement of its
parameter. -/
inductive OwnershipArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    (Var Γ .var → Grade) → Mode → Args k Γ ps → List Grade → Prop where
  /-- No argument has no ownership. -/
  | nil {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} :
      OwnershipArgs sig φ m (.nil : Args k Γ []) []
  /-- The first argument, of the parameter `p`, checked in the mode `m ⊙ p.usage`, with an ownership
  `o` that satisfies the requirement of `p` unless this mode is `00ᵐ`, and the others. -/
  | cons {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p : Parameter}
      {ps : List Parameter} {t : Term k Γ} {ts : Args k Γ ps} {o : Grade} {os : List Grade}
      (ht : Ownership sig φ (m ⊙ p.usage) o t)
      (hr : m ⊙ p.usage ≠ .zeroZero → p.requirement ≤ o) (hts : OwnershipArgs sig φ m ts os) :
      OwnershipArgs sig φ m (.cons t ts : Args k Γ (p :: ps)) (o :: os)

end

end Sic.Core
