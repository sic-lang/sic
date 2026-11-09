module

public import Sic.Core.Syntax

/-!
# Ownership

The judgment of ownership `Σ; φ ⊢ t ◀ p; m` of annex 12 of RFC 36: checked in the mode `m`, the
value of the term `t` has the ownership `p`, given the ownership `φ` of each variable of its scope
whose telescope is empty.

Ownership is defined on the term and the signature alone, without a context, as usage is: the scope
gives each second-order variable its telescope and the ownership of its result, and the signature
gives each constant its ownership.
Unlike the vector of the usage, which each premise computes and the conclusion adds, `φ` is the same
in every premise, as the context of the typing is.
The data types give the ownership of their instances and of their constructors.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- `ψ'`: the ownership `ψ` of the result of a second-order variable without the factor of the first
variable of its telescope, over the variables after it. -/
def ResultOwnership.tail {n : Nat} (ψ : ResultOwnership (n + 1)) : ResultOwnership n :=
  ⟨ψ.constant, fun i => ψ.coefficient i.succ⟩

-- ADE: none.
/-- `ψ[ō / x̄]`: the value of the ownership `ψ` of the result of a second-order variable, given the
ownerships `os` of its arguments: the meet of its constant `ψ` and of the ownership `oⱼ` of each
argument scaled by the coefficient `χⱼ` of its variable, over the factors present, and none if no
factor is.
RFC: `\mathsf{value}_\psi` -/
def ResultOwnership.value : {n : Nat} → ResultOwnership n → List Grade → Option Grade
  | _ + 1, ψ, o :: os => Option.merge (· ⊓ ·) ((ψ.coefficient 0).map (o * ·)) (ψ.tail.value os)
  | _, ψ, _ => ψ.constant

mutual

-- ADE: none.
/-- `Σ; φ ⊢ t ◀ p; m`: checked in the mode `m`, the value of the term `t` has the ownership `p`,
given the ownership `φ` of each variable of its scope whose telescope is empty. -/
inductive Ownership (sig : Signature) : {k : Nat} → {Γ : Scope} → (Var Γ .var → Grade) → Mode →
    Grade → Term k Γ → Prop where
  /-- A variable whose telescope is empty has the ownership that `φ` gives it.
  RFC: `\mathsf{var}_{◀}` -/
  | var {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {x : Var Γ .var} :
      Ownership sig φ m (φ x) (.var₀ x : Term k Γ)
  /-- The application `X[t̄]` of a second-order variable has the value of the ownership of its
  result, when it is defined, given the ownerships `os` of its arguments.
  RFC: `\mathsf{var}_{X◀}` -/
  | secondOrder {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {ps : List Parameter}
      {ψ : ResultOwnership ps.length} {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps} {os : List Grade}
      {p : Grade} (hts : OwnershipArgs sig φ m ts os) (hp : ψ.value os = some p) :
      Ownership sig φ m p (.var X ts)
  /-- A constant, defined or declared, has the ownership `p` of its entry, in every mode.
  RFC: `f_{◀}` -/
  | const {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m₁ m₂ : Mode} {f : Name} {j k' g : Nat}
      {p : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (h : sig.HasConstant f j k' g m₂ p A) :
      Ownership sig φ m₁ p (.const f qs ls ps : Term k Γ)
  /-- A sort has the least ownership, `ωωᵖ`, which states nothing.
  RFC: `\kappa_{◀}` -/
  | sort {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {κ : Universe k} :
      Ownership sig φ m .unrestrictedUnrestricted (.sort κ : Term k Γ)
  /-- An instance of a declared type, a type, has the least ownership, `ωωᵖ`, which states nothing.
  RFC: `D_{◀}` -/
  | inst {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {D : Name} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {Δ : Scope} {as : InstanceArgs k Γ Δ} :
      Ownership sig φ m .unrestrictedUnrestricted (.inst D qs ls ps as)
  /-- A constructor builds a new value, which has the ownership `11ᵖ`, whatever its fields; the
  arguments of its fields satisfy the requirements of their entries, as the arguments of a telescope
  do.
  RFC: `c_{◀}` -/
  | ctor {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {os : List Grade}
      (h : sig.HasDeclaredType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))} (hts : OwnershipArgs sig φ m ts os) :
      Ownership sig φ m .linearLinear (.ctor D qs ls ps as con.name ts.terms)
  /-- A term may be given an ownership lower than its own, which states less.
  RFC: `\mathsf{sub}_{◀}` -/
  | sub {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p q : Grade} {t : Term k Γ}
      (h : Ownership sig φ m p t) (hle : q ≤ p) : Ownership sig φ m q t

-- ADE: none.
/-- `Σ; φ ⊢ t̄ ◀ ō; Θ; m`: checked in the mode `m`, the arguments `t̄` of a telescope whose entries
have the parameters `ps` have the ownerships `os`, each satisfying the requirement of its entry. -/
inductive OwnershipArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    (Var Γ .var → Grade) → Mode → Args k Γ ps → List Grade → Prop where
  /-- No argument has no ownership.
  RFC: `\mathsf{tel}_{\varepsilon◀}` -/
  | nil {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} :
      OwnershipArgs sig φ m (.nil : Args k Γ []) []
  /-- The first argument, of the parameter `p`, checked in the mode `m ⊙ p.usage`, with an ownership
  `o` that satisfies the requirement of `p` unless this mode is `00ᵐ`, and the others.
  RFC: `\mathsf{tel}_{,◀}` -/
  | cons {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p : Parameter}
      {ps : List Parameter} {t : Term k Γ} {ts : Args k Γ ps} {o : Grade} {os : List Grade}
      (ht : Ownership sig φ (m ⊙ p.usage) o t)
      (hr : m ⊙ p.usage ≠ .zeroZero → p.requirement ≤ o) (hts : OwnershipArgs sig φ m ts os) :
      OwnershipArgs sig φ m (.cons t ts : Args k Γ (p :: ps)) (o :: os)

end

end Sic.Core
