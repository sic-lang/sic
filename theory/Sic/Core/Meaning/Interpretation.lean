module

public import Sic.Core.Reduction

/-!
# Interpretation of the Constants

The interpretation of the constants and the levels without variables of annex 18 of RFC 36, on
which the meaning computes its closed terms.
The meaning computes each constant to its interpretation `ι(c)`: it computes in the signature whose
constants become definitions with these bodies, so that it has a single reduction, that of the
conversion.
The levels of a closed term need not be numerals, since an instance of a definition may give `l ⊔ 0`
to its body, so that the meaning instantiates the level variables by numerals and relates the sorts
and the instances by the values of their levels.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Interpretation of the Constants -/

-- ADE: none.
/-- `ι`: an interpretation, which gives each constant a body, for each instance of its sort and grade
variables. -/
abbrev Interpretation : Type :=
  (c : ConstantDeclaration) → Instance c.sorts c.grades → Term c.levels []

/-- The entry `e` in which a constant becomes the definition whose body is its interpretation. -/
def Entry.interpret (ι : Interpretation) : Entry → Entry
  | .constantDeclaration c =>
    .constantDefinition ⟨c.name, c.sorts, c.levels, c.grades, c.mode, c.ownership, c.type, ι c⟩
  | e => e

/-- The signature `Σ` in which each constant becomes the definition whose body is its
interpretation.
RFC: `\mathsf{interpret}_\Sigma` -/
def Signature.interpret (ι : Interpretation) (sig : Signature) : Signature :=
  sig.map (Entry.interpret ι)

/-- `t ⇓ v` in the meaning: the closed term `t` computes to the canonical term `v`, each constant
computing to its interpretation. -/
def Computesι (sig : Signature) (ι : Interpretation) (t v : Term 0 []) : Prop :=
  Computes (sig.interpret ι) t v

/-! ## Levels Without Variables -/

/-- The level without variables whose value is `n`, written as this number.
RFC: `\mathsf{numeral}_l` -/
def Level.ofNat {k : Nat} : Nat → Level k
  | 0 => .zero
  | n + 1 => .succ (Level.ofNat n)

/-- The value of a level without variables. -/
def Level.closedValue (l : Level 0) : Nat := l.value Fin.elim0

/-- `t[ρ]`: the term `t` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Term.atLevels {k : Nat} {Γ : Scope} (ρ : Fin k → Nat) (t : Term k Γ) : Term 0 Γ :=
  t.substLevels fun i => .ofNat (ρ i)

/-- `Γ[ρ]`: the context `Γ` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Context.atLevels {k : Nat} {Γ : Scope} (ρ : Fin k → Nat) (ctx : Context k Γ) : Context 0 Γ :=
  ctx.substLevels fun i => .ofNat (ρ i)

/-- `t̄[ρ]`: the arguments `t̄` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Args.atLevels {k : Nat} {Γ : Scope} {ps : List Parameter} (ρ : Fin k → Nat) (ts : Args k Γ ps) :
    Args 0 Γ ps :=
  ts.substLevels fun i => .ofNat (ρ i)

/-- `ā[ρ]`: the arguments `ā` of an instance in which each level variable `i` has the value
`ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def InstanceArgs.atLevels {k : Nat} {Γ Δ : Scope} (ρ : Fin k → Nat) (as : InstanceArgs k Γ Δ) :
    InstanceArgs 0 Γ Δ :=
  as.substLevels fun i => .ofNat (ρ i)

/-- `κ[ρ]`: the sort `κ` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Universe.atLevels {k : Nat} (ρ : Fin k → Nat) (κ : Universe k) : Universe 0 :=
  κ.substLevels fun i => .ofNat (ρ i)

/-- `Θ[ρ]`: the telescope `Θ` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Telescope.atLevels {k : Nat} {Γ : Scope} {ps : List Parameter} (ρ : Fin k → Nat)
    (Θ : Telescope k Γ ps) : Telescope 0 Γ ps :=
  Θ.substLevels fun i => .ofNat (ρ i)

/-- `d̄[ρ]`: the destructors `d̄` in which each level variable `i` has the value `ρ i`.
RFC: `\mathsf{inst}_\rho` -/
def Destructors.atLevels {k : Nat} {Γ : Scope} {ns : List Name} (ρ : Fin k → Nat)
    (ds : Destructors k Γ ns) : Destructors 0 Γ ns :=
  ds.substLevels fun i => .ofNat (ρ i)

end Sic.Core
