module

public import Sic.Core.Syntax

/-!
# Factors of the Nestings

The factors of annex 20 of RFC 36: the factor of the result of a destructor of a lifting is the
grade that multiplies the uses of the scope by the recursive result that this destructor observes.
The result of a destructor of a lifting is a motive, at the observation of the term lifted, whose
recursive result runs the recursor once, of the factor `11ᵖ`, or an instance of another lifting,
whose recursive result is a corecursor: an observation of it runs one branch, at the grade of its
destructor, so that it uses the scope as the meet of the grades of its destructors times their
factors allows, as the usage of a corecursor bounds its uses by those of each branch.
A lifting without destructor is never observed, and uses nothing, of the factor `00ᵖ`.

The factor reads the syntax and the liftings that the signature declares, and no judgment, so that
the declaration of a lifting, its usage, its ownership and its erasure may read it.
It is a relation, as the lifting is: an instance of a lifting that the signature does not declare
has no factor.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The meet of a grade and of the meet of a list of grades, the latter absent when the list is
empty: the meet of the grades of a list of destructors, of which there may be none. -/
def _root_.Sic.Grading.Grade.meetWith (p : Grade) : Option Grade → Grade
  | none => p
  | some q => p ⊓ q

mutual

-- ADE: none.
/-- `Σ ⊢ factor(B) = π`: the result `B` of a destructor of a lifting has the factor `π`: a motive
at its arguments has the factor `11ᵖ`, and an instance of a lifting that the signature declares the
meet of the grades of its destructors times the factors of their results, or `00ᵖ` without
destructor. -/
inductive Term.Factor (sig : Signature) : {k : Nat} → {Γ : Scope} → Term k Γ → Grade → Prop where
  /-- A motive, at its arguments.
  RFC: `\mathsf{factor}_X` -/
  | var {k : Nat} {Γ : Scope} {e : Scope.Entry} (x : Var Γ e) (ts : Args k Γ e.params) :
      Term.Factor sig (.var x ts) .linearLinear
  /-- An instance of a lifting that the signature declares, whose destructors at this instance have
  the meet `π`, if any.
  RFC: `\mathsf{factor}_D` -/
  | inst {k : Nat} {Γ Δ : Scope} {decl : TypeDeclaration}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {D : Name} {S : List Nat}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
      {π : Option Grade} (h : sig.HasCodataType (.lifting D S) decl T)
      (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
      (hds : Destructors.Factor sig (T.body (.ofLists qs ps hq hp)) π) :
      Term.Factor sig (.inst (.lifting D S) qs ls ps as) (π.getD .noneNone)

-- ADE: none.
/-- `Σ ⊢ factor(d̄) = π`: the destructors `d̄` have the meet `π` of their grades times the factors
of their results, absent when there is no destructor. -/
inductive Destructors.Factor (sig : Signature) :
    {k : Nat} → {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Option Grade → Prop where
  /-- No destructor.
  RFC: `\mathsf{factor}_{\bar d\varepsilon}` -/
  | nil {k : Nat} {Γ : Scope} : Destructors.Factor sig (.nil : Destructors k Γ []) none
  /-- A destructor, of the grade `p`, whose result has the factor `π`, followed by destructors of the
  meet `π'`.
  RFC: `\mathsf{factor}_{\bar d,}` -/
  | cons {k : Nat} {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q ς : Grade}
      {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Γ) ns} {π : Grade} {π' : Option Grade}
      (hB : Term.Factor sig B π) (hds : Destructors.Factor sig ds π') :
      Destructors.Factor sig (.cons (d := d) p q ς Θ B ψ ds) (some ((p * π).meetWith π'))

end

end Sic.Core
