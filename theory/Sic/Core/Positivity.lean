module

public import Sic.Core.Substitution

/-!
# Strict Positivity

The strict positivity of annex 15 of RFC 36: a type is strictly positive in a variable when the
variable occurs in it only as the type itself, or as an argument of an instance of a declared type
at a parameter in which this type is declared strictly positive, and never in a term.
Each type of a type declaration declares the parameters in which it is strictly positive, which the
formation of the declaration checks on its fields or on its destructors, as it checks the grades
with which the type uses its parameters.

The judgment reads the syntax alone: the positions that the types of the block declare, and those
that the codata types of the signature without recursive destructor declare, and no typing, so that
the meaning of the instances may use it.
A type declared before is read only if it is such a codata type, the types through which the
meaning of a nested field goes, and so are the types below which its own destructors nest a
parameter, since the strict positivity of their declaration read the same types.

The RFC names the variables, and says that a variable does not occur in a term; with de Bruijn
indices, a term in which a variable does not occur is a term of the scope without this variable,
renamed by the renaming that skips it.

ADE have no declared types, and no strict positivity.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Variables That Do Not Occur -/

/-- The scope `Γ` without its variable `x`. -/
def Scope.remove : (Γ : Scope) → {e : Scope.Entry} → Var Γ e → Scope
  | _ :: Γ, _, .zero => Γ
  | e' :: Γ, _, .succ x => e' :: Scope.remove Γ x

/-- The renaming of the scope without the variable `x` that skips `x`, and so reaches every
variable but `x`. -/
def Var.skip : {Γ : Scope} → {e : Scope.Entry} → (x : Var Γ e) → Ren Γ (Scope.remove Γ x)
  | _ :: _, _, .zero => Ren.weaken
  | _ :: _, _, .succ x => Ren.lift (Var.skip x)

/-- `x ∉ t`: the variable `x` does not occur in the term `t`, which is a term of the scope without
`x`. -/
def Term.Avoids {Γ : Scope} {e : Scope.Entry} (t : Term k Γ) (x : Var Γ e) : Prop :=
  ∃ t' : Term k (Scope.remove Γ x), t = t'.rename x.skip

/-- `x ∉ t̄`: the variable `x` does not occur in the arguments `t̄`. -/
def Args.Avoids {Γ : Scope} {e : Scope.Entry} {ps : List Parameter} (ts : Args k Γ ps)
    (x : Var Γ e) : Prop :=
  ∃ ts' : Args k (Scope.remove Γ x) ps, ts = ts'.rename x.skip

/-- `x ∉ Θ`: the variable `x` does not occur in the telescope `Θ`. -/
def Telescope.Avoids {Γ : Scope} {e : Scope.Entry} {ps : List Parameter} (Θ : Telescope k Γ ps)
    (x : Var Γ e) : Prop :=
  ∃ Θ' : Telescope k (Scope.remove Γ x) ps, Θ = Θ'.rename x.skip

/-! ## Strictly Positive Types -/

mutual

/--
`Σ ⊢ A ⊕ X`: the type `A` is strictly positive in the variable `X`, where `marks` gives the
parameters in which each declared type of the signature is strictly positive, by their positions.
-/
inductive Term.Positive (marks : Name → Nat → Prop) :
    {Γ : Scope} → {e : Scope.Entry} → Var Γ e → Term k Γ → Prop where
  /-- A type in which the variable does not occur.
  RFC: `\oplus_{\notin}` -/
  | absent {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {A : Term k Γ} (h : A.Avoids x) :
      Term.Positive marks x A
  /-- The variable itself, applied to arguments in which it does not occur.
  RFC: `\oplus_X` -/
  | var {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {ts : Args k Γ e.params} (h : ts.Avoids x) :
      Term.Positive marks x (.var x ts)
  /-- An instance of a declared type, whose arguments are strictly positive in the variable.
  RFC: `\oplus_D` -/
  | inst {Γ Δ : Scope} {e : Scope.Entry} {x : Var Γ e} {D : Name} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
      (h : InstanceArgs.Positive marks D x as) : Term.Positive marks x (.inst D qs ls ps as)

/--
`Σ ⊢_D ā ⊕ X`: the arguments `ā` of an instance of the declared type `D` are strictly positive in
the variable `X`: the argument of a parameter in which `D` is strictly positive is strictly positive
in `X`, and `X` does not occur in the others.
-/
inductive InstanceArgs.Positive (marks : Name → Nat → Prop) :
    Name → {Γ Δ : Scope} → {e : Scope.Entry} → Var Γ e → InstanceArgs k Γ Δ → Prop where
  /-- No argument.
  RFC: `\oplus_{\bar a\varepsilon}` -/
  | nil {D : Name} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} :
      InstanceArgs.Positive marks D x .nil
  /-- The argument of a parameter in which `D` is strictly positive.
  RFC: `\oplus_{\bar a,}` -/
  | positive {D : Name} {Γ Δ : Scope} {e e' : Scope.Entry} {x : Var Γ e}
      {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend e'.params.length)} (hm : marks D Δ.length)
      (has : InstanceArgs.Positive marks D x as)
      (hB : Term.Positive marks (x.weakenN e'.params.length) B) :
      InstanceArgs.Positive marks D x (.snoc as B)
  /-- The argument of any parameter, in which the variable does not occur.
  RFC: `\oplus_{\bar a\notin}` -/
  | absent {D : Name} {Γ Δ : Scope} {e e' : Scope.Entry} {x : Var Γ e}
      {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend e'.params.length)}
      (has : InstanceArgs.Positive marks D x as) (hB : B.Avoids (x.weakenN e'.params.length)) :
      InstanceArgs.Positive marks D x (.snoc as B)

end

/-- `Σ ⊢ Θ ⊕ X`: the fields `Θ` of a constructor are strictly positive in the variable `X`, as the
type of each of them is. -/
inductive Telescope.Positive (marks : Name → Nat → Prop) :
    {Γ : Scope} → {e : Scope.Entry} → Var Γ e → {ps : List Parameter} → Telescope k Γ ps → Prop where
  /-- No field.
  RFC: `\oplus_\varepsilon` -/
  | nil {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} : Telescope.Positive marks x .nil
  /-- A field, followed by the fields after it.
  RFC: `\oplus_{\Theta,}` -/
  | cons {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {ps : List Parameter} {q : Grade}
      {p : Parameter} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps}
      (hA : Term.Positive marks x A) (hΘ : Telescope.Positive marks (.succ x) Θ) :
      Telescope.Positive marks x (.cons q p A Θ)

/-- `Σ; 𝒟 ⊢ d̄ ⊕ X`: the destructors `d̄` of a codata type are strictly positive in the variable `X`,
which does not occur in the arguments of any of them, and in which the result of each of them is
strictly positive; the formation of the destructors checks that no destructor depends on a
destructor in whose result such a variable occurs. -/
inductive Destructors.Positive (marks : Name → Nat → Prop) :
    {Γ : Scope} → {e : Scope.Entry} → Var Γ e → {ns : List Name} → Destructors k Γ ns → Prop where
  /-- No destructor.
  RFC: `\oplus_{\bar d\varepsilon}` -/
  | nil {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} : Destructors.Positive marks x .nil
  /-- A destructor whose result is strictly positive in the variable, followed by the destructors
  after it.
  RFC: `\oplus_{\bar d|}` -/
  | cons {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Γ ps}
      {B : Term k (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Γ) ns} (hΘ : Θ.Avoids x)
      (hB : Term.Positive marks (x.weakenN ps.length) B)
      (hds : Destructors.Positive marks (.succ x) ds) :
      Destructors.Positive marks x (.cons (d := d) p q ς Θ B ψ ds)

/-- Destructors strictly positive in a variable, whose first destructor is `d`: its arguments avoid
the variable, its result is strictly positive in it, and so are the destructors after it. -/
theorem Destructors.Positive.cons_inv {marks : Name → Nat → Prop} {Γ : Scope} {e : Scope.Entry}
    {x : Var Γ e} {d : Name} {ns : List Name} {ps : List Parameter} {p q ς : Grade}
    {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
    {ds : Destructors k (.secondOrder ps ψ :: Γ) ns}
    (h : Destructors.Positive marks x (.cons (d := d) p q ς Θ B ψ ds)) :
    Θ.Avoids x ∧ Term.Positive marks (x.weakenN ps.length) B ∧
      Destructors.Positive marks (.succ x) ds := by
  cases h with
  | cons hΘ hB hds => exact ⟨hΘ, hB, hds⟩

/-! ## Declared Positions -/

/-- The type `D` of the type declaration declares that it is strictly positive in its parameter at
the position `i`. -/
def TypeDeclaration.Positive (decl : TypeDeclaration) (D : Name) (i : Nat) : Prop :=
  (∃ T ∈ decl.dataTypes, T.name = D ∧ T.positive i) ∨
    ∃ T ∈ decl.codataTypes, T.name = D ∧ T.positive i

/-- `D ⊕ X ∈ Σ; 𝒟`: the strict positivity of the block `𝒟` in the signature `Σ` reads that the type
`D` is strictly positive in its parameter at the position `i`: a type of the block declares it,
for its recursive fields and destructors, or a codata type of the signature does, none of whose
destructors is recursive, at any instance, below which the types of a block may be nested.
RFC: `\in_{\oplus\mathcal{D}}` -/
def Signature.PositiveIn (sig : Signature) (decl : TypeDeclaration) (D : Name) (i : Nat) : Prop :=
  decl.Positive D i ∨
    ∃ (decl' : TypeDeclaration) (T : CodataType decl'.sorts decl'.grades decl'.levels decl'.scope),
      sig.HasCodataType D decl' T ∧ T.positive i ∧
        ∀ I, ∀ r ∈ (T.body I).recursion decl'.names, r = none

end Sic.Core
