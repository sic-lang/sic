module

public import Sic.Core.Reduction
public import Sic.Core.Substitution.Closed

/-!
# Meaning

The meaning of the judgments of annex 17 of RFC 36, after the meaning explanations of Martin-Löf: a
closed judgment is true when its terms compute as it says, and a judgment in a context when it holds
under every pair of equal closed substitutions of the context.
Each judgment of the typing has a meaning, with the same objects: the signatures and their entries,
the contexts, the types, the terms, the arguments of the telescopes and of the instances, the
telescopes in a sort and the destructors in a sort.
The meaning ignores the grades, the modes and the ownerships, as the typing does outside the
judgments of usage and of ownership that the rule of the constant definitions reads.
A closed canonical type is known by the equality of its canonical terms, a partial equivalence
relation `eq(v)`, which the sorts, the data types and the codata types give: the universe `U_n` has
the types of the level below it as terms, equal when they have the same equality of terms, the
universe of propositions `Ω_n` has the propositions of the level below it, equal when they have the
same truth, an instance of a data type has its constructors, equal when they are the same
constructor with equal fields, and an instance of a codata type has its corecursors, equal when
their observations at equal arguments are equal, as the partial equivalence relations of the types
of functions relate the functions; a proposition declared as a data type is true when one of its
constructors has terms for its fields, and one declared as a codata type when each of its
destructors has a result.

The universes are defined one level after the other, and at each level by a least relation, which
gives each type of the level together with the equality of its terms: this induction-recursion is
encoded by its graph, an inductive relation between a type and the equality of its terms, as the
formalization of Adjedj, Lennon-Bertrand, Maillard, Pédrot and Pujet does, in Coq, for its universes.
The graph gives one type at a time, rather than two equal types, and two types are equal when they
have the same equality of terms, so that the fields of a constructor, whose types depend on the
fields before them, need only the condition that equal fields before them give the same equality of
terms, as the partial equivalence relations of the types of functions do.
The fields of an instance in `U_n` have types of `U_n` or of a sort below it, so that the graph of a
level is given by the relations of all the levels below it, defined before it.
The levels of a closed term need not be numerals, since an instance of a definition may give `l ⊔ 0`
to its body, so that the sorts and the instances are related by the values of their levels.

The meaning computes each constant to its interpretation `ι(c)`: it computes in the signature whose
constants become definitions with these bodies, so that it has a single reduction, that of the
conversion.
Each entry is meaningful in the whole signature, and a closed judgment requires the names of its
signature to be distinct, rather than its meaning, so that the soundness proves each entry
meaningful in the whole signature from its typing in the signature before it.

ADE give no meaning to the judgments: their logical relation is defined on the typed reduction, for
the decidability of the conversion, and it is not a model of the type theory in the computations.
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

/-! ## Equality of the Canonical Terms -/

/-- A relation between closed terms. -/
abbrev TermRel : Type := Term 0 [] → Term 0 [] → Prop

/-- A relation between the terms of the fields of two constructors. -/
abbrev FieldsRel : Type := Terms 0 [] → Terms 0 [] → Prop

/-- The relations of the sorts of one level `n`, given by their graphs. -/
structure LevelRel where
  /-- `(v, R) ∈ ty(U_n)`: `v` is a type of `U_n`, whose canonical terms are equal by `R`. -/
  univ : Term 0 [] → TermRel → Prop
  /-- `(v, b) ∈ ty(Ω_n)`: `v` is a proposition of `Ω_n`, whose truth is `b`. -/
  prop : Term 0 [] → Prop → Prop

/-- The relations of the sorts of the levels below `n`. -/
abbrev LevelRel.Below (n : Nat) : Type := (m : Nat) → m < n → LevelRel

/-- `eq⇓(R)`: two closed terms that compute to canonical terms that `R` relates, the equality of the
terms of a type that is not a proposition, whose canonical terms are equal by `R`.
RFC: `\mathsf{eq}_\Downarrow` -/
def TermRel.computed (sig : Signature) (ι : Interpretation) (R : TermRel) : TermRel :=
  fun t u => ∃ v w, Computesι sig ι t v ∧ Computesι sig ι u w ∧ R v w

/-- The equality of the terms of the fields of the empty telescope, which relates the empty terms. -/
def FieldsRel.nil : FieldsRel
  | .nil, .nil => True
  | _, _ => False

/-- The equality of the terms of the fields of a telescope `x : A, Θ`, where `F` is the equality of the
terms of `A`, and `G a` that of the terms of `Θ[a / x]`, which the first terms instantiate. -/
def FieldsRel.cons (F : TermRel) (G : Term 0 [] → FieldsRel) : FieldsRel
  | .cons t ts, .cons u us => F t u ∧ G t ts us
  | _, _ => False

/-- `v = T.c(t̄)`: the closed term `v` is the constructor named `c` of the declared type `D`, at some
instance, applied to the terms `t̄`. -/
def Term.IsCtor (D c : Name) (ts : Terms 0 []) (v : Term 0 []) : Prop :=
  ∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
    (as : InstanceArgs 0 [] Δ), v = .ctor D qs ls ps as c ts

/-- `(eq_c)`: the equality of the canonical terms of an instance of the data type `T`, named `D`, which
relates two constructors of the same name, at any instances of `D`, whose fields are equal by the
equality `S c` of the terms of the fields of the constructor `c`.
RFC: `\mathsf{eq}_c` -/
def DataType.ctorRel {j g k : Nat} {Δ : Scope} (D : Name) (T : DataType j g k Δ)
    (S : Constructor j g k Δ → FieldsRel) : TermRel :=
  fun v w => ∃ c ∈ T.constructors, ∃ ts us, v.IsCtor D c.name ts ∧ w.IsCtor D c.name us ∧ S c ts us

/-- `(true_D)`: the truth of a proposition declared as the data type `T`, true when one of its
constructors has terms for its fields, which `S c` relates.
RFC: `\mathsf{true}_D` -/
def DataType.truth {j g k : Nat} {Δ : Scope} (T : DataType j g k Δ)
    (S : Constructor j g k Δ → FieldsRel) : Prop :=
  ∃ c ∈ T.constructors, ∃ ts, S c ts ts

/-- `(eq_μ)`: the equality of the canonical terms of the instances of the data types `Ts` of a block,
the least relations, one for each type, that relate the canonical terms that `(eq_c)` relates, when
the equality `S X c` of the terms of the fields of each constructor `c` relates the terms of its
recursive fields by the relations `X`: they are related by every relations `X` closed under these
clauses.
RFC: `\mathsf{eq}_\mu` -/
def DataType.blockRel {j g k : Nat} {Δ : Scope} (Ts : List (DataType j g k Δ))
    (S : (Name → TermRel) → Constructor j g k Δ → FieldsRel) (D : Name) : TermRel :=
  fun v w => ∀ X : Name → TermRel,
    (∀ T ∈ Ts, ∀ v w, T.ctorRel T.name (S X) v w → X T.name v w) → X D v w

/-- `(true_μ)`: the truth of the propositions declared as the data types `Ts` of a block, the least
truths, one for each type, that `(true_D)` gives, when the equality `S B c` of the terms of the fields
of each constructor `c` reads the truths `B` of its recursive fields: true when every truths `B`
closed under these clauses are.
RFC: `\mathsf{true}_\mu` -/
def DataType.blockTruth {j g k : Nat} {Δ : Scope} (Ts : List (DataType j g k Δ))
    (S : (Name → Prop) → Constructor j g k Δ → FieldsRel) (D : Name) : Prop :=
  ∀ B : Name → Prop, (∀ T ∈ Ts, T.truth (S B) → B T.name) → B D

/-- Closed abstractions, one for each destructor, found by its name and the parameters of its
arguments: the observations of a closed term of a codata type, or what the destructors of the type
relate. -/
abbrev Observations : Type := Name → (ps : List Parameter) → Term 0 (Scope.extend [] ps.length)

/-- A relation between closed abstractions for the destructors of a codata type. -/
abbrev ObsRel : Type := Observations → Observations → Prop

/-- The closed term `v` is a corecursor of the declared type `D`, whose observations at the instance
it carries are `o`. -/
def Term.CorecObservations (D : Name) (v : Term 0 []) (o : Observations) : Prop :=
  ∃ (r : Grade) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
    (as : InstanceArgs 0 [] Δ) (ss : Terms 0 []) (Ss : States 0 []) (gs : CorecBranches 0 []),
    v = .corec r D qs ls ps as ss Ss gs ∧ o = v.observation D qs ls ps as

/-- `(eq_d)`: the equality of the canonical terms of an instance of the codata type named `D`, which
relates two corecursors of `D`, at any instances, whose observations, each at the instance it
carries, the equality `S` of the destructors of the type relates: the instance only determines the
type of the term, as for `(eq_c)`.
RFC: `\mathsf{eq}_d` -/
def corecRel (D : Name) (S : ObsRel) : TermRel :=
  fun v w => ∃ o₁ o₂, v.CorecObservations D o₁ ∧ w.CorecObservations D o₂ ∧ S o₁ o₂

/-- `(true_d)`: the truth of a proposition declared as a codata type, true when the equality `S` of
its destructors relates some abstractions to themselves.
RFC: `\mathsf{true}_d` -/
def ObsRel.truth (S : ObsRel) : Prop :=
  ∃ o, S o o

/-- Two closed abstractions `x̄. B₁` and `x̄. B₂` for a destructor whose arguments have the equality
`SΘ`: at equal arguments, their results are related by the equality `F t̄` of the terms of the
result type at the first arguments. -/
def AbstractionRel {ps : List Parameter} (SΘ : FieldsRel) (F : Terms 0 [] → TermRel)
    (f₁ f₂ : Term 0 (Scope.extend [] ps.length)) : Prop :=
  ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
    F ts.terms (f₁.subst ts.toSubst) (f₂.subst us.toSubst)

/-- `(eq_ν)`: the equality of the canonical terms of the instances of the codata types `Ts` of a
block, the greatest relations, one for each type, whose related terms `(eq_d)` relates, when the
equality `S X T` of the destructors of each type `T` relates the results of its recursive
destructors by the relations `X`: they are related by some relations `X` consistent with these
clauses.
RFC: `\mathsf{eq}_\nu` -/
def CodataType.blockRel {j g k : Nat} {Δ : Scope} (Ts : List (CodataType j g k Δ))
    (S : (Name → TermRel) → CodataType j g k Δ → ObsRel) (D : Name) : TermRel :=
  fun v w => ∃ X : Name → TermRel,
    (∀ T ∈ Ts, ∀ v w, X T.name v w → corecRel T.name (S X T) v w) ∧ X D v w

/-- `(true_ν)`: the truth of the propositions declared as the codata types `Ts` of a block, the
greatest truths, one for each type, that `(true_d)` gives, when the equality `S B T` of the
destructors of each type `T` reads the truths `B` of its recursive destructors: true when some
truths `B` consistent with these clauses are.
RFC: `\mathsf{true}_\nu` -/
def CodataType.blockTruth {j g k : Nat} {Δ : Scope} (Ts : List (CodataType j g k Δ))
    (S : (Name → Prop) → CodataType j g k Δ → ObsRel) (D : Name) : Prop :=
  ∃ B : Name → Prop, (∀ T ∈ Ts, B T.name → (S B T).truth) ∧ B D

mutual

-- ADE: none.
/--
`ty(U_n)`: the least relation of the clauses of the universes and of the instances of the data
types and of the codata types in `U_n`, given the relations `below` of the levels below `n`.
-/
inductive UnivRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Term 0 [] → TermRel → Prop where
  /-- `(ty_U)`: the universe `U_k`, if `k + 1 = n`, whose terms are equal when they are types of `U_k`
  with the same equality.
  RFC: `\mathsf{ty}_U` -/
  | univ {l : Level 0} {k : Nat} (hl : l.closedValue = k) (hk : k + 1 = n) :
      UnivRel sig ι n below (.sort ⟨.type, l⟩) fun A B =>
        ∃ R, (below k (hk ▸ Nat.lt_succ_self k)).univ A R ∧
          (below k (hk ▸ Nat.lt_succ_self k)).univ B R
  /-- `(ty_Ω)`: the universe of propositions `Ω_k`, if `k + 1 = n`, whose terms are equal when they
  are propositions of `Ω_k` with the same truth.
  RFC: `\mathsf{ty}_\Omega` -/
  | prop {l : Level 0} {k : Nat} (hl : l.closedValue = k) (hk : k + 1 = n) :
      UnivRel sig ι n below (.sort ⟨.prop, l⟩) fun P Q =>
        ∃ b₁ b₂, (below k (hk ▸ Nat.lt_succ_self k)).prop P b₁ ∧
          (below k (hk ▸ Nat.lt_succ_self k)).prop Q b₂ ∧ (b₁ ↔ b₂)
  /-- `(ty_D)`: an instance `D.{s̄; l̄; p̄} ā` of a data type `T` of the signature in `U_n`, whose
  block has types whose constructors have fields that are telescopes in `U_n`, whatever the
  relations `X` of the instances of the types of the block at their recursive fields, and whose
  canonical terms are equal by `(eq_μ)`.
  RFC: `\mathsf{ty}_D` -/
  | data {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel)
      (hS : ∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        TelRel sig ι n below .type
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) :
      UnivRel sig ι n below v (DataType.blockRel decl.dataTypes S D)
  /-- `(ty_d)`: an instance `D.{s̄; l̄; p̄} ā` of a codata type `T` of the signature in `U_n`, whose
  block has types whose destructors are in `U_n` at the arguments `ā`, whatever the relations `X` of
  the instances of the types of the block at their recursive destructors, and whose canonical terms
  are equal by `(eq_ν)`.
  RFC: `\mathsf{ty}_d` -/
  | codata {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel)
      (hS : ∀ X, ∀ T' ∈ decl.codataTypes,
        DesRel sig ι n below .type
          (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S X T')) :
      UnivRel sig ι n below v (CodataType.blockRel decl.codataTypes S D)

-- ADE: none.
/--
`ty(Ω_n)`: the least relation of the clauses of the instances of the data types and of the codata
types in `Ω_n`, given the
relations `below` of the levels below `n`, which gives each proposition its truth.
-/
inductive PropRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Term 0 [] → Prop → Prop where
  /-- `(ty_DΩ)`: an instance `D.{s̄; l̄; p̄} ā` of a data type `T` of the signature in `Ω_n`, whose
  block has types whose constructors have fields that are telescopes in `Ω_n`, whatever the truths
  `B` of the instances of the types of the block at their recursive fields, and whose truth is
  `(true_μ)`.
  RFC: `\mathsf{ty}_{D\Omega}` -/
  | data {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel)
      (hS : ∀ B, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        TelRel sig ι n below .prop
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => fun _ _ => B D')
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S B c)) :
      PropRel sig ι n below v (DataType.blockTruth decl.dataTypes S D)
  /-- `(ty_dΩ)`: an instance `D.{s̄; l̄; p̄} ā` of a codata type `T` of the signature in `Ω_n`, whose
  block has types whose destructors are in `Ω_n` at the arguments `ā`, whatever the truths `B` of
  the instances of the types of the block at their recursive destructors, and whose truth is
  `(true_ν)`.
  RFC: `\mathsf{ty}_{d\Omega}` -/
  | codata {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → Prop) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel)
      (hS : ∀ B, ∀ T' ∈ decl.codataTypes,
        DesRel sig ι n below .prop
          (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => fun _ _ => B D')
          ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S B T')) :
      PropRel sig ι n below v (CodataType.blockTruth decl.codataTypes S D)

-- ADE: none.
/--
`ty(s_n)` for the telescopes: `Θ` is a closed telescope in the sort of the quality `s` at the level
`n`, the terms of whose entries are equal by `S`; the equality of the terms of the rest of the
telescope, which the first term instantiates, is the same for equal first terms.
The entries at the positions `i` where `rs i` is `R` are recursive fields, whose terms are equal by
`R`, given rather than computed, and on which the rest does not depend; a telescope that is not the
fields of a constructor has none, `rs` being `fun _ => none`.
-/
inductive TelRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Quality → (Nat → Option TermRel) → {ps : List Parameter} → Telescope 0 [] ps →
      FieldsRel → Prop where
  /-- `(ty_Θε)`: the empty telescope.
  RFC: `\mathsf{ty}_{\Theta\varepsilon}` -/
  | nil {s : Quality} {rs : Nat → Option TermRel} :
      TelRel sig ι n below s rs .nil FieldsRel.nil
  /-- `(ty_Θ,)`: a first type, not a recursive field, that computes to a type of a sort that `s_n`
  bounds, whose terms are equal by `F`, and a rest that is a telescope for each term of it.
  RFC: `\mathsf{ty}_{\Theta,}` -/
  | cons {s : Quality} {rs : Nat → Option TermRel} {q : Grade} {p : Parameter}
      {ps : List Parameter} {A v : Term 0 []} {Θ : Telescope 0 [.var] ps} {F : TermRel}
      (hA : Computesι sig ι A v) (hF : FieldRel sig ι n below s v F) (G : Term 0 [] → FieldsRel)
      (hG : ∀ a, F a a → TelRel sig ι n below s (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a))
        (G a))
      (hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us) (hrs : rs 0 = none) :
      TelRel sig ι n below s rs (.cons q p A Θ) (FieldsRel.cons F G)
  /-- `(ty_Θrec)`: a first type that is a recursive field, whose terms are equal by the relation `R`
  that `rs` gives it, and a rest that is the same telescope, with the same equality, for every term.
  RFC: `\mathsf{ty}_{\Theta\mathsf{rec}}` -/
  | recursive {s : Quality} {rs : Nat → Option TermRel} {q : Grade} {p : Parameter}
      {ps : List Parameter} {A : Term 0 []} {Θ : Telescope 0 [.var] ps} {R : TermRel}
      (hrs : rs 0 = some R) (G : FieldsRel)
      (hG : ∀ a, TelRel sig ι n below s (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a)) G) :
      TelRel sig ι n below s rs (.cons q p A Θ) (FieldsRel.cons R fun _ => G)

-- ADE: none.
/--
`ty(s_n)` for the destructors: the destructors `d̄`, at the closed substitution `θ` of their scope,
are in the sort of the quality `s` at the level `n`, and the abstractions for them are equal by `S`;
the arguments of each destructor are a telescope in `U_n`, its result a type of a sort that `s_n`
bounds for equal arguments, and the destructors after it are, for each abstraction for it, the
same for equal abstractions.
The destructors at the positions `i` where `rs i` is `R` are recursive, whose results are equal by
`R`, given rather than computed, and on which the destructors after them do not depend; the
destructors of a type that is not recursive have none.
The Lean carries the closed substitution of the scope of the destructors, rather than the closed
destructors `d̄[θ]` of the RFC, as the closed judgments of the contexts do, so that the substitution
of the destructors and their instance `d̄ⱼ[T]` at the arguments of the parameters need no definition
of their own.
RFC: `\mathsf{subst}_\theta.\bar d`
RFC: `\mathsf{inst}_{\bar d}`
-/
inductive DesRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Quality → (Nat → Option TermRel) → {Γ : Scope} → {ns : List Name} → Destructors 0 Γ ns →
      Subst 0 [] Γ → ObsRel → Prop where
  /-- `(ty_d̄ε)`: no destructor.
  RFC: `\mathsf{ty}_{\bar d\varepsilon}` -/
  | nil {s : Quality} {rs : Nat → Option TermRel} {Γ : Scope} {θ : Subst 0 [] Γ} :
      DesRel sig ι n below s rs .nil @θ fun _ _ => True
  /-- `(ty_d̄|)`: a destructor `d : (Θ ⊢ B ◀ ψ)`, not recursive, whose arguments `Θ[θ]` are a telescope
  in `U_n` with the equality `SΘ`, whose result type `B[θ, t̄]` computes, at equal arguments `t̄`, to a
  type of a sort that `s_n` bounds, with the equality `F t̄` of its terms, the same for equal
  arguments, and the destructors after it, which are for each abstraction `f` for `d` with the
  equality `G f`, the same for equal abstractions.
  RFC: `\mathsf{ty}_{\bar d|}` -/
  | cons {s : Quality} {rs : Nat → Option TermRel} {Γ : Scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q : Grade}
      {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
      {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {SΘ : FieldsRel}
      (hΘ : TelRel sig ι n below .type (fun _ => none) (Θ.subst θ) SΘ) (F : Terms 0 [] → TermRel)
      (hB : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
        ∃ v, Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v)
      (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ v,
        Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v → FieldRel sig ι n below s v (F ts.terms))
      (hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u)
      (G : Term 0 (Scope.extend [] ps.length) → ObsRel)
      (hG : ∀ f, AbstractionRel SΘ F f f →
        DesRel sig ι n below s (fun i => rs (i + 1)) ds (Subst.snoc θ f) (G f))
      (hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂)
      (hrs : rs 0 = none) :
      DesRel sig ι n below s rs (.cons (d := d) p q Θ B ψ ds) @θ fun o₁ o₂ =>
        AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂
  /-- `(ty_d̄rec)`: a recursive destructor `d : (Θ ⊢ B ◀ ψ)`, whose arguments `Θ[θ]` are a telescope
  in `U_n` with the equality `SΘ`, whose results are equal by the relation `R` that `rs` gives it, and
  the destructors after it, the same, with the same equality, for every abstraction for it.
  RFC: `\mathsf{ty}_{\bar d\mathsf{rec}}` -/
  | recursive {s : Quality} {rs : Nat → Option TermRel} {Γ : Scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q : Grade}
      {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
      {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {SΘ : FieldsRel}
      {R : TermRel} (hrs : rs 0 = some R)
      (hΘ : TelRel sig ι n below .type (fun _ => none) (Θ.subst θ) SΘ) (G : ObsRel)
      (hG : ∀ f, DesRel sig ι n below s (fun i => rs (i + 1)) ds (Subst.snoc θ f) G) :
      DesRel sig ι n below s rs (.cons (d := d) p q Θ B ψ ds) @θ fun o₁ o₂ =>
        AbstractionRel SΘ (fun _ => R) (o₁ d ps) (o₂ d ps) ∧ G o₁ o₂

-- ADE: none.
/--
The canonical type `v` of a field is a type of a sort `κ₁` that the sort of the quality `s` at the
level `n` bounds, whose closed terms are equal by `F`: a type of `U_n` or of a universe below it,
if `s` is not the quality of the propositions, or a proposition of `Ω_n` or of a universe below it.
RFC: `\mathsf{ty}_\Downarrow`
-/
inductive FieldRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Quality → Term 0 [] → TermRel → Prop where
  /-- A type of `U_n`. -/
  | univ {s : Quality} {v : Term 0 []} {R : TermRel} (hs : s = .type) (h : UnivRel sig ι n below v R) :
      FieldRel sig ι n below s v (R.computed sig ι)
  /-- A type of `U_m`, for `m < n`. -/
  | univBelow {s : Quality} {v : Term 0 []} {R : TermRel} (hs : s = .type) (m : Nat) (hm : m < n)
      (h : (below m hm).univ v R) : FieldRel sig ι n below s v (R.computed sig ι)
  /-- A proposition of `Ω_n`. -/
  | prop {s : Quality} {v : Term 0 []} {b : Prop} (h : PropRel sig ι n below v b) :
      FieldRel sig ι n below s v fun _ _ => b
  /-- A proposition of `Ω_m`, for `m < n`. -/
  | propBelow {s : Quality} {v : Term 0 []} {b : Prop} (m : Nat) (hm : m < n) (h : (below m hm).prop v b) :
      FieldRel sig ι n below s v fun _ _ => b

end

/-- The relations of the sorts of the level `n`, defined after those of the levels below it. -/
def levelRel (sig : Signature) (ι : Interpretation) (n : Nat) : LevelRel :=
  ⟨UnivRel sig ι n fun m _ => levelRel sig ι m, PropRel sig ι n fun m _ => levelRel sig ι m⟩
termination_by n
decreasing_by all_goals assumption

/-- `ty(U_n)` at the level `n`. -/
theorem levelRel_univ (sig : Signature) (ι : Interpretation) (n : Nat) :
    (levelRel sig ι n).univ = UnivRel sig ι n fun m _ => levelRel sig ι m := by
  rw [levelRel]

/-- `ty(Ω_n)` at the level `n`. -/
theorem levelRel_prop (sig : Signature) (ι : Interpretation) (n : Nat) :
    (levelRel sig ι n).prop = PropRel sig ι n fun m _ => levelRel sig ι m := by
  rw [levelRel]

-- ADE: none.
/-- `eq(v) = R`: the closed canonical type `v` is a type of a sort, whose canonical terms are equal by
`R`, or a proposition, whose closed terms are equal by `R`. -/
inductive HasEq (sig : Signature) (ι : Interpretation) (v : Term 0 []) (R : TermRel) : Prop where
  /-- A type of the universe `U_n`.
  RFC: `\mathsf{eq}_{\mathsf{type}}` -/
  | univ (n : Nat) (h : (levelRel sig ι n).univ v R)
  /-- `(eq_true)` and `(eq_false)`: a proposition of `Ω_n` whose truth is `b`, whose closed terms are
  all equal proofs when it is true, and none when it is false.
  RFC: `\mathsf{eq}_{\mathsf{true}}`
  RFC: `\mathsf{eq}_{\mathsf{false}}` -/
  | prop (n : Nat) (b : Prop) (h : (levelRel sig ι n).prop v b) (hR : ∀ t u, R t u ↔ b)

/-- `(prop_v)`: `v` is a proposition, a term of a universe of propositions.
RFC: `\mathsf{prop}_v` -/
def IsProp (sig : Signature) (ι : Interpretation) (v : Term 0 []) : Prop :=
  ∃ k b, (levelRel sig ι k).prop v b

/-- `(prop_⇓)`: the closed type `A` computes to a proposition.
RFC: `\mathsf{prop}_\Downarrow` -/
def ComputesToProp (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ∃ v, Computesι sig ι A v ∧ IsProp sig ι v

/-! ## Closed Judgments

The clauses of the closed judgments are stated without the meaning `⊨ Σ` of their signature, which
they require, so that the meaning of the signatures is defined from them. -/

/-- The clause of `(⊨_type≡)`: `A` and `B` compute to canonical types whose terms have the same
equality. -/
def EqTypeClause (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  ∃ v w R, Computesι sig ι A v ∧ Computesι sig ι B w ∧ HasEq sig ι v R ∧ HasEq sig ι w R

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` for the terms: `t` and `u` compute to equal canonical terms
of the canonical form of `A`, or are equal proofs of it when it is a proposition. -/
def EqTermClause (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  (¬ ComputesToProp sig ι A → ∃ v w₁ w₂ R, Computesι sig ι A v ∧ Computesι sig ι t w₁ ∧
    Computesι sig ι u w₂ ∧ HasEq sig ι v R ∧ R w₁ w₂) ∧
  (ComputesToProp sig ι A → ∃ v R, Computesι sig ι A v ∧ HasEq sig ι v R ∧ R t u)

/-- The clause of `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`: at each instance of the sort and grade
variables and each value of the level variables, the body is a term of the type; the meaning ignores
the mode and the ownership. -/
def ConstantDefinition.Clause (sig : Signature) (ι : Interpretation) (d : ConstantDefinition) :
    Prop :=
  ∀ inst (ρ : Fin d.levels → Nat),
    EqTypeClause sig ι ((d.type inst).atLevels ρ) ((d.type inst).atLevels ρ) ∧
      EqTermClause sig ι ((d.body inst).atLevels ρ) ((d.body inst).atLevels ρ)
        ((d.type inst).atLevels ρ)

/-- The clause of `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p`: at each instance of the sort and grade variables
and each value of the level variables, the interpretation of the constant is a term of its type; the
meaning ignores the mode and the ownership. -/
def ConstantDeclaration.Clause (sig : Signature) (ι : Interpretation) (c : ConstantDeclaration) :
    Prop :=
  ∀ inst (ρ : Fin c.levels → Nat),
    EqTypeClause sig ι ((c.type inst).atLevels ρ) ((c.type inst).atLevels ρ) ∧
      EqTermClause sig ι ((ι c inst).atLevels ρ) ((ι c inst).atLevels ρ)
        ((c.type inst).atLevels ρ)

-- ADE: none.
/-- `(⊨def)`: `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`, in a signature whose names are distinct. -/
def ValidConstantDefinition (sig : Signature) (ι : Interpretation) (d : ConstantDefinition) : Prop :=
  sig.Distinct ∧ d.Clause sig ι

-- ADE: none.
/-- `(⊨decl)`: `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p`, in a signature whose names are distinct. -/
def ValidConstantDeclaration (sig : Signature) (ι : Interpretation) (c : ConstantDeclaration) :
    Prop :=
  sig.Distinct ∧ c.Clause sig ι

/-- `(⊨_type≡)`: `Σ ⊨ A ≡ B`.
RFC: `\vDash_{\mathsf{type}\equiv}` -/
def ValidEqType₀ (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  sig.Distinct ∧ EqTypeClause sig ι A B

/-- `(⊨_type)`: `Σ ⊨ A`.
RFC: `\vDash_{\mathsf{type}}` -/
def ValidType₀ (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ValidEqType₀ sig ι A A

/-- `(⊨_≡)` and `(⊨_≡Ω)`: `Σ ⊨ t ≡ u : A`.
RFC: `\vDash_\equiv`
RFC: `\vDash_{\equiv\Omega}` -/
def ValidEqTerm₀ (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  ValidType₀ sig ι A ∧ EqTermClause sig ι t u A

/-- `(⊨)`: `Σ ⊨ t : A`.
RFC: `\vDash` -/
def ValidTerm₀ (sig : Signature) (ι : Interpretation) (t A : Term 0 []) : Prop :=
  ValidEqTerm₀ sig ι t t A

/-- `(⊨def)`, as the RFC states it: at each instance of the sort and grade variables and each value
of the level variables, the body is a term of the type; the names of the signature are then
distinct, since an instance exists whatever the numbers of the variables.
RFC: `{\vDash}\mathsf{def}` -/
theorem ValidConstantDefinition.iff {sig : Signature} {ι : Interpretation} {d : ConstantDefinition} :
    ValidConstantDefinition sig ι d ↔
      ∀ inst (ρ : Fin d.levels → Nat),
        ValidTerm₀ sig ι ((d.body inst).atLevels ρ) ((d.type inst).atLevels ρ) :=
  ⟨fun ⟨hd, hc⟩ inst ρ => ⟨⟨hd, (hc inst ρ).1⟩, (hc inst ρ).2⟩,
    fun h => ⟨(h ⟨fun _ => .type, fun _ => .zero⟩ fun _ => 0).1.1,
      fun inst ρ => ⟨(h inst ρ).1.2, (h inst ρ).2⟩⟩⟩

/-- `(⊨decl)`, as the RFC states it: at each instance of the sort and grade variables and each value
of the level variables, the interpretation of the constant is a term of its type.
RFC: `{\vDash}\mathsf{decl}` -/
theorem ValidConstantDeclaration.iff {sig : Signature} {ι : Interpretation}
    {c : ConstantDeclaration} :
    ValidConstantDeclaration sig ι c ↔
      ∀ inst (ρ : Fin c.levels → Nat),
        ValidTerm₀ sig ι ((ι c inst).atLevels ρ) ((c.type inst).atLevels ρ) :=
  ⟨fun ⟨hd, hc⟩ inst ρ => ⟨⟨hd, (hc inst ρ).1⟩, (hc inst ρ).2⟩,
    fun h => ⟨(h ⟨fun _ => .type, fun _ => .zero⟩ fun _ => 0).1.1,
      fun inst ρ => ⟨(h inst ρ).1.2, (h inst ρ).2⟩⟩⟩

/-! ## Hypothetical Judgments -/

/-- The substitution `σ` without its last entry. -/
def Subst.tail {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} (σ : Subst k Γ (e :: Δ)) : Subst k Γ Δ :=
  fun x => σ x.succ

/-- The number of the entries of a context, those of the telescope of a second-order variable
included. -/
def Context.size {k : Nat} : {Γ : Scope} → Context k Γ → Nat
  | _, .empty => 0
  | _, .var ctx _ => ctx.size + 1
  | _, .secondOrder (ps := ps) ctx _ _ _ => ctx.size + ps.length + 1

/-- The entries of `Γ, Θ` are those of `Γ` and of `Θ`. -/
theorem Context.size_append {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context k Γ) → (Θ : Telescope k Γ ps) →
      (ctx.append Θ).size = ctx.size + ps.length
  | _, [], _, .nil => rfl
  | _, _ :: _, ctx, .cons _ _ A Θ =>
    (Context.size_append (ctx.var A) Θ).trans (by simp only [Context.size, List.length_cons]; omega)

-- ADE: none.
/--
`(σ₁, σ₂) ∈ eq(Γ)`: two equal closed substitutions of `Γ`, which give each variable equal closed
terms of its type, and each second-order variable abstractions whose instances by equal arguments are
equal terms of its type; the arguments of a telescope are the equal substitutions of the context it
forms.
RFC: `\mathsf{eq}_\varepsilon`
RFC: `\mathsf{eq}_x`
RFC: `\mathsf{eq}_X`
-/
def EqSubst (sig : Signature) (ι : Interpretation) :
    {Γ : Scope} → Context 0 Γ → Subst 0 [] Γ → Subst 0 [] Γ → Prop
  /- `(eq_ε)`. -/
  | _, .empty, _, _ => True
  /- `(eq_x)`. -/
  | _, .var ctx A, σ₁, σ₂ => EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ValidEqTerm₀ sig ι (σ₁ .zero) (σ₂ .zero) (A.subst (Subst.tail σ₁))
  /- `(eq_X)`. -/
  | _, .secondOrder ctx Θ A _, σ₁, σ₂ => EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst (Subst.tail σ₁))) τ₁ τ₂ →
        ValidEqTerm₀ sig ι ((σ₁ .zero).subst τ₁) ((σ₂ .zero).subst τ₂)
          ((A.subst (Subst.liftN _ (Subst.tail σ₁))).subst τ₁)
termination_by _ ctx => ctx.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

-- ADE: none.
/-- `Σ ⊨ Γ`, at levels without variables: the last type of the context is a type in the context
before it.
RFC: `{\vDash}\mathsf{ctx}_\varepsilon` -/
def ValidCtx₀ (sig : Signature) (ι : Interpretation) : {Γ : Scope} → Context 0 Γ → Prop
  /- `(⊨ctx_ε)`. -/
  | _, .empty => sig.Distinct
  /- `(⊨ctx_x)`: `Σ; Γ ⊨ A`. -/
  | _, .var ctx A => ValidCtx₀ sig ι ctx ∧
      ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (A.subst σ₂)
  /- `(⊨ctx_X)`: `Σ; Γ, Θ ⊨ A`. -/
  | _, .secondOrder ctx Θ A _ => ValidCtx₀ sig ι (ctx.append Θ) ∧
      ∀ σ₁ σ₂, EqSubst sig ι (ctx.append Θ) σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (A.subst σ₂)
termination_by _ ctx => ctx.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

/-- `(⊨Γ_type≡)`: `Σ; Γ ⊨ A ≡ B`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{type}\equiv}` -/
def ValidEqTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A B : Term 0 Γ) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (B.subst σ₂)

/-- `(⊨Γ_type)`: `Σ; Γ ⊨ A`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{type}}` -/
def ValidTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : Prop :=
  ValidEqTypeΓ sig ι ctx A A

/-- `(⊨Γ_≡)`: `Σ; Γ ⊨ t ≡ u : A`, at levels without variables.
RFC: `{\vDash}\Gamma_\equiv` -/
def ValidEqTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t u A : Term 0 Γ) : Prop :=
  ValidTypeΓ sig ι ctx A ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι (t.subst σ₁) (u.subst σ₂) (A.subst σ₁)

/-- `(⊨Γ)`: `Σ; Γ ⊨ t : A`, at levels without variables.
RFC: `{\vDash}\Gamma` -/
def ValidTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t A : Term 0 Γ) : Prop :=
  ValidEqTermΓ sig ι ctx t t A

-- ADE: none.
/-- `(⊨Γ_tel≡)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, at levels without variables: the arguments substituted by two
equal closed substitutions `σ₁` and `σ₂` of the context are equal substitutions of the context that
the telescope `Θ[σ₁]` forms.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\equiv}` -/
def ValidEqArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts us : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) (ts.subst σ₁).toSubst
        (us.subst σ₂).toSubst

/-- `(⊨Γ_tel)`: `Σ; Γ ⊨ t̄ : Θ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{tel}}` -/
def ValidArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidEqArgsΓ sig ι ctx ts ts Θ

-- ADE: none.
/-- `(⊨Γ_arg≡)`: `Σ; Γ ⊨ ā₁ ≡ ā₂ : Δ`, at levels without variables: the arguments substituted by
two equal closed substitutions of the context are equal substitutions of the parameters `Δ`.
RFC: `{\vDash}\Gamma_{\mathsf{arg}\equiv}` -/
def ValidEqInstanceArgsΓ (sig : Signature) (ι : Interpretation) {Γ Δ : Scope} (ctx : Context 0 Γ)
    (as₁ as₂ : InstanceArgs 0 Γ Δ) (params : Context 0 Δ) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      EqSubst sig ι params (as₁.subst σ₁).toSubst (as₂.subst σ₂).toSubst

/-- `(⊨Γ_arg)`: `Σ; Γ ⊨ ā : Δ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{arg}}` -/
def ValidInstanceArgsΓ (sig : Signature) (ι : Interpretation) {Γ Δ : Scope} (ctx : Context 0 Γ)
    (as : InstanceArgs 0 Γ Δ) (params : Context 0 Δ) : Prop :=
  ValidEqInstanceArgsΓ sig ι ctx as as params

/-- `(⊨ctx_x)`, as the RFC states it.
RFC: `{\vDash}\mathsf{ctx}_x` -/
theorem validCtx₀_var {sig : Signature} {ι : Interpretation} {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : ValidCtx₀ sig ι (ctx.var A) ↔ ValidTypeΓ sig ι ctx A := by
  rw [ValidCtx₀]; rfl

/-- `(⊨ctx_X)`, as the RFC states it.
RFC: `{\vDash}\mathsf{ctx}_X` -/
theorem validCtx₀_secondOrder {sig : Signature} {ι : Interpretation} {Γ : Scope}
    {ps : List Parameter} (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (A : Term 0 (Γ.extend ps.length))
    (ψ : ResultOwnership ps.length) : ValidCtx₀ sig ι (ctx.secondOrder Θ A ψ) ↔ ValidTypeΓ sig ι (ctx.append Θ) A := by
  rw [ValidCtx₀]; rfl

/-! ## Telescopes -/

-- ADE: none.
/-- `Σ ⊨ Θ₁ ≡ Θ₂ : κ`: two closed telescopes are equal in the sort `κ`, their first types being
equal types of a sort that `κ` bounds, and the rest of them equal for every pair of equal terms of
these types; the meaning ignores their grades.
RFC: `{\vDash}\mathsf{tel}_{\kappa\varepsilon}`
RFC: `{\vDash}\mathsf{tel}_{\kappa,}` -/
def ValidEqTelescope₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0) :
    {ps : List Parameter} → Telescope 0 [] ps → Telescope 0 [] ps → Prop
  /- `(⊨tel_κε)`. -/
  | [], .nil, .nil => sig.Distinct
  /- `(⊨tel_κ,)`. -/
  | _ :: _, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂ =>
    (∃ κ₁, κ₁ ≼ κ ∧ ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) ∧
      ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ A₁ →
        ValidEqTelescope₀ sig ι κ (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))

-- ADE: none.
/-- `(⊨Γ_tel_κ≡)`: `Σ; Γ ⊨ Θ₁ ≡ Θ₂ : κ`, at levels without variables: the telescopes substituted by
two equal closed substitutions of the context give equal closed telescopes in the sort `κ`.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\kappa\equiv}` -/
def ValidEqTelescopeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (Θ₁ Θ₂ : Telescope 0 Γ ps) (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqTelescope₀ sig ι κ (Θ₁.subst σ₁) (Θ₂.subst σ₂)

/-- `(⊨Γ_tel_κ)`: `Σ; Γ ⊨ Θ : κ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\kappa}` -/
def ValidTelescopeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (κ : Universe 0) : Prop :=
  ValidEqTelescopeΓ sig ι ctx Θ Θ κ

-- ADE: none.
/-- `Σ ⊨ d̄[θ₁] ≡ d̄[θ₂] : κ` for the destructors of a codata type, whose recursive destructors `rs`
gives, of the instances `inst D` of the block: the destructors at two closed substitutions `θ₁` and
`θ₂` of their scope are equal in the sort `κ`; the arguments of each destructor are equal
telescopes in the universe of the level of `κ`; the results of a destructor that is not recursive
are equal types of a sort that `κ` bounds at equal arguments, and the destructors after it are equal
for every pair of abstractions for it whose instances at equal arguments are equal terms of its
result; the result of a recursive destructor of the type `D` is the instance `inst D` of the block,
and the destructors after it are equal for every pair of abstractions for it, on which they do not
depend.
The Lean carries the closed substitutions of the scope of the destructors, as the equality of the
abstractions for them does.
RFC: `{\vDash}\bar d_{\kappa\varepsilon}`
RFC: `{\vDash}\bar d_{\kappa|}`
RFC: `{\vDash}\bar d_{\kappa\mathsf{rec}}` -/
def ValidEqDestructors₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0) :
    {Γ : Scope} → {ns : List Name} → (Name → Term 0 Γ) → (Nat → Option Name) →
      Destructors 0 Γ ns → Subst 0 [] Γ → Subst 0 [] Γ → Prop
  /- `(⊨d̄_κε)`. -/
  | _, _, _, _, .nil, _, _ => sig.Distinct
  | _, _ :: _, inst, rs, .cons (ps := ps) _ _ Θ B ψ ds, θ₁, θ₂ =>
    ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂) ∧
    match rs 0 with
    /- `(⊨d̄_κ|)`. -/
    | none =>
      (∃ κ₁, κ₁ ≼ κ ∧ ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
          (.sort κ₁)) ∧
      ∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
        ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken) (fun i => rs (i + 1)) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂)
    /- `(⊨d̄_κrec)`. -/
    | some D => B = (inst D).rename (Ren.weakenN ps.length) ∧
      ∀ f₁ f₂, ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken)
        (fun i => rs (i + 1)) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁)
        (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂)

-- ADE: none.
/-- `Σ; Γ ⊨_𝒟 d̄ : κ`, at levels without variables, for the destructors of a codata type, whose
recursive destructors `rs` gives, of the instances `inst D` of the block: the destructors at two
equal closed substitutions of the context are equal in the sort `κ`.
RFC: `{\vDash}\Gamma_{\bar d}` -/
def ValidDestructorsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ns : List Name}
    (ctx : Context 0 Γ) (inst : Name → Term 0 Γ) (rs : Nat → Option Name)
    (ds : Destructors 0 Γ ns) (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧ ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqDestructors₀ sig ι κ inst rs ds σ₁ σ₂

-- ADE: none.
/-- `Σ ⊨ Θ₁ ≡ Θ₂ : κ` for the fields of two constructors, whose recursive fields `rs` gives: the
fields that are not recursive are equal types of a sort that `κ` bounds, the recursive fields of the
type `D` are the instances `inst₁ D` and `inst₂ D` of the block, and the rest of them are equal for
every pair of equal terms of the fields that are not recursive, and for every pair of terms of the
recursive ones, on which they do not depend; the meaning ignores their grades.
RFC: `{\vDash}\mathsf{fields}_\varepsilon`
RFC: `{\vDash}\mathsf{fields}_{,}`
RFC: `{\vDash}\mathsf{fields}_{\mathsf{rec}}` -/
def ValidEqFields₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0)
    (inst₁ inst₂ : Name → Term 0 []) :
    {ps : List Parameter} → (Nat → Option Name) → Telescope 0 [] ps → Telescope 0 [] ps → Prop
  /- `(⊨fields_ε)`. -/
  | [], _, .nil, .nil => sig.Distinct
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂ =>
    match rs 0 with
    /- `(⊨fields_,)`. -/
    | none => (∃ κ₁, κ₁ ≼ κ ∧ ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) ∧
      ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ A₁ →
        ValidEqFields₀ sig ι κ inst₁ inst₂ (fun i => rs (i + 1)) (Θ₁.subst₀ (Subst₀.single v₁))
          (Θ₂.subst₀ (Subst₀.single v₂))
    /- `(⊨fields_rec)`. -/
    | some D => A₁ = inst₁ D ∧ A₂ = inst₂ D ∧
      ∀ v₁ v₂, ValidEqFields₀ sig ι κ inst₁ inst₂ (fun i => rs (i + 1))
        (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))

-- ADE: none.
/-- `Σ; Γ ⊨ Θ : κ` for the fields of a constructor, whose recursive fields `rs` gives, of the
instances `inst D` of the block, at levels without variables: the fields substituted by two equal
closed substitutions of the context give equal closed fields in the sort `κ`.
RFC: `{\vDash}\Gamma_{\mathsf{fields}}` -/
def ValidFieldsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (inst : Name → Term 0 Γ) (rs : Nat → Option Name) (Θ : Telescope 0 Γ ps)
    (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqFields₀ sig ι κ (fun D => (inst D).subst σ₁)
      (fun D => (inst D).subst σ₂) rs (Θ.subst σ₁) (Θ.subst σ₂)

/-! ## Level Variables -/

/-- `(⊨_ρ)`: `Σ ⊨ Γ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidCtx (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ) :
    Prop :=
  ∀ ρ, ValidCtx₀ sig ι (ctx.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A ≡ B`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A B : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ) (B.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A : Term k Γ) : Prop :=
  ∀ ρ, ValidTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t ≡ u : A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t u A : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (u.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t : A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t A : Term k Γ) : Prop :=
  ∀ ρ, ValidTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts us : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidEqArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (us.atLevels ρ) (Θ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ : Θ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (Θ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ ā₁ ≡ ā₂ : Δ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqInstanceArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ Δ : Scope}
    (ctx : Context k Γ) (as₁ as₂ : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  ∀ ρ, ValidEqInstanceArgsΓ sig ι (ctx.atLevels ρ) (as₁.atLevels ρ) (as₂.atLevels ρ)
    (params.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ ā : Δ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidInstanceArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ Δ : Scope}
    (ctx : Context k Γ) (as : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  ∀ ρ, ValidInstanceArgsΓ sig ι (ctx.atLevels ρ) (as.atLevels ρ) (params.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ₁ ≡ Θ₂ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqTelescope (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ps : List Parameter} (ctx : Context k Γ) (Θ₁ Θ₂ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  ∀ ρ, ValidEqTelescopeΓ sig ι (ctx.atLevels ρ) (Θ₁.atLevels ρ) (Θ₂.atLevels ρ) (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidTelescope (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  ∀ ρ, ValidTelescopeΓ sig ι (ctx.atLevels ρ) (Θ.atLevels ρ) (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨_𝒟 d̄ : κ` for the destructors of a codata type, for every value of the level
variables.
RFC: `\vDash_\rho` -/
def ValidDestructors (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ns : List Name} (ctx : Context k Γ) (inst : Name → Term k Γ) (rs : Nat → Option Name)
    (ds : Destructors k Γ ns) (κ : Universe k) : Prop :=
  ∀ ρ, ValidDestructorsΓ sig ι (ctx.atLevels ρ) (fun D => (inst D).atLevels ρ) rs (ds.atLevels ρ)
    (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ : κ` for the fields of a constructor, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidFields (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (inst : Name → Term k Γ) (rs : Nat → Option Name) (Θ : Telescope k Γ ps)
    (κ : Universe k) : Prop :=
  ∀ ρ, ValidFieldsΓ sig ι (ctx.atLevels ρ) (fun D => (inst D).atLevels ρ) rs (Θ.atLevels ρ)
    (κ.atLevels ρ)

/-! ## Signatures and Entries -/

-- ADE: none.
/-- `Σ ⊨ D`: the type declaration `D` is meaningful in the signature `Σ`.
`(⊨data)`: `Σ ⊨ data.{s̄; l̄; p̄ | C} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort and
grade variables that `C` admits, the fields of each constructor are fields in the sort `κ`, in the
context of the parameters, at each value of the level variables, whose recursive fields are the
types of the block at the parameters themselves.
`(⊨codata)`: `Σ ⊨ codata.{s̄; l̄; p̄ | C} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort
and grade variables that `C` admits, the destructors of each type are in the sort `κ`, in the
context of the parameters, at each value of the level variables, whose recursive destructors have
the types of the block at the parameters themselves as results.
The meaning ignores the grades, and the names of the constructors and of the destructors, distinct,
are those of the signature.
RFC: `{\vDash}\mathsf{data}`
RFC: `{\vDash}\mathsf{codata}` -/
def ValidTypeDeclaration (sig : Signature) (ι : Interpretation) (decl : TypeDeclaration) : Prop :=
  match decl.body with
  | .data Ts => ∀ I, decl.constraint I → ∀ T ∈ Ts, ∀ c ∈ T.constructors,
      ValidFields sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
        ((c.fields I).recursionAt decl.names) (c.fields I) (decl.sort I)
  | .codata Ts => ∀ I, decl.constraint I → ∀ T ∈ Ts,
      ValidDestructors sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
        ((T.body I).recursionAt decl.names) (T.body I) (decl.sort I)

/-- The fields of the constructors of a data type of a meaningful type declaration are fields in its
sort, at each instance that its constraint admits. -/
theorem ValidTypeDeclaration.fields {sig : Signature} {ι : Interpretation} {decl : TypeDeclaration}
    (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    (hadm : decl.constraint I) {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : T ∈ decl.dataTypes)
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope} (hc : c ∈ T.constructors) :
    ValidFields sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
      ((c.fields I).recursionAt decl.names) (c.fields I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.dataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact h I hadm T hT c hc
  · exact nomatch hT

/-- The destructors of a codata type of a meaningful type declaration are in its sort, with the types
of the block at the parameters themselves as the results of the recursive ones, at each instance
that its constraint admits. -/
theorem ValidTypeDeclaration.destructors {sig : Signature} {ι : Interpretation}
    {decl : TypeDeclaration} (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    (hadm : decl.constraint I) {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : T ∈ decl.codataTypes) :
    ValidDestructors sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
      ((T.body I).recursionAt decl.names) (T.body I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.codataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact nomatch hT
  · exact h I hadm T hT

-- ADE: none.
/-- `Σ ⊨ e`: the entry `e` is meaningful in the signature `Σ`. -/
def ValidEntry (sig : Signature) (ι : Interpretation) : Entry → Prop
  | .typeDeclaration decl => ValidTypeDeclaration sig ι decl
  | .constantDefinition d => ValidConstantDefinition sig ι d
  | .constantDeclaration c => ValidConstantDeclaration sig ι c

-- ADE: none.
/-- `⊨ Σ`: the names of the signature are distinct, and each of its entries is meaningful in the
whole signature.
RFC: `{\vDash}\mathsf{sig}` -/
def ValidSig (ι : Interpretation) (sig : Signature) : Prop :=
  sig.Distinct ∧ ∀ e ∈ sig, ValidEntry sig ι e

/-! ## Partial Equivalence Relations

The equality `eq(v)` of the terms of a type is a partial equivalence relation, and it is unique, in a
signature whose names are distinct, so that a closed term computes to one canonical term at most and
a declared type is the data type of one declaration.
These properties are proved level by level: those of the relations of a level, `LevelRel.IsPer`,
follow from those of the levels below it, by induction on the clauses that give a type of the level,
together with the telescopes of the fields of its constructors, so that each kind of declaration
adds the cases of its clauses.
A type is given by the clauses of one level and one sort at most, which `UnivRel.level`,
`UnivRel.not_prop` and `PropRel.level` show by cases, without induction. -/

/-- The names of a signature stay distinct when its constants are interpreted. -/
theorem Signature.Distinct.interpret {ι : Interpretation} :
    {sig : Signature} → sig.Distinct → (sig.interpret ι).Distinct
  | [], _ => trivial
  | e :: _, ⟨h, hnodup, hfresh, hc⟩ => by
    have hnames : ∀ e : Entry, (e.interpret ι).names = e.names := by
      intro e; cases e <;> rfl
    refine ⟨h.interpret, (hnames e).symm ▸ hnodup, fun e' he' n hn => ?_, ?_⟩
    · obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 he'
      rw [hnames] at hn ⊢
      exact hfresh e'' he'' n hn
    · cases e <;> exact hc

/-- In a signature whose names are distinct, a closed term computes to one canonical term at
most. -/
theorem Computesι.det {sig : Signature} {ι : Interpretation} {t v₁ v₂ : Term 0 []}
    (hd : sig.Distinct) (h₁ : Computesι sig ι t v₁) (h₂ : Computesι sig ι t v₂) : v₁ = v₂ :=
  Computes.det hd.interpret h₁ h₂

/-- `R` is a partial equivalence relation: symmetric and transitive. -/
structure IsPer {α : Type} (R : α → α → Prop) : Prop where
  /-- `R` is symmetric. -/
  symm {t u : α} : R t u → R u t
  /-- `R` is transitive. -/
  trans {t u w : α} : R t u → R u w → R t w

/-- The relations of the sorts of a level give each type they relate a unique equality of its terms,
itself a partial equivalence relation, and each proposition a unique truth. -/
structure LevelRel.IsPer (L : LevelRel) : Prop where
  /-- The equality of the terms of a type of `U_n` is a partial equivalence relation. -/
  univ_isPer {v : Term 0 []} {R : TermRel} : L.univ v R → _root_.Sic.Core.IsPer R
  /-- `ty(U_n)` gives a type a unique equality of its terms. -/
  univ_unique {v : Term 0 []} {R R' : TermRel} : L.univ v R → L.univ v R' → ∀ t u, R t u ↔ R' t u
  /-- `ty(Ω_n)` gives a proposition a unique truth. -/
  prop_unique {v : Term 0 []} {b b' : Prop} : L.prop v b → L.prop v b' → (b ↔ b')

/-- The equality that `ty(U_n)` gives a type is unique. -/
theorem LevelRel.IsPer.univ_eq {L : LevelRel} (hL : L.IsPer) {v : Term 0 []} {R R' : TermRel}
    (h : L.univ v R) (h' : L.univ v R') : R = R' :=
  funext fun t => funext fun u => propext (hL.univ_unique h h' t u)

/-- `ty(U_n)` at the level `n`, as the clauses of `UnivRel`. -/
theorem levelRel_univ_iff {sig : Signature} {ι : Interpretation} {n : Nat} {v : Term 0 []}
    {R : TermRel} :
    (levelRel sig ι n).univ v R ↔ UnivRel sig ι n (fun m _ => levelRel sig ι m) v R := by
  rw [levelRel_univ]

/-- `ty(Ω_n)` at the level `n`, as the clauses of `PropRel`. -/
theorem levelRel_prop_iff {sig : Signature} {ι : Interpretation} {n : Nat} {v : Term 0 []}
    {b : Prop} : (levelRel sig ι n).prop v b ↔ PropRel sig ι n (fun m _ => levelRel sig ι m) v b := by
  rw [levelRel_prop]

/-! ### Relations Built From Others -/

/-- `eq⇓(R)` is a partial equivalence relation when `R` is one, in a signature whose names are
distinct. -/
theorem TermRel.computed_isPer {sig : Signature} {ι : Interpretation} {R : TermRel}
    (hd : sig.Distinct) (hR : IsPer R) : IsPer (R.computed sig ι) where
  symm := fun ⟨v, w, ht, hu, h⟩ => ⟨w, v, hu, ht, hR.symm h⟩
  trans := fun ⟨v, _, ht, hu, h⟩ ⟨_, x, hu', hx, h'⟩ => by
    cases Computesι.det hd hu hu'
    exact ⟨v, x, ht, hx, hR.trans h h'⟩

/-- `eq⇓(R)` relates the same terms for relations `R` that relate the same terms. -/
theorem TermRel.computed_congr {sig : Signature} {ι : Interpretation} {R R' : TermRel}
    (h : ∀ t u, R t u ↔ R' t u) : ∀ t u, R.computed sig ι t u ↔ R'.computed sig ι t u :=
  fun _ _ => ⟨fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, (h v w).1 hvw⟩,
    fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, (h v w).2 hvw⟩⟩

/-- The equality of the terms of the fields of the empty telescope is a partial equivalence
relation. -/
theorem FieldsRel.nil_isPer : IsPer FieldsRel.nil where
  symm {ts us} h := match ts, us, h with
    | .nil, .nil, _ => trivial
  trans {ts us ws} h h' := match ts, us, ws, h, h' with
    | .nil, .nil, .nil, _, _ => trivial

/-- The equality of the terms of the fields of a telescope `x : A, Θ` is a partial equivalence
relation, when the equality of the terms of `A` is one, and so is the equality of the terms of
`Θ[a / x]` for each term `a` of `A`, the same for equal terms. -/
theorem FieldsRel.cons_isPer {F : TermRel} {G : Term 0 [] → FieldsRel} (hF : IsPer F)
    (hG : ∀ a, F a a → IsPer (G a))
    (hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us) :
    IsPer (FieldsRel.cons F G) where
  symm {ts us} h := match ts, us, h with
    | .cons t ts, .cons u us, ⟨h₁, h₂⟩ =>
      ⟨hF.symm h₁, (hG u (hF.trans (hF.symm h₁) h₁)).symm ((hresp t u h₁ ts us).1 h₂)⟩
  trans {ts us ws} h h' := match ts, us, ws, h, h' with
    | .cons t _ts, .cons u us, .cons _w ws, ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩ =>
      ⟨hF.trans h₁ h₁', (hG t (hF.trans h₁ (hF.symm h₁))).trans h₂ ((hresp t u h₁ us ws).2 h₂')⟩

/-- The equalities of the terms of the fields of two telescopes `x : A, Θ` relate the same terms,
when those of `A` do, and those of `Θ[a / x]` do for each term `a` of `A`. -/
theorem FieldsRel.cons_congr {F F' : TermRel} {G G' : Term 0 [] → FieldsRel} (hFp : IsPer F)
    (hF : ∀ t u, F t u ↔ F' t u) (hG : ∀ a, F a a → ∀ ts us, G a ts us ↔ G' a ts us) :
    ∀ ts us, FieldsRel.cons F G ts us ↔ FieldsRel.cons F' G' ts us
  | .nil, _ => .rfl
  | .cons _ _, .nil => .rfl
  | .cons t ts, .cons u us =>
    ⟨fun ⟨h₁, h₂⟩ => ⟨(hF t u).1 h₁, (hG t (hFp.trans h₁ (hFp.symm h₁)) ts us).1 h₂⟩,
      fun ⟨h₁, h₂⟩ =>
        have h₁' := (hF t u).2 h₁
        ⟨h₁', (hG t (hFp.trans h₁' (hFp.symm h₁')) ts us).2 h₂⟩⟩

/-- A closed term is a constructor of one declared type, one name, and one list of fields. -/
theorem Term.IsCtor.inj {D D' c c' : Name} {ts ts' : Terms 0 []} {v : Term 0 []}
    (h : v.IsCtor D c ts) (h' : v.IsCtor D' c' ts') : D = D' ∧ c = c' ∧ ts = ts' := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  obtain ⟨_, _, _, _, _, h'⟩ := h'
  cases h'
  exact ⟨rfl, rfl, rfl⟩

/-- `(eq_c)` is a partial equivalence relation when the equalities of the terms of the fields of the
constructors are, which have distinct names. -/
theorem DataType.ctorRel_isPer {j g k : Nat} {Δ : Scope} {D : Name} {T : DataType j g k Δ}
    {S : Constructor j g k Δ → FieldsRel} (hc : (T.constructors.map (·.name)).Nodup)
    (hS : ∀ c ∈ T.constructors, IsPer (S c)) : IsPer (T.ctorRel D S) where
  symm := fun ⟨c, hcm, ts, us, hv, hw, h⟩ => ⟨c, hcm, us, ts, hw, hv, (hS c hcm).symm h⟩
  trans := fun ⟨c, hcm, ts, _, hv, hw, h⟩ ⟨_, hcm', _, vs, hw', hx, h'⟩ => by
    obtain ⟨-, hn, rfl⟩ := hw.inj hw'
    cases List.eq_of_nodup_map hc hcm hcm' hn
    exact ⟨c, hcm, ts, vs, hv, hx, (hS c hcm).trans h h'⟩

/-- `(eq_c)` relates the same terms for equalities of the terms of the fields that relate the same
terms. -/
theorem DataType.ctorRel_congr {j g k : Nat} {Δ : Scope} {D : Name} {T : DataType j g k Δ}
    {S S' : Constructor j g k Δ → FieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ ts us, S c ts us ↔ S' c ts us) :
    ∀ v w, T.ctorRel D S v w ↔ T.ctorRel D S' v w :=
  fun _ _ => ⟨fun ⟨c, hcm, ts, us, hv, hw, hS⟩ => ⟨c, hcm, ts, us, hv, hw, (h c hcm ts us).1 hS⟩,
    fun ⟨c, hcm, ts, us, hv, hw, hS⟩ => ⟨c, hcm, ts, us, hv, hw, (h c hcm ts us).2 hS⟩⟩

/-- `(true_D)` is the same for equalities of the terms of the fields that relate the same terms. -/
theorem DataType.truth_congr {j g k : Nat} {Δ : Scope} {T : DataType j g k Δ}
    {S S' : Constructor j g k Δ → FieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ ts us, S c ts us ↔ S' c ts us) : T.truth S ↔ T.truth S' :=
  ⟨fun ⟨c, hcm, ts, hS⟩ => ⟨c, hcm, ts, (h c hcm ts ts).1 hS⟩,
    fun ⟨c, hcm, ts, hS⟩ => ⟨c, hcm, ts, (h c hcm ts ts).2 hS⟩⟩

/-- The equalities of the terms of the fields of two telescopes `x : A, Θ` relate the terms that the
first one relates, when those of `A` do, and those of `Θ[a / x]` do for the terms `a` of `A`. -/
theorem FieldsRel.cons_mono {F₁ F₂ : TermRel} {G₁ G₂ : Term 0 [] → FieldsRel}
    (hF : ∀ t u, F₁ t u → F₂ t u) (hG : ∀ t u, F₁ t u → ∀ ts us, G₁ t ts us → G₂ t ts us) :
    ∀ ts us, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ ts us
  | .nil, _, h => h.elim
  | .cons _ _, .nil, h => h.elim
  | .cons t ts, .cons u us, ⟨h₁, h₂⟩ => ⟨hF t u h₁, hG t u h₁ ts us h₂⟩

/-- The equality of the terms of the fields of a telescope `x : A, Θ` relates in the other order the
terms that the equality of another one relates, when those of `A` do, and those of `Θ[a / x]` do. -/
theorem FieldsRel.cons_symm {F₁ F₂ : TermRel} {G₁ G₂ : Term 0 [] → FieldsRel}
    (hF : ∀ t u, F₁ t u → F₂ u t) (hG : ∀ t u, F₁ t u → ∀ ts us, G₁ t ts us → G₂ u us ts) :
    ∀ ts us, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ us ts
  | .nil, _, h => h.elim
  | .cons _ _, .nil, h => h.elim
  | .cons t ts, .cons u us, ⟨h₁, h₂⟩ => ⟨hF t u h₁, hG t u h₁ ts us h₂⟩

/-- The equality of the terms of the fields of a telescope `x : A, Θ` relates the terms that two
others relate in a chain, when those of `A` do, and those of `Θ[a / x]` do. -/
theorem FieldsRel.cons_trans {F₁ F₂ F₃ : TermRel} {G₁ G₂ G₃ : Term 0 [] → FieldsRel}
    (hF : ∀ t u v, F₁ t u → F₂ u v → F₃ t v)
    (hG : ∀ t u v, F₁ t u → F₂ u v → ∀ ts us vs, G₁ t ts us → G₂ u us vs → G₃ t ts vs) :
    ∀ ts us vs, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ us vs →
      FieldsRel.cons F₃ G₃ ts vs
  | .nil, _, _, h, _ => h.elim
  | .cons _ _, .nil, _, h, _ => h.elim
  | .cons _ _, .cons _ _, .nil, _, h => h.elim
  | .cons t ts, .cons u us, .cons v vs, ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩ =>
    ⟨hF t u v h₁ h₁', hG t u v h₁ h₁' ts us vs h₂ h₂'⟩

/-- `eq⇓(R₂)` relates the terms that `eq⇓(R₁)` relates, when `R₂` relates the canonical terms that
`R₁` relates. -/
theorem TermRel.computed_mono {sig : Signature} {ι : Interpretation} {R₁ R₂ : TermRel}
    (h : ∀ v w, R₁ v w → R₂ v w) {t u : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι t u :=
  fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, h v w hvw⟩

/-- `eq⇓(R₂)` relates in the other order the terms that `eq⇓(R₁)` relates, when `R₂` relates so the
canonical terms that `R₁` relates. -/
theorem TermRel.computed_symm {sig : Signature} {ι : Interpretation} {R₁ R₂ : TermRel}
    (h : ∀ v w, R₁ v w → R₂ w v) {t u : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι u t :=
  fun ⟨v, w, ht, hu, hvw⟩ => ⟨w, v, hu, ht, h v w hvw⟩

/-- `eq⇓(R₃)` relates the terms that `eq⇓(R₁)` and `eq⇓(R₂)` relate in a chain, when `R₃` relates so
the canonical terms, in a signature whose names are distinct. -/
theorem TermRel.computed_trans {sig : Signature} {ι : Interpretation} {R₁ R₂ R₃ : TermRel}
    (hd : sig.Distinct) (h : ∀ v w x, R₁ v w → R₂ w x → R₃ v x) {t u w : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι u w → R₃.computed sig ι t w :=
  fun ⟨v, _, ht, hu, h₁⟩ ⟨_, x, hu', hw, h₂⟩ => by
    cases Computesι.det hd hu hu'
    exact ⟨v, x, ht, hw, h _ _ _ h₁ h₂⟩

/-- The images of an option by two functions are related when the images of each value are. -/
theorem Option.rel_map {α β γ : Type} {r : β → γ → Prop} {f : α → β} {g : α → γ}
    (h : ∀ x, r (f x) (g x)) : (o : Option α) → Option.Rel r (o.map f) (o.map g)
  | none => .none
  | some x => .some (h x)

/-- The images of an option by three functions are all none, or related when the images of each
value are. -/
theorem Option.rel_map₃ {α β : Type} {r : β → β → β → Prop} {f g h : α → β}
    (hr : ∀ x, r (f x) (g x) (h x)) (o : Option α) :
    (o.map f = none ∧ o.map g = none ∧ o.map h = none) ∨
      ∃ x y z, o.map f = some x ∧ o.map g = some y ∧ o.map h = some z ∧ r x y z :=
  match o with
  | none => .inl ⟨rfl, rfl, rfl⟩
  | some x => .inr ⟨_, _, _, rfl, rfl, rfl, hr x⟩

/-- A telescope that is not the fields of a constructor relates its recursive fields as any
other. -/
theorem TelRel.none_rel {α β : Type} {r : α → β → Prop} (i : Nat) :
    Option.Rel r ((fun _ => none : Nat → Option α) i) ((fun _ => none : Nat → Option β) i) :=
  .none

/-- The same values at the recursive fields are related, when each one is related to itself. -/
theorem Option.rel_refl {α : Type} {r : α → α → Prop} (h : ∀ x, r x x) :
    (o : Option α) → Option.Rel r o o
  | none => .none
  | some x => .some (h x)

/-! ### Least Fixed Points

The equality `(eq_μ)` of the terms of the instances of a block is the least relation closed under
the clauses of its constructors, which every relation closed under them contains; it is closed
under them itself, and is a partial equivalence relation, when the equality of the terms of the
fields grows with the relations of the recursive fields, and inverts and composes them, by the
strict positivity of their occurrences. -/

section LeastFixedPoints

variable {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
  {S : (Name → TermRel) → Constructor j g k Δ → FieldsRel}

/-- `(eq_μ)` is closed under the clauses of the constructors, when the equality of the terms of the
fields grows with the relations of the recursive fields. -/
theorem DataType.blockRel_closed
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    {T : DataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : T.ctorRel T.name (S (DataType.blockRel Ts S)) v w) :
    DataType.blockRel Ts S T.name v w :=
  fun X hX =>
    have ⟨c, hc, ts, us, hv, hw, hs⟩ := h
    hX T hT v w ⟨c, hc, ts, us, hv, hw, hmono _ X (fun _ _ _ h => h X hX) T hT c hc ts us hs⟩

/-- `(eq_μ)` relates the constructors that the clauses relate only, when the equality of the terms
of the fields grows with the relations of the recursive fields. -/
theorem DataType.blockRel_inv
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    {D : Name} {v w : Term 0 []} (h : DataType.blockRel Ts S D v w) :
    ∃ T ∈ Ts, T.name = D ∧ T.ctorRel T.name (S (DataType.blockRel Ts S)) v w :=
  h (fun D v w => ∃ T ∈ Ts, T.name = D ∧ T.ctorRel T.name (S (DataType.blockRel Ts S)) v w)
    fun T hT _ _ ⟨c, hc, ts, us, hv, hw, hs⟩ =>
      ⟨T, hT, rfl, c, hc, ts, us, hv, hw,
        hmono _ _ (fun _ _ _ ⟨_, hT', hD, hr⟩ => hD ▸ DataType.blockRel_closed hmono hT' hr)
          T hT c hc ts us hs⟩

/-- `(eq_μ)` is a partial equivalence relation, when the equality of the terms of the fields grows
with the relations of the recursive fields, and inverts and composes them, and when the names of the
types and of the constructors of each type are distinct. -/
theorem DataType.blockRel_isPer
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    (hsymm : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D w v) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c us ts)
    (htrans : ∀ X Y Z : Name → TermRel, (∀ D u v w, X D u v → Y D v w → Z D u w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us vs, S X c ts us → S Y c us vs → S Z c ts vs)
    (hn : (Ts.map (·.name)).Nodup) (hc : ∀ T ∈ Ts, (T.constructors.map (·.name)).Nodup)
    (D : Name) : IsPer (DataType.blockRel Ts S D) where
  symm h := h (fun D v w => DataType.blockRel Ts S D w v) fun T hT v w ⟨c, hcm, ts, us, hv, hw, hs⟩ =>
    DataType.blockRel_closed hmono hT
      ⟨c, hcm, us, ts, hw, hv, hsymm _ _ (fun _ _ _ h => h) T hT c hcm ts us hs⟩
  trans h₁ h₂ := h₁ (fun D u v => ∀ w, DataType.blockRel Ts S D v w → DataType.blockRel Ts S D u w)
    (fun T hT u v ⟨c, hcm, ts, us, hu, hv, hs⟩ w hw => by
      obtain ⟨T', hT', hn', c', hcm', us', vs, hv', hw', hs'⟩ := DataType.blockRel_inv hmono hw
      cases List.eq_of_nodup_map hn hT' hT hn'
      obtain ⟨-, hcn, rfl⟩ := hv.inj hv'
      cases List.eq_of_nodup_map (hc T hT) hcm hcm' hcn
      exact DataType.blockRel_closed hmono hT
        ⟨c, hcm, ts, vs, hu, hw', htrans _ _ _ (fun _ _ _ _ h₁ h₂ => h₁ _ h₂) T hT c hcm ts us vs hs hs'⟩)
    _ h₂

/-- `(true_μ)` is closed under the clauses of the constructors, when the equality of the terms of
the fields grows with the truths of the recursive fields. -/
theorem DataType.blockTruth_closed {S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us,
      S' B c ts us → S' B' c ts us)
    {T : DataType j g k Δ} (hT : T ∈ Ts) (h : T.truth (S' (DataType.blockTruth Ts S'))) :
    DataType.blockTruth Ts S' T.name :=
  fun B hB =>
    have ⟨c, hc, ts, hs⟩ := h
    hB T hT ⟨c, hc, ts, hmono _ B (fun _ h => h B hB) T hT c hc ts ts hs⟩

/-- `(true_μ)` holds by the clause of a constructor only, when the equality of the terms of the
fields grows with the truths of the recursive fields. -/
theorem DataType.blockTruth_inv {S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us,
      S' B c ts us → S' B' c ts us)
    {D : Name} (h : DataType.blockTruth Ts S' D) :
    ∃ T ∈ Ts, T.name = D ∧ T.truth (S' (DataType.blockTruth Ts S')) :=
  h (fun D => ∃ T ∈ Ts, T.name = D ∧ T.truth (S' (DataType.blockTruth Ts S')))
    fun T hT ⟨c, hc, ts, hs⟩ =>
      ⟨T, hT, rfl, c, hc, ts, hmono _ _ (fun _ ⟨_, hT', hD, ht⟩ => hD ▸
        DataType.blockTruth_closed hmono hT' ht) T hT c hc ts ts hs⟩

end LeastFixedPoints

/-- `(eq_μ)` relates the same terms for equalities of the terms of the fields that relate the same
terms. -/
theorem DataType.blockRel_congr {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
    {S S' : (Name → TermRel) → Constructor j g k Δ → FieldsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us ↔ S' X c ts us) (D : Name) :
    ∀ v w, DataType.blockRel Ts S D v w ↔ DataType.blockRel Ts S' D v w :=
  fun _ _ => ⟨fun hr X hX => hr X fun T hT v w hc =>
      hX T hT v w ((DataType.ctorRel_congr (h X T hT) v w).1 hc),
    fun hr X hX => hr X fun T hT v w hc => hX T hT v w ((DataType.ctorRel_congr (h X T hT) v w).2 hc)⟩

/-- `(true_μ)` is the same for equalities of the terms of the fields that relate the same terms. -/
theorem DataType.blockTruth_congr {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
    {S S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (h : ∀ B, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us ↔ S' B c ts us) (D : Name) :
    DataType.blockTruth Ts S D ↔ DataType.blockTruth Ts S' D :=
  ⟨fun hr B hB => hr B fun T hT hc => hB T hT ((DataType.truth_congr (h B T hT)).1 hc),
    fun hr B hB => hr B fun T hT hc => hB T hT ((DataType.truth_congr (h B T hT)).2 hc)⟩

/-- A closed term has the observations of one corecursor at most. -/
theorem Term.CorecObservations.unique {D D' : Name} {v : Term 0 []} {o o' : Observations}
    (h : v.CorecObservations D o) (h' : v.CorecObservations D' o') : o = o' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, h', rfl⟩ := h'
  cases h'
  rfl

/-- The equality of the abstractions for a destructor is a partial equivalence relation, when the
equality of its arguments is one, and so is the equality of the terms of its result at equal
arguments, the same for equal arguments. -/
theorem AbstractionRel.isPer {ps : List Parameter} {SΘ : FieldsRel} {F : Terms 0 [] → TermRel}
    (hS : IsPer SΘ) (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → IsPer (F ts.terms))
    (hresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u) :
    IsPer (AbstractionRel (ps := ps) SΘ F) where
  symm {_ _} h ts us hts :=
    have hst := hS.symm hts
    (hresp _ _ hst _ _).1 ((hF us (hS.trans hst hts)).symm (h us ts hst))
  trans {_ _ _} h h' ts us hts :=
    have huu := hS.trans (hS.symm hts) hts
    (hF ts (hS.trans hts (hS.symm hts))).trans (h ts us hts) ((hresp _ _ hts _ _).2 (h' us us huu))

/-- The equalities of the abstractions for a destructor relate the same abstractions, when the
equalities of its arguments relate the same arguments, and those of its result the same terms. -/
theorem AbstractionRel.congr {ps : List Parameter} {SΘ SΘ' : FieldsRel} {F F' : Terms 0 [] → TermRel}
    (hSp : IsPer SΘ) (hS : ∀ ts us, SΘ ts us ↔ SΘ' ts us)
    (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u, F ts.terms t u ↔ F' ts.terms t u) :
    ∀ f₁ f₂, AbstractionRel (ps := ps) SΘ F f₁ f₂ ↔ AbstractionRel SΘ' F' f₁ f₂ :=
  fun _ _ =>
    ⟨fun h ts us hts =>
      have hts' := (hS _ _).2 hts
      (hF ts (hSp.trans hts' (hSp.symm hts')) _ _).1 (h ts us hts'),
    fun h ts us hts => (hF ts (hSp.trans hts (hSp.symm hts)) _ _).2 (h ts us ((hS _ _).1 hts))⟩

/-- The equality of the abstractions for a destructor `d` followed by the destructors after it is a
partial equivalence relation, when the equality `E` of the abstractions for `d` is one, and so is
the equality `G f` of the destructors after it for each abstraction `f`, the same for equal
abstractions. -/
theorem ObsRel.cons_isPer {d : Name} {ps : List Parameter}
    {E : Term 0 (Scope.extend [] ps.length) → Term 0 (Scope.extend [] ps.length) → Prop}
    {G : Term 0 (Scope.extend [] ps.length) → ObsRel} (hE : IsPer E) (hG : ∀ f, E f f → IsPer (G f))
    (hresp : ∀ f₁ f₂, E f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂) :
    IsPer (fun o₁ o₂ : Observations => E (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂) where
  symm := fun ⟨h₁, h₂⟩ =>
    ⟨hE.symm h₁, (hG _ (hE.trans (hE.symm h₁) h₁)).symm ((hresp _ _ h₁ _ _).1 h₂)⟩
  trans := fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨hE.trans h₁ h₁', (hG _ (hE.trans h₁ (hE.symm h₁))).trans h₂ ((hresp _ _ h₁ _ _).2 h₂')⟩

/-- The equalities of the abstractions for a destructor `d` followed by the destructors after it
relate the same abstractions, when those for `d` do, and those of the destructors after it do for
each abstraction for `d`. -/
theorem ObsRel.cons_congr {d : Name} {ps : List Parameter}
    {E E' : Term 0 (Scope.extend [] ps.length) → Term 0 (Scope.extend [] ps.length) → Prop}
    {G G' : Term 0 (Scope.extend [] ps.length) → ObsRel} (hEp : IsPer E)
    (hE : ∀ f₁ f₂, E f₁ f₂ ↔ E' f₁ f₂) (hG : ∀ f, E f f → ∀ o₁ o₂, G f o₁ o₂ ↔ G' f o₁ o₂) :
    ∀ o₁ o₂ : Observations, (E (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂) ↔
      (E' (o₁ d ps) (o₂ d ps) ∧ G' (o₁ d ps) o₁ o₂) :=
  fun _ _ =>
    ⟨fun ⟨h₁, h₂⟩ => ⟨(hE _ _).1 h₁, (hG _ (hEp.trans h₁ (hEp.symm h₁)) _ _).1 h₂⟩,
      fun ⟨h₁, h₂⟩ =>
        have h₁' := (hE _ _).2 h₁
        ⟨h₁', (hG _ (hEp.trans h₁' (hEp.symm h₁')) _ _).2 h₂⟩⟩

/-- `(eq_d)` relates the terms that it relates for an equality of the destructors that relates
fewer abstractions. -/
theorem corecRel_mono {D : Name} {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ → S' o₁ o₂) :
    ∀ v w, corecRel D S v w → corecRel D S' v w :=
  fun _ _ ⟨o₁, o₂, hv, hw, hS⟩ => ⟨o₁, o₂, hv, hw, h _ _ hS⟩

/-- `(true_d)` holds when it holds for an equality of the destructors that relates fewer
abstractions. -/
theorem ObsRel.truth_mono {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ → S' o₁ o₂) :
    S.truth → S'.truth :=
  fun ⟨o, ho⟩ => ⟨o, h o o ho⟩

/-! ### Greatest Fixed Points

The equality `(eq_ν)` of the terms of the instances of a block of codata types is the greatest
relation consistent with the clauses of its destructors, which contains every relation consistent
with them; it is consistent with them itself, closed under them, and a partial equivalence
relation, when the equality of the destructors grows with the relations of the recursive
destructors, and inverts and composes them, by the strict positivity of their occurrences. -/

section GreatestFixedPoints

variable {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
  {S : (Name → TermRel) → CodataType j g k Δ → ObsRel}

/-- `(eq_ν)` is consistent with the clauses of the destructors, when the equality of the destructors
grows with the relations of the recursive destructors. -/
theorem CodataType.blockRel_unfold
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₁ o₂)
    {T : CodataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : CodataType.blockRel Ts S T.name v w) :
    corecRel T.name (S (CodataType.blockRel Ts S) T) v w :=
  have ⟨X, hX, hv⟩ := h
  corecRel_mono (hmono X _ (fun _ _ _ h => ⟨X, hX, h⟩) T hT) _ _ (hX T hT v w hv)

/-- `(eq_ν)` is closed under the clauses of the destructors, when the equality of the destructors
grows with the relations of the recursive destructors, and when the names of the types are
distinct. -/
theorem CodataType.blockRel_fold
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₁ o₂)
    (hn : (Ts.map (·.name)).Nodup) {T : CodataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : corecRel T.name (S (CodataType.blockRel Ts S) T) v w) :
    CodataType.blockRel Ts S T.name v w :=
  ⟨fun D a b => CodataType.blockRel Ts S D a b ∨
      (D = T.name ∧ corecRel T.name (S (CodataType.blockRel Ts S) T) a b),
    fun T' hT' a b hab => by
      rcases hab with hab | ⟨hD, hab⟩
      · exact corecRel_mono (hmono _ _ (fun _ _ _ h => .inl h) T' hT') _ _
          (CodataType.blockRel_unfold hmono hT' hab)
      · cases List.eq_of_nodup_map hn hT hT' hD.symm
        exact corecRel_mono (hmono _ _ (fun _ _ _ h => .inl h) T hT) _ _ hab,
    .inr ⟨rfl, h⟩⟩

/-- `(eq_ν)` is a partial equivalence relation, when the equality of the destructors inverts and
composes the relations of the recursive destructors. -/
theorem CodataType.blockRel_isPer
    (hsymm : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D w v) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₂ o₁)
    (htrans : ∀ X Y Z : Name → TermRel, (∀ D u v w, X D u v → Y D v w → Z D u w) → ∀ T ∈ Ts,
      ∀ o₁ o₂ o₃, S X T o₁ o₂ → S Y T o₂ o₃ → S Z T o₁ o₃)
    (D : Name) : IsPer (CodataType.blockRel Ts S D) where
  symm := fun ⟨X, hX, h⟩ => ⟨fun D v w => X D w v, fun T hT v w hvw =>
      have ⟨o₁, o₂, hw, hv, hs⟩ := hX T hT w v hvw
      ⟨o₂, o₁, hv, hw, hsymm X _ (fun _ _ _ h => h) T hT o₁ o₂ hs⟩, h⟩
  trans := fun ⟨X, hX, h⟩ ⟨Y, hY, h'⟩ => ⟨fun D u w => ∃ v, X D u v ∧ Y D v w,
      fun T hT u w ⟨v, huv, hvw⟩ => by
        obtain ⟨o₁, o₂, hu, hv, hs⟩ := hX T hT u v huv
        obtain ⟨o₂', o₃, hv', hw, hs'⟩ := hY T hT v w hvw
        rw [← hv.unique hv'] at hs'
        exact ⟨o₁, o₃, hu, hw, htrans X Y _ (fun _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩) T hT o₁ o₂ o₃ hs hs'⟩,
      _, h, h'⟩

/-- `(true_ν)` is consistent with the clauses of the destructors, when the equality of the
destructors grows with the truths of the recursive destructors. -/
theorem CodataType.blockTruth_unfold {S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S' B T o₁ o₂ → S' B' T o₁ o₂)
    {T : CodataType j g k Δ} (hT : T ∈ Ts) (h : CodataType.blockTruth Ts S' T.name) :
    (S' (CodataType.blockTruth Ts S') T).truth :=
  have ⟨B, hB, hb⟩ := h
  ObsRel.truth_mono (hmono B _ (fun _ h => ⟨B, hB, h⟩) T hT) (hB T hT hb)

/-- `(true_ν)` holds by the clause of the destructors of its type, when the equality of the
destructors grows with the truths of the recursive destructors, and when the names of the types are
distinct. -/
theorem CodataType.blockTruth_fold {S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S' B T o₁ o₂ → S' B' T o₁ o₂)
    (hn : (Ts.map (·.name)).Nodup) {T : CodataType j g k Δ} (hT : T ∈ Ts)
    (h : (S' (CodataType.blockTruth Ts S') T).truth) : CodataType.blockTruth Ts S' T.name :=
  ⟨fun D => CodataType.blockTruth Ts S' D ∨ (D = T.name ∧ (S' (CodataType.blockTruth Ts S') T).truth),
    fun T' hT' hb => by
      rcases hb with hb | ⟨hD, hb⟩
      · exact ObsRel.truth_mono (hmono _ _ (fun _ h => .inl h) T' hT')
          (CodataType.blockTruth_unfold hmono hT' hb)
      · cases List.eq_of_nodup_map hn hT hT' hD.symm
        exact ObsRel.truth_mono (hmono _ _ (fun _ h => .inl h) T hT) hb,
    .inr ⟨rfl, h⟩⟩

end GreatestFixedPoints

/-- `(eq_ν)` relates the same terms for equalities of the destructors that relate the same
abstractions. -/
theorem CodataType.blockRel_congr {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
    {S S' : (Name → TermRel) → CodataType j g k Δ → ObsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ o₁ o₂, S X T o₁ o₂ ↔ S' X T o₁ o₂) (D : Name) :
    ∀ v w, CodataType.blockRel Ts S D v w ↔ CodataType.blockRel Ts S' D v w :=
  fun _ _ => ⟨fun ⟨X, hX, hv⟩ => ⟨X, fun T hT v w hx =>
      corecRel_mono (fun o₁ o₂ => (h X T hT o₁ o₂).1) _ _ (hX T hT v w hx), hv⟩,
    fun ⟨X, hX, hv⟩ => ⟨X, fun T hT v w hx =>
      corecRel_mono (fun o₁ o₂ => (h X T hT o₁ o₂).2) _ _ (hX T hT v w hx), hv⟩⟩

/-- `(true_ν)` is the same for equalities of the destructors that relate the same abstractions. -/
theorem CodataType.blockTruth_congr {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
    {S S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (h : ∀ B, ∀ T ∈ Ts, ∀ o₁ o₂, S B T o₁ o₂ ↔ S' B T o₁ o₂) (D : Name) :
    CodataType.blockTruth Ts S D ↔ CodataType.blockTruth Ts S' D :=
  ⟨fun ⟨B, hB, hb⟩ => ⟨B, fun T hT h' => ObsRel.truth_mono (fun o₁ o₂ => (h B T hT o₁ o₂).1)
      (hB T hT h'), hb⟩,
    fun ⟨B, hB, hb⟩ => ⟨B, fun T hT h' => ObsRel.truth_mono (fun o₁ o₂ => (h B T hT o₁ o₂).2)
      (hB T hT h'), hb⟩⟩

/-! ### A Type Has One Level and One Sort -/

/-- Two instances of a declared type of a signature whose names are distinct, given by a data type
and by a codata type, do not exist. -/
theorem Signature.Distinct.inst_data_codata {sig : Signature} (hd : sig.Distinct)
    {decl₁ decl₂ : TypeDeclaration} {D₁ D₂ : Name}
    {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope} {qs₁ qs₂ : List Quality}
    {ls₁ ls₂ : List (Level 0)} {ps₁ ps₂ : List Grade} {as₁ : InstanceArgs 0 [] decl₁.scope}
    {as₂ : InstanceArgs 0 [] decl₂.scope} (h₁ : sig.HasDataType D₁ decl₁ T₁)
    (h₂ : sig.HasCodataType D₂ decl₂ T₂)
    (hv : Term.inst D₁ qs₁ ls₁ ps₁ as₁ = Term.inst D₂ qs₂ ls₂ ps₂ as₂) : False := by
  obtain ⟨-, hD, -⟩ := Term.inst.inj hv
  subst hD
  exact hd.not_hasDataType_hasCodataType h₁ h₂

/-- A type of a universe has one level, in a signature whose names are distinct. -/
theorem UnivRel.level {sig : Signature} {ι : Interpretation} {n m : Nat} {below₁ : LevelRel.Below n}
    {below₂ : LevelRel.Below m} {v : Term 0 []} {R R' : TermRel} (hd : sig.Distinct)
    (h : UnivRel sig ι n below₁ v R) (h' : UnivRel sig ι m below₂ v R') : n = m := by
  cases h with
  | univ hl hk => cases h' with
    | univ hl' hk' => omega
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop hl hk => cases h' with
    | prop hl' hk' => omega
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | data h _ _ _ hv _ hn => cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact hn.symm.trans hn'
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | codata h _ _ _ hv _ hn => cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact hn.symm.trans hn'

/-- A type of a universe is not a proposition, in a signature whose names are distinct. -/
theorem UnivRel.not_prop {sig : Signature} {ι : Interpretation} {n m : Nat}
    {below₁ : LevelRel.Below n} {below₂ : LevelRel.Below m} {v : Term 0 []} {R : TermRel} {b : Prop}
    (hd : sig.Distinct) (h : UnivRel sig ι n below₁ v R) (h' : PropRel sig ι m below₂ v b) :
    False := by
  cases h' with
  | data h' _ _ _ hv' hs' =>
    subst hv'
    cases h with
    | data h _ _ _ hv hs =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata h _ _ _ hv => exact hd.inst_data_codata h' h hv
  | codata h' _ _ _ hv' hs' =>
    subst hv'
    cases h with
    | data h _ _ _ hv => exact hd.inst_data_codata h h' hv.symm
    | codata h _ _ _ hv hs =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hs.symm.trans hs'

/-- A proposition has one level, in a signature whose names are distinct. -/
theorem PropRel.level {sig : Signature} {ι : Interpretation} {n m : Nat} {below₁ : LevelRel.Below n}
    {below₂ : LevelRel.Below m} {v : Term 0 []} {b b' : Prop} (hd : sig.Distinct)
    (h : PropRel sig ι n below₁ v b) (h' : PropRel sig ι m below₂ v b') : n = m := by
  cases h with
  | data h _ _ _ hv _ hn => cases h' with
    | data h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact hn.symm.trans hn'
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | codata h _ _ _ hv _ hn => cases h' with
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact hn.symm.trans hn'

/-! ### The Relations of a Level

The partial equivalence and the uniqueness are proved together, since the equality `(eq_μ)` of a
block is a partial equivalence relation by the transfer of the equalities of the fields between
relations of the recursive fields, which identifies the equalities of the fields that are not
recursive by their uniqueness. -/

mutual

/-- The equality of the terms of a type of `U_n` is a partial equivalence relation, if the relations
of the levels below `n` are partial equivalence relations. -/
theorem UnivRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {R : TermRel} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R → IsPer R
  | .univ (k := k) _ hk =>
    have hL := ih k (hk ▸ Nat.lt_succ_self k)
    ⟨fun ⟨R', h₁, h₂⟩ => ⟨R', h₂, h₁⟩,
      fun ⟨R₁, h₁, h₂⟩ ⟨_, h₂', h₃⟩ => ⟨R₁, h₁, hL.univ_eq h₂' h₂ ▸ h₃⟩⟩
  | .prop (k := k) _ hk =>
    have hL := ih k (hk ▸ Nat.lt_succ_self k)
    ⟨fun ⟨b₁, b₂, h₁, h₂, hb⟩ => ⟨b₂, b₁, h₂, h₁, hb.symm⟩,
      fun ⟨b₁, _, h₁, h₂, hb⟩ ⟨_, b₃, h₂', h₃, hb'⟩ =>
        ⟨b₁, b₃, h₁, h₃, hb.trans ((hL.prop_unique h₂ h₂').trans hb')⟩⟩
  | .data h _ _ _ _ _ _ _ hS =>
    DataType.blockRel_isPer
      (fun X Y hXY T hT c hc ts us hs => TelRel.mono hd ih (hS X T hT c hc) _ _ _ (hS Y T hT c hc)
        (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _) ts us hs)
      (fun X Y hXY T hT c hc ts us hs => TelRel.symm_of hd ih (hS X T hT c hc) _ _ _
        (hS Y T hT c hc) (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_symm (hXY D)) _)
        ts us hs)
      (fun X Y Z hXYZ T hT c hc ts us vs hs hs' => TelRel.trans_of hd ih (hS X T hT c hc) _ _ _
        (hS Y T hT c hc) _ _ _ (hS Z T hT c hc)
        (fun _ => Option.rel_map₃
          (r := fun (x y z : TermRel) => ∀ t u w, x t u → y u w → z t w)
          (f := fun D => (X D).computed sig ι) (g := fun D => (Y D).computed sig ι)
          (h := fun D => (Z D).computed sig ι)
          (fun D _ _ _ => TermRel.computed_trans hd (hXYZ D)) _)
        ts us vs hs hs')
      (TypeDeclaration.dataTypes_nodup (hd.nodup h.1))
      (fun _ hT => hd.constructors_nodup ⟨h.1, hT, rfl⟩) _
  | .codata _ _ _ _ _ _ _ _ hS =>
    CodataType.blockRel_isPer
      (fun X Y hXY T hT o₁ o₂ hs => DesRel.symm_of hd ih (hS X T hT) _ _ _ (hS Y T hT)
        (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_symm (hXY D)) _) o₁ o₂ hs)
      (fun X Y Z hXYZ T hT o₁ o₂ o₃ hs hs' => DesRel.trans_of hd ih (hS X T hT) _ _ _ (hS Y T hT)
        _ _ _ (hS Z T hT)
        (fun _ => Option.rel_map₃
          (r := fun (x y z : TermRel) => ∀ t u w, x t u → y u w → z t w)
          (f := fun D => (X D).computed sig ι) (g := fun D => (Y D).computed sig ι)
          (h := fun D => (Z D).computed sig ι)
          (fun D _ _ _ => TermRel.computed_trans hd (hXYZ D)) _)
        o₁ o₂ o₃ hs hs') _
termination_by structural h => h

/-- The equality of the abstractions for destructors relates in the other order the abstractions
that the equality of the same destructors relates, at relations of the recursive destructors that do
so. -/
theorem DesRel.symm_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y u t) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ → S₂ o₂ o₁
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' hresp' _ =>
      have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
        have hf := hEp.trans h₁ (hEp.symm h₁)
        ⟨(hEE _ _).1 (hEp.symm h₁), (hresp' _ _ ((hEE _ _).1 h₁) _ _).1
          (DesRel.symm_of hd ih (hG _ hf) _ _ _ (hG' _ ((hEE _ _).1 hf)) (fun i => hR (i + 1))
            _ _ h₂)⟩
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
          ⟨fun ts us hts => hr _ _ (h₁ us ts (hSΘp.symm ((hSS _ _).2 hts))),
            DesRel.symm_of hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
              (fun i => hR (i + 1)) _ _ h₂⟩
termination_by structural h _ _ _ _ _ => h

/-- The equality of the abstractions for destructors relates the abstractions that two equalities of
the same destructors relate in a chain, at relations of the recursive destructors that do so. -/
theorem DesRel.trans_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
      ∀ (s₃ : Quality) (rs₃ : Nat → Option TermRel) (S₃ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₃ rs₃ ds @θ S₃ →
        (∀ i, (rs₁ i = none ∧ rs₂ i = none ∧ rs₃ i = none) ∨
          ∃ x y z, rs₁ i = some x ∧ rs₂ i = some y ∧ rs₃ i = some z ∧
            ∀ t u w, x t u → y u w → z t w) →
        ∀ o₁ o₂ o₃, S₁ o₁ o₂ → S₂ o₂ o₃ → S₃ o₁ o₃
  | .nil, _, _, _, h', _, _, _, h'', _ => by
    cases h'; cases h''; exact fun _ _ _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', _, _, _, h'', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' hresp' _ =>
      cases h'' with
      | cons hΘ'' F'' _ hF'' _ _ hG'' _ _ =>
        have hSS' := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        have hSS'' := TelRel.congr hd ih hΘ _ _ _ hΘ'' TelRel.none_rel
        have hFF' : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
            F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
          have ⟨_, hv⟩ := hB ts hts
          FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS' _ _).1 hts) _ hv)
        have hFF'' : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
            F ts.terms t u ↔ F'' ts.terms t u := fun ts hts =>
          have ⟨_, hv⟩ := hB ts hts
          FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF'' ts ((hSS'' _ _).1 hts) _ hv)
        have hEE' := AbstractionRel.congr hSΘp hSS' hFF'
        have hEE'' := AbstractionRel.congr hSΘp hSS'' hFF''
        exact fun o₁ o₂ o₃ ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
          have hf := hEp.trans h₁ (hEp.symm h₁)
          ⟨(hEE'' _ _).1 (hEp.trans h₁ ((hEE' _ _).2 h₁')),
            DesRel.trans_of hd ih (hG _ hf) _ _ _ (hG' _ ((hEE' _ _).1 hf)) _ _ _
              (hG'' _ ((hEE'' _ _).1 hf)) (fun i => hR (i + 1)) _ _ _ h₂
              ((hresp' _ _ ((hEE' _ _).1 h₁) _ _).2 h₂')⟩
      | recursive hrs'' =>
        rcases hR 0 with ⟨-, -, h0⟩ | ⟨_, _, _, h0, -⟩
        · rw [hrs''] at h0; cases h0
        · rw [hrs] at h0; cases h0
    | recursive hrs' =>
      rcases hR 0 with ⟨-, h0, -⟩ | ⟨_, _, _, h0, -⟩
      · rw [hrs'] at h0; cases h0
      · rw [hrs] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', _, _, _, h'', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' =>
      rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, h0, -⟩
      · rw [hrs] at h0; cases h0
      · rw [hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      cases h'' with
      | cons _ _ _ _ _ _ _ _ hrs'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, -, h0, -⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs''] at h0; cases h0
      | recursive hrs'' hΘ'' _ hG'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨x, y, z, hx, hy, hz, hr⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs] at hx; rw [hrs'] at hy; rw [hrs''] at hz
          cases hx; cases hy; cases hz
          have hSS' := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
          have hSS'' := TelRel.congr hd ih hΘ _ _ _ hΘ'' TelRel.none_rel
          exact fun o₁ o₂ o₃ ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
            ⟨fun ts us hts =>
              have hts' := (hSS'' _ _).2 hts
              have hus := hSΘp.trans (hSΘp.symm hts') hts'
              hr _ _ _ (h₁ ts us hts') (h₁' us us ((hSS' _ _).1 hus)),
              DesRel.trans_of hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
                _ _ _ (hG'' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1)) _ _ _ h₂ h₂'⟩
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-- The equalities of the abstractions for destructors relate the same abstractions, at relations of
the recursive destructors that relate the same terms. -/
theorem DesRel.congr {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u ↔ y t u) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ ↔ S₂ o₁ o₂
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' _ _ =>
      have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact ObsRel.cons_congr hEp hEE fun f hf =>
        DesRel.congr hd ih (hG f hf) _ _ _ (hG' f ((hEE f f).1 hf)) (fun i => hR (i + 1))
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        have hGG := DesRel.congr hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _
          (hG' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1))
        exact fun o₁ o₂ =>
          and_congr (AbstractionRel.congr hSΘp hSS (fun _ _ => hr) _ _) (hGG o₁ o₂)
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the type of a field is a partial equivalence relation. -/
theorem FieldRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {v : Term 0 []} {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → IsPer F
  | .univ _ h => TermRel.computed_isPer hd (UnivRel.isPer hd ih h)
  | .univBelow _ m hm h => TermRel.computed_isPer hd ((ih m hm).univ_isPer h)
  | .prop _ => ⟨id, fun h _ => h⟩
  | .propBelow _ _ _ => ⟨id, fun h _ => h⟩
termination_by structural h => h

/-- The equality of the terms of the fields of a telescope relates the terms that the equality of
the same telescope relates, at relations of the recursive fields that relate more terms. -/
theorem TelRel.mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y t u) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us → S₂ ts us
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ h => h
  | .cons hA hF _ hG hresp hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      refine FieldsRel.cons_mono (fun t u h => (hFF t u).1 h) fun t u htu ts us hg => ?_
      have htt := hFp.trans htu (hFp.symm htu)
      exact TelRel.mono hd ih (hG t htt) _ _ _ (hG' t ((hFF t t).1 htt)) (fun i => hR (i + 1))
        ts us hg
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact FieldsRel.cons_mono hr fun t _ _ ts us hg =>
          TelRel.mono hd ih (hG t) _ _ _ (hG' t) (fun i => hR (i + 1)) ts us hg
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the fields of a telescope relates in the other order the terms that
the equality of the same telescope relates, at relations of the recursive fields that do so. -/
theorem TelRel.symm_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y u t) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us → S₂ us ts
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ h => FieldsRel.nil_isPer.symm h
  | .cons hA hF _ hG hresp hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      refine FieldsRel.cons_symm (fun t u h => (hFF u t).1 (hFp.symm h)) fun t u htu ts us hg => ?_
      have huu := hFp.trans (hFp.symm htu) htu
      exact TelRel.symm_of hd ih (hG u huu) _ _ _ (hG' u ((hFF u u).1 huu)) (fun i => hR (i + 1))
        ts us ((hresp t u htu ts us).1 hg)
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact FieldsRel.cons_symm hr fun _ u _ ts us hg =>
          TelRel.symm_of hd ih (hG u) _ _ _ (hG' u) (fun i => hR (i + 1)) ts us hg
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the fields of a telescope relates the terms that two equalities of
the same telescope relate in a chain, at relations of the recursive fields that do so. -/
theorem TelRel.trans_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
      ∀ (s₃ : Quality) (rs₃ : Nat → Option TermRel) (S₃ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₃ rs₃ Θ S₃ →
        (∀ i, (rs₁ i = none ∧ rs₂ i = none ∧ rs₃ i = none) ∨
          ∃ x y z, rs₁ i = some x ∧ rs₂ i = some y ∧ rs₃ i = some z ∧
            ∀ t u w, x t u → y u w → z t w) →
        ∀ ts us vs, S₁ ts us → S₂ us vs → S₃ ts vs
  | .nil, _, _, _, h', _, _, _, h'', _ => by
    cases h'; cases h''; exact fun _ _ _ h h' => FieldsRel.nil_isPer.trans h h'
  | .cons hA hF _ hG _ hrs, _, _, _, h', _, _, _, h'', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' hresp' _ =>
      cases h'' with
      | cons hA'' hF'' _ hG'' _ _ =>
        cases Computesι.det hd hA hA'
        cases Computesι.det hd hA hA''
        have hFF' := FieldRel.unique hd ih hF _ _ hF'
        have hFF'' := FieldRel.unique hd ih hF _ _ hF''
        refine FieldsRel.cons_trans
          (fun t u w h₁ h₂ => (hFF'' t w).1 (hFp.trans h₁ ((hFF' u w).2 h₂)))
          fun t u w htu huw ts us vs hg hg' => ?_
        have htt := hFp.trans htu (hFp.symm htu)
        exact TelRel.trans_of hd ih (hG t htt) _ _ _ (hG' t ((hFF' t t).1 htt)) _ _ _
          (hG'' t ((hFF'' t t).1 htt)) (fun i => hR (i + 1)) ts us vs hg
          ((hresp' t u ((hFF' t u).1 htu) us vs).2 hg')
      | recursive hrs'' _ _ =>
        rcases hR 0 with ⟨-, -, h0⟩ | ⟨_, _, _, h0, -⟩
        · rw [hrs''] at h0; cases h0
        · rw [hrs] at h0; cases h0
    | recursive hrs' _ _ =>
      rcases hR 0 with ⟨-, h0, -⟩ | ⟨_, _, _, h0, -⟩
      · rw [hrs'] at h0; cases h0
      · rw [hrs] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', _, _, _, h'', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' =>
      rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, h0, -⟩
      · rw [hrs] at h0; cases h0
      · rw [hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      cases h'' with
      | cons _ _ _ _ _ hrs'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, -, h0, -⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs''] at h0; cases h0
      | recursive hrs'' _ hG'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨x, y, z, hx, hy, hz, hr⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs] at hx; rw [hrs'] at hy; rw [hrs''] at hz
          cases hx; cases hy; cases hz
          exact FieldsRel.cons_trans hr fun t _ _ _ _ ts us vs hg hg' =>
            TelRel.trans_of hd ih (hG t) _ _ _ (hG' t) _ _ _ (hG'' t) (fun i => hR (i + 1))
              ts us vs hg hg'
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-- The equalities of the terms of the fields of a telescope relate the same terms, at relations of
the recursive fields that relate the same terms. -/
theorem TelRel.congr {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u ↔ y t u) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us ↔ S₂ ts us
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ => .rfl
  | .cons hA hF _ hG _ hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      exact FieldsRel.cons_congr hFp hFF fun a ha =>
        TelRel.congr hd ih (hG a ha) _ _ _ (hG' a ((hFF a a).1 ha)) (fun i => hR (i + 1))
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hGG := TelRel.congr hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
          (fun i => hR (i + 1))
        intro ts us
        match ts, us with
        | .nil, _ => exact .rfl
        | .cons _ _, .nil => exact .rfl
        | .cons t ts, .cons u us => exact and_congr (hr t u) (hGG ts us)
termination_by structural h _ _ _ _ _ => h

/-- A type of `U_n` has a unique equality of its terms, if the relations of the levels below `n` are
partial equivalence relations. -/
theorem UnivRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {R : TermRel} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R →
      ∀ (R' : TermRel), UnivRel sig ι n (fun m _ => levelRel sig ι m) v R' →
        ∀ t u, R t u ↔ R' t u
  | .univ hl _, _, h' => by
    cases h' with
    | univ hl' _ => subst hl; subst hl'; exact fun _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .prop hl _, _, h' => by
    cases h' with
    | prop hl' _ => subst hl; subst hl'; exact fun _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases hT
      cases has
      exact DataType.blockRel_congr (fun X T hT c hc => TelRel.congr hd ih (hS X T hT c hc) _ _ _
        (hS' X T hT c hc) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      cases hT
      cases has
      exact CodataType.blockRel_congr (fun X T hT => DesRel.congr hd ih (hS X T hT) _ _ _
        (hS' X T hT) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- A proposition of `Ω_n` has a unique truth. -/
theorem PropRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {b : Prop} :
    PropRel sig ι n (fun m _ => levelRel sig ι m) v b →
      ∀ (b' : Prop), PropRel sig ι n (fun m _ => levelRel sig ι m) v b' → (b ↔ b')
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | data h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases hT
      cases has
      exact DataType.blockTruth_congr (fun B T hT c hc => TelRel.congr hd ih (hS B T hT c hc) _ _ _
        (hS' B T hT c hc) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      cases hT
      cases has
      exact CodataType.blockTruth_congr (fun B T hT => DesRel.congr hd ih (hS B T hT) _ _ _
        (hS' B T hT) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- The type of a field has a unique equality of its terms. -/
theorem FieldRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {v : Term 0 []} {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F →
      ∀ (s' : Quality) (F' : TermRel), FieldRel sig ι n (fun m _ => levelRel sig ι m) s' v F' →
        ∀ t u, F t u ↔ F' t u
  | .univ _ h, _, _, h' => by
    have hu := UnivRel.unique hd ih h
    cases h' with
    | univ _ h' => exact TermRel.computed_congr (hu _ h')
    | univBelow _ m hm h' => exact absurd (UnivRel.level hd h (levelRel_univ_iff.1 h')) (by omega)
    | prop h' => exact (UnivRel.not_prop hd h h').elim
    | propBelow m _ h' => exact (UnivRel.not_prop hd h (levelRel_prop_iff.1 h')).elim
  | .univBelow _ m hm h, _, _, h' => by
    cases h' with
    | univ _ h' => exact absurd (UnivRel.level hd h' (levelRel_univ_iff.1 h)) (by omega)
    | univBelow _ m' hm' h' =>
      cases UnivRel.level hd (levelRel_univ_iff.1 h) (levelRel_univ_iff.1 h')
      exact TermRel.computed_congr ((ih m hm).univ_unique h h')
    | prop h' => exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h) h').elim
    | propBelow m' _ h' =>
      exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h) (levelRel_prop_iff.1 h')).elim
  | .prop h, _, _, h' => by
    have hu := PropRel.unique hd ih h
    cases h' with
    | univ _ h' => exact (UnivRel.not_prop hd h' h).elim
    | univBelow _ m _ h' => exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h') h).elim
    | prop h' => exact fun _ _ => hu _ h'
    | propBelow m hm h' => exact absurd (PropRel.level hd h (levelRel_prop_iff.1 h')) (by omega)
  | .propBelow m hm h, _, _, h' => by
    cases h' with
    | univ _ h' => exact (UnivRel.not_prop hd h' (levelRel_prop_iff.1 h)).elim
    | univBelow _ m' _ h' =>
      exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h') (levelRel_prop_iff.1 h)).elim
    | prop h' => exact absurd (PropRel.level hd h' (levelRel_prop_iff.1 h)) (by omega)
    | propBelow m' hm' h' =>
      cases PropRel.level hd (levelRel_prop_iff.1 h) (levelRel_prop_iff.1 h')
      exact fun _ _ => (ih m hm).prop_unique h h'
termination_by structural h _ _ _ => h

end

/-- The equality of the terms of the fields of a telescope is a partial equivalence relation, at
relations of the recursive fields that are. -/
theorem TelRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} (hrs : ∀ i x, rs i = some x → IsPer x)
    {ps : List Parameter} {Θ : Telescope 0 [] ps} {S : FieldsRel}
    (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S) : IsPer S where
  symm h' := TelRel.symm_of hd ih h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .none
    | some x => exact .some fun _ _ => (hrs i x hi).symm) _ _ h'
  trans h₁ h₂ := TelRel.trans_of hd ih h _ _ _ h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .inl ⟨rfl, rfl, rfl⟩
    | some x => exact .inr ⟨x, x, x, rfl, rfl, rfl, fun _ _ _ => (hrs i x hi).trans⟩) _ _ _ h₁ h₂

/-- A telescope has a unique equality of the terms of its fields, at given relations of its
recursive fields. -/
theorem TelRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S : FieldsRel} (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S) (s' : Quality)
    (S' : FieldsRel) (h' : TelRel sig ι n (fun m _ => levelRel sig ι m) s' rs Θ S') :
    ∀ ts us, S ts us ↔ S' ts us :=
  TelRel.congr hd ih h _ _ _ h' fun _ => Option.rel_refl (fun _ _ _ => .rfl) _

/-- The equality of the abstractions for destructors is a partial equivalence relation, at relations
of the recursive destructors that are. -/
theorem DesRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} (hrs : ∀ i x, rs i = some x → IsPer x) {Γ : Scope}
    {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S) : IsPer S where
  symm h' := DesRel.symm_of hd ih h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .none
    | some x => exact .some fun _ _ => (hrs i x hi).symm) _ _ h'
  trans h₁ h₂ := DesRel.trans_of hd ih h _ _ _ h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .inl ⟨rfl, rfl, rfl⟩
    | some x => exact .inr ⟨x, x, x, rfl, rfl, rfl, fun _ _ _ => (hrs i x hi).trans⟩) _ _ _ h₁ h₂

/-- Destructors have a unique equality of the abstractions for them, at given relations of their
recursive destructors. -/
theorem DesRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S) (s' : Quality) (S' : ObsRel)
    (h' : DesRel sig ι n (fun m _ => levelRel sig ι m) s' rs ds @θ S') :
    ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂ :=
  DesRel.congr hd ih h _ _ _ h' fun _ => Option.rel_refl (fun _ _ _ => .rfl) _

/-- The equality of the abstractions for destructors relates the abstractions that the equality of
the same destructors relates, at relations of the recursive destructors that relate more terms. -/
theorem DesRel.mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y t u) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ → S₂ o₁ o₂
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' _ _ =>
      have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
        have hf := hEp.trans h₁ (hEp.symm h₁)
        ⟨(hEE _ _).1 h₁, DesRel.mono hd ih (hG _ hf) _ _ _ (hG' _ ((hEE _ _).1 hf))
          (fun i => hR (i + 1)) _ _ h₂⟩
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs hΘ _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
        exact fun o₁ o₂ ⟨h₁, h₂⟩ => ⟨fun ts us hts => hr _ _ (h₁ ts us ((hSS _ _).2 hts)),
          DesRel.mono hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
            (fun i => hR (i + 1)) _ _ h₂⟩

/-- The equality of the terms of the fields of the constructors of a block, at relations `F X D` of
its recursive fields of the type `D`, grows with `X` when they do: the premise of the properties of
`(eq_μ)` and `(true_μ)`. -/
theorem TelRel.block_mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {j g k : Nat} {Δ : Scope} {α : Type}
    {Ts : List (DataType j g k Δ)} {s : Quality}
    {rec : Constructor j g k Δ → Nat → Option Name}
    {Θ : Constructor j g k Δ → (ps : List Parameter) × Telescope 0 [] ps}
    {F : α → Name → TermRel} {S : α → Constructor j g k Δ → FieldsRel}
    (hS : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, TelRel sig ι n (fun m _ => levelRel sig ι m) s
      (fun i => (rec c i).map (F X)) (Θ c).2 (S X c))
    (X Y : α) (hXY : ∀ D t u, F X D t u → F Y D t u) (T : DataType j g k Δ)
    (hT : T ∈ Ts) (c : Constructor j g k Δ) (hc : c ∈ T.constructors) (ts us : Terms 0 []) :
    S X c ts us → S Y c ts us :=
  TelRel.mono hd ih (hS X T hT c hc) _ _ _ (hS Y T hT c hc)
    (fun _ => Option.rel_map (fun D => hXY D) _) ts us

/-- The relations of every level are partial equivalence relations, in a signature whose names are
distinct. -/
theorem levelRel_isPer {sig : Signature} {ι : Interpretation} (hd : sig.Distinct) (n : Nat) :
    (levelRel sig ι n).IsPer :=
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  { univ_isPer := fun h => UnivRel.isPer hd ih (levelRel_univ_iff.1 h)
    univ_unique := fun h h' =>
      UnivRel.unique hd ih (levelRel_univ_iff.1 h) _ (levelRel_univ_iff.1 h')
    prop_unique := fun h h' =>
      PropRel.unique hd ih (levelRel_prop_iff.1 h) _ (levelRel_prop_iff.1 h') }
termination_by n
decreasing_by all_goals assumption

/-- `eq(v)` is a partial equivalence relation, symmetric and transitive, in a signature whose names
are distinct.
RFC: `\mathsf{per}_{\mathsf{eq}}.\mathsf{symm}`
RFC: `\mathsf{per}_{\mathsf{eq}}.\mathsf{trans}` -/
theorem HasEq.isPer {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R : TermRel}
    (hd : sig.Distinct) : HasEq sig ι v R → IsPer R
  | .univ n h => (levelRel_isPer hd n).univ_isPer h
  | .prop _ _ _ hR => ⟨fun h => (hR _ _).2 ((hR _ _).1 h), fun h _ => (hR _ _).2 ((hR _ _).1 h)⟩

/-- A type of a universe is not a proposition, in a signature whose names are distinct. -/
theorem HasEq.univ_not_prop {sig : Signature} {ι : Interpretation} {v : Term 0 []} {n k : Nat}
    {R : TermRel} {b : Prop} (hd : sig.Distinct) (h : (levelRel sig ι n).univ v R)
    (h' : (levelRel sig ι k).prop v b) : False :=
  UnivRel.not_prop hd (levelRel_univ_iff.1 h) (levelRel_prop_iff.1 h')

/-- The level of a type of a universe is unique, in a signature whose names are distinct. -/
theorem HasEq.univ_level {sig : Signature} {ι : Interpretation} {v : Term 0 []} {n n' : Nat}
    {R R' : TermRel} (hd : sig.Distinct) (h : (levelRel sig ι n).univ v R)
    (h' : (levelRel sig ι n').univ v R') : n = n' :=
  UnivRel.level hd (levelRel_univ_iff.1 h) (levelRel_univ_iff.1 h')

/-- `eq(v)` is unique: two equalities of the terms of a type relate the same terms, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\mathsf{eq}}` -/
theorem HasEq.unique {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R R' : TermRel}
    (hd : sig.Distinct) : HasEq sig ι v R → HasEq sig ι v R' → ∀ t u, R t u ↔ R' t u
  | .univ n h, .univ _ h' => by
    cases HasEq.univ_level hd h h'
    exact (levelRel_isPer hd n).univ_unique h h'
  | .univ _ h, .prop _ _ h' _ => (HasEq.univ_not_prop hd h h').elim
  | .prop _ _ h _, .univ _ h' => (HasEq.univ_not_prop hd h' h).elim
  | .prop k _ h hR, .prop _ _ h' hR' => by
    cases PropRel.level hd (levelRel_prop_iff.1 h) (levelRel_prop_iff.1 h')
    exact fun t u => (hR t u).trans (((levelRel_isPer hd k).prop_unique h h').trans (hR' t u).symm)

/-! ## Exactness of the Proofs -/

/-- The names of a meaningful signature are distinct.
RFC: `\mathsf{distinct}_{\vDash\Sigma}` -/
theorem ValidSig.distinct {ι : Interpretation} {sig : Signature} (h : ValidSig ι sig) :
    sig.Distinct :=
  h.1

/-- A sort computes to itself. -/
theorem Computes.sort (sig : Signature) (κ : Universe 0) : Computes sig (.sort κ) (.sort κ) :=
  ⟨.refl _, .sort κ⟩

/-- A sort computes to nothing else than itself. -/
theorem Computes.sort_inv {sig : Signature} {κ : Universe 0} {v : Term 0 []} :
    Computes sig (.sort κ) v → v = .sort κ
  | ⟨.refl _, _⟩ => rfl
  | ⟨.step h _, _⟩ => nomatch h

/-- The terms that the universe of propositions `Ω_l` relates are propositions. -/
theorem HasEq.prop_isProp {sig : Signature} {ι : Interpretation} {l : Level 0} {R : TermRel}
    {v w : Term 0 []} (hR : HasEq sig ι (.sort ⟨.prop, l⟩) R) (hvw : R v w) : IsProp sig ι v := by
  cases hR with
  | univ n h =>
    cases levelRel_univ_iff.1 h with
    | prop _ hk =>
      obtain ⟨b, _, hb, -⟩ := hvw
      exact ⟨_, b, hb⟩
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop _ _ h _ =>
    cases levelRel_prop_iff.1 h with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv

/-- A sort is not a proposition. -/
theorem not_isProp_sort {sig : Signature} {ι : Interpretation} {κ : Universe 0} :
    ¬ IsProp sig ι (.sort κ) := fun ⟨_, _, h⟩ => by
  cases levelRel_prop_iff.1 h with
  | data _ _ _ _ hv => cases hv
  | codata _ _ _ _ hv => cases hv

/-- A sort does not compute to a proposition. -/
theorem not_computesToProp_sort {sig : Signature} {ι : Interpretation} {κ : Universe 0} :
    ¬ ComputesToProp sig ι (.sort κ) := fun ⟨_, hc, hp⟩ => by
  cases hc.sort_inv
  exact not_isProp_sort hp

/-- `(exact_Ω)`: two closed terms are equal proofs of a proposition exactly when each of them is a
proof of it.
RFC: `\mathsf{exact}_\Omega` -/
theorem exact_prop {sig : Signature} {ι : Interpretation} {A t u : Term 0 []} {l : Level 0}
    (hA : ValidTerm₀ sig ι A (.sort ⟨.prop, l⟩)) :
    ValidEqTerm₀ sig ι t u A ↔ ValidTerm₀ sig ι t A ∧ ValidTerm₀ sig ι u A := by
  obtain ⟨⟨hd, -⟩, hcl, -⟩ := hA
  obtain ⟨A₀, v, w, R, hc, hv, -, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  have hvp := hR.prop_isProp hvw
  have hP : ComputesToProp sig ι A := ⟨v, hv, hvp⟩
  constructor
  · rintro ⟨hTA, -, hcl'⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htu⟩ := hcl' hP
    have hper := hR₁.isPer hd
    exact ⟨⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans htu (hper.symm htu)⟩⟩,
      ⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans (hper.symm htu) htu⟩⟩⟩
  · rintro ⟨⟨hTA, -, hclt⟩, -⟩
    refine ⟨hTA, fun h => absurd hP h, fun _ => ?_⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htt⟩ := hclt hP
    cases Computesι.det hd hA₁ hv
    obtain ⟨k, b, hb⟩ := hvp
    have hRb : ∀ t u, R₁ t u ↔ b := fun t u => hR₁.unique hd (.prop k b hb fun _ _ => .rfl) t u
    exact ⟨v, R₁, hA₁, hR₁, (hRb t u).2 ((hRb t t).1 htt)⟩

end Sic.Core
