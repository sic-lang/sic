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

/-! ## Hypothetical Judgments -/

/-- The substitution `σ` without its last entry. -/
def Subst.tail {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} (σ : Subst k Γ (e :: Δ)) : Subst k Γ Δ :=
  fun x => σ x.succ

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

/-! ## Partial Equivalence Relations -/

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

end Sic.Core
