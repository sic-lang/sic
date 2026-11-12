module

public import Sic.Core.Evaluation
public import Sic.Core.Meaning.Interpretation
public import Sic.Core.Substitution.Closed

/-!
# Equality of the Canonical Terms

The equality of the canonical terms of the closed canonical types of annex 18 of RFC 36, by the
graphs of the relations of the sorts of each level.
A closed canonical type is known by the equality of its canonical terms, a partial equivalence
relation `eq(v)`, which the sorts, the data types and the codata types give: the universe `U_n` has
the types of the level below it as terms, equal when they have the same equality of terms and, for
each program, the same relation of run time, the
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
Each level also gives each of its types a relation of run time, which `Sic.Core.Meaning.RunTime`
defines on the graph of the same level, so that the relations of a level, `LevelRel`, gather the
three of them.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Equality of the Canonical Terms -/

/-- A relation between closed terms. -/
abbrev TermRel : Type := Term 0 [] → Term 0 [] → Prop

/-- A relation between the terms of the fields of two constructors. -/
abbrev FieldsRel : Type := Terms 0 [] → Terms 0 [] → Prop

/-- A relation of run time, between a closed term of the source and the address of a value in a
heap. -/
abbrev RunRel : Type := Heap → Term 0 [] → Nat → Prop

/-- The relations of the sorts of one level `n`, given by their graphs: the equality of the terms of
its types, the truth of its propositions and the relations of run time of its types. -/
structure LevelRel where
  /-- `(v, R) ∈ ty(U_n)`: `v` is a type of `U_n`, whose canonical terms are equal by `R`. -/
  univ : Term 0 [] → TermRel → Prop
  /-- `(v, b) ∈ ty(Ω_n)`: `v` is a proposition of `Ω_n`, whose truth is `b`. -/
  prop : Term 0 [] → Prop → Prop
  /-- `(v, R) ∈ rt(U_n)`: `v` is a type of `U_n`, whose terms are related at run time by `R` to the
  addresses of the values that the program `P` computes. -/
  run : Program → Term 0 [] → RunRel → Prop

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
  with the same equality and, for each program, the same relation of run time.
  RFC: `\mathsf{ty}_U` -/
  | univ {l : Level 0} {k : Nat} (hl : l.closedValue = k) (hk : k + 1 = n) :
      UnivRel sig ι n below (.sort ⟨.type, l⟩) fun A B =>
        (∃ R, (below k (hk ▸ Nat.lt_succ_self k)).univ A R ∧
          (below k (hk ▸ Nat.lt_succ_self k)).univ B R) ∧
        ∀ P, ∃ Q, (below k (hk ▸ Nat.lt_succ_self k)).run P A Q ∧
          (below k (hk ▸ Nat.lt_succ_self k)).run P B Q
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

end Sic.Core
