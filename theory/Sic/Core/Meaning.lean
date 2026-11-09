module

public import Sic.Core.Reduction

/-!
# Meaning

The meaning of the judgments of annex 16 of RFC 36, after the meaning explanations of Martin-Löf: a
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

/-- Closed abstractions, one for each destructor, found by its name and the parameters of its
arguments: the observations of a closed term of a codata type, or what the destructors of the type
relate. -/
abbrev Observations : Type := Name → (ps : List Parameter) → Term 0 (Scope.extend [] ps.length)

/-- A relation between closed abstractions for the destructors of a codata type. -/
abbrev ObsRel : Type := Observations → Observations → Prop

/-- `x̄. v.(T.d)(x̄)`: the observations of the closed term `v` at the instance `T = D.{s̄; l̄; p̄} ā`, an
abstraction over the arguments of each destructor. -/
def Term.observations {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) (as : InstanceArgs 0 [] Δ) (v : Term 0 []) : Observations := fun d xs =>
  .obs D qs ls ps (as.rename fun x => by cases x) v.weakenClosed d (Args.bound (Γ := []) xs).terms

/-- The closed term `v` is a corecursor of the declared type `D`, whose observations at the instance
it carries are `o`. -/
def Term.CorecObservations (D : Name) (v : Term 0 []) (o : Observations) : Prop :=
  ∃ (r : Grade) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
    (as : InstanceArgs 0 [] Δ) (ss : Terms 0 []) (Ss : States 0 []) (gs : CorecBranches 0 []),
    v = .corec r D qs ls ps as ss Ss gs ∧ o = v.observations D qs ls ps as

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
  constructors have fields that are telescopes in `U_n`, and whose canonical terms are equal by
  `(eq_c)`.
  RFC: `\mathsf{ty}_D` -/
  | data {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel)
      (hS : ∀ c ∈ T.constructors,
        TelRel sig ι n below .type (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S c)) :
      UnivRel sig ι n below v (T.ctorRel D S)
  /-- `(ty_d)`: an instance `D.{s̄; l̄; p̄} ā` of a codata type `T` of the signature in `U_n`, whose
  destructors are in `U_n` at the arguments `ā`, and whose canonical terms are equal by `(eq_d)`.
  RFC: `\mathsf{ty}_d` -/
  | codata {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : ObsRel)
      (hS : DesRel sig ι n below .type ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
        as.toSubst S) :
      UnivRel sig ι n below v (corecRel D S)

-- ADE: none.
/--
`ty(Ω_n)`: the least relation of the clauses of the instances of the data types and of the codata
types in `Ω_n`, given the
relations `below` of the levels below `n`, which gives each proposition its truth.
-/
inductive PropRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Term 0 [] → Prop → Prop where
  /-- `(ty_DΩ)`: an instance `D.{s̄; l̄; p̄} ā` of a data type `T` of the signature in `Ω_n`, whose
  constructors have fields that are telescopes in `Ω_n`, and whose truth is `(true_D)`.
  RFC: `\mathsf{ty}_{D\Omega}` -/
  | data {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel)
      (hS : ∀ c ∈ T.constructors,
        TelRel sig ι n below .prop (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S c)) :
      PropRel sig ι n below v (T.truth S)
  /-- `(ty_dΩ)`: an instance `D.{s̄; l̄; p̄} ā` of a codata type `T` of the signature in `Ω_n`, whose
  destructors are in `Ω_n` at the arguments `ā`, and whose truth is `(true_d)`.
  RFC: `\mathsf{ty}_{d\Omega}` -/
  | codata {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : ObsRel)
      (hS : DesRel sig ι n below .prop ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
        as.toSubst S) :
      PropRel sig ι n below v S.truth

-- ADE: none.
/--
`ty(s_n)` for the telescopes: `Θ` is a closed telescope in the sort of the quality `s` at the level
`n`, the terms of whose entries are equal by `S`; the equality of the terms of the rest of the
telescope, which the first term instantiates, is the same for equal first terms.
-/
inductive TelRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Quality → {ps : List Parameter} → Telescope 0 [] ps → FieldsRel → Prop where
  /-- `(ty_Θε)`: the empty telescope.
  RFC: `\mathsf{ty}_{\Theta\varepsilon}` -/
  | nil {s : Quality} : TelRel sig ι n below s .nil FieldsRel.nil
  /-- `(ty_Θ,)`: a first type that computes to a type of a sort that `s_n` bounds, whose terms are
  equal by `F`, and a rest that is a telescope for each term of it.
  RFC: `\mathsf{ty}_{\Theta,}` -/
  | cons {s : Quality} {q : Grade} {p : Parameter} {ps : List Parameter} {A v : Term 0 []}
      {Θ : Telescope 0 [.var] ps} {F : TermRel} (hA : Computesι sig ι A v)
      (hF : FieldRel sig ι n below s v F) (G : Term 0 [] → FieldsRel)
      (hG : ∀ a, F a a → TelRel sig ι n below s (Θ.subst₀ (Subst₀.single a)) (G a))
      (hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us) :
      TelRel sig ι n below s (.cons q p A Θ) (FieldsRel.cons F G)

-- ADE: none.
/--
`ty(s_n)` for the destructors: the destructors `d̄`, at the closed substitution `θ` of their scope,
are in the sort of the quality `s` at the level `n`, and the abstractions for them are equal by `S`;
the arguments of each destructor are a telescope in `U_n`, its result a type of a sort that `s_n`
bounds for equal arguments, and the destructors after it are, for each abstraction for it, the
same for equal abstractions.
The Lean carries the closed substitution of the scope of the destructors, rather than the closed
destructors `d̄[θ]` of the RFC, as the closed judgments of the contexts do.
-/
inductive DesRel (sig : Signature) (ι : Interpretation) (n : Nat) (below : LevelRel.Below n) :
    Quality → {Γ : Scope} → {ns : List Name} → Destructors 0 Γ ns → Subst 0 [] Γ → ObsRel → Prop
    where
  /-- `(ty_d̄ε)`: no destructor.
  RFC: `\mathsf{ty}_{\bar d\varepsilon}` -/
  | nil {s : Quality} {Γ : Scope} {θ : Subst 0 [] Γ} : DesRel sig ι n below s .nil @θ fun _ _ => True
  /-- `(ty_d̄|)`: a destructor `d : (Θ ⊢ B ◀ ψ)`, whose arguments `Θ[θ]` are a telescope in `U_n`
  with the equality `SΘ`, whose result type `B[θ, t̄]` computes, at equal arguments `t̄`, to a type of
  a sort that `s_n` bounds, with the equality `F t̄` of its terms, the same for equal arguments, and
  the destructors after it, which are for each abstraction `f` for `d` with the equality `G f`, the
  same for equal abstractions.
  RFC: `\mathsf{ty}_{\bar d|}` -/
  | cons {s : Quality} {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
      {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
      {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {SΘ : FieldsRel}
      (hΘ : TelRel sig ι n below .type (Θ.subst θ) SΘ) (F : Terms 0 [] → TermRel)
      (hB : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
        ∃ v, Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v)
      (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ v,
        Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v → FieldRel sig ι n below s v (F ts.terms))
      (hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u)
      (G : Term 0 (Scope.extend [] ps.length) → ObsRel)
      (hG : ∀ f, AbstractionRel SΘ F f f → DesRel sig ι n below s ds (Subst.snoc θ f) (G f))
      (hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂) :
      DesRel sig ι n below s (.cons (d := d) p q Θ B ψ ds) @θ fun o₁ o₂ =>
        AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂

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
  RFC: `\mathsf{eq}_{\mathsf{true}}`, `\mathsf{eq}_{\mathsf{false}}` -/
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
RFC: `\vDash_\equiv`, `\vDash_{\equiv\Omega}` -/
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
RFC: `\mathsf{eq}_\varepsilon`, `\mathsf{eq}_x`, `\mathsf{eq}_X`
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
RFC: `{\vDash}\mathsf{tel}_{\kappa\varepsilon}`, `{\vDash}\mathsf{tel}_{\kappa,}` -/
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
/-- `(⊨Γ_tel_κ)`: `Σ; Γ ⊨ Θ : κ`, at levels without variables: the telescope substituted by two
equal closed substitutions of the context gives equal closed telescopes in the sort `κ`.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\kappa}` -/
def ValidTelescopeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqTelescope₀ sig ι κ (Θ.subst σ₁) (Θ.subst σ₂)

-- ADE: none.
/-- `Σ; Γ ⊨ d̄ : κ`, at levels without variables: the arguments of each destructor are a telescope in
the universe of the level of `κ`, its result a term of a sort that `κ` bounds, in the context
extended by its arguments, and the destructors after it are in `κ`, in the context extended by it.
RFC: `{\vDash}\bar d_{\kappa\varepsilon}`, `{\vDash}\bar d_{\kappa|}` -/
def ValidDestructorsΓ (sig : Signature) (ι : Interpretation) :
    {Γ : Scope} → {ns : List Name} → Context 0 Γ → Destructors 0 Γ ns → Universe 0 → Prop
  /- `(⊨d̄_κε)`. -/
  | _, _, ctx, .nil, _ => ValidCtx₀ sig ι ctx
  /- `(⊨d̄_κ|)`. -/
  | _, _, ctx, .cons _ _ Θ B ψ ds, κ => ValidTelescopeΓ sig ι ctx Θ ⟨.type, κ.level⟩ ∧
      (∃ κ₁, κ₁ ≼ κ ∧ ValidTermΓ sig ι (ctx.append Θ) B (.sort κ₁)) ∧
      ValidDestructorsΓ sig ι (ctx.secondOrder Θ B ψ) ds κ

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

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidTelescope (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  ∀ ρ, ValidTelescopeΓ sig ι (ctx.atLevels ρ) (Θ.atLevels ρ) (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ d̄ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidDestructors (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ns : List Name} (ctx : Context k Γ) (ds : Destructors k Γ ns) (κ : Universe k) : Prop :=
  ∀ ρ, ValidDestructorsΓ sig ι (ctx.atLevels ρ) (ds.atLevels ρ) (κ.atLevels ρ)

/-! ## Signatures and Entries -/

-- ADE: none.
/-- `Σ ⊨ D`: the type declaration `D` is meaningful in the signature `Σ`.
`(⊨data)`: `Σ ⊨ data.{s̄; l̄; p̄} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort and grade
variables, the fields of each constructor are a telescope in the sort `κ`, in the context of the
parameters, at each value of the level variables.
`(⊨codata)`: `Σ ⊨ codata.{s̄; l̄; p̄} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort and
grade variables, the destructors of each type are in the sort `κ`, in the context of the
parameters, at each value of the level variables.
The meaning ignores the grades, and the names of the constructors and of the destructors, distinct,
are those of the signature.
RFC: `{\vDash}\mathsf{data}`, `{\vDash}\mathsf{codata}` -/
def ValidTypeDeclaration (sig : Signature) (ι : Interpretation) (decl : TypeDeclaration) : Prop :=
  match decl.body with
  | .data Ts => ∀ I, ∀ T ∈ Ts, ∀ c ∈ T.constructors,
      ValidTelescope sig ι (decl.params I) (c.fields I) (decl.sort I)
  | .codata Ts => ∀ I, ∀ T ∈ Ts, ValidDestructors sig ι (decl.params I) (T.body I) (decl.sort I)

/-- The fields of the constructors of a data type of a meaningful type declaration are telescopes in
its sort. -/
theorem ValidTypeDeclaration.fields {sig : Signature} {ι : Interpretation} {decl : TypeDeclaration}
    (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope} (hc : c ∈ T.constructors) :
    ValidTelescope sig ι (decl.params I) (c.fields I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.dataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact h I T hT c hc
  · exact nomatch hT

/-- The destructors of a codata type of a meaningful type declaration are in its sort. -/
theorem ValidTypeDeclaration.destructors {sig : Signature} {ι : Interpretation}
    {decl : TypeDeclaration} (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes) :
    ValidDestructors sig ι (decl.params I) (T.body I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.codataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact nomatch hT
  · exact h I T hT

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

/-- A closed term has the observations of one corecursor at most. -/
theorem Term.CorecObservations.unique {D D' : Name} {v : Term 0 []} {o o' : Observations}
    (h : v.CorecObservations D o) (h' : v.CorecObservations D' o') : o = o' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, h', rfl⟩ := h'
  cases h'
  rfl

/-- `(eq_d)` is a partial equivalence relation when the equality of the destructors is one. -/
theorem corecRel_isPer {D : Name} {S : ObsRel} (hS : IsPer S) : IsPer (corecRel D S) where
  symm := fun ⟨o₁, o₂, hv, hw, h⟩ => ⟨o₂, o₁, hw, hv, hS.symm h⟩
  trans := fun ⟨o₁, o₂, hv, hw, h⟩ ⟨_, o₃, hw', hx, h'⟩ => by
    cases hw.unique hw'
    exact ⟨o₁, o₃, hv, hx, hS.trans h h'⟩

/-- `(eq_d)` relates the same terms for equalities of the destructors that relate the same
abstractions. -/
theorem corecRel_congr {D : Name} {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂) :
    ∀ v w, corecRel D S v w ↔ corecRel D S' v w :=
  fun _ _ => ⟨fun ⟨o₁, o₂, hv, hw, hS⟩ => ⟨o₁, o₂, hv, hw, (h _ _).1 hS⟩,
    fun ⟨o₁, o₂, hv, hw, hS⟩ => ⟨o₁, o₂, hv, hw, (h _ _).2 hS⟩⟩

/-- `(true_d)` is the same for equalities of the destructors that relate the same abstractions. -/
theorem ObsRel.truth_congr {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂) :
    S.truth ↔ S'.truth :=
  ⟨fun ⟨o, ho⟩ => ⟨o, (h o o).1 ho⟩, fun ⟨o, ho⟩ => ⟨o, (h o o).2 ho⟩⟩

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

/-! ### The Relations of a Level -/

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
    DataType.ctorRel_isPer (hd.constructors_nodup h) fun c hcm => TelRel.isPer hd ih (hS c hcm)
  | .codata _ _ _ _ _ _ _ _ hS => corecRel_isPer (DesRel.isPer hd ih hS)

/-- The equality of the terms of the fields of a telescope is a partial equivalence relation. -/
theorem TelRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s Θ S → IsPer S
  | .nil => FieldsRel.nil_isPer
  | .cons _ hF _ hG hresp =>
    FieldsRel.cons_isPer (FieldRel.isPer hd ih hF) (fun a ha => TelRel.isPer hd ih (hG a ha)) hresp

/-- The equality of the abstractions for destructors is a partial equivalence relation. -/
theorem DesRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {Γ : Scope} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s ds @θ S → IsPer S
  | .nil => ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .cons hΘ _ hB hF hBresp _ hG hresp =>
    ObsRel.cons_isPer
      (AbstractionRel.isPer (TelRel.isPer hd ih hΘ)
        (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp)
      (fun f hf => DesRel.isPer hd ih (hG f hf)) hresp

/-- The equality of the terms of the type of a field is a partial equivalence relation. -/
theorem FieldRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {v : Term 0 []} {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → IsPer F
  | .univ _ h => TermRel.computed_isPer hd (UnivRel.isPer hd ih h)
  | .univBelow _ m hm h => TermRel.computed_isPer hd ((ih m hm).univ_isPer h)
  | .prop _ => ⟨id, fun h _ => h⟩
  | .propBelow _ _ _ => ⟨id, fun h _ => h⟩

end

mutual

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
    have hu := fun c hcm => TelRel.unique hd ih (hS c hcm)
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
      exact DataType.ctorRel_congr fun c hcm => hu c hcm _ _ (hS' c hcm)
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    have hu := DesRel.unique hd ih hS
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
      exact corecRel_congr (hu _ _ hS')
termination_by structural h _ _ => h

/-- A proposition of `Ω_n` has a unique truth. -/
theorem PropRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {b : Prop} :
    PropRel sig ι n (fun m _ => levelRel sig ι m) v b →
      ∀ (b' : Prop), PropRel sig ι n (fun m _ => levelRel sig ι m) v b' → (b ↔ b')
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
    have hu := fun c hcm => TelRel.unique hd ih (hS c hcm)
    cases h' with
    | data h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases hT
      cases has
      exact DataType.truth_congr fun c hcm => hu c hcm _ _ (hS' c hcm)
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    have hu := DesRel.unique hd ih hS
    cases h' with
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      cases hT
      cases has
      exact ObsRel.truth_congr (hu _ _ hS')
termination_by structural h _ _ => h

/-- A telescope has a unique equality of the terms of its fields. -/
theorem TelRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s Θ S →
      ∀ (s' : Quality) (S' : FieldsRel), TelRel sig ι n (fun m _ => levelRel sig ι m) s' Θ S' →
        ∀ ts us, S ts us ↔ S' ts us
  | .nil, _, _, h' => by cases h'; exact fun _ _ => .rfl
  | .cons hA hF _ hG _, _, _, h' => by
    have hFu := FieldRel.unique hd ih hF
    have hGu := fun a ha => TelRel.unique hd ih (hG a ha)
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have hFF := hFu _ _ hF'
      exact FieldsRel.cons_congr hFp hFF fun a ha => hGu a ha _ _ (hG' a ((hFF a a).1 ha))
termination_by structural h _ _ _ => h

/-- Destructors have a unique equality of the abstractions for them. -/
theorem DesRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {Γ : Scope} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s ds @θ S →
      ∀ (s' : Quality) (S' : ObsRel), DesRel sig ι n (fun m _ => levelRel sig ι m) s' ds @θ S' →
        ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂
  | .nil, _, _, h' => by cases h'; exact fun _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _, _, _, h' => by
    have hSΘu := TelRel.unique hd ih hΘ
    have hSΘp := TelRel.isPer hd ih hΘ
    have hGu := fun f hf => DesRel.unique hd ih (hG f hf)
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' _ =>
      have hSS := hSΘu _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u, F ts.terms t u ↔ F' ts.terms t u :=
          fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact ObsRel.cons_congr hEp hEE fun f hf => hGu f hf _ _ (hG' f ((hEE f f).1 hf))
termination_by structural h _ _ _ => h

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
RFC: `\mathsf{per}_{\mathsf{eq}}.\mathsf{symm}`, `\mathsf{per}_{\mathsf{eq}}.\mathsf{trans}` -/
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
