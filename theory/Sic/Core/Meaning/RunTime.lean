module

public import Sic.Core.Evaluation.Heap
public import Sic.Core.Meaning.Equality
public import Sic.Grading.GradeSet

/-!
# Relations of Run Time

The relations of run time of the closed canonical types of annex 18 of RFC 36, between a closed term
of the source and the address of a value of the target language in a heap, which state that the
value at the address is what the erasure by `S^{11ᵐ}` of the term computes at run time.
The terms of a universe and those of a proposition are related to every address, since their
positions are erased or used by no computation at run time; a term of an instance of a data type is
related to a constructor of the same case, whose fields of a grade that run time uses are related to
the fields of the term, and a term of an instance of a codata type to a value whose observations by
the destructors of a grade that run time uses, at related arguments, give results related to the
observations of the term.

The relation of a type is defined as its equality of terms, by the graph of the relations of the
types of each level, a least relation between a type and its relation of run time, whose relations
of the data types are least fixed points and those of the codata types greatest fixed points; the
graph of a level is given by the relations of all the levels below it, those of `LevelRel`.
It reads the equality of the terms of the same level: the rest of a telescope of fields, and the
destructors after a destructor, are given for each term that the equality gives to the field or to
the destructor, since a field erased at run time says nothing at run time of its term, on which the
types after it depend.
The heap of an observation extends the heap in which the closure is related, since its arguments
may be computed after the closure is: the relation of the codata types is stated in each heap that
extends `H`, while those of the data types read only the values of `H`, which every heap that
extends `H` keeps.

The program `P` gives the constants of the target language their bodies, the erasure of the
signature, and the interpretation `ι` the constants of the source, as in the equality, so that the
relation holds for the programs that realize the declared constants as `ι` interprets them.

ADE relate a term to the term of the target language that it extracts to, by recursion on the proof
that its type is reducible, in `Graded/Erasure/LogicalRelation.agda`, after the reduction of the
target language, without heap, while the relation here relates a term to an address of the heap of
an evaluation.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Relations of Run Time -/

/-- A relation of run time between the terms of the fields of a constructor, or of the arguments of
a destructor, and the addresses of their values in a heap. -/
abbrev RunFieldsRel : Type := Heap → Terms 0 [] → List Nat → Prop

/-- A relation of run time between the observations of a closed term of a codata type and the
address of a value in a heap. -/
abbrev RunObsRel : Type := Heap → Observations → Nat → Prop

/-- The relations of run time of the types of a level, given by their graph. -/
abbrev RunLevelRel : Type := Term 0 [] → RunRel → Prop


-- ADE: none.
/-- `®⇓(R)`: a closed term that computes to a canonical term that `R` relates to the address.
RFC: `\circledR_\Downarrow` -/
def RunRel.computed (sig : Signature) (ι : Interpretation) (R : RunRel) : RunRel :=
  fun H t a => ∃ v, Computesι sig ι t v ∧ R H v a

-- ADE: none.
/-- `R^p`: the relation `R` at the grade `p`, the relation `R` if the grade `p` is used at run time,
and every term and address otherwise, since the erasure replaces by `↯` a position of this grade.
RFC: `\circledR_p` -/
def RunRel.atGrade (p : Grade) (R : RunRel) : RunRel :=
  fun H t a => p ∉ Mode.oneOne.erased → R H t a

/-- The relation of run time of the terms of the fields of the empty telescope, which relates the
empty terms to the empty addresses. -/
def RunFieldsRel.nil : RunFieldsRel
  | _, .nil, [] => True
  | _, _, _ => False

/-- The relation of run time of the terms of the fields of a telescope `x : A, Θ`, where `F` relates
the first term to the first address, and `G a` the other terms, those of `Θ[a / x]`, to the other
addresses. -/
def RunFieldsRel.cons (F : RunRel) (G : Term 0 [] → RunFieldsRel) : RunFieldsRel
  | H, .cons t ts, a :: as => F H t a ∧ G t H ts as
  | _, _, _ => False

-- ADE: none.
/-- `(®_c)`: the relation of run time of the canonical terms of the instance `I` of the data type
`T`, named `D`, which relates a constructor of `D` to a constructor of the target language of its
case, whose fields are at the multiplicities at run time of their grades and at the requirements at
run time of their requirements at the instance, and whose fields the relation `S c` of the fields
of the constructor `c` relates.
RFC: `\circledR_c` -/
def DataType.runCtorRel {j g k : Nat} {Δ : Scope} (sig : Signature) (I : Instance j g) (D : Name)
    (T : DataType j g k Δ) (S : Constructor j g k Δ → RunFieldsRel) : RunRel :=
  fun H v a => ∃ c ∈ T.constructors, ∃ i ts as, v.IsCtor D c.name ts ∧
    sig.constructorCase D c.name = some i ∧
      H[a]? = some (.ctor i ((c.params I).map (·.usage.run)) ((c.params I).map (·.requirement.run))
        as) ∧ S c H ts as

-- ADE: none.
/-- `(®_μ)`: the relations of run time of the canonical terms of the instances of the data types
`Ts` of a block, the least relations, one for each type, that relate what `(®_c)` relates, when the
relation `S X c` of the fields of each constructor `c` relates its recursive fields by the relations
`X`: a term and an address are related by every relations `X` closed under these clauses.
RFC: `\circledR_\mu` -/
def DataType.runBlockRel {j g k : Nat} {Δ : Scope} (sig : Signature) (I : Instance j g)
    (Ts : List (DataType j g k Δ)) (S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel)
    (D : Name) : RunRel :=
  fun H v a => ∀ X : Name → RunRel,
    (∀ T ∈ Ts, ∀ H v a, T.runCtorRel sig I T.name (S X) H v a → X T.name H v a) → X D H v a

-- ADE: none.
/-- `(®_d)`: the relation of run time of the canonical terms of an instance of the codata type
named `D`, which relates a corecursor of `D` to an address when the relation `S` of the destructors
of the type relates its observations to the address.
RFC: `\circledR_d` -/
def runCorecRel (D : Name) (S : RunObsRel) : RunRel :=
  fun H v a => ∃ o, v.CorecObservations D o ∧ S H o a

-- ADE: none.
/-- `(®_ν)`: the relations of run time of the canonical terms of the instances of the codata types
`Ts` of a block, the greatest relations, one for each type, whose related terms and addresses
`(®_d)` relates, when the relation `S X T` of the destructors of each type `T` relates the results
of its recursive destructors by the relations `X`: a term and an address are related by some
relations `X` consistent with these clauses.
RFC: `\circledR_\nu` -/
def CodataType.runBlockRel {j g k : Nat} {Δ : Scope} (Ts : List (CodataType j g k Δ))
    (S : (Name → RunRel) → CodataType j g k Δ → RunObsRel) (D : Name) : RunRel :=
  fun H v a => ∃ X : Name → RunRel,
    (∀ T ∈ Ts, ∀ H v a, X T.name H v a → runCorecRel T.name (S X T) H v a) ∧ X D H v a

-- ADE: none.
/-- `(®_x̄)`: the closed abstraction `x̄. B` for the destructor of the case `i`, whose arguments
`ps` have the relation of run time `SΘ`, whose result has the ownership `ψ` and which requires the
ownership `χ` of the value that it observes, and the value at the address `a`: in each heap `H'`
that extends `H`, at arguments `t̄` that `SΘ` relates to addresses `b̄`, the observation of the value
at `a` by the destructor, at each weight `ϖ`, applied to `b̄` at the multiplicities and the
requirements at run time of the grades and of the requirements of the arguments, with the ownership
at run time of the result and the requirement at run time on the value, gives a value, reading some
cells, that the relation `F t̄` of the result type relates to `B[t̄ / x̄]`.
RFC: `\circledR_{\bar x}` -/
def RunAbstractionRel (P : Program) {ps : List Parameter} (i : Nat)
    (ψ : ResultOwnership Grade ps.length) (χ : Grade) (SΘ : RunFieldsRel)
    (F : Terms 0 [] → RunRel) (f : Term 0 (Scope.extend [] ps.length)) (H : Heap) (a : Nat) :
    Prop :=
  ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps) (bs : List Nat), SΘ H' ts.terms bs →
    ∀ ϖ, ∃ w H'' R, EvalObs P ϖ H' a i (ψ.map Grade.run) χ.run (ps.map (·.usage.run))
      (ps.map (·.requirement.run)) bs w H'' R ∧ F ts.terms H'' (f.subst ts.toSubst) w

/-! ## Graph of the Relations of Run Time -/

mutual

-- ADE: none.
/--
`rt(U_n)`: the least relation of the clauses of the universes and of the instances of the data
types and of the codata types in `U_n`, given the relations `below` of run time of the levels below
`n`, which gives each type of `U_n` its relation of run time.
-/
inductive RunUnivRel (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (below : LevelRel.Below n) : Term 0 [] → RunRel → Prop where
  /-- `(rt_U)`: the universe `U_k`, if `k + 1 = n`, whose terms, types, are erased.
  RFC: `\mathsf{rt}_U` -/
  | univ {l : Level 0} {k : Nat} (hl : l.closedValue = k) (hk : k + 1 = n) :
      RunUnivRel sig ι P n below (.sort ⟨.type, l⟩) fun _ _ _ => True
  /-- `(rt_Ω)`: the universe of propositions `Ω_k`, if `k + 1 = n`, whose terms, propositions, are
  erased.
  RFC: `\mathsf{rt}_\Omega` -/
  | prop {l : Level 0} {k : Nat} (hl : l.closedValue = k) (hk : k + 1 = n) :
      RunUnivRel sig ι P n below (.sort ⟨.prop, l⟩) fun _ _ _ => True
  /-- `(rt_D)`: an instance `D.{s̄; l̄; p̄} ā` of a data type `T` of the signature in `U_n`, whose
  block has types whose constructors have fields that are telescopes of run time in `U_n`, whatever
  the relations `X` of the instances of the types of the block at their recursive fields, and whose
  relation of run time is `(®_μ)`.
  RFC: `\mathsf{rt}_D` -/
  | data {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        RunFieldsRel)
      (hS : ∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        RunTelRel sig ι P n below
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) :
      RunUnivRel sig ι P n below v
        (DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D)
  /-- `(rt_d)`: an instance `D.{s̄; l̄; p̄} ā` of a codata type `T` of the signature in `U_n`, whose
  block has types whose destructors are of run time in `U_n` at the arguments `ā`, whatever the
  relations `X` of the instances of the types of the block at their recursive destructors, and whose
  relation of run time is `(®_ν)`.
  RFC: `\mathsf{rt}_d` -/
  | codata {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope} {v : Term 0 []}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
      (hp : ps.length = decl.grades) (hv : v = .inst D qs ls ps as)
      (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
      (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
      (S : (Name → RunRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → RunObsRel)
      (hS : ∀ X, ∀ T' ∈ decl.codataTypes,
        RunDesRel sig ι P n below T'.name
          (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S X T')) :
      RunUnivRel sig ι P n below v (CodataType.runBlockRel decl.codataTypes S D)

-- ADE: none.
/--
`rt(U_n)` for the telescopes: `Θ` is a closed telescope in `U_n`, whose terms of the entries are
related to addresses by `S` at run time; the relation of the rest of the telescope is given for each
term that the equality gives to the first entry, which the rest depends on even when it is erased.
The entries at the positions `i` where `rs i` is `R` are recursive fields, related by `R`, given
rather than computed, and on which the rest does not depend; a telescope that is not the fields of a
constructor has none, `rs` being `fun _ => none`.
-/
inductive RunTelRel (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (below : LevelRel.Below n) :
    (Nat → Option RunRel) → {ps : List Parameter} → Telescope 0 [] ps → RunFieldsRel → Prop where
  /-- `(rt_Θε)`: the empty telescope.
  RFC: `\mathsf{rt}_{\Theta\varepsilon}` -/
  | nil {rs : Nat → Option RunRel} : RunTelRel sig ι P n below rs .nil RunFieldsRel.nil
  /-- `(rt_Θ,)`: a first type `A ▶ p`, not a recursive field, that computes to a type of a sort that
  `U_n` bounds, whose terms are equal by `F` and related by `R` at run time, so that
  the first term is one that the equality gives to `A`, related by `R` when `p` is used at run time,
  and a rest that is a telescope of run time for each term that the equality gives to `A`.
  RFC: `\mathsf{rt}_{\Theta,}` -/
  | cons {rs : Nat → Option RunRel} {q : Grade} {p : Parameter} {ps : List Parameter}
      {A v : Term 0 []} {Θ : Telescope 0 [.var] ps} {F : TermRel} {R : RunRel}
      (hA : Computesι sig ι A v) (hF : FieldRel sig ι n below .type v F)
      (hR : RunFieldRel sig ι P n below v R) (G : Term 0 [] → RunFieldsRel)
      (hG : ∀ a, F a a →
        RunTelRel sig ι P n below (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a)) (G a))
      (hrs : rs 0 = none) :
      RunTelRel sig ι P n below rs (.cons q p A Θ)
        (RunFieldsRel.cons (fun H t a => F t t ∧ RunRel.atGrade p.usage R H t a) G)
  /-- `(rt_Θrec)`: a first type `A ▶ p` that is a recursive field, whose terms are related by the
  relation `R` that `rs` gives it when `p` is used at run time, and a rest that is the same telescope,
  with the same relation, for every term.
  RFC: `\mathsf{rt}_{\Theta\mathsf{rec}}` -/
  | recursive {rs : Nat → Option RunRel} {q : Grade} {p : Parameter} {ps : List Parameter}
      {A : Term 0 []} {Θ : Telescope 0 [.var] ps} {R : RunRel} (hrs : rs 0 = some R)
      (G : RunFieldsRel)
      (hG : ∀ a, RunTelRel sig ι P n below (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a)) G) :
      RunTelRel sig ι P n below rs (.cons q p A Θ)
        (RunFieldsRel.cons (RunRel.atGrade p.usage R) fun _ => G)

-- ADE: none.
/--
`rt(U_n)` for the destructors: the destructors `d̄` of the codata type `D`, at the closed
substitution `θ` of their scope, are of run time in `U_n`, and the observations of a term and an
address are related by `S`: the arguments of each destructor are a telescope of run time in `U_n`,
its result a type of a sort that `U_n` bounds for the arguments that the equality gives, with its
relation of run time `R t̄`, and the destructors after it are of run time for each abstraction that
the meaning gives to it.
The destructors at the positions `i` where `rs i` is `R` are recursive, whose results are related by
`R`, given rather than computed, and on which the destructors after them do not depend.
The Lean carries the closed substitution of the scope of the destructors, as the equality does.
-/
inductive RunDesRel (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (below : LevelRel.Below n) :
    Name → (Nat → Option RunRel) → {Γ : Scope} → {ns : List Name} → Destructors 0 Γ ns →
      Subst 0 [] Γ → RunObsRel → Prop where
  /-- `(rt_d̄ε)`: no destructor.
  RFC: `\mathsf{rt}_{\bar d\varepsilon}` -/
  | nil {D : Name} {rs : Nat → Option RunRel} {Γ : Scope} {θ : Subst 0 [] Γ} :
      RunDesRel sig ι P n below D rs .nil @θ fun _ _ _ => True
  /-- `(rt_d̄|)`: a destructor `d : (Θ ⊢ B ◀ ψ) ▶ p`, not recursive, whose arguments `Θ[θ]` are a
  telescope in `U_n` with the equality `SΘ` and of run time with the relation `RΘ`, whose result
  type `B[θ, t̄]` computes, at the arguments `t̄` that the equality gives, to a type of a sort that
  `U_n` bounds, with the equality `F t̄` and the relation of run time `R t̄`, so that the observation
  of a term is one that the equality gives to `d`, related by `(®_x̄)` at the case `i` of `d` when `p`
  is used at run time,
  and the destructors after it, of run time for each abstraction `f` that the equality gives to `d`,
  with the relation `G f`.
  RFC: `\mathsf{rt}_{\bar d|}` -/
  | cons {D : Name} {rs : Nat → Option RunRel} {Γ : Scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q χ : Grade}
      {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {SΘ : FieldsRel}
      {RΘ : RunFieldsRel} {i : Nat} (hi : sig.destructorCase D d = some i)
      (hΘ : TelRel sig ι n below .type (fun _ => none) (Θ.subst θ) SΘ)
      (hRΘ : RunTelRel sig ι P n below (fun _ => none) (Θ.subst θ) RΘ)
      (F : Terms 0 [] → TermRel) (R : Terms 0 [] → RunRel)
      (hB : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
        ∃ v, Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v)
      (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ v,
        Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v →
          FieldRel sig ι n below .type v (F ts.terms))
      (hR : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ v,
        Computesι sig ι (B.subst (Subst.append θ ts.toSubst)) v →
          RunFieldRel sig ι P n below v (R ts.terms))
      (G : Term 0 (Scope.extend [] ps.length) → RunObsRel)
      (hG : ∀ f, AbstractionRel SΘ F f f →
        RunDesRel sig ι P n below D (fun i => rs (i + 1)) ds (Subst.snoc θ f) (G f))
      (hrs : rs 0 = none) :
      RunDesRel sig ι P n below D rs (.cons (d := d) p q χ Θ B ψ ds) @θ fun H o a =>
        AbstractionRel SΘ F (o d ps) (o d ps) ∧
          (p ∉ Mode.oneOne.erased → RunAbstractionRel P i ψ χ RΘ R (o d ps) H a) ∧ G (o d ps) H o a
  /-- `(rt_d̄rec)`: a recursive destructor `d : (Θ ⊢ B ◀ ψ) ▶ p`, whose arguments `Θ[θ]` are a
  telescope of run time in `U_n` with the relation `RΘ`, whose results are related by the relation
  `R` that `rs` gives it, by `(®_x̄)` at the case `i` of `d`, when `p` is used at run time, and the destructors after it, the same, with
  the same relation, for every abstraction for it.
  RFC: `\mathsf{rt}_{\bar d\mathsf{rec}}` -/
  | recursive {D : Name} {rs : Nat → Option RunRel} {Γ : Scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q χ : Grade}
      {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {RΘ : RunFieldsRel}
      {R : RunRel} {i : Nat} (hi : sig.destructorCase D d = some i) (hrs : rs 0 = some R)
      (hRΘ : RunTelRel sig ι P n below (fun _ => none) (Θ.subst θ) RΘ) (G : RunObsRel)
      (hG : ∀ f, RunDesRel sig ι P n below D (fun i => rs (i + 1)) ds (Subst.snoc θ f) G) :
      RunDesRel sig ι P n below D rs (.cons (d := d) p q χ Θ B ψ ds) @θ fun H o a =>
        (p ∉ Mode.oneOne.erased → RunAbstractionRel P i ψ χ RΘ (fun _ => R) (o d ps) H a) ∧ G H o a

-- ADE: none.
/--
The canonical type `v` of a field, or of the result of a destructor, is a type of a sort that `U_n`
bounds, whose closed terms are related at run time by `R`: a type of `U_n` or of a universe below
it, or a proposition of `Ω_n` or of a universe below it, whose terms are related to every address.
RFC: `\mathsf{rt}_\Downarrow`
-/
inductive RunFieldRel (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (below : LevelRel.Below n) : Term 0 [] → RunRel → Prop where
  /-- A type of `U_n`. -/
  | univ {v : Term 0 []} {R : RunRel} (h : RunUnivRel sig ι P n below v R) :
      RunFieldRel sig ι P n below v (R.computed sig ι)
  /-- A type of `U_m`, for `m < n`. -/
  | univBelow {v : Term 0 []} {R : RunRel} (m : Nat) (hm : m < n) (h : (below m hm).run P v R) :
      RunFieldRel sig ι P n below v (R.computed sig ι)
  /-- A proposition of `Ω_n`. -/
  | prop {v : Term 0 []} {b : Prop} (h : PropRel sig ι n below v b) :
      RunFieldRel sig ι P n below v fun _ _ _ => True
  /-- A proposition of `Ω_m`, for `m < n`. -/
  | propBelow {v : Term 0 []} {b : Prop} (m : Nat) (hm : m < n) (h : (below m hm).prop v b) :
      RunFieldRel sig ι P n below v fun _ _ _ => True

end

end Sic.Core
