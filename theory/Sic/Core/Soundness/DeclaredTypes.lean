module

public import Sic.Core.Meaning
public import Sic.Core.Nesting.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Soundness of the Declared Types

The rules of the declared types of annex 15 of RFC 36 keep the meaning of annex 21: an instance of a
declared type is a type of the sort of its declaration, whose fields are those of its declaration at
its levels and its arguments, and equal arguments give instances with the same equality of their
canonical terms, or the same truth.
The proofs take the premises at two equal closed substitutions of the context, as those of `Rules`.

ADE have no declared types: their types are those of the theory.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Levels Without Variables

The meaning of a type declaration holds at the values of its levels, which the proofs on its data
types and its codata types read at the values of levels without variables: the facts that relate
the two are stated once, for every instance of the declaration at equal arguments of its
parameters. -/

-- ADE: none.
/-- The instance of a type of a block at the parameters themselves, at the values of the levels
`ls`, substituted by the arguments `ā`, is the instance of the type at `ls` and `ā`, up to the
levels. -/
theorem TypeDeclaration.blockInstance_atLevels_subst (decl : TypeDeclaration) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 [] decl.scope) (D : Name) :
    Term.LevelEquiv (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst) (.inst D qs ls ps as) := by
  show Term.LevelEquiv (.inst D (List.ofFn (qs.getFin hq))
    ((List.ofFn Level.var).map (Level.subst fun i => Level.ofNat (ls.getFin hl i).closedValue))
    (List.ofFn (ps.getFin hp))
    (((InstanceArgs.identity decl.scope).substLevels
      fun i => Level.ofNat (ls.getFin hl i).closedValue).subst as.toSubst)) _
  rw [List.ofFn_getFin, List.ofFn_getFin, InstanceArgs.identity_substLevels,
    InstanceArgs.identity_subst_toSubst]
  exact .inst D qs ps (Level.ListEquiv.of_getFin (by simp) hl fun i => by
      simp only [List.getFin, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Fin.val_cast,
        Level.subst]
      exact Level.ofNat_closedValue _) (InstanceArgs.LevelEquiv.refl as)

-- ADE: none.
/-- The facts of a type declaration at the values of levels `ls` without variables, at equal
arguments `a₁` and `a₂` of its parameters. -/
structure TypeDeclaration.AtClosedLevels (sig : Signature) (ι : Interpretation)
    (decl : TypeDeclaration) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (a₁ a₂ : InstanceArgs 0 [] decl.scope) : Prop where
  /-- The numerals of the values of `ls` are equal to `ls` up to their levels. -/
  levels : ∀ i, (Level.ofNat (ls.getFin hl i).closedValue : Level 0) ≈ ls.getFin hl i
  /-- The destructors of each codata type of the block are meaningful at the values of `ls`, at
  `a₁` and `a₂`. -/
  destructors : ∀ T ∈ decl.codataTypes,
    ValidEqDestructors₀ sig ι
      ((decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue)
      (fun D => (decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue)
      ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names)
      ((T.body (.ofLists qs ps hq hp)).nestedAt (Nesting.ofPositive T.positive))
      ((T.body (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue)
      a₁.toSubst a₂.toSubst
  /-- The fields of each constructor of each data type of the block are meaningful at the values
  of `ls`, at `a₁` and `a₂`. -/
  fields : ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
    ValidEqFields₀ sig ι
      ((decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue)
      decl.names
      (fun D => ((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst a₁.toSubst)
      (fun D => ((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst a₂.toSubst)
      ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names)
      (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst a₁.toSubst)
      (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst a₂.toSubst)
  /-- The level of the sort has the same value at the values of `ls` and at `ls`. -/
  sort : ((decl.sort (.ofLists qs ps hq hp)).atLevels
      fun i => (ls.getFin hl i).closedValue).level.closedValue =
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
  /-- The instances of the block at the values of `ls`, at any arguments, are equal to those at
  `ls` up to their levels. -/
  instances : ∀ (a : InstanceArgs 0 [] decl.scope) D, Term.LevelEquiv
    (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
      fun i => (ls.getFin hl i).closedValue).subst a.toSubst) (.inst D qs ls ps a)
  /-- The fields of a constructor at the values of `ls`, at any arguments, are equal to those at
  `ls` up to their levels. -/
  telescopes : ∀ (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
      (a : InstanceArgs 0 [] decl.scope),
    Telescope.LevelEquiv (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst a.toSubst)
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) a)
  /-- The instances of the block at the values of `ls`, at any arguments, compute to
  themselves. -/
  computes : ∀ (a : InstanceArgs 0 [] decl.scope) D, Computesι sig ι
    (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
      fun i => (ls.getFin hl i).closedValue).subst a.toSubst)
    (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
      fun i => (ls.getFin hl i).closedValue).subst a.toSubst)
  /-- A relation of the destructors of a codata type of the block at `ls` is one at the values of
  `ls`. -/
  desRel : ∀ {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {n : Nat} {s : Quality}
      {rs : Nat → Option TermRel} {θ : Subst 0 [] decl.scope} {S : ObsRel},
    DesRel sig ι n (fun m _ => levelRel sig ι m) s rs
        ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) θ S →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rs
        ((T.body (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue) θ S
  /-- A relation of run time of the destructors of a codata type of the block at `ls` is one at
  the values of `ls`. -/
  runDesRel : ∀ {P : Program} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
      {n : Nat} {D : Name} {rs : Nat → Option RunRel} {θ : Subst 0 [] decl.scope} {S : RunObsRel},
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs
        ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) θ S →
      RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs
        ((T.body (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue) θ S

-- ADE: none.
/-- A meaningful type declaration, at equal arguments of its parameters, has its facts at the values
of levels without variables, in a signature whose names are distinct. -/
theorem ValidTypeDeclaration.atClosedLevels (hd : sig.Distinct) {decl : TypeDeclaration}
    (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) (hadm : decl.constraint (.ofLists qs ps hq hp))
    {a₁ a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      a₁.toSubst a₂.toSubst) :
    decl.AtClosedLevels sig ι hq hl hp a₁ a₂ :=
  have hls : ∀ i, (Level.ofNat (ls.getFin hl i).closedValue : Level 0) ≈ ls.getFin hl i :=
    fun _ => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  { levels := hls
    destructors := fun _ hT => (hv.destructors _ hadm hT _).2 _ _ hθ
    fields := fun _ hT _ hc => (hv.fields _ hadm hT hc _).2 _ _ hθ
    sort := Level.closedValue_subst_equiv hls _
    instances := fun a D => decl.blockInstance_atLevels_subst hq hl hp a D
    telescopes := fun _ _ => (Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _)
    computes := fun _ _ => (Whnf.inst ..).computes
    desRel := fun hS => DesRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
    runDesRel := fun hS => RunDesRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _) }

section

variable {decl : TypeDeclaration} {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
  {hq : qs.length = decl.sorts} {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {a₁ a₂ : InstanceArgs 0 [] decl.scope}

-- ADE: none.
/-- The fields of a constructor at the values of the levels `ls`, at arguments `ā`, telescopes of
the graph of a sort at the value of its level there, whose positions hold the instances of the
block there, are telescopes of the graph at `ls`, whose positions hold the instances at `ls`, with
the same equality of their terms, in a signature whose names are distinct. -/
theorem TypeDeclaration.AtClosedLevels.telRel (hd : sig.Distinct)
    (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂)
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope}
    {as : InstanceArgs 0 [] decl.scope} {s : Quality} {Rf : Name → TermRel} {S : FieldsRel}
    (h : TelRel sig ι (((decl.sort (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).level.closedValue)
      (fun m _ => levelRel sig ι m) s
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map fun D =>
        (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
          fun i => (ls.getFin hl i).closedValue).subst as.toSubst, Rf D))
      (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst) S) :
    TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) s
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
        fun D => (.inst D qs ls ps as, Rf D))
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) S :=
  hA.sort ▸ TelRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) h (hA.telescopes c as)
    (fun _ => Nest.map_rel₃ (r := fun (x y _ : NestLeaf) => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2)
      (f := fun D => (((decl.blockInstance (.ofLists qs ps hq hp) D
        (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
        as.toSubst, Rf D))
      (g := fun D => (.inst D qs ls ps as, Rf D)) (h := fun D => (.inst D qs ls ps as, Rf D))
      (fun D => ⟨hA.instances as D, rfl⟩) _)

-- ADE: none.
/-- The fields of a constructor at the values of the levels `ls`, at arguments `ā`, telescopes of
the graph of run time of a sort at the value of its level there, whose positions hold the
instances of the block there, are telescopes of the graph at `ls`, whose positions hold the
instances at `ls`, with the same relation of their terms, in a signature whose names are
distinct. -/
theorem TypeDeclaration.AtClosedLevels.runTelRel (hd : sig.Distinct)
    (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂) {P : Program}
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope}
    {as : InstanceArgs 0 [] decl.scope} {Rf : Name → RunRel} {S : RunFieldsRel}
    (h : RunTelRel sig ι P (((decl.sort (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).level.closedValue)
      (fun m _ => levelRel sig ι m)
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map fun D =>
        (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
          fun i => (ls.getFin hl i).closedValue).subst as.toSubst, Rf D))
      (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst) S) :
    RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m)
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
        fun D => (.inst D qs ls ps as, Rf D))
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) S :=
  hA.sort ▸ RunTelRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) h
    (hA.telescopes c as)
    (fun _ => Nest.map_rel₃ (r := fun (x y _ : RunNestLeaf) => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2)
      (f := fun D => (((decl.blockInstance (.ofLists qs ps hq hp) D
        (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
        as.toSubst, Rf D))
      (g := fun D => (.inst D qs ls ps as, Rf D)) (h := fun D => (.inst D qs ls ps as, Rf D))
      (fun D => ⟨hA.instances as D, rfl⟩) _)

-- ADE: none.
/-- Two closed substitutions are equal for the fields of a constructor at the values of the levels
`ls`, at arguments `ā`, if and only if they are equal for its fields at `ls`. -/
theorem TypeDeclaration.AtClosedLevels.eqSubst_fields (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂)
    (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
    (as : InstanceArgs 0 [] decl.scope) {σ₁ σ₂ : Subst 0 [] _} :
    EqSubst sig ι (Context.empty.append (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)) σ₁ σ₂ ↔
      EqSubst sig ι (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
        σ₁ σ₂ :=
  ⟨EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hA.telescopes c as)),
    EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hA.telescopes c as).symm)⟩

-- ADE: none.
/-- Two closed substitutions are equal for the arguments `Θ` of a destructor of a codata type at
the numerals of the values of the levels `ls`, at a substitution `σ` of its scope, if and only if
they are equal for them at `ls`. -/
theorem TypeDeclaration.AtClosedLevels.eqSubst_destructor
    (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂) {Ξ : Scope} {ps' : List Parameter}
    (Θ : Telescope decl.levels Ξ ps') (σ : Subst 0 [] Ξ) {σ₁ σ₂ : Subst 0 [] _} :
    EqSubst sig ι (Context.empty.append
        ((Θ.substLevels fun i => Level.ofNat (ls.getFin hl i).closedValue).subst σ)) σ₁ σ₂ ↔
      EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst σ)) σ₁ σ₂ :=
  ⟨EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hA.levels Θ))),
    EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hA.levels Θ)).symm)⟩

-- ADE: none.
/-- The positions of the fields of a constructor of a block of data types, at the values of the
levels `ls` and at arguments `ā`, hold the instances of the block there, which the graph of run
time relates by relations `X`, when the instances at `ls` are types of a universe with these
relations, in a signature whose names are distinct. -/
theorem TypeDeclaration.AtClosedLevels.runNestRel_instances (hd : sig.Distinct)
    (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂) {P : Program}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
    {as : InstanceArgs 0 [] decl.scope} {X : Name → RunRel}
    (hU : ∀ T' ∈ decl.dataTypes,
      RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as) (X T'.name)) :
    ∀ j, Nest.All
      (fun x : RunNestLeaf => RunNestRel sig ι P
        (((decl.sort (.ofLists qs ps hq hp)).atLevels
          fun i => (ls.getFin hl i).closedValue).level.closedValue)
        (fun m _ => levelRel sig ι m) .plain x.1 x.2)
      (((c.fields (.ofLists qs ps hq hp)).nestAt decl.names j).map fun D' =>
          (((decl.blockInstance (.ofLists qs ps hq hp) D' (.identity decl.scope)).atLevels
            fun i => (ls.getFin hl i).closedValue).subst as.toSubst,
            (X D').computed sig ι)) := fun j =>
  Nest.All.map_rel₃ (fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
      exact hA.sort ▸ RunNestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m)
        (.plain (Whnf.inst ..).computes (.univ (hU T' hT'))) (hA.instances as T'.name).symm .plain)
    (Telescope.nestAt_all decl.names _ j)

end

/-! ## Declared Types

An instance of a declared type is a type of the sort of its declaration, whose fields are those of
its declaration at its levels and its arguments: the meaning of the declaration makes them closed
telescopes equal in this sort for equal arguments, which the graph of the sort gives the same
equality of their terms, so that equal arguments give instances with the same equality of their
canonical terms, or the same truth.

The equality of the terms of the rest of a telescope is the one that the graph gives it at each
term of its first type: it is defined from the graph, as the relation that some equality of the
terms of the rest relates, rather than chosen among them, since the graph gives one at most.
The instance at levels of the same values then follows as for the constants. -/

/-- Two equal closed terms of a sort `κ₁` that the sort of the quality `s` at the level `n` bounds,
as `(⊨tel_κ,)` gives the types of the first fields of two equal closed telescopes, compute to types
of the fields of this sort, whose terms are equal by the same `F`: the terms that `F` relates are
equal terms of the first type. -/
theorem ValidEqTerm₀.fieldRel {A₁ A₂ : Term 0 []} {κ₁ : Universe 0} {n : Nat} {s : Quality}
    (hκs : κ₁.quality ≤ s) (hκn : κ₁.level.closedValue ≤ n)
    (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) :
    ∃ w₁ w₂ F, Computesι sig ι A₁ w₁ ∧ Computesι sig ι A₂ w₂ ∧
      FieldRel sig ι n (fun m _ => levelRel sig ι m) s w₁ F ∧
      FieldRel sig ι n (fun m _ => levelRel sig ι m) s w₂ F ∧
      ∀ a₁ a₂, F a₁ a₂ → ValidEqTerm₀ sig ι a₁ a₂ A₁ := by
  obtain ⟨s₁, l₁⟩ := κ₁
  have hd := h.1.1
  have hm : l₁.closedValue ≤ n := hκn
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ k hk =>
    cases levelRel_univ_iff.1 hk with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      subst hl
      obtain ⟨⟨R', h₁, h₂⟩, -⟩ := hvw
      have hs : s = .type := by
        cases hq : s with
        | type => rfl
        | prop => exact nomatch hκs hq
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).univ w R' →
          FieldRel sig ι n (fun m _ => levelRel sig ι m) s w
            (R'.computed sig ι) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .univBelow hs _ hlt hw
        · exact .univ hs (heq ▸ levelRel_univ_iff.1 hw)
      refine ⟨w₁, w₂, R'.computed sig ι, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ ⟨v, w, ha₁, ha₂, hR'⟩ => ⟨(ValidEqTerm₀.univType h).left, fun _ =>
          ⟨w₁, v, w, R', hw₁, ha₁, ha₂, .univ _ h₁, hR'⟩,
          fun hp => (Computesι.not_computesToProp hd hw₁ h₁ hp).elim⟩⟩
    | prop hl _ =>
      subst hl
      obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := hvw
      cases propext hb
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).prop w b₁ →
          FieldRel sig ι n (fun m _ => levelRel sig ι m) s w
            (fun _ _ => b₁) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .propBelow _ hlt hw
        · exact .prop (heq ▸ levelRel_prop_iff.1 hw)
      refine ⟨w₁, w₂, fun _ _ => b₁, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ hb₁ => ⟨(ValidEqTerm₀.propType h).left, fun hn => absurd ⟨w₁, hw₁, _, _, h₁⟩ hn,
          fun _ => ⟨w₁, fun _ _ => b₁, hw₁, .prop _ b₁ h₁ fun _ _ => .rfl, hb₁⟩⟩⟩

/-- Two equal closed terms of a sort `κ₁` whose level the level `n` bounds compute to types with a
common relation of run time `R` of the graph of `U_n`, for each program `P`: the relation that the
equality of `U_n` gives them, or the one of the propositions. -/
theorem ValidEqTerm₀.runFieldRel (P : Program) {A₁ A₂ : Term 0 []} {κ₁ : Universe 0} {n : Nat}
    (hκn : κ₁.level.closedValue ≤ n) (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) :
    ∃ w₁ w₂ R, Computesι sig ι A₁ w₁ ∧ Computesι sig ι A₂ w₂ ∧
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w₁ R ∧
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w₂ R := by
  obtain ⟨s₁, l₁⟩ := κ₁
  have hm : l₁.closedValue ≤ n := hκn
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ k hk =>
    cases levelRel_univ_iff.1 hk with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      subst hl
      obtain ⟨-, hr⟩ := hvw
      obtain ⟨Q, h₁, h₂⟩ := hr P
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).run P w Q →
          RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w
            (Q.computed sig ι) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .univBelow _ hlt hw
        · exact .univ (heq ▸ levelRel_run_iff.1 hw)
      exact ⟨w₁, w₂, _, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂⟩
    | prop hl _ =>
      subst hl
      obtain ⟨b₁, b₂, h₁, h₂, -⟩ := hvw
      have hF : ∀ w b, (levelRel sig ι l₁.closedValue).prop w b →
          RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w
            fun _ _ _ => True := fun w b hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .propBelow _ hlt hw
        · exact .prop (heq ▸ levelRel_prop_iff.1 hw)
      exact ⟨w₁, w₂, _, hw₁, hw₂, hF w₁ b₁ h₁, hF w₂ b₂ h₂⟩

/-- Two closed telescopes equal in the sort `κ` are equal fields without position. -/
theorem ValidEqTelescope₀.toFields {κ : Universe 0} (names : List Name)
    (inst₁ inst₂ : Name → Term 0 []) :
    {ps : List Parameter} → {Θ₁ Θ₂ : Telescope 0 [] ps} → ValidEqTelescope₀ sig ι κ Θ₁ Θ₂ →
      ValidEqFields₀ sig ι κ names inst₁ inst₂ (fun _ => .plain) Θ₁ Θ₂
  | [], .nil, .nil, h => h
  | _ :: _, .cons _ _ _ _, .cons _ _ _ _, h => by
    rw [ValidEqTelescope₀] at h
    rw [ValidEqFields₀]
    exact ⟨h.1, fun v₁ v₂ hv => ValidEqTelescope₀.toFields names inst₁ inst₂ (h.2 v₁ v₂ hv)⟩

/-- Two closed fields equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, whatever the relations `Rf D` given at the positions of
their nestings for the instances of the type `D`, in a signature whose names are distinct: the
equality of the rest after a field whose nesting has a position, on which it does not depend, is
the one at any term. -/
theorem ValidEqFields₀.telRel (hd : sig.Distinct) {κ : Universe 0} {names : List Name}
    {inst₁ inst₂ : Name → Term 0 []} (Rf : Name → TermRel) :
    {ps : List Parameter} → {rs : Nat → Nest Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ names inst₁ inst₂ rs Θ₁ Θ₂ →
      ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map fun D => (inst₁ D, Rf D)) Θ₁ S ∧
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map fun D => (inst₂ D, Rf D)) Θ₂ S
  | [], _, .nil, .nil, _ => ⟨FieldsRel.nil, .nil, .nil⟩
  | _ :: _, rs, .cons q₁ p A₁ Θ₁, .cons q₂ _ A₂ Θ₂, h => by
    have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd) κ.level.closedValue
    -- A first field whose nesting has a position, read by the graph of the nestings, and a rest
    -- that does not depend on it.
    have hnested : rs 0 ≠ .plain →
        (∃ F, NestRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality κ.quality
            ((rs 0).map fun D => (inst₁ D, Rf D)) A₁ F ∧
          NestRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality κ.quality
            ((rs 0).map fun D => (inst₂ D, Rf D)) A₂ F) →
        (∀ v₁ v₂, ValidEqFields₀ sig ι κ names inst₁ inst₂ (fun i => rs (i + 1))
          (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))) →
        ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs i).map fun D => (inst₁ D, Rf D)) (.cons q₁ p A₁ Θ₁) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs i).map fun D => (inst₂ D, Rf D)) (.cons q₂ p A₂ Θ₂) S := by
      intro hr ⟨F, hF₁, hF₂⟩ hΘ
      let a₀ : Term 0 [] := .sort ⟨.type, .zero⟩
      have hcommon : ∀ a₁ a₂, ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map fun D => (inst₂ D, Rf D))
            (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂)
      obtain ⟨G, h₀₁, h₀₂⟩ := hcommon a₀ a₀
      refine ⟨FieldsRel.cons F fun _ => G,
        .nested (fun h => hr (Nest.map_eq_plain.1 h)) hF₁ G fun a => ?_,
        .nested (fun h => hr (Nest.map_eq_plain.1 h)) hF₂ G fun a => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a₀
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₂ _ _ h₀₂ ts us)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a₀ a
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₁ _ _ h₀₁ ts us)
        exact hSG ▸ h₂
    rw [ValidEqFields₀] at h
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
      obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ.1 (hκ.2 Fin.elim0)
      have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map fun D => (inst₂ D, Rf D))
            (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ ha => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂ (hFv a₁ a₂ ha))
      let G : Term 0 [] → FieldsRel := fun a ts us => ∃ S,
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a)) S ∧ S ts us
      have hG : ∀ a S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a)) S → G a = S :=
        fun a S hS => funext fun ts => funext fun us => propext
          ⟨fun ⟨_, hS', hs⟩ => (TelRel.unique hd ih hS' _ _ hS ts us).1 hs, fun hs => ⟨S, hS, hs⟩⟩
      have hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us := fun a₁ a₂ ha ts us => by
        have hFp := FieldRel.isPer hd ih hF₁
        obtain ⟨S, h₁, h₂⟩ := hcommon a₁ a₂ ha
        obtain ⟨S', h₁', h₂'⟩ := hcommon a₂ a₂ (hFp.trans (hFp.symm ha) ha)
        rw [hG a₁ S h₁, hG a₂ S' h₁']
        exact TelRel.unique hd ih h₂ _ _ h₂' ts us
      refine ⟨FieldsRel.cons F G,
        .cons hc₁ hF₁ G (fun a ha => ?_) hresp (by show (rs 0).map _ = _; rw [hr]; rfl),
        .cons hc₂ hF₂ G (fun a ha => ?_) hresp (by show (rs 0).map _ = _; rw [hr]; rfl)⟩
      · obtain ⟨S, h₁, -⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₂
    · rename_i D hr
      obtain ⟨hA₁, hA₂, hΘ⟩ := h
      refine hnested (fun h => nomatch hr.symm.trans h) ⟨Rf D, ?_, ?_⟩ hΘ
      · rw [hr, hA₁]
        exact .direct rfl (Term.LevelEquiv.refl _)
      · rw [hr, hA₂]
        exact .direct rfl (Term.LevelEquiv.refl _)
    · rename_i νs hr
      obtain ⟨hN, -, -, hΘ⟩ := h
      exact hnested (fun h => nomatch hr.symm.trans h) (hr ▸ hN Rf) hΘ

/-- Two closed telescopes equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.telRel (hd : sig.Distinct) {κ : Universe 0} {ps : List Parameter}
    {Θ₁ Θ₂ : Telescope 0 [] ps} (h : ValidEqTelescope₀ sig ι κ Θ₁ Θ₂) :
    ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => .plain)
        Θ₁ S ∧
      TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => .plain)
        Θ₂ S :=
  ValidEqFields₀.telRel hd (fun _ _ _ => False) (h.toFields [] (fun _ => .sort ⟨.type, .zero⟩)
    (fun _ => .sort ⟨.type, .zero⟩))

/-- Two closed fields equal in a sort `κ` of types are telescopes of the graph of run time of `U_n`,
at the level `n` of `κ`, with the same relation of run time of the terms of their fields, for each
program `P`, whatever the relations `Rf D` given at the positions of their nestings for the
instances of the type `D`, in a signature whose names are distinct: the relation of the rest is
defined from the graph at the first telescope, rather than chosen, since the graph gives one at
most, and after a field whose nesting has a position, on which the rest does not depend, it is the
one at any term. -/
theorem ValidEqFields₀.runTelRel (hd : sig.Distinct) (P : Program) {κ : Universe 0}
    (hs : κ.quality = .type) {names : List Name} {inst₁ inst₂ : Name → Term 0 []}
    (Rf : Name → RunRel) :
    {ps : List Parameter} → {rs : Nat → Nest Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ names inst₁ inst₂ rs Θ₁ Θ₂ →
      ∃ S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs i).map fun D => (inst₁ D, Rf D)) Θ₁ S ∧
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs i).map fun D => (inst₂ D, Rf D)) Θ₂ S
  | [], _, .nil, .nil, _ => ⟨RunFieldsRel.nil, .nil, .nil⟩
  | _ :: _, rs, .cons q₁ p A₁ Θ₁, .cons q₂ _ A₂ Θ₂, h => by
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) κ.level.closedValue
    have ih : ∀ m, m < κ.level.closedValue → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have hrr : ∀ (inst : Name → Term 0 []) i,
        Nest.Rel (fun x y : RunNestLeaf => ∀ H t a, x.2 H t a ↔ y.2 H t a)
          ((rs (i + 1)).map fun D => (inst D, Rf D))
          ((rs (i + 1)).map fun D => (inst D, Rf D)) :=
      fun _ _ => Nest.rel₃_refl (fun _ _ _ _ => .rfl) _
    -- A first field whose nesting has a position, read by the graph of the nestings, and a rest
    -- that does not depend on it.
    have hnested : rs 0 ≠ .plain →
        (∃ R, RunNestRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            ((rs 0).map fun D => (inst₁ D, Rf D)) A₁ R ∧
          RunNestRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            ((rs 0).map fun D => (inst₂ D, Rf D)) A₂ R) →
        (∀ v₁ v₂, ValidEqFields₀ sig ι κ names inst₁ inst₂ (fun i => rs (i + 1))
          (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))) →
        ∃ S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs i).map fun D => (inst₁ D, Rf D)) (.cons q₁ p A₁ Θ₁) S ∧
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs i).map fun D => (inst₂ D, Rf D)) (.cons q₂ p A₂ Θ₂) S := by
      intro hr ⟨R, hR₁, hR₂⟩ hΘ
      let a₀ : Term 0 [] := .sort ⟨.type, .zero⟩
      have hcommon : ∀ a₁ a₂, ∃ S,
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map fun D => (inst₂ D, Rf D))
            (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ => ValidEqFields₀.runTelRel hd P hs Rf (hΘ a₁ a₂)
      obtain ⟨G, h₀₁, h₀₂⟩ := hcommon a₀ a₀
      refine ⟨RunFieldsRel.cons (RunRel.atGrade _ R) fun _ => G,
        .nested (fun h => hr (Nest.map_eq_plain.1 h)) hR₁ G fun a => ?_,
        .nested (fun h => hr (Nest.map_eq_plain.1 h)) hR₂ G fun a => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a₀
        have hSG : S = G := funext fun H => funext fun ts => funext fun bs => propext
          (RunTelRel.congr hd ihm ih h₂ _ _ h₀₂ (hrr inst₂) H ts bs)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a₀ a
        have hSG : S = G := funext fun H => funext fun ts => funext fun bs => propext
          (RunTelRel.congr hd ihm ih h₁ _ _ h₀₁ (hrr inst₁) H ts bs)
        exact hSG ▸ h₂
    rw [ValidEqFields₀] at h
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
      obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ.1 (hκ.2 Fin.elim0)
      obtain ⟨w₁', w₂', R, hc₁', hc₂', hR₁, hR₂⟩ := hA.runFieldRel P (hκ.2 Fin.elim0)
      cases Computesι.det hd hc₁ hc₁'
      cases Computesι.det hd hc₂ hc₂'
      rw [hs] at hF₁ hF₂
      have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map fun D => (inst₂ D, Rf D))
            (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ ha => ValidEqFields₀.runTelRel hd P hs Rf (hΘ a₁ a₂ (hFv a₁ a₂ ha))
      let G : Term 0 [] → RunFieldsRel := fun a H ts bs => ∃ S,
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a)) S ∧ S H ts bs
      have hG : ∀ a S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs (i + 1)).map fun D => (inst₁ D, Rf D))
            (Θ₁.subst₀ (Subst₀.single a)) S → G a = S :=
        fun a S hS => funext fun H => funext fun ts => funext fun bs => propext
          ⟨fun ⟨_, hS', hs⟩ => (RunTelRel.congr hd ihm ih hS' _ _ hS (hrr inst₁) H ts bs).1 hs,
            fun hs => ⟨S, hS, hs⟩⟩
      refine ⟨_,
        .cons hc₁ hF₁ hR₁ G (fun a ha => ?_) (by show (rs 0).map _ = _; rw [hr]; rfl),
        .cons hc₂ hF₂ hR₂ G (fun a ha => ?_) (by show (rs 0).map _ = _; rw [hr]; rfl)⟩
      · obtain ⟨S, h₁, -⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₂
    · rename_i D hr
      obtain ⟨hA₁, hA₂, hΘ⟩ := h
      refine hnested (fun h => nomatch hr.symm.trans h) ⟨Rf D, ?_, ?_⟩ hΘ
      · rw [hr, hA₁]
        exact .direct (Term.LevelEquiv.refl _)
      · rw [hr, hA₂]
        exact .direct (Term.LevelEquiv.refl _)
    · rename_i νs hr
      obtain ⟨-, hN, -, hΘ⟩ := h
      exact hnested (fun h => nomatch hr.symm.trans h) (hr ▸ hN hs P Rf) hΘ

/-- Two closed telescopes equal in a sort `κ` of types are telescopes of the graph of run time of
`U_n`, at the level `n` of `κ`, with the same relation of run time of the terms of their fields, for
each program `P`, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.runTelRel (hd : sig.Distinct) (P : Program) {κ : Universe 0}
    (hs : κ.quality = .type) {ps : List Parameter} {Θ₁ Θ₂ : Telescope 0 [] ps}
    (h : ValidEqTelescope₀ sig ι κ Θ₁ Θ₂) :
    ∃ S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => .plain) Θ₁
        S ∧
      RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => .plain) Θ₂
        S :=
  ValidEqFields₀.runTelRel hd P hs (fun _ _ _ _ => False)
    (h.toFields [] (fun _ => .sort ⟨.type, .zero⟩) (fun _ => .sort ⟨.type, .zero⟩))

-- ADE: none.
/-- The types of the fields of a closed telescope at the positions that `nested` holds of, those
whose nesting is that of an instance, are terms of a sort that the sort of the quality `s` at the
level `n` bounds, the rest being so at every term of each field: the graph of the nestings does not
tell that such a type is a type without position, which the meaning of a declaration does. -/
def Telescope.NestHeads (sig : Signature) (ι : Interpretation) (n : Nat) (s : Quality) :
    {ps : List Parameter} → (Nat → Prop) → Telescope 0 [] ps → Prop
  | [], _, .nil => True
  | _ :: _, nested, .cons _ _ A Θ =>
    (nested 0 → ∃ κ₁ : Universe 0, κ₁.quality ≤ s ∧ κ₁.level.closedValue ≤ n ∧
      ValidEqTerm₀ sig ι A A (.sort κ₁)) ∧
    ∀ a, ValidEqTerm₀ sig ι a a A →
      Telescope.NestHeads sig ι n s (fun i => nested (i + 1)) (Θ.subst₀ (Subst₀.single a))

/-- A telescope none of whose positions is that of an instance has nothing to tell of them. -/
theorem Telescope.nestHeads_of_not {n : Nat} {s : Quality} :
    {ps : List Parameter} → {nested : Nat → Prop} → (Θ : Telescope 0 [] ps) →
      (∀ i, ¬ nested i) → Θ.NestHeads sig ι n s nested
  | [], _, .nil, _ => trivial
  | _ :: _, _, .cons _ _ _ _, h => by
    rw [Telescope.NestHeads]
    exact ⟨fun h₀ => (h 0 h₀).elim, fun _ _ => Telescope.nestHeads_of_not _ fun i => h (i + 1)⟩

/-- A telescope that has what there is to tell of some of its positions has it of fewer. -/
theorem Telescope.NestHeads.imp {n : Nat} {s : Quality} :
    {ps : List Parameter} → {nested nested' : Nat → Prop} → {Θ : Telescope 0 [] ps} →
      Θ.NestHeads sig ι n s nested → (∀ i, nested' i → nested i) → Θ.NestHeads sig ι n s nested'
  | [], _, _, .nil, _, _ => trivial
  | _ :: _, _, _, .cons _ _ _ _, h, hi => by
    rw [Telescope.NestHeads] at h ⊢
    exact ⟨fun h₀ => h.1 (hi 0 h₀), fun a ha => (h.2 a ha).imp fun i => hi (i + 1)⟩

/-- The types of the nested fields of two closed fields equal in the sort `κ` are terms of a sort
that `κ` bounds, when the instances of the types of the block are equal types of `κ`, as the
meaning of the nested fields tells. -/
theorem ValidEqFields₀.nestHeads {κ : Universe 0} {names : List Name}
    {inst₁ inst₂ : Name → Term 0 []} :
    {ps : List Parameter} → {rs : Nat → Nest Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ names inst₁ inst₂ rs Θ₁ Θ₂ →
      (∀ D ∈ names, ValidEqTerm₀ sig ι (inst₁ D) (inst₂ D) (.sort κ)) →
      Θ₁.NestHeads sig ι κ.level.closedValue κ.quality (fun i => ∃ νs, rs i = .inst νs)
  | [], _, .nil, .nil, _, _ => trivial
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂, h, hI => by
    rw [ValidEqFields₀] at h
    rw [Telescope.NestHeads]
    split at h
    · rename_i hr
      exact ⟨fun ⟨_, h'⟩ => (nomatch hr.symm.trans h'), fun a ha =>
        ValidEqFields₀.nestHeads (h.2 a a ha) hI⟩
    · rename_i D hr
      exact ⟨fun ⟨_, h'⟩ => (nomatch hr.symm.trans h'), fun a _ =>
        ValidEqFields₀.nestHeads (h.2.2 a a) hI⟩
    · rename_i νs hr
      obtain ⟨-, -, hS, hΘ⟩ := h
      refine ⟨fun _ => ?_, fun a _ => ValidEqFields₀.nestHeads (hΘ a a) hI⟩
      obtain ⟨κ₁, hκ, hA⟩ := hS hI
      exact ⟨κ₁, hκ.1, hκ.2 Fin.elim0, hA.trans hA.symm⟩

/-- Equal closed terms of a type that computes to a type of a field, whose terms are equal by `F`,
are related by `F`: the converse of the last property of `ValidEqTerm₀.fieldRel`. -/
theorem FieldRel.of_validEqTerm {n : Nat} {s : Quality} {A v t u : Term 0 []} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F) (hA : Computesι sig ι A v)
    (h : ValidEqTerm₀ sig ι t u A) : F t u := by
  have hd := h.1.1
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u := fun m R hR => by
    have hnp := Computesι.not_computesToProp hd hA hR
    obtain ⟨v', w₁, w₂, R', hv', ht, hu, hR', hw⟩ := h.2.1 hnp
    cases Computesι.det hd hA hv'
    exact ⟨w₁, w₂, ht, hu, (HasEq.unique hd hR' (.univ m hR) w₁ w₂).1 hw⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b := fun m b hb => by
    obtain ⟨v', R', hv', hR', hR⟩ := h.2.2 ⟨v, hA, m, b, hb⟩
    cases Computesι.det hd hA hv'
    exact (HasEq.unique hd hR' (.prop m b hb fun _ _ => .rfl) t u).1 hR
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU)
  | univBelow _ m _ hU => exact huniv m _ hU
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP)
  | propBelow m _ hP => exact hprop m _ hP

/-- Two equal closed terms of the type of a field, whose terms are equal by `F`, are related by `F`:
the converse of `FieldRel.of_validEqTerm`. -/
theorem FieldRel.validEqTerm (hd : sig.Distinct) {n : Nat} {s : Quality} {A v t u : Term 0 []}
    {F : TermRel} (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F)
    (hA : Computesι sig ι A v) (htu : F t u) : ValidEqTerm₀ sig ι t u A := by
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u →
      ValidEqTerm₀ sig ι t u A := fun m R hR ⟨w₁, w₂, h₁, h₂, hw⟩ =>
    ⟨⟨hd, v, v, R, hA, hA, .univ m hR, .univ m hR, fun _ _ => .rfl⟩, fun _ => ⟨v, w₁, w₂, R, hA, h₁, h₂, .univ m hR, hw⟩,
      fun hp => (Computesι.not_computesToProp hd hA hR hp).elim⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b → ValidEqTerm₀ sig ι t u A :=
    fun m b hP hb =>
      ⟨⟨hd, v, v, fun _ _ => b, hA, hA, .prop m b hP fun _ _ => .rfl,
        .prop m b hP fun _ _ => .rfl, fun _ _ => .rfl⟩, fun hn => absurd ⟨v, hA, m, b, hP⟩ hn,
        fun _ => ⟨v, fun _ _ => b, hA, .prop m b hP fun _ _ => .rfl, hb⟩⟩
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU) htu
  | univBelow _ m _ hU => exact huniv m _ hU htu
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP) htu
  | propBelow m _ hP => exact hprop m _ hP htu

/-- A type that the graph of the nestings reads, at positions that hold types with the equality of
their terms, is a type without position: the type of the block that a position holds, up to the
values of its levels, and an instance of a declared type when it is a term of a sort that the sort
of the quality `s` at the level `n` bounds, in a signature whose names are distinct. -/
theorem NestRel.plain_of_leaves (hd : sig.Distinct) {n : Nat} {sT s : Quality}
    {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel}
    (h : NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F)
    (hτ : Nest.All
      (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) τ)
    (hA : (∃ νs, τ = .inst νs) → ∃ κ₁ : Universe 0, κ₁.quality ≤ s ∧ κ₁.level.closedValue ≤ n ∧
      ValidEqTerm₀ sig ι A A (.sort κ₁)) :
    ∃ s' F', NestRel sig ι n (fun m _ => levelRel sig ι m) .type s' .plain A F' := by
  have hsort : (∃ κ₁ : Universe 0, κ₁.quality ≤ s ∧ κ₁.level.closedValue ≤ n ∧
      ValidEqTerm₀ sig ι A A (.sort κ₁)) →
      ∃ s' F', NestRel sig ι n (fun m _ => levelRel sig ι m) .type s' .plain A F' :=
    fun ⟨_, hs, hn, hv⟩ =>
      have ⟨_, _, F', hc, _, hF, _, _⟩ := hv.fieldRel hs hn
      ⟨s, F', .plain hc hF⟩
  cases h with
  | plain hc hF => exact ⟨s, F, .plain hc hF⟩
  | direct _ hT =>
    cases hτ with
    | direct hx =>
      exact ⟨.type, _, NestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hx hT .plain⟩
  | codata => exact hsort (hA ⟨_, rfl⟩)
  | codataProp => exact hsort (hA ⟨_, rfl⟩)

/-- The equality that the graph of the nestings gives a type, at positions that hold types with the
equality of their terms, relates the equal terms of the type, and only them, in a signature whose
names are distinct, when the type is a term of a sort if it is an instance of a declared type. -/
theorem NestRel.validEqTerm_iff (hd : sig.Distinct) {n : Nat} {sT s : Quality} {τ : Nest NestLeaf}
    {A : Term 0 []} {F : TermRel} (h : NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F)
    (hτ : Nest.All
      (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) τ)
    (hA : (∃ νs, τ = .inst νs) → ∃ κ₁ : Universe 0, κ₁.quality ≤ s ∧ κ₁.level.closedValue ≤ n ∧
      ValidEqTerm₀ sig ι A A (.sort κ₁)) (t u : Term 0 []) :
    F t u ↔ ValidEqTerm₀ sig ι t u A := by
  obtain ⟨_, _, h'⟩ := h.plain_of_leaves hd hτ hA
  refine (levelRel_nest_agree hd (fun _ _ _ hT hTA =>
    NestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hT hTA .plain) h hτ h' t u).trans ?_
  cases h' with
  | plain hc hF => exact ⟨hF.validEqTerm hd hc, hF.of_validEqTerm hc⟩

/-- Equal closed arguments of a closed telescope of the graph of a sort, whose fields have the
equality `S`, have terms related by `S`, at positions that hold types with the equality of their
terms: the converse of `ValidEqTelescope₀.telRel`, for the arguments. -/
theorem TelRel.of_eqSubst {n : Nat} {s : Quality} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs : Nat → Nest NestLeaf} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S →
      Θ.NestHeads sig ι n s (fun i => ∃ νs, rs i = .inst νs) →
      (∀ i, Nest.All
        (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) (rs i)) →
      (ts us : Args 0 [] ps) →
      EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst → S ts.terms us.terms
  | [], .nil, _, _, .nil, _, _, .nil, .nil, _ => trivial
  | _ :: ps, .cons q p A Θ, _, _, h', hH, hτ, .cons t ts, .cons u us, h => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    have hd : sig.Distinct := ht.1.1
    have htt := ht.trans ht.symm
    rw [Telescope.NestHeads] at hH
    cases h' with
    | cons hA hF G hG _ _ =>
      have hFtu := hF.of_validEqTerm hA ht
      have hFp := FieldRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) hF
      exact ⟨hFtu, TelRel.of_eqSubst (hG t (hFp.trans hFtu (hFp.symm hFtu))) (hH.2 t htt)
        (fun i => hτ (i + 1)) ts us hts⟩
    | nested hrs hF G hG =>
      exact ⟨(hF.validEqTerm_iff hd (hτ 0) hH.1 t u).2 ht, TelRel.of_eqSubst (hG t) (hH.2 t htt)
        (fun i => hτ (i + 1)) ts us hts⟩

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are the terms of equal arguments of the telescope, at positions that hold types with
the equality of their terms: the converse of `TelRel.of_eqSubst`. -/
theorem TelRel.to_eqSubst (hd : sig.Distinct) {n : Nat} {s : Quality} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs : Nat → Nest NestLeaf} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S →
      Θ.NestHeads sig ι n s (fun i => ∃ νs, rs i = .inst νs) →
      (∀ i, Nest.All
        (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) (rs i)) →
      (ts us : Terms 0 []) → S ts us →
        ∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append Θ) ts'.toSubst us'.toSubst
  | [], .nil, _, _, .nil, _, _, .nil, .nil, _ =>
    ⟨.nil, .nil, rfl, rfl, (EqSubst.empty_iff _ _).2 trivial⟩
  | [], .nil, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, _, h', hH, hτ, ts₀, us₀, hS => by
    have key : ∀ t u (ts us : Terms 0 []) (htu : ValidEqTerm₀ sig ι t u A),
        (∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append (Θ.subst₀ (Subst₀.single t))) ts'.toSubst
            us'.toSubst) →
        ∃ ts' us' : Args 0 [] (_ :: ps), ts'.terms = .cons t ts ∧ us'.terms = .cons u us ∧
          EqSubst sig ι (Context.empty.append (.cons q p A Θ)) ts'.toSubst us'.toSubst := by
      intro t u ts us htu ⟨ts', us', h₁, h₂, hτ⟩
      subst h₁ h₂
      exact ⟨.cons t ts', .cons u us', rfl, rfl, EqSubst.args_cons_iff.2 ⟨htu, hτ⟩⟩
    rw [Telescope.NestHeads] at hH
    cases h' with
    | cons hA hF G hG _ _ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) hF
        have hv := hF.validEqTerm hd hA htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t (hFp.trans htu (hFp.symm htu)))
          (hH.2 t (hv.trans hv.symm)) (fun i => hτ (i + 1)) ts us hts)
    | nested hrs hF G hG =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hv : ValidEqTerm₀ sig ι t u A := (hF.validEqTerm_iff hd (hτ 0) hH.1 t u).1 htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t) (hH.2 t (hv.trans hv.symm))
          (fun i => hτ (i + 1)) ts us hts)

/-- The terms `ts₁` and `ts₂` of fields are related by `Q D` at each recursive field of the type `D`
that the types `rs` of the block mark. -/
def Terms.RecRel (Q : Name → TermRel) : List (Option Name) → Terms 0 [] → Terms 0 [] → Prop
  | some D :: rs, .cons t₁ ts₁, .cons t₂ ts₂ => Q D t₁ t₂ ∧ Terms.RecRel Q rs ts₁ ts₂
  | none :: rs, .cons _ ts₁, .cons _ ts₂ => Terms.RecRel Q rs ts₁ ts₂
  | [], _, _ | _ :: _, .nil, _ | _ :: _, .cons _ _, .nil => True

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are related at its recursive fields, which `rs` marks, by the relations `Rf` that the
positions of their nestings hold. -/
theorem TelRel.recRel (hd : sig.Distinct) {n : Nat} {s : Quality} {Rf : Name → TermRel} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Nest NestLeaf} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → (rs : List (Option Name)) →
      (∀ i D, rs[i]?.join = some D → ∃ T, rs' i = .direct (T, Rf D)) →
      (ts us : Terms 0 []) → S ts us →
        Terms.RecRel Rf rs ts us
  | [], .nil, _, _, .nil, rs, _, .nil, .nil, _ => by
    cases rs with
    | nil => trivial
    | cons o _ => cases o <;> trivial
  | [], .nil, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, rs', h', rs, hrs, ts₀, us₀, hS => by
    have htail : ∀ i D, rs.tail[i]?.join = some D → ∃ T, rs' (i + 1) = .direct (T, Rf D) :=
      fun i D h => hrs (i + 1) D (by
        cases rs with
        | nil => exact nomatch h
        | cons _ _ => exact h)
    cases h' with
    | cons hA hF G hG _ hrs₀ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) hF
        have ih := TelRel.recRel hd (hG t (hFp.trans htu (hFp.symm htu))) rs.tail htail ts us hts
        match rs, hrs with
        | [], _ => trivial
        | none :: _, _ => exact ih
        | some D :: _, hrs =>
          obtain ⟨_, hR⟩ := hrs 0 D rfl
          exact nomatch hR.symm.trans hrs₀
    | nested hrs₀ hF G hG =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have ih := TelRel.recRel hd (hG t) rs.tail htail ts us hts
        match rs, hrs with
        | [], _ => trivial
        | none :: _, _ => exact ih
        | some D :: _, hrs =>
          obtain ⟨_, hR⟩ := hrs 0 D rfl
          rw [hR] at hF
          cases hF with
          | direct _ _ => exact ⟨htu, ih⟩

-- ADE: none.
/-- The terms `ts₁` and `ts₂` of the fields of the closed telescope `Θ`, whose nestings are `ns`,
are related, at each field whose nesting has a position, by an equality that the graph of the
nestings of the sort of the quality `s` at the level `n` gives the type of the field, at the terms
`ts₁` of the fields before it, where `L` gives each type of the block its closed instance and the
relation of its terms. -/
def Terms.NestedRel (sig : Signature) (ι : Interpretation) (n : Nat) (s : Quality)
    (L : Name → NestLeaf) :
    List (Nest Name) → {ps : List Parameter} → Telescope 0 [] ps → Terms 0 [] → Terms 0 [] → Prop
  | ν :: ns, _ :: _, .cons _ _ A Θ, .cons t₁ ts₁, .cons t₂ ts₂ =>
    (ν ≠ .plain → ∃ F, NestRel sig ι n (fun m _ => levelRel sig ι m) s s (ν.map L) A F ∧ F t₁ t₂) ∧
      Terms.NestedRel sig ι n s L ns (Θ.subst₀ (Subst₀.single t₁)) ts₁ ts₂
  | _, _, _, _, _ => True

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are related at its fields whose nestings `ns` have a position by the equalities that
the graph of the nestings gives their types. -/
theorem TelRel.nestedRel (hd : sig.Distinct) {n : Nat} {s : Quality} {L : Name → NestLeaf} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Nest NestLeaf} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → (ns : List (Nest Name)) →
      (∀ i, rs' i = ((ns[i]?).getD .plain).map L) →
      (ts us : Terms 0 []) → S ts us →
        Terms.NestedRel sig ι n s L ns Θ ts us
  | [], .nil, _, _, .nil, ns, _, ts, us, _ => by
    cases ns <;> cases ts <;> cases us <;> trivial
  | _ :: ps, .cons q p A Θ, _, rs', h', ns, hrs, ts₀, us₀, hS => by
    have htail : ∀ i, rs' (i + 1) = ((ns.tail[i]?).getD .plain).map L := fun i => by
      rw [hrs (i + 1)]
      cases ns <;> rfl
    cases h' with
    | cons hA hF G hG _ hrs₀ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) hF
        have ih := TelRel.nestedRel hd (L := L) (hG t (hFp.trans htu (hFp.symm htu))) ns.tail
          htail ts us hts
        match ns, hrs with
        | [], _ => trivial
        | ν :: _, hrs =>
          refine ⟨fun hν => ?_, ih⟩
          have h0 := (hrs 0).symm.trans hrs₀
          cases ν with
          | plain => exact absurd rfl hν
          | direct _ => exact nomatch h0
          | inst _ => exact nomatch h0
    | nested hrs₀ hF G hG =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have ih := TelRel.nestedRel hd (L := L) (hG t) ns.tail htail ts us hts
        match ns, hrs with
        | [], _ => trivial
        | ν :: _, hrs => exact ⟨fun _ => ⟨_, (hrs 0) ▸ hF, htu⟩, ih⟩

/-- Arguments related by the equality of the fields of a closed telescope of the graph of a sort are
equal arguments of the telescope, and conversely, at positions that hold types with the equality of
their terms. -/
theorem TelRel.eqSubst_iff (hd : sig.Distinct) {n : Nat} {s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S : FieldsRel} {rs : Nat → Nest NestLeaf}
    (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S)
    (hH : Θ.NestHeads sig ι n s (fun i => ∃ νs, rs i = .inst νs))
    (hτ : ∀ i, Nest.All
      (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) (rs i))
    (ts us : Args 0 [] ps) :
    S ts.terms us.terms ↔ EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst :=
  ⟨fun hS => by
    obtain ⟨ts', us', h₁, h₂, hE⟩ := h.to_eqSubst hd hH hτ _ _ hS
    rw [Args.terms_inj h₁, Args.terms_inj h₂] at hE
    exact hE,
  h.of_eqSubst hH hτ ts us⟩

/-- Two closed terms that compute to types of `U_l` with the same equality of their terms and, for each
program, a common relation of run time are equal terms of `U_l`, in a signature whose names are
distinct. -/
theorem ValidEqTerm₀.ofUniv (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {R : TermRel}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).univ v R) (hw : (levelRel sig ι l.closedValue).univ w R)
    (hr : ∀ P, ∃ Q, (levelRel sig ι l.closedValue).run P v Q ∧
      (levelRel sig ι l.closedValue).run P w Q) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.type, l⟩) := by
  have hU := HasEq.univ (sig := sig) (ι := ι) (l.closedValue + 1)
    (levelRel_univ_iff.2 (.univ (l := l) rfl rfl))
  exact ⟨⟨hd, _, _, _, (Whnf.sort _).computes, (Whnf.sort _).computes, hU, hU, fun _ _ => .rfl⟩,
    fun _ => ⟨_, _, _, _, (Whnf.sort _).computes, ht, hu, hU, ⟨R, hv, hw⟩, hr⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

/-- Two closed terms that compute to propositions of `Ω_l` with the same truth are equal terms of
`Ω_l`, in a signature whose names are distinct. -/
theorem ValidEqTerm₀.ofProp (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {b : Prop}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).prop v b) (hw : (levelRel sig ι l.closedValue).prop w b) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.prop, l⟩) := by
  have hU : HasEq sig ι (.sort ⟨.prop, l⟩)
      (fun P Q => ∃ b₁ b₂, (levelRel sig ι l.closedValue).prop P b₁ ∧
        (levelRel sig ι l.closedValue).prop Q b₂ ∧ (b₁ ↔ b₂)) :=
    .univ (l.closedValue + 1) (levelRel_univ_iff.2 (.prop rfl rfl))
  exact ⟨⟨hd, _, _, _, (Whnf.sort _).computes, (Whnf.sort _).computes, hU, hU, fun _ _ => .rfl⟩,
    fun _ => ⟨_, _, _, _, (Whnf.sort _).computes, ht, hu, hU, b, b, hv, hw, .rfl⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

-- ADE: none.
/-- At equal closed arguments of the parameters of a meaningful type declaration, the fields of each
constructor of one of its types, at relations `Rf D` given at the positions of their nestings for
the instances of the type `D`, are telescopes of the graph of its sort with one equality `S Rf c`
of their terms, defined from the graph rather than chosen, since the graph gives one at most; when
the instances of the types of the block, at the first arguments, are types of the graph whose
equalities are the relations `Rf D`, and are, at the two arguments, equal types of the sort of the
declaration, the equality relates the terms of equal arguments of the fields, and only them. -/
theorem ValidTypeDeclaration.fieldsRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      ∀ Rf, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
            fun D => (.inst D qs ls ps as₁, Rf D))
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S Rf c) ∧
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
            fun D => (.inst D qs ls ps as₂, Rf D))
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S Rf c) ∧
        ((∀ D ∈ decl.names, NestRel sig ι
            ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
            (fun m _ => levelRel sig ι m) .type .type .plain (.inst D qs ls ps as₁) (Rf D)) →
          (∀ D ∈ decl.names, ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
            (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))) →
          (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            S Rf c ts.terms us.terms ↔ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
          ∀ fs₁ fs₂, S Rf c fs₁ fs₂ → ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            ts.terms = fs₁ ∧ us.terms = fs₂ ∧ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) := by
  have hA := hv.atClosedLevels hd hq hl hp hadm has
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun Rf c ts us =>
    ∃ S', TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
        fun D => (.inst D qs ls ps as₁, Rf D))
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' ts us
  refine ⟨S, fun Rf T hT c hc => ?_⟩
  have hF := hA.fields T hT c hc
  obtain ⟨S', h₁, h₂⟩ := hF.telRel hd Rf
  have h₁' := hA.telRel hd h₁
  have h₂' := hA.telRel hd h₂
  have hS : S Rf c = S' := funext fun ts => funext fun us => propext
    ⟨fun ⟨_, h', hs⟩ => (TelRel.unique hd (Nat.forall_lt (levelRel_isPer hd) _) h' _ _ h₁' ts us).1
      hs,
      fun hs => ⟨S', h₁', hs⟩⟩
  rw [hS]
  refine ⟨h₁', h₂', fun hRf hI => ?_⟩
  -- The positions hold the instances of the block, up to the values of their levels.
  have hτ : ∀ i, Nest.All
      (fun x : NestLeaf => NestRel sig ι
        (((decl.sort (.ofLists qs ps hq hp)).atLevels
          fun i => (ls.getFin hl i).closedValue).level.closedValue)
        (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2)
      (((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map fun D =>
        (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
          fun i => (ls.getFin hl i).closedValue).subst as₁.toSubst, Rf D)) := fun i =>
    Nest.All.map_rel₃ (fun D hD => hA.sort ▸
        NestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) (hRf D hD)
          (hA.instances as₁ D).symm .plain)
      (Telescope.nestAt_all decl.names _ i)
  -- The types of the nested fields are terms of a sort, since the instances of the block are.
  have hH := hF.nestHeads fun D hD =>
    (hI D hD).levelEquiv (hA.instances as₁ D).symm (hA.instances as₂ D).symm
      (.sort _ (Level.equivalence.symm (Level.subst_equiv hA.levels _)))
  refine ⟨fun ts us => (TelRel.eqSubst_iff hd h₁
    (hH.imp fun _ h => h.elim fun _ h => Nest.map_eq_inst h) hτ ts us).trans
      (hA.eqSubst_fields c as₁),
    fun fs₁ fs₂ hs => ?_⟩
  obtain ⟨ts, us, rfl, rfl, hts⟩ := TelRel.to_eqSubst hd h₁
    (hH.imp fun _ h => h.elim fun _ h => Nest.map_eq_inst h) hτ fs₁ fs₂ hs
  exact ⟨ts, us, rfl, rfl, (hA.eqSubst_fields c as₁).1 hts⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe, at equal closed
arguments of its parameters, are types of the graph of run time of its sort whose relation of run
time is `(®_μ)`, at a relation `S` of the fields common to the two arguments, for each program `P`:
the fields of each constructor at the two arguments are telescopes of the graph of run time with
the same relation, defined from the graph at the first arguments, rather than chosen, since the
graph gives one at most, whatever the relations of the recursive fields. -/
theorem ValidTypeDeclaration.runUnivRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) (P : Program) :
    ∃ S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        RunFieldsRel,
      (∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m)
          (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
            fun D' => (.inst D' qs ls ps as₁, (X D').computed sig ι))
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S X c)) ∧
      ∀ T ∈ decl.dataTypes,
        RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S T.name) ∧
        RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S T.name) := by
  have hA := hv.atClosedLevels hd hq hl hp hadm has
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Unique ((levelRel sig ι m).run P) := Nat.forall_lt (levelRel_run_unique hd) _
  let S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      RunFieldsRel := fun X c H ts bs =>
    ∃ S', RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m)
      (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
        fun D' => (.inst D' qs ls ps as₁, (X D').computed sig ι))
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' H ts bs
  have hS : ∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
      RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m)
        (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
          fun D' => (.inst D' qs ls ps as₁, (X D').computed sig ι))
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S X c) ∧
      RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m)
        (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
          fun D' => (.inst D' qs ls ps as₂, (X D').computed sig ι))
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S X c) := fun X T hT c hc => by
    obtain ⟨S', h₁, h₂⟩ := (hA.fields T hT c hc).runTelRel hd P hs fun D' => (X D').computed sig ι
    have h₁' := hA.runTelRel hd h₁
    have h₂' := hA.runTelRel hd h₂
    have hSS : S X c = S' := funext fun H => funext fun ts => funext fun bs => propext
      ⟨fun ⟨_, h', hs⟩ => (RunTelRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _) ih h' _ _ h₁'
          (fun _ => Nest.rel₃_refl (fun _ _ _ _ => .rfl) _) H ts bs).1 hs,
        fun hs => ⟨S', h₁', hs⟩⟩
    rw [hSS]
    exact ⟨h₁', h₂'⟩
  exact ⟨S, fun X T hT c hc => (hS X T hT c hc).1, fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => (hS X T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => (hS X T' hT' c hc).2⟩⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe, at equal closed
arguments of its parameters, are types of the graph of its sort whose equality is `(eq_μ)`, at the
equality `S` of the fields that the graph gives, which grows with the relations of the recursive
fields; two terms that compute to terms that `(eq_μ)` relates are equal terms of the instance at the
first arguments; at the relations `(eq_μ)` of the recursive fields, `S` relates the terms of equal
arguments of the fields at the first arguments, and only them, and each of them to itself. -/
theorem ValidTypeDeclaration.univRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockRel decl.dataTypes S T.name) ∧
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockRel decl.dataTypes S T.name)) ∧
      (∀ T ∈ decl.dataTypes, ∀ a b, (DataType.blockRel decl.dataTypes S T.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T.name qs ls ps as₁)) ∧
      (∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us) ∧
      (∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us →
        Terms.RecRel (fun D => (X D).computed sig ι)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      (∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us →
        Terms.NestedRel sig ι
          ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue .type
          (fun D => (.inst D qs ls ps as₁, (X D).computed sig ι))
          ((c.fields (.ofLists qs ps hq hp)).nest decl.names)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockRel decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockRel decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd)
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun X => S₀ fun D => (X D).computed sig ι
  have hU : ∀ T ∈ decl.dataTypes,
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockRel decl.dataTypes S T.name) ∧
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockRel decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun X D => (.inst D qs ls ps as₁, (X D).computed sig ι))
      (fun X T hT c hc => (hS₀ (fun D => (X D).computed sig ι) T hT c hc).1) X Y
      fun D _ _ => TermRel.computed_mono (hXY D)
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => (Whnf.inst ..).computes
  have hF : ∀ T ∈ decl.dataTypes, FieldRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) .type (.inst T.name qs ls ps as₁)
      ((DataType.blockRel decl.dataTypes S T.name).computed sig ι) := fun T hT =>
    .univ rfl (hU T hT).1
  refine ⟨S, hU, fun T hT _ _ hab => (hF T hT).validEqTerm hd (hI _) hab, hmono,
    fun X T hT c hc ts us h => TelRel.recRel hd (hS₀ _ T hT c hc).1 _
      (fun i D h => ⟨_, by rw [(Telescope.nestAt_eq_direct _ i).2 h]; rfl⟩) ts us h,
    fun X T hT c hc ts us h =>
      TelRel.nestedRel hd (hs ▸ (hS₀ _ T hT c hc).1) _ (fun _ => rfl) ts us h,
    fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, NestRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) .type .type .plain (.inst D qs ls ps as₁)
      ((DataType.blockRel decl.dataTypes S D).computed sig ι) := fun D hD => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    exact .plain (hI _) (hF T' hT')
  -- The instances of the block are equal types of its sort, which the nested fields read.
  have hV : ∀ D ∈ decl.names, ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := fun D hD => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
      (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
    rw [hs]
    exact ValidEqTerm₀.ofUniv hd (Whnf.inst ..).computes (Whnf.inst ..).computes
      (levelRel_univ_iff.2 (hU T' hT').1) (levelRel_univ_iff.2 (hU T' hT').2) fun P =>
        have ⟨_, _, hR⟩ := hv.runUnivRel hd hdecl hq hl hp hadm has hs P
        ⟨_, levelRel_run_iff.2 (hR T' hT').1, levelRel_run_iff.2 (hR T' hT').2⟩
  obtain ⟨-, -, hiff⟩ := hS₀ (fun D => (DataType.blockRel decl.dataTypes S D).computed sig ι) T hT c hc
  obtain ⟨hof, hto⟩ := hiff hRf hV
  refine ⟨hof, hto, fun fs₁ fs₂ h => ?_⟩
  have hper : IsPer (S (DataType.blockRel decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i => Nest.All.map_rel₃ (fun D hD => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
        exact FieldRel.isPer hd ih (hF T' hT')) (Telescope.nestAt_all decl.names _ i))
      (hS₀ _ T hT c hc).1
  exact hper.trans h (hper.symm h)

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe of propositions,
at equal closed arguments of its parameters, are propositions of the graph of its sort whose truth
is `(true_μ)`, at the equality `S` of the fields that the graph gives, which grows with the truths
of the recursive fields; at the truths `(true_μ)` of the recursive fields, `S` relates the terms of
equal arguments of the fields at the first arguments, and only them. -/
theorem ValidTypeDeclaration.propRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop) :
    ∃ S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockTruth decl.dataTypes S T.name) ∧
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockTruth decl.dataTypes S T.name)) ∧
      (∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us) ∧
      (∀ B, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us →
        Terms.RecRel (fun D _ _ => B D)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      (∀ B, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us →
        Terms.NestedRel sig ι
          ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue .prop
          (fun D => (.inst D qs ls ps as₁, fun _ _ => B D))
          ((c.fields (.ofLists qs ps hq hp)).nest decl.names)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockTruth decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd)
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
  let S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun B => S₀ fun D _ _ => B D
  have hP : ∀ T ∈ decl.dataTypes,
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockTruth decl.dataTypes S T.name) ∧
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockTruth decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us := fun B B' hB =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun B D => (.inst D qs ls ps as₁, fun _ _ => B D))
      (fun B T hT c hc => (hS₀ (fun D _ _ => B D) T hT c hc).1) B B' fun D _ _ => hB D
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => (Whnf.inst ..).computes
  refine ⟨S, hP, hmono, fun B T hT c hc ts us h =>
    TelRel.recRel hd (hS₀ _ T hT c hc).1 _
      (fun i D h => ⟨_, by rw [(Telescope.nestAt_eq_direct _ i).2 h]; rfl⟩) ts us h,
    fun B T hT c hc ts us h =>
      TelRel.nestedRel hd (hs ▸ (hS₀ _ T hT c hc).1) _ (fun _ => rfl) ts us h,
    fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, NestRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) .type .type .plain (.inst D qs ls ps as₁)
      (fun _ _ => DataType.blockTruth decl.dataTypes S D) := fun D hD => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    exact .plain (hI _) (.prop (hP T' hT').1)
  -- The instances of the block are equal propositions of its sort, which the nested fields read.
  have hV : ∀ D ∈ decl.names, ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := fun D hD => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
      (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
    rw [hs]
    exact ValidEqTerm₀.ofProp hd (Whnf.inst ..).computes (Whnf.inst ..).computes
      (levelRel_prop_iff.2 (hP T' hT').1) (levelRel_prop_iff.2 (hP T' hT').2)
  obtain ⟨hof, hto⟩ :=
    (hS₀ (fun D _ _ => DataType.blockTruth decl.dataTypes S D) T hT c hc).2.2 hRf hV
  have hper : IsPer (S (DataType.blockTruth decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i => Nest.map_rel₃ (r := fun (x : NestLeaf) _ _ => IsPer x.2)
      (fun _ => ⟨id, fun h _ => h⟩) _) (hS₀ _ T hT c hc).1
  exact ⟨hof, hto, fun _ _ h => hper.trans h (hper.symm h)⟩

-- ADE: none.
/-- `(D)`, closed: two instances of a declared type of `Σ`, whose type declaration is meaningful, at
the same levels and at equal arguments of its parameters, are equal terms of its sort: the fields
of each constructor at the two arguments are telescopes of the graph of the sort with the same
equality of their terms, and of the graph of run time with the same relation of their terms, for
each program. -/
theorem ValidEqTerm₀.inst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := by
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : ∀ as : InstanceArgs 0 [] decl.scope,
      Computesι sig ι (.inst T.name qs ls ps as) (.inst T.name qs ls ps as) :=
    fun as => (Whnf.inst _ _ _ _ as).computes
  show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
    (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · obtain ⟨S, hU, -⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofUniv hd (hw as₁) (hw as₂) (levelRel_univ_iff.2 (hU T hT).1)
      (levelRel_univ_iff.2 (hU T hT).2) fun P =>
        have ⟨S', _, hR⟩ := hv.runUnivRel hd hdecl hq hl hp hadm has hs P
        ⟨_, levelRel_run_iff.2 (hR T hT).1, levelRel_run_iff.2 (hR T hT).2⟩
  · obtain ⟨S, hP, -⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofProp hd (hw as₁) (hw as₂) (levelRel_prop_iff.2 (hP T hT).1)
      (levelRel_prop_iff.2 (hP T hT).2)

/-- The types of the nested fields of a constructor of a meaningful type declaration of `Σ`, at
the values of the levels of an instance and at equal closed arguments of its parameters, are terms
of a sort that the sort of the declaration bounds, the rest being so at every term of each field:
the instances of the types of the block are equal types of this sort. -/
theorem ValidTypeDeclaration.nestHeads (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope} (hc : c ∈ T.constructors)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    Telescope.NestHeads sig ι
      (((decl.sort (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).level.closedValue)
      (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ∃ νs, (c.fields (.ofLists qs ps hq hp)).nestAt decl.names i = .inst νs)
      (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as₁.toSubst) := by
  have hA := hv.atClosedLevels hd hq hl hp hadm has
  exact (hA.fields T hT c hc).nestHeads fun D hD => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    exact (ValidEqTerm₀.inst hd ⟨hdecl, hT', rfl⟩ hv hq hl hp hadm has).levelEquiv
      (hA.instances as₁ T'.name).symm (hA.instances as₂ T'.name).symm
      (.sort _ (Level.equivalence.symm (Level.subst_equiv hA.levels _)))

-- ADE: none.
/-- `(c)` and `(c_≡)`, closed: two applications of a constructor of a declared type of `Σ`, whose
type declaration is meaningful, at the same levels, at equal arguments of the parameters and at
equal arguments of its fields, are equal terms of the instance: canonical terms that `(eq_c)`
relates, or proofs of a proposition that the first one makes true. -/
theorem ValidEqTerm₀.ctor (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    {ts us : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
      ts.toSubst us.toSubst) :
    ValidEqTerm₀ sig ι (.ctor D qs ls ps as₁ con.name ts.terms)
      (.ctor D qs ls ps as₂ con.name us.terms) (.inst D qs ls ps as₁) := by
  have hI : ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩) :=
    ValidEqTerm₀.inst hd h hv hq hl hp hadm has
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : Computesι sig ι (.inst T.name qs ls ps as₁) (.inst T.name qs ls ps as₁) :=
    (Whnf.inst ..).computes
  have hct : ∀ (as : InstanceArgs 0 [] decl.scope) (ts : Terms 0 []),
      Computesι sig ι (.ctor T.name qs ls ps as con.name ts)
        (.ctor T.name qs ls ps as con.name ts) :=
    fun _ _ => (Whnf.ctor ..).computes
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · rw [hs] at hI
    obtain ⟨S, hU, -, hmono, hrec, -, hiff⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hrel : DataType.blockRel decl.dataTypes S T.name
        (.ctor T.name qs ls ps as₁ con.name ts.terms) (.ctor T.name qs ls ps as₂ con.name us.terms) :=
      DataType.blockRel_closed hmono hT ⟨con, hc, ts.terms, us.terms, ⟨qs, ls, ps, _, as₁, rfl⟩,
        ⟨qs, ls, ps, _, as₂, rfl⟩, ((hiff T hT con hc).1 ts us).2 hts⟩
    refine ⟨(ValidEqTerm₀.univType hI).left,
      fun _ => ⟨_, _, _, _, hw, hct _ _, hct _ _, .univ _ hU', hrel⟩,
      fun hp => (Computesι.not_computesToProp hd hw hU' hp).elim⟩
  · rw [hs] at hI
    obtain ⟨S, hP, hmono, hrec, -, hiff⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      DataType.blockTruth_closed hmono hT ⟨con, hc, ts.terms,
        (hiff T hT con hc).2.2 _ _ (((hiff T hT con hc).1 ts us).2 hts)⟩
    refine ⟨(ValidEqTerm₀.propType hI).left, fun hn => absurd ⟨_, hw, _, _, hP'⟩ hn,
      fun _ => ⟨_, fun _ _ => DataType.blockTruth decl.dataTypes S T.name, hw,
        .prop _ _ hP' fun _ _ => .rfl, htrue⟩⟩

/-- The equality of the terms of an instance in a universe of a data type of `Σ` is `(eq_μ)`, at an
equality of the fields of the constructors of its block that the graph gives. -/
theorem HasEq.dataInst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {as : InstanceArgs 0 [] decl.scope}
    {R : TermRel} (hR : HasEq sig ι (.inst D qs ls ps as) R) :
    ∃ (n : Nat) (S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        FieldsRel),
      (∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type
          (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
            fun D' => (.inst D' qs ls ps as, (X D').computed sig ι))
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) ∧
      ∀ t u, R t u ↔ DataType.blockRel decl.dataTypes S D t u := by
  cases hR with
  | univ n hU =>
    rw [levelRel_univ_iff] at hU
    cases hU with
    | data h' _ _ _ hv _ _ S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases has
      exact ⟨n, S, hS, fun _ _ => .rfl⟩
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim
  | prop n b hP _ =>
    rw [levelRel_prop_iff] at hP
    cases hP with
    | data h' _ _ _ hv hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

/-- A proposition that is an instance of a data type of `Σ` is an instance in a universe of
propositions. -/
theorem PropRel.dataInst_quality (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {n : Nat} {b : Prop}
    (hP : (levelRel sig ι n).prop (.inst D qs ls ps as) b) :
    (decl.sort (.ofLists qs ps hq hp)).quality = .prop := by
  rw [levelRel_prop_iff] at hP
  cases hP with
  | data h' _ _ _ hv hs' =>
    obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
    subst hD hqs hls hps
    obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
    exact hs'
  | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

-- ADE: none.
/-- Two equal terms of an instance in a universe of a data type of `Σ` whose constructors have no
field with a position compute to the same constructor of a type of the block, applied to equal
arguments of its fields: the canonical terms that `(eq_μ)` relates, which the equality of the instance, its
meaning as a type, gives. -/
theorem ValidEqTerm₀.ctor_inv {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hnr : ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors, ∀ i,
      (c.fields (.ofLists qs ps hq hp)).nestAt decl.names i = .plain)
    {as : InstanceArgs 0 [] decl.scope} {t₁ t₂ : Term 0 []}
    (ht : ValidEqTerm₀ sig ι t₁ t₂ (.inst D qs ls ps as)) :
    ∃ T' ∈ decl.dataTypes, T'.name = D ∧ ∃ con ∈ T'.constructors,
      ∃ ts₁ ts₂ : Args 0 [] (con.params (.ofLists qs ps hq hp)),
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₁ (.ctor D qs' ls' ps' as' con.name ts₁.terms)) ∧
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₂ (.ctor D qs' ls' ps' as' con.name ts₂.terms)) ∧
        EqSubst sig ι
          (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
          ts₁.toSubst ts₂.toSubst := by
  obtain ⟨⟨hd, v, -, R, hv, -, hR, -⟩, hne, -⟩ := ht
  have hw : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    (Whnf.inst ..).computes
  cases Computesι.det hd hw hv
  obtain ⟨n, S, hS, hiff⟩ := HasEq.dataInst hd h hq hl hp hs hR
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd (Nat.forall_lt (levelRel_isPer hd) _)
      (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
      (F := fun X D => (.inst D qs ls ps as, (X D).computed sig ι)) hS X Y
      fun D _ _ => TermRel.computed_mono (hXY D)
  obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := hne fun ⟨v', hv', _, _, hP⟩ => by
    cases Computesι.det hd hw hv'
    exact nomatch hs.symm.trans (PropRel.dataInst_quality hd h hq hp hP)
  cases Computesι.det hd hw hv'
  have hrel' := (hiff w₁ w₂).1 ((HasEq.unique hd hR' hR w₁ w₂).1 hrel)
  obtain ⟨T', hT', hn, c, hc, fs₁, fs₂, ⟨qs₁, ls₁, ps₁, Δ₁, as₁, rfl⟩,
    ⟨qs₂, ls₂, ps₂, Δ₂, as₂, rfl⟩, hfs⟩ := DataType.blockRel_inv hmono hrel'
  obtain ⟨ts₁, ts₂, rfl, rfl, hts⟩ := (hS _ T' hT' c hc).to_eqSubst hd
    (Telescope.nestHeads_of_not _ fun i ⟨_, h⟩ => by rw [hnr T' hT' c hc i] at h; exact nomatch h)
    (fun i => by rw [hnr T' hT' c hc i]; exact .plain) _ _ hfs
  exact ⟨T', hT', hn, c, hc, ts₁, ts₂, ⟨_, _, _, _, _, hn ▸ hw₁⟩, ⟨_, _, _, _, _, hn ▸ hw₂⟩, hts⟩

end
end Sic.Core
