module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.Corecursors
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Computation
import Sic.Core.RunTime.DeclaredTypes
import Sic.Core.RunTime.Levels
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Recursors
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Run Time of the Corecursors

The observations at run time: the erasure of an observation evaluates its term, then its arguments,
then observes the closure at the address of the term by the destructor of its case.

A term of an instance of a codata type that is a type is related to the address of its value by
`(®_ν)`, some relations consistent with its clauses: the term computes to a corecursor whose
observations are related to the address, destructor by destructor, so that, at the position of the
observed destructor, whose grade is used at run time, arguments related to addresses by the relation
of its telescope give an observation that evaluates to an address related to the observation of the
corecursor at its result.
The observations of the term and those of the corecursor it computes to are equal, as the soundness
of the observations relates them, so that the telescope and the result of the destructor are equal
types at both, with the same relations of run time.
The formation gives the destructors of a proposition grades without use at run time, so that no
observation of a proof runs.

The position that the branch of a recursive destructor gives is a constructor of the type of
positions of the prelude, which has no recursive field: a new state, whose packing unpacks into the
nested pairs of the arguments of the state, related to the addresses that the evaluation unpacks
when the grade of the corecursor is used at run time, and whose entries have grades without use at
run time otherwise, so that the evaluation does not read it; or a term already built, related to
the address of its field.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Observations -/

/-- The destructor at a position of destructors of run time, whose grade is used at run time,
observes a value whose observations are related at run time: at arguments related to addresses by
the relation of run time of its telescope, in a heap that extends that of the value, the
observation evaluates to an address to which the observation of the term is related at the result
of the destructor; the relations of the recursive destructors relate only terms related at their
instances. -/
theorem Destructors.Pos.run (hd : sig.Distinct) {κ : Universe 0} {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hpos : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {θ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs ds θ θ → {rsR : Nat → Option RunRel} →
      (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R, rsR i = some R ∧
        ∀ H t a, R H t a → RunsAs sig ι P H t a ((inst D).subst θ)) →
      {D : Name} → {S : RunObsRel} →
      RunDesRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) D rsR ds θ S →
      {H : Heap} → {o : Observations} → {a : Nat} → S H o a → p ∉ Mode.oneOne.erased →
      ∃ i RΘ, sig.destructorCase D d = some i ∧
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => none)
          (Θ.subst (hpos.obsSubst o θ)) RΘ ∧
        ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps) (bs : List Nat), RΘ H' ts.terms bs →
          ∃ w H'', EvalObs P H' a i bs w H'' ∧
            RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
              (B.subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))
  | _, _, _, _, _, _, _, .here, _, _, _, hv, _, hN, hR, _, _, hS, _, _, _, ho, hp => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    split at hv
    · rename_i hr
      cases hS with
      | recursive _ hrs => rw [hN 0 hr] at hrs; cases hrs
      | cons hi hΘ hRΘ _ _ hB _ hRv _ _ _ =>
        obtain ⟨-, hrun, -⟩ := ho
        refine ⟨_, _, hi, hRΘ, fun H' hH' ts bs hts => ?_⟩
        obtain ⟨w, H'', hev, hw⟩ := hrun hp H' hH' ts bs hts
        have htt := RunTelRel.fieldsRel hd (fun m _ => levelRel_isPer hd m) hRΘ (fun _ => rfl) _ _
          hΘ (fun _ => rfl) H' ts.terms bs hts
        obtain ⟨v, hv'⟩ := hB ts htt
        exact ⟨w, H'', hev, (hRv ts htt v hv').runsAs hv' hw⟩
    · rename_i D' hr
      obtain ⟨rfl, -⟩ := hv
      obtain ⟨R, hR0, hRr⟩ := hR 0 D' hr
      cases hS with
      | cons _ _ _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | recursive hi hrs hRΘ _ _ =>
        rw [hR0] at hrs
        cases hrs
        obtain ⟨hrun, -⟩ := ho
        refine ⟨_, _, hi, hRΘ, fun H' hH' ts bs hts => ?_⟩
        obtain ⟨w, H'', hev, hw⟩ := hrun hp H' hH' ts bs hts
        refine ⟨w, H'', hev, ?_⟩
        rw [Term.subst_append_rename_weakenN]
        exact hRr _ _ _ hw
  | _, _, _, _, _, _, _, .there (ps' := ps') (ψ' := ψ') h, inst, rs, θ, hv, rsR, hN, hR, _, _,
      hS, _, o, _, ho, hp => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    have hN' : ∀ i, rs (i + 1) = none → rsR (i + 1) = none := fun i => hN (i + 1)
    have hR' : ∀ (f : Term 0 (Scope.extend [] ps'.length)) i D, rs (i + 1) = some D → ∃ R,
        rsR (i + 1) = some R ∧ ∀ H t a, R H t a → RunsAs sig ι P H t a
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ f)) :=
      fun f i D hi => by
        rw [show ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ f) =
          (inst D).subst θ from Term.subst_rename_of (fun _ => rfl) _]
        exact hR (i + 1) D hi
    split at hv
    · rename_i hr
      obtain ⟨-, hds⟩ := hv
      cases hS with
      | recursive _ hrs => rw [hN 0 hr] at hrs; cases hrs
      | cons _ hΘ _ _ _ hB hF _ _ hG _ =>
        obtain ⟨hA, -, hGo⟩ := ho
        have hSp := TelRel.isPer hd (fun m _ => levelRel_isPer hd m) (fun _ _ h => by cases h) hΘ
        refine h.run hd (hds _ _ fun τ₁ τ₂ hτ => ?_) hN' (hR' _) (hG _ hA) hGo hp
        obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) ts.toSubst @τ₁ :=
          ⟨_, Subst.args_toSubst ps' τ₁⟩
        obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) us.toSubst @τ₂ :=
          ⟨_, Subst.args_toSubst ps' τ₂⟩
        have hts := (TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
          ts us).2 hτ
        have htt := hSp.trans hts (hSp.symm hts)
        obtain ⟨v, hv'⟩ := hB ts htt
        exact (hF ts htt v hv').validEqTerm hd hv' (hA ts us hts)
    · rename_i D' hr
      obtain ⟨-, hds⟩ := hv
      obtain ⟨R, hR0, -⟩ := hR 0 D' hr
      cases hS with
      | cons _ _ _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | recursive _ _ _ _ hG =>
        obtain ⟨-, hGo⟩ := ho
        exact h.run hd (hds _ _) hN' (hR' _) (hG _) hGo hp

/-- At a position of destructors equal at two substitutions of their scope, the telescope and the
result of the destructor are equal at two observations whose abstractions the destructors before it
relate, at equal arguments, as terms of their results; the result of a recursive destructor being an
instance of the block, equal at both substitutions. -/
theorem Destructors.Pos.validEq {κ : Universe 0} {d : Name} {p q : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hpos : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {θ₁ θ₂ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁ θ₂ →
      (∀ i D, rs i = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι ((inst D).subst θ₁) ((inst D).subst θ₂) (.sort κ₁)) →
      {f₁ f₂ : Observations} →
      (∀ (d' : Name) (p' q' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope 0 Ξ' ps') (B' : Term 0 (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership ps'.length) (hpos' : ds.Pos d' p' q' Ξ' Θ' B' ψ')
        (ts us : Args 0 [] ps'),
        EqSubst sig ι (Context.empty.append (Θ'.subst (hpos'.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι ((f₁ d' ps').subst ts.toSubst) ((f₂ d' ps').subst us.toSubst)
          (B'.subst (Subst.append (hpos'.obsSubst f₁ θ₁) ts.toSubst))) →
      ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst (hpos.obsSubst f₁ θ₁))
        (Θ.subst (hpos.obsSubst f₂ θ₂)) ∧
      ∀ ts us : Args 0 [] ps,
        EqSubst sig ι (Context.empty.append (Θ.subst (hpos.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ∃ κ₁, ValidEqTerm₀ sig ι (B.subst (Subst.append (hpos.obsSubst f₁ θ₁) ts.toSubst))
          (B.subst (Subst.append (hpos.obsSubst f₂ θ₂) us.toSubst)) (.sort κ₁)
  | _, _, _, _, _, _, _, .here, _, _, _, _, hv, hI, _, _, _ => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨hΘ, hv⟩ := hv
    refine ⟨hΘ, ?_⟩
    split at hv
    · obtain ⟨⟨κ₁, -, hB⟩, -⟩ := hv
      exact fun ts us hτ => ⟨κ₁, hB _ _ hτ⟩
    · rename_i D hr
      obtain ⟨rfl, -⟩ := hv
      obtain ⟨κ₁, hI0⟩ := hI 0 D hr
      refine fun ts us _ => ⟨κ₁, ?_⟩
      rw [Term.subst_append_rename_weakenN, Term.subst_append_rename_weakenN]
      exact hI0
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (ψ' := ψ') h, inst, rs, θ₁, θ₂, hv, hI,
      f₁, f₂, hobs => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    have hI' : ∀ i D, rs (i + 1) = some D → ∃ κ₁, ValidEqTerm₀ sig ι
        (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ (f₁ d' ps')))
        (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₂ (f₂ d' ps')))
        (.sort κ₁) := fun i D hi => by
      rw [Term.subst_rename_of (fun _ => rfl), Term.subst_rename_of (fun _ => rfl)]
      exact hI (i + 1) D hi
    have hobs' := fun d'' p' q' ps'' Ξ' Θ' B' ψ' (hpos' : Destructors.Pos d'' p' q' _ Ξ' Θ' B' ψ')
      => hobs d'' p' q' ps'' Ξ' Θ' B' ψ' (.there hpos')
    split at hv
    · obtain ⟨-, hds⟩ := hv
      refine h.validEq (hds _ _ fun τ₁ τ₂ hτ => ?_) hI' hobs'
      obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps',
          @Eq (Subst 0 [] (Scope.extend [] ps'.length)) ts.toSubst @τ₁ :=
        ⟨_, Subst.args_toSubst ps' τ₁⟩
      obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps',
          @Eq (Subst 0 [] (Scope.extend [] ps'.length)) us.toSubst @τ₂ :=
        ⟨_, Subst.args_toSubst ps' τ₂⟩
      exact hobs _ _ _ _ _ _ _ _ .here ts us hτ
    · obtain ⟨-, hds⟩ := hv
      exact h.validEq (hds _ _) hI' hobs'

-- ADE: none.
/-- `(d)` at run time, closed: a term of an instance of a codata type of `Σ`, whose type declaration
is meaningful, related to an address, observed by a destructor whose grade is used at run time, at
arguments that the meaning relates to themselves and that are related to addresses in a heap that
extends that of the term, evaluates to an address to which the observation is related at its
result, in a signature whose names are distinct; the formation makes the grade of the destructor of
a proposition without use at run time. -/
theorem RunsAs.obs (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst)
    {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) (hpr : p ∉ Mode.oneOne.erased)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → p.mode ≠ .oneOne)
    {H : Heap} {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t (.inst D qs ls ps as))
    (ht : RunsAs sig ι P H t a (.inst D qs ls ps as)) {H' : Heap} (hH' : H.Extends H')
    {ts : Args 0 [] ps'} {bs : List Nat}
    (hts : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst ts.toSubst)
    (hbs : RunsAsArgs sig ι P H' (Parameter.grades ps') ts bs
      ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
    ∃ i w H'', sig.destructorCase D d = some i ∧ EvalObs P H' a i bs w H'' ∧ H'.Extends H'' ∧
      RunsAs sig ι P H'' (.obs D qs ls ps as t d ts.terms) w
        ((B.substLevels (ls.getFin hl)).subst
          (Subst.append (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst)) := by
  obtain ⟨hdecl, hT, hD⟩ := id h
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm hT ρ).2 _ _ hθ
  have hn := Level.closedValue_subst_equiv hls (decl.sort I).level
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst as.toSubst
  have hX : ∀ D', Term.LevelEquiv (X D') (.inst D' qs ls ps as) := fun D' =>
    decl.blockInstance_atLevels_subst hq hl hp as D'
  have hcX : ∀ D', Computesι sig ι (X D') (X D') := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hXeq : ∀ D' ∈ decl.names, ∃ κ₁, ValidEqTerm₀ sig ι (X D') (X D') (.sort κ₁) :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT hD'
      exact ⟨_, (ValidEqTerm₀.instCodata hd ⟨hdecl, hT', rfl⟩ hv hq hl hp hadm has).levelEquiv
        (hX _).symm (hX _).symm (Term.LevelEquiv.refl _)⟩
  have hI : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  -- The instance is a type, since the destructor of a proposition has no use at run time.
  have hs : (decl.sort I).quality = .type := by
    cases hs : (decl.sort I).quality with
    | type => rfl
    | prop =>
      exact absurd ((by decide : ∀ p : Grade, p ∉ Mode.oneOne.erased → p.mode = .oneOne) p hpr)
        (hprop hs)
  -- The term computes to a corecursor whose observations `(®_ν)` relates.
  obtain ⟨v, hcv, hrun⟩ := ht
  cases Computesι.det hd hI hcv
  rcases hrun with ⟨k, b, hk⟩ | ⟨R, hR, htR⟩
  · cases levelRel_prop_iff.1 hk with
    | data hc _ _ _ hv' => exact (hd.inst_data_codata hc h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD', hqs, hls₂, hps, -⟩ := Term.inst.inj hv'
      subst hD' hqs hls₂ hps
      obtain ⟨rfl, -⟩ := hd.hasCodataType_unique h h'
      exact nomatch hs.symm.trans hs'
  obtain ⟨n, S, hnS, hS, rfl⟩ := HasRun.codata hd h hq hl hp hR hs
  obtain ⟨v', hv', Y, hY, hYD⟩ := htR
  rw [← hD] at hYD
  obtain ⟨o', hco', hSo⟩ := hY T hT H v' a hYD
  have e : ((decl.sort I).atLevels ρ).level.closedValue = n := hn.trans hnS
  have hSρ : RunDesRel sig ι P ((decl.sort I).atLevels ρ).level.closedValue
      (fun m _ => levelRel sig ι m) T.name
      (fun i => ((T.body I).recursionAt decl.names i).map fun D' => (Y D').computed sig ι)
      ((T.body I).atLevels ρ) as.toSubst (S Y T) := by
    rw [e]
    exact RunDesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) (hS Y T hT)
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  -- The observation by the destructor, at arguments related by the relation of its telescope.
  obtain ⟨i, RΘ, hi, hRΘ, hobsR⟩ := (hpos.substLevels Lρ).run hd hmean
    (fun i hi => by rw [hi]; rfl) (fun i D' hi => ⟨_, by rw [hi]; rfl, fun H₀ t₀ b htb => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
        (Destructors.recursionAt_mem hi)
      obtain ⟨w, hw, hYw⟩ := htb
      have hU : RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
          (CodataType.runBlockRel decl.codataTypes S T'.name) :=
        .codata ⟨hdecl, hT', rfl⟩ hq hl hp rfl hs hnS S hS
      exact RunsAs.levelEquiv (hX _).symm
        ⟨_, ⟨.refl _, .inst _ _ _ _ _⟩, .inr ⟨_, .univ n (levelRel_run_iff.2 hU), w, hw, Y, hY,
          hYw⟩⟩⟩) hSρ hSo hpr
  -- The equality of the term relates its observations to those of the corecursor.
  obtain ⟨v₂, -, Req, hcv₂, -, hReq, -⟩ := htv.1.2
  cases Computesι.det hd hcv₂ hI
  obtain ⟨-, Se, hSe, rfl⟩ := (HasEq.instCodata_inv hd h hq hl hp hReq).resolve_right
    fun ⟨hs', _⟩ => nomatch hs.symm.trans hs'
  have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
      (.inst D qs ls ps as) (CodataType.blockRel decl.codataTypes Se D) :=
    levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl Se hSe)
  have hnp : ¬ ComputesToProp sig ι (.inst D qs ls ps as) := fun ⟨v, hv, k, b, hk⟩ => by
    cases Computesι.det hd hI hv
    exact HasEq.univ_not_prop hd hU₀ hk
  obtain ⟨v₀, w₁, w₂, R', hv₀, hw₁, hw₂, hR', hrel⟩ := htv.2.1 hnp
  cases Computesι.det hd hI hv₀
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
      ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, Se X T' o₁ o₂ → Se Y T' o₁ o₂ :=
    fun X Y hXY T' hT' => DesRel.mono hd ih (hSe X T' hT') _ _ _ (hSe Y T' hT')
      fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
  have hrel' := (HasEq.unique hd hR' hReq w₁ w₂).1 hrel
  rw [← hD] at hrel'
  obtain ⟨o₁, o₂, hc₁, hc₂, ho⟩ := CodataType.blockRel_unfold hmono hT hrel'
  cases Computesι.det hd hv' hw₁
  cases Computesι.det hd hv' hw₂
  -- The observations of the corecursor are those of the run time.
  have hoo : ∀ {o o'' : Observations}, v'.CorecObservations T.name o →
      v'.CorecObservations T.name o'' → o = o'' := fun {o o''} h₁ h₂ => by
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, he, rfl⟩ := h₂
    cases he
    rfl
  cases hoo hc₁ hco'
  cases hoo hc₂ hco'
  have hf₁ : ObsEquiv sig ι ((decl.sort I).atLevels ρ).quality (t.observation D qs ls ps as) o' :=
    ObsEquiv.of_computes hd hv' hc₁
  have hf₂ : ObsEquiv sig ι ((decl.sort I).atLevels ρ).quality o' o' := .inr fun _ _ _ _ => .rfl
  have hDes : DesRel sig ι ((decl.sort I).atLevels ρ).level.closedValue
      (fun m _ => levelRel sig ι m) ((decl.sort I).atLevels ρ).quality
      (fun i => ((T.body I).recursionAt decl.names i).map
        fun D' => (CodataType.blockRel decl.codataTypes Se D').computed sig ι)
      ((T.body I).atLevels ρ) as.toSubst (Se (CodataType.blockRel decl.codataTypes Se) T) := by
    have e' : ((decl.sort I).atLevels ρ).level.closedValue =
        ((decl.sort I).level.subst L).closedValue := hn
    have hq' : ((decl.sort I).atLevels ρ).quality = .type := hs
    rw [e', hq']
    exact DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) (hSe _ T hT)
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  have hRr : ∀ i D', (T.body I).recursionAt decl.names i = some D' → ∃ R v,
      ((T.body I).recursionAt decl.names i).map
        (fun D' => (CodataType.blockRel decl.codataTypes Se D').computed sig ι) = some R ∧
      Computesι sig ι (X D') v ∧
      FieldRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        ((decl.sort I).atLevels ρ).quality v R := fun i D' hi => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
      (Destructors.recursionAt_mem hi)
    have hU : UnivRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (CodataType.blockRel decl.codataTypes Se T'.name) :=
      .codata ⟨hdecl, hT', rfl⟩ hq hl hp rfl hs rfl Se hSe
    have e' : ((decl.sort I).atLevels ρ).level.closedValue =
        ((decl.sort I).level.subst L).closedValue := hn
    have hq' : ((decl.sort I).atLevels ρ).quality = .type := hs
    rw [hi, e', hq']
    exact ⟨_, _, rfl, hcX _,
      FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m) (.univ rfl hU) (hX _).symm⟩
  -- The telescope and the result of the destructor at both observations are equal.
  obtain ⟨htel, hBeq⟩ := (hpos.substLevels Lρ).validEq hmean
    (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi))
    (fun _ _ _ _ _ _ _ _ hpos' => (hpos'.sound hd hmean (fun i hi => by rw [hi]; rfl) hRr
      (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi)) hDes ho hf₁ hf₂).2)
  have hres := ((hpos.substLevels Lρ).sound hd hmean (fun i hi => by rw [hi]; rfl) hRr
      (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi)) hDes ho hf₁ hf₂).2
  -- The arguments, at the levels without variables, are related by the relation of the telescope.
  have hcE : Subst.LevelEquiv
      ((hpos.substLevels Lρ).obsSubst (t.observation D qs ls ps as) as.toSubst)
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) := fun {_} x => by
    show Term.LevelEquiv
      ((hpos.substLevels Lρ).obsSubst (t.observation D qs ls ps as) as.toSubst x)
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst x)
    rw [Destructors.Pos.obsSubst_posSubstLevels]
    exact Term.LevelEquiv.refl _
  have hΘE : Telescope.LevelEquiv
      ((Θ.substLevels Lρ).subst
        ((hpos.substLevels Lρ).obsSubst (t.observation D qs ls ps as) as.toSubst))
      ((Θ.substLevels L).subst (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)) :=
    Telescope.LevelEquiv.subst hcE (Telescope.substLevels_levelEquiv hls Θ)
  have htsρ := EqSubst.levelEquiv (Context.LevelEquiv.append .empty hΘE.symm) hts
  have hbsρ := hbs.levelEquiv hΘE.symm
  obtain ⟨S', h₁, h₂⟩ := htel.runTelRel hd P rfl
  have hS' := RunTelRel.of_runsAsArgs hd h₁
    (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h) _
    (fun _ _ hl hp => (Parameter.grades_of_getElem? hl).symm ▸ hp) ts htsρ bs hbsρ
  have hRΘts : RΘ H' ts.terms bs := (RunTelRel.congr hd (fun m _ => levelRel_isPer hd m)
    (fun m _ => levelRel_run_unique hd m) h₂ _ _ hRΘ
    (fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) H' ts.terms bs).1 hS'
  -- The observation evaluates to an address to which the observation of the corecursor is related.
  obtain ⟨w, H'', hev, hw⟩ := hobsR H' hH' ts bs hRΘts
  refine ⟨i, w, H'', hD ▸ hi, hev, hev.extends, ?_⟩
  -- The observation of the term computes as that of the corecursor.
  have hcomp : ∀ w', Computesι sig ι ((o' d ps').subst ts.toSubst) w' ↔
      Computesι sig ι (.obs D qs ls ps as t d ts.terms) w' := by
    rcases hf₁ with hp' | hf
    · exact nomatch (hs : ((decl.sort I).atLevels ρ).quality = .type).symm.trans hp'
    · intro w'
      rw [← Term.observation_subst_args]
      exact (hf d ps' ts.toSubst w').symm
  have hw₁ := (RunsAs.congr_computes hcomp).1 hw
  -- Its result at the observations of the corecursor is equal to that at those of the term.
  have hBT : ValidEqType₀ sig ι
      ((B.substLevels Lρ).subst (Subst.append
        ((hpos.substLevels Lρ).obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst))
      ((B.substLevels Lρ).subst (Subst.append
        ((hpos.substLevels Lρ).obsSubst o' as.toSubst) ts.toSubst)) := by
    obtain ⟨⟨s₁, l₁⟩, hB₁⟩ := hBeq ts ts htsρ
    cases s₁
    · exact ValidEqTerm₀.univType hB₁
    · exact ValidEqTerm₀.propType hB₁
  have hres' := hres ts ts htsρ
  rw [Term.observation_subst_args] at hres'
  have hw₂ := RunsAs.conv hd (ValidEqTerm₀.conv hres'.left hBT).2 hBT.symm.2 hw₁
  exact hw₂.levelEquiv (Term.LevelEquiv.subst (Subst.LevelEquiv.append hcE (Subst.LevelEquiv.refl _))
    (Term.substLevels_levelEquiv hls B))

-- ADE: none.
/-- `(d)` at run time: an observation of a term of an instance of a codata type of `Σ`, whose type
declaration is meaningful, valid at run time with the grades `γ`, by a destructor whose grade is
used at run time, at arguments valid at run time with the grades `δ`, is valid at run time at its
result with the grades `γ + δ`, in a signature whose names are distinct: its erasure evaluates its
term, then its arguments, then observes the closure. -/
theorem RunValid.obs (hd : sig.Distinct) {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ}
    {γ δ : GradeVector Γ.length} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) (hpr : p ∉ Mode.oneOne.erased)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → p.mode ≠ .oneOne)
    {t : Term 0 Γ} (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : RunValid sig ι P hΓ ctx γ t (.inst D qs ls ps as)) {bs : Args 0 Γ ps'}
    (hbs : ValidArgsΓ sig ι ctx bs ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))
    (hbr : RunValidArgs sig ι P hΓ ctx δ bs ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
    RunValid sig ι P hΓ ctx (γ +ᶜ δ) (.obs D qs ls ps as t d bs.terms)
      (((B.substLevels (ls.getFin hl)).subst
        (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))).instantiate
          bs) := by
  intro σ H E hσ hE
  have hS := Mode.erasesUncounted .oneOne
  have hEγ : RunsAsSubst sig ι P H ctx γ σ E := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ h')) hE
  have hEδ : RunsAsSubst sig ι P H ctx δ σ E := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  -- The scope of the destructor, substituted, is that of the observations of the term substituted.
  have hc : ∀ {a} (x : Var Ξ a),
      ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
        (Subst.liftN a.params.length σ) =
      hpos.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
    hpos.obsSubst_subst σ (fun d ps' => Term.observation_subst σ D qs ls ps as t d ps')
      (InstanceArgs.toSubst_subst σ as)
  have hΘ : ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)).subst σ =
      (Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst) :=
    Telescope.subst_subst_of hc _
  have hA : (((B.substLevels (ls.getFin hl)).subst
      (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))).instantiate
        bs).subst σ =
      (B.substLevels (ls.getFin hl)).subst (Subst.append
        (hpos.obsSubst ((t.subst σ).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst)
        (bs.subst σ).toSubst) := by
    rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _ hc),
      Term.instantiate_eq_subst, Term.subst_append]
  -- The term, then the arguments, then the observation.
  obtain ⟨a, H₁, hev, hH₁, hta⟩ := htr σ H E hσ hEγ
  obtain ⟨bs', H₂, hevs, hH₂, hruns⟩ := hbr σ H₁ E hσ (hEδ.mono hd hH₁ ctx)
  rw [hΘ] at hruns
  have hbsσ := hbs.2 σ σ hσ
  rw [hΘ] at hbsσ
  obtain ⟨i, w, H₃, hi, hevo, hH₃, hrun⟩ := RunsAs.obs hd h hv hq hl hp hadm (has.2 σ σ hσ) hpos
    hpr hprop (ht.2 σ σ hσ) hta hH₂ hbsσ hruns
  have he : (Term.obs D qs ls ps as t d bs.terms).erase sig Mode.oneOne.erased hΓ =
      .obs (t.erase sig Mode.oneOne.erased hΓ) i
        (bs.terms.erase sig Mode.oneOne.erased hΓ (ps'.map (·.usage))) := by
    rw [Term.erase, hi, hd.argumentGrades h hq hp hpos]
    rfl
  refine ⟨w, H₃, he ▸ .obs hev hevs hevo, hH₁.trans (hH₂.trans hH₃), ?_⟩
  rw [hA]
  simp only [Term.subst, ← Args.terms_subst]
  exact hrun

/-! ## Positions -/

/-- The case of the constructor of the pair of the prelude is the first one. -/
theorem Signature.Distinct.pairCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Pair" "mk" = some i) : i = 0 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.pair (List.mem_singleton_self _)
    (hi : sig.constructorCase Prelude.pairType.name Prelude.pairMk.name = some i)
  rw [show Prelude.pair.cases = [(0, Prelude.pairType, Prelude.pairMk)] from rfl] at hj
  match i, hj with
  | 0, _ => rfl

/-- A closed term of the packing of a closed telescope, related to an address, computes to the
nested pairs of arguments of the telescope, which the meaning relates to themselves, and the value at
the address unpacks into addresses to which the arguments are related, each at the type of its
entry, when its grade is used at run time, in a signature whose names are distinct and that holds
the prelude. -/
theorem RunsAs.unpack (hd : sig.Distinct) (hpre : sig.HasPrelude) {H : Heap} :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → (κs : List (Universe 0)) → (l : Level 0) →
      {x : Term 0 []} → {a : Nat} → ValidTerm₀ sig ι x (Θ.pack κs l) →
      RunsAs sig ι P H x a (Θ.pack κs l) →
      ∃ (ts : Args 0 [] ps) (as : List Nat), Term.Packs sig ι x ts.terms ∧
        EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst ∧
        Unpack H ps.length a as ∧ RunsAsArgs sig ι P H (Parameter.grades ps) ts as Θ
  | [], .nil, _, l, _, _, hx, hr => by
    obtain ⟨T', hT', -, con, hc, ts, i, bs, hct, -, -, -, -⟩ := RunsAs.ctor_inv hd hpre.unit
      (qs := []) (ls := [l]) (ps := []) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rfl) hx hr
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    match ts with
    | .nil =>
      refine ⟨.nil, [], ?_, (EqSubst.empty_iff _ _).2 trivial, .zero, trivial⟩
      simp only [Args.terms, Term.Packs]
      exact hct
  | _ :: _, .cons q p A Θ, κs, l, _, _, hx, hr => by
    obtain ⟨T', hT', -, con, hc, ts, i, bs, hct, hi, ha, hts, hruns⟩ := RunsAs.ctor_inv hd hpre.pair
      (qs := [(κs.headD ⟨.type, l⟩).quality])
      (ls := [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l])
      (ps := [p.usage, p.requirement]) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rcases i with _ | _ | _ <;> rfl) hx hr
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    obtain rfl := hd.pairCase hpre hi
    match ts, bs, hts, hruns with
    | .cons t (.cons y .nil), [b, c], hts, hruns =>
      obtain ⟨ht, hys⟩ := EqSubst.args_cons_iff.1 hts
      obtain ⟨hy, -⟩ := EqSubst.args_cons_iff.1 hys
      obtain ⟨hb, hc', -⟩ := hruns
      have hy' : ValidTerm₀ sig ι y ((Θ.subst₀ (Subst₀.single t)).pack κs.tail l) := by
        rw [← Telescope.pack_subst₀, ← Prelude.pairSecond (Θ.pack κs.tail l)]
        exact hy
      have hry : RunsAs sig ι P H y c ((Θ.subst₀ (Subst₀.single t)).pack κs.tail l) := by
        rw [← Telescope.pack_subst₀, ← Prelude.pairSecond (Θ.pack κs.tail l)]
        exact hc' (by decide : Grade.one ∉ Mode.oneOne.erased)
      obtain ⟨ts', as', hp', hτ, hu, hrs⟩ := RunsAs.unpack hd hpre _ κs.tail l hy' hry
      obtain ⟨qs₁, ls₁, ps₁, Δ₁, as₁, hc₁⟩ := hct
      refine ⟨.cons t ts', b :: as', ?_, EqSubst.args_cons_iff.2 ⟨ht, hτ⟩, .pair ha hu, hb, hrs⟩
      simp only [Args.terms, Term.Packs]
      exact ⟨qs₁, ls₁, ps₁, Δ₁, as₁, y, hc₁, hp'⟩


/-- The case of the constructor `next` of the type of positions of the prelude is the first one. -/
theorem Signature.Distinct.nextCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Step" "next" = some i) : i = 0 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.step (List.mem_cons_self ..)
    (hi : sig.constructorCase Prelude.stepType.name Prelude.stepNext.name = some i)
  rw [show Prelude.step.cases = [(0, Prelude.stepType, Prelude.stepNext),
    (0, Prelude.stepType, Prelude.stepDone)] from rfl] at hj
  match i, hj with
  | 0, _ => rfl
  | 1, hj =>
    exact absurd (congrArg (fun x => x.2.2.name) (Option.some.inj hj))
      (by decide : Prelude.stepDone.name ≠ Prelude.stepNext.name)

/-- The case of the constructor `done` of the type of positions of the prelude is the second one. -/
theorem Signature.Distinct.doneCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Step" "done" = some i) : i = 1 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.step
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (hi : sig.constructorCase Prelude.stepType.name Prelude.stepDone.name = some i)
  rw [show Prelude.step.cases = [(0, Prelude.stepType, Prelude.stepNext),
    (0, Prelude.stepType, Prelude.stepDone)] from rfl] at hj
  match i, hj with
  | 0, hj =>
    exact absurd (congrArg (fun x => x.2.2.name) (Option.some.inj hj))
      (by decide : Prelude.stepNext.name ≠ Prelude.stepDone.name)
  | 1, _ => rfl

-- ADE: none.
/-- A closed position of a corecursor of the grade `r`, in a universe, related to an address,
resumes: the position computes to a new state, the nested pairs of arguments of the state that the
meaning relates to themselves, and its resumption, a new closure from addresses to which the
arguments are related at the grades of the state times `r`, which it unpacks from the new state
when `r` is used at run time, and takes at the address of the new state otherwise, without reading
it; or the position computes to a term already built, related to the address that its resumption
gives. -/
theorem RunsAs.resume (hd : sig.Distinct) (hpre : sig.HasPrelude) {κ : Universe 0}
    (hκ : κ.quality = .type) {r χ : Grade} {ps' : List Parameter} {S : Telescope 0 [] ps'}
    {κs : List (Universe 0)} {T g : Term 0 []}
    (hgv : ValidTerm₀ sig ι g (Term.positions κ r χ S κs T)) {H : Heap} {w : Nat}
    (hg : RunsAs sig ι P H g w (Term.positions κ r χ S κs T)) (n : Nat) (E : List Nat)
    (Ps : TargetCorecBranches n) (D' : Name) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) {Δ : Scope} (as : InstanceArgs 0 [] Δ) (Ss : States 0 [])
    (gs : CorecBranches 0 []) :
    ∃ v H', EvalResume H n E Ps
        (Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps'.length)) w v H' ∧
      H.Extends H' ∧
      ((∃ (ts : Args 0 [] ps') (bs : List Nat),
          RedStar (sig.interpret ι) (Term.resume r D' qs ls ps as Ss gs κ χ S κs g)
            (.corec r D' qs ls ps as ts.terms Ss gs) ∧
          EqSubst sig ι (Context.empty.append S) ts.toSubst ts.toSubst ∧
          RunsAsArgs sig ι P H (fun l => r * Parameter.grades ps' l) ts bs S ∧
          H' = H ++ [.corec n E Ps bs] ∧ v = H.length) ∨
        (H' = H ∧ RunsAs sig ι P H (Term.resume r D' qs ls ps as Ss gs κ χ S κs g) v T)) := by
  obtain ⟨T', hT', -, con, hc, ts, i, bs, ⟨qs', ls', ps'', Δ', as', hct⟩, hi, ha, hts, hruns⟩ :=
    RunsAs.ctor_inv hd hpre.step (qs := [κ.quality])
      (ls := [Telescope.packLevel κs (Telescope.packLevel κs .zero), κ.level])
      (ps := [r, Prelude.doneGrade κ.quality, χ]) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩ <;> cases i <;> rfl) hgv hg
  obtain rfl := List.mem_singleton.1 hT'
  rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩
  · -- A new state.
    obtain rfl := hd.nextCase hpre hi
    match ts, bs, hts, hruns with
    | .cons x .nil, [b], hts, hruns =>
      have hx := (EqSubst.args_cons_iff.1 hts).1
      have hred := fun (ts' : Args 0 [] ps') (hp' : Term.Packs sig ι x ts'.terms) =>
        RedStar.resume_next (r := r) (D := D') (qs := qs) (ls := ls) (ps := ps) (as := as)
          (Ss := Ss) (gs := gs) (κ := κ) (χ := χ) (S := S) (κs := κs) hpre hct.1 ts' hp'
      by_cases hrS : r ∈ Mode.oneOne.erased
      · -- The state is erased, and the new closure does not read it.
        obtain ⟨ts₁, ts₂, hp₁, hp₂, hτ⟩ := ValidEqTerm₀.pack_inv hpre S κs _ hx
        have e₀ := Args.terms_inj (Term.Packs.det hd hp₁ hp₂)
        subst e₀
        refine ⟨_, _, ?_, List.prefix_append _ _, .inl ⟨ts₁, List.replicate ps'.length b,
          hred ts₁ hp₁, hτ, RunsAsArgs.of_erased ts₁ _ S (fun l p _ =>
            (by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased) r
              _ hrS) List.length_replicate, rfl, rfl⟩⟩
        simp only [hrS, decide_true, Resumption.ofArity, ↓reduceIte]
        exact .erased ha
      · -- The state is used, and the new closure unpacks it.
        obtain ⟨ts', bs', hp', hτ, hu, hrs⟩ := RunsAs.unpack hd hpre S κs _ hx (hruns.1 hrS)
        refine ⟨_, _, ?_, List.prefix_append _ _, .inl ⟨ts', bs', hred ts' hp', hτ,
          RunsAsArgs.of_counted (fun l h => (by decide : ∀ r u : Grade,
            r * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) r (Parameter.grades ps' l) h) hrs,
          rfl, rfl⟩⟩
        simp only [hrS, decide_false, Resumption.ofArity, Bool.false_eq_true, ↓reduceIte]
        exact .next ha hu
  · -- A term already built.
    obtain rfl := hd.doneCase hpre hi
    match ts, bs, hruns with
    | .cons t .nil, [b], hruns =>
      have hne : Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps'.length) ≠
          .none := by
        cases decide (r ∈ Mode.oneOne.erased) <;> intro h <;> cases h
      refine ⟨b, H, .done hne ha, List.prefix_refl _, .inr ⟨rfl, ?_⟩⟩
      rw [RunsAs.redStar_iff hd (RedStar.resume_done hpre hct.1)]
      exact hruns.1 (by
        show Prelude.doneGrade κ.quality ∉ Mode.oneOne.erased
        rw [hκ]
        decide)

end

end Sic.Core
