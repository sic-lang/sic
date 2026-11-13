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
import Sic.Core.RunTime.Substitution
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

A corecursor is related to the address of the closure of its branches that its erasure allocates,
by coinduction: the relations of `(®_ν)`, joined with the corecursors of the block from states
related to the addresses of such closures, are consistent with the clauses of `(®_ν)`, since an
observation by a destructor whose grade is used at run time runs its branch, valid at run time at
the state and the arguments, and gives the observation, or a position that it resumes into a new
closure of the same branches or into a term already built.
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
          ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ps.map (·.usage.run)) bs w H'' tr ∧
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
        refine ⟨_, _, hi, hRΘ, fun H' hH' ts bs hts ϖ' => ?_⟩
        obtain ⟨w, H'', tr, hev, hw⟩ := hrun hp H' hH' ts bs hts ϖ'
        have htt := RunTelRel.fieldsRel hd (fun m _ => levelRel_isPer hd m) hRΘ (fun _ => rfl) _ _
          hΘ (fun _ => rfl) H' ts.terms bs hts
        obtain ⟨v, hv'⟩ := hB ts htt
        exact ⟨w, H'', tr, hev, (hRv ts htt v hv').runsAs hv' hw⟩
    · rename_i D' hr
      obtain ⟨rfl, -⟩ := hv
      obtain ⟨R, hR0, hRr⟩ := hR 0 D' hr
      cases hS with
      | cons _ _ _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | recursive hi hrs hRΘ _ _ =>
        rw [hR0] at hrs
        cases hrs
        obtain ⟨hrun, -⟩ := ho
        refine ⟨_, _, hi, hRΘ, fun H' hH' ts bs hts ϖ' => ?_⟩
        obtain ⟨w, H'', tr, hev, hw⟩ := hrun hp H' hH' ts bs hts ϖ'
        refine ⟨w, H'', tr, hev, ?_⟩
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
    (ϖ₀ : Multiplicity) {ts : Args 0 [] ps'} {bs : List Nat}
    (hts : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst ts.toSubst)
    (hbs : RunsAsArgs sig ι P H' (Parameter.grades ps') ts bs
      ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
    ∃ i w H'' tr, sig.destructorCase D d = some i ∧
      EvalObs P ϖ₀ H' a i (ps'.map (·.usage.run)) bs w H'' tr ∧ H'.Extends H'' ∧
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
  obtain ⟨w, H'', tr, hev, hw⟩ := hobsR H' hH' ts bs hRΘts ϖ₀
  refine ⟨i, w, H'', tr, hD ▸ hi, hev, hev.extends, ?_⟩
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
  intro ϖ₀ σ H E V hσ hEV hE
  have hS := Mode.erasesUncounted .oneOne
  have hEγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ h')) hE
  have hEδ : RunsAsSubst sig ι P H ctx δ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
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
  obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr ϖ₀ σ H E V hσ hEV hEγ
  obtain ⟨bs', H₂, tr₂, hevs, hH₂, hruns⟩ := hbr ϖ₀ σ H₁ E V hσ (hEV.mono hH₁) (hEδ.mono hd hH₁ ctx)
  rw [hΘ] at hruns
  have hbsσ := hbs.2 σ σ hσ
  rw [hΘ] at hbsσ
  obtain ⟨i, w, H₃, tr₃, hi, hevo, hH₃, hrun⟩ := RunsAs.obs hd h hv hq hl hp hadm (has.2 σ σ hσ) hpos
    hpr hprop (ht.2 σ σ hσ) hta hH₂ ϖ₀ hbsσ hruns
  have he : (Term.obs D qs ls ps as t d bs.terms).erase sig Mode.oneOne.erased hΓ =
      .obs (t.erase sig Mode.oneOne.erased hΓ) i
        (bs.terms.erase sig Mode.oneOne.erased hΓ (ps'.map (·.usage))) := by
    rw [Term.erase, hi, hd.argumentGrades h hq hp hpos]
    rfl
  refine ⟨w, H₃, tr₁ ++ (tr₂ ++ tr₃), he ▸ .obs hev hevs
    (by rw [Args.multiplicities_erase]; exact hevo), hH₁.trans (hH₂.trans hH₃), ?_⟩
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
entry, when its grade is used at run time, and at the multiplicity at run time of its grade, in a
signature whose names are distinct and that holds the prelude. -/
theorem RunsAs.unpack (hd : sig.Distinct) (hpre : sig.HasPrelude) {H : Heap} :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → (κs : List (Universe 0)) → (l : Level 0) →
      {x : Term 0 []} → {a : Nat} → ValidTerm₀ sig ι x (Θ.pack κs l) →
      RunsAs sig ι P H x a (Θ.pack κs l) →
      ∃ (ts : Args 0 [] ps) (as : List Nat), Term.Packs sig ι x ts.terms ∧
        EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst ∧
        Unpack H ps.length a (ps.map (·.usage.run)) as ∧
        RunsAsArgs sig ι P H (Parameter.grades ps) ts as Θ
  | [], .nil, _, l, _, _, hx, hr => by
    obtain ⟨T', hT', -, con, hc, ts, i, bs, hct, -, ha, -, hruns⟩ := RunsAs.ctor_inv hd hpre.unit
      (qs := []) (ls := [l]) (ps := []) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rfl) hx hr
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    match ts, bs, hruns with
    | .nil, [], _ =>
      -- The unit stores no field.
      refine ⟨.nil, [], ?_, (EqSubst.empty_iff _ _).2 trivial,
        .zero (ha : H[_]? = some (Value.ctor i [] [])), trivial⟩
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
      -- The pair stores its entry at the multiplicity of its grade, and the others at `1`.
      have ha' : _ = some (Value.ctor 0 [p.usage.run, .one] [b, c]) := ha
      have hone : ∀ πs : List Multiplicity, πs.map (Multiplicity.one * ·) = πs := fun πs => by
        induction πs with
        | nil => rfl
        | cons π πs ih =>
          rw [List.map_cons, ih]
          exact congrArg (· :: πs) ((by decide : ∀ π : Multiplicity, .one * π = π) π)
      have hu' := Unpack.pair ha' hu
      rw [hone] at hu'
      refine ⟨.cons t ts', b :: as', ?_, EqSubst.args_cons_iff.2 ⟨ht, hτ⟩, hu', hb, hrs⟩
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
arguments are related at the grades of the state times `r`, each at the multiplicity at run time of
this grade, which it unpacks from the new state when `r` is used at run time, and takes at the
address of the new state otherwise, without reading it; or the position computes to a term already
built, related to the address that its resumption gives. -/
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
          H' = H ++ [.corec n E Ps (ps'.map fun p => (r * p.usage).run) bs] ∧ v = H.length) ∨
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
        have hz : (ps'.map fun p => (r * p.usage).run) = List.replicate ps'.length .zero :=
          List.eq_replicate_iff.2 ⟨List.length_map .., fun π hπ => by
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hπ
            exact (Mode.erased_values.1 _).1
              ((by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased)
                r p.usage hrS)⟩
        rw [hz]
        -- The field of `next` has the multiplicity at run time of `r`, erased.
        have ha' : H[w]? = some (.ctor 0 [r.run] [b]) := ha
        rw [(Mode.erased_values.1 _).1 hrS] at ha'
        exact .erased ha'
      · -- The state is used, and the new closure unpacks it.
        obtain ⟨ts', bs', hp', hτ, hu, hrs⟩ := RunsAs.unpack hd hpre S κs _ hx (hruns.1 hrS)
        refine ⟨_, _, ?_, List.prefix_append _ _, .inl ⟨ts', bs', hred ts' hp', hτ,
          RunsAsArgs.of_counted (fun l h => (by decide : ∀ r u : Grade,
            r * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) r (Parameter.grades ps' l) h) hrs,
          rfl, rfl⟩⟩
        simp only [hrS, decide_false, Resumption.ofArity, Bool.false_eq_true, ↓reduceIte]
        have ha' : H[w]? = some (.ctor 0 [r.run] [b]) := ha
        have hev := EvalResume.next (n := n) (E := E) (Ps := Ps) ha' hu
        rwa [List.map_map] at hev
  · -- A term already built.
    obtain rfl := hd.doneCase hpre hi
    match ts, bs, hruns with
    | .cons t .nil, [b], hruns =>
      have hne : Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps'.length) ≠
          .none := by
        cases decide (r ∈ Mode.oneOne.erased) <;> intro h <;> cases h
      -- The field of `done` has the multiplicity at run time of its grade, used at run time.
      have hq : Prelude.doneGrade κ.quality ∉ Mode.oneOne.erased := by
        rw [hκ]
        decide
      have ha' : H[w]? = some (.ctor 1 [(Prelude.doneGrade κ.quality).run] [b]) := ha
      refine ⟨b, H, .done hne ha' fun h0 => hq ((Mode.erased_values.1 _).2 h0), List.prefix_refl _,
        .inr ⟨rfl, ?_⟩⟩
      rw [RunsAs.redStar_iff hd (RedStar.resume_done hpre hct.1)]
      exact hruns.1 hq

/-! ## Signatures -/

/-- An entry that does not introduce the name `D` gives the case of no destructor of `D`. -/
theorem Entry.destructorCase_of_not_mem {D d : Name} :
    {e : Entry} → D ∉ e.names → Entry.destructorCase D d e = none
  | .typeDeclaration decl, hD => by
    simp only [Entry.destructorCase]
    refine List.findIdx?_eq_none_iff.2 fun x hx => ?_
    have hT := (TypeDeclaration.mem_casesFrom hx).1
    cases h : (x.2.1.name == D) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.1 h ▸ TypeDeclaration.codata_name_mem_names hT) hD
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- A signature none of whose entries introduces the name `D` gives the case of no destructor of
`D`. -/
theorem Signature.destructorCase_of_not_mem {D d : Name} :
    {sig : Signature} → (∀ e ∈ sig, D ∉ e.names) → sig.destructorCase D d = none
  | [], _ => rfl
  | e :: sig, h => by
    unfold Signature.destructorCase
    rw [List.findSome?_cons_of_isNone
      (by rw [Entry.destructorCase_of_not_mem (h e List.mem_cons_self)]; rfl)]
    exact Signature.destructorCase_of_not_mem fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- In a signature whose names are distinct, the case of a destructor of a codata type is its case in
the block of its declaration. -/
theorem Signature.Distinct.destructorCase {d : Name} : {sig : Signature} → sig.Distinct →
    {D : Name} → {decl : TypeDeclaration} →
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} → sig.HasCodataType D decl T →
    sig.destructorCase D d = Entry.destructorCase D d (.typeDeclaration decl)
  | [], _, _, _, _, h => nomatch h.1
  | e :: sig, ⟨hd, _, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩ => by
    unfold Signature.destructorCase
    rcases List.mem_cons.1 he with rfl | he'
    · cases hc : Entry.destructorCase D d (.typeDeclaration decl) with
      | some i => rw [List.findSome?_cons_of_isSome (by rw [hc]; rfl), hc]
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hc]; rfl)]
        exact Signature.destructorCase_of_not_mem fun e' he'' hDe =>
          hfresh _ he'' D (hD ▸ TypeDeclaration.codata_name_mem_names hT) hDe
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.destructorCase_of_not_mem hDe]; rfl)]
      exact hd.destructorCase ⟨he', hT, hD⟩

/-- In a signature whose names are distinct, a case of the corecursors of a block is the case of its
destructor. -/
theorem Signature.Distinct.destructorCase_of_codataCases (hd : sig.Distinct)
    {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig) {i j : Nat}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {d : Name}
    (hi : decl.codataCases[i]? = some (j, T, d)) : sig.destructorCase T.name d = some i := by
  have hT := (TypeDeclaration.mem_casesFrom (List.mem_of_getElem? hi)).1
  rw [hd.destructorCase ⟨hdecl, hT, rfl⟩]
  show decl.codataCases.findIdx? (fun x => x.2.1.name == T.name && x.2.2 == d) = some i
  have hs := List.findIdx?_isSome_of_mem (p := fun x => x.2.1.name == T.name && x.2.2 == d)
    (List.mem_of_getElem? hi) (by simp only [Bool.and_eq_true, beq_iff_eq, and_self])
  cases h : decl.codataCases.findIdx? (fun x => x.2.1.name == T.name && x.2.2 == d) with
  | none => rw [h] at hs; cases hs
  | some i' =>
    obtain ⟨x, hx, hpx⟩ := List.getElem?_of_findIdx?_eq_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hpx
    exact congrArg some (List.getElem?_inj_of_nodup_map (hd.codataCases_nodup hdecl) hx hi
      (by rw [hpx.1, hpx.2]))

/-- An entry that does not introduce the name `D` gives the types resumed by the destructors of no
block of `D`. -/
theorem Entry.resumedTypes_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.resumedTypes D qs ps e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.codataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.codata_name_mem_names hT)
    simp only [Entry.resumedTypes]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.map_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- In a signature whose names are distinct, the types resumed by the destructors of the cases of the
block of a codata type are the positions of the types that their results name, at the instance. -/
theorem Signature.Distinct.resumedTypes : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.resumedTypes D qs ps = some (decl.codataCases.map fun x =>
      ((x.2.1.body (.ofLists qs ps hq hp)).resultName decl.names x.2.2).bind decl.names.idxOf?)
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    unfold Signature.resumedTypes
    rcases List.mem_cons.1 he with rfl | he'
    · have hg : Entry.resumedTypes D qs ps (.typeDeclaration decl) = some (decl.codataCases.map
          fun x => ((x.2.1.body (.ofLists qs ps hq hp)).resultName decl.names x.2.2).bind
            decl.names.idxOf?) := by
        simp only [Entry.resumedTypes, hq, hp, ↓reduceDIte, ← hD,
          List.find?_of_nodup_map (TypeDeclaration.codataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.resumedTypes_of_not_mem hDe]; rfl)]
      exact hd.resumedTypes ⟨he', hT, hD⟩ hq hp

/-! ## Erasure -/

/-- The grade of the mode of a destructor with a use at run time is `1`. -/
theorem Mode.grade_odot_of_not_erased :
    ∀ p : Grade, p ∉ Mode.oneOne.erased → (Mode.oneOne ⊙ p).grade = Grade.one := by
  decide

/-- The branch at a position of the erased branches of a corecursor, without non-uniform
parameters, is the erasure of the branch at this position, at the grade `p` of its destructor, with
the resumption at this position, and the multiplicities `run(⌜11ᵐ ⊙ p⌝ · q)` of its binders, for
the grades `q` of the entries of the state and of the arguments at this position. -/
theorem CorecBranches.get_erase (S : Math.Set Grade) [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (gs : CorecBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
      (pss : List (List Grade × List Grade)) → {i b c : Nat} →
      {g : Term k ((Γ.extend b).extend c)} → gs.get i = some ⟨0, b, c, g⟩ → {p : Grade} →
      ps[i]? = some p →
      (gs.erase sig S hΓ ps ks pss).get i = some (ks.getD i .none, ⟨b, c,
        fun j => (((pss.drop i).headD ([], [])).1[(j : Nat)]?.map
          fun q => ((Mode.oneOne ⊙ p).grade * q).run).getD .omega,
        fun j => (((pss.drop i).headD ([], [])).2[(j : Nat)]?.map
          fun q => ((Mode.oneOne ⊙ p).grade * q).run).getD .omega,
        if p ∈ S then .erased else
          Scope.length_extend_extend Γ b c ▸ g.erase sig S ((hΓ.extend b).extend c)⟩)
  | .nil, _, _, _, _, _, _, _, h, _, _ => nomatch h
  | .cons 0 _ _ _ _, _ :: _, ks, pss, 0, _, _, _, h, _, hp => by
    cases h
    cases hp
    cases ks <;> rfl
  | .cons 0 _ _ _ _, [], _, _, 0, _, _, _, _, _, hp => nomatch hp
  | .cons (_ + 1) _ _ _ _, _, _, _, 0, _, _, _, h, _, _ => by cases h
  | .cons 0 _ _ _ vs, _ :: ps, ks, pss, i + 1, _, _, _, h, _, hp => by
    have e : ks.tail.getD i .none = ks.getD (i + 1) .none := by cases ks <;> simp
    have e' : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
    rw [← e, e']
    exact CorecBranches.get_erase S hΓ vs ps ks.tail pss.tail h hp
  | .cons 0 _ _ _ _, [], _, _, _ + 1, _, _, _, _, _, hp => nomatch hp
  | .cons (_ + 1) _ _ _ vs, ps, ks, pss, i + 1, _, _, _, h, p, hp => by
    have e : ks.tail.getD i .none = ks.getD (i + 1) .none := by cases ks <;> simp
    have e' : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
    have hp' : ps.tail[i]? = some p := by cases ps <;> simp_all
    rw [← e, e']
    exact CorecBranches.get_erase S hΓ vs ps.tail ks.tail pss.tail h hp'

/-- The erasure of terms at grades `r` times the grades `us` evaluates, at a weight, as their
erasure at `us` at the weight times `r`, when `r` is used at run time, since a grade times `r` is
used at run time when the grade is: the two erasures keep the same terms, each evaluated at the
weight times `r` times its grade, and differ only by the multiplicities at which they store them. -/
theorem Terms.evalAll_erase_mul_of_not_erased {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) {r : Grade}
    (hr : r ∉ Mode.oneOne.erased) {ϖ : Multiplicity} {E : List Nat} :
    (ts : Terms k Γ) → (us : List Grade) → {H H' : Heap} → {bs tr : List Nat} →
      EvalAll P (ϖ * r.run) H E (ts.erase sig Mode.oneOne.erased hΓ us) bs H' tr →
      EvalAll P ϖ H E (ts.erase sig Mode.oneOne.erased hΓ (us.map (r * ·))) bs H' tr
  | .nil, _, _, _, _, _, h => by
    cases h
    exact .nil
  | .cons _ ts, [], _, _, _, _, h => by
    cases h with
    | cons hM hMs =>
      cases hM
      exact .cons .erased (Terms.evalAll_erase_mul_of_not_erased hΓ hr ts [] hMs)
  | .cons _ ts, u :: us, _, _, _, _, h => by
    have hu := (by decide : ∀ r u : Grade, r ∉ Mode.oneOne.erased →
      (r * u ∈ Mode.oneOne.erased ↔ u ∈ Mode.oneOne.erased)) r u hr
    simp only [List.map_cons, Terms.erase, hu] at h ⊢
    cases h with
    | cons hM hMs =>
      refine .cons ?_ (Terms.evalAll_erase_mul_of_not_erased hΓ hr ts us hMs)
      rwa [show (r * u).run = r.run * u.run from rfl,
        ← Multiplicity.modality.semiring.mul_assoc]

/-- Arguments erased at grades that are all erased evaluate to `↯`, allocated one after the other,
at as many addresses as arguments, reading no cell. -/
theorem Args.evalAll_erased (S : Math.Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) (ϖ : Multiplicity) (E : List Nat) :
    {ps : List Parameter} → (ts : Args k Γ ps) → (us : List Grade) → (∀ u ∈ us, u ∈ S) →
      (H : Heap) → ∃ bs H', EvalAll P ϖ H E (ts.terms.erase sig S hΓ us) bs H' [] ∧
        H.Extends H' ∧ bs.length = ps.length
  | [], .nil, _, _, H => ⟨[], H, .nil, List.prefix_refl _, rfl⟩
  | _ :: _, .cons _ ts, [], _, H => by
    obtain ⟨bs, H', hev, hH, hl⟩ :=
      Args.evalAll_erased S hΓ ϖ E ts [] (fun _ h => nomatch h) (H ++ [.erased])
    exact ⟨H.length :: bs, H', .cons .erased hev, (List.prefix_append _ _).trans hH,
      congrArg (· + 1) hl⟩
  | _ :: _, .cons _ ts, u :: us, hu, H => by
    obtain ⟨bs, H', hev, hH, hl⟩ := Args.evalAll_erased S hΓ ϖ E ts us
      (fun u' h => hu u' (List.mem_cons_of_mem _ h)) (H ++ [.erased])
    refine ⟨H.length :: bs, H', ?_, (List.prefix_append _ _).trans hH, congrArg (· + 1) hl⟩
    simp only [Args.terms, Terms.erase, hu u List.mem_cons_self, ↓reduceIte]
    exact .cons .erased hev

/-! ## Corecursors -/

/-- Observations whose results are equal, destructor by destructor, at equal arguments, and whose
observations by each destructor whose grade is used at run time, at arguments related to addresses
in a heap that extends `H`, evaluate to addresses to which they are related, are related to the
address `a` by the relation of run time of the destructors, at instantiated levels: as terms of the
result of each destructor that is not recursive, and by the relation `R` that `rsR` gives each
recursive one, whose result is the instance of the block; the converse of `Destructors.Pos.run`. -/
theorem RunDesRel.of_obs (hd : sig.Distinct) {κ : Universe 0} {k' : Nat} (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {inst : Name → Term 0 Γ} →
      {rs : Nat → Option Name} → {θ θ' : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs (ds.substLevels L) θ θ' →
      {rsR : Nat → Option RunRel} → (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R, rsR i = some R) → {D : Name} → {S : RunObsRel} →
      RunDesRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) D rsR
        (ds.substLevels L) θ S →
      {H : Heap} → {o : Observations} → {a : Nat} →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o θ)))
          ts.toSubst us.toSubst → rs hpos.index = none →
        ValidEqTerm₀ sig ι ((o d ps).subst ts.toSubst) ((o d ps).subst us.toSubst)
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (i : Nat), p ∉ Mode.oneOne.erased →
        sig.destructorCase D d = some i → ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps)
        (bs : List Nat),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o θ)))
          ts.toSubst ts.toSubst →
        RunsAsArgs sig ι P H' (Parameter.grades ps) ts bs
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) →
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ps.map (·.usage.run)) bs w H'' tr ∧
          (rs hpos.index = none → RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
            ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) ∧
          ∀ D' R, rs hpos.index = some D' → rsR hpos.index = some R →
            (B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst) =
              (inst D').subst θ →
            R H'' ((o d ps).subst ts.toSubst) w) →
      S H o a
  | _, _, .nil, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q Θ B ψ ds, inst, rs, θ, θ', hm, rsR, hN, hS, D, S, h, H, o,
      a, hv, hr => by
    have ihm : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    rw [Destructors.substLevels, ValidEqDestructors₀] at hm
    obtain ⟨hΘm, hm⟩ := hm
    have hsw : ∀ (f : Term 0 (Scope.extend [] ps.length)) D',
        ((inst D').rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ f) =
          (inst D').subst θ := fun f D' => Term.subst_rename_of (fun _ => rfl) _
    have hv' := fun d' p' q' ps' Ξ' Θ' B' ψ' (hpos : ds.Pos d' p' q' Ξ' Θ' B' ψ') =>
      hv d' p' q' ps' Ξ' Θ' B' ψ' (.there hpos)
    have hrec : ∀ (d' : Name) (p' q' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope k' Ξ' ps') (B' : Term k' (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership ps'.length) (hpos : ds.Pos d' p' q' Ξ' Θ' B' ψ') (i : Nat),
        p' ∉ Mode.oneOne.erased → sig.destructorCase D d' = some i → ∀ H', H.Extends H' →
        ∀ (ts : Args 0 [] ps') (bs : List Nat),
        EqSubst sig ι (Context.empty.append ((Θ'.substLevels L).subst
          (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))))) ts.toSubst
          ts.toSubst →
        RunsAsArgs sig ι P H' (Parameter.grades ps') ts bs ((Θ'.substLevels L).subst
          (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps)))) →
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ps'.map (·.usage.run)) bs w H'' tr ∧
          (rs (hpos.index + 1) = none → RunsAs sig ι P H'' ((o d' ps').subst ts.toSubst) w
            ((B'.substLevels L).subst (Subst.append
              (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))) ts.toSubst))) ∧
          ∀ D' R, rs (hpos.index + 1) = some D' → rsR (hpos.index + 1) = some R →
            (B'.substLevels L).subst (Subst.append
              (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))) ts.toSubst) =
              ((inst D').rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps)) →
            R H'' ((o d' ps').subst ts.toSubst) w :=
      fun d' p' q' ps' Ξ' Θ' B' ψ' hpos i hp hi H' hH' ts bs hτ hbs ϖ' => by
        obtain ⟨w, H'', tr, hev, h₁, h₂⟩ :=
          hr d' p' q' ps' Ξ' Θ' B' ψ' (.there hpos) i hp hi H' hH' ts bs hτ hbs ϖ'
        exact ⟨w, H'', tr, hev, h₁, fun D' R hD' hR e => h₂ D' R hD' hR (e.trans (hsw _ D'))⟩
    have hgr : ∀ l (p' : Parameter), ps[l]? = some p' → Parameter.grades ps l ∉ Mode.oneOne.erased →
        p'.usage ∉ Mode.oneOne.erased := fun _ _ hl h => Parameter.grades_of_getElem? hl ▸ h
    split at hm
    · rename_i hr0
      obtain ⟨-, hds⟩ := hm
      cases h with
      | recursive _ hrs => rw [hN 0 hr0] at hrs; cases hrs
      | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ RΘ i hi hΘ hRΘ F R hB hF hR G hG _ =>
        have hSp := TelRel.isPer hd ihm (fun _ _ h => by cases h) hΘ
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        have hA : AbstractionRel SΘ F (o d ps) (o d ps) := fun ts us hts => by
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv''⟩ := hB ts htt
          exact (hF ts htt v hv'').of_validEqTerm hv'' (hv d p q ps _ Θ B ψ .here ts us
            ((hT ts us).1 hts) hr0)
        have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst θ))
            τ₁ τ₂ → ValidEqTerm₀ sig ι ((o d ps).subst τ₁) ((o d ps).subst τ₂)
              ((B.substLevels L).subst (Subst.append θ τ₁)) := fun τ₁ τ₂ hτ => by
          obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
            ⟨_, Subst.args_toSubst ps τ₁⟩
          obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
            ⟨_, Subst.args_toSubst ps τ₂⟩
          have hts := (hT ts us).2 hτ
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv''⟩ := hB ts htt
          exact (hF ts htt v hv'').validEqTerm hd hv'' (hA ts us hts)
        refine ⟨hA, fun hp H' hH' ts bs hts ϖ' => ?_, RunDesRel.of_obs hd L ds (hds _ _ hcond)
          (fun i => hN (i + 1)) (fun i => hS (i + 1)) (hG _ hA) hv' hrec⟩
        have htt := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H'
          ts.terms bs hts
        have hτ := (hT ts ts).1 htt
        have hbs := RunsAsArgs.of_runTelRel hRΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h) _
          hgr ts hτ bs hts
        obtain ⟨w, H'', tr, hev, hw, -⟩ :=
          hr d p q ps _ Θ B ψ .here i hp hi H' hH' ts bs hτ hbs ϖ'
        obtain ⟨v, hv''⟩ := hB ts htt
        exact ⟨w, H'', tr, hev, RunFieldRel.of_runsAs hd (hR ts htt v hv'') hv'' (hw hr0)⟩
    · rename_i D' hr0
      obtain ⟨hBD, hds⟩ := hm
      obtain ⟨R, hR0⟩ := hS 0 D' hr0
      cases h with
      | cons _ _ _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | recursive hi hrs hRΘ G hG =>
        rw [hR0] at hrs
        cases hrs
        obtain ⟨SΘ, hΘ₁, -⟩ := hΘm.telRel hd
        have hT := TelRel.eqSubst_iff hd hΘ₁
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        refine ⟨fun hp H' hH' ts bs hts ϖ' => ?_, RunDesRel.of_obs hd L ds (hds (o d ps) (o d ps))
          (fun i => hN (i + 1)) (fun i => hS (i + 1)) (hG _) hv' hrec⟩
        have htt := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ₁ (fun _ => rfl) H'
          ts.terms bs hts
        have hτ := (hT ts ts).1 htt
        have hbs := RunsAsArgs.of_runTelRel hRΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h) _
          hgr ts hτ bs hts
        obtain ⟨w, H'', tr, hev, -, hw⟩ :=
          hr d p q ps _ Θ B ψ .here _ hp hi H' hH' ts bs hτ hbs ϖ'
        have e : (B.substLevels L).subst (Subst.append θ ts.toSubst) = (inst D').subst θ := by
          rw [hBD, Term.subst_append_rename_weakenN]
        exact ⟨w, H'', tr, hev, hw D' R hr0 hR0 e⟩

/-- The extension of a vector by the variables of a telescope at the grades of their entries times
`r` is its extension by these grades times `r`, at their positions. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_eq_extendGrades {Γ : Scope} :
    (γ : GradeVector Γ.length) → (r : Grade) → (ps : List Parameter) →
    γ.extendParams r ps = γ.extendGrades (fun l => r * Parameter.grades ps l) ps
  | _, _, [] => rfl
  | γ, r, p :: ps => by
    rw [GradeVector.extendParams, GradeVector.extendGrades,
      extendParams_eq_extendGrades (Γ := .var :: Γ)]
    rfl

-- ADE: none.
/-- The branches of a corecursor whose destructors have a grade used at run time are valid at run
time with the grades `δs i` of the variables of the context, those of the entries of the state
`r` times their grades and those of the arguments their grades, at the results of their
destructors, as the usage of `(corec)` premises them in the mode `11ᵐ`: the premise that the Lean of
`(corec)` at run time reads. -/
def RunValidCorecBranches (sig : Signature) (ι : Interpretation) (P : Program) {Γ : Scope}
    (hΓ : Γ.FirstOrder) (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ) (gs : CorecBranches 0 Γ)
    (δs : Nat → GradeVector Γ.length) : Prop :=
  ∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps'') (p q : Grade)
    (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
    (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
    (g : Term 0 ((Γ.extend ps''.length).extend ps₁.length)),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
    gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → p ∉ Mode.oneOne.erased →
    RunValid sig ι P ((hΓ.extend _).extend _)
      ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
          ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst)))
      (((δs i).extendParams (Mode.oneOne.grade * r) ps'').extendParams Mode.oneOne.grade ps₁) g
      (Term.branchResult decl.names B
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted)
        ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
            ls ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))))

-- ADE: none.
/-- `(corec)` at run time, closed: a corecursor of a codata type of `Σ`, whose type declaration is
meaningful, from a closed state related to the addresses of a closure of its branches erased, at a
substitution of the context of its branches for which addresses stand as the grades `δ` require, is
related to the closure at its instance, in a signature whose names are distinct: the relations of the
corecursors of the block from such states and closures, together with `(®_ν)`, are consistent with
the clauses of `(®_ν)`, since an observation by a destructor whose grade is used at run time runs its
branch, valid at run time, and resumes its position into such a closure or into a term already
built. -/
theorem RunsAs.corec (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {Γ : Scope} {hΓ : Γ.FirstOrder}
    {ctx : Context 0 Γ} {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude)
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {δ : GradeVector Γ.length}
    {δs : Nat → GradeVector Γ.length}
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hgv : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs)
    (hgr : RunValidCorecBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as r Ss gs δs)
    (hδ : ∀ i j T' d (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership ps₁.length), decl.codataCases[i]? = some (j, T', d) →
      (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ → δ ≤ᶜ p ·ᶜ δs i)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ)
    (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx δ σ V) {j : Nat}
    {T' : CodataType decl.sorts decl.grades decl.levels decl.scope} {ps'' : List Parameter}
    {S' : Telescope 0 Γ ps''} (hj : decl.codataTypes[j]? = some T')
    (hS' : Ss.get j = some ⟨0, ps'', S'⟩) {ts : Args 0 [] ps''} {bs : List Nat}
    (hts : EqSubst sig ι (Context.empty.append (S'.subst σ)) ts.toSubst ts.toSubst)
    (hbs : RunsAsArgs sig ι P H (fun l => r * Parameter.grades ps'' l) ts bs (S'.subst σ))
    {a : Nat} (ha : H[a]? = some (.corec Γ.length E
      (gs.erase sig Mode.oneOne.erased hΓ ((sig.destructorGrades D qs ps).getD [])
        (((sig.resumedTypes D qs ps).getD []).map
          fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity))
        (((sig.destructorArguments D qs ps).getD []).map fun ⟨j, as⟩ =>
          ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map (r * ·.usage), as)))
      (ps''.map fun p => (r * p.usage).run) bs)) :
    RunsAs sig ι P H (.corec r T'.name qs ls ps (as.subst σ) ts.terms (Ss.subst σ) (gs.subst σ)) a
      (.inst T'.name qs ls ps (as.subst σ)) := by
  obtain ⟨hdecl, hT, hD⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hn := TypeDeclaration.codataTypes_nodup hnd
  have hT' : T' ∈ decl.codataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) hasσ
  have hmean : ∀ T₁ ∈ decl.codataTypes, _ := fun T₁ hT₁ =>
    (hv.destructors I hadm hT₁ ρ).2 _ _ hθ
  have hw : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  cases hs : (decl.sort I).quality with
  | prop =>
    -- A proposition, whose proofs are related to every address.
    obtain ⟨_, -, hPr⟩ := hv.codataPropRel hd hdecl hq hl hp hadm hasσ hs
    exact ⟨_, hw _, .inl ⟨_, _, levelRel_prop_iff.2 (hPr T' hT').1⟩⟩
  | type =>
    -- The relations of run time of the instances of the block.
    obtain ⟨Sr, hU⟩ := hv.codataRunUnivRel hd hdecl hq hl hp hadm hasσ hs P
    obtain ⟨n, S, hnS, hS, -⟩ := HasRun.codata hd (D := T'.name) ⟨hdecl, hT', rfl⟩ hq hl hp
      (.univ _ (levelRel_run_iff.2 (hU T' hT').1)) hs
    have hFR : ∀ T₁ ∈ decl.codataTypes, RunFieldRel sig ι P n (fun m _ => levelRel sig ι m)
        (.inst T₁.name qs ls ps (as.subst σ))
        ((CodataType.runBlockRel decl.codataTypes S T₁.name).computed sig ι) := fun T₁ hT₁ =>
      .univ (.codata ⟨hdecl, hT₁, rfl⟩ hq hl hp rfl hs hnS S hS)
    have hmono : ∀ X Y : Name → RunRel, (∀ D' H₁ v b, X D' H₁ v b → Y D' H₁ v b) →
        ∀ T₁ ∈ decl.codataTypes, ∀ H₁ o b, S X T₁ H₁ o b → S Y T₁ H₁ o b :=
      fun X Y hXY T₁ hT₁ H₁ => RunDesRel.mono hd (List.prefix_refl H₁) (hS X T₁ hT₁) _ _
        (hS Y T₁ hT₁) (fun _ => Option.rel_map (fun D' H₂ _ _ => RunRel.computed_mono (hXY D' H₂)) _)
    have e : ((decl.sort I).atLevels ρ).level.closedValue = n :=
      (Level.closedValue_subst_equiv hls (decl.sort I).level).trans hnS
    have hX : ∀ D', Term.LevelEquiv
        (((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst (as.subst σ).toSubst)
        (.inst D' qs ls ps (as.subst σ)) := fun D' =>
      decl.blockInstance_atLevels_subst hq hl hp (as.subst σ) D'
    -- The grades of the destructors and the resumptions that the erasure of the closure reads.
    obtain ⟨grs, hgrs, hgrs'⟩ := hd.destructorGrades h hq hp
    have hrt := hd.resumedTypes h hq hp
    let ks : List Resumption := ((sig.resumedTypes D qs ps).getD []).map
      fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity)
    let pss : List (List Grade × List Grade) :=
      ((sig.destructorArguments D qs ps).getD []).map fun ⟨j, as⟩ =>
        ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map (r * ·.usage), as)
    let Ps := gs.erase sig Mode.oneOne.erased hΓ ((sig.destructorGrades D qs ps).getD []) ks pss
    -- The corecursors of the block from closed states related to the addresses of closures of the
    -- branches, joined with `(®_ν)`.
    let Clo : Name → RunRel := fun D' H₁ v b =>
      ∃ (j₁ : Nat) (T₁ : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (ps₁ : List Parameter) (S₁ : Telescope 0 Γ ps₁) (ts₁ : Args 0 [] ps₁) (bs₁ : List Nat),
        decl.codataTypes[j₁]? = some T₁ ∧ T₁.name = D' ∧ Ss.get j₁ = some ⟨0, ps₁, S₁⟩ ∧
        EqSubst sig ι (Context.empty.append (S₁.subst σ)) ts₁.toSubst ts₁.toSubst ∧
        H.Extends H₁ ∧
        RunsAsArgs sig ι P H₁ (fun l => r * Parameter.grades ps₁ l) ts₁ bs₁ (S₁.subst σ) ∧
        H₁[b]? = some (.corec Γ.length E Ps (ps₁.map fun p => (r * p.usage).run) bs₁) ∧
        v = .corec r D' qs ls ps (as.subst σ) ts₁.terms (Ss.subst σ) (gs.subst σ)
    let X : Name → RunRel := fun D' H₁ v b =>
      CodataType.runBlockRel decl.codataTypes S D' H₁ v b ∨ Clo D' H₁ v b
    have hcons : ∀ T₁ ∈ decl.codataTypes, ∀ H₁ v b, X T₁.name H₁ v b →
        runCorecRel T₁.name (S X T₁) H₁ v b := by
      intro T₁ hT₁ H₁ v b hx
      rcases hx with ⟨X', hX', hx'⟩ | ⟨j₁, T₂, ps₁, S₁, ts₁, bs₁, hj₁, hn₁, hS₁, hts₁, hH₁, hbs₁,
        hb, rfl⟩
      · exact runCorecRel_mono (fun o b' => hmono X' X (fun D' H₂ v' b'' h => .inl ⟨X', hX', h⟩)
          T₁ hT₁ H₁ o b') (hX' T₁ hT₁ H₁ v b hx')
      obtain rfl : T₂ = T₁ := List.eq_of_nodup_map hn (List.mem_of_getElem? hj₁) hT₁ hn₁
      have h₀ : sig.HasCodataType T₂.name decl T₂ := ⟨hdecl, hT₁, rfl⟩
      refine ⟨_, ⟨r, qs, ls, ps, _, as.subst σ, ts₁.terms, Ss.subst σ, gs.subst σ, rfl, rfl⟩, ?_⟩
      have hSρ : RunDesRel sig ι P ((decl.sort I).atLevels ρ).level.closedValue
          (fun m _ => levelRel sig ι m) T₂.name
          (fun i => ((T₂.body I).recursionAt decl.names i).map fun D' => (X D').computed sig ι)
          ((T₂.body I).substLevels Lρ) (as.subst σ).toSubst (S X T₂) := by
        rw [e]
        exact RunDesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) (hS X T₂ hT₁)
          (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
          (Subst.LevelEquiv.refl _)
      -- The case of a destructor of the type and its branch.
      have hcase : ∀ {d p q ps' Ξ} {Θ : Telescope decl.levels Ξ ps'}
          {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length},
          (T₂.body I).Pos d p q Ξ Θ B ψ → ∃ i g, decl.codataCases[i]? = some (j₁, T₂, d) ∧
            gs.get i = some ⟨0, ps₁.length, ps'.length, g⟩ := fun {d p q ps' Ξ Θ B ψ} hpos => by
        have hm := TypeDeclaration.mem_casesFrom_of (f := CodataType.destructors) (i := 0) hj₁
          hpos.mem
        rw [Nat.zero_add] at hm
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
        obtain ⟨g, -, hg, -⟩ := hgv.1 i j₁ T₂ d ps₁ S₁ hi hS₁ p q ps' Ξ Θ B ψ hpos
        exact ⟨i, g, hi, hg⟩
      refine RunDesRel.of_obs hd Lρ (T₂.body I) (hmean T₂ hT₁) (fun i hi => by rw [hi]; rfl)
        (fun i D' hi => by rw [hi]; exact ⟨_, rfl⟩) hSρ ?_ ?_
      · -- The observations by a destructor that is not recursive step to its branch, whose
        -- premise makes it a term of the result of the destructor.
        intro d p q ps' Ξ Θ B ψ hpos ts₂ us₂ hτ hr0
        obtain ⟨i, g, hi, hg⟩ := hcase hpos
        have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
          (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
            (Telescope.substLevels_levelEquiv hls Θ))) hτ
        have hb := ValidEqTerm₀.corecBranch hpos
          (hgv.2 i j₁ T₂ d ps₁ S₁ p q ps' Ξ Θ B ψ g g hi hS₁ hpos hg hg) hσ hts₁ hτ'
        have hred₁ := Red.beta_corec (ι := ι) hd h₀ hq hl hp hi hpos hg σ ts₁ ts₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hred₂ := Red.beta_corec (ι := ι) hd h₀ hq hl hp hi hpos hg σ ts₁ us₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hbn : B.blockName decl.names = none := by
          rw [← hpos.recursionAt_index]
          exact hr0
        simp only [Term.branchResult, hbn] at hb
        simp only [Term.observed, hbn] at hred₁ hred₂
        rw [Term.observation_subst_args, Term.observation_subst_args]
        exact (((ValidEqTerm₀.red_iff hd hred₂).2
          ((ValidEqTerm₀.red_iff hd hred₁).2 hb).symm).symm).levelEquiv (Term.LevelEquiv.refl _)
          (Term.LevelEquiv.refl _) (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
            (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
      · -- The observation by a destructor whose grade is used at run time runs its branch, valid
        -- at run time, and resumes its value.
        intro d p q ps' Ξ Θ B ψ hpos i' hpr hi' H₂ hH₂ ts₂ bs₂ hτ hbs₂ ϖ₀
        obtain ⟨i, g, hi, hg⟩ := hcase hpos
        obtain rfl : i' = i :=
          Option.some.inj (hi'.symm.trans (hd.destructorCase_of_codataCases hdecl hi))
        have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
          (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
            (Telescope.substLevels_levelEquiv hls Θ))) hτ
        have hbs₂' := hbs₂.levelEquiv (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
          (Telescope.substLevels_levelEquiv hls Θ))
        -- The branch in the closure, at the grade of its destructor.
        have hpg : ((sig.destructorGrades D qs ps).getD [])[i']? = some p := by
          rw [hgrs]
          exact hgrs' i' j₁ T₂ d hi p (hpos.grade (hd.destructors_nodup h₀))
        have hget :=
          CorecBranches.get_erase (sig := sig) Mode.oneOne.erased hΓ gs _ ks pss hg hpg
        simp only [hpr, ↓reduceIte] at hget
        -- The grades of the entries of the state and of the arguments of the branch.
        have hpss : (pss.drop i').headD ([], []) = (ps₁.map (r * ·.usage), ps'.map (·.usage)) :=
          List.headD_drop_of_getElem? (by
            simp [pss, hd.destructorArguments h hq hp, hi, hS₁]
            rw [hpos.arguments (hd.destructors_nodup h₀)]
            rfl)
        rw [hpss, Mode.grade_odot_of_not_erased p hpr] at hget
        -- The uses of each entry and of each argument by the branch are those that the closure
        -- and the observation allow.
        have hπ₁ : ∀ j : Fin ps₁.length, ∃ π₁,
            (ps₁.map fun p => (r * p.usage).run)[(j : Nat)]? = some π₁ ∧
            π₁ ≤ ((ps₁.map (r * ·.usage))[(j : Nat)]?.map
              fun q => (Grade.one * q).run).getD .omega := fun j =>
          ⟨_, List.getElem?_eq_getElem (by simp), by
            simp only [List.getElem?_map, List.getElem?_eq_getElem j.2, Option.map_some,
              Option.getD_some, List.getElem_map, Grade.modality.semiring.one_mul]
            exact (by decide : ∀ π : Multiplicity, π ≤ π) _⟩
        have hπ₂ : ∀ j : Fin ps'.length, ∃ π₂,
            (ps'.map (·.usage.run))[(j : Nat)]? = some π₂ ∧
            π₂ ≤ ((ps'.map (·.usage))[(j : Nat)]?.map
              fun q => (Grade.one * q).run).getD .omega := fun j =>
          ⟨_, List.getElem?_eq_getElem (by simp), by
            simp only [List.getElem?_map, List.getElem?_eq_getElem j.2, Option.map_some,
              Option.getD_some, List.getElem_map, Grade.modality.semiring.one_mul]
            exact (by decide : ∀ π : Multiplicity, π ≤ π) _⟩
        -- The context of the branch, at the grades of its variables.
        have hc := fun (a' : Scope.Entry) (x : Var Ξ a') =>
          hpos.obsSubst_corecAt σ r T₂.name qs ls ps as Ss gs ts₁
            (InstanceArgs.toSubst_rename_subst_append σ as ts₁) x
        have hEq := (EqSubst.append_append_iff (ctx.append S₁) _ _ _ _ _).2
          ⟨(EqSubst.append_append_iff ctx S₁ _ _ _ _).2 ⟨hσ, hts₁⟩,
            by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hτ'⟩
        have hδi : RunsAsSubst sig ι P H₂ ctx (δs i') σ V :=
          RunsAsSubst.of_counted ctx (fun x hx => (by decide : ∀ c p u : Grade, c ≤ p * u →
            p ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased → c ∉ Mode.oneOne.erased) _ _ _
            (hδ i' j₁ T₂ d p q ps' Ξ Θ B ψ hi hpos x) hpr hx) (hE.mono hd (hH₁.trans hH₂))
        have hbs₁' : RunsAsArgs sig ι P H₂
            (fun l => (Mode.oneOne.grade * r) * Parameter.grades ps₁ l) ts₁ bs₁ (S₁.subst σ) :=
          RunsAsArgs.of_counted (fun l h' => (by decide : ∀ r u : Grade,
            (Mode.oneOne.grade * r) * u ∉ Mode.oneOne.erased → r * u ∉ Mode.oneOne.erased) r _ h')
            (hbs₁.mono hd hH₂)
        have hbs₂'' := RunsAsArgs.of_counted (g' := fun l => Mode.oneOne.grade *
          Parameter.grades ps' l) (fun l h' => (by decide : ∀ u : Grade,
            Mode.oneOne.grade * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) _ h') hbs₂'
        have hσr := RunsAsSubst.append (ctx.append S₁) _ (RunsAsSubst.append ctx S₁ hδi hbs₁')
          (by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hbs₂'')
        have hbr := hgr i' j₁ T₂ d ps₁ S₁ p q ps' Ξ Θ B ψ g hi hS₁ hpos hg hpr
        rw [GradeVector.extendParams_eq_extendGrades,
          GradeVector.extendParams_eq_extendGrades] at hbr
        -- The branch binds its variables to cells, at the multiplicities of its binders.
        let πs₁ : Fin ps₁.length → Multiplicity := fun j =>
          ((ps₁.map (r * ·.usage))[(j : Nat)]?.map fun q => (Grade.one * q).run).getD .omega
        let πs₂ : Fin ps'.length → Multiplicity := fun j =>
          ((ps'.map (·.usage))[(j : Nat)]?.map fun q => (Grade.one * q).run).getD .omega
        have hlen₁ := RunsAsArgs.length hbs₁
        have hlen₂ := RunsAsArgs.length hbs₂
        have hlen : ((List.ofFn πs₁ ++ List.ofFn πs₂).map (ϖ₀ * ·)).length =
            (bs₁ ++ bs₂).length := by
          simp only [List.length_map, List.length_append, List.length_ofFn, hlen₁, hlen₂]
        let H₂' := H₂.bind ((List.ofFn πs₁ ++ List.ofFn πs₂).map (ϖ₀ * ·)) (bs₁ ++ bs₂)
        have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
        have hB : H₂'.Binds ((List.range' H₂.length (bs₁ ++ bs₂).length).reverse ++ E)
            (bs₂.reverse ++ (bs₁.reverse ++ V)) := by
          have h' := (Heap.binds_bind H₂ hlen).reverse.append
            (hEV.mono (hH₁.trans (hH₂.trans hH₂')))
          rwa [List.reverse_append, List.append_assoc] at h'
        obtain ⟨w₀, H₃, tr, hev, hH₃, hrun⟩ := hbr ϖ₀ _ H₂' _ _ hEq hB (hσr.mono hd hH₂')
        rw [Term.branchResult_corecAt] at hrun
        have hev' := (Eval.cast (Scope.length_extend_extend Γ ps₁.length ps'.length)).2 hev
        have hclo : H₂[b]? =
            some (.corec Γ.length E Ps (ps₁.map fun p => (r * p.usage).run) bs₁) :=
          hH₂.getElem? hb
        have hred := Red.beta_corec (ι := ι) hd h₀ hq hl hp hi hpos hg σ ts₁ ts₂
          (D' := T₂.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ) (as := as)
          (Ss := Ss) (r := r)
        have hrn := hpos.resultName decl.names (hd.destructors_nodup h₀)
        rw [Term.observation_subst_args]
        cases hbn : B.blockName decl.names with
        | none =>
          -- The branch gives the observation.
          have hk : ks.getD i' .none = .none := by
            simp only [ks, hrt, Option.getD_some, List.map_map, List.getD_eq_getElem?_getD,
              List.getElem?_map, hi, Option.map_some, Function.comp_apply]
            rw [hrn, hbn]
            rfl
          rw [hk] at hget
          simp only [Term.branchResult, hbn] at hrun
          simp only [Term.observed, hbn] at hred
          refine ⟨w₀, H₃, tr, .beta hclo hget hlen₁ hlen₂ hπ₁ hπ₂ hev' .none, fun _ => ?_,
            fun D' R hD' => ?_⟩
          · exact ((RunsAs.redStar_iff hd (.step hred (.refl _))).2 hrun).levelEquiv
              (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
                (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
          · simp only [hpos.recursionAt_index, hbn] at hD'
            cases hD'
        | some D₃ =>
          -- The branch gives a position of the corecursor of the type of the result.
          obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
            (Term.blockName_mem hbn)
          obtain ⟨j₃, hj₃⟩ := List.mem_iff_getElem?.1 hT₃
          obtain ⟨ps₃, S₃, hS₃⟩ := hSs j₃ T₃ hj₃
          have hpr : sig.HasPrelude := hpre ⟨j₁, T₂, hpos.index, T₃.name, hj₁,
            by rw [hpos.recursionAt_index]; exact hbn⟩
          have hst : (Ss.subst σ).stateOf decl.names T₃.name =
              some ⟨ps₃, S₃.subst σ, Ss.sorts j₃⟩ := by
            rw [States.stateOf_subst, States.stateOf_of_get hnd hj₃ hS₃]
            rfl
          have hk : ks.getD i' .none =
              Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps₃.length) := by
            simp only [ks, hrt, Option.getD_some, List.map_map, List.getD_eq_getElem?_getD,
              List.getElem?_map, hi, Option.map_some, Function.comp_apply]
            rw [hrn, hbn]
            simp only [Option.bind_some, TypeDeclaration.idxOf?_codataTypes hnd hj₃, States.arity,
              hS₃]
            rfl
          rw [hk] at hget
          have hb := ValidEqTerm₀.corecBranch hpos
            (hgv.2 i' j₁ T₂ d ps₁ S₁ p q ps' Ξ Θ B ψ g g hi hS₁ hpos hg hg) hσ hts₁ hτ'
          simp only [Term.branchResult, hbn, hst] at hb hrun
          simp only [Term.observed, hbn, hst] at hred
          obtain ⟨v', H₄, hres, -, hnext | ⟨rfl, hdone⟩⟩ := RunsAs.resume hd hpr hs hb hrun
            Γ.length E Ps T₃.name qs ls ps (as.subst σ) (Ss.subst σ) (gs.subst σ)
          · -- A new state: a new closure of the branches.
            obtain ⟨ts₃, bs₃, hred', hτ₃, hbs₃, rfl, rfl⟩ := hnext
            refine ⟨_, _, tr, .beta hclo hget hlen₁ hlen₂ hπ₁ hπ₂ hev' hres, fun hr0 => ?_,
              fun D' R hD' hR _ => ?_⟩
            · simp only [hpos.recursionAt_index, hbn] at hr0
              cases hr0
            · simp only [hpos.recursionAt_index, hbn, Option.map_some, Option.some.injEq] at hD' hR
              subst hD' hR
              exact ⟨_, ⟨.step hred hred', .corec _ _ _ _ _ _ _ _ _⟩, .inr ⟨j₃, T₃, ps₃, S₃, ts₃,
                bs₃, hj₃, rfl, hS₃, hτ₃, (hH₁.trans (hH₂.trans (hH₂'.trans hH₃))).trans
                  (List.prefix_append _ _),
                hbs₃.mono hd (List.prefix_append _ _), by simp, rfl⟩⟩
          · -- A term already built, related at the instance of the type of the result.
            refine ⟨_, _, tr, .beta hclo hget hlen₁ hlen₂ hπ₁ hπ₂ hev' hres, fun hr0 => ?_,
              fun D' R hD' hR he => ?_⟩
            · simp only [hpos.recursionAt_index, hbn] at hr0
              cases hr0
            · simp only [hpos.recursionAt_index, hbn, Option.map_some, Option.some.injEq] at hD' hR
              subst hD' hR
              have h₁ := ((RunsAs.redStar_iff hd (.step hred (.refl _))).2 hdone).levelEquiv
                (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
                  (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
              rw [he] at h₁
              exact RunRel.computed_mono (fun _ _ h => .inl h)
                (RunFieldRel.of_runsAs hd (hFR T₃ hT₃) (hw _) (h₁.levelEquiv (hX T₃.name)))
    -- The corecursor is related to the closure.
    exact ⟨_, hw _, .inr ⟨_, .univ n (levelRel_run_iff.2 (.codata ⟨hdecl, hT', rfl⟩ hq hl hp rfl hs
      hnS S hS)), _, ⟨.refl _, .corec _ _ _ _ _ _ _ _ _⟩, X, hcons,
      .inr ⟨j, T', ps'', S', ts, bs, hj, rfl, hS', hts, List.prefix_refl _, hbs, ha, rfl⟩⟩⟩

-- ADE: none.
/-- `(corec)` at run time: a corecursor of a codata type of `Σ`, whose type declaration is
meaningful, from a state valid at run time with the grades `γ` when its grade `r` is used at run
time, with branches valid at run time with the grades `δs i`, which `δ` bounds, is valid at run time
at its instance with the grades `r · γ + δ`, in a signature whose names are distinct: its erasure
evaluates its state and allocates the closure of its branches, to which `RunsAs.corec` relates it. -/
theorem RunValid.corec (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {Γ : Scope} {hΓ : Γ.FirstOrder}
    {ctx : Context 0 Γ} {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude)
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {γ δ : GradeVector Γ.length}
    {δs : Nat → GradeVector Γ.length} {h' : Nat} {ps' : List Parameter} {S : Telescope 0 Γ ps'}
    {ss : Args 0 Γ ps'} (hh : decl.codataTypes[h']? = some T)
    (hS : Ss.get h' = some ⟨0, ps', S⟩) (hss : ValidArgsΓ sig ι ctx ss S)
    (hssr : r ∉ Mode.oneOne.erased → RunValidArgs sig ι P hΓ ctx γ ss S)
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hgv : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs)
    (hgr : RunValidCorecBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as r Ss gs δs)
    (hδ : ∀ i j T' d (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership ps₁.length), decl.codataCases[i]? = some (j, T', d) →
      (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ → δ ≤ᶜ p ·ᶜ δs i) :
    RunValid sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ δ) (.corec r D qs ls ps as ss.terms Ss gs)
      (.inst D qs ls ps as) := by
  intro ϖ₀ σ H E V hσ hEV hE
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS₀ := Mode.erasesUncounted .oneOne
  have hEδ : RunsAsSubst sig ι P H ctx δ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS₀.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  -- The erasure evaluates the state, each entry at its grade times `r`.
  have hst : (((sig.position T.name).bind Ss.get).elim [] fun ⟨_, ps, _⟩ => ps.map (r * ·.usage)) =
      (ps'.map (·.usage)).map (r * ·) := by
    rw [hd.position h hh, Option.bind_some, hS, List.map_map]
    rfl
  obtain ⟨bs, H', tr, hev, hH', hbs⟩ : ∃ bs H' tr, EvalAll P ϖ₀ H E
      (ss.terms.erase sig Mode.oneOne.erased hΓ ((ps'.map (·.usage)).map (r * ·))) bs H' tr ∧
      H.Extends H' ∧
      RunsAsArgs sig ι P H' (fun l => r * Parameter.grades ps' l) (ss.subst σ) bs (S.subst σ) := by
    by_cases hr : r ∈ Mode.oneOne.erased
    · -- Every entry is erased.
      have hrS := (by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased)
        r
      obtain ⟨bs, H', hev, hH', hl⟩ := Args.evalAll_erased (sig := sig) (P := P)
        Mode.oneOne.erased hΓ ϖ₀ E ss _ (fun u hu => by
          obtain ⟨u', -, rfl⟩ := List.mem_map.1 hu
          exact hrS u' hr) H
      exact ⟨bs, H', [], hev, hH', RunsAsArgs.of_erased (ss.subst σ) bs (S.subst σ)
        (fun _ _ _ => hrS _ hr) hl⟩
    · -- The state is valid at run time with the grades `γ`.
      have hEγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h ((by decide : ∀ r u : Grade, r ∉ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased →
          u ∈ Mode.oneOne.erased) r _ hr (hS₀.add _ _ h'))) hE
      obtain ⟨bs, H', tr, hev, hH', hrs⟩ := hssr hr (ϖ₀ * r.run) σ H E V hσ hEV hEγ
      refine ⟨bs, H', tr, ?_, hH', RunsAsArgs.of_counted (fun l h' => (by decide : ∀ r u : Grade,
        r * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) r _ h') hrs⟩
      exact Terms.evalAll_erase_mul_of_not_erased hΓ hr _ _ hev
  -- Then it allocates the closure of its branches, to which the corecursor is related.
  refine ⟨H'.length, H' ++ [.corec Γ.length E (gs.erase sig Mode.oneOne.erased hΓ
    ((sig.destructorGrades T.name qs ps).getD []) (((sig.resumedTypes T.name qs ps).getD []).map
      fun h => Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (h.bind Ss.arity))
    (((sig.destructorArguments T.name qs ps).getD []).map fun ⟨j, as⟩ =>
      ((Ss.get j).elim [] fun ⟨_, ps, _⟩ => ps.map (r * ·.usage), as)))
    (ps'.map fun p => (r * p.usage).run) bs], tr, ?_,
    hH'.trans (List.prefix_append _ _), ?_⟩
  · rw [Term.erase, hst]
    have hm : (ss.terms.erase sig Mode.oneOne.erased hΓ
        ((ps'.map (·.usage)).map (r * ·))).multiplicities = ps'.map fun p => (r * p.usage).run := by
      rw [List.map_map]
      exact Args.multiplicities_erase_map sig Mode.oneOne.erased hΓ (r * ·) ss
    rw [← hm]
    exact .corec hev
  · rw [Term.corec_subst]
    exact RunsAs.corec hd h hv hq hl hp hadm has hpre hSs hgv hgr hδ hσ
      ((hEV.mono hH').mono (List.prefix_append _ _))
      ((hEδ.mono hd hH').mono hd (List.prefix_append _ _)) hh hS (hss.2 σ σ hσ)
      (hbs.mono hd (List.prefix_append _ _)) (by simp)

end

end Sic.Core
