module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Levels
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Corecursors
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Run Time of the Observations

The relation of run time of the destructors of a codata type holds of observations and of the
address of a value when the observations are equal at equal arguments, destructor by destructor,
and when the observation of the value by each destructor whose grade is used at run time, at
arguments related to addresses, evaluates to an address to which the observation is related at the
result of the destructor.
This is what a corecursor and the recursive result of a nested field both need, apart from what
their values are, so that neither module of them imports the other.

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

ADE have no codata types.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- Observations whose results are equal, destructor by destructor, at equal arguments, and whose
observations by each destructor whose grade is used at run time, at arguments related to addresses
in a heap that extends `H`, evaluate to addresses to which they are related, are related to the
address `a` by the relation of run time of the destructors, at instantiated levels: as terms of the
result of each destructor that is not recursive, and by the relation `R` that `rsR` gives each
recursive one, whose result is the instance of the block; the converse of `Destructors.Pos.run`. -/
theorem RunDesRel.of_obs (hd : sig.Distinct) {κ : Universe 0} {k' : Nat} (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {inst : Name → Term 0 Γ} →
      {rs : Nat → Option Name} → {nested : Nat → Bool} → {θ θ' : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs nested (ds.substLevels L) θ θ' →
      {rsR : Nat → Option RunRel} → (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R, rsR i = some R) → {D : Name} → {S : RunObsRel} →
      RunDesRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) D rsR
        (ds.substLevels L) θ S →
      {H : Heap} → {o : Observations} → {a : Nat} →
      (∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o θ)))
          ts.toSubst us.toSubst → rs hpos.index = none →
        ValidEqTerm₀ sig ι ((o d ps).subst ts.toSubst) ((o d ps).subst us.toSubst)
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) →
      (∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (i : Nat), p ∉ Mode.oneOne.erased →
        sig.destructorCase D d = some i → ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps)
        (bs : List Nat),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o θ)))
          ts.toSubst ts.toSubst →
        RunsAsArgs sig ι P H' (Parameter.grades ps) ts bs
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) →
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ψ.map Grade.run) ς.run (ps.map (·.usage.run))
          (ps.map (·.requirement.run)) bs w H'' tr ∧
          (rs hpos.index = none → RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
            ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) ∧
          ∀ D' R, rs hpos.index = some D' → rsR hpos.index = some R →
            (B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst) =
              (inst D').subst θ →
            R H'' ((o d ps).subst ts.toSubst) w) →
      S H o a
  | _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q ς Θ B ψ ds, inst, rs, _, θ, θ', hm, rsR, hN, hS, D, S, h, H, o,
      a, hv, hr => by
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) κ.level.closedValue
    rw [Destructors.substLevels] at hm
    replace hm := hm.cons_inv
    obtain ⟨hΘm, hm⟩ := hm
    have hsw : ∀ (f : Term 0 (Scope.extend [] ps.length)) D',
        ((inst D').rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ f) =
          (inst D').subst θ := fun f D' => Term.subst_rename_of (fun _ => rfl) _
    have hv' := fun d' p' q' ς' ps' Ξ' Θ' B' ψ' (hpos : ds.Pos d' p' q' ς' Ξ' Θ' B' ψ') =>
      hv d' p' q' ς' ps' Ξ' Θ' B' ψ' (.there hpos)
    have hrec : ∀ (d' : Name) (p' q' ς' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope k' Ξ' ps') (B' : Term k' (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership Grade ps'.length) (hpos : ds.Pos d' p' q' ς' Ξ' Θ' B' ψ') (i : Nat),
        p' ∉ Mode.oneOne.erased → sig.destructorCase D d' = some i → ∀ H', H.Extends H' →
        ∀ (ts : Args 0 [] ps') (bs : List Nat),
        EqSubst sig ι (Context.empty.append ((Θ'.substLevels L).subst
          (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))))) ts.toSubst
          ts.toSubst →
        RunsAsArgs sig ι P H' (Parameter.grades ps') ts bs ((Θ'.substLevels L).subst
          (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps)))) →
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ψ'.map Grade.run) ς'.run (ps'.map (·.usage.run))
          (ps'.map (·.requirement.run)) bs w H'' tr ∧
          (rs (hpos.index + 1) = none → RunsAs sig ι P H'' ((o d' ps').subst ts.toSubst) w
            ((B'.substLevels L).subst (Subst.append
              (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))) ts.toSubst))) ∧
          ∀ D' R, rs (hpos.index + 1) = some D' → rsR (hpos.index + 1) = some R →
            (B'.substLevels L).subst (Subst.append
              (hpos.obsSubst o (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps))) ts.toSubst) =
              ((inst D').rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ (o d ps)) →
            R H'' ((o d' ps').subst ts.toSubst) w :=
      fun d' p' q' ς' ps' Ξ' Θ' B' ψ' hpos i hp hi H' hH' ts bs hτ hbs ϖ' => by
        obtain ⟨w, H'', tr, hev, h₁, h₂⟩ :=
          hr d' p' q' ς' ps' Ξ' Θ' B' ψ' (.there hpos) i hp hi H' hH' ts bs hτ hbs ϖ'
        exact ⟨w, H'', tr, hev, h₁, fun D' R hD' hR e => h₂ D' R hD' hR (e.trans (hsw _ D'))⟩
    have hgr : ∀ l (p' : Parameter), ps[l]? = some p' → Parameter.grades ps l ∉ Mode.oneOne.erased →
        p'.usage ∉ Mode.oneOne.erased := fun _ _ hl h => Parameter.grades_of_getElem? hl ▸ h
    split at hm
    · rename_i hr0
      obtain ⟨-, hds⟩ := hm
      cases h with
      | recursive _ hrs => rw [hN 0 hr0] at hrs; cases hrs
      | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ RΘ i hi hΘ hRΘ F R hB hF hR G hG _ =>
        have hSp := TelRel.isPer hd ihm (fun _ => .plain) hΘ
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
          (fun _ => .plain)
        have hA : AbstractionRel SΘ F (o d ps) (o d ps) := fun ts us hts => by
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv''⟩ := hB ts htt
          exact (hF ts htt v hv'').of_validEqTerm hv'' (hv d p q ς ps _ Θ B ψ .here ts us
            ((hT ts us).1 hts) hr0)
        have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst θ))
            τ₁ τ₂ → ValidEqTerm₀ sig ι ((o d ps).subst τ₁) ((o d ps).subst τ₂)
              ((B.substLevels L).subst (Subst.append θ τ₁)) := fun τ₁ τ₂ hτ => by
          obtain ⟨ts, rfl⟩ := Subst.exists_args ps @τ₁
          obtain ⟨us, rfl⟩ := Subst.exists_args ps @τ₂
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
          (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
          (fun _ => .plain) _ hgr ts hτ bs hts
        obtain ⟨w, H'', tr, hev, hw, -⟩ :=
          hr d p q ς ps _ Θ B ψ .here i hp hi H' hH' ts bs hτ hbs ϖ'
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
          (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
          (fun _ => .plain)
        refine ⟨fun hp H' hH' ts bs hts ϖ' => ?_, RunDesRel.of_obs hd L ds (hds (o d ps) (o d ps))
          (fun i => hN (i + 1)) (fun i => hS (i + 1)) (hG _) hv' hrec⟩
        have htt := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ₁ (fun _ => rfl) H'
          ts.terms bs hts
        have hτ := (hT ts ts).1 htt
        have hbs := RunsAsArgs.of_runTelRel hRΘ
          (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
          (fun _ => .plain) _ hgr ts hτ bs hts
        obtain ⟨w, H'', tr, hev, -, hw⟩ :=
          hr d p q ς ps _ Θ B ψ .here _ hp hi H' hH' ts bs hτ hbs ϖ'
        have e : (B.substLevels L).subst (Subst.append θ ts.toSubst) = (inst D').subst θ := by
          rw [hBD, Term.subst_append_rename_weakenN]
        exact ⟨w, H'', tr, hev, hw D' R hr0 hR0 e⟩

/-- Observations whose results are equal, destructor by destructor, at equal arguments, and whose
observations by each destructor whose grade is used at run time, at arguments related to addresses
in a heap that extends `H`, evaluate to addresses to which they are related, are related to the
address `a` by the relation of run time of the destructors, none of which is recursive, at
instantiated levels: the telescopes and the results that the clauses of the relation carry replace
the meaning of the destructors that `RunDesRel.of_obs` reads, as `DesRel.of_positions` does for the
equality, and the observation by each destructor may read the equality and the relation of run
time of its result, which the clause of the destructor gives. -/
theorem RunDesRel.of_positions (hd : sig.Distinct) {n : Nat} {k' : Nat} (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {rs : Nat → Option RunRel} →
      (∀ i, rs i = none) → {D : Name} → {θ : Subst 0 [] Γ} → {S : RunObsRel} →
      RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs (ds.substLevels L) θ S →
      {H : Heap} → {o : Observations} → {a : Nat} →
      (∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (SΘ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) SΘ →
        ∀ (ts us : Args 0 [] ps), SΘ ts.terms us.terms → ∀ (v : Term 0 []) (F : TermRel),
        Computesι sig ι
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst)) v →
        FieldRel sig ι n (fun m _ => levelRel sig ι m) .type v F →
        F ((o d ps).subst ts.toSubst) ((o d ps).subst us.toSubst)) →
      (∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (i : Nat) (SΘ : FieldsRel) (RΘ : RunFieldsRel),
        p ∉ Mode.oneOne.erased → sig.destructorCase D d = some i →
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) SΘ →
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain)
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) RΘ →
        ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps) (bs : List Nat), RΘ H' ts.terms bs →
        (∃ v F R, Computesι sig ι
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst)) v ∧
          FieldRel sig ι n (fun m _ => levelRel sig ι m) .type v F ∧
          RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R) →
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ψ.map Grade.run) ς.run (ps.map (·.usage.run))
          (ps.map (·.requirement.run)) bs w H'' tr ∧
          RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
            ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) →
      S H o a
  | _, _, .nil, _, _, _, _, _, h, _, _, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q ς Θ B ψ ds, rs, hN, D, θ, _, h, H, o, a, hv, hr => by
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    cases h with
    | recursive _ hrs => rw [hN 0] at hrs; cases hrs
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ RΘ i hi hΘ hRΘ F R hB hF hR G hG _ =>
      have hSp := TelRel.isPer hd ihm (fun _ => .plain) hΘ
      have hA : AbstractionRel SΘ F (o d ps) (o d ps) := fun ts us hts => by
        have htt := hSp.trans hts (hSp.symm hts)
        obtain ⟨v, hv'⟩ := hB ts htt
        exact hv d p q ς ps _ Θ B ψ .here SΘ hΘ ts us hts v _ hv' (hF ts htt v hv')
      refine ⟨hA, fun hp H' hH' ts bs hts ϖ' => ?_,
        RunDesRel.of_positions hd L ds (fun i => hN (i + 1)) (hG _ hA)
          (fun d' p' q' ς' ps' Ξ' Θ' B' ψ' hpos => hv d' p' q' ς' ps' Ξ' Θ' B' ψ' (.there hpos))
          (fun d' p' q' ς' ps' Ξ' Θ' B' ψ' hpos => hr d' p' q' ς' ps' Ξ' Θ' B' ψ' (.there hpos))⟩
      have htt := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H'
        ts.terms bs hts
      obtain ⟨v, hv'⟩ := hB ts htt
      obtain ⟨w, H'', tr, hev, hw⟩ := hr d p q ς ps _ Θ B ψ .here i SΘ RΘ hp hi hΘ hRΘ H' hH' ts bs
        hts ⟨v, _, _, hv', hF ts htt v hv', hR ts htt v hv'⟩ ϖ'
      exact ⟨w, H'', tr, hev, RunFieldRel.of_runsAs hd (hR ts htt v hv') hv' hw⟩

/-! ## Observations -/

/-- The destructor at a position of destructors of run time, whose grade is used at run time,
observes a value whose observations are related at run time: at arguments related to addresses by
the relation of run time of its telescope, in a heap that extends that of the value, the
observation evaluates to an address to which the observation of the term is related at the result
of the destructor; the relations of the recursive destructors relate only terms related at their
instances. -/
theorem Destructors.Pos.run (hd : sig.Distinct) {κ : Universe 0} {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {nested : Nat → Bool} → {θ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs nested ds θ θ → {rsR : Nat → Option RunRel} →
      (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R, rsR i = some R ∧
        ∀ H t a, R H t a → RunsAs sig ι P H t a ((inst D).subst θ)) →
      {D : Name} → {S : RunObsRel} →
      RunDesRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) D rsR ds θ S →
      {H : Heap} → {o : Observations} → {a : Nat} → S H o a → p ∉ Mode.oneOne.erased →
      ∃ i RΘ, sig.destructorCase D d = some i ∧
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => .plain)
          (Θ.subst (hpos.obsSubst o θ)) RΘ ∧
        ∀ H', H.Extends H' → ∀ (ts : Args 0 [] ps) (bs : List Nat), RΘ H' ts.terms bs →
          ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ψ.map Grade.run) ς.run (ps.map (·.usage.run))
            (ps.map (·.requirement.run)) bs w H'' tr ∧
            RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
              (B.subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))
  | _, _, _, _, _, _, _, .here, _, _, _, _, hv, _, hN, hR, _, _, hS, _, _, _, ho, hp => by
    replace hv := hv.cons_inv
    obtain ⟨-, hv⟩ := hv
    split at hv
    · rename_i hr
      cases hS with
      | recursive _ hrs => rw [hN 0 hr] at hrs; cases hrs
      | cons hi hΘ hRΘ _ _ hB _ hRv _ _ _ =>
        obtain ⟨-, hrun, -⟩ := ho
        refine ⟨_, _, hi, hRΘ, fun H' hH' ts bs hts ϖ' => ?_⟩
        obtain ⟨w, H'', tr, hev, hw⟩ := hrun hp H' hH' ts bs hts ϖ'
        have htt := RunTelRel.fieldsRel hd (Nat.forall_lt (levelRel_isPer hd) _) hRΘ (fun _ => rfl)
          _ _ hΘ (fun _ => rfl) H' ts.terms bs hts
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
  | _, _, _, _, _, _, _, .there (ps' := ps') (ψ' := ψ') h, inst, rs, _, θ, hv, rsR, hN, hR, _, _,
      hS, _, o, _, ho, hp => by
    replace hv := hv.cons_inv
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
        have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) (fun _ => .plain) hΘ
        refine h.run hd (hds _ _ fun τ₁ τ₂ hτ => ?_) hN' (hR' _) (hG _ hA) hGo hp
        obtain ⟨ts, rfl⟩ := Subst.exists_args ps' @τ₁
        obtain ⟨us, rfl⟩ := Subst.exists_args ps' @τ₂
        have hts := (TelRel.eqSubst_iff hd hΘ
          (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
          (fun _ => .plain)
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
theorem Destructors.Pos.validEq {κ : Universe 0} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {nested : Nat → Bool} → {θ₁ θ₂ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs nested ds θ₁ θ₂ →
      (∀ i D, rs i = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι ((inst D).subst θ₁) ((inst D).subst θ₂) (.sort κ₁)) →
      {f₁ f₂ : Observations} →
      (∀ (d' : Name) (p' q' ς' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope 0 Ξ' ps') (B' : Term 0 (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership Grade ps'.length) (hpos' : ds.Pos d' p' q' ς' Ξ' Θ' B' ψ')
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
  | _, _, _, _, _, _, _, .here, _, _, _, _, _, hv, hI, _, _, _ => by
    replace hv := hv.cons_inv
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
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (ψ' := ψ') h, inst, rs, _, θ₁, θ₂, hv, hI,
      f₁, f₂, hobs => by
    replace hv := hv.cons_inv
    obtain ⟨-, hv⟩ := hv
    have hI' : ∀ i D, rs (i + 1) = some D → ∃ κ₁, ValidEqTerm₀ sig ι
        (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ (f₁ d' ps')))
        (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₂ (f₂ d' ps')))
        (.sort κ₁) := fun i D hi => by
      rw [Term.subst_rename_of (fun _ => rfl), Term.subst_rename_of (fun _ => rfl)]
      exact hI (i + 1) D hi
    have hobs' := fun d'' p' q' ς' ps'' Ξ' Θ' B' ψ' (hpos' : Destructors.Pos d'' p' q' ς' _ Ξ' Θ' B' ψ')
      => hobs d'' p' q' ς' ps'' Ξ' Θ' B' ψ' (.there hpos')
    split at hv
    · obtain ⟨-, hds⟩ := hv
      refine h.validEq (hds _ _ fun τ₁ τ₂ hτ => ?_) hI' hobs'
      obtain ⟨ts, rfl⟩ := Subst.exists_args ps' @τ₁
      obtain ⟨us, rfl⟩ := Subst.exists_args ps' @τ₂
      exact hobs _ _ _ _ _ _ _ _ _ .here ts us hτ
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
    {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership Grade ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) (hpr : p ∉ Mode.oneOne.erased)
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
      EvalObs P ϖ₀ H' a i (ψ.map Grade.run) ς.run (ps'.map (·.usage.run))
        (ps'.map (·.requirement.run)) bs w H'' tr ∧ H'.Extends H'' ∧
      RunsAs sig ι P H'' (.obs D qs ls ps as t d ts.terms) w
        ((B.substLevels (ls.getFin hl)).subst
          (Subst.append (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst)) := by
  obtain ⟨hdecl, hT, hD⟩ := id h
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hDs := hv.destructorsAtClosedLevels hq hl hp hadm has
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst as.toSubst
  have hXeq : ∀ D' ∈ decl.names, ∃ κ₁, ValidEqTerm₀ sig ι (X D') (X D') (.sort κ₁) :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT hD'
      exact ⟨_, ValidEqTerm₀.blockInstance_atLevels hq hl hp
        (ValidEqTerm₀.instCodata hd ⟨hdecl, hT', rfl⟩ hv hq hl hp hadm has)⟩
  have hI : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    (Whnf.inst ..).computes
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
  have e : ((decl.sort I).atLevels ρ).level.closedValue = n :=
    (decl.sort_atLevels_closedValue hq hl hp).trans hnS
  have hSρ : RunDesRel sig ι P ((decl.sort I).atLevels ρ).level.closedValue
      (fun m _ => levelRel sig ι m) T.name
      (fun i => ((T.body I).recursionAt decl.names i).map fun D' => (Y D').computed sig ι)
      ((T.body I).atLevels ρ) as.toSubst (S Y T) := by
    rw [e]
    exact RunDesRel.atLevels_of_substLevels hd (hS Y T hT)
  -- The observation by the destructor, at arguments related by the relation of its telescope.
  obtain ⟨i, RΘ, hi, hRΘ, hobsR⟩ := (hpos.substLevels Lρ).run hd (hDs T hT)
    (fun i hi => by rw [hi]; rfl) (fun i D' hi => ⟨_, by rw [hi]; rfl, fun H₀ t₀ b htb => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
        (Destructors.recursionAt_mem hi)
      obtain ⟨w, hw, hYw⟩ := htb
      have hU : RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
          (CodataType.runBlockRel decl.codataTypes S T'.name) :=
        .codata ⟨hdecl, hT', rfl⟩ hq hl hp rfl hs hnS S hS
      exact RunsAs.levelEquiv hd (decl.blockInstance_atLevels_subst hq hl hp as _).symm
        ⟨_, (Whnf.inst ..).computes, .inr ⟨_, .univ n (levelRel_run_iff.2 hU), w, hw, Y, hY,
          hYw⟩⟩⟩) hSρ hSo hpr
  -- The equality of the term relates its observations to those of the corecursor.
  obtain ⟨v₂, -, Req, hcv₂, -, hReq, -⟩ := htv.1.2
  cases Computesι.det hd hcv₂ hI
  obtain ⟨-, Se, hSe, rfl⟩ := (HasEq.instCodata_inv hd h hq hl hp hReq).resolve_right
    fun ⟨hs', _⟩ => nomatch hs.symm.trans hs'
  have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
      (.inst D qs ls ps as) (CodataType.blockRel decl.codataTypes Se D) :=
    levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl Se hSe)
  have hnp := Computesι.not_computesToProp hd hI hU₀
  obtain ⟨v₀, w₁, w₂, R', hv₀, hw₁, hw₂, hR', hrel⟩ := htv.2.1 hnp
  cases Computesι.det hd hI hv₀
  have hmono := DesRel.blockMono hd hSe
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
    have hq' : ((decl.sort I).atLevels ρ).quality = .type := hs
    rw [decl.sort_atLevels_closedValue hq hl hp, hq']
    exact DesRel.atLevels_of_substLevels hd (hSe _ T hT)
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
    have hq' : ((decl.sort I).atLevels ρ).quality = .type := hs
    rw [hi, decl.sort_atLevels_closedValue hq hl hp, hq']
    exact ⟨_, _, rfl, (Whnf.inst ..).computes,
      FieldRel.blockInstance_atLevels hd hq hl hp (.univ rfl hU)⟩
  -- The telescope and the result of the destructor at both observations are equal.
  obtain ⟨htel, hBeq⟩ := (hpos.substLevels Lρ).validEq (hDs T hT)
    (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi))
    (fun _ _ _ _ _ _ _ _ _ hpos' => (hpos'.sound hd (hDs T hT)
      (fun i hi => by rw [hi]; rfl) hRr
      (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi)) hDes ho hf₁ hf₂).2)
  have hres := ((hpos.substLevels Lρ).sound hd (hDs T hT)
    (fun i hi => by rw [hi]; rfl) hRr
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
  have htsρ := (EqSubst.substLevels_iff_atLevels L Θ hcE.symm).1 hts
  have hbsρ := RunsAsArgs.levelEquiv hd (Θ.closedValues_levelEquiv L hcE.symm) hbs
  obtain ⟨S', h₁, h₂⟩ := htel.runTelRel hd P rfl
  have hS' := RunTelRel.of_runsAsArgs hd h₁
    (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain) _
    (fun _ _ hl hp => (Parameter.grades_of_getElem? hl).symm ▸ hp) ts htsρ bs hbsρ
  have hRΘts : RΘ H' ts.terms bs := (RunTelRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _)
    (Nat.forall_lt (levelRel_run_unique hd) _) h₂ _ _ hRΘ
    (fun _ => .plain) H' ts.terms bs).1 hS'
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
  exact hw₂.levelEquiv hd
    (B.closedValues_levelEquiv L (Subst.LevelEquiv.append hcE.symm (Subst.LevelEquiv.refl _))).symm

-- ADE: none.
/-- `(d)` at run time: an observation of a term of an instance of a codata type of `Σ`, whose type
declaration is meaningful, valid at run time with the grades `γ`, by a destructor whose grade is
used at run time, at arguments valid at run time with the grades `δ`, is valid at run time at its
result with the grades `γ + δ`, in a signature whose names are distinct: its erasure evaluates its
term, then its arguments, then observes the closure, in every environment that binds the scope
through a renaming. -/
theorem RunValidRen.obs (hd : sig.Distinct) {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ}
    {γ δ : GradeVector Γ.length} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership Grade ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) (hpr : p ∉ Mode.oneOne.erased)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → p.mode ≠ .oneOne)
    {t : Term 0 Γ} (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : RunValidRen sig ι P hΓ ctx γ t (.inst D qs ls ps as)) {bs : Args 0 Γ ps'}
    (hbs : ValidArgsΓ sig ι ctx bs ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))
    (hbr : RunValidArgsRen sig ι P hΓ ctx δ bs ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
    RunValidRen sig ι P hΓ ctx (γ +ᶜ δ) (.obs D qs ls ps as t d bs.terms)
      (((B.substLevels (ls.getFin hl)).subst
        (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))).instantiate
          bs) := by
  intro ϖ₀ σ H E V hσ hEV hE _ g E' hg
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
  obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr ϖ₀ σ H E V hσ hEV hEγ g E' hg
  obtain ⟨bs', H₂, tr₂, hevs, hH₂, hruns⟩ :=
    hbr ϖ₀ σ H₁ E V hσ (hEV.mono hH₁) (hEδ.mono hd hH₁ ctx) g E' hg
  rw [hΘ] at hruns
  have hbsσ := hbs.2 σ σ hσ
  rw [hΘ] at hbsσ
  obtain ⟨i, w, H₃, tr₃, hi, hevo, hH₃, hrun⟩ := RunsAs.obs hd h hv hq hl hp hadm (has.2 σ σ hσ) hpos
    hpr hprop (ht.2 σ σ hσ) hta hH₂ ϖ₀ hbsσ hruns
  have he : (Term.obs D qs ls ps as t d bs.terms).erase sig Mode.oneOne.erased hΓ =
      .obs (t.erase sig Mode.oneOne.erased hΓ) i (ψ.map Grade.run) ς.run
        (bs.terms.erase sig Mode.oneOne.erased hΓ ps') := by
    rw [Term.erase, hi, hd.argumentParams h hq hp hpos]
    rfl
  refine ⟨w, H₃, tr₁ ++ (tr₂ ++ tr₃), by
    rw [he]
    exact .obs hev hevs (by
      rw [Targets.multiplicities_rename, Targets.requirements_rename, Args.multiplicities_erase,
        Args.requirements_erase]
      exact hevo),
    hH₁.trans (hH₂.trans hH₃), ?_⟩
  rw [hA]
  simp only [Term.subst, ← Args.terms_subst]
  exact hrun

end Sic.Core
