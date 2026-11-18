module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.Soundness.Substitution

/-!
# Run Time of the Observations

The relation of run time of the destructors of a codata type holds of observations and of the
address of a value when the observations are equal at equal arguments, destructor by destructor,
and when the observation of the value by each destructor whose grade is used at run time, at
arguments related to addresses, evaluates to an address to which the observation is related at the
result of the destructor.
This is what a corecursor and the recursive result of a nested field both need, apart from what
their values are, so that neither module of them imports the other.

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
    have ihm : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
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
equality. -/
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
        ∀ ϖ', ∃ w H'' tr, EvalObs P ϖ' H' a i (ψ.map Grade.run) ς.run (ps.map (·.usage.run))
          (ps.map (·.requirement.run)) bs w H'' tr ∧
          RunsAs sig ι P H'' ((o d ps).subst ts.toSubst) w
            ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst))) →
      S H o a
  | _, _, .nil, _, _, _, _, _, h, _, _, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q ς Θ B ψ ds, rs, hN, D, θ, _, h, H, o, a, hv, hr => by
    have ihm : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
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
      obtain ⟨w, H'', tr, hev, hw⟩ := hr d p q ς ps _ Θ B ψ .here i SΘ RΘ hp hi hΘ hRΘ H' hH' ts bs
        hts ϖ'
      obtain ⟨v, hv'⟩ := hB ts htt
      exact ⟨w, H'', tr, hev, RunFieldRel.of_runsAs hd (hR ts htt v hv') hv' hw⟩

end Sic.Core
