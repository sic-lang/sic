module

public import Sic.Core.Nesting.Relation
public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.Soundness.Levels
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Levels of the Relation of Run Time

The relation of run time of annex 22 of RFC 36 reads the levels of its type by their values, as the
meaning does: two types that differ only by levels of the same values compute to canonical types
that differ in the same way, which the graph of run time does not tell apart, so that a term related
to an address at one is related to it at the other, and so are the arguments of two telescopes that
differ in the same way.
It reads the levels of its terms by their values too: a term whose levels change for equal ones is
related to the same addresses, by mutual recursion on the graph of run time, level by level, as its
monotonicity in the heap is proved, since the canonical term that it computes changes in the same
way, and the relations of its type read its levels only through the equality of the terms of its
fields and of its observations, which the meaning proves to read them by their values.

ADE have levels as terms, and no counterpart is needed there.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- A term related to an address at a type is related to it at every type equal to it up to its
levels, in a signature whose names are distinct. -/
theorem RunsAs.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t : Term 0 []} {a : Nat} {A A' : Term 0 []} (hd : sig.Distinct)
    (hAA : Term.LevelEquiv A A') : RunsAs sig ι P H t a A → RunsAs sig ι P H t a A'
  | ⟨_, hA, h⟩ => by
    obtain ⟨v', hA', hv⟩ := Computes.levelEquiv hd.interpret hA hAA
    rcases h with hp | ⟨R, hR, ht⟩
    · exact ⟨v', hA', .inl (hp.levelEquiv hd hv)⟩
    · exact ⟨v', hA', .inr ⟨R, hR.levelEquiv hd hv, ht⟩⟩

/-- Arguments related to addresses at a telescope are related to them at every telescope equal to
it up to its levels, in a signature whose names are distinct. -/
theorem RunsAsArgs.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    (hd : sig.Distinct) : {ps : List Parameter} → {g : Nat → Grade} → {ts : Args 0 [] ps} → {bs : List Nat} →
    {Θ Θ' : Telescope 0 [] ps} → Telescope.LevelEquiv Θ Θ' → RunsAsArgs sig ι P H g ts bs Θ →
      RunsAsArgs sig ι P H g ts bs Θ'
  | [], _, .nil, [], .nil, .nil, .nil, h => h
  | _ :: _, _, .cons _ _, _ :: _, .cons _ _ _ _, .cons _ _ _ _, .cons _ _ hA hΘ, h => by
    obtain ⟨ht, hts⟩ := h
    exact ⟨fun hp => (ht hp).levelEquiv hd hA,
      RunsAsArgs.levelEquiv hd (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl _))) hts⟩

/-! ## Terms Equal up to the Values of Their Levels

The relation of run time of a type relates a term whose levels change for equal ones to the same
addresses: the relations of the data types by induction on their least fixed points, which relate
the terms that a related term equals up to its levels, and those of the codata types by the
consistency of the relations of the terms that a related term equals up to its levels; the rest of a
telescope, and the destructors after a destructor, given for the term of the first field or for the
observation by the first destructor, have relations of run time at the term whose levels change,
which those at the term itself are, by the relation of run time of the types up to their levels. -/

/-- A relation of run time relates a term whose levels change for equal ones to the same
addresses. -/
abbrev RunRel.LevelInvariant (R : RunRel) : Prop :=
  ∀ {H : Heap} {t t' : Term 0 []} {a : Nat}, R H t a → Term.LevelEquiv t t' → R H t' a

/-- The relations of run time of the types of a level relate a term whose levels change for equal
ones to the same addresses. -/
abbrev RunLevelRel.LevelInvariant (L : RunLevelRel) : Prop :=
  ∀ {v : Term 0 []} {R : RunRel}, L v R → R.LevelInvariant

/-- `®⇓(R₂)` relates a term whose levels change for equal ones to an address that `®⇓(R₁)` relates
the term to, when `R₂` relates so the canonical terms that `R₁` relates, in a signature whose names
are distinct. -/
theorem RunRel.computed_levelEquiv {sig : Signature} {ι : Interpretation} {R₁ R₂ : RunRel}
    {H : Heap} (hd : sig.Distinct) (h : ∀ v v' a, R₁ H v a → Term.LevelEquiv v v' → R₂ H v' a)
    {t t' : Term 0 []} {a : Nat} :
    R₁.computed sig ι H t a → Term.LevelEquiv t t' → R₂.computed sig ι H t' a :=
  fun ⟨_, hc, hv⟩ ht =>
    have ⟨v', hc', hvv⟩ := Computes.levelEquiv hd.interpret hc ht
    ⟨v', hc', h _ _ a hv hvv⟩

/-- The relation of run time of the terms of the fields of a telescope `x : A, Θ` relates terms
whose levels change for equal ones to the addresses that another relates the terms to, when the
relations of `A` do so, and those of `Θ[a / x]` do so for each term `a` that the first relates. -/
theorem RunFieldsRel.cons_levelEquiv {F F' : RunRel} {G G' : Term 0 [] → RunFieldsRel} {H : Heap}
    (hF : ∀ t t' a, F H t a → Term.LevelEquiv t t' → F' H t' a)
    (hG : ∀ t t' a, F H t a → Term.LevelEquiv t t' → ∀ ts ts' as, G t H ts as →
      Terms.LevelEquiv ts ts' → G' t' H ts' as) :
    ∀ ts ts' as, RunFieldsRel.cons F G H ts as → Terms.LevelEquiv ts ts' →
      RunFieldsRel.cons F' G' H ts' as
  | .cons t ts, .cons t' ts', a :: as, ⟨h₁, h₂⟩, .cons ht hts =>
    ⟨hF t t' a h₁ ht, hG t t' a h₁ ht ts ts' as h₂ hts⟩

/-- `(®_x̄)` relates the value at an address to an abstraction whose levels change for equal ones,
when the relations of the result types relate the terms whose levels change for equal ones. -/
theorem RunAbstractionRel.levelEquiv {P : Program} {ps : List Parameter} {i : Nat}
    {ψ : ResultOwnership Grade ps.length} {ς : Grade} {SΘ : RunFieldsRel}
    {F : Terms 0 [] → RunRel}
    (hF : ∀ H (ts : Args 0 [] ps) bs, SΘ H ts.terms bs → (F ts.terms).LevelInvariant)
    {f f' : Term 0 (Scope.extend [] ps.length)} {H : Heap} {a : Nat}
    (h : RunAbstractionRel P i ψ ς SΘ F f H a) (hf : Term.LevelEquiv f f') :
    RunAbstractionRel P i ψ ς SΘ F f' H a :=
  fun H₁ hH ts bs hts ϖ =>
    have ⟨w, H₂, R, he, hr⟩ := h H₁ hH ts bs hts ϖ
    ⟨w, H₂, R, he, hF H₁ ts bs hts hr (hf.subst (Subst.LevelEquiv.refl _))⟩

mutual

/-- The relation of run time of a type of `U_n` relates a term whose levels change for equal ones to
the same addresses, if those of the levels below `n` do, in a signature whose names are
distinct. -/
theorem RunUnivRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P))
    {v : Term 0 []} {R : RunRel} :
    RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R → R.LevelInvariant
  | .univ _ _ => fun _ _ => trivial
  | .prop _ _ => fun _ _ => trivial
  | .data (decl := decl) _ _ _ _ _ _ _ S hS => fun h ht => by
    have hstep : ∀ X Y : Name → RunRel,
        (∀ D H w w' a, X D H w a → Term.LevelEquiv w w' → Y D H w' a) →
        ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts ts' as, S X c H ts as →
          Terms.LevelEquiv ts ts' → S Y c H ts' as :=
      fun X Y hXY T hT c hc H => RunTelRel.rel_levelEquiv hd ih (hS X T hT c hc) _ _
        (hS Y T hT c hc)
        (fun _ => Nest.map_rel₃
          (r := fun (x y _ : RunNestLeaf) => ∀ H t t' a, x.2 H t a → Term.LevelEquiv t t' →
            y.2 H t' a)
          (fun D' H _ _ _ => RunRel.computed_levelEquiv hd (hXY D' H)) _) H
    have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
        ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
      fun X Y hXY => RunTelRel.block_mono hd (Nat.forall_lt (levelRel_run_mono hd) _)
        (Θ := fun c => ⟨_, c.fieldsAt _ _ _⟩)
        (F := fun X D => (.inst D _ _ _ _, (X D).computed sig ι)) hS X Y
        fun D H _ _ => RunRel.computed_mono (hXY D H)
    exact h (fun D H w a => ∀ w', Term.LevelEquiv w w' →
        DataType.runBlockRel sig _ decl.dataTypes S D H w' a)
      (fun T hT H w a ⟨c, hc, i, ts, as, hw, hi, ha, hs⟩ w' hww => by
        obtain ⟨_, _, _, _, _, rfl⟩ := hw
        cases hww with
        | ctor _ _ _ _ _ _ hts =>
          exact DataType.runBlockRel_fold hmono hT ⟨c, hc, i, _, as, ⟨_, _, _, _, _, rfl⟩, hi, ha,
            hstep _ _ (fun _ _ _ _ _ h hw => h _ hw) T hT c hc H _ _ as hs hts⟩) _ ht
  | .codata (decl := decl) _ _ _ _ _ _ _ S hS => fun ⟨X, hX, hx⟩ ht =>
    ⟨fun D H w' a => ∃ w, Term.LevelEquiv w w' ∧ X D H w a,
      fun T hT H w' a ⟨w, hww, hw⟩ => by
        obtain ⟨o, ⟨r, qs, ls, ps, Δ, as, ss, Ss, gs, rfl, rfl⟩, ho⟩ := hX T hT H w a hw
        cases hww with
        | corec _ _ _ _ hl has hss hSs hgs =>
          refine ⟨_, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
            RunDesRel.rel_levelEquiv hd ih (hS X T hT) _ _ (hS _ T hT)
              (fun _ => Option.rel_map (fun D' _ _ _ _ => RunRel.computed_levelEquiv hd
                fun _ _ _ h hv => ⟨_, hv, h⟩) _) H _ _ a ho fun d _ => ?_⟩
          exact .obs _ _ _ d hl (has.rename _)
            (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl has hss hSs hgs)) (Terms.LevelEquiv.refl _),
      _, ht, hx⟩
termination_by structural h => h

/-- The relation of run time of the terms of the fields of a telescope relates terms whose levels
change for equal ones to the addresses that another relation of the same telescope relates the terms
to, at positions whose relations do so. -/
theorem RunTelRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P))
    {rs₁ : Nat → Nest RunNestLeaf} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Nest RunNestLeaf) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₂ Θ S₂ →
        (∀ i, Nest.Rel (fun x y => ∀ H t t' a, x.2 H t a → Term.LevelEquiv t t' → y.2 H t' a)
          (rs₁ i) (rs₂ i)) →
        ∀ H ts ts' as, S₁ H ts as → Terms.LevelEquiv ts ts' → S₂ H ts' as
  | .nil, _, _, h', _ => by
    cases h'
    exact fun _ ts ts' as h hts => match ts, ts', as, h, hts with
      | .nil, .nil, [], _, _ => trivial
  | .cons hA hF hR _ hG hrs, _, _, h', hRs => by
    cases h' with
    | cons hA' hF' hR' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
      have hFF := FieldRel.unique hd ihm hF _ _ hF'
      have hRR := RunFieldRel.congr hd ihm (Nat.forall_lt (levelRel_run_unique hd) _) hR _ hR'
      have hFt := fun t t' htt (ht : Term.LevelEquiv t t') =>
        (hFF t' t').1
          (FieldRel.rel_levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _) hF htt ht ht)
      exact fun H => RunFieldsRel.cons_levelEquiv
        (fun t t' a ⟨htt, hr⟩ ht => ⟨hFt t t' htt ht,
          fun hp => (hRR H t' a).1 (RunFieldRel.rel_levelEquiv hd ih hR (hr hp) ht)⟩)
        fun t t' _ ⟨htt, _⟩ ht => RunTelRel.rel_levelEquiv hd ih (hG t htt) _ _
          (RunTelRel.levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _)
            (hG' t' (hFt t t' htt ht))
            ((Telescope.LevelEquiv.refl _).subst₀ (Subst₀.LevelEquiv.single ht.symm))
            (fun _ => Nest.rel₃_refl (fun _ => ⟨Term.LevelEquiv.refl _, rfl⟩) _))
          (fun i => hRs (i + 1)) H
    | nested hrs' _ _ _ => exact absurd ((hRs 0).eq_plain.1.2 hrs) hrs'
  | .nested hrs hR _ hG, _, _, h', hRs => by
    cases h' with
    | cons _ _ _ _ _ hrs' => exact absurd ((hRs 0).eq_plain.1.1 hrs') hrs
    | nested hrs' hR' _ hG' =>
      exact fun H => RunFieldsRel.cons_levelEquiv
        (fun t t' a h ht hp =>
          RunNestRel.rel_levelEquiv hd ih hR _ _ hR' (hRs 0) H t t' a (h hp) ht)
        fun t _ _ _ _ => RunTelRel.rel_levelEquiv hd ih (hG t) _ _ (hG' t)
          (fun i => hRs (i + 1)) H
termination_by structural h _ _ _ _ => h

/-- The relation of run time that the graph of the nestings gives the terms of a type relates a term
whose levels change for equal ones to the addresses that another relation of the same type relates
the term to, at positions whose relations do so. -/
theorem RunNestRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P))
    {τ₁ : Nest RunNestLeaf} {A : Term 0 []} {R₁ : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₁ A R₁ →
      ∀ (τ₂ : Nest RunNestLeaf) (R₂ : RunRel),
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₂ A R₂ →
        Nest.Rel (fun x y => ∀ H t t' a, x.2 H t a → Term.LevelEquiv t t' → y.2 H t' a) τ₁ τ₂ →
        ∀ H t t' a, R₁ H t a → Term.LevelEquiv t t' → R₂ H t' a
  | .plain hA hR, _, _, h', hτ => by
    cases hτ
    cases h' with
    | plain hA' hR' =>
      cases Computesι.det hd hA hA'
      have hRR := RunFieldRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _)
        (Nat.forall_lt (levelRel_run_unique hd) _) hR _ hR'
      exact fun H t t' a h ht => (hRR H t' a).1 (RunFieldRel.rel_levelEquiv hd ih hR h ht)
  | .direct _, _, _, h', hτ => by
    cases hτ with
    | direct hr =>
      cases h' with
      | direct _ => exact hr
  | .codata hD _ _ _ hA hκ _ _ _ hS, _, _, h', hτ => by
    cases hτ with
    | inst hνs =>
      cases h' with
      | codata hD' _ _ _ hA' _ _ _ _ hS' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        cases hT
        cases has
        refine fun H _ _ _ => RunRel.computed_levelEquiv hd fun v v' a hv hvv => ?_
        obtain ⟨o, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩, ho⟩ := hv
        cases hvv with
        | corec _ _ _ _ hl has hss hSs hgs =>
          refine ⟨_, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
            RunNestDesRel.rel_levelEquiv hd ih hS _ _ hS' (Nesting.ofArgs_rel₃ hνs) H _ _ a ho
              fun d _ => ?_⟩
          exact .obs _ _ _ d hl (has.rename _)
            (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl has hss hSs hgs)) (Terms.LevelEquiv.refl _)
      | codataProp hD' _ _ _ hA' _ hκ' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        exact nomatch hκ.symm.trans hκ'
  | .codataProp hD _ _ _ hA _ hκ _ _, _, _, h', hτ => by
    cases hτ with
    | inst hνs =>
      cases h' with
      | codata hD' _ _ _ hA' hκ' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        exact nomatch hκ.symm.trans hκ'
      | codataProp => exact fun _ _ _ _ _ _ => trivial
termination_by structural h _ _ _ _ => h

/-- The relation of run time of the observations by destructors read at nestings relates
observations whose levels change for equal ones to the addresses that another relation of the same
destructors relates the observations to, at positions whose relations do so. -/
theorem RunNestDesRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program}
    {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P)) {D : Name}
    {Γ : Scope} {ν₁ : Nesting RunNestLeaf Γ} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₁ ds @θ S₁ →
      ∀ (ν₂ : Nesting RunNestLeaf Γ) (S₂ : RunObsRel),
        RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₂ ds @θ S₂ →
        Nesting.Rel (fun x y => ∀ H t t' a, x.2 H t a → Term.LevelEquiv t t' → y.2 H t' a)
          @ν₁ @ν₂ →
        ∀ H o o' a, S₁ H o a → (∀ d ps, Term.LevelEquiv (o d ps) (o' d ps)) → S₂ H o' a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ _ _ _ => trivial
  | .cons (d := d) (ps := ps) (B := B) (ψ := ψ) (ς := ς) (SΘ := SΘ) (RΘ := RΘ) (i := i) hi hν hΘ
      hRΘ F R hF hR _ hG _, _, _, h', hRs => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hSΘp := TelRel.isPer hd ihm (fun _ => .plain) hΘ
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRs) B
    cases h' with
    | cons hi' _ hΘ' hRΘ' F' R' hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        NestRel.unique hd ihm (hF ts hts) _ _ (hF' ts ((hSS _ _).1 hts))
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      have hE : ∀ f f', AbstractionRel (ps := ps) SΘ F f f → Term.LevelEquiv f f' →
          AbstractionRel (ps := ps) SΘ F f' f' :=
        fun _ _ h ef ts us hts =>
          have hts' := hSΘp.trans hts (hSΘp.symm hts)
          NestRel.rel_levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _) (hF ts hts')
            _ _ _ (hF ts hts') .plain (h ts us hts) (ef.subst (Subst.LevelEquiv.refl _))
            (ef.subst (Subst.LevelEquiv.refl _))
      have hRΘΘ := RunTelRel.congr hd ihm ihu hRΘ _ _ hRΘ' fun _ => .plain
      have hfields : ∀ H (ts : Args 0 [] ps) bs, RΘ H ts.terms bs → SΘ ts.terms ts.terms :=
        fun H ts bs hts =>
          RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (ψ := ψ) (ς := ς)
        (f := f)
        (H := H) (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := hfields H ts bs hts
          RunNestRel.unique hd ihm ihu (hR ts hts') _ (hR' ts ((hSS _ _).1 hts'))
      have hRinv : ∀ H (ts : Args 0 [] ps) bs, RΘ H ts.terms bs → (R ts.terms).LevelInvariant :=
        fun H ts bs hts =>
          have hts' := hfields H ts bs hts
          fun h ht => RunNestRel.rel_levelEquiv hd ih (hR ts hts') _ _ (hR ts hts') .plain _ _ _ _
            h ht
      exact fun H o o' a ⟨h₁, h₂, h₃⟩ e =>
        have h₁' := hE _ _ h₁ (e d ps)
        ⟨(hEE _ _).1 h₁', fun hp => (hAA _ H a).1 ((h₂ hp).levelEquiv hRinv (e d ps)),
          RunNestDesRel.rel_levelEquiv hd ih (hG _ h₁) _ _
            (RunNestDesRel.levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _)
              (hG' _ ((hEE _ _).1 h₁')) (Destructors.LevelEquiv.refl _)
              (Subst.LevelEquiv.snoc (Subst.LevelEquiv.refl θ) (e d ps).symm)
              (fun _ _ => Nest.rel₃_refl (fun _ => ⟨Term.LevelEquiv.refl _, rfl⟩) _))
            (Nesting.lift_rel₃ hRs) H o o' a h₃ e⟩
    | nested _ hν' => exact absurd (hB.eq_plain.1.2 hν) hν'
  | .nested (d := d) (ps := ps) (B := B) (SΘ := SΘ) (RΘ := RΘ) hi hν hΘ hRΘ R hR _ hG, _, _, h',
      hRs => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRs) B
    cases h' with
    | cons _ hν' => exact absurd (hB.eq_plain.1.1 hν') hν
    | nested hi' _ hΘ' hRΘ' R' hR' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hRΘΘ := RunTelRel.congr hd ihm ihu hRΘ _ _ hRΘ' fun _ => .plain
      have hfields : ∀ H (ts : Args 0 [] ps) bs, RΘ H ts.terms bs → SΘ ts.terms ts.terms :=
        fun H ts bs hts =>
          RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
      exact fun H o o' a ⟨h₁, h₂⟩ e =>
        ⟨fun hp H₁ hH₁ ts bs hts ϖ =>
          have hts' := (hRΘΘ _ _ _).2 hts
          have htt := hfields _ ts bs hts'
          have ⟨w, H₂, Rr, he, hw⟩ := h₁ hp H₁ hH₁ ts bs hts' ϖ
          ⟨w, H₂, Rr, he, RunNestRel.rel_levelEquiv hd ih (hR ts htt) _ _
            (hR' ts ((hSS _ _).1 htt)) hB _ _ _ _ hw ((e d ps).subst (Subst.LevelEquiv.refl _))⟩,
          RunNestDesRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _
            (hG' (.sort ⟨.type, .zero⟩)) (Nesting.lift_rel₃ hRs) H o o' a h₂ e⟩
termination_by structural h _ _ _ _ => h

/-- The relation of run time of the observations by destructors relates observations whose levels
change for equal ones to the addresses that another relation of the same destructors relates the
observations to, at relations of the recursive destructors that do so. -/
theorem RunDesRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P))
    {D : Name} {rs₁ : Nat → Option RunRel} {Γ : Scope} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₁ ds @θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunObsRel),
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t t' a, x H t a → Term.LevelEquiv t t' → y H t' a)
          (rs₁ i) (rs₂ i)) →
        ∀ H o o' a, S₁ H o a → (∀ d ps, Term.LevelEquiv (o d ps) (o' d ps)) → S₂ H o' a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ _ _ _ => trivial
  | .cons (d := d) (ps := ps) (ψ := ψ) (ς := ς) (SΘ := SΘ) (RΘ := RΘ) (i := i) hi hΘ hRΘ F R hB hF hR
      _ hG hrs, _, _,
      h', hRs => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hSΘp := TelRel.isPer hd ihm (fun _ => .plain) hΘ
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' _ hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ihm (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      have hE : ∀ f f', AbstractionRel (ps := ps) SΘ F f f → Term.LevelEquiv f f' →
          AbstractionRel (ps := ps) SΘ F f' f' :=
        fun _ _ h ef ts us hts =>
          have hts' := hSΘp.trans hts (hSΘp.symm hts)
          have ⟨_, hv⟩ := hB ts hts'
          FieldRel.rel_levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _)
            (hF ts hts' _ hv)
            (h ts us hts) (ef.subst (Subst.LevelEquiv.refl _)) (ef.subst (Subst.LevelEquiv.refl _))
      have hRΘΘ := RunTelRel.congr hd ihm ihu hRΘ _ _ hRΘ' fun _ => .plain
      have hfields : ∀ H (ts : Args 0 [] ps) bs, RΘ H ts.terms bs → SΘ ts.terms ts.terms :=
        fun H ts bs hts =>
          RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (ψ := ψ) (ς := ς)
        (f := f)
        (H := H) (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := hfields H ts bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.congr hd ihm ihu (hR ts hts' _ hv) _ (hR' ts ((hSS _ _).1 hts') _ hv)
      have hRinv : ∀ H (ts : Args 0 [] ps) bs, RΘ H ts.terms bs → (R ts.terms).LevelInvariant :=
        fun H ts bs hts =>
          have hts' := hfields H ts bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.rel_levelEquiv hd ih (hR ts hts' _ hv)
      exact fun H o o' a ⟨h₁, h₂, h₃⟩ e =>
        have h₁' := hE _ _ h₁ (e d ps)
        ⟨(hEE _ _).1 h₁', fun hp => (hAA _ H a).1 ((h₂ hp).levelEquiv hRinv (e d ps)),
          RunDesRel.rel_levelEquiv hd ih (hG _ h₁) _ _
            (RunDesRel.levelEquiv hd (Nat.forall_lt (levelRel_levelInvariant hd) _)
              (hG' _ ((hEE _ _).1 h₁'))
              (Destructors.LevelEquiv.refl _) (Subst.LevelEquiv.snoc (Subst.LevelEquiv.refl θ) (e d ps).symm))
            (fun i => hRs (i + 1)) H o o' a h₃ e⟩
    | recursive _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (d := d) (ps := ps) hi hrs hRΘ _ hG, _, _, h', hRs => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    cases h' with
    | cons _ _ _ _ _ _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hi' hrs' hRΘ' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hRΘΘ := RunTelRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _) ihu hRΘ _ _ hRΘ'
          fun _ => .plain
        exact fun H o o' a ⟨h₁, h₂⟩ e =>
          ⟨fun hp H₁ hH₁ ts bs hts ϖ =>
            have ⟨w, H₂, R, he, hw⟩ := h₁ hp H₁ hH₁ ts bs ((hRΘΘ _ _ _).2 hts) ϖ
            ⟨w, H₂, R, he, hr _ _ _ _ hw ((e d ps).subst (Subst.LevelEquiv.refl _))⟩,
            RunDesRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _
              (hG' (.sort ⟨.type, .zero⟩)) (fun i => hRs (i + 1)) H o o' a h₂ e⟩
termination_by structural h _ _ _ _ => h

/-- The relation of run time of the type of a field relates a term whose levels change for equal
ones to the same addresses. -/
theorem RunFieldRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P))
    {v : Term 0 []} {R : RunRel} :
    RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R → R.LevelInvariant
  | .univ h =>
    RunRel.computed_levelEquiv hd fun _ _ _ hv hvv => RunUnivRel.rel_levelEquiv hd ih h hv hvv
  | .univBelow m hm h => RunRel.computed_levelEquiv hd fun _ _ _ hv hvv => ih m hm h hv hvv
  | .prop _ => fun _ _ => trivial
  | .propBelow _ _ _ => fun _ _ => trivial
termination_by structural h => h

end

/-- The relations of run time of every level relate a term whose levels change for equal ones to the
same addresses, in a signature whose names are distinct. -/
theorem levelRel_run_levelInvariant {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : RunLevelRel.LevelInvariant ((levelRel sig ι n).run P) :=
  have ih : ∀ m, m < n → RunLevelRel.LevelInvariant ((levelRel sig ι m).run P) :=
    fun m _ => levelRel_run_levelInvariant hd m
  fun h => RunUnivRel.rel_levelEquiv hd ih (levelRel_run_iff.1 h)
termination_by n
decreasing_by all_goals assumption

/-- The relation of run time of a canonical type relates a term whose levels change for equal ones to
the same addresses, in a signature whose names are distinct. -/
theorem HasRun.rel_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R : RunRel} (hd : sig.Distinct) : HasRun sig ι P v R → R.LevelInvariant
  | .univ n hn => levelRel_run_levelInvariant hd n hn
  | .prop _ _ _ hR => fun _ _ => hR _ _ _

/-- A term whose levels change for equal ones is related to the addresses that the term is related
to, in a signature whose names are distinct. -/
theorem RunsAs.term_levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {H : Heap}
    {t t' : Term 0 []} {a : Nat} {A : Term 0 []} (hd : sig.Distinct)
    (ht : Term.LevelEquiv t t') : RunsAs sig ι P H t a A → RunsAs sig ι P H t' a A
  | ⟨v, hA, .inl hp⟩ => ⟨v, hA, .inl hp⟩
  | ⟨v, hA, .inr ⟨R, hR, hr⟩⟩ =>
    ⟨v, hA, .inr ⟨R, hR, RunRel.computed_levelEquiv hd (fun _ _ _ h hw => hR.rel_levelEquiv hd h hw)
      hr ht⟩⟩

end Sic.Core
