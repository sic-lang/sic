module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Syntax.Signature

/-!
# Properties of the Relations of Run Time

The relations of run time of annex 18 of RFC 36 are unique: two derivations of `rt(U_n)` for the
same type relate the same terms to the same addresses in each heap, by mutual recursion on the
graph, as the equality proves its uniqueness, of which it reads the equality of the terms of each
field and of each result.
The uniqueness of a level follows from that of the levels below it, which `Sic.Core.Meaning.Uniqueness`
proves by induction on the level.

ADE prove the irrelevance of the derivations of their relation, in
`Graded/Erasure/LogicalRelation/Irrelevance.agda`; their target language has no heap.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Statements -/

/-- The relations of run time of the types of a level are unique: two of them for the same type
relate the same terms to the same addresses in each heap. -/
abbrev RunLevelRel.Unique (L : RunLevelRel) : Prop :=
  ∀ {v : Term 0 []} {R R' : RunRel}, L v R → L v R' → ∀ H t a, R H t a ↔ R' H t a

/-! ## Relations Built from Others -/

/-- `rt(U_n)` at the level `n`, as the clauses of `RunUnivRel`. -/
theorem levelRel_run_iff {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    {v : Term 0 []} {R : RunRel} :
    (levelRel sig ι n).run P v R ↔ RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R := by
  rw [levelRel]

/-- `®⇓(R)` relates the same terms and addresses for relations `R` that do. -/
theorem RunRel.computed_congr {sig : Signature} {ι : Interpretation} {R R' : RunRel}
    (h : ∀ H t a, R H t a ↔ R' H t a) :
    ∀ H t a, R.computed sig ι H t a ↔ R'.computed sig ι H t a :=
  fun H _ a => ⟨fun ⟨v, ht, hv⟩ => ⟨v, ht, (h H v a).1 hv⟩, fun ⟨v, ht, hv⟩ => ⟨v, ht, (h H v a).2 hv⟩⟩

/-- `R^p` relates the same terms and addresses for relations `R` that do. -/
theorem RunRel.atGrade_congr {p : Grade} {R R' : RunRel} {H : Heap} {t : Term 0 []} {a : Nat}
    (h : R H t a ↔ R' H t a) : RunRel.atGrade p R H t a ↔ RunRel.atGrade p R' H t a :=
  imp_congr_right fun _ => h

/-- The relations of run time of the terms of the fields of two telescopes `x : A, Θ` relate the
same terms and addresses in a heap, when those of `A` do, and those of `Θ[a / x]` do for each term
`a` that the first relates. -/
theorem RunFieldsRel.cons_congr {F F' : RunRel} {G G' : Term 0 [] → RunFieldsRel} {H : Heap}
    (hF : ∀ t a, F H t a ↔ F' H t a)
    (hG : ∀ t a, F H t a → ∀ ts as, G t H ts as ↔ G' t H ts as) :
    ∀ ts as, RunFieldsRel.cons F G H ts as ↔ RunFieldsRel.cons F' G' H ts as
  | .nil, _ => .rfl
  | .cons _ _, [] => .rfl
  | .cons t ts, a :: as =>
    ⟨fun ⟨h₁, h₂⟩ => ⟨(hF t a).1 h₁, (hG t a h₁ ts as).1 h₂⟩,
      fun ⟨h₁, h₂⟩ =>
        have h₁' := (hF t a).2 h₁
        ⟨h₁', (hG t a h₁' ts as).2 h₂⟩⟩

/-- `(®_c)` relates the same terms and addresses for relations of the terms of the fields that
do. -/
theorem DataType.runCtorRel_congr {j g k : Nat} {Δ : Scope} {sig : Signature} {I : Instance j g}
    {D : Name}
    {T : DataType j g k Δ} {S S' : Constructor j g k Δ → RunFieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ H ts as, S c H ts as ↔ S' c H ts as) :
    ∀ H v a, T.runCtorRel sig I D S H v a ↔ T.runCtorRel sig I D S' H v a :=
  fun H _ _ =>
    ⟨fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ => ⟨c, hc, i, ts, as, hv, hi, ha, (h c hc H ts as).1 hs⟩,
      fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ =>
        ⟨c, hc, i, ts, as, hv, hi, ha, (h c hc H ts as).2 hs⟩⟩

/-- `(®_μ)` relates the same terms and addresses for relations of the terms of the fields that
do. -/
theorem DataType.runBlockRel_congr {j g k : Nat} {Δ : Scope} {sig : Signature} {I : Instance j g}
    {Ts : List (DataType j g k Δ)} {S S' : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as ↔ S' X c H ts as)
    (D : Name) :
    ∀ H v a, DataType.runBlockRel sig I Ts S D H v a ↔ DataType.runBlockRel sig I Ts S' D H v a :=
  fun _ _ _ => ⟨fun hr X hX => hr X fun T hT H v a hc =>
      hX T hT H v a ((DataType.runCtorRel_congr (h X T hT) H v a).1 hc),
    fun hr X hX => hr X fun T hT H v a hc =>
      hX T hT H v a ((DataType.runCtorRel_congr (h X T hT) H v a).2 hc)⟩

/-- `(®_d)` relates in a heap `H'` what it relates in a heap `H`, at relations of the observations
that do so. -/
theorem runCorecRel_mono {D : Name} {S S' : RunObsRel} {H H' : Heap}
    (h : ∀ o a, S H o a → S' H' o a) {v : Term 0 []} {a : Nat} :
    runCorecRel D S H v a → runCorecRel D S' H' v a :=
  fun ⟨o, hv, hs⟩ => ⟨o, hv, h o a hs⟩

/-- `(®_ν)` relates the same terms and addresses for relations of the observations that do. -/
theorem CodataType.runBlockRel_congr {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
    {S S' : (Name → RunRel) → CodataType j g k Δ → RunObsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ H o a, S X T H o a ↔ S' X T H o a) (D : Name) :
    ∀ H v a, CodataType.runBlockRel Ts S D H v a ↔ CodataType.runBlockRel Ts S' D H v a :=
  fun _ _ _ => ⟨fun ⟨X, hX, hv⟩ => ⟨X, fun T hT H v a hx =>
      runCorecRel_mono (fun o a => (h X T hT H o a).1) (hX T hT H v a hx), hv⟩,
    fun ⟨X, hX, hv⟩ => ⟨X, fun T hT H v a hx =>
      runCorecRel_mono (fun o a => (h X T hT H o a).2) (hX T hT H v a hx), hv⟩⟩

/-- `(®_x̄)` relates the same abstractions and addresses for relations of the arguments that relate
the same arguments, and relations of the results that relate the same terms at the arguments that
they relate. -/
theorem RunAbstractionRel.congr {P : Program} {ps : List Parameter} {i : Nat}
    {SΘ SΘ' : RunFieldsRel} {F F' : Terms 0 [] → RunRel}
    (hS : ∀ H ts bs, SΘ H ts bs ↔ SΘ' H ts bs)
    (hF : ∀ H (ts : Args 0 [] ps) bs, SΘ H ts.terms bs → ∀ H' t w, F ts.terms H' t w ↔ F' ts.terms H' t w)
    {f : Term 0 (Scope.extend [] ps.length)} {H : Heap} {a : Nat} :
    RunAbstractionRel P i SΘ F f H a ↔ RunAbstractionRel P i SΘ' F' f H a :=
  ⟨fun h H' hH ts bs hts ϖ =>
      have hts' := (hS H' ts.terms bs).2 hts
      have ⟨w, H'', R, he, hr⟩ := h H' hH ts bs hts' ϖ
      ⟨w, H'', R, he, (hF H' ts bs hts' H'' _ w).1 hr⟩,
    fun h H' hH ts bs hts ϖ =>
      have ⟨w, H'', R, he, hr⟩ := h H' hH ts bs ((hS H' ts.terms bs).1 hts) ϖ
      ⟨w, H'', R, he, (hF H' ts bs hts H'' _ w).2 hr⟩⟩

/-! ## A Type Has One Level and One Sort -/

/-- A type of a universe has one level of run time, in a signature whose names are distinct. -/
theorem RunUnivRel.level {sig : Signature} {ι : Interpretation} {P : Program} {n m : Nat}
    {below₁ : LevelRel.Below n} {below₂ : LevelRel.Below m} {v : Term 0 []} {R R' : RunRel}
    (hd : sig.Distinct) (h : RunUnivRel sig ι P n below₁ v R)
    (h' : RunUnivRel sig ι P m below₂ v R') : n = m := by
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

/-- A type of a universe of run time is not a proposition, in a signature whose names are
distinct. -/
theorem RunUnivRel.not_prop {sig : Signature} {ι : Interpretation} {P : Program} {n m : Nat}
    {below₁ : LevelRel.Below n} {below₂ : LevelRel.Below m} {v : Term 0 []} {R : RunRel}
    {b : Prop} (hd : sig.Distinct) (h : RunUnivRel sig ι P n below₁ v R)
    (h' : PropRel sig ι m below₂ v b) : False := by
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

/-! ## The Relation of Run Time Reads the Equality -/

/-- The relation of run time of the terms of the fields of a telescope without recursive fields
relates only terms that the equality gives to its fields, in a signature whose names are distinct,
if the relations of the levels below `n` are partial equivalence relations. -/
theorem RunTelRel.fieldsRel {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    {rs : Nat → Option RunRel} {ps : List Parameter} {Θ : Telescope 0 [] ps} {RΘ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ RΘ → (∀ i, rs i = none) →
      ∀ (rs' : Nat → Option TermRel) (SΘ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type rs' Θ SΘ → (∀ i, rs' i = none) →
        ∀ H ts bs, RΘ H ts bs → SΘ ts ts
  | .nil, _, _, _, h', _, _, ts, bs, hr => by
    cases h'
    match ts, bs, hr with
    | .nil, [], _ => trivial
  | .cons hA hF _ _ hG _, hn, _, _, h', hn', H, ts, bs, hr => by
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ihm hF _ _ hF'
      match ts, bs, hr with
      | .cons t ts, _ :: bs, ⟨⟨htt, _⟩, hg⟩ =>
        exact ⟨(hFF t t).1 htt, RunTelRel.fieldsRel hd ihm (hG t htt) (fun i => hn (i + 1)) _ _
          (hG' t ((hFF t t).1 htt)) (fun i => hn' (i + 1)) H ts bs hg⟩
    | recursive hrs' _ _ => rw [hn' 0] at hrs'; cases hrs'
  | .recursive hrs _ _, hn, _, _, _, _, _, _, _, _ => by rw [hn 0] at hrs; cases hrs
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-! ## Uniqueness

A type has one relation of run time, by mutual recursion on the graph: the relations of the fields,
of the arguments and of the results of the destructors are unique, those of the equality by its own
uniqueness, and those of run time by recursion. -/

mutual

/-- A type of `U_n` has a unique relation of run time, if the relations of the levels below `n`
are unique and their equalities partial equivalence relations. -/
theorem RunUnivRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P)) {v : Term 0 []}
    {R : RunRel} :
    RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R →
      ∀ (R' : RunRel), RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R' →
        ∀ H t a, R H t a ↔ R' H t a
  | .univ hl _, _, h' => by
    cases h' with
    | univ => exact fun _ _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .prop hl _, _, h' => by
    cases h' with
    | prop => exact fun _ _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
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
      exact DataType.runBlockRel_congr (fun X T hT c hc => RunTelRel.congr hd ihm ih (hS X T hT c hc)
        _ _ (hS' X T hT c hc) fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) _
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
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
      exact CodataType.runBlockRel_congr (fun X T hT => RunDesRel.congr hd ihm ih (hS X T hT) _ _
        (hS' X T hT) fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- The relations of run time of the terms of the fields of a telescope relate the same terms and
addresses, at relations of the recursive fields that do. -/
theorem RunTelRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P))
    {rs₁ : Nat → Option RunRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a ↔ y H t a) (rs₁ i) (rs₂ i)) →
        ∀ H ts as, S₁ H ts as ↔ S₂ H ts as
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => .rfl
  | .cons hA hF hR _ hG hrs, _, _, h', hRs => by
    cases h' with
    | cons hA' hF' hR' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ihm hF _ _ hF'
      have hRR := RunFieldRel.congr hd ihm ih hR _ hR'
      exact fun H => RunFieldsRel.cons_congr
        (fun t a => and_congr (hFF t t) (RunRel.atGrade_congr (hRR H t a)))
        fun t _ ⟨htt, _⟩ => RunTelRel.congr hd ihm ih (hG t htt) _ _ (hG' t ((hFF t t).1 htt))
          (fun i => hRs (i + 1)) H
    | recursive hrs' _ _ => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, h', hRs => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact fun H => RunFieldsRel.cons_congr (fun t a => RunRel.atGrade_congr (hr H t a))
          fun t _ _ => RunTelRel.congr hd ihm ih (hG t) _ _ (hG' t) (fun i => hRs (i + 1)) H
termination_by structural h _ _ _ _ => h

/-- The relations of run time of the observations by destructors relate the same observations and
addresses, at relations of the recursive destructors that do. -/
theorem RunDesRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P)) {D : Name}
    {rs₁ : Nat → Option RunRel} {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₁ ds @θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunObsRel),
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a ↔ y H t a) (rs₁ i) (rs₂ i)) →
        ∀ H o a, S₁ H o a ↔ S₂ H o a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) (i := i) hi hΘ hRΘ F R hB hF hR _ hG hrs, _, _, h', hRs => by
    have hSΘp := TelRel.isPer hd ihm (fun _ _ h => by cases h) hΘ
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' _ hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ihm (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      have hRΘΘ := RunTelRel.congr hd ihm ih hRΘ _ _ hRΘ' TelRel.none_rel
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (f := f) (H := H)
        (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.congr hd ihm ih (hR ts hts' _ hv) _ (hR' ts ((hSS _ _).1 hts') _ hv)
      exact fun H o a =>
        ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨(hEE _ _).1 h₁, fun hp => (hAA _ H a).1 (h₂ hp),
            (RunDesRel.congr hd ihm ih (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁)) (fun i => hRs (i + 1))
              H o a).1 h₃⟩,
          fun ⟨h₁, h₂, h₃⟩ =>
            have h₁' := (hEE _ _).2 h₁
            ⟨h₁', fun hp => (hAA _ H a).2 (h₂ hp),
              (RunDesRel.congr hd ihm ih (hG _ h₁') _ _ (hG' _ h₁) (fun i => hRs (i + 1)) H o a).2 h₃⟩⟩
    | recursive _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hi hrs hRΘ _ hG, _, _, h', hRs => by
    cases h' with
    | cons _ _ _ _ _ _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hi' hrs' hRΘ' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hRΘΘ := RunTelRel.congr hd ihm ih hRΘ _ _ hRΘ' TelRel.none_rel
        have hGG := RunDesRel.congr hd ihm ih (hG (.sort ⟨.type, .zero⟩)) _ _
          (hG' (.sort ⟨.type, .zero⟩)) (fun i => hRs (i + 1))
        exact fun H o a => and_congr
          (imp_congr_right fun _ => RunAbstractionRel.congr hRΘΘ fun _ _ _ _ => hr)
          (hGG H o a)
termination_by structural h _ _ _ _ => h

/-- The type of a field has a unique relation of run time. -/
theorem RunFieldRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P)) {v : Term 0 []}
    {R : RunRel} :
    RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R →
      ∀ (R' : RunRel), RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R' →
        ∀ H t a, R H t a ↔ R' H t a
  | .univ h, _, h' => by
    cases h' with
    | univ h' => exact RunRel.computed_congr (RunUnivRel.congr hd ihm ih h _ h')
    | univBelow m hm h' => exact absurd (RunUnivRel.level hd h (levelRel_run_iff.1 h')) (by omega)
    | prop h' => exact (RunUnivRel.not_prop hd h h').elim
    | propBelow m _ h' => exact (RunUnivRel.not_prop hd h (levelRel_prop_iff.1 h')).elim
  | .univBelow m hm h, _, h' => by
    cases h' with
    | univ h' => exact absurd (RunUnivRel.level hd h' (levelRel_run_iff.1 h)) (by omega)
    | univBelow m' hm' h' =>
      cases RunUnivRel.level hd (levelRel_run_iff.1 h) (levelRel_run_iff.1 h')
      exact RunRel.computed_congr (ih m hm h h')
    | prop h' => exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 h) h').elim
    | propBelow m' _ h' =>
      exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 h) (levelRel_prop_iff.1 h')).elim
  | .prop h, _, h' => by
    cases h' with
    | univ h' => exact (RunUnivRel.not_prop hd h' h).elim
    | univBelow _ _ h' => exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 h') h).elim
    | prop => exact fun _ _ _ => .rfl
    | propBelow => exact fun _ _ _ => .rfl
  | .propBelow _ _ h, _, h' => by
    cases h' with
    | univ h' => exact (RunUnivRel.not_prop hd h' (levelRel_prop_iff.1 h)).elim
    | univBelow _ _ h' =>
      exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 h') (levelRel_prop_iff.1 h)).elim
    | prop => exact fun _ _ _ => .rfl
    | propBelow => exact fun _ _ _ => .rfl
termination_by structural h _ _ => h

end

end Sic.Core
