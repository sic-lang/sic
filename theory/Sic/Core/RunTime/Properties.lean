module

public import Sic.Core.Meaning.Relations
public import Sic.Core.RunTime.Relation
import Sic.Core.Syntax.Signature

/-!
# Properties of the Relation of Run Time

The relation of run time of annex 20 of RFC 36 is unique, and it is monotone in the heap.
A type has one relation of run time: two derivations of `rt(U_n)` for the same type relate the same
terms to the same addresses in each heap, by mutual recursion on the graph, as the meaning proves
its uniqueness, of which it reads the equality of the terms of each field and of each result.
A term related to an address in a heap stays related to it in each heap that extends it: the
relations of the data types read only values that the heap keeps, by induction on their least fixed
points, and those of the codata types are stated in each heap that extends it.

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

/-- A relation of run time is monotone in the heap: it relates a term to an address in each heap
that extends a heap in which it relates them. -/
abbrev RunRel.Monotone (R : RunRel) : Prop :=
  ∀ {H H' : Heap}, H.Extends H' → ∀ {t : Term 0 []} {a : Nat}, R H t a → R H' t a

/-- The relations of run time of the types of a level are monotone in the heap. -/
abbrev RunLevelRel.Monotone (L : RunLevelRel) : Prop :=
  ∀ {v : Term 0 []} {R : RunRel}, L v R → R.Monotone

/-! ## Relations Built from Others -/

/-- `rt(U_n)` at the level `n`, as the clauses of `RunUnivRel`. -/
theorem runLevelRel_iff {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    {v : Term 0 []} {R : RunRel} :
    runLevelRel sig ι P n v R ↔ RunUnivRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R := by
  rw [runLevelRel]

/-- `®⇓(R)` relates the same terms and addresses for relations `R` that do. -/
theorem RunRel.computed_congr {sig : Signature} {ι : Interpretation} {R R' : RunRel}
    (h : ∀ H t a, R H t a ↔ R' H t a) :
    ∀ H t a, R.computed sig ι H t a ↔ R'.computed sig ι H t a :=
  fun H _ a => ⟨fun ⟨v, ht, hv⟩ => ⟨v, ht, (h H v a).1 hv⟩, fun ⟨v, ht, hv⟩ => ⟨v, ht, (h H v a).2 hv⟩⟩

/-- `®⇓(R₂)` relates in a heap `H'` what `®⇓(R₁)` relates in a heap `H`, when `R₂` relates so the
canonical terms that `R₁` relates. -/
theorem RunRel.computed_mono {sig : Signature} {ι : Interpretation} {R₁ R₂ : RunRel} {H H' : Heap}
    (h : ∀ v a, R₁ H v a → R₂ H' v a) {t : Term 0 []} {a : Nat} :
    R₁.computed sig ι H t a → R₂.computed sig ι H' t a :=
  fun ⟨v, ht, hv⟩ => ⟨v, ht, h v a hv⟩

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

/-- The relation of run time of the terms of the fields of a telescope `x : A, Θ` relates in a heap
`H'` what another relates in a heap `H`, when the relations of `A` do so, and those of `Θ[a / x]` do
so for each term `a` that the first relates. -/
theorem RunFieldsRel.cons_mono {F F' : RunRel} {G G' : Term 0 [] → RunFieldsRel} {H H' : Heap}
    (hF : ∀ t a, F H t a → F' H' t a)
    (hG : ∀ t a, F H t a → ∀ ts as, G t H ts as → G' t H' ts as) :
    ∀ ts as, RunFieldsRel.cons F G H ts as → RunFieldsRel.cons F' G' H' ts as
  | .cons t ts, a :: as, ⟨h₁, h₂⟩ => ⟨hF t a h₁, hG t a h₁ ts as h₂⟩

/-- `(®_c)` relates the same terms and addresses for relations of the terms of the fields that
do. -/
theorem DataType.runCtorRel_congr {j g k : Nat} {Δ : Scope} {sig : Signature} {D : Name}
    {T : DataType j g k Δ} {S S' : Constructor j g k Δ → RunFieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ H ts as, S c H ts as ↔ S' c H ts as) :
    ∀ H v a, T.runCtorRel sig D S H v a ↔ T.runCtorRel sig D S' H v a :=
  fun H _ _ =>
    ⟨fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ => ⟨c, hc, i, ts, as, hv, hi, ha, (h c hc H ts as).1 hs⟩,
      fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ =>
        ⟨c, hc, i, ts, as, hv, hi, ha, (h c hc H ts as).2 hs⟩⟩

/-- `(®_c)` relates in a heap `H'` that extends `H` what it relates in `H`, at relations of the
terms of the fields that do so. -/
theorem DataType.runCtorRel_mono {j g k : Nat} {Δ : Scope} {sig : Signature} {D : Name}
    {T : DataType j g k Δ} {S S' : Constructor j g k Δ → RunFieldsRel} {H H' : Heap}
    (hH : H.Extends H') (h : ∀ c ∈ T.constructors, ∀ ts as, S c H ts as → S' c H' ts as)
    {v : Term 0 []} {a : Nat} : T.runCtorRel sig D S H v a → T.runCtorRel sig D S' H' v a :=
  fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ => ⟨c, hc, i, ts, as, hv, hi, hH.getElem? ha, h c hc ts as hs⟩

/-- `(®_μ)` relates the same terms and addresses for relations of the terms of the fields that
do. -/
theorem DataType.runBlockRel_congr {j g k : Nat} {Δ : Scope} {sig : Signature}
    {Ts : List (DataType j g k Δ)} {S S' : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as ↔ S' X c H ts as)
    (D : Name) : ∀ H v a, DataType.runBlockRel sig Ts S D H v a ↔ DataType.runBlockRel sig Ts S' D H v a :=
  fun _ _ _ => ⟨fun hr X hX => hr X fun T hT H v a hc =>
      hX T hT H v a ((DataType.runCtorRel_congr (h X T hT) H v a).1 hc),
    fun hr X hX => hr X fun T hT H v a hc =>
      hX T hT H v a ((DataType.runCtorRel_congr (h X T hT) H v a).2 hc)⟩

/-- `(®_μ)` is closed under the clauses of the constructors, when the relation of the terms of the
fields grows with the relations of the recursive fields. -/
theorem DataType.runBlockRel_fold {j g k : Nat} {Δ : Scope} {sig : Signature}
    {Ts : List (DataType j g k Δ)} {S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as)
    {T : DataType j g k Δ} (hT : T ∈ Ts) {H : Heap} {v : Term 0 []} {a : Nat}
    (h : T.runCtorRel sig T.name (S (DataType.runBlockRel sig Ts S)) H v a) :
    DataType.runBlockRel sig Ts S T.name H v a :=
  fun X hX => hX T hT H v a (DataType.runCtorRel_mono (List.prefix_refl H)
    (fun c hc ts as => hmono _ X (fun _ _ _ _ h => h X hX) T hT c hc H ts as) h)

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
  ⟨fun h H' hH ts bs hts =>
      have hts' := (hS H' ts.terms bs).2 hts
      have ⟨w, H'', he, hr⟩ := h H' hH ts bs hts'
      ⟨w, H'', he, (hF H' ts bs hts' H'' _ w).1 hr⟩,
    fun h H' hH ts bs hts =>
      have ⟨w, H'', he, hr⟩ := h H' hH ts bs ((hS H' ts.terms bs).1 hts)
      ⟨w, H'', he, (hF H' ts bs hts H'' _ w).2 hr⟩⟩

/-! ## A Type Has One Level and One Sort -/

/-- A type of a universe has one level of run time, in a signature whose names are distinct. -/
theorem RunUnivRel.level {sig : Signature} {ι : Interpretation} {P : Program} {n m : Nat}
    {below₁ : RunLevelRel.Below n} {below₂ : RunLevelRel.Below m} {v : Term 0 []} {R R' : RunRel}
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
    {below₁ : RunLevelRel.Below n} {below₂ : LevelRel.Below m} {v : Term 0 []} {R : RunRel}
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

/-! ## The Relation of Run Time Reads the Meaning -/

/-- The relation of run time of the terms of the fields of a telescope without recursive fields
relates only terms that the meaning gives to its fields, in a signature whose names are distinct. -/
theorem RunTelRel.fieldsRel {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    {below : RunLevelRel.Below n} (hd : sig.Distinct) {rs : Nat → Option RunRel}
    {ps : List Parameter} {Θ : Telescope 0 [] ps} {RΘ : RunFieldsRel} :
    RunTelRel sig ι P n below rs Θ RΘ → (∀ i, rs i = none) →
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
      have hFF := FieldRel.unique hd (fun m _ => levelRel_isPer hd m) hF _ _ hF'
      match ts, bs, hr with
      | .cons t ts, _ :: bs, ⟨⟨htt, _⟩, hg⟩ =>
        exact ⟨(hFF t t).1 htt, RunTelRel.fieldsRel hd (hG t htt) (fun i => hn (i + 1)) _ _
          (hG' t ((hFF t t).1 htt)) (fun i => hn' (i + 1)) H ts bs hg⟩
    | recursive hrs' _ _ => rw [hn' 0] at hrs'; cases hrs'
  | .recursive hrs _ _, hn, _, _, _, _, _, _, _, _ => by rw [hn 0] at hrs; cases hrs
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-! ## Uniqueness

A type has one relation of run time, by mutual recursion on the graph: the relations of the fields,
of the arguments and of the results of the destructors are unique, those of the meaning by its own
uniqueness, and those of run time by recursion. -/

mutual

/-- A type of `U_n` has a unique relation of run time, if the relations of the levels below `n`
are unique. -/
theorem RunUnivRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique) {v : Term 0 []}
    {R : RunRel} :
    RunUnivRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R →
      ∀ (R' : RunRel), RunUnivRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R' →
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
      exact DataType.runBlockRel_congr (fun X T hT c hc => RunTelRel.congr hd ih (hS X T hT c hc)
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
      exact CodataType.runBlockRel_congr (fun X T hT => RunDesRel.congr hd ih (hS X T hT) _ _
        (hS' X T hT) fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- The relations of run time of the terms of the fields of a telescope relate the same terms and
addresses, at relations of the recursive fields that do. -/
theorem RunTelRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique)
    {rs₁ : Nat → Option RunRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => runLevelRel sig ι P m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => runLevelRel sig ι P m) rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a ↔ y H t a) (rs₁ i) (rs₂ i)) →
        ∀ H ts as, S₁ H ts as ↔ S₂ H ts as
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => .rfl
  | .cons hA hF hR _ hG hrs, _, _, h', hRs => by
    cases h' with
    | cons hA' hF' hR' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd (fun m _ => levelRel_isPer hd m) hF _ _ hF'
      have hRR := RunFieldRel.congr hd ih hR _ hR'
      exact fun H => RunFieldsRel.cons_congr
        (fun t a => and_congr (hFF t t) (RunRel.atGrade_congr (hRR H t a)))
        fun t _ ⟨htt, _⟩ => RunTelRel.congr hd ih (hG t htt) _ _ (hG' t ((hFF t t).1 htt))
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
          fun t _ _ => RunTelRel.congr hd ih (hG t) _ _ (hG' t) (fun i => hRs (i + 1)) H
termination_by structural h _ _ _ _ => h

/-- The relations of run time of the observations by destructors relate the same observations and
addresses, at relations of the recursive destructors that do. -/
theorem RunDesRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique) {D : Name}
    {rs₁ : Nat → Option RunRel} {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => runLevelRel sig ι P m) D rs₁ ds @θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunObsRel),
        RunDesRel sig ι P n (fun m _ => runLevelRel sig ι P m) D rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a ↔ y H t a) (rs₁ i) (rs₂ i)) →
        ∀ H o a, S₁ H o a ↔ S₂ H o a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) (i := i) hi hΘ hRΘ F R hB hF hR _ hG hrs, _, _, h', hRs => by
    have ihm : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
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
      have hRΘΘ := RunTelRel.congr hd ih hRΘ _ _ hRΘ' TelRel.none_rel
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (f := f) (H := H)
        (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := RunTelRel.fieldsRel hd hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.congr hd ih (hR ts hts' _ hv) _ (hR' ts ((hSS _ _).1 hts') _ hv)
      exact fun H o a =>
        ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨(hEE _ _).1 h₁, fun hp => (hAA _ H a).1 (h₂ hp),
            (RunDesRel.congr hd ih (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁)) (fun i => hRs (i + 1))
              H o a).1 h₃⟩,
          fun ⟨h₁, h₂, h₃⟩ =>
            have h₁' := (hEE _ _).2 h₁
            ⟨h₁', fun hp => (hAA _ H a).2 (h₂ hp),
              (RunDesRel.congr hd ih (hG _ h₁') _ _ (hG' _ h₁) (fun i => hRs (i + 1)) H o a).2 h₃⟩⟩
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
        have hRΘΘ := RunTelRel.congr hd ih hRΘ _ _ hRΘ' TelRel.none_rel
        have hGG := RunDesRel.congr hd ih (hG (.sort ⟨.type, .zero⟩)) _ _
          (hG' (.sort ⟨.type, .zero⟩)) (fun i => hRs (i + 1))
        exact fun H o a => and_congr
          (imp_congr_right fun _ => RunAbstractionRel.congr hRΘΘ fun _ _ _ _ => hr)
          (hGG H o a)
termination_by structural h _ _ _ _ => h

/-- The type of a field has a unique relation of run time. -/
theorem RunFieldRel.congr {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique) {v : Term 0 []}
    {R : RunRel} :
    RunFieldRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R →
      ∀ (R' : RunRel), RunFieldRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R' →
        ∀ H t a, R H t a ↔ R' H t a
  | .univ h, _, h' => by
    cases h' with
    | univ h' => exact RunRel.computed_congr (RunUnivRel.congr hd ih h _ h')
    | univBelow m hm h' => exact absurd (RunUnivRel.level hd h (runLevelRel_iff.1 h')) (by omega)
    | prop h' => exact (RunUnivRel.not_prop hd h h').elim
    | propBelow m _ h' => exact (RunUnivRel.not_prop hd h (levelRel_prop_iff.1 h')).elim
  | .univBelow m hm h, _, h' => by
    cases h' with
    | univ h' => exact absurd (RunUnivRel.level hd h' (runLevelRel_iff.1 h)) (by omega)
    | univBelow m' hm' h' =>
      cases RunUnivRel.level hd (runLevelRel_iff.1 h) (runLevelRel_iff.1 h')
      exact RunRel.computed_congr (ih m hm h h')
    | prop h' => exact (RunUnivRel.not_prop hd (runLevelRel_iff.1 h) h').elim
    | propBelow m' _ h' =>
      exact (RunUnivRel.not_prop hd (runLevelRel_iff.1 h) (levelRel_prop_iff.1 h')).elim
  | .prop h, _, h' => by
    cases h' with
    | univ h' => exact (RunUnivRel.not_prop hd h' h).elim
    | univBelow _ _ h' => exact (RunUnivRel.not_prop hd (runLevelRel_iff.1 h') h).elim
    | prop => exact fun _ _ _ => .rfl
    | propBelow => exact fun _ _ _ => .rfl
  | .propBelow _ _ h, _, h' => by
    cases h' with
    | univ h' => exact (RunUnivRel.not_prop hd h' (levelRel_prop_iff.1 h)).elim
    | univBelow _ _ h' =>
      exact (RunUnivRel.not_prop hd (runLevelRel_iff.1 h') (levelRel_prop_iff.1 h)).elim
    | prop => exact fun _ _ _ => .rfl
    | propBelow => exact fun _ _ _ => .rfl
termination_by structural h _ _ => h

end

/-- The relations of run time of every level are unique, in a signature whose names are
distinct. -/
theorem runLevelRel_unique {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : (runLevelRel sig ι P n).Unique :=
  have ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique := fun m _ => runLevelRel_unique hd m
  fun h h' => RunUnivRel.congr hd ih (runLevelRel_iff.1 h) _ (runLevelRel_iff.1 h')
termination_by n
decreasing_by all_goals assumption

-- ADE: `irrelevanceTerm`, in `Graded/Erasure/LogicalRelation/Irrelevance.agda`.
/-- `®(v)` is unique: two relations of run time of a type relate the same terms to the same
addresses in each heap, in a signature whose names are distinct.
RFC: `\mathsf{unique}_\circledR` -/
theorem HasRun.unique {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R R' : RunRel} (hd : sig.Distinct) :
    HasRun sig ι P v R → HasRun sig ι P v R' → ∀ H t a, R H t a ↔ R' H t a
  | .univ n h, .univ _ h' => by
    cases RunUnivRel.level hd (runLevelRel_iff.1 h) (runLevelRel_iff.1 h')
    exact runLevelRel_unique hd n h h'
  | .univ _ h, .prop _ _ h' _ => (RunUnivRel.not_prop hd (runLevelRel_iff.1 h)
      (levelRel_prop_iff.1 h')).elim
  | .prop _ _ h _, .univ _ h' => (RunUnivRel.not_prop hd (runLevelRel_iff.1 h')
      (levelRel_prop_iff.1 h)).elim
  | .prop _ _ _ hR, .prop _ _ _ hR' => fun H t a => ⟨fun _ => hR' H t a, fun _ => hR H t a⟩

/-! ## Monotonicity in the Heap

A relation of run time relates a term to an address in each heap that extends a heap in which it
relates them: the relations of the data types read the values of the heap, which every heap that
extends it keeps, by induction on their least fixed points, and those of the codata types relate
the observations in each heap that extends the heap of the closure, which a later heap extends
too. -/

/-- The relation of run time of the observations by destructors relates in a heap `H'` that extends
`H` what another relation of the same destructors relates in `H`, at relations of the recursive
destructors that relate more terms and addresses in each heap. -/
theorem RunDesRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) {H H' : Heap} (hH : H.Extends H') {D : Name} {rs₁ : Nat → Option RunRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => runLevelRel sig ι P m) D rs₁ ds @θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunObsRel),
        RunDesRel sig ι P n (fun m _ => runLevelRel sig ι P m) D rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a → y H t a) (rs₁ i) (rs₂ i)) →
        ∀ o a, S₁ H o a → S₂ H' o a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) (i := i) hi hΘ hRΘ F R hB hF hR _ hG hrs, _, _, h', hRs => by
    have ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique := fun m _ => runLevelRel_unique hd m
    have ihm : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
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
      have hRΘΘ := RunTelRel.congr hd ih hRΘ _ _ hRΘ' TelRel.none_rel
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (f := f) (H := H)
        (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := RunTelRel.fieldsRel hd hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.congr hd ih (hR ts hts' _ hv) _ (hR' ts ((hSS _ _).1 hts') _ hv)
      exact fun o a ⟨h₁, h₂, h₃⟩ =>
        ⟨(hEE _ _).1 h₁,
          fun hp => (hAA _ H' a).1 fun H'' hH'' => h₂ hp H'' (hH.trans hH''),
          RunDesRel.mono hd hH (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁)) (fun i => hRs (i + 1)) o a
            h₃⟩
    | recursive _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hi hrs hRΘ _ hG, _, _, h', hRs => by
    have ih : ∀ m, m < n → (runLevelRel sig ι P m).Unique := fun m _ => runLevelRel_unique hd m
    cases h' with
    | cons _ _ _ _ _ _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hi' hrs' hRΘ' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hRΘΘ := RunTelRel.congr hd ih hRΘ _ _ hRΘ' TelRel.none_rel
        exact fun o a ⟨h₁, h₂⟩ =>
          ⟨fun hp H'' hH'' ts bs hts =>
            have ⟨w, H''', he, hw⟩ := h₁ hp H'' (hH.trans hH'') ts bs ((hRΘΘ _ _ _).2 hts)
            ⟨w, H''', he, hr _ _ _ hw⟩,
            RunDesRel.mono hd hH (hG (.sort ⟨.type, .zero⟩)) _ _ (hG' (.sort ⟨.type, .zero⟩))
              (fun i => hRs (i + 1)) o a h₂⟩
termination_by structural h _ _ _ _ => h

mutual

/-- The relation of run time of a type of `U_n` is monotone in the heap, if those of the levels
below `n` are. -/
theorem RunUnivRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Monotone) {v : Term 0 []}
    {R : RunRel} : RunUnivRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R → R.Monotone
  | .univ _ _ => fun _ {_ _} _ => trivial
  | .prop _ _ => fun _ {_ _} _ => trivial
  | .data (decl := decl) _ _ _ _ _ _ _ S hS => fun hH {_ _} h => by
    have hstep : ∀ (X Y : Name → RunRel) {H H' : Heap}, H.Extends H' →
        (∀ D t a, X D H t a → Y D H' t a) → ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts as,
          S X c H ts as → S Y c H' ts as :=
      fun X Y {_ _} hH hXY T hT c hc => RunTelRel.mono hd ih hH (hS X T hT c hc) _ _ (hS Y T hT c hc)
        (fun _ => Option.rel_map (fun D' _ _ => RunRel.computed_mono (hXY D')) _)
    have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
        ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
      fun X Y hXY T hT c hc H =>
        hstep X Y (List.prefix_refl H) (fun D t a => hXY D H t a) T hT c hc
    exact h (fun (D : Name) (H : Heap) (t : Term 0 []) (a : Nat) => ∀ H', H.Extends H' → DataType.runBlockRel sig decl.dataTypes S D H' t a)
      (fun T hT H t a hc H' hH' => DataType.runBlockRel_fold hmono hT
        (DataType.runCtorRel_mono hH' (fun c hc ts as => hstep _ _ hH'
          (fun _ _ _ h => h H' hH') T hT c hc ts as) hc)) _ hH
  | .codata (decl := decl) _ _ _ _ _ _ _ S hS => fun hH {_ _} ⟨X, hX, hx⟩ =>
    ⟨fun (D : Name) (H' : Heap) (t : Term 0 []) (a : Nat) => ∃ H : Heap, H.Extends H' ∧ X D H t a,
      fun T hT H' t a ⟨H, hH, hx⟩ => runCorecRel_mono
        (RunDesRel.mono hd hH (hS X T hT) _ _ (hS _ T hT)
          (fun _ => Option.rel_map (fun _ H'' _ _ =>
            RunRel.computed_mono fun _ _ h => ⟨H'', List.prefix_refl H'', h⟩) _))
        (hX T hT H t a hx),
      _, hH, hx⟩
termination_by structural h => h

/-- The relation of run time of the terms of the fields of a telescope relates in a heap `H'` that
extends `H` what another relation of the same telescope relates in `H`, at relations of the
recursive fields that do so. -/
theorem RunTelRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Monotone) {H H' : Heap}
    (hH : H.Extends H') {rs₁ : Nat → Option RunRel} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => runLevelRel sig ι P m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => runLevelRel sig ι P m) rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t a, x H t a → y H' t a) (rs₁ i) (rs₂ i)) →
        ∀ ts as, S₁ H ts as → S₂ H' ts as
  | .nil, _, _, h', _ => by
    cases h'
    exact fun ts as h => match ts, as, h with
      | .nil, [], _ => trivial
  | .cons hA hF hR _ hG hrs, _, _, h', hRs => by
    cases h' with
    | cons hA' hF' hR' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd (fun m _ => levelRel_isPer hd m) hF _ _ hF'
      have hRR := RunFieldRel.congr hd (fun m _ => runLevelRel_unique hd m) hR _ hR'
      exact RunFieldsRel.cons_mono
        (fun t a ⟨htt, hr⟩ => ⟨(hFF t t).1 htt, fun hp => (hRR H' t a).1 (RunFieldRel.mono hd ih hR hH (hr hp))⟩)
        fun t _ ⟨htt, _⟩ => RunTelRel.mono hd ih hH (hG t htt) _ _ (hG' t ((hFF t t).1 htt))
          (fun i => hRs (i + 1))
    | recursive hrs' _ _ => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, h', hRs => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact RunFieldsRel.cons_mono (fun t a h hp => hr t a (h hp))
          fun t _ _ => RunTelRel.mono hd ih hH (hG t) _ _ (hG' t) (fun i => hRs (i + 1))
termination_by structural h _ _ _ _ => h

/-- The relation of run time of the type of a field is monotone in the heap. -/
theorem RunFieldRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (runLevelRel sig ι P m).Monotone) {v : Term 0 []}
    {R : RunRel} : RunFieldRel sig ι P n (fun m _ => runLevelRel sig ι P m) v R → R.Monotone
  | .univ h => fun hH => RunRel.computed_mono fun _ _ hv => RunUnivRel.mono hd ih h hH hv
  | .univBelow m hm h => fun hH => RunRel.computed_mono fun _ _ hv => ih m hm h hH hv
  | .prop _ => fun _ {_ _} _ => trivial
  | .propBelow _ _ _ => fun _ {_ _} _ => trivial
termination_by structural h => h

end

/-- The relations of run time of every level are monotone in the heap, in a signature whose names
are distinct. -/
theorem runLevelRel_mono {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : (runLevelRel sig ι P n).Monotone :=
  have ih : ∀ m, m < n → (runLevelRel sig ι P m).Monotone := fun m _ => runLevelRel_mono hd m
  fun h => RunUnivRel.mono hd ih (runLevelRel_iff.1 h)
termination_by n
decreasing_by all_goals assumption

-- ADE: none.
/-- `®(v)` is monotone in the heap, in a signature whose names are distinct. -/
theorem HasRun.mono {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R : RunRel} (hd : sig.Distinct) : HasRun sig ι P v R → R.Monotone
  | .univ n h => runLevelRel_mono hd n h
  | .prop _ _ _ hR => fun _ {_ _} _ => hR _ _ _

-- ADE: none.
/-- `t ®_H a : A` holds in each heap `H'` that extends `H`, in a signature whose names are
distinct.
RFC: `\mathsf{ext}_\circledR` -/
theorem RunsAs.mono {sig : Signature} {ι : Interpretation} {P : Program} {H H' : Heap}
    {t : Term 0 []} {a : Nat} {A : Term 0 []} (hd : sig.Distinct) (hH : H.Extends H') :
    RunsAs sig ι P H t a A → RunsAs sig ι P H' t a A :=
  fun ⟨v, R, hA, hR, ht⟩ => ⟨v, R, hA, hR, RunRel.computed_mono (fun _ _ hv => hR.mono hd hH hv) ht⟩

end Sic.Core
