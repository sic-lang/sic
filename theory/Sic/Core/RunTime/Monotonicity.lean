module

public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness

/-!
# Monotonicity of the Relation of Run Time

The relation of run time of annex 20 of RFC 36 is monotone in the heap: a term related to an address
in a heap stays related to it in each heap that extends it, since the relations of the data types
read only values that the heap keeps, by induction on their least fixed points, and those of the
codata types are stated in each heap that extends it.

ADE have no heap in their target language, so that they have no monotonicity.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- A relation of run time is monotone in the heap: it relates a term to an address in each heap
that extends a heap in which it relates them. -/
abbrev RunRel.Monotone (R : RunRel) : Prop :=
  ∀ {H H' : Heap}, H.Extends H' → ∀ {t : Term 0 []} {a : Nat}, R H t a → R H' t a

/-- The relations of run time of the types of a level are monotone in the heap. -/
abbrev RunLevelRel.Monotone (L : RunLevelRel) : Prop :=
  ∀ {v : Term 0 []} {R : RunRel}, L v R → R.Monotone

/-- `®⇓(R₂)` relates in a heap `H'` what `®⇓(R₁)` relates in a heap `H`, when `R₂` relates so the
canonical terms that `R₁` relates. -/
theorem RunRel.computed_mono {sig : Signature} {ι : Interpretation} {R₁ R₂ : RunRel} {H H' : Heap}
    (h : ∀ v a, R₁ H v a → R₂ H' v a) {t : Term 0 []} {a : Nat} :
    R₁.computed sig ι H t a → R₂.computed sig ι H' t a :=
  fun ⟨v, ht, hv⟩ => ⟨v, ht, h v a hv⟩

/-- The relation of run time of the terms of the fields of a telescope `x : A, Θ` relates in a heap
`H'` what another relates in a heap `H`, when the relations of `A` do so, and those of `Θ[a / x]` do
so for each term `a` that the first relates. -/
theorem RunFieldsRel.cons_mono {F F' : RunRel} {G G' : Term 0 [] → RunFieldsRel} {H H' : Heap}
    (hF : ∀ t a, F H t a → F' H' t a)
    (hG : ∀ t a, F H t a → ∀ ts as, G t H ts as → G' t H' ts as) :
    ∀ ts as, RunFieldsRel.cons F G H ts as → RunFieldsRel.cons F' G' H' ts as
  | .cons t ts, a :: as, ⟨h₁, h₂⟩ => ⟨hF t a h₁, hG t a h₁ ts as h₂⟩

/-- `(®_c)` relates in a heap `H'` that extends `H` what it relates in `H`, at relations of the
terms of the fields that do so. -/
theorem DataType.runCtorRel_mono {j g k : Nat} {Δ : Scope} {sig : Signature} {D : Name}
    {T : DataType j g k Δ} {S S' : Constructor j g k Δ → RunFieldsRel} {H H' : Heap}
    (hH : H.Extends H') (h : ∀ c ∈ T.constructors, ∀ ts as, S c H ts as → S' c H' ts as)
    {v : Term 0 []} {a : Nat} : T.runCtorRel sig D S H v a → T.runCtorRel sig D S' H' v a :=
  fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ => ⟨c, hc, i, ts, as, hv, hi, hH.getElem? ha, h c hc ts as hs⟩

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
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₁ ds @θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunObsRel),
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ H t a, x H t a → y H t a) (rs₁ i) (rs₂ i)) →
        ∀ o a, S₁ H o a → S₂ H' o a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) (i := i) hi hΘ hRΘ F R hB hF hR _ hG hrs, _, _, h', hRs => by
    have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
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
      have hRΘΘ := RunTelRel.congr hd (fun m _ => levelRel_isPer hd m) ih hRΘ _ _ hRΘ' TelRel.none_rel
      have hAA := fun f H a => RunAbstractionRel.congr (P := P) (ps := ps) (i := i) (f := f) (H := H)
        (a := a) (F := R) (F' := R') hRΘΘ fun H ts bs hts =>
          have hts' := RunTelRel.fieldsRel hd (fun m _ => levelRel_isPer hd m) hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H _ bs hts
          have ⟨_, hv⟩ := hB ts hts'
          RunFieldRel.congr hd (fun m _ => levelRel_isPer hd m) ih (hR ts hts' _ hv) _ (hR' ts ((hSS _ _).1 hts') _ hv)
      exact fun o a ⟨h₁, h₂, h₃⟩ =>
        ⟨(hEE _ _).1 h₁,
          fun hp => (hAA _ H' a).1 fun H'' hH'' => h₂ hp H'' (hH.trans hH''),
          RunDesRel.mono hd hH (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁)) (fun i => hRs (i + 1)) o a
            h₃⟩
    | recursive _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hi hrs hRΘ _ hG, _, _, h', hRs => by
    have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
    cases h' with
    | cons _ _ _ _ _ _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hi' hrs' hRΘ' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hRΘΘ := RunTelRel.congr hd (fun m _ => levelRel_isPer hd m) ih hRΘ _ _ hRΘ' TelRel.none_rel
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
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P)) {v : Term 0 []}
    {R : RunRel} : RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R → R.Monotone
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
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P)) {H H' : Heap}
    (hH : H.Extends H') {rs₁ : Nat → Option RunRel} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Option RunRel) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₂ Θ S₂ →
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
      have hRR := RunFieldRel.congr hd (fun m _ => levelRel_isPer hd m) (fun m _ => levelRel_run_unique hd m) hR _ hR'
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
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P)) {v : Term 0 []}
    {R : RunRel} : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R → R.Monotone
  | .univ h => fun hH => RunRel.computed_mono fun _ _ hv => RunUnivRel.mono hd ih h hH hv
  | .univBelow m hm h => fun hH => RunRel.computed_mono fun _ _ hv => ih m hm h hH hv
  | .prop _ => fun _ {_ _} _ => trivial
  | .propBelow _ _ _ => fun _ {_ _} _ => trivial
termination_by structural h => h

end

/-- The relations of run time of every level are monotone in the heap, in a signature whose names
are distinct. -/
theorem levelRel_run_mono {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : RunLevelRel.Monotone ((levelRel sig ι n).run P) :=
  have ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
  fun h => RunUnivRel.mono hd ih (levelRel_run_iff.1 h)
termination_by n
decreasing_by all_goals assumption

-- ADE: none.
/-- `®(v)` is monotone in the heap, in a signature whose names are distinct. -/
theorem HasRun.mono {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R : RunRel} (hd : sig.Distinct) : HasRun sig ι P v R → R.Monotone
  | .univ n h => levelRel_run_mono hd n h
  | .prop _ _ _ hR => fun _ {_ _} _ => hR _ _ _

-- ADE: none.
/-- `t ®_H a : A` holds in each heap `H'` that extends `H`, in a signature whose names are
distinct.
RFC: `\mathsf{ext}_\circledR` -/
theorem RunsAs.mono {sig : Signature} {ι : Interpretation} {P : Program} {H H' : Heap}
    {t : Term 0 []} {a : Nat} {A : Term 0 []} (hd : sig.Distinct) (hH : H.Extends H') :
    RunsAs sig ι P H t a A → RunsAs sig ι P H' t a A
  | ⟨v, hA, .inl hp⟩ => ⟨v, hA, .inl hp⟩
  | ⟨v, hA, .inr ⟨R, hR, ht⟩⟩ =>
    ⟨v, hA, .inr ⟨R, hR, RunRel.computed_mono (fun _ _ hv => hR.mono hd hH hv) ht⟩⟩

end Sic.Core
