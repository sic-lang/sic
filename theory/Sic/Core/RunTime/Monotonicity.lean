module

public import Sic.Core.Nesting.Relation
public import Sic.Core.RunTime.Relation
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Monotonicity of the Relation of Run Time

The relation of run time of annex 22 of RFC 36 is monotone in the heap: a term related to an address
in a heap stays related to it in each heap that extends it, since the relations of the data types
read only values that the heap keeps, by induction on their least fixed points, and those of the
codata types are stated in each heap that extends it.
The relation that the graph of the nestings of run time of annex 21 gives a type is monotone in the
heap too, when the relations that the nesting holds are.

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
theorem DataType.runCtorRel_mono {j g k : Nat} {Δ : Scope} {sig : Signature} {I : Instance j g}
    {D : Name} {T : DataType j g k Δ} {S S' : Constructor j g k Δ → RunFieldsRel} {H H' : Heap}
    (hH : H.Extends H') (h : ∀ c ∈ T.constructors, ∀ ts as, S c H ts as → S' c H' ts as)
    {v : Term 0 []} {a : Nat} : T.runCtorRel sig I D S H v a → T.runCtorRel sig I D S' H' v a :=
  fun ⟨c, hc, i, ts, as, hv, hi, ha, hs⟩ => ⟨c, hc, i, ts, as, hv, hi, hH.getElem? ha, h c hc ts as hs⟩

/-- The relations of run time `S X c` of the fields of the constructors `c` of the data types `Ts`
grow with the relations `X` of the recursive fields. -/
def DataType.RunBlockMono {j g k : Nat} {Δ : Scope} (Ts : List (DataType j g k Δ))
    (S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel) : Prop :=
  ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) → ∀ T ∈ Ts,
    ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as

/-- `(®_μ)` is closed under the clauses of the constructors, when the relation of the terms of the
fields grows with the relations of the recursive fields. -/
theorem DataType.runBlockRel_fold {j g k : Nat} {Δ : Scope} {sig : Signature} {I : Instance j g}
    {Ts : List (DataType j g k Δ)} {S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (hmono : DataType.RunBlockMono Ts S)
    {T : DataType j g k Δ} (hT : T ∈ Ts) {H : Heap} {v : Term 0 []} {a : Nat}
    (h : T.runCtorRel sig I T.name (S (DataType.runBlockRel sig I Ts S)) H v a) :
    DataType.runBlockRel sig I Ts S T.name H v a :=
  fun X hX => hX T hT H v a (DataType.runCtorRel_mono (List.prefix_refl H)
    (fun c hc ts as => hmono _ X (fun _ _ _ _ h => h X hX) T hT c hc H ts as) h)

/-- `(®_μ)` relates only what its clauses relate, when the relation of the terms of the fields
grows with the relations of the recursive fields: the converse of `DataType.runBlockRel_fold`. -/
theorem DataType.runBlockRel_unfold {j g k : Nat} {Δ : Scope} {sig : Signature} {I : Instance j g}
    {Ts : List (DataType j g k Δ)} {S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (hmono : DataType.RunBlockMono Ts S)
    {D : Name} {H : Heap} {v : Term 0 []} {a : Nat} (h : DataType.runBlockRel sig I Ts S D H v a) :
    ∃ T ∈ Ts, T.name = D ∧ T.runCtorRel sig I T.name (S (DataType.runBlockRel sig I Ts S)) H v a :=
  h (fun D H v a => ∃ T ∈ Ts, T.name = D ∧
      T.runCtorRel sig I T.name (S (DataType.runBlockRel sig I Ts S)) H v a)
    fun T hT H _ _ hc => ⟨T, hT, rfl, DataType.runCtorRel_mono (List.prefix_refl H)
      (fun c hc' ts as => hmono _ _ (fun _ _ _ _ ⟨_, hT', hD, hr⟩ =>
        hD ▸ DataType.runBlockRel_fold hmono hT' hr) T hT c hc' H ts as) hc⟩

/-! ## Monotonicity in the Heap

A relation of run time relates a term to an address in each heap that extends a heap in which it
relates them: the relations of the data types read the values of the heap, which every heap that
extends it keeps, by induction on their least fixed points, and those of the codata types relate
the observations in each heap that extends the heap of the closure, which a later heap extends
too.
The relation that the graph of the nestings gives a type, which the fields of a telescope read at
their nestings, is monotone when the relations of its positions are.
An observation of a value of a codata type reads the relation of its result in the heap that the
observation gives, which is not the heap of the value, so that the relations of the positions are
compared at each pair of heaps of a relation `K` between heaps, contained in the extension and
reflexive: the extension itself for the monotonicity, and the equality of the heaps for the growth
of the relation with those of the positions. -/

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
  | .cons (ps := ps) (ψ := ψ) (ς := ς) (SΘ := SΘ) (i := i) hi hΘ hRΘ F R hB hF hR
      _ hG hrs, _, _, h', hRs => by
    have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' _ hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hEE := AbstractionRel.unique_of_fieldRel hd ihm hΘ hB hF hΘ' hF'
      have hAA := RunAbstractionRel.unique_of_runFieldRel (i := i) (ψ := ψ) (ς := ς) hd ihm ih hΘ hRΘ hB
        hR hΘ' hRΘ' hR'
      exact fun o a ⟨h₁, h₂, h₃⟩ =>
        ⟨(hEE _ _).1 h₁,
          fun hp => (hAA _ H' a).1 fun H'' hH'' => h₂ hp H'' (hH.trans hH''),
          RunDesRel.mono hd hH (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁)) (fun i => hRs (i + 1)) o a
            h₃⟩
    | recursive _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hi hrs hRΘ _ hG, _, _, h', hRs => by
    have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    cases h' with
    | cons _ _ _ _ _ _ _ _ _ _ hrs' => have h0 := hRs 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hi' hrs' hRΘ' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have h0 := hRs 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hRΘΘ := RunTelRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _) ih hRΘ _ _ hRΘ'
          fun _ => .plain
        exact fun o a ⟨h₁, h₂⟩ =>
          ⟨fun hp H'' hH'' ts bs hts ϖ =>
            have ⟨w, H''', R, he, hw⟩ := h₁ hp H'' (hH.trans hH'') ts bs ((hRΘΘ _ _ _).2 hts) ϖ
            ⟨w, H''', R, he, hr _ _ _ hw⟩,
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
    have hstep : ∀ (K : Heap → Heap → Prop), (∀ {H H' : Heap}, K H H' → H.Extends H') →
        (∀ H, K H H) → ∀ (X Y : Name → RunRel),
          (∀ D H H', K H H' → ∀ t a, X D H t a → Y D H' t a) → ∀ T ∈ decl.dataTypes,
            ∀ c ∈ T.constructors, ∀ H H', K H H' → ∀ ts as, S X c H ts as → S Y c H' ts as :=
      fun K hK hKr X Y hXY T hT c hc =>
        RunTelRel.mono hd ih hK hKr (hS X T hT c hc) _ _ (hS Y T hT c hc)
          (fun _ => Nest.map_rel₃
            (fun D' H H' hH _ _ => RunRel.computed_mono (hXY D' H H' hH)) _)
    have hmono : DataType.RunBlockMono decl.dataTypes S :=
      fun X Y hXY T hT c hc H =>
        hstep Eq (fun e => e ▸ List.prefix_refl _) (fun _ => rfl) X Y
          (fun D H _ e t a => e ▸ hXY D H t a) T hT c hc H H rfl
    exact h (fun (D : Name) (H : Heap) (t : Term 0 []) (a : Nat) => ∀ H', H.Extends H' → DataType.runBlockRel sig _ decl.dataTypes S D H' t a)
      (fun T hT H t a hc H' hH' => DataType.runBlockRel_fold hmono hT
        (DataType.runCtorRel_mono hH' (fun c hc ts as => hstep Heap.Extends id List.prefix_refl
          _ _ (fun _ _ H₂ hH₂ _ _ h => h H₂ hH₂) T hT c hc H H' hH' ts as) hc)) _ hH
  | .codata (decl := decl) _ _ _ _ _ _ _ S hS => fun hH {_ _} ⟨X, hX, hx⟩ =>
    ⟨fun (D : Name) (H' : Heap) (t : Term 0 []) (a : Nat) => ∃ H : Heap, H.Extends H' ∧ X D H t a,
      fun T hT H' t a ⟨H, hH, hx⟩ => runCorecRel_mono
        (RunDesRel.mono hd hH (hS X T hT) _ _ (hS _ T hT)
          (fun _ => Option.rel_map (fun _ H'' _ _ =>
            RunRel.computed_mono fun _ _ h => ⟨H'', List.prefix_refl H'', h⟩) _))
        (hX T hT H t a hx),
      _, hH, hx⟩
termination_by structural h => h

/-- The relation of run time of the terms of the fields of a telescope relates in a heap `H'` what
another relation of the same telescope relates in a heap `H`, for the heaps that `K` relates, at
nestings of the fields whose positions have relations that do so. -/
theorem RunTelRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {K : Heap → Heap → Prop} (hK : ∀ {H H' : Heap}, K H H' → H.Extends H') (hKr : ∀ H, K H H)
    {rs₁ : Nat → Nest RunNestLeaf} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₁ Θ S₁ →
      ∀ (rs₂ : Nat → Nest RunNestLeaf) (S₂ : RunFieldsRel),
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs₂ Θ S₂ →
        (∀ i, Nest.Rel (fun x y => ∀ H H', K H H' → ∀ t a, x.2 H t a → y.2 H' t a)
          (rs₁ i) (rs₂ i)) →
        ∀ H H', K H H' → ∀ ts as, S₁ H ts as → S₂ H' ts as
  | .nil, _, _, h', _ => by
    cases h'
    exact fun _ _ _ ts as h => match ts, as, h with
      | .nil, [], _ => trivial
  | .cons hA hF hR _ hG hrs, _, _, h', hRs => by
    cases h' with
    | cons hA' hF' hR' _ hG' _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd (Nat.forall_lt (levelRel_isPer hd) _) hF _ _ hF'
      have hRR := RunFieldRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _)
        (Nat.forall_lt (levelRel_run_unique hd) _) hR _ hR'
      exact fun H H' hH => RunFieldsRel.cons_mono
        (fun t a ⟨htt, hr⟩ => ⟨(hFF t t).1 htt,
          fun hp => (hRR H' t a).1 (RunFieldRel.mono hd ih hR (hK hH) (hr hp))⟩)
        fun t _ ⟨htt, _⟩ => RunTelRel.mono hd ih hK hKr (hG t htt) _ _ (hG' t ((hFF t t).1 htt))
          (fun i => hRs (i + 1)) H H' hH
    | nested hrs' _ _ _ => exact absurd ((hRs 0).eq_plain.1.2 hrs) hrs'
  | .nested hrs hR _ hG, _, _, h', hRs => by
    cases h' with
    | cons _ _ _ _ _ hrs' => exact absurd ((hRs 0).eq_plain.1.1 hrs') hrs
    | nested hrs' hR' _ hG' =>
      exact fun H H' hH => RunFieldsRel.cons_mono
        (fun t a h hp => RunNestRel.mono hd ih hK hKr hR _ _ hR' (hRs 0) H H' hH t a (h hp))
        fun t _ _ => RunTelRel.mono hd ih hK hKr (hG t) _ _ (hG' t) (fun i => hRs (i + 1)) H H' hH
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

/-- The relation of run time that the graph of the nestings gives a type relates in a heap `H'`
what another relation of the same type relates in a heap `H`, for the heaps that `K` relates, at
positions whose relations do so. -/
theorem RunNestRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {K : Heap → Heap → Prop} (hK : ∀ {H H' : Heap}, K H H' → H.Extends H') (hKr : ∀ H, K H H)
    {τ₁ : Nest RunNestLeaf} {A : Term 0 []} {R₁ : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₁ A R₁ →
      ∀ (τ₂ : Nest RunNestLeaf) (R₂ : RunRel),
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₂ A R₂ →
        Nest.Rel (fun x y => ∀ H H', K H H' → ∀ t a, x.2 H t a → y.2 H' t a) τ₁ τ₂ →
        ∀ H H', K H H' → ∀ t a, R₁ H t a → R₂ H' t a
  | .plain hA hR, _, _, h', hτ => by
    cases hτ
    cases h' with
    | plain hA' hR' =>
      cases Computesι.det hd hA hA'
      have hRR := RunFieldRel.congr hd (Nat.forall_lt (levelRel_isPer hd) _)
        (Nat.forall_lt (levelRel_run_unique hd) _) hR _ hR'
      exact fun _ H' hH t a h => (hRR H' t a).1 (RunFieldRel.mono hd ih hR (hK hH) h)
  | .direct _, _, _, h', hτ => by
    cases hτ with
    | direct hr =>
      cases h' with
      | direct _ => exact hr
  | .codata h _ _ _ hA hκ _ _ _ hS, _, _, h', hτ => by
    cases hτ with
    | inst hνs =>
      cases h' with
      | codata h' _ _ _ hA' _ _ _ _ hS' =>
        subst hA
        obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h' hA'
        exact fun H _ hH _ _ => RunRel.computed_mono fun _ _ => runCorecRel_mono
          (RunNestDesRel.mono hd ih hK hKr hS _ _ hS' (Nesting.ofArgs_rel₃ hνs) H _ hH)
      | codataProp h' _ _ _ hA' _ hκ' =>
        subst hA
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hA'
        exact nomatch hκ.symm.trans hκ'
  | .codataProp h _ _ _ hA _ hκ _ _, _, _, h', hτ => by
    cases hτ with
    | inst hνs =>
      cases h' with
      | codata h' _ _ _ hA' hκ' =>
        subst hA
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hA'
        exact nomatch hκ.symm.trans hκ'
      | codataProp => exact fun _ _ _ _ _ _ => trivial
termination_by structural h _ _ _ _ => h

/-- The relation of run time of the observations by destructors read at nestings relates in a heap
`H'` what another relation of the same destructors relates in a heap `H`, for the heaps that `K`
relates, at positions whose relations do so. -/
theorem RunNestDesRel.mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {K : Heap → Heap → Prop} (hK : ∀ {H H' : Heap}, K H H' → H.Extends H') (hKr : ∀ H, K H H)
    {D : Name} {Γ : Scope} {ν₁ : Nesting RunNestLeaf Γ} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : RunObsRel} :
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₁ ds @θ S₁ →
      ∀ (ν₂ : Nesting RunNestLeaf Γ) (S₂ : RunObsRel),
        RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₂ ds @θ S₂ →
        Nesting.Rel (fun x y => ∀ H H', K H H' → ∀ t a, x.2 H t a → y.2 H' t a) @ν₁ @ν₂ →
        ∀ H H', K H H' → ∀ o a, S₁ H o a → S₂ H' o a
  | .nil, _, _, h', _ => by cases h'; exact fun _ _ _ _ _ _ => trivial
  | .cons (ps := ps) (B := B) (ψ := ψ) (ς := ς) (SΘ := SΘ) (i := i) hi hν hΘ hRΘ F R hF hR _ hG _,
      _, _, h', hτ => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hτ) B
    cases h' with
    | cons hi' _ hΘ' hRΘ' F' R' hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hEE := AbstractionRel.unique_of_nestRel hd ihm hΘ hF hΘ' hF'
      have hAA := RunAbstractionRel.unique_of_runNestRel (i := i) (ψ := ψ) (ς := ς) hd ihm ihu hΘ hRΘ hR
        hΘ' hRΘ' hR'
      exact fun H H' hH o a ⟨h₁, h₂, h₃⟩ =>
        ⟨(hEE _ _).1 h₁,
          fun hp => (hAA _ H' a).1 fun H₁ hH₁ => h₂ hp H₁ ((hK hH).trans hH₁),
          RunNestDesRel.mono hd ih hK hKr (hG _ h₁) _ _ (hG' _ ((hEE _ _).1 h₁))
            (Nesting.lift_rel₃ hτ) H H' hH o a h₃⟩
    | nested _ hν' => exact absurd (hB.eq_plain.1.2 hν) hν'
  | .nested (ps := ps) (B := B) (SΘ := SΘ) hi hν hΘ hRΘ R hR _ hG, _, _, h', hτ => by
    have ihu : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      Nat.forall_lt (levelRel_run_unique hd) _
    have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hτ) B
    cases h' with
    | cons _ hν' => exact absurd (hB.eq_plain.1.1 hν') hν
    | nested hi' _ hΘ' hRΘ' R' hR' _ hG' =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hRΘΘ := RunTelRel.congr hd ihm ihu hRΘ _ _ hRΘ' fun _ => .plain
      exact fun H H' hH o a ⟨h₁, h₂⟩ =>
        ⟨fun hp H₁ hH₁ ts bs hts ϖ =>
          have hts₁ := (hRΘΘ _ _ _).2 hts
          have hts' := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H₁ _ bs
            hts₁
          have ⟨w, H₂, Rc, he, hw⟩ := h₁ hp H₁ ((hK hH).trans hH₁) ts bs hts₁ ϖ
          ⟨w, H₂, Rc, he, RunNestRel.mono hd ih hK hKr (hR ts hts') _ _
            (hR' ts ((hSS _ _).1 hts')) hB H₂ H₂ (hKr H₂) _ _ hw⟩,
          RunNestDesRel.mono hd ih hK hKr (hG (.sort ⟨.type, .zero⟩)) _ _
            (hG' (.sort ⟨.type, .zero⟩)) (Nesting.lift_rel₃ hτ) H H' hH o a h₂⟩
termination_by structural h _ _ _ _ => h

end

/-- The relation of run time of the terms of the fields of the constructors of a block, at
relations `F X D` of the instances of its types `D` at the positions of the nestings of its fields,
grows with `X` when they do, in one heap: the premise of `DataType.runBlockRel_fold` and
`DataType.runBlockRel_unfold`, the properties of `(®_μ)`. -/
theorem RunTelRel.block_mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {j g k : Nat} {Δ : Scope} {α : Type} {Ts : List (DataType j g k Δ)}
    {rec : Constructor j g k Δ → Nat → Nest Name}
    {Θ : Constructor j g k Δ → (ps : List Parameter) × Telescope 0 [] ps}
    {F : α → Name → RunNestLeaf} {S : α → Constructor j g k Δ → RunFieldsRel}
    (hS : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, RunTelRel sig ι P n (fun m _ => levelRel sig ι m)
      (fun i => (rec c i).map (F X)) (Θ c).2 (S X c))
    (X Y : α) (hXY : ∀ D H t a, (F X D).2 H t a → (F Y D).2 H t a) (T : DataType j g k Δ)
    (hT : T ∈ Ts) (c : Constructor j g k Δ) (hc : c ∈ T.constructors) (H : Heap)
    (ts : Terms 0 []) (as : List Nat) :
    S X c H ts as → S Y c H ts as :=
  RunTelRel.mono hd ih (K := Eq) (fun e => e ▸ List.prefix_refl _) (fun _ => rfl)
    (hS X T hT c hc) _ _ (hS Y T hT c hc)
    (fun _ => Nest.map_rel₃ (fun D H _ e _ _ => e ▸ hXY D H _ _) _) H H rfl ts as

/-- The relations of run time of the fields of the constructors of a block, graphs of telescopes
whose recursive fields, at the instances `inst D`, have the relations computed from the relations
`X`, grow with these relations. -/
theorem DataType.RunBlockMono.of_runTelRel {sig : Signature} {ι : Interpretation} {P : Program}
    {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
    {rec : Constructor j g k Δ → Nat → Nest Name}
    {Θ : Constructor j g k Δ → (ps : List Parameter) × Telescope 0 [] ps} {inst : Name → Term 0 []}
    {S : (Name → RunRel) → Constructor j g k Δ → RunFieldsRel}
    (hS : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, RunTelRel sig ι P n (fun m _ => levelRel sig ι m)
      (fun i => (rec c i).map fun D => (inst D, (X D).computed sig ι)) (Θ c).2 (S X c)) :
    DataType.RunBlockMono Ts S := fun X Y hXY =>
  RunTelRel.block_mono hd ih (F := fun X D => (inst D, (X D).computed sig ι)) hS X Y
    fun D H _ _ => RunRel.computed_mono (hXY D H)

/-- The relations of run time of every level are monotone in the heap, in a signature whose names
are distinct. -/
theorem levelRel_run_mono {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : RunLevelRel.Monotone ((levelRel sig ι n).run P) :=
  have ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
  fun h => RunUnivRel.mono hd ih (levelRel_run_iff.1 h)
termination_by n
decreasing_by all_goals assumption

/-! ## Monotonicity at a Nesting

The relation of run time that the graph of the nestings gives a type is monotone in the heap when
the relations of its positions are, the relation `K` being the extension of the heaps. -/

/-- The relation of run time that the graph of the nestings gives a type is monotone in the heap, at
positions whose relations are. -/
theorem RunNestRel.monotone {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → RunLevelRel.Monotone ((levelRel sig ι m).run P))
    {τ : Nest RunNestLeaf} (hτ : Nest.All (fun x => x.2.Monotone) τ) {A : Term 0 []} {R : RunRel}
    (h : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R) : R.Monotone :=
  fun {_ _} hH {_ _} hr => RunNestRel.mono hd ih (K := Heap.Extends) id List.prefix_refl h _ _ h
    (hτ.rel₃ fun _ hx => by intro _ _ hH _ _ h; exact hx hH h) _ _ hH _ _ hr

/-- `rt(U_n)[λ]` gives a type a relation of run time that is monotone in the heap, when the
relations that the nesting holds are, in a signature whose names are distinct.
RFC: `\mathsf{ext}_{\circledR\lambda}` -/
theorem levelRel_runNest_mono {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel} (hd : sig.Distinct)
    (h : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (hτ : Nest.All (fun x => x.2.Monotone) τ) : R.Monotone :=
  RunNestRel.monotone hd (Nat.forall_lt (levelRel_run_mono hd) _) hτ h

/-- `®(v)` is monotone in the heap, in a signature whose names are distinct. -/
theorem HasRun.mono {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R : RunRel} (hd : sig.Distinct) : HasRun sig ι P v R → R.Monotone
  | .univ n h => levelRel_run_mono hd n h
  | .prop _ _ _ hR => fun _ {_ _} _ => hR _ _ _

/-- `t ®_H a : A` holds in each heap `H'` that extends `H`, in a signature whose names are
distinct.
RFC: `\mathsf{ext}_\circledR` -/
theorem RunsAs.mono {sig : Signature} {ι : Interpretation} {P : Program} {H H' : Heap}
    {t : Term 0 []} {a : Nat} {A : Term 0 []} (hd : sig.Distinct) (hH : H.Extends H') :
    RunsAs sig ι P H t a A → RunsAs sig ι P H' t a A
  | ⟨v, hA, .inl hp⟩ => ⟨v, hA, .inl hp⟩
  | ⟨v, hA, .inr ⟨R, hR, ht⟩⟩ =>
    ⟨v, hA, .inr ⟨R, hR, RunRel.computed_mono (fun _ _ hv => hR.mono hd hH hv) ht⟩⟩

/-- Addresses that stand for a substitution in the heap `H` stand for it in each heap `H'` that
extends `H`, in a signature whose names are distinct. -/
theorem RunsAsSubst.mono {sig : Signature} {ι : Interpretation} {P : Program} {H H' : Heap}
    (hd : sig.Distinct) (hH : H.Extends H') :
    {Γ : Scope} → (ctx : Context 0 Γ) → {γ : GradeVector Γ.length} → {σ : Subst 0 [] Γ} →
    {E : List Nat} → RunsAsSubst sig ι P H ctx γ σ E → RunsAsSubst sig ι P H' ctx γ σ E
  | _, .empty, _, _, _, h => h
  | _, .var ctx _, _, _, _, h => by
    obtain ⟨a, E', hE, hs, hx⟩ := h
    exact ⟨a, E', hE, RunsAsSubst.mono hd hH ctx hs, fun hγ => (hx hγ).mono hd hH⟩
  | _, .secondOrder .., _, _, _, h => h

/-- Arguments related to addresses at a telescope in the heap `H` are related to them in each heap
`H'` that extends `H`, in a signature whose names are distinct. -/
theorem RunsAsArgs.mono {sig : Signature} {ι : Interpretation} {P : Program} {H H' : Heap}
    (hd : sig.Distinct) (hH : H.Extends H') :
    {ps : List Parameter} → {g : Nat → Grade} → {ts : Args 0 [] ps} → {bs : List Nat} →
    {Θ : Telescope 0 [] ps} → RunsAsArgs sig ι P H g ts bs Θ → RunsAsArgs sig ι P H' g ts bs Θ
  | [], _, .nil, [], .nil, h => h
  | _ :: _, _, .cons _ _, _ :: _, .cons _ _ _ _, h => by
    obtain ⟨ht, hts⟩ := h
    exact ⟨fun hp => (ht hp).mono hd hH, RunsAsArgs.mono hd hH hts⟩

end Sic.Core
