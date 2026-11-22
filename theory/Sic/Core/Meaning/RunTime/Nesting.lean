module

public import Sic.Core.Meaning.RunTime.Properties
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Syntax.Signature

/-!
# Agreement of the Graph of the Nestings of Run Time

The graph of the nestings of run time of annex 21 of RFC 36 agrees with the graph of run time, at
positions that hold types with their relations of run time, on the terms that the equality of a
type relates to themselves.
The two graphs do not give a type the same relation: a position holds no equality, so that the
observation of a term by a destructor whose result has a position is related at run time alone,
while the graph of run time asks that it be one that the equality gives to the destructor.
The graph of the nestings then relates every term that the graph of run time relates, and the
graph of run time relates those of them that the equality of the type relates to themselves.

Both are proved by recursion on the clauses of the graph of the nestings, after the uniqueness of
the relations of a level: the clause of a type without position is that of the graph of run time,
the relation of a position is that of its type, which is unique and the same for the types equal
up to the values of their levels, a property of the graph of run time that is proved after this
module and that the agreement takes as a premise, and the clauses of an instance of a codata type
are those of the graph of run time, where the block has no recursive destructor.
The second reads the equality of the observations of a term from the equality of the term, which
gives the equality that the graph of run time asks of each observation.
An instance of a codata type may live below the level of the graph of the nestings that reads it,
as for the equality, and the graphs of run time of a level relate what those of a level below
relate, which the first section proves.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## The Graph at a Higher Level -/

/-- A type of a field of a sort that `U_m` bounds is one of a sort that `U_n` bounds, at a level
`n` above `m`, with the same relation of run time. -/
theorem RunFieldRel.levelLe {sig : Signature} {ι : Interpretation} {P : Program} {m n : Nat}
    (hmn : m ≤ n) {v : Term 0 []} {R : RunRel}
    (h : RunFieldRel sig ι P m (fun k _ => levelRel sig ι k) v R) :
    RunFieldRel sig ι P n (fun k _ => levelRel sig ι k) v R := by
  rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
  · exact h
  · cases h with
    | univ hu => exact .univBelow m hlt (levelRel_run_iff.2 hu)
    | univBelow k hk hu => exact .univBelow k (Nat.lt_trans hk hlt) hu
    | prop hu => exact .propBelow m hlt (levelRel_prop_iff.2 hu)
    | propBelow k hk hu => exact .propBelow k (Nat.lt_trans hk hlt) hu

mutual

/-- A telescope of run time in `U_m` is one in `U_n`, at a level `n` above `m`, with the same
relation. -/
theorem RunTelRel.levelLe {sig : Signature} {ι : Interpretation} {P : Program} {m n : Nat}
    (hmn : m ≤ n) {rs : Nat → Nest RunNestLeaf} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S : RunFieldsRel} :
    RunTelRel sig ι P m (fun k _ => levelRel sig ι k) rs Θ S →
      RunTelRel sig ι P n (fun k _ => levelRel sig ι k) rs Θ S
  | .nil => .nil
  | .cons hA hF hR G hG hrs =>
    .cons hA (hF.levelLe hmn) (hR.levelLe hmn) G (fun a ha => RunTelRel.levelLe hmn (hG a ha)) hrs
  | .nested hrs hR G hG =>
    .nested hrs (RunNestRel.levelLe hmn hR) G fun a => RunTelRel.levelLe hmn (hG a)
termination_by structural h => h

/-- A type that the graph of the nestings of run time reads at the level `m` is read at a level
`n` above `m`, with the same relation. -/
theorem RunNestRel.levelLe {sig : Signature} {ι : Interpretation} {P : Program} {m n : Nat}
    (hmn : m ≤ n) {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel} :
    RunNestRel sig ι P m (fun k _ => levelRel sig ι k) τ A R →
      RunNestRel sig ι P n (fun k _ => levelRel sig ι k) τ A R
  | .plain hA hR => .plain hA (hR.levelLe hmn)
  | .direct hA => .direct hA
  | .codata h hq hl hp hA hκ hn hrec S hS =>
    .codata h hq hl hp hA hκ (Nat.le_trans hn hmn) hrec S (RunNestDesRel.levelLe hmn hS)
  | .codataProp h hq hl hp hA hadm hκ hn hrec =>
    .codataProp h hq hl hp hA hadm hκ (Nat.le_trans hn hmn) hrec
termination_by structural h => h

/-- Destructors that the graph of the nestings of run time reads at the level `m` are read at a
level `n` above `m`, with the same relation. -/
theorem RunNestDesRel.levelLe {sig : Signature} {ι : Interpretation} {P : Program} {m n : Nat}
    (hmn : m ≤ n) {D : Name} {Γ : Scope} {ν : Nesting RunNestLeaf Γ} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : RunObsRel} :
    RunNestDesRel sig ι P m (fun k _ => levelRel sig ι k) D @ν ds @θ S →
      RunNestDesRel sig ι P n (fun k _ => levelRel sig ι k) D @ν ds @θ S
  | .nil => .nil
  | .cons hi hν hΘ hRΘ F R hF hR G hG hresp =>
    .cons hi hν (hΘ.levelLe hmn) (RunTelRel.levelLe hmn hRΘ) F R
      (fun ts hts => (hF ts hts).levelLe hmn) (fun ts hts => RunNestRel.levelLe hmn (hR ts hts)) G
      (fun f hf => RunNestDesRel.levelLe hmn (hG f hf)) hresp
  | .nested hi hν hΘ hRΘ R hR G hG =>
    .nested hi hν (hΘ.levelLe hmn) (RunTelRel.levelLe hmn hRΘ) R
      (fun ts hts => RunNestRel.levelLe hmn (hR ts hts)) G
      fun f => RunNestDesRel.levelLe hmn (hG f)
termination_by structural h => h

end

/-- Destructors of run time in `U_m` are of run time in `U_n`, at a level `n` above `m`, with the
same relation. -/
theorem RunDesRel.levelLe {sig : Signature} {ι : Interpretation} {P : Program} {m n : Nat}
    (hmn : m ≤ n) {D : Name} {rs : Nat → Option RunRel} {Γ : Scope} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : RunObsRel} :
    RunDesRel sig ι P m (fun k _ => levelRel sig ι k) D rs ds @θ S →
      RunDesRel sig ι P n (fun k _ => levelRel sig ι k) D rs ds @θ S
  | .nil => .nil
  | .cons hi hΘ hRΘ F R hB hF hR G hG hrs =>
    .cons hi (hΘ.levelLe hmn) (hRΘ.levelLe hmn) F R hB
      (fun ts hts v hv => (hF ts hts v hv).levelLe hmn)
      (fun ts hts v hv => (hR ts hts v hv).levelLe hmn) G
      (fun f hf => RunDesRel.levelLe hmn (hG f hf)) hrs
  | .recursive hi hrs hRΘ G hG =>
    .recursive hi hrs (hRΘ.levelLe hmn) G fun f => RunDesRel.levelLe hmn (hG f)

/-! ## Instances of Codata Types -/

/-- An instance of a codata type in a universe has a relation of run time by the clauses of
`rt(U_m)`, at its level `m`, which the level of the field bounds. -/
theorem RunFieldRel.codata_type {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    {R : RunRel}
    (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) (.inst D qs ls ps as) R) :
    ∃ m, m ≤ n ∧ ∃ R₀,
      RunUnivRel sig ι P m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R₀ ∧
        R = R₀.computed sig ι := by
  cases hR with
  | univ hu => exact ⟨n, Nat.le_refl n, _, hu, rfl⟩
  | univBelow m hm hu => exact ⟨m, Nat.le_of_lt hm, _, levelRel_run_iff.1 hu, rfl⟩
  | prop hu =>
    cases hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'
  | propBelow m hm hu =>
    cases levelRel_prop_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'

/-- An instance of a codata type in `Ω_n` has the relation of run time of the propositions, which
relates every term to every address. -/
theorem RunFieldRel.codata_prop {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop) {R : RunRel}
    (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) (.inst D qs ls ps as) R) :
    ∀ H t a, R H t a := by
  cases hR with
  | univ hu =>
    cases hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'
  | univBelow m hm hu =>
    cases levelRel_run_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'
  | prop _ => exact fun _ _ _ => trivial
  | propBelow _ _ _ => exact fun _ _ _ => trivial

/-! ## The Graph of the Nestings Relates What the Graph of Run Time Relates -/

mutual

/-- The graph of the nestings of run time relates a term to an address when the graph of run time
does, at positions that hold types with their relations of run time. -/
theorem RunNestRel.of_plain {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P))
    (hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R)
    {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R →
      Nest.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) τ →
      ∀ (R' : RunRel), RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R' →
        ∀ H t a, R' H t a → R H t a
  | .plain hA hR, _, _, h' => fun H t a =>
    (RunNestRel.unique hd ihm ih (.plain hA hR) _ h' H t a).2
  | .direct hA, hτ, _, h' => by
    cases hτ with
    | direct hT =>
      exact fun H t a => (RunNestRel.unique hd ihm ih (hinv _ _ _ hT hA) _ h' H t a).2
  | .codata (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hq hl hp hA hκ hn hrec _ hS,
      hτ, _, h' => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hR' =>
        cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA'
        obtain ⟨m, hm, _, hu, rfl⟩ := RunFieldRel.codata_type hd h hq hp hκ hR'
        cases hu with
        | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
        | codata h' _ _ _ hv' _ _ _ hS' =>
          obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h' hv'
          have hTn := h.2.2
          exact fun H _ a ⟨v, ht, X, hX, hx⟩ => ⟨v, ht, runCorecRel_mono (fun o a =>
            RunNestDesRel.of_plain hd ihm ih hinv hS (Nesting.ofArgs_rel₃ hνs) _ (by
              have hS'' := hS' X _ h.2.1
              simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
              rw [hTn] at hS''
              exact hS''.levelLe hm) H o a) (hTn ▸ hX _ h.2.1 H v a (hTn ▸ hx))⟩
  | .codataProp _ _ _ _ _ _ _ _ _, _, _, _ => fun _ _ _ _ => trivial
termination_by structural h _ _ _ => h

/-- The graph of the nestings of run time relates the observations by destructors to an address when
the graph of the destructors of run time does, at positions that hold types with their relations of
run time. -/
theorem RunNestDesRel.of_plain {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P))
    (hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R)
    {D : Name} {Γ : Scope} {ν : Nesting RunNestLeaf Γ} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : RunObsRel} :
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν ds @θ S →
      Nesting.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2)
        @ν →
      ∀ (S' : RunObsRel),
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D (fun _ => none) ds @θ S' →
        ∀ H o a, S' H o a → S H o a
  | .nil, _, _, h' => by cases h'; exact fun _ _ _ _ => trivial
  | .cons (ps := ps) (ψ := ψ) (ς := ς) (SΘ := SΘ) (i := i) hi _ hΘ hRΘ F R hF hR _ hG _, hν, _,
      h' => by
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' hB' hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hEE := AbstractionRel.unique_of_nestRel hd ihm hΘ hF hΘ' fun ts hts =>
        have ⟨_, hv⟩ := hB' ts hts
        .plain (sT := .type) hv (hF' ts hts _ hv)
      have hAA := RunAbstractionRel.unique_of_runNestRel (i := i) (ψ := ψ) (ς := ς) hd ihm ih hΘ hRΘ hR
        hΘ' hRΘ' fun ts hts =>
          have ⟨_, hv⟩ := hB' ts hts
          .plain hv (hR' ts hts _ hv)
      exact fun H o a ⟨h₁, h₂, h₃⟩ =>
        have h₁' := (hEE _ _).2 h₁
        ⟨h₁', fun hp => (hAA _ H a).2 (h₂ hp),
          RunNestDesRel.of_plain hd ihm ih hinv (hG _ h₁') (Nesting.lift_rel₃ hν) _ (hG' _ h₁)
            H o a h₃⟩
    | recursive _ hrs' => cases hrs'
  | .nested (ps := ps) (B := B) (SΘ := SΘ) hi _ hΘ hRΘ R hR _ hG, hν, _, h' => by
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' hB' hF' hR' _ hG' _ =>
      obtain rfl := Option.some.inj (hi.symm.trans hi')
      have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
      have hRΘΘ := RunTelRel.congr hd ihm ih hRΘ _ _ hRΘ' fun _ => .plain
      exact fun H o a ⟨h₁, h₂, h₃⟩ =>
        ⟨fun hp H₁ hH₁ ts bs hts ϖ =>
          have hts' := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H₁ _ bs
            hts
          have hts'' := (hSS _ _).1 hts'
          have ⟨_, hv⟩ := hB' ts hts''
          have ⟨w, H₂, Rc, he, hw⟩ := h₂ hp H₁ hH₁ ts bs ((hRΘΘ _ _ _).1 hts) ϖ
          ⟨w, H₂, Rc, he, RunNestRel.of_plain hd ihm ih hinv (hR ts hts')
            (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hν) B) _
            (.plain hv (hR' ts hts'' _ hv)) H₂ _ w hw⟩,
          RunNestDesRel.of_plain hd ihm ih hinv (hG _) (Nesting.lift_rel₃ hν) _ (hG' _ h₁)
            H o a h₃⟩
    | recursive _ hrs' => cases hrs'
termination_by structural h _ _ _ => h

end

/-! ## The Graph of Run Time Relates What the Equality Relates to Itself -/

mutual

/-- The graph of run time relates a term to an address when the graph of the nestings of run time
does and the equality of the type relates the term to itself, at positions that hold types with
their relations of run time. -/
theorem RunNestRel.to_plain {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P))
    (hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R)
    {sT : Quality} {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R →
      Nest.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) τ →
      ∀ (R' : RunRel), RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R' →
      ∀ (s : Quality) (E : TermRel), NestRel sig ι n (fun m _ => levelRel sig ι m) sT s .plain A E →
        ∀ H t a, E t t → R H t a → R' H t a
  | .plain hA hR, _, _, h', _, _, _ => fun H t a _ =>
    (RunNestRel.unique hd ihm ih (.plain hA hR) _ h' H t a).1
  | .direct hA, hτ, _, h', _, _, _ => by
    cases hτ with
    | direct hT =>
      exact fun H t a _ => (RunNestRel.unique hd ihm ih (hinv _ _ _ hT hA) _ h' H t a).1
  | .codata (D := D) (T := T) (qs := qs) (ls := ls) (ps := ps) (as := as) h hq hl hp hA hκ hn hrec
      S hS, hτ, _, h', _, _, hE => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hR' =>
        cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA'
        obtain ⟨m, hm, _, hu, rfl⟩ := RunFieldRel.codata_type hd h hq hp hκ hR'
        cases hE with
        | plain hA'' hF =>
          cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA''
          obtain ⟨m', hm', _, hue, rfl⟩ := FieldRel.codata_type hd h hq hp hκ hF
          cases hu with
          | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
          | codata h' _ _ _ hv' _ _ _ hS' =>
            obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h' hv'
            cases hue with
            | data h'' _ _ _ hv'' => exact (hd.inst_data_codata h'' h hv''.symm).elim
            | codata h'' _ _ _ hv'' _ _ _ hSE =>
              obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h'' hv''
              have hTn := h.2.2
              have hT := h.2.1
              have hnd := TypeDeclaration.codataTypes_nodup (hd.nodup h.1)
              exact fun H t a ⟨v, w, hv, hw, XE, hXE, hxe⟩ ⟨v', hv', hx⟩ => by
                cases Computesι.det hd hv hw
                cases Computesι.det hd hv hv'
                exact ⟨v, hv,
                  fun (N : Name) (H : Heap) (v : Term 0 []) (a : Nat) =>
                    N = D ∧ runCorecRel D S H v a ∧ XE N v v,
                  fun T' hT' H v a ⟨hN, hx, hxe⟩ => by
                    cases List.eq_of_nodup_map hnd hT hT' (hTn.trans hN.symm)
                    obtain ⟨o, ho, hs⟩ := hx
                    obtain ⟨o₁, o₂, ho₁, ho₂, hse⟩ := hXE _ hT v v hxe
                    cases ho.unique ho₁
                    cases ho.unique ho₂
                    rw [hTn]
                    exact ⟨o, ho, RunNestDesRel.to_plain hd ihm ih hinv hS
                      (Nesting.ofArgs_rel₃ hνs) _ (by
                        have hS'' := hS' (fun N H v a =>
                          N = D ∧ runCorecRel D S H v a ∧ XE N v v) _ hT
                        simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
                        rw [hTn] at hS''
                        exact hS''.levelLe hm) _ _ (by
                        have hSE'' := hSE XE _ hT
                        simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hSE''
                        exact hSE''.levelLe hm') H o a hse hs⟩,
                  rfl, hx, hxe⟩
  | .codataProp (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hq _ hp hA _ hκ _ _, hτ, _,
      h', _, _, _ => by
    subst hA
    cases h' with
    | plain hA' hR' =>
      cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA'
      exact fun H t a _ _ => RunFieldRel.codata_prop hd h hq hp hκ hR' H t a
termination_by structural h _ _ _ _ _ _ => h

/-- The graph of the destructors of run time relates the observations by destructors to an address
when the graph of the nestings of run time does and the equality of the destructors relates the
observations to themselves, at positions that hold types with their relations of run time. -/
theorem RunNestDesRel.to_plain {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ihm : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P))
    (hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R)
    {D : Name} {Γ : Scope} {ν : Nesting RunNestLeaf Γ} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : RunObsRel} :
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν ds @θ S →
      Nesting.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2)
        @ν →
      ∀ (S' : RunObsRel),
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D (fun _ => none) ds @θ S' →
      ∀ (s : Quality) (SE : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s (fun _ => none) ds @θ SE →
        ∀ H o a, SE o o → S H o a → S' H o a
  | .nil, _, _, h', _, _, _ => by cases h'; exact fun _ _ _ _ _ => trivial
  | .cons (ps := ps) (ψ := ψ) (ς := ς) (SΘ := SΘ) (i := i) hi _ hΘ hRΘ F R hF hR _ hG _, hν, _,
      h', _, _, hE => by
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' hB' hF' hR' _ hG' _ =>
      cases hE with
      | cons hΘE FE hBE hFE _ _ hGE _ _ =>
        obtain rfl := Option.some.inj (hi.symm.trans hi')
        have hEE := AbstractionRel.unique_of_nestRel hd ihm hΘ hF hΘ' fun ts hts =>
          have ⟨_, hv⟩ := hB' ts hts
          .plain (sT := .type) hv (hF' ts hts _ hv)
        have hEEE := AbstractionRel.unique_of_nestRel hd ihm hΘ hF hΘE fun ts hts =>
          have ⟨_, hv⟩ := hBE ts hts
          .plain (sT := .type) hv (hFE ts hts _ hv)
        have hAA := RunAbstractionRel.unique_of_runNestRel (i := i) (ψ := ψ) (ς := ς) hd ihm ih hΘ hRΘ hR
          hΘ' hRΘ' fun ts hts =>
            have ⟨_, hv⟩ := hB' ts hts
            .plain hv (hR' ts hts _ hv)
        exact fun H o a ⟨e₁, e₂⟩ ⟨h₁, h₂, h₃⟩ =>
          ⟨(hEE _ _).1 h₁, fun hp => (hAA _ H a).1 (h₂ hp),
            RunNestDesRel.to_plain hd ihm ih hinv (hG _ h₁) (Nesting.lift_rel₃ hν) _
              (hG' _ ((hEE _ _).1 h₁)) _ _ (hGE _ ((hEEE _ _).1 h₁)) H o a e₂ h₃⟩
      | recursive hrs' => cases hrs'
    | recursive _ hrs' => cases hrs'
  | .nested (ps := ps) (B := B) (SΘ := SΘ) hi _ hΘ hRΘ R hR _ hG, hν, _, h', _, _, hE => by
    cases h' with
    | cons hi' hΘ' hRΘ' F' R' hB' hF' hR' _ hG' _ =>
      cases hE with
      | cons hΘE FE hBE hFE _ _ hGE _ _ =>
        obtain rfl := Option.some.inj (hi.symm.trans hi')
        have hSS := TelRel.unique hd ihm hΘ _ _ hΘ'
        have hEE := AbstractionRel.unique_of_fieldRel hd ihm hΘE hBE hFE hΘ' hF'
        have hRΘΘ := RunTelRel.congr hd ihm ih hRΘ _ _ hRΘ' fun _ => .plain
        exact fun H o a ⟨e₁, e₂⟩ ⟨h₁, h₂⟩ =>
          have e₁' := (hEE _ _).1 e₁
          ⟨e₁', fun hp H₁ hH₁ ts bs hts ϖ =>
            have hts₁ := (hRΘΘ _ _ _).2 hts
            have hts' := RunTelRel.fieldsRel hd ihm hRΘ (fun _ => rfl) _ _ hΘ (fun _ => rfl) H₁ _ bs
              hts₁
            have hts'' := (hSS _ _).1 hts'
            have ⟨_, hv⟩ := hB' ts hts''
            have ⟨w, H₂, Rc, he, hw⟩ := h₁ hp H₁ hH₁ ts bs hts₁ ϖ
            ⟨w, H₂, Rc, he, RunNestRel.to_plain hd ihm ih hinv (hR ts hts')
              (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hν) B) _
              (.plain hv (hR' ts hts'' _ hv)) _ _
              (.plain (sT := .type) hv (hF' ts hts'' _ hv)) H₂ _ w
              (e₁' ts ts hts'') hw⟩,
            RunNestDesRel.to_plain hd ihm ih hinv (hG _) (Nesting.lift_rel₃ hν) _ (hG' _ e₁') _ _
              (hGE _ e₁) H o a e₂ h₂⟩
      | recursive hrs' => cases hrs'
    | recursive _ hrs' => cases hrs'
termination_by structural h _ _ _ _ _ _ => h

end

end Sic.Core
