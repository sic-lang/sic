module

public import Sic.Core.Meaning
public import Sic.Core.Nesting.Relation
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness.Levels
import Sic.Core.Syntax.Signature

/-!
# Agreement of the Graph of the Nestings

The graph of the nestings of annex 21 of RFC 36 agrees with the graph of the types: at positions
that hold types with the equality of their terms, it gives a type the equality that the graph of the
types gives it, when this graph gives it one.
The graph of the types need not give one: the graph of the nestings takes the relation of a position
whatever the type that the position holds and whatever its level, which the formation of a
declaration checks, and only asks that the position be read in a sort of the quality of the sorts
of the types at the positions.

The agreement is proved by recursion on the clauses of the graph of the nestings, after the
properties of the relations of a level, which it reads: the clause of a type without position is
that of the graph of the types, the relation of a position is the equality of its type, which is
unique and the same for the types equal up to the values of their levels, a property of the graph
of the types that `Sic.Core.Meaning.Uniqueness.Levels` proves, and the clauses of an instance of a
codata type are those of the graph of the types, where the block has no recursive destructor.
An instance of a codata type may live below the level of the graph of the nestings that reads it,
while the graph of the types reads it at its own level: the graphs of a level relate what those of
a level below relate, which the first section proves.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## The Graph at a Higher Level -/

/-- A type of a field of a sort that the sort of the quality `s` at the level `m` bounds is one of
a sort that the sort at a level `n` above `m` bounds. -/
theorem FieldRel.levelLe {sig : Signature} {ι : Interpretation} {m n : Nat} (hmn : m ≤ n)
    {s : Quality} {v : Term 0 []} {F : TermRel}
    (h : FieldRel sig ι m (fun k _ => levelRel sig ι k) s v F) :
    FieldRel sig ι n (fun k _ => levelRel sig ι k) s v F := by
  rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
  · exact h
  · cases h with
    | univ hs hu => exact .univBelow hs m hlt (levelRel_univ_iff.2 hu)
    | univBelow hs k hk hu => exact .univBelow hs k (Nat.lt_trans hk hlt) hu
    | prop hu => exact .propBelow m hlt (levelRel_prop_iff.2 hu)
    | propBelow k hk hu => exact .propBelow k (Nat.lt_trans hk hlt) hu

mutual

/-- A telescope in the sort of the quality `s` at the level `m` is one in the sort at a level `n`
above `m`, with the same equality. -/
theorem TelRel.levelLe {sig : Signature} {ι : Interpretation} {m n : Nat} (hmn : m ≤ n)
    {s : Quality} {rs : Nat → Nest NestLeaf} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S : FieldsRel} :
    TelRel sig ι m (fun k _ => levelRel sig ι k) s rs Θ S →
      TelRel sig ι n (fun k _ => levelRel sig ι k) s rs Θ S
  | .nil => .nil
  | .cons hA hF G hG hresp hrs =>
    .cons hA (hF.levelLe hmn) G (fun a ha => TelRel.levelLe hmn (hG a ha)) hresp hrs
  | .nested hrs hF G hG =>
    .nested hrs (NestRel.levelLe hmn hF) G fun a => TelRel.levelLe hmn (hG a)
termination_by structural h => h

/-- A type that the graph of the nestings reads at the level `m` is read at a level `n` above
`m`, with the same equality. -/
theorem NestRel.levelLe {sig : Signature} {ι : Interpretation} {m n : Nat} (hmn : m ≤ n)
    {sT s : Quality} {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel} :
    NestRel sig ι m (fun k _ => levelRel sig ι k) sT s τ A F →
      NestRel sig ι n (fun k _ => levelRel sig ι k) sT s τ A F
  | .plain hA hF => .plain hA (hF.levelLe hmn)
  | .direct hs hA => .direct hs hA
  | .codata h hqp hl hA hs hκ hn hrec S hS =>
    .codata h hqp hl hA hs hκ (Nat.le_trans hn hmn) hrec S (NestDesRel.levelLe hmn hS)
  | .codataProp h hqp hl hA hκ hn hrec S hS =>
    .codataProp h hqp hl hA hκ (Nat.le_trans hn hmn) hrec S (NestDesRel.levelLe hmn hS)
termination_by structural h => h

/-- Destructors that the graph of the nestings reads at the level `m` are read at a level `n`
above `m`, with the same equality. -/
theorem NestDesRel.levelLe {sig : Signature} {ι : Interpretation} {m n : Nat} (hmn : m ≤ n)
    {sT s : Quality} {Γ : Scope} {ν : Nesting NestLeaf Γ} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S : ObsRel} :
    NestDesRel sig ι m (fun k _ => levelRel sig ι k) sT s @ν ds @θ S →
      NestDesRel sig ι n (fun k _ => levelRel sig ι k) sT s @ν ds @θ S
  | .nil => .nil
  | .cons hν hΘ F hF hBresp G hG hresp =>
    .cons hν (TelRel.levelLe hmn hΘ) F (fun ts hts => NestRel.levelLe hmn (hF ts hts)) hBresp G
      (fun f hf => NestDesRel.levelLe hmn (hG f hf)) hresp
  | .nested hν hΘ F hF hBresp G hG =>
    .nested hν (TelRel.levelLe hmn hΘ) F (fun ts hts => NestRel.levelLe hmn (hF ts hts)) hBresp G
      fun f => NestDesRel.levelLe hmn (hG f)
termination_by structural h => h

end

/-- Destructors in the sort of the quality `s` at the level `m` are in the sort at a level `n`
above `m`, with the same equality. -/
theorem DesRel.levelLe {sig : Signature} {ι : Interpretation} {m n : Nat} (hmn : m ≤ n)
    {s : Quality} {rs : Nat → Option TermRel} {Γ : Scope} {ns : List Name}
    {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel} :
    DesRel sig ι m (fun k _ => levelRel sig ι k) s rs ds @θ S →
      DesRel sig ι n (fun k _ => levelRel sig ι k) s rs ds @θ S
  | .nil => .nil
  | .cons hΘ F hB hF hBresp G hG hresp hrs =>
    .cons (hΘ.levelLe hmn) F hB (fun ts hts v hv => (hF ts hts v hv).levelLe hmn) hBresp G
      (fun f hf => DesRel.levelLe hmn (hG f hf)) hresp hrs
  | .recursive hrs hΘ G hG =>
    .recursive hrs (hΘ.levelLe hmn) G fun f => DesRel.levelLe hmn (hG f)

/-! ## Agreement -/

/-- An instance of a codata type in a universe is a type of a field by the clauses of `ty(U_m)`,
at its level `m`, which the level of the field bounds. -/
theorem FieldRel.codata_type {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hκ : (decl.sort hqp.inst).quality = .type)
    {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ∃ m, m ≤ n ∧ ∃ R, UnivRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R ∧
      F = R.computed sig ι := by
  cases hF with
  | univ _ hu => exact ⟨n, Nat.le_refl n, _, hu, rfl⟩
  | univBelow _ m hm hu => exact ⟨m, Nat.le_of_lt hm, _, levelRel_univ_iff.1 hu, rfl⟩
  | prop hu =>
    cases hu with
    | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'
  | propBelow m hm hu =>
    cases levelRel_prop_iff.1 hu with
    | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'

/-- An instance of a codata type in a universe of propositions is a type of a field by the clauses
of `ty(Ω_m)`, at its level `m`, which the level of the field bounds. -/
theorem FieldRel.codata_prop {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hκ : (decl.sort hqp.inst).quality = .prop)
    {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ∃ m, m ≤ n ∧ ∃ b, PropRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) b ∧
      F = fun _ _ => b := by
  cases hF with
  | prop hu => exact ⟨n, Nat.le_refl n, _, hu, rfl⟩
  | propBelow m hm hu => exact ⟨m, Nat.le_of_lt hm, _, levelRel_prop_iff.1 hu, rfl⟩
  | univ _ hu =>
    cases hu with
    | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'
  | univBelow _ m hm hu =>
    cases levelRel_univ_iff.1 hu with
    | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ hv' hs' =>
      obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
      exact nomatch hκ.symm.trans hs'

mutual

/-- The graph of the nestings gives a type the equality that the graph of the types gives it, at
positions that hold types with the equality of their terms. -/
theorem NestRel.agree {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer)
    {sT sT' s : Quality} {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F →
      Nest.All
        (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) τ →
      ∀ (s' : Quality) (F' : TermRel),
        NestRel sig ι n (fun m _ => levelRel sig ι m) sT' s' .plain A F' →
        ∀ t u, F t u ↔ F' t u
  | .plain hA hF, _, _, _, h' => NestRel.unique hd ih (.plain (sT := sT) hA hF) _ _ h'
  | .direct _ hA, hτ, _, _, h' => by
    cases hτ with
    | direct hT =>
      exact NestRel.unique hd ih
        (NestRel.levelEquiv hd (levelRel_levelInvariant_lt hd _) hT hA .plain) _ _ h'
  | .codata (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hqp hl hA _ hκ hn hrec _ hS,
      hτ, _, _, h' => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hF' =>
        cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA'
        obtain ⟨m, hm, _, hu, rfl⟩ := FieldRel.codata_type hd h hqp hκ hF'
        cases hu with
        | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
        | codata h' _ _ hv' _ _ _ hS' =>
          obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h' hv'
          obtain ⟨hdecl, hT, rfl⟩ := h
          exact TermRel.computed_congr fun v w => ((CodataType.blockRel_iff_corecRel
            (TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)) hT fun X o₁ o₂ =>
              (NestDesRel.agree hd ih hS (Nesting.ofArgs_rel₃ hνs) _ _ (by
                have hS'' := hS' X _ hT
                simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
                exact hS''.levelLe hm) o₁ o₂).symm) v w).symm
  | .codataProp (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hqp hl hA hκ hn hrec _ hS,
      hτ, _, _, h' => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hF' =>
        cases Computesι.det hd (Whnf.inst D qs ls ps as).computes hA'
        obtain ⟨m, hm, _, hu, rfl⟩ := FieldRel.codata_prop hd h hqp hκ hF'
        cases hu with
        | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
        | codata h' _ _ hv' _ _ _ hS' =>
          obtain ⟨rfl, rfl, ⟨⟩, rfl, rfl, rfl, ⟨⟩⟩ := hd.codataInst_unique h h' hv'
          obtain ⟨hdecl, hT, rfl⟩ := h
          exact fun _ _ => (CodataType.blockTruth_iff_truth
            (TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)) hT fun B o₁ o₂ =>
              (NestDesRel.agree hd ih hS (Nesting.ofArgs_rel₃ hνs) _ _ (by
                have hS'' := hS' B _ hT
                simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
                exact hS''.levelLe hm) o₁ o₂).symm).symm
termination_by structural h _ _ _ _ => h

/-- The graph of the nestings gives destructors the equality that the graph of the destructors
gives them, at positions that hold types with the equality of their terms. -/
theorem NestDesRel.agree {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer)
    {sT s : Quality} {Γ : Scope}
    {ν : Nesting NestLeaf Γ} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ}
    {S : ObsRel} :
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν ds @θ S →
      Nesting.All
        (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .type .plain x.1 x.2) @ν →
      ∀ (s' : Quality) (S' : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s' (fun _ => none) ds @θ S' →
        ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂
  | .nil, _, _, _, h' => by cases h'; exact fun _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) _ hΘ F hF hBresp _ hG _, hν, _, _, h' => by
    have hSΘp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    have hEp := AbstractionRel.isPer hSΘp (fun ts hts => NestRel.isPer hd ih .plain (hF ts hts))
      hBresp
    cases h' with
    | cons hΘ' F' hB' hF' _ _ hG' _ _ =>
      have hEE := AbstractionRel.unique_of_agree hd ih hΘ hΘ' fun ts hts hts' =>
        have ⟨_, hv⟩ := hB' ts hts'
        NestRel.agree hd ih (hF ts hts) .plain _ _ (.plain (sT := .type) hv (hF' ts hts' _ hv))
      exact ObsRel.cons_congr hEp hEE fun f hf =>
        NestDesRel.agree hd ih (hG f hf) (Nesting.lift_rel₃ hν) _ _ (hG' f ((hEE f f).1 hf))
    | recursive hrs' => cases hrs'
  | .nested (ps := ps) (B := B) (SΘ := SΘ) _ hΘ F hF _ _ hG, hν, _, _, h' => by
    cases h' with
    | cons hΘ' F' hB' hF' hBresp' _ hG' _ _ =>
      have hSΘp' := TelRel.isPer hd ih (fun _ => .plain) hΘ'
      have hEE := AbstractionRel.unique_of_agree hd ih hΘ hΘ' fun ts hts hts' =>
        have ⟨_, hv⟩ := hB' ts hts'
        NestRel.agree hd ih (hF ts hts) (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hν) B) _ _
          (.plain (sT := .type) hv (hF' ts hts' _ hv))
      have hEp' := AbstractionRel.isPer hSΘp'
        (fun ts hts => have ⟨_, hv⟩ := hB' ts hts; FieldRel.isPer hd ih (hF' ts hts _ hv)) hBresp'
      have hGG : ∀ f, AbstractionRel _ F' f f → ∀ o₁ o₂, _ ↔ _ := fun f hf =>
        NestDesRel.agree hd ih (hG f) (Nesting.lift_rel₃ hν) _ _ (hG' f hf)
      exact fun o₁ o₂ =>
        ⟨fun ⟨h₁, h₂⟩ =>
          have h₁' := (hEE _ _).1 h₁
          ⟨h₁', (hGG _ (hEp'.left h₁') o₁ o₂).1 h₂⟩,
        fun ⟨h₁', h₂'⟩ =>
          ⟨(hEE _ _).2 h₁', (hGG _ (hEp'.left h₁') o₁ o₂).2 h₂'⟩⟩
    | recursive hrs' => cases hrs'
termination_by structural h _ _ _ _ => h

end

end Sic.Core
