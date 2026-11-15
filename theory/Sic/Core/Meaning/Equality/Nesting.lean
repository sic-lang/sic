module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Syntax.Signature

/-!
# Agreement of the Graph of the Nestings

The graph of the nestings of annex 18 of RFC 36 agrees with the graph of the types: at positions
that hold types with the equality of their terms, it gives a type the equality that the graph of the
types gives it, when this graph gives it one.
The graph of the types need not give one: the graph of the nestings takes the relation of a position
whatever the sort that bounds its type, which the formation of a declaration checks, while a
proposition has no destructor whose result is a type of a universe.

The agreement is proved by recursion on the clauses of the graph of the nestings, after the
properties of the relations of a level, which it reads: the clause of a type without position is
that of the graph of the types, the relation of a position is the equality of its type, which is
unique and the same for the types equal up to the values of their levels, a property of the graph
of the types that is proved after this module and that the agreement takes as a premise, and the clauses of an instance of a codata type are those of the graph of the types, where
the block has no recursive destructor.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- An instance of a codata type in `U_n` is a type of a field by the clauses of `ty(U_n)` alone. -/
theorem FieldRel.codata_type {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
    {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ∃ R, UnivRel sig ι n (fun m _ => levelRel sig ι m) (.inst D qs ls ps as) R ∧
      F = R.computed sig ι := by
  cases hF with
  | univ _ hu => exact ⟨_, hu, rfl⟩
  | univBelow _ m hm hu =>
    cases levelRel_univ_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact absurd (hn.symm.trans hn') (by omega)
  | prop hu =>
    cases hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hκ.symm.trans hs'
  | propBelow m hm hu =>
    cases levelRel_prop_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hκ.symm.trans hs'

/-- An instance of a codata type in `Ω_n` is a type of a field by the clauses of `ty(Ω_n)` alone. -/
theorem FieldRel.codata_prop {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop)
    (hn : ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n)
    {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ∃ b, PropRel sig ι n (fun m _ => levelRel sig ι m) (.inst D qs ls ps as) b ∧
      F = fun _ _ => b := by
  cases hF with
  | prop hu => exact ⟨_, hu, rfl⟩
  | propBelow m hm hu =>
    cases levelRel_prop_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact absurd (hn.symm.trans hn') (by omega)
  | univ _ hu =>
    cases hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hκ.symm.trans hs'
  | univBelow _ m hm hu =>
    cases levelRel_univ_iff.1 hu with
    | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hκ.symm.trans hs'

mutual

/-- The graph of the nestings gives a type the equality that the graph of the types gives it, at
positions that hold types with the equality of their terms. -/
theorem NestRel.agree {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (hinv : ∀ (T A : Term 0 []) (R : TermRel),
      NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain T R → Term.LevelEquiv T A →
        NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain A R)
    {s : Quality} {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) s τ A F →
      Nest.All (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain x.1 x.2) τ →
      ∀ (s' : Quality) (F' : TermRel),
        NestRel sig ι n (fun m _ => levelRel sig ι m) s' .plain A F' →
        ∀ t u, F t u ↔ F' t u
  | .plain hA hF, _, _, _, h' => NestRel.unique hd ih (.plain hA hF) _ _ h'
  | .direct hA, hτ, _, _, h' => by
    cases hτ with
    | direct hT => exact NestRel.unique hd ih (hinv _ _ _ hT hA) _ _ h'
  | .codata (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hq hl hp hA _ hκ hn hrec _ hS,
      hτ, _, _, h' => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hF' =>
        cases Computesι.det hd ⟨.refl _, .inst D qs ls ps as⟩ hA'
        obtain ⟨_, hu, rfl⟩ := FieldRel.codata_type hd h hq hl hp hκ hn hF'
        cases hu with
        | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
        | codata h' _ _ _ hv' _ _ _ hS' =>
          obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
          subst hD hqs hls hps
          obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
          cases hT
          cases has
          obtain ⟨hdecl, hT, rfl⟩ := h
          exact TermRel.computed_congr fun v w => ((CodataType.blockRel_iff_corecRel
            (TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)) hT fun X o₁ o₂ =>
              (NestDesRel.agree hd ih hinv hS (Nesting.ofArgs_rel₃ hνs) _ _ (by
                have hS'' := hS' X _ hT
                simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
                exact hS'') o₁ o₂).symm) v w).symm
  | .codataProp (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h hq hl hp hA hκ hn hrec _ hS,
      hτ, _, _, h' => by
    cases hτ with
    | inst hνs =>
      subst hA
      cases h' with
      | plain hA' hF' =>
        cases Computesι.det hd ⟨.refl _, .inst D qs ls ps as⟩ hA'
        obtain ⟨_, hu, rfl⟩ := FieldRel.codata_prop hd h hq hl hp hκ hn hF'
        cases hu with
        | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
        | codata h' _ _ _ hv' _ _ _ hS' =>
          obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
          subst hD hqs hls hps
          obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
          cases hT
          cases has
          obtain ⟨hdecl, hT, rfl⟩ := h
          exact fun _ _ => (CodataType.blockTruth_iff_truth
            (TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)) hT fun B o₁ o₂ =>
              (NestDesRel.agree hd ih hinv hS (Nesting.ofArgs_rel₃ hνs) _ _ (by
                have hS'' := hS' B _ hT
                simp only [Destructors.recursionAt_eq_none hrec, Option.map_none] at hS''
                exact hS'') o₁ o₂).symm).symm
termination_by structural h _ _ _ _ => h

/-- The graph of the nestings gives destructors the equality that the graph of the destructors
gives them, at positions that hold types with the equality of their terms. -/
theorem NestDesRel.agree {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer)
    (hinv : ∀ (T A : Term 0 []) (R : TermRel),
      NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain T R → Term.LevelEquiv T A →
        NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain A R)
    {s : Quality} {Γ : Scope}
    {ν : Nesting NestLeaf Γ} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ}
    {S : ObsRel} :
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) s @ν ds @θ S →
      Nesting.All (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain x.1 x.2)
        @ν →
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
      have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have hts' := (hSS _ _).1 hts
        have ⟨_, hv⟩ := hB' ts hts'
        NestRel.agree hd ih hinv (hF ts hts) .plain _ _ (.plain hv (hF' ts hts' _ hv))
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact ObsRel.cons_congr hEp hEE fun f hf =>
        NestDesRel.agree hd ih hinv (hG f hf) (Nesting.lift_rel₃ hν) _ _ (hG' f ((hEE f f).1 hf))
    | recursive hrs' => cases hrs'
  | .nested (ps := ps) (B := B) (SΘ := SΘ) _ hΘ F hF _ _ hG, hν, _, _, h' => by
    have hSΘp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    cases h' with
    | cons hΘ' F' hB' hF' hBresp' _ hG' _ _ =>
      have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
      have hSΘp' := TelRel.isPer hd ih (fun _ => .plain) hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have hts' := (hSS _ _).1 hts
        have ⟨_, hv⟩ := hB' ts hts'
        NestRel.agree hd ih hinv (hF ts hts) (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hν) B) _ _
          (.plain hv (hF' ts hts' _ hv))
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      have hEp' := AbstractionRel.isPer hSΘp'
        (fun ts hts => have ⟨_, hv⟩ := hB' ts hts; FieldRel.isPer hd ih (hF' ts hts _ hv)) hBresp'
      have hGG : ∀ f, AbstractionRel _ F' f f → ∀ o₁ o₂, _ ↔ _ := fun f hf =>
        NestDesRel.agree hd ih hinv (hG f) (Nesting.lift_rel₃ hν) _ _ (hG' f hf)
      exact fun o₁ o₂ =>
        ⟨fun ⟨h₁, h₂⟩ =>
          have h₁' := (hEE _ _).1 h₁
          ⟨h₁', (hGG _ (hEp'.trans h₁' (hEp'.symm h₁')) o₁ o₂).1 h₂⟩,
        fun ⟨h₁', h₂'⟩ =>
          ⟨(hEE _ _).2 h₁', (hGG _ (hEp'.trans h₁' (hEp'.symm h₁')) o₁ o₂).2 h₂'⟩⟩
    | recursive hrs' => cases hrs'
termination_by structural h _ _ _ _ => h

end

end Sic.Core
