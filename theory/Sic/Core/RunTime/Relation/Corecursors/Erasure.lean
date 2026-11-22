module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.Corecursors
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Erasure of the Corecursors at Run Time

The properties of the positions that the branches of the destructors of a codata type give, of the
signatures of the cases they read, and of the erased arguments and observations, which the relation
of run time of the corecursors reads.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Positions -/

/-- The case of the constructor of the pair of the prelude is the first one. -/
theorem Signature.Distinct.pairCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Pair" "mk" = some i) : i = 0 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.pair (List.mem_singleton_self _)
    (hi : sig.constructorCase Prelude.pairType.name Prelude.pairMk.name = some i)
  rw [show Prelude.pair.cases = [(0, Prelude.pairType, Prelude.pairMk)] from rfl] at hj
  match i, hj with
  | 0, _ => rfl

/-- A closed term of the packing of a closed telescope, related to an address, computes to the
nested pairs of arguments of the telescope, which the meaning relates to themselves, and the value at
the address unpacks into addresses to which the arguments are related, each at the type of its
entry, when its grade is used at run time, and at the multiplicity at run time of its grade and the
requirement at run time of its requirement, in a signature whose names are distinct and that holds
the prelude. -/
theorem RunsAs.unpack (hd : sig.Distinct) (hpre : sig.HasPrelude) {H : Heap} :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → (κs : List (Universe 0)) → (l : Level 0) →
      {x : Term 0 []} → {a : Nat} → ValidTerm₀ sig ι x (Θ.pack κs l) →
      RunsAs sig ι P H x a (Θ.pack κs l) →
      ∃ (ts : Args 0 [] ps) (as : List Nat), Term.Packs sig ι x ts.terms ∧
        EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst ∧
        Unpack H ps.length a (ps.map (·.usage.run)) (ps.map (·.requirement.run)) as ∧
        RunsAsArgs sig ι P H (Parameter.grades ps) ts as Θ
  | [], .nil, _, l, _, _, hx, hr => by
    obtain ⟨T', hT', -, con, hc, ts, i, bs, hct, -, ha, -, hruns⟩ := RunsAs.ctor_inv hd hpre.unit
      (qs := []) (ls := [l]) (ps := []) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rfl) hx hr
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    match ts, bs, hruns with
    | .nil, [], _ =>
      -- The unit stores no field.
      refine ⟨.nil, [], ?_, (EqSubst.empty_iff _ _).2 trivial,
        .zero (ha : H[_]? = some (Value.ctor i [] [] [])), trivial⟩
      simp only [Args.terms, Term.Packs]
      exact hct
  | _ :: _, .cons q p A Θ, κs, l, _, _, hx, hr => by
    obtain ⟨T', hT', -, con, hc, ts, i, bs, hct, hi, ha, hts, hruns⟩ := RunsAs.ctor_inv hd hpre.pair
      (qs := [(κs.headD ⟨.type, l⟩).quality])
      (ls := [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l])
      (ps := [p.usage, p.requirement]) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rcases i with _ | _ | _ <;> rfl) hx hr
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    obtain rfl := hd.pairCase hpre hi
    match ts, bs, hts, hruns with
    | .cons t (.cons y .nil), [b, c], hts, hruns =>
      obtain ⟨ht, hys⟩ := EqSubst.args_cons_iff.1 hts
      obtain ⟨hy, -⟩ := EqSubst.args_cons_iff.1 hys
      obtain ⟨hb, hc', -⟩ := hruns
      have hy' : ValidTerm₀ sig ι y ((Θ.subst₀ (Subst₀.single t)).pack κs.tail l) := by
        rw [← Telescope.pack_subst₀, ← Prelude.pairSecond (Θ.pack κs.tail l)]
        exact hy
      have hry : RunsAs sig ι P H y c ((Θ.subst₀ (Subst₀.single t)).pack κs.tail l) := by
        rw [← Telescope.pack_subst₀, ← Prelude.pairSecond (Θ.pack κs.tail l)]
        exact hc' (by decide : Grade.one ∉ Mode.oneOne.erased)
      obtain ⟨ts', as', hp', hτ, hu, hrs⟩ := RunsAs.unpack hd hpre _ κs.tail l hy' hry
      obtain ⟨qs₁, ls₁, ps₁, Δ₁, as₁, hc₁⟩ := hct
      -- The pair stores its entry at the multiplicity and the requirement of its parameter, and
      -- the others at `1`.
      have ha' : _ = some (Value.ctor 0 [p.usage.run, .one] [p.requirement.run, .one] [b, c]) := ha
      have hone : ∀ πs : List Multiplicity, πs.map (Multiplicity.one * ·) = πs := fun πs => by
        induction πs with
        | nil => rfl
        | cons π πs ih =>
          rw [List.map_cons, ih]
          exact congrArg (· :: πs) ((by decide : ∀ π : Multiplicity, .one * π = π) π)
      have hu' := Unpack.pair ha' hu
      rw [hone, hone] at hu'
      refine ⟨.cons t ts', b :: as', ?_, EqSubst.args_cons_iff.2 ⟨ht, hτ⟩, hu', hb, hrs⟩
      simp only [Args.terms, Term.Packs]
      exact ⟨qs₁, ls₁, ps₁, Δ₁, as₁, y, hc₁, hp'⟩


/-- The case of the constructor `next` of the type of positions of the prelude is the first one. -/
theorem Signature.Distinct.nextCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Step" "next" = some i) : i = 0 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.step (List.mem_cons_self ..)
    (hi : sig.constructorCase Prelude.stepType.name Prelude.stepNext.name = some i)
  rw [show Prelude.step.cases = [(0, Prelude.stepType, Prelude.stepNext),
    (0, Prelude.stepType, Prelude.stepDone)] from rfl] at hj
  match i, hj with
  | 0, _ => rfl
  | 1, hj =>
    exact absurd (congrArg (fun x => x.2.2.name) (Option.some.inj hj))
      (by decide : Prelude.stepDone.name ≠ Prelude.stepNext.name)

/-- The case of the constructor `done` of the type of positions of the prelude is the second one. -/
theorem Signature.Distinct.doneCase (hd : sig.Distinct) (hpre : sig.HasPrelude) {i : Nat}
    (hi : sig.constructorCase "Step" "done" = some i) : i = 1 := by
  obtain ⟨j, hj⟩ := hd.cases_of_constructorCase hpre.step
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (hi : sig.constructorCase Prelude.stepType.name Prelude.stepDone.name = some i)
  rw [show Prelude.step.cases = [(0, Prelude.stepType, Prelude.stepNext),
    (0, Prelude.stepType, Prelude.stepDone)] from rfl] at hj
  match i, hj with
  | 0, hj =>
    exact absurd (congrArg (fun x => x.2.2.name) (Option.some.inj hj))
      (by decide : Prelude.stepNext.name ≠ Prelude.stepDone.name)
  | 1, _ => rfl

-- ADE: none.
/-- A closed position of a corecursor of the grade `r`, in a universe, related to an address,
resumes: the position computes to a new state, the nested pairs of arguments of the state that the
meaning relates to themselves, and its resumption, a new closure from addresses to which the
arguments are related at the grades of the state times `r`, each at the multiplicity at run time of
this grade, which it unpacks from the new state, with the requirements at run time of the entries,
when `r` is used at run time, and takes at the address of the new state otherwise, without reading
it; or the position computes to a term already built, related to the address that its resumption
gives, which the ownership `ψ` at run time of the result allows, whose constant is that of `χ`. -/
theorem RunsAs.resume (hd : sig.Distinct) (hpre : sig.HasPrelude) {κ : Universe 0}
    (hκ : κ.quality = .type) {r χ : Grade} {ps' : List Parameter} {S : Telescope 0 [] ps'}
    {κs : List (Universe 0)} {T g : Term 0 []}
    (hgv : ValidTerm₀ sig ι g (Term.positions κ r χ S κs T)) {H : Heap} {w : Nat}
    (hg : RunsAs sig ι P H g w (Term.positions κ r χ S κs T)) (n : Nat) (E : List Nat)
    (Ps : TargetCorecBranches n) (D' : Name) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) {Δ : Scope} (as : InstanceArgs 0 [] Δ) (Ss : States 0 [])
    (gs : DestructorBranches 0 []) {c : Nat} (ψ : ResultOwnership Multiplicity c)
    (hψ : ψ.constant.getD .omega ≤ χ.run) :
    ∃ v H', EvalResume H n E Ps
        (Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps'.length)) ψ w v H' ∧
      H.Extends H' ∧
      ((∃ (ts : Args 0 [] ps') (bs : List Nat) (ϱs : List Multiplicity),
          RedStar (sig.interpret ι) (Term.resume r D' qs ls ps as Ss gs κ χ S κs g)
            (.corec r D' qs ls ps as ts.terms Ss gs) ∧
          EqSubst sig ι (Context.empty.append S) ts.toSubst ts.toSubst ∧
          RunsAsArgs sig ι P H (fun l => r * Parameter.grades ps' l) ts bs S ∧
          H' = H ++ [.corec n E Ps (ps'.map fun p => (r * p.usage).run) ϱs bs] ∧
          (ϱs.length = ps'.length ∧ (r ∉ Mode.oneOne.erased → ϱs = ps'.map (·.requirement.run))) ∧
          v = H.length) ∨
        (H' = H ∧ RunsAs sig ι P H (Term.resume r D' qs ls ps as Ss gs κ χ S κs g) v T)) := by
  obtain ⟨T', hT', -, con, hc, ts, i, bs, ⟨qs', ls', ps'', Δ', as', hct⟩, hi, ha, hts, hruns⟩ :=
    RunsAs.ctor_inv hd hpre.step (qs := [κ.quality])
      (ls := [Telescope.packLevel κs (Telescope.packLevel κs .zero), κ.level])
      (ps := [r, Prelude.doneGrade κ.quality, χ]) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩ <;> cases i <;> rfl) hgv hg
  obtain rfl := List.mem_singleton.1 hT'
  rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩
  · -- A new state.
    obtain rfl := hd.nextCase hpre hi
    match ts, bs, hts, hruns with
    | .cons x .nil, [b], hts, hruns =>
      have hx := (EqSubst.args_cons_iff.1 hts).1
      have hred := fun (ts' : Args 0 [] ps') (hp' : Term.Packs sig ι x ts'.terms) =>
        RedStar.resume_next (r := r) (D := D') (qs := qs) (ls := ls) (ps := ps) (as := as)
          (Ss := Ss) (gs := gs) (κ := κ) (χ := χ) (S := S) (κs := κs) hpre hct.1 ts' hp'
      by_cases hrS : r ∈ Mode.oneOne.erased
      · -- The state is erased, and the new closure does not read it.
        obtain ⟨ts₁, ts₂, hp₁, hp₂, hτ⟩ := ValidEqTerm₀.pack_inv hpre S κs _ hx
        have e₀ := Args.terms_inj (Term.Packs.det hd hp₁ hp₂)
        subst e₀
        refine ⟨_, _, ?_, List.prefix_append _ _, .inl ⟨ts₁, List.replicate ps'.length b,
          List.replicate ps'.length .zero, hred ts₁ hp₁, hτ, RunsAsArgs.of_erased ts₁ _ S
            (fun l p _ =>
              (by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased) r
                _ hrS) List.length_replicate, rfl, ⟨List.length_replicate, fun h => absurd hrS h⟩,
            rfl⟩⟩
        simp only [hrS, decide_true, Resumption.ofArity, ↓reduceIte]
        have hz : (ps'.map fun p => (r * p.usage).run) = List.replicate ps'.length .zero :=
          List.eq_replicate_iff.2 ⟨List.length_map .., fun π hπ => by
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hπ
            exact (Mode.erased_values.1 _).1
              ((by decide : ∀ r u : Grade, r ∈ Mode.oneOne.erased → r * u ∈ Mode.oneOne.erased)
                r p.usage hrS)⟩
        rw [hz]
        -- The field of `next` has the multiplicity at run time of `r`, erased.
        have ha' : H[w]? = some (.ctor 0 [r.run] [Grade.one.run] [b]) := ha
        rw [(Mode.erased_values.1 _).1 hrS] at ha'
        exact .erased ha'
      · -- The state is used, and the new closure unpacks it.
        obtain ⟨ts', bs', hp', hτ, hu, hrs⟩ := RunsAs.unpack hd hpre S κs _ hx (hruns.1 hrS)
        refine ⟨_, _, ?_, List.prefix_append _ _, .inl ⟨ts', bs', ps'.map (·.requirement.run),
          hred ts' hp', hτ,
          RunsAsArgs.of_counted (fun l h => (by decide : ∀ r u : Grade,
            r * u ∉ Mode.oneOne.erased → u ∉ Mode.oneOne.erased) r (Parameter.grades ps' l) h) hrs,
          rfl, ⟨List.length_map .., fun _ => rfl⟩, rfl⟩⟩
        simp only [hrS, decide_false, Resumption.ofArity, Bool.false_eq_true, ↓reduceIte]
        -- The field of `next` requires the ownership `1`, which keeps the requirements.
        have ha' : H[w]? = some (.ctor 0 [r.run] [.one] [b]) := ha
        have hev := EvalResume.next (n := n) (E := E) (Ps := Ps) (ψ := ψ) ha' hu
        have hone : ∀ πs : List Multiplicity, πs.map (Multiplicity.one * ·) = πs := fun πs => by
          induction πs with
          | nil => rfl
          | cons π πs ih =>
            rw [List.map_cons, ih]
            exact congrArg (· :: πs) ((by decide : ∀ π : Multiplicity, .one * π = π) π)
        rwa [List.map_map, hone] at hev
  · -- A term already built.
    obtain rfl := hd.doneCase hpre hi
    match ts, bs, hruns with
    | .cons t .nil, [b], hruns =>
      have hne : Resumption.ofArity (decide (r ∈ Mode.oneOne.erased)) (some ps'.length) ≠
          .none := by
        cases decide (r ∈ Mode.oneOne.erased) <;> intro h <;> cases h
      -- The field of `done` has the multiplicity at run time of its grade, used at run time.
      have hq : Prelude.doneGrade κ.quality ∉ Mode.oneOne.erased := by
        rw [hκ]
        decide
      have ha' : H[w]? = some (.ctor 1 [(Prelude.doneGrade κ.quality).run] [χ.run] [b]) := ha
      refine ⟨b, H, .done hne ha' (fun h0 => hq ((Mode.erased_values.1 _).2 h0)) hψ,
        List.prefix_refl _, .inr ⟨rfl, ?_⟩⟩
      rw [RunsAs.redStar_iff hd (RedStar.resume_done hpre hct.1)]
      exact hruns.1 hq

/-! ## Signatures -/

/-- An entry that does not introduce the name `D` gives the types resumed by the destructors of no
block of `D`. -/
theorem Entry.resumedTypes_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.resumedTypes D qs ps e = none
  | .typeDeclaration decl, hD => by
    have hnone : decl.codataTypes.find? (·.name == D) = none := List.find?_eq_none.2 fun T hT h =>
      hD (beq_iff_eq.1 h ▸ TypeDeclaration.codata_name_mem_names hT)
    simp only [Entry.resumedTypes]
    split
    · try split
      all_goals first
        | rfl
        | rw [hnone, Option.map_none]
    · rfl
  | .constantDefinition _, _ => rfl
  | .constantDeclaration _, _ => rfl

/-- In a signature whose names are distinct, the types resumed by the destructors of the cases of the
block of a codata type are the positions of the types that their results name, at the instance. -/
theorem Signature.Distinct.resumedTypes : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hq : qs.length = decl.sorts) → (hp : ps.length = decl.grades) →
    sig.resumedTypes D qs ps = some (decl.codataCases.map fun x =>
      ((x.2.1.body (.ofLists qs ps hq hp)).resultName decl.names x.2.2).bind decl.names.idxOf?)
  | [], _, _, _, _, h, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hq, hp => by
    unfold Signature.resumedTypes
    rcases List.mem_cons.1 he with rfl | he'
    · have hg : Entry.resumedTypes D qs ps (.typeDeclaration decl) = some (decl.codataCases.map
          fun x => ((x.2.1.body (.ofLists qs ps hq hp)).resultName decl.names x.2.2).bind
            decl.names.idxOf?) := by
        simp only [Entry.resumedTypes, hq, hp, ↓reduceDIte, ← hD,
          List.find?_of_nodup_map (TypeDeclaration.codataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.resumedTypes_of_not_mem hDe]; rfl)]
      exact hd.resumedTypes ⟨he', hT, hD⟩ hq hp

/-- The case `i` of the branches `vs` of a corecursor on a codata type of a block, whose states are
those of the types of the block and whose branches bind the arguments of their destructors, is a
destructor `d` of the type `T'` at a position `j`, of state `S'`, with its branch `g`, and what the
erasure of the corecursor reads at this case: the grade of the destructor, its arguments and the
position of the type of its result in the block, whatever the erasure maps them to. -/
theorem Signature.Distinct.corecCase (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasCodataType D decl T)
    {qs : List Quality} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) {k : Nat} {Γ : Scope} {Ss : States k Γ}
    {vs : DestructorBranches k Γ}
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' → ∃ ps'' S', Ss.get j = some ⟨0, ps'', S'⟩)
    (hgl : vs.length = decl.codataCases.length)
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
      (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
      ∃ g, vs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
    {i : Nat} (hi : i < vs.length) :
    ∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name)
      (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade) (ps₁ : List Parameter)
      (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership Grade ps₁.length) (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) ∧ Ss.get j = some ⟨0, ps'', S'⟩ ∧
      Nonempty ((T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) ∧
      vs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ ∧
      ((sig.destructorGrades D qs ps).getD [])[i]? = some p ∧
      (∀ {β : Type} (f : (Nat × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade) → β)
        (a : β), ((((sig.destructorArguments D qs ps).getD []).map f).drop i).headD a =
          f (j, ⟨ps₁, ψ, ς⟩)) ∧
      (∀ {β : Type} (f : Option Nat → β) (a : β),
        ((((sig.resumedTypes D qs ps).getD []).map f).drop i).headD a =
          f ((B.blockName decl.names).bind decl.names.idxOf?)) := by
  obtain ⟨grs, hgrs, hgri⟩ := hd.destructorGrades h hq hp
  obtain ⟨⟨j, T', d⟩, hc⟩ : ∃ c, decl.codataCases[i]? = some c :=
    ⟨_, List.getElem?_eq_getElem (hgl ▸ hi)⟩
  have hcm := List.mem_of_getElem? hc
  obtain ⟨hT', hdm⟩ := TypeDeclaration.mem_casesFrom hcm
  obtain ⟨ps'', S', hSj⟩ := hSs j T' (TypeDeclaration.codataTypes_getElem?_of_codataCases hcm)
  obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos (T'.body _) hdm
  have hnd := hd.destructors_nodup ⟨h.1, hT', rfl⟩
  obtain ⟨g, hg⟩ := hgs i j T' d ps'' S' hc hSj p q ς ps₁ Ξ Θ B ψ hpos
  refine ⟨j, T', d, ps'', S', p, q, ς, ps₁, Ξ, Θ, B, ψ, g, hc, hSj, ⟨hpos⟩, hg, ?_,
    fun f _ => List.headD_drop ?_, fun f _ => List.headD_drop ?_⟩
  · rw [hgrs]
    exact hgri i j T' d hc p (hpos.grade hnd)
  · simp [hd.destructorArguments h hq hp, hc, hpos.arguments hnd]
  · simp [hd.resumedTypes h hq hp, hc, hpos.resultName decl.names hnd]

/-! ## Erasure -/

/-- The branch at a position of the erased branches of a corecursor, without non-uniform
parameters, is the erasure of the branch at this position, at the grade `p` of its destructor, with
the resumption at this position, the multiplicities `run(⌜11ᵐ ⊙ p⌝ · q)` and the requirements at
run time of its binders, for the parameters of the entries of the state and of the arguments at this
position, the ownership at run time of the result and the requirement at run time on the observed
value at this position. -/
theorem DestructorBranches.get_erase (S : Math.Set Grade) [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) :
    (gs : DestructorBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
      (pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)) →
      {i b c : Nat} →
      {g : Term k ((Γ.extend b).extend c)} → gs.get i = some ⟨0, b, c, g⟩ → {p : Grade} →
      ps[i]? = some p →
      (gs.erase sig S hΓ ps ks pss).get i = some (ks.getD i .none, ⟨b, c,
        fun j => (((pss.drop i).headD ([], ResultOwnership.noArguments)).1[(j : Nat)]?.map
          fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega,
        fun j => (((pss.drop i).headD ([], ResultOwnership.noArguments)).1[(j : Nat)]?.map
          (·.requirement.run)).getD .omega,
        fun j => (((pss.drop i).headD ([], ResultOwnership.noArguments)).2.1[(j : Nat)]?.map
          fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega,
        fun j => (((pss.drop i).headD ([], ResultOwnership.noArguments)).2.1[(j : Nat)]?.map
          (·.requirement.run)).getD .omega,
        (((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.1.toArity c).map Grade.run,
        ((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.2.run,
        if p ∈ S then .erased else
          Scope.length_extend_extend Γ b c ▸ g.erase sig S ((hΓ.extend b).extend c)⟩)
  | .nil, _, _, _, _, _, _, _, h, _, _ => nomatch h
  | .cons 0 _ _ _ _, _ :: _, ks, pss, 0, _, _, _, h, _, hp => by
    cases h
    cases hp
    cases ks <;> rfl
  | .cons 0 _ _ _ _, [], _, _, 0, _, _, _, _, _, hp => nomatch hp
  | .cons (_ + 1) _ _ _ _, _, _, _, 0, _, _, _, h, _, _ => by cases h
  | .cons 0 _ _ _ vs, _ :: ps, ks, pss, i + 1, _, _, _, h, _, hp => by
    have e : ks.tail.getD i .none = ks.getD (i + 1) .none := by cases ks <;> simp
    have e' : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
    rw [← e, e']
    exact DestructorBranches.get_erase S hΓ vs ps ks.tail pss.tail h hp
  | .cons 0 _ _ _ _, [], _, _, _ + 1, _, _, _, _, _, hp => nomatch hp
  | .cons (_ + 1) _ _ _ vs, ps, ks, pss, i + 1, _, _, _, h, p, hp => by
    have e : ks.tail.getD i .none = ks.getD (i + 1) .none := by cases ks <;> simp
    have e' : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
    have hp' : ps.tail[i]? = some p := by cases ps <;> simp_all
    rw [← e, e']
    exact DestructorBranches.get_erase S hΓ vs ps.tail ks.tail pss.tail h hp'

/-- The erasure of terms at the parameters `us` whose grades are multiplied by `r`, renamed by `g`,
evaluates, at a weight, as their erasure at `us`, renamed, at the weight times `r`, when `r` is used
at run time, since a grade times `r` is used at run time when the grade is: the two erasures keep
the same terms, each evaluated at the weight times `r` times its grade, and differ only by the
multiplicities at which they store them. -/
theorem Terms.evalAll_erase_mul_of_not_erased {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) {r : Grade}
    (hr : r ∉ Mode.oneOne.erased) {m : Nat} (g : TargetRen m Γ.length) {ϖ : Multiplicity}
    {E : List Nat} :
    (ts : Terms k Γ) → (us : List Parameter) → {H H' : Heap} → {bs tr : List Nat} →
      EvalAll P (ϖ * r.run) H E ((ts.erase sig Mode.oneOne.erased hΓ us).rename g) bs H' tr →
      EvalAll P ϖ H E ((ts.erase sig Mode.oneOne.erased hΓ
        (us.map fun u => ⟨r * u.usage, u.requirement⟩)).rename g) bs H' tr
  | .nil, _, _, _, _, _, h => by
    cases h
    exact .nil
  | .cons _ ts, [], _, _, _, _, h => by
    cases h with
    | cons hM hMs =>
      cases hM
      exact .cons .erased (Terms.evalAll_erase_mul_of_not_erased hΓ hr g ts [] hMs)
  | .cons _ ts, u :: us, _, _, _, _, h => by
    have hu := (by decide : ∀ r u : Grade, r ∉ Mode.oneOne.erased →
      (r * u ∈ Mode.oneOne.erased ↔ u ∈ Mode.oneOne.erased)) r u.usage hr
    simp only [List.map_cons, Terms.erase, Targets.rename, hu] at h ⊢
    cases h with
    | cons hM hMs =>
      refine .cons ?_ (Terms.evalAll_erase_mul_of_not_erased hΓ hr g ts us hMs)
      rwa [show (r * u.usage).run = r.run * u.usage.run from rfl,
        ← Multiplicity.modality.semiring.mul_assoc]

/-- Arguments erased at grades that are all erased, renamed by `g`, evaluate to `↯`, allocated one
after the other, at as many addresses as arguments, reading no cell. -/
theorem Args.evalAll_erased (S : Math.Set Grade) [DecidablePred (· ∈ S)] {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {m : Nat} (g : TargetRen m Γ.length) (ϖ : Multiplicity) (E : List Nat) :
    {ps : List Parameter} → (ts : Args k Γ ps) → (us : List Parameter) → (∀ u ∈ us, u.usage ∈ S) →
      (H : Heap) → ∃ bs H', EvalAll P ϖ H E ((ts.terms.erase sig S hΓ us).rename g) bs H' [] ∧
        H.Extends H' ∧ bs.length = ps.length
  | [], .nil, _, _, H => ⟨[], H, .nil, List.prefix_refl _, rfl⟩
  | _ :: _, .cons _ ts, [], _, H => by
    obtain ⟨bs, H', hev, hH, hl⟩ :=
      Args.evalAll_erased S hΓ g ϖ E ts [] (fun _ h => nomatch h) (H ++ [.erased])
    exact ⟨H.length :: bs, H', .cons .erased hev, (List.prefix_append _ _).trans hH,
      congrArg (· + 1) hl⟩
  | _ :: _, .cons _ ts, u :: us, hu, H => by
    obtain ⟨bs, H', hev, hH, hl⟩ := Args.evalAll_erased S hΓ g ϖ E ts us
      (fun u' h => hu u' (List.mem_cons_of_mem _ h)) (H ++ [.erased])
    refine ⟨H.length :: bs, H', ?_, (List.prefix_append _ _).trans hH, congrArg (· + 1) hl⟩
    simp only [Args.terms, Terms.erase, Targets.rename, hu u List.mem_cons_self, ↓reduceIte]
    exact .cons .erased hev


end Sic.Core
