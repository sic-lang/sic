module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Levels
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Run Time of the Declared Types

The constructors of the data types of a meaningful declaration at run time: a constructor applied
to arguments of its fields, allocated with the addresses of their values, is related to its address
at its instance, when each argument is related to its address at the type of its field, as `(®_μ)`
relates it once unfolded, `(®_c)` relating the fields by the relation of run time of the telescope
of the fields, whose recursive fields are related by `(®_μ)`, as their types, the instances of the
block, say.
Conversely, the relation of run time of an instance of a data type of a type is `(®_μ)` of its
block, and the arguments that the relation of the fields relates to addresses are related to them at
their fields, which the recursors read.

The relation of run time of the fields that the graph gives is that of the fields at the values of
the levels, which the meaning of the declaration makes meaningful, and whose positions hold the
instances of the block with the relations `(®_μ)`, their relations of run time, so that the
arguments are related at these fields, then at the fields at the levels of the instance, which
differ from them only by levels of the same values.

ADE prove the validity of their constructors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- A term related to an address at a type that computes to the type of a field is related to it by
the relation of run time of the field. -/
theorem RunFieldRel.of_runsAs (hd : sig.Distinct) {n : Nat} {v A t : Term 0 []} {R : RunRel}
    {H : Heap} {b : Nat} (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R)
    (hA : Computesι sig ι A v) (h : RunsAs sig ι P H t b A) : R H t b := by
  obtain ⟨v', hA', h⟩ := h
  cases Computesι.det hd hA hA'
  have huniv : ∀ m R₀, (levelRel sig ι m).run P v R₀ → R₀.computed sig ι H t b :=
    fun m R₀ hR₀ => by
      rcases h with ⟨_, _, hp⟩ | ⟨Q, hQ, htQ⟩
      · exact (RunUnivRel.not_prop hd (levelRel_run_iff.1 hR₀) (levelRel_prop_iff.1 hp)).elim
      · rw [HasRun.eq hd hQ (.univ m hR₀)] at htQ
        exact htQ
  cases hR with
  | univ h' => exact huniv n _ (levelRel_run_iff.2 h')
  | univBelow m _ h' => exact huniv m _ h'
  | prop _ => trivial
  | propBelow _ _ _ => trivial

/-- A term related to an address at a type is related to it by the relation of run time that the
graph of the nestings gives the type, at positions that hold types with their relations of run
time, in a signature whose names are distinct, when the type is a term of a sort whose level the
level `n` bounds if it is an instance of a declared type. -/
theorem RunNestRel.of_runsAs (hd : sig.Distinct) {n : Nat} {τ : Nest RunNestLeaf}
    {A t : Term 0 []} {R : RunRel} {H : Heap} {b : Nat}
    (h : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (hτ : Nest.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) τ)
    (hA : (∃ νs, τ = .inst νs) → ∃ κ₁ : Universe 0, κ₁.quality ≤ .type ∧
      κ₁.level.closedValue ≤ n ∧ ValidEqTerm₀ sig ι A A (.sort κ₁))
    (hr : RunsAs sig ι P H t b A) : R H t b := by
  have hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R := fun _ _ _ hT hTA =>
    RunNestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hT hTA .plain
  have hplain : ∃ R', RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R' := by
    have hsort : (∃ κ₁ : Universe 0, κ₁.quality ≤ .type ∧ κ₁.level.closedValue ≤ n ∧
        ValidEqTerm₀ sig ι A A (.sort κ₁)) →
        ∃ R', RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R' :=
      fun ⟨_, _, hn, hv⟩ =>
        have ⟨_, _, R', hc, _, hR', _⟩ := hv.runFieldRel P hn
        ⟨R', .plain hc hR'⟩
    cases h with
    | plain hc hR => exact ⟨R, .plain hc hR⟩
    | direct hT =>
      cases hτ with
      | direct hx => exact ⟨_, hinv _ _ _ hx hT⟩
    | codata => exact hsort (hA ⟨_, rfl⟩)
    | codataProp => exact hsort (hA ⟨_, rfl⟩)
  obtain ⟨R', h'⟩ := hplain
  refine levelRel_runNest_agree_nest hd hinv h hτ h' H t b ?_
  cases h' with
  | plain hc hR' => exact hR'.of_runsAs hd hc hr

/-- Arguments of a closed telescope of the graph of run time, which the meaning relates to
themselves and which are related to addresses at its fields, are related to them by the relation of
run time of the terms of its fields, at positions that hold types with their relations of run
time. -/
theorem RunTelRel.of_runsAsArgs (hd : sig.Distinct) {n : Nat} {H : Heap} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : RunFieldsRel} →
      {rs : Nat → Nest RunNestLeaf} →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S →
      Θ.NestHeads sig ι n .type (fun i => ∃ νs, rs i = .inst νs) →
      (∀ i, Nest.All
        (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) (rs i)) →
      (g : Nat → Grade) →
      (∀ l p, ps[l]? = some p → p.usage ∉ Mode.oneOne.erased → g l ∉ Mode.oneOne.erased) →
      (ts : Args 0 [] ps) → EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
      (bs : List Nat) → RunsAsArgs sig ι P H g ts bs Θ → S H ts.terms bs
  | [], .nil, _, _, h', _, _, _, _, .nil, _, [], _ => by cases h'; trivial
  | [], .nil, _, _, _, _, _, _, _, .nil, _, _ :: _, h => (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, _, _, _, _, _, .cons _ _, _, [], h => (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, h', hH, hτ, g, hg, .cons t ts, h, b :: bs, hargs => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    obtain ⟨hb, hbs⟩ := hargs
    rw [Telescope.NestHeads] at hH
    have hg' : ∀ l (p : Parameter), _ → p.usage ∉ Mode.oneOne.erased →
        g (l + 1) ∉ Mode.oneOne.erased :=
      fun l p hl => hg (l + 1) p hl
    cases h' with
    | cons hA hF hRf G hG _ =>
      have hFtt := hF.of_validEqTerm hA ht
      exact And.intro ⟨hFtt, fun hp => hRf.of_runsAs hd hA (hb (hg 0 _ rfl hp))⟩
        (RunTelRel.of_runsAsArgs hd (hG t hFtt) (hH.2 t ht) (fun i => hτ (i + 1)) _ hg' ts hts
          bs hbs)
    | nested hrs hRn G hG =>
      exact And.intro (fun hp => hRn.of_runsAs hd (hτ 0) hH.1 (hb (hg 0 _ rfl hp)))
        (RunTelRel.of_runsAsArgs hd (hG t) (hH.2 t ht) (fun i => hτ (i + 1)) _ hg' ts hts bs
          hbs)

/-- The type of a field, or of the result of a destructor, of the graph of run time has a relation of
run time. -/
theorem RunFieldRel.hasRun {n : Nat} {v : Term 0 []} {R : RunRel}
    (h : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R) : ∃ R', HasRun sig ι P v R' := by
  cases h with
  | univ h => exact ⟨_, .univ n (levelRel_run_iff.2 h)⟩
  | univBelow m _ h => exact ⟨_, .univ m h⟩
  | prop h => exact ⟨_, .prop n _ (levelRel_prop_iff.2 h) fun _ _ _ => trivial⟩
  | propBelow m _ h => exact ⟨_, .prop m _ h fun _ _ _ => trivial⟩

/-- A term related to an address by the relation of run time of the type of a field is related to
it at a type that computes to this type: the converse of `RunFieldRel.of_runsAs`. -/
theorem RunFieldRel.runsAs {n : Nat} {v A t : Term 0 []} {R : RunRel} {H : Heap} {b : Nat}
    (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R) (hA : Computesι sig ι A v)
    (h : R H t b) : RunsAs sig ι P H t b A := by
  cases hR with
  | univ h' => exact ⟨v, hA, .inr ⟨_, .univ n (levelRel_run_iff.2 h'), h⟩⟩
  | univBelow m _ h' => exact ⟨v, hA, .inr ⟨_, .univ m h', h⟩⟩
  | prop h' => exact ⟨v, hA, .inl ⟨n, _, levelRel_prop_iff.2 h'⟩⟩
  | propBelow m _ h' => exact ⟨v, hA, .inl ⟨m, _, h'⟩⟩

/-- A term that the meaning relates to itself and that the relation of run time that the graph of
the nestings gives a type relates to an address is related to it at the type, at positions that
hold types with their relations of run time, when the type is a term of a sort whose level the
level `n` bounds if it is an instance of a declared type: the converse of `RunNestRel.of_runsAs`,
for the terms that the equality of the type relates to themselves. -/
theorem RunNestRel.runsAs {n : Nat} {τ : Nest RunNestLeaf} {A t : Term 0 []} {R : RunRel}
    {H : Heap} {b : Nat} (h : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (hτ : Nest.All (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) τ)
    (hA : (∃ νs, τ = .inst νs) → ∃ κ₁ : Universe 0, κ₁.quality ≤ .type ∧
      κ₁.level.closedValue ≤ n ∧ ValidEqTerm₀ sig ι A A (.sort κ₁))
    (ht : ValidEqTerm₀ sig ι t t A) (hr : R H t b) : RunsAs sig ι P H t b A := by
  have hd : sig.Distinct := ht.1.1
  have hinv : ∀ (T A : Term 0 []) (R : RunRel),
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain T R → Term.LevelEquiv T A →
        RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain A R := fun _ _ _ hT hTA =>
    RunNestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hT hTA .plain
  -- An instance of a declared type is a type without position, whose equality relates the term to
  -- itself: the graph of run time then relates what the graph of the nestings does.
  have hsort : (∃ νs, τ = .inst νs) → RunsAs sig ι P H t b A := fun hi => by
    obtain ⟨_, hs, hn, hv⟩ := hA hi
    obtain ⟨_, _, E, hc, _, hE, _, _⟩ := hv.fieldRel hs hn
    obtain ⟨_, _, R', hc', _, hR', _⟩ := hv.runFieldRel P hn
    cases Computesι.det hd hc hc'
    exact hR'.runsAs hc (levelRel_runNest_agree_plain hd hinv h hτ (.plain hc hR')
      (.plain (sT := .type) hc hE) H t b (hE.of_validEqTerm hc ht) hr)
  cases h with
  | plain hc hR => exact hR.runsAs hc hr
  | direct hT =>
    cases hτ with
    | direct hx =>
      cases hinv _ _ _ hx hT with
      | plain hc hR => exact hR.runsAs hc hr
  | codata => exact hsort ⟨_, rfl⟩
  | codataProp => exact hsort ⟨_, rfl⟩

/-- Arguments of a closed telescope of the graph of run time, which the meaning relates to
themselves and which its relation of run time relates to addresses, are related to them at its
fields, at positions that hold types with their relations of run time: the converse of
`RunTelRel.of_runsAsArgs`. -/
theorem RunsAsArgs.of_runTelRel {n : Nat} {H : Heap} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : RunFieldsRel} →
      {rs : Nat → Nest RunNestLeaf} →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S →
      Θ.NestHeads sig ι n .type (fun i => ∃ νs, rs i = .inst νs) →
      (∀ i, Nest.All
        (fun x => RunNestRel sig ι P n (fun m _ => levelRel sig ι m) .plain x.1 x.2) (rs i)) →
      (g : Nat → Grade) →
      (∀ l p, ps[l]? = some p → g l ∉ Mode.oneOne.erased → p.usage ∉ Mode.oneOne.erased) →
      (ts : Args 0 [] ps) → EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
      (bs : List Nat) → S H ts.terms bs → RunsAsArgs sig ι P H g ts bs Θ
  | [], .nil, _, _, _, _, _, _, _, .nil, _, [], _ => trivial
  | [], .nil, _, _, h', _, _, _, _, .nil, _, _ :: _, h => by cases h'; exact (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, h', _, _, _, _, .cons _ _, _, [], h => by
    cases h' <;> exact (h : False).elim
  | _ :: _, .cons _ _ _ _, _, _, h', hH, hτ, g, hg, .cons t ts, h, b :: bs, hS => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    rw [Telescope.NestHeads] at hH
    have hg' : ∀ l (p : Parameter), _ → g (l + 1) ∉ Mode.oneOne.erased →
        p.usage ∉ Mode.oneOne.erased :=
      fun l p hl => hg (l + 1) p hl
    cases h' with
    | cons hA _ hRf G hG _ =>
      obtain ⟨⟨hFtt, hb⟩, hbs⟩ := hS
      exact And.intro (fun hp => hRf.runsAs hA (hb (hg 0 _ rfl hp)))
        (RunsAsArgs.of_runTelRel (hG t hFtt) (hH.2 t ht) (fun i => hτ (i + 1)) _ hg' ts hts bs
          hbs)
    | nested hrs hRn G hG =>
      obtain ⟨hb, hbs⟩ := hS
      exact And.intro (fun hp => hRn.runsAs (hτ 0) hH.1 ht (hb (hg 0 _ rfl hp)))
        (RunsAsArgs.of_runTelRel (hG t) (hH.2 t ht) (fun i => hτ (i + 1)) _ hg' ts hts bs hbs)

/-- Arguments related to addresses are as many as the addresses. -/
theorem RunsAsArgs.length {H : Heap} : {ps : List Parameter} → {g : Nat → Grade} →
    {ts : Args 0 [] ps} → {bs : List Nat} → {Θ : Telescope 0 [] ps} →
    RunsAsArgs sig ι P H g ts bs Θ → bs.length = ps.length
  | [], _, .nil, [], .nil, _ => rfl
  | _ :: _, _, .cons _ _, _ :: _, .cons _ _ _ _, h => congrArg (· + 1) (RunsAsArgs.length h.2)
  | [], _, .nil, _ :: _, .nil, h => (h : False).elim
  | _ :: _, _, .cons _ _, [], .cons _ _ _ _, h => (h : False).elim

/-- The relation of run time of an instance of a data type of a type is `(®_μ)` of its block, for
relations of the fields that the graph of a level gives, in a signature whose names are distinct. -/
theorem HasRun.data (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasDataType D decl T)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {R : RunRel}
    (hR : HasRun sig ι P (.inst D qs ls ps as) R)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ n S, (∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m)
          (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
            fun D' => (.inst D' qs ls ps as, (X D').computed sig ι))
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) ∧
      R = DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D := by
  cases hR with
  | prop n b hb _ =>
    cases levelRel_prop_iff.1 hb with
    | data h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, -⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata hc _ _ _ hv' => exact (hd.inst_data_codata h hc hv').elim
  | univ n hn =>
    cases levelRel_run_iff.1 hn with
    | data h' _ _ _ hv' _ _ S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasDataType_unique h h'
      cases eq_of_heq has
      exact ⟨n, S, hS, rfl⟩
    | codata hc _ _ _ hv' => exact (hd.inst_data_codata h hc hv').elim

/-- The relation of run time of an instance of a codata type of a type is `(®_ν)` of its block, for
relations of the destructors that the graph of its level gives, in a signature whose names are
distinct. -/
theorem HasRun.codata (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasCodataType D decl T)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {R : RunRel}
    (hR : HasRun sig ι P (.inst D qs ls ps as) R)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ n S, ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = n ∧
      (∀ X, ∀ T' ∈ decl.codataTypes,
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) T'.name
          (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S X T')) ∧
      R = CodataType.runBlockRel decl.codataTypes S D := by
  cases hR with
  | prop n b hb _ =>
    cases levelRel_prop_iff.1 hb with
    | data hc _ _ _ hv' => exact (hd.inst_data_codata hc h hv'.symm).elim
    | codata h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, -⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasCodataType_unique h h'
      exact nomatch hs.symm.trans hs'
  | univ n hn =>
    cases levelRel_run_iff.1 hn with
    | data hc _ _ _ hv' => exact (hd.inst_data_codata hc h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasCodataType_unique h h'
      cases eq_of_heq has
      exact ⟨n, S, hn, hS, rfl⟩

/-- A closed term of an instance of a data type of a type, whose constructors have no field with a
position, related to an address, computes to a constructor whose fields the meaning relates to
themselves and are related to the fields of a value of its case at the address, each at the type of
its entry, in a signature whose names are distinct. -/
theorem RunsAs.ctor_inv (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasDataType D decl T)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hnr : ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors, ∀ i,
      (c.fields (.ofLists qs ps hq hp)).nestAt decl.names i = .plain)
    {as : InstanceArgs 0 [] decl.scope} {H : Heap} {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t (.inst D qs ls ps as)) (ht : RunsAs sig ι P H t a (.inst D qs ls ps as)) :
    ∃ T' ∈ decl.dataTypes, T'.name = D ∧ ∃ con ∈ T'.constructors,
      ∃ (ts : Args 0 [] (con.params (.ofLists qs ps hq hp))) (i : Nat) (bs : List Nat),
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t (.ctor D qs' ls' ps' as' con.name ts.terms)) ∧
        sig.constructorCase D con.name = some i ∧
        H[a]? = some (.ctor i ((con.params (.ofLists qs ps hq hp)).map (·.usage.run))
          ((con.params (.ofLists qs ps hq hp)).map (·.requirement.run)) bs) ∧
        EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
          ts.toSubst ts.toSubst ∧
        RunsAsArgs sig ι P H (Parameter.grades (con.params (.ofLists qs ps hq hp))) ts bs
          (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) := by
  obtain ⟨T', hT', hn, con, hc, ts, ts₂, ⟨qs', ls', ps', Δ', as', hct⟩,
    ⟨qs₂, ls₂, ps₂, Δ₂, as₂, hct₂⟩, hts⟩ := ValidEqTerm₀.ctor_inv h hq hl hp hs hnr htv
  have he : ts.terms = ts₂.terms := by
    have e := Computesι.det hd hct hct₂
    injection e
  have e₀ := Args.terms_inj he
  subst e₀
  have hw : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    (Whnf.inst ..).computes
  obtain ⟨v, hcv, hor⟩ := ht
  cases Computesι.det hd hw hcv
  rcases hor with ⟨k, b, hk⟩ | ⟨R, hR, w, htw, hrel⟩
  · cases levelRel_prop_iff.1 hk with
    | data h' _ _ _ hv' hs' =>
      obtain ⟨-, hD, hqs, hls, hps, -⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, -⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata hc' _ _ _ hv' => exact (hd.inst_data_codata h hc' hv').elim
  obtain ⟨n, S, hS, rfl⟩ := HasRun.data hd h hq hl hp hR hs
  cases Computesι.det hd htw hct
  have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
    fun X Y hXY => RunTelRel.block_mono hd (fun m _ => levelRel_run_mono hd m)
      (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
      (F := fun X D => (.inst D qs ls ps as, (X D).computed sig ι)) hS X Y
      fun D H _ _ => RunRel.computed_mono (hXY D H)
  obtain ⟨T'', hT'', hn'', c, hc', i, fs, bs, hIs, hi, ha, hSc⟩ :=
    DataType.runBlockRel_unfold hmono hrel
  have e₁ : T'' = T' := List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup h.1))
    hT'' hT' (hn''.trans hn.symm)
  subst e₁
  obtain ⟨-, hcn, rfl⟩ := hIs.inj ⟨_, _, _, _, _, rfl⟩
  have e₂ : c = con := List.eq_of_nodup_map (hd.constructors_nodup ⟨h.1, hT', hn⟩) hc' hc hcn
  subst e₂
  exact ⟨T'', hT', hn, c, hc, ts, i, bs, ⟨_, _, _, _, _, hct⟩, hn ▸ hi, ha, hts,
    RunsAsArgs.of_runTelRel (hS _ T'' hT' c hc)
      (Telescope.nestHeads_of_not _ fun j ⟨_, h⟩ => by
        rw [hnr T'' hT' c hc j] at h
        exact nomatch h)
      (fun j => by rw [hnr T'' hT' c hc j]; exact .plain) _
      (fun _ _ hl' hgl => (Parameter.grades_of_getElem? hl') ▸ hgl) ts hts bs hSc⟩

-- ADE: none.
/-- The positions of the fields of a constructor of a block of data types, at the values of the
levels `ls` and at arguments `ā`, hold the instances of the block there, which the graph of run
time relates by relations `X`, when the instances at `ls` are types of a universe with these
relations, in a signature whose names are distinct. -/
theorem TypeDeclaration.AtClosedLevels.runNestRel_instances (hd : sig.Distinct)
    {decl : TypeDeclaration} {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    {hq : qs.length = decl.sorts} {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
    {a₁ a₂ : InstanceArgs 0 [] decl.scope} (hA : decl.AtClosedLevels sig ι hq hl hp a₁ a₂)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
    {as : InstanceArgs 0 [] decl.scope} {X : Name → RunRel}
    (hU : ∀ T' ∈ decl.dataTypes,
      RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as) (X T'.name)) :
    ∀ j, Nest.All
      (fun x : RunNestLeaf => RunNestRel sig ι P
        (((decl.sort (.ofLists qs ps hq hp)).atLevels
          fun i => (ls.getFin hl i).closedValue).level.closedValue)
        (fun m _ => levelRel sig ι m) .plain x.1 x.2)
      (((c.fields (.ofLists qs ps hq hp)).nestAt decl.names j).map fun D' =>
          (((decl.blockInstance (.ofLists qs ps hq hp) D' (.identity decl.scope)).atLevels
            fun i => (ls.getFin hl i).closedValue).subst as.toSubst,
            (X D').computed sig ι)) := fun j =>
  Nest.All.map_rel₃ (fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
      exact hA.sort ▸ RunNestRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m)
        (.plain (Whnf.inst ..).computes (.univ (hU T' hT'))) (hA.instances as T'.name).symm .plain)
    (Telescope.nestAt_all decl.names _ j)

-- ADE: none.
/-- `(c)` at run time, closed: a constructor of a data type of `Σ`, whose type declaration is
meaningful, applied to arguments of its fields that the meaning relates to themselves, is related at
its instance to the address of a value of its case whose fields are the addresses to which the
arguments are related, in a signature whose names are distinct: a proof of a proposition is related
to every address, and a term of a type, by `(®_μ)` unfolded once. -/
theorem RunsAs.ctor (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst)
    {ts : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      ts.toSubst ts.toSubst)
    {i : Nat} (hi : sig.constructorCase D con.name = some i) {H : Heap} {a : Nat} {bs : List Nat}
    (ha : H[a]? = some (.ctor i ((con.params (.ofLists qs ps hq hp)).map (·.usage.run))
      ((con.params (.ofLists qs ps hq hp)).map (·.requirement.run)) bs))
    (hbs : RunsAsArgs sig ι P H (Parameter.grades (con.params (.ofLists qs ps hq hp))) ts bs
      (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) :
    RunsAs sig ι P H (.ctor D qs ls ps as con.name ts.terms) a (.inst D qs ls ps as) := by
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : ∀ D', Computesι sig ι (.inst D' qs ls ps as) (.inst D' qs ls ps as) :=
    fun _ => (Whnf.inst ..).computes
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · obtain ⟨S, hS, hU⟩ := hv.runUnivRel hd hdecl hq hl hp hadm has hs P
    have hR : ∀ T' ∈ decl.dataTypes, HasRun sig ι P (.inst T'.name qs ls ps as)
        (DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S T'.name) := fun T' hT' =>
      .univ _ (levelRel_run_iff.2 (hU T' hT').1)
    have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
        RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
    have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
        ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
      fun X Y hXY => RunTelRel.block_mono hd (fun m _ => levelRel_run_mono hd m)
        (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
        (F := fun X D => (.inst D qs ls ps as, (X D).computed sig ι)) hS X Y
        fun D H _ _ => RunRel.computed_mono (hXY D H)
    refine ⟨_, hw _, .inr ⟨_, hR T hT, _, (Whnf.ctor ..).computes,
      DataType.runBlockRel_fold hmono hT ⟨con, hc, i, ts.terms, bs, ⟨qs, ls, ps, _, as, rfl⟩, hi, ha,
        ?_⟩⟩⟩
    -- The fields at the values of the levels, which the meaning of the declaration gives.
    have hA := hv.atClosedLevels hd hq hl hp hadm has
    let X : Name → RunRel := DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S
    obtain ⟨S', h₁, -⟩ := (hA.fields T hT con hc).runTelRel hd P hs fun D' => (X D').computed sig ι
    have hS' := RunTelRel.of_runsAsArgs hd h₁
      ((hs ▸ hv.nestHeads hd hdecl hT hc hq hl hp hadm has).imp
        fun _ h => h.elim fun _ h => Nest.map_eq_inst h)
      (hA.runNestRel_instances hd hT con fun T' hT' => (hU T' hT').1) _
      (fun _ _ hl hp => (Parameter.grades_of_getElem? hl).symm ▸ hp) ts
      ((hA.eqSubst_fields con as).2 hts) bs (RunsAsArgs.levelEquiv hd (hA.telescopes con as).symm hbs)
    exact (RunTelRel.congr hd (levelRel_isPer_lt hd _) ih (hS X T hT con hc) _ _ (hA.runTelRel hd h₁)
      (fun _ => Nest.rel₃_refl (fun _ _ _ _ => .rfl) _) H ts.terms bs).2 hS'
  · obtain ⟨S, hP, -⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    exact ⟨_, hw _, .inl ⟨_, _, levelRel_prop_iff.2 (hP T hT).1⟩⟩

-- ADE: none.
/-- The converse of `RunsAs.ctor`: the arguments of the fields of a constructor of a meaningful
declaration, which `(®_c)` relates to addresses at relations `X` of the recursive fields within
`(®_μ)`, are related to them, each at the type of its entry, when its grade is used at run time,
the recursive fields at the instances of the block, as the branches of a recursor read them. -/
theorem RunsAsArgs.of_fields (hd : sig.Distinct) {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    (hT : T ∈ decl.dataTypes) (hc : con ∈ T.constructors)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    {S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      RunFieldsRel}
    (hS : ∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
      RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m)
        (fun i => ((c.fields (.ofLists qs ps hq hp)).nestAt decl.names i).map
          fun D' => (.inst D' qs ls ps as, (X D').computed sig ι))
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c))
    (hU : ∀ T' ∈ decl.dataTypes,
      RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S T'.name))
    {X : Name → RunRel}
    (hX : ∀ D H t b, X D H t b →
      DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D H t b)
    {ts : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      ts.toSubst ts.toSubst)
    (g : Nat → Grade) (hg : ∀ l p, (con.params (.ofLists qs ps hq hp))[l]? = some p →
      g l ∉ Mode.oneOne.erased → p.usage ∉ Mode.oneOne.erased)
    {H : Heap} {bs : List Nat} (h : S X con H ts.terms bs) :
    RunsAsArgs sig ι P H g ts bs (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) := by
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
  -- The fields at the values of the levels, which the meaning of the declaration gives.
  have hA := hv.atClosedLevels hd hq hl hp hadm has
  -- The relations `(®_μ)` of the block relate the fields that the relations `X` within them do.
  let Y : Name → RunRel := DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S
  have hY : S Y con H ts.terms bs :=
    RunTelRel.block_mono hd (fun m _ => levelRel_run_mono hd m)
      (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
      (F := fun X D => (.inst D qs ls ps as, (X D).computed sig ι)) hS X Y
      (fun D H _ _ => RunRel.computed_mono (hX D H)) T hT con hc H _ _ h
  obtain ⟨S', h₁, -⟩ := (hA.fields T hT con hc).runTelRel hd P hs fun D' => (Y D').computed sig ι
  have hS' := (RunTelRel.congr hd (levelRel_isPer_lt hd _) ih (hS Y T hT con hc) _ _
    (hA.runTelRel hd h₁) (fun _ => Nest.rel₃_refl (fun _ _ _ _ => .rfl) _) H ts.terms bs).1 hY
  exact RunsAsArgs.levelEquiv hd (hA.telescopes con as) (RunsAsArgs.of_runTelRel h₁
    ((hs ▸ hv.nestHeads hd hdecl hT hc hq hl hp hadm has).imp
      fun _ h => h.elim fun _ h => Nest.map_eq_inst h)
    (hA.runNestRel_instances hd hT con hU) g hg ts ((hA.eqSubst_fields con as).2 hts) bs hS')

-- ADE: none.
/-- `(c)` at run time: a constructor of a data type of `Σ`, whose type declaration is meaningful,
applied to arguments of its fields valid at run time with the grades `γ`, is valid at run time at its
instance with the grades `γ`, in a signature whose names are distinct: its erasure evaluates its
arguments, then allocates a value of its case with their addresses, the same in every environment
that binds the scope through a renaming. -/
theorem RunValidRen.ctor (hd : sig.Distinct) {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ}
    {γ : GradeVector Γ.length} {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {ts : Args 0 Γ (con.params (.ofLists qs ps hq hp))}
    (hts : ValidArgsΓ sig ι ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
    (hrun : RunValidArgsRen sig ι P hΓ ctx γ ts
      (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) :
    RunValidRen sig ι P hΓ ctx γ (.ctor D qs ls ps as con.name ts.terms) (.inst D qs ls ps as) := by
  intro w σ H E V hσ hEV hE _ g E' hg
  have hfg := hd.fieldParams h hc hq hp
  obtain ⟨hdecl, hT, rfl⟩ := h
  obtain ⟨i, hi⟩ := Signature.constructorCase_of_mem hdecl hT hc
  have he : (Term.ctor T.name qs ls ps as con.name ts.terms).erase sig Mode.oneOne.erased hΓ =
      .ctor i (ts.terms.erase sig Mode.oneOne.erased hΓ (con.params (.ofLists qs ps hq hp))) := by
    rw [Term.erase, hi, hfg]
    rfl
  obtain ⟨bs, H', R, hevs, hH', hruns⟩ := hrun w σ H E V hσ hEV hE g E' hg
  have hev := Eval.ctor (i := i) hevs
  rw [Targets.multiplicities_rename, Targets.requirements_rename,
    Args.multiplicities_erase sig Mode.oneOne.erased hΓ ts,
    Args.requirements_erase sig Mode.oneOne.erased hΓ ts] at hev
  have hH'' : H'.Extends
      (H' ++ [.ctor i ((con.params (.ofLists qs ps hq hp)).map (·.usage.run))
        ((con.params (.ofLists qs ps hq hp)).map (·.requirement.run)) bs]) :=
    List.prefix_append _ _
  refine ⟨H'.length, _, R, by rw [he]; exact hev, hH'.trans hH'', ?_⟩
  have hts' := hts.2 σ σ hσ
  rw [Constructor.fieldsAt_subst] at hts' hruns
  have hc' := RunsAs.ctor hd ⟨hdecl, hT, rfl⟩ hv hc hq hl hp hadm (has.2 σ σ hσ) hts' hi
    List.getElem?_concat_length (hruns.mono hd hH'')
  rw [Args.terms_subst] at hc'
  exact hc'

end

end Sic.Core
