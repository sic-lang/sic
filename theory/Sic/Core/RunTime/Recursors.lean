module

public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Computation
import Sic.Core.RunTime.DeclaredTypes
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Skeleton
import Sic.Core.RunTime.Substitution
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Run Time of the Recursors

The recursors at run time: the erasure of a recursor evaluates its term, or the skeleton of its
instance when its grade is erased, then eliminates the value of the case of its constructor by the
branch of the case, with its fields and its recursive results, each the recursor on its recursive
field, or `↯` when its grade is erased.

When the grade of the recursor is used at run time, the term of the recursor is related to the
address of its value at its instance, by `(®_μ)`, the least relations closed under its clauses: the
relations of the canonical terms that `(®_μ)` relates and on whose addresses the recursor evaluates
to the address of a value related to the recursor at the motive are closed, since the recursor on a
constructor steps to its branch, at the terms of the fields and at the recursive results, which
these relations relate to the addresses of the fields and of the results.

ADE prove the validity of their recursors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Evaluation -/

/-- A cast of the number of variables of a term of the target language keeps its evaluations. -/
theorem Eval.cast {n m : Nat} (h : n = m) {H H' : Heap} {E : List Nat} {M : Target n} {a : Nat} :
    Eval P H E (h ▸ M) a H' ↔ Eval P H E M a H' := by
  subst h
  rfl

/-! ## Signatures -/

/-- In a signature whose names are distinct, the case of a constructor of a data type is a case of
the block of its declaration with this constructor. -/
theorem Signature.Distinct.cases_of_constructorCase (hd : sig.Distinct) {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType T.name decl T) (hc : con ∈ T.constructors) {i : Nat}
    (hi : sig.constructorCase T.name con.name = some i) :
    ∃ j, decl.cases[i]? = some (j, T, con) := by
  obtain ⟨hdecl, hT, -⟩ := h
  rw [hd.constructorCase ⟨hdecl, hT, rfl⟩] at hi
  obtain ⟨⟨j', T', con'⟩, hx, hpx⟩ := List.getElem?_of_findIdx?_eq_some hi
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hm : (j, T, con) ∈ decl.cases := by
    have := TypeDeclaration.mem_casesFrom_of (i := 0) (f := DataType.constructors) hj hc
    rwa [Nat.zero_add] at this
  have hn : T'.name = T.name ∧ con'.name = con.name := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hpx
    exact hpx
  have he := List.eq_of_nodup_map (f := fun x => (x.2.1.name, x.2.2.name))
    (hd.cases_nodup hdecl) (List.mem_of_getElem? hx) hm
    (show (T'.name, con'.name) = (T.name, con.name) by rw [hn.1, hn.2])
  exact ⟨j, he ▸ hx⟩

/-- A constructor of a type of a block is in a case of the block, with the position of its type. -/
theorem TypeDeclaration.exists_cases {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hcon : con ∈ T.constructors) :
    ∃ i j : Nat, decl.cases[i]? = some (j, T, con) ∧ decl.dataTypes[j]? = some T := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hmem : (j, T, con) ∈ decl.cases := by
    have := TypeDeclaration.mem_casesFrom_of (i := 0) hj hcon
    rwa [Nat.zero_add] at this
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  exact ⟨i, j, hi, hj⟩

/-! ## Erasure -/

/-- The branch at a position of the erased branches of a recursor is the erasure of the branch at
this position, with the positions of its recursive fields that the erasure gives, each `none` when
the grade of its result is erased. -/
theorem Branches.get_erase (sig : Signature) (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) : (us : Branches k Γ) → (es : List (List Nat)) →
    {i n m : Nat} → {u : Term k ((Γ.extend n).extend m)} → us.get i = some ⟨n, m, u⟩ →
    ∃ gs : Vector Grade m, us.grades i = gs.toList ∧ (us.erase sig S hΓ es).get i =
      some ⟨n, m, fun j => if gs[j] ∈ S then none else ((es.drop i).headD [])[(j : Nat)]?,
        Scope.length_extend_extend Γ n m ▸ u.erase sig S ((hΓ.extend n).extend m)⟩
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons _ _ gs _ _, _, 0, _, _, _, h => by
    cases h
    exact ⟨gs, rfl, rfl⟩
  | .cons _ _ _ _ us, es, i + 1, _, _, _, h => by
    obtain ⟨gs, h₁, h₂⟩ := Branches.get_erase sig S hΓ us es.tail h
    have he : es.drop (i + 1) = es.tail.drop i := by
      cases es
      · exact List.drop_nil.trans List.drop_nil.symm
      · rfl
    exact ⟨gs, h₁, he ▸ h₂⟩

/-- The positions of the recursive fields that the types `rs` of the block mark, from the position
`o`, are as many as the recursive results. -/
theorem Telescope.length_positions : (rs : List (Option Name)) → {ps : List Parameter} →
    rs.length = ps.length → (o : Nat) →
    ((rs.zipIdx o).filterMap fun y => y.1.map fun _ => y.2).length =
      (Telescope.resultParams rs ps).length
  | [], [], _, _ => rfl
  | some _ :: rs, _ :: _, h, o =>
    congrArg (· + 1) (Telescope.length_positions rs (Nat.succ.inj h) (o + 1))
  | none :: rs, _ :: _, h, o => Telescope.length_positions rs (Nat.succ.inj h) (o + 1)

/-- A field that is not recursive has no recursive result, whose grade is then `0`. -/
theorem Telescope.resultGrades_of_none : (rs : List (Option Name)) → (es : List Grade) →
    (l : Nat) → rs[l]?.join = none → Telescope.resultGrades rs es l = Grade.zero
  | [], _, _, _ => rfl
  | some _ :: _, _, 0, h => nomatch h
  | some _ :: rs, [], l + 1, h => by
    rw [Telescope.resultGrades_nil]
  | some _ :: rs, _ :: es, l + 1, h => Telescope.resultGrades_of_none rs es l h
  | none :: _, _, 0, _ => rfl
  | none :: rs, es, l + 1, h => Telescope.resultGrades_of_none rs es l h

/-- Arguments related to addresses are as many as the addresses. -/
theorem RunsAsArgs.length {H : Heap} : {ps : List Parameter} → {g : Nat → Grade} →
    {ts : Args 0 [] ps} → {bs : List Nat} → {Θ : Telescope 0 [] ps} →
    RunsAsArgs sig ι P H g ts bs Θ → bs.length = ps.length
  | [], _, .nil, [], .nil, _ => rfl
  | _ :: _, _, .cons _ _, _ :: _, .cons _ _ _ _, h => congrArg (· + 1) (RunsAsArgs.length h.2)
  | [], _, .nil, _ :: _, .nil, h => (h : False).elim
  | _ :: _, _, .cons _ _, [], .cons _ _ _ _, h => (h : False).elim

/-- Terms related to themselves at the recursive fields by `Q` are related to themselves by `Q'`,
when `Q'` relates each term to itself that `Q` does. -/
theorem Terms.RecRel.of_diag {Q Q' : Name → TermRel} :
    (rs : List (Option Name)) → {ts : Terms 0 []} →
      (∀ D, some D ∈ rs → ∀ t, Q D t t → Q' D t t) → Terms.RecRel Q rs ts ts →
        Terms.RecRel Q' rs ts ts
  | some D :: rs, .cons _ _, h, hqs =>
    ⟨h D (List.mem_cons_self ..) _ hqs.1,
      Terms.RecRel.of_diag rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hqs.2⟩
  | none :: rs, .cons _ _, h, hs =>
    Terms.RecRel.of_diag (Q := Q) rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hs
  | [], _, _, _ | some _ :: _, .nil, _, _ | none :: _, .nil, _, _ => trivial

/-! ## Recursive Results -/

/-- `Q` holds of the terms `ts` of the fields of the types `rs` of a block, at their addresses `bs`,
at each recursive field whose result, at its grade in `es`, is used at run time. -/
def Terms.RecAt (Q : Name → Term 0 [] → Nat → Prop) :
    List (Option Name) → List Grade → Terms 0 [] → List Nat → Prop
  | some D :: rs, e :: es, .cons t ts, b :: bs =>
    (e ∉ Mode.oneOne.erased → Q D t b) ∧ Terms.RecAt Q rs es ts bs
  | none :: rs, es, .cons _ ts, _ :: bs => Terms.RecAt Q rs es ts bs
  | _, _, _, _ => True

/-- The fields that the relation of run time of a telescope relates to their addresses in the heap
`H₀` satisfy `Q` at each recursive field whose result is used at run time, when the relation of each
recursive field, at its type `D`, implies `Q` on the terms that `V D` holds of, and when the field of
each result used at run time is used too. -/
theorem RunTelRel.recAt {n : Nat} {below : LevelRel.Below n} {Q : Name → Term 0 [] → Nat → Prop}
    {V : Name → Term 0 [] → Prop} {H₀ : Heap} :
    {rs' : Nat → Option RunRel} → {ps : List Parameter} → {Θ : Telescope 0 [] ps} →
    {S : RunFieldsRel} → RunTelRel sig ι P n below rs' Θ S → (rsN : List (Option Name)) →
    rsN.length = ps.length → (∀ i, rs' i = none → ∀ D, rsN[i]? ≠ some (some D)) →
    (∀ i R, rs' i = some R → ∃ D, rsN[i]? = some (some D) ∧ ∀ t b, R H₀ t b → V D t → Q D t b) →
    (ts : Args 0 [] ps) → (bs : List Nat) → S H₀ ts.terms bs →
    Terms.RecRel (fun D t _ => V D t) rsN ts.terms ts.terms → (es : List Grade) →
    (∀ l (p : Parameter), ps[l]? = some p → Telescope.resultGrades rsN es l ∉ Mode.oneOne.erased →
      p.usage ∉ Mode.oneOne.erased) →
    Terms.RecAt Q rsN es ts.terms bs
  | _, [], .nil, _, .nil, rsN, hlen, _, _, .nil, _, _, _, _, _ => by
    cases rsN with
    | nil => trivial
    | cons => cases hlen
  | _, p :: ps, .cons _ _ _ Θ, _, .cons _ _ _ G hG hrs0, rsN, hlen, hnone, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨⟨hFt, -⟩, hGt⟩ := hS
    cases rsN with
    | nil => cases hlen
    | cons x rsN =>
    cases x with
    | some D => exact (hnone 0 hrs0 D rfl).elim
    | none =>
    exact RunTelRel.recAt (hG t hFt) rsN (Nat.succ.inj hlen) (fun i => hnone (i + 1))
      (fun i => hrs (i + 1)) ts bs hGt hV es (fun l => hg (l + 1))
  | _, p :: ps, .cons _ _ _ Θ, _, .recursive hrs0 G hG, rsN, hlen, hnone, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨hb, hGt⟩ := hS
    obtain ⟨D, hD, hQ⟩ := hrs 0 _ hrs0
    cases rsN with
    | nil => cases hD
    | cons x rsN =>
    cases hD
    cases es with
    | nil => trivial
    | cons e es =>
    obtain ⟨hVt, hV'⟩ := hV
    exact ⟨fun he => hQ t b (hb (hg 0 p rfl he)) hVt,
      RunTelRel.recAt (hG t) rsN (Nat.succ.inj hlen) (fun i => hnone (i + 1))
        (fun i => hrs (i + 1)) ts bs hGt hV' es (fun l => hg (l + 1))⟩

/-- The recursive results of a branch at run time, by induction on the fields: from the addresses
`bs` of the fields, the last of the addresses `bsAll` from the position `o`, the recursive results
evaluate, in each heap that extends `H₀`, to addresses related to the results `f D t` at the
motives at their fields, each at its grade in `es`, when the recursor on each recursive field `t` of
the type `D` whose result is used evaluates, in each such heap, to such an address. -/
theorem Args.evalResults (hd : sig.Distinct) {m : Nat} {Ns : TargetBranches m} {E : List Nat}
    {f : Name → Term 0 [] → Term 0 []} {names : List Name} {Cs : Motives 0 []} {H₀ : Heap}
    {bsAll : List Nat} :
    {ps : List Parameter} → (rsN : List (Option Name)) → rsN.length = ps.length →
    (ts : Args 0 [] ps) → (o : Nat) → (bs : List Nat) → bsAll.drop o = bs →
    bs.length = ps.length → (es : List Grade) →
    es.length = (Telescope.resultParams rsN ps).length →
    Terms.RecAt (fun D t b => ∀ H', H₀.Extends H' → ∃ v H₂, EvalRec P H' E Ns b v H₂ ∧
      H'.Extends H₂ ∧ ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        RunsAs sig ι P H₂ (f D t) v (C.subst₀ (Subst₀.single t))) rsN es ts.terms bs →
    {R : Telescope 0 [] (Telescope.resultParams rsN ps)} →
    Motives.results names Cs rsN ts.terms = some R →
    ∀ H', H₀.Extends H' → ∃ vs H₂, EvalResults P H' E Ns bsAll
      (List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then none else some l) es
        ((rsN.zipIdx o).filterMap fun y => y.1.map fun _ => y.2)) vs H₂ ∧ H'.Extends H₂ ∧
      RunsAsArgs sig ι P H₂ (fun j => es.getD j Grade.zero) (ts.results f rsN) vs R
  | [], rsN, hlen, .nil, _, _, _, _, es, _, _, R, hR, H', _ => by
    cases rsN with
    | cons _ _ => cases hlen
    | nil =>
      unfold Motives.results at hR
      cases hR
      refine ⟨[], H', ?_, List.prefix_refl H', trivial⟩
      show EvalResults P H' E Ns bsAll (List.zipWith _ es []) [] H'
      rw [List.zipWith_nil_right]
      exact .nil
  | _ :: _, [], hlen, _, _, _, _, _, _, _, _, _, _, _, _ => by cases hlen
  | _ :: _, _ :: _, _, .cons _ _, _, [], _, hbl, _, _, _, _, _, _, _ => by cases hbl
  | p :: ps, none :: rsN, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, H',
      hH' => by
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    unfold Motives.results at hR
    exact Args.evalResults hd rsN (Nat.succ.inj hlen) ts (o + 1) bs hdrop' (Nat.succ.inj hbl) es
      hes hQ hR H' hH'
  | p :: ps, some D :: rsN, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, H',
      hH' => by
    cases es with
    | nil => cases hes
    | cons e es =>
    obtain ⟨hQt, hQ'⟩ := hQ
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    have hbo : bsAll[o]? = some b := by
      have h0 := congrArg (·[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero] at h0
      exact h0
    simp only [Args.terms] at hR
    unfold Motives.results at hR
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at hR; cases hR
    | some a =>
    obtain ⟨k, C⟩ := a
    cases k with
    | succ => simp only [hC] at hR; cases hR
    | zero =>
    simp only [hC] at hR
    obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 hR
    -- The rest of the results, at the result `f D t`, are the results of the rest of the fields.
    have hR'' : Motives.results names Cs rsN (ps := ps) ts.terms =
        some (R'.subst₀ (Subst₀.single (f D t))) := by
      let σ₀ : Subst 0 [] [] := fun x => nomatch x
      have h := Motives.results_subst names (Subst₀.toSubst (Subst₀.single (f D t))) rsN hR'
      rw [Motives.subst_rename_of (θ' := σ₀) (fun x => by cases x),
        Motives.subst_id_of (fun x => by cases x), Terms.subst_rename_of (θ' := σ₀)
          (fun x => by cases x), Terms.subst_id_of (fun x => by cases x),
        ← Telescope.subst₀_eq_subst] at h
      exact h
    have hlen' : rsN.length = ps.length := Nat.succ.inj hlen
    have hbl' : bs.length = ps.length := Nat.succ.inj hbl
    have hes' : es.length = (Telescope.resultParams rsN ps).length := Nat.succ.inj hes
    by_cases he : e ∈ Mode.oneOne.erased
    · have hH'' : H'.Extends (H' ++ [.erased]) := List.prefix_append _ _
      obtain ⟨vs, H₂, hevs, hH₂, hruns⟩ := Args.evalResults hd rsN hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' _ (hH'.trans hH'')
      refine ⟨H'.length :: vs, H₂, ?_, hH''.trans hH₂, fun h => (h he).elim, hruns⟩
      show EvalResults P H' E Ns bsAll
        ((if e ∈ Mode.oneOne.erased then none else some o) :: _) _ H₂
      rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
      exact .erased hevs
    · obtain ⟨v, H₂, hev, hH₂, hrun⟩ := hQt he H' hH'
      obtain ⟨vs, H₃, hevs, hH₃, hruns⟩ := Args.evalResults hd rsN hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' _ (hH'.trans hH₂)
      refine ⟨v :: vs, H₃, ?_, hH₂.trans hH₃, fun _ => (hrun C hC).mono hd hH₃, hruns⟩
      show EvalResults P H' E Ns bsAll
        ((if e ∈ Mode.oneOne.erased then none else some o) :: _) _ H₃
      rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
      exact .recursor hbo hev hevs

/-! ## Recursors -/

section

variable {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {decl : TypeDeclaration} {D : Name}
  {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {as : InstanceArgs 0 Γ decl.scope} {r : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
  {χ : GradeVector Γ.length} {δs : Nat → GradeVector Γ.length} {gs : Nat → Nat → Grade}
  {κ : Universe 0}

/-- The branches of a recursor are valid at run time: each branch, in the context extended by the
fields of its constructor and by its recursive results, at the grades of its variables. -/
def RunValidBranches (sig : Signature) (ι : Interpretation) (P : Program) (hΓ : Γ.FirstOrder)
    (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) (as : InstanceArgs 0 Γ decl.scope) (Cs : Motives 0 Γ)
    (us : Branches 0 Γ) (δs : Nat → GradeVector Γ.length) (gs : Nat → Nat → Grade) : Prop :=
  ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
    con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
    us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
      (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
    RunValid sig ι P ((hΓ.extend _).extend _)
      ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
      (((δs i).extendGrades (gs i) (con.params (.ofLists qs ps hq hp))).extendResults
        (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)
        (con.params (.ofLists qs ps hq hp))) u
      ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
        (Ren.weakenN _))

/-- The motives of a block of data types, one for each type, give one to each name of the block. -/
theorem Motives.get_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩) {D' : Name}
    (hD' : D' ∈ decl.names) : ∃ C, Cs.get (decl.names.idxOf D') = some ⟨0, C⟩ := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  rw [TypeDeclaration.idxOf_dataTypes hnd hj]
  exact hCs j T' hj

/-- The motive of a name of a block of data types in its motives substituted by `σ` is the motive of
the type of this name, substituted. -/
theorem Motives.get_subst_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (σ : Subst 0 [] Γ) {D' : Name} (hD' : D' ∈ decl.names) {C}
    (hC : (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩) :
    ∃ j T' C', decl.dataTypes[j]? = some T' ∧ T'.name = D' ∧ Cs.get j = some ⟨0, C'⟩ ∧
      C = C'.subst (Subst.lift σ) := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  obtain ⟨C', hC'⟩ := hCs j T' hj
  rw [TypeDeclaration.idxOf_dataTypes hnd hj, Motives.get_subst σ hC'] at hC
  cases hC
  exact ⟨j, T', C', hj, rfl, hC', rfl⟩

/-- A recursor on a term is related at the motive at the term as on the value of the term. -/
theorem RunsAs.recursor_of_redStar (hd : sig.Distinct)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r T'.name qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    {σ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ σ) {j : Nat}
    {T' : DataType decl.sorts decl.grades decl.levels decl.scope} {C' : Term 0 (.var :: Γ)}
    (hj : decl.dataTypes[j]? = some T') (hCj : Cs.get j = some ⟨0, C'⟩) {t v : Term 0 []}
    (htv : RedStar (sig.interpret ι) t v)
    (hvt : ValidTerm₀ sig ι t (.inst T'.name qs ls ps (as.subst σ))) {H : Heap} {b : Nat}
    (hrun : RunsAs sig ι P H
      (.recursor r T'.name qs ls ps (as.subst σ) v (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))) :
    RunsAs sig ι P H (.recursor r T'.name qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  have hvv := (ValidEqTerm₀.redStar_iff hd htv).1 hvt
  have hrv := hrec j T' C' hj hCj σ hσ v (hvv.trans hvv.symm)
  have hmot := (hCv j T' C' hj hCj).motive hσ hvv
  exact (RunsAs.redStar_iff hd (RedStar.recursor htv)).2 (hrun.conv hd hrv.2 hmot.2)

/-- The erased recursor eliminates the address of a constructor of a type of the block, by the
branch of its case, to the address of a value to which the recursor on a term of the instance that
computes to this constructor is related at the motive at the term, when the fields of the
constructor are related to their addresses at their grades in the branch, and the recursive
results used at run time evaluate to addresses related to them. -/
theorem RunsAs.recursor_ctor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r T'.name qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {σ : Subst 0 [] Γ} {H : Heap}
    {E : List Nat} (hσ : EqSubst sig ι ctx σ σ) (hE : RunsAsSubst sig ι P H ctx χ σ E)
    {i j : Nat} {T' : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T') (hcon : con ∈ T'.constructors)
    (hi : decl.cases[i]? = some (j, T', con)) {fs : Terms 0 []} {w : Term 0 []}
    (hw : w.IsCtor T'.name con.name fs)
    (hwv : ValidTerm₀ sig ι w (.inst T'.name qs ls ps (as.subst σ))) {H' : Heap}
    (hH' : H.Extends H') {a : Nat} {bs : List Nat} (ha : H'[a]? = some (.ctor i bs))
    (hfr : ∀ ts : Args 0 [] (con.params (.ofLists qs ps hq hp)), ts.terms = fs →
      EqSubst sig ι (Context.empty.append
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ))) ts.toSubst ts.toSubst →
      Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms →
      RunsAsArgs sig ι P H' (gs i) ts bs
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)) ∧
      Terms.RecAt (fun D' t b => ∀ H'', H'.Extends H'' → ∃ v H₂,
        EvalRec P H'' E (us.erase sig Mode.oneOne.erased hΓ
          ((sig.recursiveFields D qs ps).getD [])) b v H₂ ∧ H''.Extends H₂ ∧
        ∀ C, (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩ →
          RunsAs sig ι P H₂ (.recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)) v
            (C.subst₀ (Subst₀.single t)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) (us.grades i) ts.terms bs) :
    ∃ v H₃, EvalRec P H' E (us.erase sig Mode.oneOne.erased hΓ
        ((sig.recursiveFields D qs ps).getD [])) a v H₃ ∧ H'.Extends H₃ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ →
        RunsAs sig ι P H₃ (.recursor r T'.name qs ls ps (as.subst σ) w (Cs.subst σ) (us.subst σ))
          v ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hT' : T' ∈ decl.dataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  -- The meaning of the constructor gives the arguments of its fields.
  obtain ⟨qs', ls', ps', Δ', as', rfl⟩ := hw
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ := hwv.2.1 fun ⟨v, hv', _, _, hk⟩ => by
    cases Computesι.det hd (hI _) hv'
    exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hUM T' hT').1) hk
  cases Computesι.det hd (hI _) hv'
  cases Computesι.det hd hw₁ ⟨.refl _, .ctor _ _ _ _ _ _ _⟩
  have hrel' := (HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T' hT').1)) _ _).1 hrel
  obtain ⟨T'', hT'', hn'', con'', hcon'', fs₁, fs₂, hv₁, -, hS''⟩ :=
    DataType.blockRel_inv hmonoM hrel'
  cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT'' hT' hn''
  obtain ⟨-, hcn, rfl⟩ := hv₁.inj ⟨_, _, _, _, _, rfl⟩
  cases List.eq_of_nodup_map (hd.constructors_nodup ⟨hdecl, hT', rfl⟩) hcon'' hcon hcn
  have hself := (hiffM T' hT' con hcon).2.2 _ _ hS''
  obtain ⟨ts, -, rfl, -, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hself
  have hts := ((hiffM T' hT' con hcon).1 ts ts).1 hself
  have hrecV : Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms :=
    Terms.RecRel.mono _ (fun D hD t₁ t₂ h₁₂ => by
        obtain ⟨T₃, hT₃, rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.mem_recursion hD)
        have h' := hval T₃ hT₃ t₁ t₂ h₁₂
        exact h'.trans h'.symm)
      (hrecM _ T' hT' con hcon _ _ hself)
  obtain ⟨hfa, hQ⟩ := hfr ts rfl hts hrecV
  -- The case of the constructor, its branch and its recursive results.
  obtain ⟨u, hu⟩ := hus i j T' con hi
  obtain ⟨Rt, hRt⟩ := Constructor.results_isSome con (.ofLists qs ps hq hp)
    (fun _ hD' => Motives.get_idxOf hT hnd hCs hD')
  obtain ⟨gs₀, hgs, hget⟩ := Branches.get_erase sig Mode.oneOne.erased hΓ us
    ((sig.recursiveFields T.name qs ps).getD []) hu
  -- The positions of the recursive fields of each case.
  let rfs : List (List Nat) := decl.cases.map fun x =>
    ((x.2.2.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
      fun y => y.1.map fun _ => y.2
  have hrfs : (sig.recursiveFields T.name qs ps).getD [] = rfs := by
    rw [hd.recursiveFields ⟨hdecl, hT, rfl⟩ hq hp]
    rfl
  rw [hrfs] at hQ hget ⊢
  rw [hgs] at hQ
  have hpos : (rfs.drop i).headD [] =
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
        fun y => y.1.map fun _ => y.2 :=
    List.headD_drop (by rw [List.getElem?_map, hi]; rfl)
  obtain ⟨vs, H₂, hevs, hH₂, hruns⟩ := Args.evalResults hd
    ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) (Telescope.length_recursion _ _)
    ts 0 bs List.drop_zero (RunsAsArgs.length hfa) gs₀.toList gs₀.length_toList hQ
    (Constructor.results_subst_append hRt σ ts) H' (List.prefix_refl _)
  -- The branch, at the substitution of its context by `σ`, the fields and the results.
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)
  have hres := EqSubst.results (sig := sig) (ι := ι) (f₁ := f) (f₂ := f) _ ts ts
    (Constructor.results_subst_append hRt σ ts)
    (Terms.RecRel.of_diag _ (fun D hD t₁ hVt C hC => by
        obtain ⟨j₃, T₃, C₃, hj₃, rfl, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ
          (Telescope.mem_recursion hD) hC
        exact hrec j₃ T₃ C₃ hj₃ hC₃ σ hσ t₁ hVt) hrecV)
  have hEqbr := (EqSubst.append_append_iff _ Rt _ _ _ _).2
    ⟨(EqSubst.append_append_iff ctx _ σ σ _ _).2
      ⟨hσ, by rw [Constructor.fieldsAt_subst]; exact hts⟩, hres⟩
  have hχi : RunsAsSubst sig ι P H₂ ctx (δs i) σ E :=
    RunsAsSubst.of_counted ctx (fun x hδ => (by decide : ∀ c d x : Grade,
        c ≤ d + x → d ∉ Mode.oneOne.erased → c ∉ Mode.oneOne.erased) _ _ _
        (hχ i j T' con hi x) hδ) (hE.mono hd (hH'.trans hH₂))
  have hfa₂ : RunsAsArgs sig ι P H₂ (gs i) ts bs
      ((con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as).subst σ) := by
    rw [Constructor.fieldsAt_subst]
    exact hfa.mono hd hH₂
  have hσr := RunsAsSubst.append _ Rt (RunsAsSubst.append ctx _ hχi hfa₂) hruns
  obtain ⟨C', hC'⟩ : ∃ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ := hCs j T' hj
  have hbr := husr i j T' con C' Rt u hi hC' hRt hu
  rw [Branches.resultGrades, hgs, GradeVector.extendResults_resultGrades] at hbr
  obtain ⟨v, H₃, hev, hH₃, hrun⟩ := hbr _ H₂ _ hEqbr hσr
  -- The erased recursor steps to the erased branch.
  have hks : List.ofFn (fun j : Fin (con.resultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then none else ((rfs.drop i).headD [])[(j : Nat)]?) =
      List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then none else some l) gs₀.toList
        ((((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx 0).filterMap
          fun y => y.1.map fun _ => y.2) := by
    rw [hpos]
    exact List.ofFn_ite_getElem? _ gs₀ _
      (Telescope.length_positions _ (Telescope.length_recursion _ _) 0)
  refine ⟨v, H₃, .iota ha hget (RunsAsArgs.length hfa) (hks ▸ hevs)
    ((Eval.cast _).2 (by rw [List.append_assoc]; exact hev)), hH₂.trans hH₃, fun C'' hC'' => ?_⟩
  rw [hC'] at hC''
  cases hC''
  -- The recursor on the constructor steps to the branch, at the motive at the constructor.
  rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hrun
  have hrun₁ := (RunsAs.redStar_iff hd
    (.step (Red.iota_subst (D' := T'.name) (qs'' := qs') (ls'' := ls') (ps'' := ps') (as := as')
      ⟨hdecl, hT', rfl⟩ hi σ hq hp ts hu) (.refl _))).2 hrun
  have hca : ValidEqTerm₀ sig ι
      (.ctor T'.name qs ls ps (as.subst σ) con.name ts.terms)
      (.ctor T'.name qs' ls' ps' as' con.name ts.terms) (.inst T'.name qs ls ps (as.subst σ)) :=
    hval T' hT' _ _ ⟨_, _, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩,
      DataType.blockRel_closed hmonoM hT' ⟨con, hcon, ts.terms, ts.terms, ⟨_, _, _, _, _, rfl⟩,
        ⟨_, _, _, _, _, rfl⟩, hself⟩⟩
  have hmot := (hCv j T' C' hj hC').motive hσ hca
  have hrw := hrec j T' C' hj hC' σ hσ _ hwv
  exact hrun₁.conv hd (hrw.conv hmot.symm).2 hmot.2

/-- `r ∉ S`, by induction on `(®_μ)`: the erased recursor eliminates the address of a term of the
instance related to it to the address of a value to which the recursor on the term is related at
the motive at the term. -/
theorem RunsAs.recursor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {h' : Nat} {C : Term 0 (.var :: Γ)} (hh : decl.dataTypes[h']? = some T)
    (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r T'.name qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
          (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)) l
          else Grade.zero) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∉ Mode.oneOne.erased) {σ : Subst 0 [] Γ} {H : Heap} {E : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hE : RunsAsSubst sig ι P H ctx χ σ E) {H₁ : Heap}
    (hH₁ : H.Extends H₁) {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ))
    (ht : RunsAs sig ι P H₁ t a ((Term.inst D qs ls ps as).subst σ)) :
    ∃ b H₂, EvalRec P H₁ E (us.erase sig Mode.oneOne.erased hΓ
        ((sig.recursiveFields D qs ps).getD [])) a b H₂ ∧ H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ (.recursor r D qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The relations of run time of the block at the arguments substituted.
  obtain ⟨S, hS, hU⟩ := hv.runUnivRel hd hdecl hq hl hp hadm hasσ hs P
  have ihmono : ∀ m,
      m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
  have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
    fun X Y hXY T hT c hc H =>
      RunTelRel.mono hd ihmono (List.prefix_refl H) (hS X T hT c hc) _ _ (hS Y T hT c hc)
        (fun _ => Option.rel_map (fun D' _ _ => RunRel.computed_mono (hXY D' H)) _)
  let Ns := us.erase sig Mode.oneOne.erased hΓ ((sig.recursiveFields T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)
  -- The relations of the canonical terms that `(®_μ)` relates and on whose addresses the erased
  -- recursor evaluates, in each heap that extends `H`, to the address of a value related to the
  -- recursor at the motive.
  let X : Name → RunRel := fun D' H₀ w a => DataType.runBlockRel sig decl.dataTypes S D' H₀ w a ∧
    ∀ H', H₀.Extends H' → H.Extends H' →
      ValidTerm₀ sig ι w (.inst D' qs ls ps (as.subst σ)) →
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        ∃ b H₂, EvalRec P H' E Ns a b H₂ ∧ H'.Extends H₂ ∧
          RunsAs sig ι P H₂ (f D' w) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w))
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ H₀ w a, T'.runCtorRel sig T'.name (S X) H₀ w a →
      X T'.name H₀ w a := by
    intro T' hT' H₀ w a hc
    have hcb := DataType.runCtorRel_mono (List.prefix_refl H₀)
      (fun c hc' ts bs => hmono X _ (fun _ _ _ _ h => h.1) T' hT' c hc' H₀ ts bs) hc
    refine ⟨DataType.runBlockRel_fold hmono hT' hcb, fun H' hH' hHH' hwv C' hC' => ?_⟩
    obtain ⟨con, hcon, i, fs, bs, hw, hi, ha, hSX⟩ := hc
    -- The case of the constructor.
    obtain ⟨j₀, hij⟩ := hd.cases_of_constructorCase ⟨hdecl, hT', rfl⟩ hcon hi
    obtain ⟨i', j, hi', hj⟩ := TypeDeclaration.exists_cases hT' hcon
    obtain rfl : i = i' := List.getElem?_inj_of_nodup_map (hd.cases_nodup hdecl) hij hi' rfl
    rw [hidx j T' hj] at hC'
    obtain ⟨v, H₃, hev, hH₃, hrun⟩ := RunsAs.recursor_ctor hd ⟨hdecl, hT, rfl⟩ hv hadm has hCs
      hCv hus hrec husr hχ hs hσ hE hj hcon hi' hw hwv hHH' (hH'.getElem? ha)
      fun ts hfs hts hrecV => by
        subst hfs
        -- The fields, related at their types.
        refine ⟨(RunsAsArgs.of_fields hd hv hT' hcon hq hl hp hadm hasσ hs hS
          (fun T' hT' => (hU T' hT').1) (fun _ _ _ _ h => h.1) hts (gs i)
          (fun l p hl' hgl => (by decide : ∀ r p g x : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + x * r → g ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased) r p.usage
            (gs i l) _ hr (hg i j T' con l p hi' hl') hgl) hSX).mono hd hH', ?_⟩
        -- The recursive results used at run time, of fields that `X` relates.
        refine RunTelRel.recAt (hS X T' hT' con hcon) _ (Telescope.length_recursion _ _)
          (fun l hl D hD => by
            simp only [Telescope.recursionAt, hD, Option.join_some, Option.map_some] at hl
            cases hl)
          (fun l R hR => ?_) ts bs hSX hrecV _
          (fun l p hl' he => by
            cases hrA : (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l with
            | none =>
              exact (he ((Telescope.resultGrades_of_none _ _ l hrA).symm ▸
                (by decide : Grade.zero ∈ Mode.oneOne.erased))).elim
            | some D =>
              have h₁ := hg i j T' con l p hi' hl'
              rw [hrA, Option.isSome_some, ite_eq_left_of_eq_true _ _ (eq_true rfl),
                Branches.resultGrades] at h₁
              exact (by decide : ∀ r p g e : Grade, r ∉ Mode.oneOne.erased →
                r * p ≤ g + e * r → e ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased)
                r p.usage _ _ hr h₁ he)
        cases hr' : (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l with
        | none => simp only [hr', Option.map_none] at hR; cases hR
        | some D =>
        simp only [hr', Option.map_some] at hR
        cases hR
        have hD : ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)[l]? =
            some (some D) := by
          simp only [Telescope.recursionAt] at hr'
          cases hx : ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)[l]? with
          | none => simp only [hx, Option.join_none] at hr'; cases hr'
          | some x =>
            simp only [hx, Option.join_some] at hr'
            rw [hr']
        refine ⟨D, hD, fun t b ⟨v, hcv, hXv⟩ hVt H'' hH'' => ?_⟩
        have hDn := Telescope.recursionAt_mem hr'
        obtain ⟨C₃, hC₃⟩ := Motives.get_idxOf hT hnd hCs hDn
        obtain ⟨j₃, T₃, C₃', hj₃, rfl, hC₃', -⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn (Motives.get_subst σ hC₃)
        rw [hidx j₃ T₃ hj₃, hC₃'] at hC₃
        cases hC₃
        have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        obtain ⟨b', H₃, hev, hH₃, hrun⟩ := hXv.2 H'' (hH'.trans hH'') (hHH'.trans hH'')
          (hvv.trans hvv.symm) C₃ ((hidx j₃ T₃ hj₃).symm ▸ hC₃')
        refine ⟨b', H₃, hev, hH₃, fun C hC => ?_⟩
        obtain ⟨j₄, T₄, C₄, hj₄, hT₄, hC₄, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hDn hC
        have hj₄₃ : j₄ = j₃ :=
          List.getElem?_inj_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hj₄ hj₃ hT₄
        rw [hj₄₃, hC₃'] at hC₄
        have hCC : C₄ = C₃ := by cases hC₄; rfl
        rw [hCC]
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃' hcv.1 hVt hrun
    exact ⟨v, H₃, hev, hH₃, hrun C' hC'⟩
  -- The term of the recursor, related to its address by `(®_μ)`, which the relations `X` contain.
  obtain ⟨v, hv₀, hp₀ | ⟨R, hR, w, htw, hRw⟩⟩ := ht
  · cases Computesι.det hd hv₀ (hI _)
    obtain ⟨_, _, hp₁⟩ := hp₀
    exact (RunUnivRel.not_prop hd (hU T hT).1 (levelRel_prop_iff.1 hp₁)).elim
  · cases Computesι.det hd hv₀ (hI _)
    rw [HasRun.eq hd hR (.univ _ (levelRel_run_iff.2 (hU T hT).1))] at hRw
    have hwv := (ValidEqTerm₀.redStar_iff hd htw.1).1 htv
    have hC₀ : Cs.get (decl.names.idxOf T.name) = some ⟨0, C⟩ := (hidx h' T hh).symm ▸ hC
    obtain ⟨b, H₂, hev, hH₂, hrun⟩ :=
      (hRw X hclosed).2 H₁ (List.prefix_refl _) hH₁ (hwv.trans hwv.symm) C hC₀
    exact ⟨b, H₂, hev, hH₂, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC htw.1 htv hrun⟩

end

end Sic.Core
