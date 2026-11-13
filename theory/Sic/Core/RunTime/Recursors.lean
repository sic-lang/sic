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
import Sic.Math.Relation

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

When the grade of the recursor is erased, every type of the block has one constructor at most, and
every field of the branch is erased, so that the skeleton of the instance stands for the term: the
term computes to a canonical term that `(eq_μ)` relates, and the relations of the canonical terms
that `(eq_μ)` relates, whose type is accessible for `≺`, and on whose skeletons the recursor evaluates
to the address of a value related to the recursor at the motive, are closed, since the skeleton of a
type unfolds into its constructor, applied to the skeletons of the types of its recursive fields,
within a depth that their ancestors, fewer than the types of the block, never reach.

Both cases eliminate a constructor in the same way, once its fields are related to their addresses
and its recursive results evaluated, which `RunsAs.recursor_ctor` states.

ADE prove the validity of their recursors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Evaluation -/

/-- A cast of the number of variables of a term of the target language keeps its evaluations. -/
theorem Eval.cast {n m : Nat} (h : n = m) {H H' : Heap} {E : List Nat} {M : Target n} {a : Nat}
    {R : List Nat} : Eval P H E (h ▸ M) a H' R ↔ Eval P H E M a H' R := by
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

/-- In a signature whose names are distinct, the case of a constructor of a block is its position in
the cases of the block. -/
theorem Entry.constructorCase_of_cases {decl : TypeDeclaration}
    (hn : (decl.cases.map fun x => (x.2.1.name, x.2.2.name)).Nodup) {i j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hi : decl.cases[i]? = some (j, T, con)) :
    Entry.constructorCase T.name con.name (.typeDeclaration decl) = some i := by
  show decl.cases.findIdx? (fun x => x.2.1.name == T.name && x.2.2.name == con.name) = some i
  have hs := List.findIdx?_isSome_of_mem
    (p := fun x => x.2.1.name == T.name && x.2.2.name == con.name) (List.mem_of_getElem? hi)
    (by simp only [Bool.and_eq_true, beq_iff_eq, and_self])
  cases h : decl.cases.findIdx? (fun x => x.2.1.name == T.name && x.2.2.name == con.name) with
  | none => rw [h] at hs; cases hs
  | some i' =>
    obtain ⟨x, hx, hpx⟩ := List.getElem?_of_findIdx?_eq_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hpx
    exact congrArg some (List.getElem?_inj_of_nodup_map hn hx hi (by rw [hpx.1, hpx.2]))

/-! ## Erasure -/

/-- The branch at a position of the erased branches of a recursor is the erasure of the branch at
this position, with the multiplicities that the erasure gives its binders and the positions of its
recursive fields that it gives, each `none` when the grade of its result is erased. -/
theorem Branches.get_erase (sig : Signature) (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade) : (us : Branches k Γ) →
    (es : List (List Nat)) → (fs : List (List Grade)) →
    {i n m : Nat} → {u : Term k ((Γ.extend n).extend m)} → us.get i = some ⟨n, m, u⟩ →
    ∃ gs : Vector Grade m, us.grades i = gs.toList ∧ (us.erase sig S hΓ r es fs).get i =
      some ⟨n, m,
        fun l => r.fieldMultiplicity ((fs.drop i).headD [])[(l : Nat)]?
          ((((es.drop i).headD []).idxOf? (l : Nat)).bind fun j => gs.toList[j]?),
        fun j => gs[j].run,
        fun j => if gs[j] ∈ S then none else ((es.drop i).headD [])[(j : Nat)]?,
        Scope.length_extend_extend Γ n m ▸ u.erase sig S ((hΓ.extend n).extend m)⟩
  | .nil, _, _, _, _, _, _, h => nomatch h
  | .cons _ _ gs _ _, _, _, 0, _, _, _, h => by
    cases h
    exact ⟨gs, rfl, rfl⟩
  | .cons _ _ _ _ us, es, fs, i + 1, _, _, _, h => by
    obtain ⟨gs, h₁, h₂⟩ := Branches.get_erase sig S hΓ r us es.tail fs.tail h
    have he : es.drop (i + 1) = es.tail.drop i := by
      cases es
      · exact List.drop_nil.trans List.drop_nil.symm
      · rfl
    have hf : fs.drop (i + 1) = fs.tail.drop i := by
      cases fs
      · exact List.drop_nil.trans List.drop_nil.symm
      · rfl
    exact ⟨gs, h₁, he ▸ hf ▸ h₂⟩

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

/-- The first element of a list from a position is its element at this position. -/
theorem _root_.List.headD_drop_of_getElem? {α : Type} {d x : α} : {l : List α} → {i : Nat} →
    l[i]? = some x → (l.drop i).headD d = x
  | _ :: _, 0, h => by simpa using h
  | _ :: l, i + 1, h => headD_drop_of_getElem? (l := l) (i := i) (by simpa using h)

/-- The positions of the recursive fields from the position `o` are at `o` or after it. -/
theorem Telescope.le_of_mem_positions {y : Nat} : (rs : List (Option Name)) → (o : Nat) →
    y ∈ (rs.zipIdx o).filterMap (fun z => z.1.map fun _ => z.2) → o ≤ y
  | [], _, h => nomatch h
  | some _ :: rs, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (Telescope.le_of_mem_positions rs (o + 1) h)
  | none :: rs, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none] at h
    exact Nat.le_of_succ_le (Telescope.le_of_mem_positions rs (o + 1) h)

/-- The grade of the recursive result of the field at a position, read from the grades `es` of the
recursive results in order, is the grade at the index of this position in the positions of the
recursive fields, or `0` when the field is not recursive. -/
theorem Telescope.resultGrades_eq_idxOf : (rs : List (Option Name)) → (es : List Grade) →
    (o l : Nat) →
    ((((rs.zipIdx o).filterMap fun z => z.1.map fun _ => z.2).idxOf? (o + l)).bind
      fun j => es[j]?).getD Grade.zero = Telescope.resultGrades rs es l
  | [], _, _, _ => rfl
  | some _ :: rs, es, o, 0 => by
    have hself : (o == o + 0) = true := decide_eq_true rfl
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.idxOf?_cons, hself,
      ↓reduceIte, Option.bind_some]
    cases es <;> rfl
  | some _ :: rs, es, o, l + 1 => by
    have hne : (o == o + (l + 1)) = false := beq_false_of_ne (by omega)
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.idxOf?_cons, hne,
      Bool.false_eq_true, ↓reduceIte]
    have ih := Telescope.resultGrades_eq_idxOf rs es.tail (o + 1) l
    rw [show o + 1 + l = o + (l + 1) by omega] at ih
    cases es with
    | nil =>
      simp only [List.getElem?_nil] at ih ⊢
      cases h : List.idxOf? (o + (l + 1))
          ((rs.zipIdx (o + 1)).filterMap fun z => z.1.map fun _ => z.2) <;> rfl
    | cons e es =>
      cases h : List.idxOf? (o + (l + 1))
          ((rs.zipIdx (o + 1)).filterMap fun z => z.1.map fun _ => z.2) with
      | none =>
        simp only [h, Option.map_none, Option.bind_none, Option.getD_none] at ih ⊢
        exact ih
      | some j =>
        simp only [h, Option.map_some, Option.bind_some, List.getElem?_cons_succ,
          List.tail_cons] at ih ⊢
        exact ih
  | none :: rs, es, o, 0 => by
    have hn : o ∉ (rs.zipIdx (o + 1)).filterMap (fun z => z.1.map fun _ => z.2) :=
      fun h => by have := Telescope.le_of_mem_positions rs (o + 1) h; omega
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none, Nat.add_zero,
      List.idxOf?_eq_none_iff.2 hn, Option.bind_none, Option.getD_none]
    rfl
  | none :: rs, es, o, l + 1 => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none]
    rw [show o + (l + 1) = o + 1 + l by omega]
    exact Telescope.resultGrades_eq_idxOf rs es (o + 1) l

/-- No recursion runs on a field before the positions of the recursive fields from the position
`o`. -/
theorem Telescope.recursionsAt_lt (S : Math.Set Grade) [DecidablePred (· ∈ S)] {o' : Nat} :
    (rs : List (Option Name)) → (es : List Grade) → (o : Nat) → o' < o →
    recursionsAt (List.zipWith (fun e l => if e ∈ S then none else some l) es
      ((rs.zipIdx o).filterMap fun y => y.1.map fun _ => y.2)) o' = .zero
  | [], es, _, _ => by cases es <;> rfl
  | some _ :: _, [], _, _ => rfl
  | some _ :: rs, e :: es, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.zipWith_cons_cons,
      recursionsAt]
    rw [Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_of_lt h)]
    have hne : (if e ∈ S then none else some o) ≠ some o' := by
      split
      · exact nofun
      · exact fun h' => Nat.ne_of_gt h (Option.some.inj h')
    simp only [hne, ↓reduceIte]
    rfl
  | none :: rs, es, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none]
    exact Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_of_lt h)

/-- The recursions that a branch runs on its field at a position: one when the field is recursive
and the grade of its result is not in `S`, none otherwise. -/
theorem Telescope.recursionsAt_positions (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    (h0 : Grade.zero ∈ S) : (rs : List (Option Name)) → (es : List Grade) → (o l : Nat) →
    recursionsAt (List.zipWith (fun e l => if e ∈ S then none else some l) es
      ((rs.zipIdx o).filterMap fun y => y.1.map fun _ => y.2)) (o + l) =
      if Telescope.resultGrades rs es l ∈ S then .zero else .one
  | [], es, _, l => by
    have h : Telescope.resultGrades [] es l ∈ S := h0
    simp only [h, ↓reduceIte]
    cases es <;> rfl
  | some D :: rs, [], _, l => by
    have h : Telescope.resultGrades (some D :: rs) [] l ∈ S := by
      rw [Telescope.resultGrades_nil]
      exact h0
    simp only [h, ↓reduceIte]
    rfl
  | some _ :: rs, e :: es, o, 0 => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.zipWith_cons_cons,
      recursionsAt, Nat.add_zero]
    rw [Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_self o)]
    show _ = if e ∈ S then _ else _
    by_cases he : e ∈ S
    · simp only [he, ↓reduceIte]
      rfl
    · simp only [he, ↓reduceIte]
      rfl
  | some _ :: rs, e :: es, o, l + 1 => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.zipWith_cons_cons,
      recursionsAt]
    have hne : (if e ∈ S then none else some o) ≠ some (o + (l + 1)) := by
      split
      · exact nofun
      · exact fun h' => by have := Option.some.inj h'; omega
    simp only [hne, ↓reduceIte]
    rw [show o + (l + 1) = o + 1 + l by omega,
      Telescope.recursionsAt_positions S h0 rs es (o + 1) l]
    show _ = if Telescope.resultGrades rs es l ∈ S then _ else _
    split <;> rfl
  | none :: rs, es, o, 0 => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none, Nat.add_zero]
    rw [Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_self o)]
    have h : Telescope.resultGrades (none :: rs) es 0 ∈ S := h0
    simp only [h, ↓reduceIte]
  | none :: rs, es, o, l + 1 => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none]
    rw [show o + (l + 1) = o + 1 + l by omega]
    exact Telescope.recursionsAt_positions S h0 rs es (o + 1) l

/-- The uses at run time of a field of the grade `p`, stored at a multiplicity `π` within it, that
a recursor of the grade `r` gives are within those that the branch makes of it, when its usage
bounds them by the grade `g` of its variable and the grade `e` of its recursive result: by the
variable of the field, at the multiplicity that the erasure gives it, and by the recursion on it
when its result has a use at run time. -/
theorem _root_.Sic.Grading.Grade.run_mul_le_fieldMultiplicity : ∀ (π : Multiplicity) (r p e g : Grade),
    r.run * π ≤ r.run * p.run → r * p ≤ g + e * r → r.run * π ≤ ((r * p).run - (e * r).run) +
      r.run * (if e ∈ Mode.oneOne.erased then .zero else .one) := by
  decide

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

/-- Arguments whose grades are all erased are related to addresses as many as them, whatever they
are. -/
theorem RunsAsArgs.of_erased {H : Heap} : {ps : List Parameter} → {g : Nat → Grade} →
    (ts : Args 0 [] ps) → (bs : List Nat) → (Θ : Telescope 0 [] ps) →
    (∀ l (p : Parameter), ps[l]? = some p → g l ∈ Mode.oneOne.erased) → bs.length = ps.length →
    RunsAsArgs sig ι P H g ts bs Θ
  | [], _, .nil, [], .nil, _, _ => trivial
  | _ :: _, _, .cons _ ts, _ :: bs, .cons _ _ _ _, hg, hl =>
    ⟨fun h => (h (hg 0 _ rfl)).elim,
      RunsAsArgs.of_erased ts bs _ (fun l p h => hg (l + 1) p h) (Nat.succ.inj hl)⟩
  | [], _, .nil, _ :: _, .nil, _, hl => nomatch hl
  | _ :: _, _, .cons _ _, [], .cons _ _ _ _, _, hl => nomatch hl

/-- The fields of arguments related at the recursive fields by `Q`, a recursive field of a type `D`
of which is marked by `rs`, have terms that `Q D` relates. -/
theorem Terms.RecRel.exists_of_mem {Q : Name → TermRel} {D : Name} : {ps : List Parameter} →
    (rs : List (Option Name)) → rs.length = ps.length → (ts us : Args 0 [] ps) →
    Terms.RecRel Q rs ts.terms us.terms → some D ∈ rs → ∃ t u, Q D t u
  | [], [], _, .nil, .nil, _, h => nomatch h
  | _ :: _, some _ :: rs, hl, .cons t ts, .cons u us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      exact ⟨t, u, hq.1⟩
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq.2 hm
  | _ :: _, none :: rs, hl, .cons _ ts, .cons _ us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq hm
  | [], _ :: _, hl, _, _, _, _ => nomatch hl
  | _ :: _, [], hl, _, _, _, _ => nomatch hl

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
theorem Args.evalResults (hd : sig.Distinct) {m : Nat} {ρ : Multiplicity} {Ns : TargetBranches m}
    {E : List Nat}
    {f : Name → Term 0 [] → Term 0 []} {names : List Name} {Cs : Motives 0 []} {H₀ : Heap}
    {bsAll : List Nat} :
    {ps : List Parameter} → (rsN : List (Option Name)) → rsN.length = ps.length →
    (ts : Args 0 [] ps) → (o : Nat) → (bs : List Nat) → bsAll.drop o = bs →
    bs.length = ps.length → (es : List Grade) →
    es.length = (Telescope.resultParams rsN ps).length →
    Terms.RecAt (fun D t b => ∀ H', H₀.Extends H' → ∃ v H₂ tr, EvalRec P H' E ρ Ns b v H₂ tr ∧
      H'.Extends H₂ ∧ ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        RunsAs sig ι P H₂ (f D t) v (C.subst₀ (Subst₀.single t))) rsN es ts.terms bs →
    {R : Telescope 0 [] (Telescope.resultParams rsN ps)} →
    Motives.results names Cs rsN ts.terms = some R →
    ∀ H', H₀.Extends H' → ∃ vs H₂ tr, EvalResults P H' E ρ Ns bsAll
      (List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then none else some l) es
        ((rsN.zipIdx o).filterMap fun y => y.1.map fun _ => y.2)) vs H₂ tr ∧ H'.Extends H₂ ∧
      RunsAsArgs sig ι P H₂ (fun j => es.getD j Grade.zero) (ts.results f rsN) vs R
  | [], rsN, hlen, .nil, _, _, _, _, es, _, _, R, hR, H', _ => by
    cases rsN with
    | cons _ _ => cases hlen
    | nil =>
      unfold Motives.results at hR
      cases hR
      refine ⟨[], H', [], ?_, List.prefix_refl H', trivial⟩
      show EvalResults P H' E ρ Ns bsAll (List.zipWith _ es []) [] H' []
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
      obtain ⟨vs, H₂, R₂, hevs, hH₂, hruns⟩ := Args.evalResults hd rsN hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' _ (hH'.trans hH'')
      refine ⟨H'.length :: vs, H₂, R₂, ?_, hH''.trans hH₂, fun h => (h he).elim, hruns⟩
      show EvalResults P H' E ρ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then none else some o) :: _) _ H₂ _
      rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
      exact .erased hevs
    · obtain ⟨v, H₂, R₁, hev, hH₂, hrun⟩ := hQt he H' hH'
      obtain ⟨vs, H₃, R₂, hevs, hH₃, hruns⟩ := Args.evalResults hd rsN hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' _ (hH'.trans hH₂)
      refine ⟨v :: vs, H₃, R₁ ++ R₂, ?_, hH₂.trans hH₃, fun _ => (hrun C hC).mono hd hH₃, hruns⟩
      show EvalResults P H' E ρ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then none else some o) :: _) _ H₃ _
      rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
      exact .recursor hbo hev hevs

/-- Terms of a list evaluate to as many addresses. -/
theorem EvalAll.length_ofList {n : Nat} {H H' : Heap} {E : List Nat} :
    (Ms : List (Multiplicity × Target n)) → {as : List Nat} → {R : List Nat} →
      EvalAll P H E (Targets.ofList Ms) as H' R → as.length = Ms.length
  | [], _, _, .nil => rfl
  | _ :: Ms, _, _, .cons _ hs => congrArg (· + 1) (EvalAll.length_ofList Ms hs)

/-- The fields of arguments related at the recursive fields by `V`, at the addresses to which the
terms `G (some D)` of their types `D` evaluate, satisfy `Q`, when `Q D` holds of each term of a
recursive field that `V D` relates, at each address to which `G (some D)` evaluates in a heap that
extends `H₀`, to a heap that `Hf` extends. -/
theorem EvalAll.recAt {n : Nat} {E : List Nat} {G : Option Name → Multiplicity × Target n}
    {V : Name → TermRel} {Q : Name → Term 0 [] → Nat → Prop} {H₀ Hf : Heap} :
    {ps : List Parameter} → (rs : List (Option Name)) →
    (∀ D, some D ∈ rs → ∀ t u, V D t u → ∀ Ha b Hb R, H₀.Extends Ha →
      Eval P Ha E (G (some D)).2 b Hb R → Hb.Extends Hf → Q D t b) →
    rs.length = ps.length → (es : List Grade) → (ts us : Args 0 [] ps) → {H₁ : Heap} →
    {as : List Nat} → {R : List Nat} → H₀.Extends H₁ →
    EvalAll P H₁ E (Targets.ofList (rs.map G)) as Hf R →
    Terms.RecRel V rs ts.terms us.terms → Terms.RecAt Q rs es ts.terms as
  | [], [], _, _, _, .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, some D :: rs, hG, hl, _ :: es, .cons t ts, .cons u us, _, _, _, hH, .cons h hs, hV =>
    ⟨fun _ => hG D (List.mem_cons_self ..) t u hV.1 _ _ _ _ hH h hs.extends,
      EvalAll.recAt rs (fun D hD => hG D (List.mem_cons_of_mem _ hD)) (Nat.succ.inj hl) es ts us
        (hH.trans h.extends) hs hV.2⟩
  | _ :: _, some _ :: _, _, _, [], .cons _ _, .cons _ _, _, _, _, _, _, _ => trivial
  | _ :: _, none :: rs, hG, hl, es, .cons _ ts, .cons _ us, _, _, _, hH, .cons h hs, hV =>
    EvalAll.recAt rs (fun D hD => hG D (List.mem_cons_of_mem _ hD)) (Nat.succ.inj hl) es ts us
      (hH.trans h.extends) hs hV
  | [], _ :: _, _, hl, _, _, _, _, _, _, _, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _, _, _, _, _, _, _, _ => nomatch hl

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
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {σ : Subst 0 [] Γ} {H : Heap}
    {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V)
    (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {i j : Nat} {T' : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T') (hcon : con ∈ T'.constructors)
    (hi : decl.cases[i]? = some (j, T', con)) {fs : Terms 0 []} {w : Term 0 []}
    (hw : w.IsCtor T'.name con.name fs)
    (hwv : ValidTerm₀ sig ι w (.inst T'.name qs ls ps (as.subst σ))) {H' : Heap}
    (hH' : H.Extends H') {a : Nat} {πv : List Multiplicity} {bs : List Nat}
    (ha : H'[a]? = some (.ctor i πv bs))
    (hπv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀, πv[l]? = some π₀ ∧ r.run * π₀ ≤ r.run * p.usage.run)
    (hfr : ∀ ts : Args 0 [] (con.params (.ofLists qs ps hq hp)), ts.terms = fs →
      EqSubst sig ι (Context.empty.append
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ))) ts.toSubst ts.toSubst →
      Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms →
      RunsAsArgs sig ι P H' (gs i) ts bs
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)) ∧
      Terms.RecAt (fun D' t b => ∀ H'', H'.Extends H'' → ∃ v H₂ tr,
        EvalRec P H'' E r.run (us.erase sig Mode.oneOne.erased hΓ r
          ((sig.recursiveFields D qs ps).getD []) ((sig.caseFieldGrades D qs ps).getD [])) b v H₂
          tr ∧ H''.Extends H₂ ∧
        ∀ C, (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩ →
          RunsAs sig ι P H₂ (.recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)) v
            (C.subst₀ (Subst₀.single t)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) (us.grades i) ts.terms bs) :
    ∃ v H₃ tr, EvalRec P H' E r.run (us.erase sig Mode.oneOne.erased hΓ r
        ((sig.recursiveFields D qs ps).getD []) ((sig.caseFieldGrades D qs ps).getD [])) a v H₃ tr ∧
      H'.Extends H₃ ∧
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
  obtain ⟨gs₀, hgs, hget⟩ := Branches.get_erase sig Mode.oneOne.erased hΓ r us
    ((sig.recursiveFields T.name qs ps).getD []) ((sig.caseFieldGrades T.name qs ps).getD []) hu
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
  obtain ⟨vs, H₂, tr₁, hevs, hH₂, hruns⟩ := Args.evalResults hd
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
  have hχi : RunsAsSubst sig ι P H₂ ctx (δs i) σ V :=
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
  -- The branch binds its variables to cells, at the multiplicities of its binders.
  let πs₀ : Fin (con.params (.ofLists qs ps hq hp)).length → Multiplicity := fun l =>
    r.fieldMultiplicity
      ((((sig.caseFieldGrades T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?
      ((((rfs.drop i).headD []).idxOf? (l : Nat)).bind fun j => gs₀.toList[j]?)
  let πs₀' : Fin (con.resultParams (.ofLists qs ps hq hp) decl.names).length → Multiplicity :=
    fun j => gs₀[j].run
  have hlen : (List.ofFn πs₀ ++ List.ofFn πs₀').length = (bs ++ vs).length := by
    simp only [List.length_append, List.length_ofFn, RunsAsArgs.length hfa, RunsAsArgs.length hruns]
  let H₂' := H₂.bind (List.ofFn πs₀ ++ List.ofFn πs₀') (bs ++ vs)
  have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
  have hB : H₂'.Binds ((List.range' H₂.length (bs ++ vs).length).reverse ++ E)
      (vs.reverse ++ (bs.reverse ++ V)) := by
    have h' := (Heap.binds_bind H₂ hlen).reverse.append (hEV.mono (hH'.trans (hH₂.trans hH₂')))
    rwa [List.reverse_append, List.append_assoc] at h'
  obtain ⟨v, H₃, tr₂, hev, hH₃, hrun⟩ := hbr _ H₂' _ _ hEqbr hB (hσr.mono hd hH₂')
  -- The erased recursor steps to the erased branch.
  have hks : List.ofFn (fun j : Fin (con.resultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then none else ((rfs.drop i).headD [])[(j : Nat)]?) =
      List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then none else some l) gs₀.toList
        ((((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx 0).filterMap
          fun y => y.1.map fun _ => y.2) := by
    rw [hpos]
    exact List.ofFn_ite_getElem? _ gs₀ _
      (Telescope.length_positions _ (Telescope.length_recursion _ _) 0)
  -- The uses of each field by the branch are within those that the constructor allows.
  have hπ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length,
      ∃ π₀, πv[(l : Nat)]? = some π₀ ∧ r.run * π₀ ≤ πs₀ l + r.run * recursionsAt
      (List.ofFn fun j : Fin (con.resultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then none else ((rfs.drop i).headD [])[(j : Nat)]?) l := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, hπ₀, hle⟩ := hπv l p' hp'
    refine ⟨π₀, hπ₀, ?_⟩
    -- The grade of the field, which the signature gives the case.
    have hfs : ((((sig.caseFieldGrades T.name qs ps).getD []).drop i).headD [])[(l : Nat)]? =
        some p'.usage := by
      rw [hd.caseFieldGrades ⟨hdecl, hT, rfl⟩ hq hp, Option.getD_some,
        List.headD_drop_of_getElem? (by rw [List.getElem?_map, hi]; rfl), List.getElem?_map,
        hp']
      rfl
    -- The grade of the recursive result of the field, `0` when it has none.
    have hrg : (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
          us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) l
        else Grade.zero) = Telescope.resultGrades
          ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) gs₀.toList l := by
      rw [Branches.resultGrades, hgs]
      split
      · rfl
      · rename_i hn
        exact (Telescope.resultGrades_of_none _ _ _
          (by simpa [Telescope.recursionAt] using hn)).symm
    have hgl := hg i j T' con l p' hi hp'
    rw [hrg] at hgl
    have he := Telescope.resultGrades_eq_idxOf
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) gs₀.toList 0 l
    have hr := Telescope.recursionsAt_positions Mode.oneOne.erased (by decide)
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) gs₀.toList 0 l
    rw [Nat.zero_add] at he hr
    rw [hks, hr]
    simp only [πs₀, hfs, Grade.fieldMultiplicity, hpos, he]
    exact Grade.run_mul_le_fieldMultiplicity π₀ r p'.usage _ _ hle hgl
  refine ⟨v, H₃, tr₁ ++ tr₂, .iota ha hget (RunsAsArgs.length hfa) hπ (hks ▸ hevs)
    ((Eval.cast _).2 hev), hH₂.trans (hH₂'.trans hH₃), fun C'' hC'' => ?_⟩
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
    (hr : r ∉ Mode.oneOne.erased) {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ))
    (ht : RunsAs sig ι P H₁ t a ((Term.inst D qs ls ps as).subst σ)) :
    ∃ b H₂ tr, EvalRec P H₁ E r.run (us.erase sig Mode.oneOne.erased hΓ r
        ((sig.recursiveFields D qs ps).getD []) ((sig.caseFieldGrades D qs ps).getD [])) a b H₂ tr ∧
      H₁.Extends H₂ ∧
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
  let Ns := us.erase sig Mode.oneOne.erased hΓ r ((sig.recursiveFields T.name qs ps).getD [])
    ((sig.caseFieldGrades T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)
  -- The relations of the canonical terms that `(®_μ)` relates and on whose addresses the erased
  -- recursor evaluates, in each heap that extends `H`, to the address of a value related to the
  -- recursor at the motive.
  let X : Name → RunRel := fun D' H₀ w a => DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D' H₀ w a ∧
    ∀ H', H₀.Extends H' → H.Extends H' →
      ValidTerm₀ sig ι w (.inst D' qs ls ps (as.subst σ)) →
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        ∃ b H₂ tr, EvalRec P H' E r.run Ns a b H₂ tr ∧ H'.Extends H₂ ∧
          RunsAs sig ι P H₂ (f D' w) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w))
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ H₀ w a, T'.runCtorRel sig (.ofLists qs ps hq hp) T'.name (S X) H₀ w a →
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
    obtain ⟨v, H₃, tr, hev, hH₃, hrun⟩ := RunsAs.recursor_ctor hd ⟨hdecl, hT, rfl⟩ hv hadm has hCs
      hCv hus hrec husr hg hχ hs hσ hEV hE hj hcon hi' hw hwv hHH' (hH'.getElem? ha)
      (fun l p hlp => ⟨_, by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ π π' : Multiplicity, π * π' ≤ π * π') _ _⟩)
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
        obtain ⟨b', H₃, tr', hev, hH₃, hrun⟩ := hXv.2 H'' (hH'.trans hH'') (hHH'.trans hH'')
          (hvv.trans hvv.symm) C₃ ((hidx j₃ T₃ hj₃).symm ▸ hC₃')
        refine ⟨b', H₃, tr', hev, hH₃, fun C hC => ?_⟩
        obtain ⟨j₄, T₄, C₄, hj₄, hT₄, hC₄, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hDn hC
        have hj₄₃ : j₄ = j₃ :=
          List.getElem?_inj_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hj₄ hj₃ hT₄
        rw [hj₄₃, hC₃'] at hC₄
        have hCC : C₄ = C₃ := by cases hC₄; rfl
        rw [hCC]
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃' hcv.1 hVt hrun
    exact ⟨v, H₃, tr, hev, hH₃, hrun C' hC'⟩
  -- The term of the recursor, related to its address by `(®_μ)`, which the relations `X` contain.
  obtain ⟨v, hv₀, hp₀ | ⟨R, hR, w, htw, hRw⟩⟩ := ht
  · cases Computesι.det hd hv₀ (hI _)
    obtain ⟨_, _, hp₁⟩ := hp₀
    exact (RunUnivRel.not_prop hd (hU T hT).1 (levelRel_prop_iff.1 hp₁)).elim
  · cases Computesι.det hd hv₀ (hI _)
    rw [HasRun.eq hd hR (.univ _ (levelRel_run_iff.2 (hU T hT).1))] at hRw
    have hwv := (ValidEqTerm₀.redStar_iff hd htw.1).1 htv
    have hC₀ : Cs.get (decl.names.idxOf T.name) = some ⟨0, C⟩ := (hidx h' T hh).symm ▸ hC
    obtain ⟨b, H₂, tr, hev, hH₂, hrun⟩ :=
      (hRw X hclosed).2 H₁ (List.prefix_refl _) hH₁ (hwv.trans hwv.symm) C hC₀
    exact ⟨b, H₂, tr, hev, hH₂, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC htw.1 htv hrun⟩

/-- `r ∈ S`, by induction on `(eq_μ)`: the skeleton of the instance evaluates to an address that the
erased recursor eliminates to the address of a value to which the recursor on a term of the
instance is related at the motive at the term, when every type of the block has one constructor at
most. -/
theorem RunsAs.recursor_skeleton (hd : sig.Distinct) (h : sig.HasDataType D decl T)
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
    (hr : r ∈ Mode.oneOne.erased) (h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) {t : Term 0 []}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ)) :
    ∃ a H₂ b H₃ tr, Eval P H₁ E (sig.skeleton D qs ps : Target Γ.length) a H₂ [] ∧
      EvalRec P H₂ E r.run (us.erase sig Mode.oneOne.erased hΓ r
        ((sig.recursiveFields D qs ps).getD []) ((sig.caseFieldGrades D qs ps).getD [])) a b H₃
        tr ∧ H₁.Extends H₃ ∧
      RunsAs sig ι P H₃ (.recursor r D qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  let Ns := us.erase sig Mode.oneOne.erased hΓ r ((sig.recursiveFields T.name qs ps).getD [])
    ((sig.caseFieldGrades T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r D' qs ls ps (as.subst σ) t (Cs.subst σ) (us.subst σ)
  -- The erased recursor on a skeleton of the type `D'` of a canonical term `v`, within the depth of
  -- the number of the types of the block minus that of the ancestors `A` of `D'`, evaluates, in
  -- each heap that extends the heap of the skeleton, to the address of a value related to the
  -- recursor on `v` at the motive.
  let Pk : Name → Term 0 [] → Prop := fun D' v => ∀ (A : List Name) (d : Nat), A.Nodup →
    (∀ X ∈ A, X ∈ decl.names) → (∀ X ∈ A, Relation.TransGen (decl.Below I) D' X) →
    d + A.length = decl.names.length → ∀ H₂ a H₃ tr₀, H.Extends H₂ →
    Eval P H₂ E (decl.skeleton I d D' : Target Γ.length) a H₃ tr₀ →
    ValidTerm₀ sig ι v (.inst D' qs ls ps (as.subst σ)) → ∀ H', H₃.Extends H' →
    ∃ b H₄ tr, EvalRec P H' E r.run Ns a b H₄ tr ∧ H'.Extends H₄ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        RunsAs sig ι P H₄ (f D' v) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))
  -- The relations of the canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`,
  -- and on whose skeletons the erased recursor evaluates as `Pk` states.
  let X : Name → TermRel := fun D' v w =>
    DataType.blockRel decl.dataTypes SM D' v w ∧ Acc (decl.Below I) D' ∧ Pk D' v
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ v w, T'.ctorRel T'.name (SM X) v w →
      X T'.name v w := by
    intro T' hT' v w hc
    obtain ⟨con, hcon, fs, fs₂, hvc, hwc, hSX⟩ := hc
    have hSX' := hmonoM X _ (fun _ _ _ h => h.1) T' hT' con hcon fs fs₂ hSX
    obtain ⟨ts, us', rfl, rfl, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hSX'
    have hrX := hrecM X T' hT' con hcon _ _ hSX
    have hcons : T'.constructors = [con] :=
      List.eq_singleton_of_mem_of_length_le_one hcon (h1 T' hT')
    -- The type is accessible for `≺`: each type below it is that of a recursive field.
    have hacc : Acc (decl.Below I) T'.name := Acc.intro _ fun D'' ⟨T₀, hT₀, hn₀, c₀, hc₀, hm⟩ => by
      cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT₀ hT' hn₀
      rw [hcons] at hc₀
      cases hc₀
      obtain ⟨_, _, _, _, _, _, hX₁⟩ :=
        Terms.RecRel.exists_of_mem _ (Telescope.length_recursion _ _) ts us' hrX hm
      exact hX₁.2.1
    refine ⟨DataType.blockRel_closed hmonoM hT'
      ⟨con, hcon, ts.terms, us'.terms, hvc, hwc, hSX'⟩, hacc, ?_⟩
    intro A d hA hAn hAD hdA H₂ a H₃ _ hH₂ hev hvv H' hH'
    -- The depth is not reached, since the ancestors are fewer than the types of the block.
    have hlt := TypeDeclaration.length_ancestors_lt hacc (TypeDeclaration.name_mem_names hT') hA
      hAn hAD
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    -- The skeleton unfolds into the constructor of the case of the type.
    obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
    rw [TypeDeclaration.skeleton_succ hnd I hT' rfl hcons
      (Entry.constructorCase_of_cases (hd.cases_nodup hdecl) hi)] at hev
    cases hev with
    | @ctor _ _ H₂₀ _ _ _ bs _ hall =>
    have hH₂₀ : H₂₀.Extends H' := (List.prefix_append H₂₀ _).trans hH'
    have hHH' : H.Extends H' := hH₂.trans (hall.extends.trans hH₂₀)
    have hbl : bs.length = (con.params I).length := by
      rw [EvalAll.length_ofList _ hall, List.length_map, Telescope.length_recursion]
    -- The fields of the skeleton are stored at the multiplicity `0`, and the grade of the recursor
    -- has no use at run time.
    have hπv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), (decl.skeleton I d' D' : Target Γ.length))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          r.run * π₀ ≤ r.run * p.usage.run := fun l p hlp => by
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨.zero, ?_, (by decide : ∀ (r : Grade) (π π' : Multiplicity),
        r ∈ Mode.oneOne.erased → r.run * π ≤ r.run * π') r _ _ hr⟩
      rw [Targets.multiplicities_ofList, List.map_map, List.getElem?_map,
        List.getElem?_eq_getElem hl, Option.map_some]
      congr 1
      simp only [Function.comp_apply]
      split <;> rfl
    obtain ⟨b, H₄, tr, hevr, hH₄, hrun⟩ := RunsAs.recursor_ctor hd ⟨hdecl, hT, rfl⟩ hv hadm has
      hCs hCv hus hrec husr hg hχ hs hσ hEV hE hj hcon hi hvc hvv hHH'
      (hH'.getElem? List.getElem?_concat_length) hπv
      fun ts' hfs _ _ => by
        rw [hfs]
        -- The fields are erased, at grades erased since the grade of the recursor is.
        refine ⟨RunsAsArgs.of_erased ts' bs _ (fun l p hl' => (by decide : ∀ r p g x : Grade,
          r ∈ Mode.oneOne.erased → r * p ≤ g + x * r → g ∈ Mode.oneOne.erased) r p.usage
          (gs i l) _ hr (hg i j T' con l p hi hl')) hbl, ?_⟩
        -- The recursive results used at run time, on the skeletons of the recursive fields.
        refine EvalAll.recAt _ (fun D'' hD'' t u ⟨v₁, w₁, hcv, hcw, hX₁⟩ Ha b' Hb Rb hHa hevb hHb
          H'' hH'' => ?_) (Telescope.length_recursion _ _) _ ts us' (List.prefix_refl _) hall hrX
        have hDn := Telescope.mem_recursion hD''
        obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hDn
        have htu := hval T₃ hT₃ t u ⟨v₁, w₁, hcv, hcw, hX₁.1⟩
        have hVt := htu.trans htu.symm
        have hvv₁ := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        have hb : decl.Below I T₃.name T'.name := ⟨T', hT', rfl, con, hcons, hD''⟩
        obtain ⟨b'', H₅, tr', hev', hH₅, hrun'⟩ := hX₁.2.2 (T'.name :: A) d'
          (List.nodup_cons.2 ⟨fun hm => hacc.not_transGen_self (hAD _ hm), hA⟩)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact TypeDeclaration.name_mem_names hT'
            · exact hAn X hX)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact .single hb
            · exact .trans (.single hb) (hAD X hX))
          (by simp only [List.length_cons]; omega) Ha b' Hb Rb (hH₂.trans hHa) hevb
          (hvv₁.trans hvv₁.symm) H'' (hHb.trans (hH₂₀.trans hH''))
        refine ⟨b'', H₅, tr', hev', hH₅, fun C₄ hC₄ => ?_⟩
        obtain ⟨j₄, T₄, C₄', hj₄, hT₄, hC₄', rfl⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn hC₄
        obtain rfl : T₄ = T₃ := List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd)
          (List.mem_of_getElem? hj₄) hT₃ hT₄
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₄ hC₄' hcv.1 hVt
          (hrun' C₄' ((hidx j₄ _ hj₄).symm ▸ hC₄'))
    refine ⟨b, H₄, tr, hevr, hH₄, fun C' hC' => hrun C' ?_⟩
    rwa [hidx j T' hj] at hC'
  -- The term of the recursor computes to a canonical term that `(eq_μ)` relates, which the
  -- relations `X` contain.
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ := htv.2.1 fun ⟨v, hv', _, _, hk⟩ => by
    cases Computesι.det hd (hI _) hv'
    exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hUM T hT).1) hk
  cases Computesι.det hd (hI _) hv'
  have hX := ((HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T hT).1)) _ _).1 hrel) X
    hclosed
  have hww := (ValidEqTerm₀.redStar_iff hd hw₁.1).1 htv
  obtain ⟨a, H₂, hev, hH₂⟩ := (decl.skeleton_isSkeleton I decl.names.length T.name).eval P H₁ E
  obtain ⟨b, H₃, tr, hevr, hH₃, hrun⟩ := hX.2.2 [] _ List.nodup_nil (fun _ h => nomatch h)
    (fun _ h => nomatch h) rfl H₁ a H₂ [] hH₁ hev (hww.trans hww.symm) H₂ (List.prefix_refl _)
  refine ⟨a, H₂, b, H₃, tr, ?_, hevr, hH₂.trans hH₃, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC
    hw₁.1 htv (hrun C ((hidx h' T hh).symm ▸ hC))⟩
  rw [hd.skeleton ⟨hdecl, hT, rfl⟩ hq hp]
  exact hev


-- ADE: the cases `natrecₘ`, `prodrecₘ`, `unitrecₘ` and `emptyrecₘ` of `fundamental`, in
-- `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- `(rec)` keeps the validity at run time: the erasure of the recursor evaluates its term, or the
skeleton of its instance when its grade `r` is erased, then the branch of the case of its value. A
recursor on a block of propositions has no constructor, in the mode `11ᵐ`, so that no term of its
instance is true and none is substituted. -/
theorem RunValid.recursor (hd : sig.Distinct) (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {γ : GradeVector Γ.length} {t : Term 0 Γ} {h' : Nat} {C : Term 0 (.var :: Γ)}
    (hh : decl.dataTypes[h']? = some T) (hC : Cs.get h' = some ⟨0, C⟩)
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
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : r ∉ Mode.oneOne.erased → RunValid sig ι P hΓ ctx γ t (.inst D qs ls ps as))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      Mode.oneOne.grade * r * p.usage ≤ gs i l +
        (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
          (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)) l
          else Grade.zero) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ·ᶜ χ)
    (hr : (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) → r.mode = .oneOne)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases = []) :
    RunValid sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ χ) (.recursor r D qs ls ps as t Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  intro σ H E V hσ hEV hE
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS := Mode.erasesUncounted .oneOne
  have hEχ : RunsAsSubst sig ι P H ctx χ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  have hg' : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
          (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)) l
          else Grade.zero) * r := fun i j T' con l p hi hl' => by
    have h₁ := hg i j T' con l p hi hl'
    rwa [show Mode.oneOne.grade = Grade.one from rfl, Grade.modality.semiring.one_mul] at h₁
  have htσ : ValidTerm₀ sig ι (t.subst σ) ((Term.inst T.name qs ls ps as).subst σ) :=
    ht.2 σ σ hσ
  have hCσ : (C.subst₀ (Subst₀.single t)).subst σ =
      (C.subst (Subst.lift σ)).subst₀ (Subst₀.single (t.subst σ)) :=
    Term.subst_subst₀_of (Subst₀.Swaps.single _ _) C
  rw [hCσ]
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality with
  | prop =>
    -- No term of an instance of a block of propositions without constructor is true.
    have hasσ := has.2 σ σ hσ
    obtain ⟨S, hP, hmono, -, -⟩ := hv.propRel hd hdecl hq hl hp hadm hasσ hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have hI : Computesι sig ι (.inst T.name qs ls ps (as.subst σ))
        (.inst T.name qs ls ps (as.subst σ)) := ⟨.refl _, .inst _ _ _ _ _⟩
    obtain ⟨v', R', hv', hR', hrel⟩ := htσ.2.2 ⟨_, hI, _, _, hP'⟩
    cases Computesι.det hd hI hv'
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      (HasEq.unique hd hR' (.prop _ _ hP' fun _ _ => .rfl) _ _).1 hrel
    obtain ⟨T₀, hT₀, -, con₀, hcon₀, -⟩ := DataType.blockTruth_inv hmono htrue
    obtain ⟨i, j, hi, -⟩ := TypeDeclaration.exists_cases hT₀ hcon₀
    rw [hprop hs] at hi
    cases hi
  | type =>
    by_cases hrS : r ∈ Mode.oneOne.erased
    · -- The skeleton of the instance stands for the term.
      have h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1 := fun T' hT' => by
        refine Nat.le_of_not_lt fun h2 => ?_
        exact (by decide : ∀ r : Grade, r ∈ Mode.oneOne.erased → r.mode ≠ .oneOne) r hrS
          (hr ⟨T', hT', h2⟩)
      obtain ⟨a, H₂, b, H₃, tr, hev, hevr, hH₃, hrun⟩ := RunsAs.recursor_skeleton hd h hv hadm
        has hh hC hCs hCv hus hrec husr hg' hχ hs hrS h1 hσ hEV hEχ (List.prefix_refl H) htσ
      refine ⟨b, H₃, [] ++ tr, ?_, hH₃, hrun⟩
      show Eval P H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _) _) b H₃ _
      rw [ite_eq_left hrS]
      exact .recursor hev hevr
    · -- The term evaluates to the address of its value.
      have hγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h (hS.mul _ _ hrS (hS.add _ _ h'))) hE
      obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr hrS σ H E V hσ hEV hγ
      obtain ⟨b, H₂, tr₂, hevr, hH₂, hrun⟩ := RunsAs.recursor hd h hv hadm has hh hC hCs hCv hus
        hrec husr hg' hχ hs hrS hσ hEV hEχ hH₁ htσ hta
      refine ⟨b, H₂, tr₁ ++ tr₂, ?_, hH₁.trans hH₂, hrun⟩
      show Eval P H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _) _) b H₂ _
      rw [ite_eq_right hrS]
      exact .recursor hev hevr

end

end Sic.Core
