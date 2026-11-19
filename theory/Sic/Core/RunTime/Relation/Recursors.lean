module

public import Sic.Core.RunTime.Relation
public import Sic.Core.RunTime.Relation.Recursors.Results
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.Data
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Skeleton
import Sic.Core.RunTime.Relation.Substitution
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature
import Sic.Math.Relation

/-!
# Run Time of the Recursors

The recursors at run time: the erasure of a recursor evaluates its term, or the term of the
skeleton of its instance when its grade is erased, then eliminates the value of the case of its
constructor by the branch of the case, with its fields and its recursive results, each the recursor
on its recursive field, or `↯` when its grade is erased.

When the grade of the recursor is used at run time, the term of the recursor is related to the
address of its value at its instance, by `(®_μ)`, the least relations closed under its clauses: the
relations of the canonical terms that `(®_μ)` relates and on whose addresses the recursor evaluates
to the address of a value related to the recursor at the motive are closed, since the recursor on a
constructor steps to its branch, at the terms of the fields and at the recursive results, which
these relations relate to the addresses of the fields and of the results.

When the grade of the recursor is erased, every type of the block has one constructor at most, and
every field of the branch is erased, so that the term of the skeleton of the instance stands for
the term: the term computes to a canonical term that `(eq_μ)` relates, and the relations of the
canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`, and on the terms of whose
skeletons the recursor evaluates to the address of a value related to the recursor at the motive,
are closed, since the term of the skeleton of a type unfolds into its constructor, applied to the
terms of the skeletons of the types of its recursive fields,
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
theorem Eval.cast {n m : Nat} (h : n = m) {ϖ : Multiplicity} {H H' : Heap} {E : List Nat}
    {M : Target n} {a : Nat} {R : List Nat} :
    Eval P ϖ H E (h ▸ M) a H' R ↔ Eval P ϖ H E M a H' R := by
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
this position, with the multiplicities and the coefficients of ownership that the erasure gives its
binders and the recursive results that it gives, each `⊥` when the grade of its result is
erased. -/
theorem Branches.get_erase (sig : Signature) (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade) : (us : Branches k Γ) →
    (ws : List (List RecursiveResult)) → (fs : List (List Parameter)) →
    {i n m : Nat} → {u : Term k ((Γ.extend n).extend m)} → us.get i = some ⟨n, m, u⟩ →
    ∃ gs : Vector Grade m, us.grades i = gs.toList ∧ (us.erase sig S hΓ r ws fs).get i =
      some ⟨n, m,
        fun l => r.fieldMultiplicity ((((fs.drop i).headD [])[(l : Nat)]?).map (·.usage))
          ((((ws.drop i).headD []).zip gs.toList).find? fun x => x.1.fieldPosition == some (l : Nat)),
        fun l => r.fieldCoefficient ((fs.drop i).headD [])[(l : Nat)]?,
        fun j => gs[j].run,
        fun j => if gs[j] ∈ S then .erased else (((ws.drop i).headD [])[(j : Nat)]?).getD .erased,
        Scope.length_extend_extend Γ n m ▸ u.erase sig S ((hΓ.extend n).extend m)⟩
  | .nil, _, _, _, _, _, _, h => nomatch h
  | .cons _ _ gs _ _, _, _, 0, _, _, _, h => by
    cases h
    refine ⟨gs, rfl, ?_⟩
    rfl
  | .cons _ _ _ _ us, ws, fs, i + 1, _, _, _, h => by
    obtain ⟨gs, h₁, h₂⟩ := Branches.get_erase sig S hΓ r us ws.tail fs.tail h
    have he : ws.drop (i + 1) = ws.tail.drop i := by
      cases ws
      · exact List.drop_nil.trans List.drop_nil.symm
      · rfl
    have hf : fs.drop (i + 1) = fs.tail.drop i := by
      cases fs
      · exact List.drop_nil.trans List.drop_nil.symm
      · rfl
    exact ⟨gs, h₁, he ▸ hf ▸ h₂⟩

/-- The positions of the recursive fields among fields none of which is nested, whose nestings are
`ns`, from the position `o`, are as many as the recursive results. -/
theorem Telescope.length_positions : (ns : List (Nest Name)) → {ps : List Parameter} →
    ns.length = ps.length → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) → (o : Nat) →
    (((ns.map Nest.blockName).zipIdx o).filterMap fun y => y.1.map fun _ => y.2).length =
      (Telescope.nestResultParams ns ps).length
  | [], [], _, _, _ => rfl
  | .direct _ :: ns, _ :: _, h, hn, o =>
    congrArg (· + 1) (Telescope.length_positions ns (Nat.succ.inj h)
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν)) (o + 1))
  | .plain :: ns, _ :: _, h, hn, o => Telescope.length_positions ns (Nat.succ.inj h)
    (fun ν hν => hn ν (List.mem_cons_of_mem _ hν)) (o + 1)
  | .inst ms :: _, _ :: _, _, hn, _ => absurd rfl (hn _ List.mem_cons_self ms)

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

/-- The positions of the recursive fields from the position `o` are before the end of the fields. -/
theorem Telescope.lt_of_mem_positions {y : Nat} : (rs : List (Option Name)) → (o : Nat) →
    y ∈ (rs.zipIdx o).filterMap (fun z => z.1.map fun _ => z.2) → y < o + rs.length
  | [], _, h => nomatch h
  | some _ :: rs, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := Telescope.lt_of_mem_positions rs (o + 1) h
      simp only [List.length_cons]
      omega
  | none :: rs, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none] at h
    have := Telescope.lt_of_mem_positions rs (o + 1) h
    simp only [List.length_cons]
    omega

/-- The grade of the recursive result of the field at a position, among fields none of which is
nested, read from the grades `es` of the recursive results in order, is the grade at the index of
this position in the positions of the recursive fields, or `0` when the field is not recursive. -/
theorem Telescope.resultGrades_eq_idxOf : (ns : List (Nest Name)) → (es : List Grade) →
    (o l : Nat) → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
    (((((ns.map Nest.blockName).zipIdx o).filterMap fun z => z.1.map fun _ => z.2).idxOf?
      (o + l)).bind fun j => es[j]?).getD Grade.zero = Telescope.resultGrades ns es l
  | [], _, _, _, _ => rfl
  | .inst ms :: _, _, _, _, hn => absurd rfl (hn _ List.mem_cons_self ms)
  | .direct _ :: ns, es, o, 0, _ => by
    have hself : (o == o + 0) = true := decide_eq_true rfl
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_some, List.idxOf?_cons, hself, ↓reduceIte, Option.bind_some]
    cases es <;> rfl
  | .direct _ :: ns, es, o, l + 1, hn => by
    have hne : (o == o + (l + 1)) = false := beq_false_of_ne (by omega)
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_some, List.idxOf?_cons, hne, Bool.false_eq_true, ↓reduceIte]
    have ih := Telescope.resultGrades_eq_idxOf ns es.tail (o + 1) l
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))
    rw [show o + 1 + l = o + (l + 1) by omega] at ih
    cases es with
    | nil =>
      simp only [List.getElem?_nil] at ih ⊢
      cases h : List.idxOf? (o + (l + 1))
          (((ns.map Nest.blockName).zipIdx (o + 1)).filterMap fun z => z.1.map fun _ => z.2) <;>
        rfl
    | cons e es =>
      cases h : List.idxOf? (o + (l + 1))
          (((ns.map Nest.blockName).zipIdx (o + 1)).filterMap fun z => z.1.map fun _ => z.2) with
      | none =>
        simp only [h, Option.map_none, Option.bind_none, Option.getD_none] at ih ⊢
        exact ih
      | some j =>
        simp only [h, Option.map_some, Option.bind_some, List.getElem?_cons_succ,
          List.tail_cons] at ih ⊢
        exact ih
  | .plain :: ns, es, o, 0, _ => by
    have hn : o ∉ ((ns.map Nest.blockName).zipIdx (o + 1)).filterMap
        (fun z => z.1.map fun _ => z.2) :=
      fun h => by have := Telescope.le_of_mem_positions _ (o + 1) h; omega
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_none, Nat.add_zero, List.idxOf?_eq_none_iff.2 hn, Option.bind_none,
      Option.getD_none]
    rfl
  | .plain :: ns, es, o, l + 1, hn => by
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_none]
    rw [show o + (l + 1) = o + 1 + l by omega]
    exact Telescope.resultGrades_eq_idxOf ns es (o + 1) l
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))

/-- The first recursor on a field among recursors on fields at the positions `xs`, each with its
grade in `es`, that names the field `n` is the one at the index of `n` in `xs`, with its grade, when
it has one. -/
theorem RecursiveResult.find?_zip_map_field : (xs : List Nat) → (es : List Grade) → (n : Nat) →
    ((xs.map RecursiveResult.field).zip es).find? (fun x => x.1.fieldPosition == some n) =
      ((xs.idxOf? n).bind fun j => es[j]?).map (RecursiveResult.field n, ·)
  | [], _, _ => rfl
  | x :: xs, [], n => by
    simp only [List.map_cons, List.zip_nil_right, List.find?_nil, List.getElem?_nil,
      Option.bind_fun_none, Option.map_none]
  | x :: xs, e :: es, n => by
    by_cases h : x = n
    · subst h
      rw [List.map_cons, List.zip_cons_cons, List.find?_cons_of_pos
          (p := fun y : RecursiveResult × Grade => y.1.fieldPosition == some x) (a := (.field x, e))
          (beq_iff_eq.2 rfl),
        List.idxOf?_cons, beq_iff_eq.2 rfl]
      rfl
    · have hne : (x == n) = false := beq_false_of_ne h
      rw [List.map_cons, List.zip_cons_cons, List.find?_cons_of_neg
          (p := fun y : RecursiveResult × Grade => y.1.fieldPosition == some n) (a := (.field x, e))
          (fun h' => h (Option.some.inj (beq_iff_eq.1 h'))),
        RecursiveResult.find?_zip_map_field xs es n, List.idxOf?_cons, hne]
      cases List.idxOf? n xs <;> rfl

/-- The multiplicity that the erasure gives the variable of a field of the grade `p`, among fields
none of which is nested, whose nestings are `ns`, from the position `o`, is the uses at run time of
the field that the recursor gives minus those of the recursion on it, at the grade of its recursive
result, `0` when it has none. -/
theorem _root_.Sic.Grading.Grade.fieldMultiplicity_positions (r p : Grade) (ns : List (Nest Name))
    (es : List Grade) (o l : Nat) (hn : ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) :
    r.fieldMultiplicity (some p)
      (((((ns.map Nest.blockName).zipIdx o).filterMap fun z => z.1.map fun _ => z.2).map
        RecursiveResult.field).zip es |>.find? fun x => x.1.fieldPosition == some (o + l)) =
      (r * p).run - ((Telescope.resultGrades ns es l) * r).run := by
  rw [RecursiveResult.find?_zip_map_field, ← Telescope.resultGrades_eq_idxOf ns es o l hn]
  cases ((((ns.map Nest.blockName).zipIdx o).filterMap fun z => z.1.map fun _ => z.2).idxOf?
    (o + l)).bind (fun j => es[j]?) with
  | none => exact (by decide : ∀ (m : Multiplicity) (r : Grade), m = m - (Grade.zero * r).run) _ _
  | some e => rfl

/-- The recursive results of the first constructor from a position, among the recursors on the
fields at the positions `es`, are the recursors on the fields at its positions. -/
theorem RecursiveResult.headD_drop_map_field (es : List (List Nat)) (i : Nat) :
    ((es.map (·.map RecursiveResult.field)).drop i).headD [] = ((es.drop i).headD []).map .field := by
  rw [← List.map_drop]
  cases es.drop i <;> rfl

/-- The recursive result at a position among recursors on fields at the positions `xs` is the
result of the field at this position, erased when there is none. -/
theorem RecursiveResult.getD_map_field (xs : List Nat) (j : Nat) :
    ((xs.map RecursiveResult.field)[j]?).getD .erased = .ofPosition xs[j]? := by
  rw [List.getElem?_map]
  cases xs[j]? <;> rfl

/-- No recursion runs on a field before the positions of the recursive fields from the position
`o`. -/
theorem Telescope.recursionsAt_lt (S : Math.Set Grade) [DecidablePred (· ∈ S)] {o' : Nat} :
    (rs : List (Option Name)) → (es : List Grade) → (o : Nat) → o' < o →
    recursionsAt (List.zipWith (fun e l => if e ∈ S then RecursiveResult.erased else .field l) es
      ((rs.zipIdx o).filterMap fun y => y.1.map fun _ => y.2)) (es.map Grade.run) o' = .zero
  | [], es, _, _ => by cases es <;> rfl
  | some _ :: _, [], _, _ => rfl
  | some _ :: rs, e :: es, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_some, List.zipWith_cons_cons,
      List.map_cons, recursionsAt]
    rw [Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_of_lt h)]
    have hne : (if e ∈ S then RecursiveResult.erased else .field o).fieldPosition ≠ some o' := by
      split
      · exact nofun
      · exact fun h' => Nat.ne_of_gt h (Option.some.inj h')
    simp only [hne, ↓reduceIte]
    rfl
  | none :: rs, es, o, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons, Option.map_none]
    exact Telescope.recursionsAt_lt S rs es (o + 1) (Nat.lt_succ_of_lt h)

/-- The recursions that a branch runs on its field at a position, among fields none of which is
nested: the multiplicity of the grade of its result when the field is recursive and this grade is
not in `S`, none otherwise. -/
theorem Telescope.recursionsAt_positions (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    (h0 : Grade.zero ∈ S) : (ns : List (Nest Name)) → (es : List Grade) → (o l : Nat) →
    (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
    recursionsAt (List.zipWith (fun e l => if e ∈ S then RecursiveResult.erased else .field l) es
      (((ns.map Nest.blockName).zipIdx o).filterMap fun y => y.1.map fun _ => y.2))
      (es.map Grade.run) (o + l) =
      if Telescope.resultGrades ns es l ∈ S then .zero else (Telescope.resultGrades ns es l).run
  | [], es, _, l, _ => by
    have h : Telescope.resultGrades [] es l ∈ S := h0
    simp only [h, ↓reduceIte]
    cases es <;> rfl
  | .inst ms :: _, _, _, _, hn => absurd rfl (hn _ List.mem_cons_self ms)
  | .direct D :: ns, [], _, l, _ => by
    have h : Telescope.resultGrades (.direct D :: ns) [] l ∈ S := by
      rw [Telescope.resultGrades_nil]
      exact h0
    simp only [h, ↓reduceIte]
    rfl
  | .direct _ :: ns, e :: es, o, 0, _ => by
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_some, List.zipWith_cons_cons, List.map_cons, recursionsAt, Nat.add_zero]
    rw [Telescope.recursionsAt_lt S _ es (o + 1) (Nat.lt_succ_self o)]
    show _ = if e ∈ S then _ else e.run
    by_cases he : e ∈ S
    · simp only [he, ↓reduceIte, RecursiveResult.fieldPosition]
      rfl
    · simp only [he, ↓reduceIte, RecursiveResult.fieldPosition, RecursiveResult.factor]
      cases e.run <;> rfl
  | .direct _ :: ns, e :: es, o, l + 1, hn => by
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_some, List.zipWith_cons_cons, List.map_cons, recursionsAt]
    have hne : (if e ∈ S then RecursiveResult.erased else .field o).fieldPosition ≠
        some (o + (l + 1)) := by
      split
      · exact nofun
      · exact fun h' => by have := Option.some.inj h'; omega
    simp only [hne, ↓reduceIte]
    rw [show o + (l + 1) = o + 1 + l by omega,
      Telescope.recursionsAt_positions S h0 ns es (o + 1) l
        (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))]
    show _ = if Telescope.resultGrades ns es l ∈ S then _ else (Telescope.resultGrades ns es l).run
    split
    · rfl
    · cases (Telescope.resultGrades ns es l).run <;> rfl
  | .plain :: ns, es, o, 0, _ => by
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_none, Nat.add_zero]
    rw [Telescope.recursionsAt_lt S _ es (o + 1) (Nat.lt_succ_self o)]
    have h : Telescope.resultGrades (.plain :: ns) es 0 ∈ S := h0
    simp only [h, ↓reduceIte]
  | .plain :: ns, es, o, l + 1, hn => by
    simp only [List.map_cons, Nest.blockName, List.zipIdx_cons, List.filterMap_cons,
      Option.map_none]
    rw [show o + (l + 1) = o + 1 + l by omega]
    exact Telescope.recursionsAt_positions S h0 ns es (o + 1) l
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))

/-- The uses at run time of a field of the grade `p`, stored at a multiplicity `π` within it, that
a recursor of the grade `r` gives are within those that the branch makes of it, when its usage
bounds them by the grade `g` of its variable and the grade `e` of its recursive result: by the
variable of the field, at the multiplicity that the erasure gives it, and by the recursion on it,
as many times as its result is read, when it has a use at run time. -/
theorem _root_.Sic.Grading.Grade.run_mul_le_fieldMultiplicity : ∀ (π : Multiplicity) (r p e g : Grade),
    r.run * π ≤ r.run * p.run → r * p ≤ g + e * r → r.run * π ≤ ((r * p).run - (e * r).run) +
      r.run * (if e ∈ Mode.oneOne.erased then .zero else e.run) := by
  decide

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
`H₀` satisfy `Q` at each recursive field whose result is used at run time, among fields none of
which is nested, whose nestings are `ns`, when the relation that the position of each recursive
field holds, at its type `D`, implies `Q` on the terms that `V D` holds of, and when the field of
each result used at run time is used too. -/
theorem RunTelRel.recAt {n : Nat} {below : LevelRel.Below n} {Q : Name → Term 0 [] → Nat → Prop}
    {V : Name → Term 0 [] → Prop} {H₀ : Heap} :
    {rs' : Nat → Nest RunNestLeaf} → {ps : List Parameter} → {Θ : Telescope 0 [] ps} →
    {S : RunFieldsRel} → RunTelRel sig ι P n below rs' Θ S → (ns : List (Nest Name)) →
    ns.length = ps.length → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
    (∀ i D, ns[i]? = some (.direct D) → ∃ x, rs' i = .direct x ∧
      ∀ t b, x.2 H₀ t b → V D t → Q D t b) →
    (ts : Args 0 [] ps) → (bs : List Nat) → S H₀ ts.terms bs →
    Terms.RecRel (fun D t _ => V D t) (ns.map Nest.blockName) ts.terms ts.terms →
    (es : List Grade) →
    (∀ l (p : Parameter), ps[l]? = some p → Telescope.resultGrades ns es l ∉ Mode.oneOne.erased →
      p.usage ∉ Mode.oneOne.erased) →
    Terms.RecAt Q (ns.map Nest.blockName) es ts.terms bs
  | _, [], .nil, _, .nil, ns, hlen, _, _, .nil, _, _, _, _, _ => by
    cases ns with
    | nil => trivial
    | cons => cases hlen
  | _, p :: ps, .cons _ _ _ Θ, _, .cons _ _ _ G hG hrs0, ns, hlen, hn, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨⟨hFt, -⟩, hGt⟩ := hS
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    have hn' : ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms := fun ν hν => hn ν (List.mem_cons_of_mem _ hν)
    cases x with
    | direct D =>
      obtain ⟨_, h, -⟩ := hrs 0 D rfl
      exact nomatch h.symm.trans hrs0
    | inst ms => exact absurd rfl (hn _ List.mem_cons_self ms)
    | plain =>
    exact RunTelRel.recAt (hG t hFt) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt
      hV es (fun l => hg (l + 1))
  | _, p :: ps, .cons _ _ _ Θ, _, .nested hrs0 hRn G hG, ns, hlen, hn, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨hb, hGt⟩ := hS
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    have hn' : ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms := fun ν hν => hn ν (List.mem_cons_of_mem _ hν)
    cases x with
    | plain =>
      exact RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt
        hV es (fun l => hg (l + 1))
    | inst ms => exact absurd rfl (hn _ List.mem_cons_self ms)
    | direct D =>
    obtain ⟨⟨_, _⟩, hτ, hQ⟩ := hrs 0 D rfl
    rw [hτ] at hRn
    cases hRn with
    | direct _ =>
    cases es with
    | nil => trivial
    | cons e es =>
    obtain ⟨hVt, hV'⟩ := hV
    exact ⟨fun he => hQ t b (hb (hg 0 p rfl he)) hVt,
      RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt hV' es
        (fun l => hg (l + 1))⟩

/-- The recursive results of a branch at run time, by induction on the fields, whose nestings are
`ns`: from the addresses `bs` of the fields, the last of the addresses `bsAll` from the position
`o`, the recursive results evaluate, at each weight and in each heap that extends `H₀`, to addresses
related to the results `f D t` at the motives at their fields, each at its grade in `es`, when the
recursor on each recursive field `t` of the type `D` whose result is used evaluates, at each weight
and in each such heap, to such an address. -/
theorem Args.evalResults (hd : sig.Distinct) {m : Nat} {ρ ϱ : Multiplicity} {Ns : TargetBranches m}
    {E : List Nat}
    {f : Name → Term 0 [] → Term 0 []} {names : List Name} {Cs : Motives 0 []} {H₀ : Heap}
    {bsAll : List Nat} :
    {ps : List Parameter} → (ns : List (Nest Name)) → ns.length = ps.length →
    (ts : Args 0 [] ps) → (o : Nat) → (bs : List Nat) → bsAll.drop o = bs →
    bs.length = ps.length → (es : List Grade) →
    es.length = (Telescope.nestResultParams ns ps).length →
    Terms.RecAt (fun D t b => ∀ ϖ H', H₀.Extends H' → ∃ v H₂ tr, EvalRec P ϖ H' E ρ ϱ Ns b v H₂ tr ∧
      H'.Extends H₂ ∧ ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        RunsAs sig ι P H₂ (f D t) v (C.subst₀ (Subst₀.single t))) (ns.map Nest.blockName) es
      ts.terms bs →
    {R : Telescope 0 [] (Telescope.nestResultParams ns ps)} →
    Motives.results names Cs ns ts.terms = some R →
    {rs : Args 0 [] (Telescope.nestResultParams ns ps)} → ts.results f ns = some rs →
    ∀ ϖ H', H₀.Extends H' → ∃ vs H₂ tr, EvalResults P ϖ H' E ρ ϱ Ns bsAll
      (List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field l)
        es
        (((ns.map Nest.blockName).zipIdx o).filterMap fun y => y.1.map fun _ => y.2))
        (es.map Grade.run) vs H₂ tr ∧
      H'.Extends H₂ ∧
      RunsAsArgs sig ι P H₂ (fun j => es.getD j Grade.zero) rs vs R
  | [], ns, hlen, .nil, _, _, _, _, es, hes, _, R, hR, rs, hrs, ϖ, H', _ => by
    cases ns with
    | cons _ _ => cases hlen
    | nil =>
      unfold Motives.results at hR
      cases hR
      unfold Args.results at hrs
      cases hrs
      refine ⟨[], H', [], ?_, List.prefix_refl H', trivial⟩
      have hes' : es = [] := List.eq_nil_of_length_eq_zero hes
      subst hes'
      exact .nil
  | _ :: _, [], hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases hlen
  | _ :: _, _ :: _, _, .cons _ _, _, [], _, hbl, _, _, _, _, _, _, _, _, _, _ => by cases hbl
  | _ :: _, .inst _ :: _, _, .cons _ _, _, _ :: _, _, _, _, _, _, _, hR, _, _, _, _, _ => by
    unfold Motives.results at hR
    cases hR
  | p :: ps, .plain :: ns, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, rs, hrs,
      ϖ, H', hH' => by
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    unfold Motives.results at hR
    unfold Args.results at hrs
    exact Args.evalResults hd ns (Nat.succ.inj hlen) ts (o + 1) bs hdrop' (Nat.succ.inj hbl) es
      hes hQ hR hrs ϖ H' hH'
  | p :: ps, .direct D :: ns, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, rs,
      hrs, ϖ, H', hH' => by
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
    obtain ⟨rs', hrs', rfl⟩ := Option.map_eq_some_iff.1 hrs
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
    have hR'' : Motives.results names Cs ns (ps := ps) ts.terms =
        some (R'.subst₀ (Subst₀.single (f D t))) := by
      let σ₀ : Subst 0 [] [] := fun x => nomatch x
      have h := Motives.results_subst names (Subst₀.toSubst (Subst₀.single (f D t))) ns hR'
      rw [Motives.subst_rename_of (θ' := σ₀) (fun x => by cases x),
        Motives.subst_id_of (fun x => by cases x), Terms.subst_rename_of (θ' := σ₀)
          (fun x => by cases x), Terms.subst_id_of (fun x => by cases x),
        ← Telescope.subst₀_eq_subst] at h
      exact h
    have hlen' : ns.length = ps.length := Nat.succ.inj hlen
    have hbl' : bs.length = ps.length := Nat.succ.inj hbl
    have hes' : es.length = (Telescope.nestResultParams ns ps).length := Nat.succ.inj hes
    by_cases he : e ∈ Mode.oneOne.erased
    · have hH'' : H'.Extends (H' ++ [.erased]) := List.prefix_append _ _
      obtain ⟨vs, H₂, R₂, hevs, hH₂, hruns⟩ := Args.evalResults hd ns hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' hrs' ϖ _ (hH'.trans hH'')
      refine ⟨H'.length :: vs, H₂, R₂, ?_, hH''.trans hH₂, fun h => (h he).elim, hruns⟩
      show EvalResults P ϖ H' E ρ ϱ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field o) :: _) (e.run :: _) _
        H₂ _
      rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
      exact .erased hevs
    · obtain ⟨v, H₂, R₁, hev, hH₂, hrun⟩ := hQt he (ϖ * e.run) H' hH'
      obtain ⟨vs, H₃, R₂, hevs, hH₃, hruns⟩ := Args.evalResults hd ns hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' hrs' ϖ _ (hH'.trans hH₂)
      refine ⟨v :: vs, H₃, R₁ ++ R₂, ?_, hH₂.trans hH₃, fun _ => (hrun C hC).mono hd hH₃, hruns⟩
      show EvalResults P ϖ H' E ρ ϱ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field o) :: _) (e.run :: _) _
        H₃ _
      rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
      exact .recursor hbo hev hevs

/-- Terms of a list evaluate to as many addresses. -/
theorem EvalAll.length_ofList {n : Nat} {ϖ : Multiplicity} {H H' : Heap} {E : List Nat} :
    (Ms : List (Multiplicity × Target n)) → {as : List Nat} → {R : List Nat} →
      EvalAll P ϖ H E (Targets.ofList Ms) as H' R → as.length = Ms.length
  | [], _, _, .nil => rfl
  | _ :: Ms, _, _, .cons _ hs => congrArg (· + 1) (EvalAll.length_ofList Ms hs)

/-- The fields of arguments related at the recursive fields by `V`, at the addresses to which the
terms `G (some D)` of their types `D` evaluate, satisfy `Q`, when `Q D` holds of each term of a
recursive field that `V D` relates, at each address to which `G (some D)` evaluates, at some weight,
in a heap that extends `H₀`, to a heap that `Hf` extends. -/
theorem EvalAll.recAt {n : Nat} {ϖ : Multiplicity} {E : List Nat}
    {G : Option Name → Multiplicity × Target n}
    {V : Name → TermRel} {Q : Name → Term 0 [] → Nat → Prop} {H₀ Hf : Heap} :
    {ps : List Parameter} → (rs : List (Option Name)) →
    (∀ D, some D ∈ rs → ∀ t u, V D t u → ∀ ϖ' Ha b Hb R, H₀.Extends Ha →
      Eval P ϖ' Ha E (G (some D)).2 b Hb R → Hb.Extends Hf → Q D t b) →
    rs.length = ps.length → (es : List Grade) → (ts us : Args 0 [] ps) → {H₁ : Heap} →
    {as : List Nat} → {R : List Nat} → H₀.Extends H₁ →
    EvalAll P ϖ H₁ E (Targets.ofList (rs.map G)) as Hf R →
    Terms.RecRel V rs ts.terms us.terms → Terms.RecAt Q rs es ts.terms as
  | [], [], _, _, _, .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, some D :: rs, hG, hl, _ :: es, .cons t ts, .cons u us, _, _, _, hH, .cons h hs, hV =>
    ⟨fun _ => hG D (List.mem_cons_self ..) t u hV.1 _ _ _ _ _ hH h hs.extends,
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
  {as : InstanceArgs 0 Γ decl.scope} {r ς χ' : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
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
      (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
    RunValid sig ι P ((hΓ.extend _).extend _)
      ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
      (((δs i).extendGrades (gs i) (con.params (.ofLists qs ps hq hp))).extendResults
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
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
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    {σ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ σ) {j : Nat}
    {T' : DataType decl.sorts decl.grades decl.levels decl.scope} {C' : Term 0 (.var :: Γ)}
    (hj : decl.dataTypes[j]? = some T') (hCj : Cs.get j = some ⟨0, C'⟩) {t v : Term 0 []}
    (htv : RedStar (sig.interpret ι) t v)
    (hvt : ValidTerm₀ sig ι t (.inst T'.name qs ls ps (as.subst σ))) {H : Heap} {b : Nat}
    (hrun : RunsAs sig ι P H
      (.recursor r ς χ' T'.name qs ls ps (as.subst σ) v κ (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))) :
    RunsAs sig ι P H (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
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
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {σ : Subst 0 [] Γ} {H : Heap}
    {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V)
    (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {i j : Nat} {T' : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T') (hcon : con ∈ T'.constructors)
    (hi : decl.cases[i]? = some (j, T', con)) {fs : Terms 0 []} {w : Term 0 []}
    (hw : w.IsCtor T'.name con.name fs)
    (hwv : ValidTerm₀ sig ι w (.inst T'.name qs ls ps (as.subst σ))) {H' : Heap}
    (hH' : H.Extends H') (ϖ₀ : Multiplicity) {a : Nat} {πv ϱv : List Multiplicity}
    {bs : List Nat} (ha : H'[a]? = some (.ctor i πv ϱv bs))
    (hπv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀, πv[l]? = some π₀ ∧ r.run * π₀ ≤ r.run * p.usage.run)
    (hκv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
        (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀))
    {ϱ : Multiplicity}
    (hϱv : ∀ l ∈ ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
        (fun y => y.1.map fun _ => y.2), ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
          (r.run * π₀ ≠ .zero → ϱ ≤ ϱ₀ * (r.run * π₀)))
    (hϱ0 : r.run = .zero → ϱ = .omega)
    (hfr : ∀ ts : Args 0 [] (con.params (.ofLists qs ps hq hp)), ts.terms = fs →
      EqSubst sig ι (Context.empty.append
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ))) ts.toSubst ts.toSubst →
      Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms →
      RunsAsArgs sig ι P H' (gs i) ts bs
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)) ∧
      Terms.RecAt (fun D' t b => ∀ ϖ' H'', H'.Extends H'' → ∃ v H₂ tr,
        EvalRec P ϖ' H'' E r.run ϱ (us.erase sig Mode.oneOne.erased hΓ r
          (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) b v H₂
          tr ∧ H''.Extends H₂ ∧
        ∀ C, (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩ →
          RunsAs sig ι P H₂ (.recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) v
            (C.subst₀ (Subst₀.single t)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) (us.grades i) ts.terms bs) :
    ∃ v H₃ tr, EvalRec P ϖ₀ H' E r.run ϱ (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a v H₃ tr ∧
      H'.Extends H₃ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ →
        RunsAs sig ι P H₃ (.recursor r ς χ' T'.name qs ls ps (as.subst σ) w κ (Cs.subst σ) (us.subst σ))
          v ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hT' : T' ∈ decl.dataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, -, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
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
  have hn := hns i j T' con hi
  have hrn := Telescope.recursion_eq_map_nest decl.names (con.fields (.ofLists qs ps hq hp))
  obtain ⟨Rt, hRt⟩ := Constructor.results_isSome con (.ofLists qs ps hq hp)
    (fun _ hD' => Motives.get_idxOf hT hnd hCs hD') hn
  -- The terms of the recursive results, the recursor on each recursive field.
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  obtain ⟨rs, hrsf, hrs⟩ : ∃ rs,
      ts.results f ((con.fields (.ofLists qs ps hq hp)).nest decl.names) = some rs ∧ Constructor.ResultTerms sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp)
        decl.names (ls.getFin hl) (as.subst σ)
        (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
        (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ts rs := by
    obtain ⟨rs, h₁, h₂⟩ := Constructor.resultTerms_results (sig := sig) (v := ⟨κ.quality, r, ς⟩)
      (names := decl.names) (ls.getFin hl) (as.subst σ)
      (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
      (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ts hn
    rw [funext fun D'' => funext fun t =>
      Term.recursorAt_subst₀ r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ) D'' t] at h₁
    exact ⟨rs, h₁, h₂⟩
  obtain ⟨gs₀, hgs, hget⟩ := Branches.get_erase sig Mode.oneOne.erased hΓ r us
    (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams T.name qs ps).getD [])
    hu
  -- The positions of the recursive fields of each case.
  let rfs : List (List Nat) := decl.cases.map fun x =>
    ((x.2.2.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
      fun y => y.1.map fun _ => y.2
  have hrfs : sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ' = rfs.map (·.map .field) := by
    rw [hd.recursiveResults ⟨hdecl, hT, rfl⟩ hq hp,
      TypeDeclaration.recursiveResults_of_not_nested hns]
    rfl
  rw [hrfs] at hQ hget ⊢
  rw [RecursiveResult.headD_drop_map_field] at hget
  simp only [RecursiveResult.getD_map_field] at hget
  rw [hgs] at hQ
  have hpos : (rfs.drop i).headD [] =
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
        fun y => y.1.map fun _ => y.2 :=
    List.headD_drop (by rw [List.getElem?_map, hi]; rfl)
  have hpos' : (rfs.drop i).headD [] =
      (((con.fields (.ofLists qs ps hq hp)).nest decl.names).map Nest.blockName).zipIdx.filterMap
        fun y => y.1.map fun _ => y.2 := hrn ▸ hpos
  obtain ⟨vs, H₂, tr₁, hevs, hH₂, hruns⟩ := Args.evalResults hd
    ((con.fields (.ofLists qs ps hq hp)).nest decl.names) (Telescope.length_nest _ _)
    ts 0 bs List.drop_zero (RunsAsArgs.length hfa) gs₀.toList gs₀.length_toList (hrn ▸ hQ)
    (Constructor.results_subst_append hRt σ ts) hrsf ϖ₀ H' (List.prefix_refl _)
  -- The branch, at the substitution of its context by `σ`, the fields and the results.
  have hres := EqSubst.results (sig := sig) (ι := ι) (f₁ := f) (f₂ := f) _ ts ts
    (Constructor.results_subst_append hRt σ ts) hrsf hrsf
    (Terms.RecRel.of_diag _ (fun D hD t₁ hVt C hC => by
        obtain ⟨j₃, T₃, C₃, hj₃, rfl, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ
          (Telescope.mem_recursion (hrn ▸ hD)) hC
        exact hrec j₃ T₃ C₃ hj₃ hC₃ σ hσ t₁ hVt) (hrn ▸ hrecV))
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
  rw [hgs, GradeVector.extendResults_resultGrades] at hbr
  -- The branch binds its variables to cells, at the multiplicities of its binders.
  let πs₀ : Fin (con.params (.ofLists qs ps hq hp)).length → Multiplicity := fun l =>
    r.fieldMultiplicity
      (((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?.map (·.usage))
      ((((rfs.drop i).headD []).map RecursiveResult.field).zip gs₀.toList |>.find?
        fun x => x.1.fieldPosition == some (l : Nat))
  let πs₀' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length → Multiplicity :=
    fun j => gs₀[j].run
  have hlen : ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)).length = (bs ++ vs).length := by
    simp only [List.length_map, List.length_append, List.length_ofFn, RunsAsArgs.length hfa,
      RunsAsArgs.length hruns]
  let H₂' := H₂.bind ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)) (bs ++ vs)
  have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
  have hB : H₂'.Binds ((List.range' H₂.length (bs ++ vs).length).reverse ++ E)
      (vs.reverse ++ (bs.reverse ++ V)) := by
    have h' := (Heap.binds_bind H₂ hlen).reverse.append (hEV.mono (hH'.trans (hH₂.trans hH₂')))
    rwa [List.reverse_append, List.append_assoc] at h'
  obtain ⟨v, H₃, tr₂, hev, hH₃, hrun⟩ := hbr ϖ₀ _ H₂' _ _ hEqbr hB (hσr.mono hd hH₂')
  -- The erased recursor steps to the erased branch.
  have hks : List.ofFn
      (fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?) =
      List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field l)
        gs₀.toList (((((con.fields (.ofLists qs ps hq hp)).nest decl.names).map
          Nest.blockName).zipIdx 0).filterMap fun y => y.1.map fun _ => y.2) := by
    rw [hpos']
    exact List.ofFn_ite_getElem? _ _ RecursiveResult.ofPosition gs₀ _
      (Telescope.length_positions _ (Telescope.length_nest _ _) hn 0)
  have hπs' : List.ofFn πs₀' = gs₀.toList.map Grade.run := by
    apply List.ext_getElem <;> simp [πs₀']
  rw [← hπs'] at hevs
  -- The parameter of each field, which the signature gives the case.
  have hfs : ∀ (l : Nat) (p' : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p' →
      ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[l]? = some p' :=
    fun l p' hp' => by
      rw [hd.caseFieldParams ⟨hdecl, hT, rfl⟩ hq hp, Option.getD_some,
        List.headD_drop (by rw [List.getElem?_map, hi]; rfl), hp']
  -- The uses of each field by the branch are within those that the constructor allows.
  have hπ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length,
      ∃ π₀, πv[(l : Nat)]? = some π₀ ∧ r.run * π₀ ≤ πs₀ l + r.run * recursionsAt
      (List.ofFn fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?)
      (List.ofFn πs₀') l := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, hπ₀, hle⟩ := hπv l p' hp'
    refine ⟨π₀, hπ₀, ?_⟩
    have hgl := hg i j T' con l p' hi hp'
    rw [hgs] at hgl
    have he := Grade.fieldMultiplicity_positions r p'.usage
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) gs₀.toList 0 l hn
    have hr := Telescope.recursionsAt_positions Mode.oneOne.erased (by decide)
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) gs₀.toList 0 l hn
    rw [Nat.zero_add] at he hr
    rw [hks, hπs', hr]
    simp only [πs₀, hfs l p' hp', Option.map_some, hpos', he]
    exact Grade.run_mul_le_fieldMultiplicity π₀ r p'.usage _ _ hle hgl
  -- The coefficient of the ownership of each field is within the one that the constructor
  -- allows.
  have hκ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length, ∃ π₀ ϱ₀,
      πv[(l : Nat)]? = some π₀ ∧ ϱv[(l : Nat)]? = some ϱ₀ ∧
      r.fieldCoefficient ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?
        ≤ ϱ₀ * (r.run * π₀) := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hκv l p' hp'
    refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
    rw [hfs l p' hp']
    exact hle
  -- The requirement of the recursion is within the requirement times the uses of each field on
  -- which a recursive result recurses: such a field has recursions, so that the constructor
  -- allows uses of it unless the grade of the recursor has none at run time.
  have hϱ : ∀ (j' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) (l : Nat),
      (if gs₀[j'] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else .ofPosition ((rfs.drop i).headD [])[(j' : Nat)]?) = .field l →
        ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧ ϱ ≤ ϱ₀ * (r.run * π₀) := by
    intro j' l hl
    have hl₀ := hl
    split at hl
    · cases hl
    · rename_i hg'
      have hl' : ((rfs.drop i).headD [])[(j' : Nat)]? = some l := by
        revert hl
        cases ((rfs.drop i).headD [])[(j' : Nat)]? <;> simp [RecursiveResult.ofPosition]
      rw [hpos] at hl'
      obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hϱv l (List.mem_of_getElem? hl')
      refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
      have hlt := Telescope.lt_of_mem_positions _ 0 (List.mem_of_getElem? hl')
      rw [Telescope.length_recursion, Nat.zero_add] at hlt
      obtain ⟨π₁, hπ₁, hle₁⟩ := hπ ⟨l, hlt⟩
      cases hπ₀.symm.trans hπ₁
      have hne := recursionsAt_ne_zero (l := l) (k := .field l) (π := πs₀' j') rfl
        ((by decide : ∀ g : Grade, g ∉ Mode.oneOne.erased → g.run * .one ≠ .zero) _ hg')
        (ks := List.ofFn
          fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
          if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
          else .ofPosition ((rfs.drop i).headD [])[(j : Nat)]?)
        (πs := List.ofFn πs₀') (j := j')
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]; exact congrArg some hl₀)
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn])
      by_cases hz : r.run * π₀ = .zero
      · rw [hϱ0 ((by decide : ∀ ρ π₀ π x : Multiplicity, ρ * π₀ ≤ π + ρ * x → x ≠ .zero →
          ρ * π₀ = .zero → ρ = .zero) _ _ _ _ hle₁ hne hz)]
        exact (by decide : ∀ x : Multiplicity, .omega ≤ x) _
      · exact hle hz
  refine ⟨v, H₃, tr₁ ++ tr₂, .iota ha hget (RunsAsArgs.length hfa) hπ hκ hϱ (hks ▸ hevs)
    ((Eval.cast _).2 hev), hH₂.trans (hH₂'.trans hH₃), fun C'' hC'' => ?_⟩
  rw [hC'] at hC''
  cases hC''
  -- The recursor on the constructor steps to the branch, at the motive at the constructor.
  rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hrun
  have hrun₁ := (RunsAs.redStar_iff hd
    (.step (Red.iota_subst (D' := T'.name) (qs'' := qs') (ls'' := ls') (ps'' := ps') (as := as')
      ⟨hdecl, hT', rfl⟩ hi σ hq hl hp ts hu hrs) (.refl _))).2 hrun
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
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∉ Mode.oneOne.erased) {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ))
    (ht : RunsAs sig ι P H₁ t a ((Term.inst D qs ls ps as).subst σ)) :
    ∃ b H₂ tr, EvalRec P ϖ₀ H₁ E r.run
        (sig.recursionRequirement D qs ps ⟨κ.quality, r, ς⟩ χ').run (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a b H₂ tr ∧
      H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
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
      RunTelRel.mono hd ihmono (K := Eq) (fun e => e ▸ List.prefix_refl _) (fun _ => rfl)
        (hS X T hT c hc) _ _ (hS Y T hT c hc)
        (fun _ => Nest.map_rel₃
          (fun D' H _ e _ _ => e ▸ RunRel.computed_mono (hXY D' H)) _) H H rfl
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let ϱ := (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  -- The relations of the canonical terms that `(®_μ)` relates and on whose addresses the erased
  -- recursor evaluates, in each heap that extends `H`, to the address of a value related to the
  -- recursor at the motive.
  let X : Name → RunRel := fun D' H₀ w a => DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D' H₀ w a ∧
    ∀ ϖ' H', H₀.Extends H' → H.Extends H' →
      ValidTerm₀ sig ι w (.inst D' qs ls ps (as.subst σ)) →
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        ∃ b H₂ tr, EvalRec P ϖ' H' E r.run ϱ Ns a b H₂ tr ∧ H'.Extends H₂ ∧
          RunsAs sig ι P H₂ (f D' w) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w))
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ H₀ w a, T'.runCtorRel sig (.ofLists qs ps hq hp) T'.name (S X) H₀ w a →
      X T'.name H₀ w a := by
    intro T' hT' H₀ w a hc
    have hcb := DataType.runCtorRel_mono (List.prefix_refl H₀)
      (fun c hc' ts bs => hmono X _ (fun _ _ _ _ h => h.1) T' hT' c hc' H₀ ts bs) hc
    refine ⟨DataType.runBlockRel_fold hmono hT' hcb, fun ϖ' H' hH' hHH' hwv C' hC' => ?_⟩
    obtain ⟨con, hcon, i, fs, bs, hw, hi, ha, hSX⟩ := hc
    -- The case of the constructor.
    obtain ⟨j₀, hij⟩ := hd.cases_of_constructorCase ⟨hdecl, hT', rfl⟩ hcon hi
    obtain ⟨i', j, hi', hj⟩ := TypeDeclaration.exists_cases hT' hcon
    obtain rfl : i = i' := List.getElem?_inj_of_nodup_map (hd.cases_nodup hdecl) hij hi' rfl
    rw [hidx j T' hj] at hC'
    obtain ⟨v, H₃, tr, hev, hH₃, hrun⟩ := RunsAs.recursor_ctor (ϱ := ϱ) hd ⟨hdecl, hT, rfl⟩ hv hadm
      has hCs
      hCv hus hns hrec husr hg hχ hs hσ hEV hE hj hcon hi' hw hwv hHH' ϖ' (hH'.getElem? ha)
      (fun l p hlp => ⟨_, by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ π π' : Multiplicity, π * π' ≤ π * π') _ _⟩)
      (fun l p hlp => ⟨_, _, by rw [List.getElem?_map, hlp]; rfl,
        by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ a r q : Grade, (a * (r * q)).run ≤ a.run * (r.run * q.run)) _ _ _⟩)
      (fun l hl => by
        -- The requirement of the recursion is below the coefficient of the field.
        have hlt := Telescope.lt_of_mem_positions _ 0 hl
        rw [Telescope.length_recursion, Nat.zero_add] at hlt
        refine ⟨_, _, by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl,
          by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl, fun hne => ?_⟩
        show (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run ≤ _
        rw [hd.recursionRequirement_eq ⟨hdecl, hT, rfl⟩ hq hp]
        have h1 : Mode.oneOne.grade * r = r := Grade.modality.semiring.one_mul r
        have hle := TypeDeclaration.recursionRequirement_run_le (sig := sig)
          (v := ⟨κ.quality, r, ς⟩) (m := .oneOne) (χ := χ') (qs := qs) (ps := ps) hi' hl
          (List.getElem?_eq_getElem hlt) (by rw [h1]; rwa [(Grade.run_op _ _).2.1])
        rw [h1] at hle
        rwa [(Grade.run_op _ _).2.1] at hle)
      (fun h0 => absurd ((by decide : ∀ g : Grade, g.run = .zero → g ∈ Mode.oneOne.erased) r h0) hr)
      fun ts hfs hts hrecV => by
        subst hfs
        -- The fields, related at their types.
        refine ⟨(RunsAsArgs.of_fields hd hdecl hv hT' hcon hq hl hp hadm hasσ hs hS
          (fun T' hT' => (hU T' hT').1) (fun _ _ _ _ h => h.1) hts (gs i)
          (fun l p hl' hgl => (by decide : ∀ r p g x : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + x * r → g ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased) r p.usage
            (gs i l) _ hr (hg i j T' con l p hi' hl') hgl) hSX).mono hd hH', ?_⟩
        -- The recursive results used at run time, of fields that `X` relates.
        rw [Telescope.recursion_eq_map_nest] at hrecV ⊢
        refine RunTelRel.recAt (hS X T' hT' con hcon) _ (Telescope.length_nest _ _)
          (hns i j T' con hi') (fun l D hD => ?_) ts bs hSX hrecV _
          (fun l p hl' he => (by decide : ∀ r p g e : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + e * r → e ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased)
            r p.usage _ _ hr (hg i j T' con l p hi' hl') he)
        have hr' : (con.fields (.ofLists qs ps hq hp)).nestAt decl.names l = .direct D := by
          simp only [Telescope.nestAt, hD, Option.getD_some]
        refine ⟨(_, (X D).computed sig ι), by rw [hr']; rfl,
          fun t b ⟨v, hcv, hXv⟩ hVt ϖ'' H'' hH'' => ?_⟩
        have hDn := Telescope.mem_names_of_direct_mem (List.mem_of_getElem? hD)
        obtain ⟨C₃, hC₃⟩ := Motives.get_idxOf hT hnd hCs hDn
        obtain ⟨j₃, T₃, C₃', hj₃, rfl, hC₃', -⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn (Motives.get_subst σ hC₃)
        rw [hidx j₃ T₃ hj₃, hC₃'] at hC₃
        cases hC₃
        have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        obtain ⟨b', H₃, tr', hev, hH₃, hrun⟩ := hXv.2 ϖ'' H'' (hH'.trans hH'') (hHH'.trans hH'')
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
      (hRw X hclosed).2 ϖ₀ H₁ (List.prefix_refl _) hH₁ (hwv.trans hwv.symm) C hC₀
    exact ⟨b, H₂, tr, hev, hH₂, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC htw.1 htv hrun⟩

/-- `r ∈ S`, by induction on `(eq_μ)`: the term of the skeleton of the instance evaluates to an
address that the erased recursor eliminates to the address of a value to which the recursor on a
term of the instance is related at the motive at the term, when every type of the block has one
constructor at most. -/
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
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∈ Mode.oneOne.erased) (h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ)) :
    ∃ a H₂ b H₃ tr, Eval P (ϖ₀ * r.run) H₁ E ((sig.skeleton D qs ps).target : Target Γ.length) a H₂ [] ∧
      EvalRec P ϖ₀ H₂ E r.run .omega (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams D qs ps).getD [])) a b H₃
        tr ∧ H₁.Extends H₃ ∧
      RunsAs sig ι P H₃ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, -, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  -- The erased recursor on the term of a skeleton of the type `D'` of a canonical term `v`, within
  -- the depth of the number of the types of the block minus that of the ancestors `A` of `D'`,
  -- evaluates, in each heap that extends the heap of this term, to the address of a value related
  -- to the recursor on `v` at the motive.
  let Pk : Name → Term 0 [] → Prop := fun D' v => ∀ (A : List Name) (d : Nat), A.Nodup →
    (∀ X ∈ A, X ∈ decl.names) → (∀ X ∈ A, Relation.TransGen (decl.Below I) D' X) →
    d + A.length = decl.names.length → ∀ ϖ' H₂ a H₃ tr₀, H.Extends H₂ →
    Eval P ϖ' H₂ E ((decl.skeleton I d D').target : Target Γ.length) a H₃ tr₀ →
    ValidTerm₀ sig ι v (.inst D' qs ls ps (as.subst σ)) → ∀ ϖ'' H', H₃.Extends H' →
    ∃ b H₄ tr, EvalRec P ϖ'' H' E r.run .omega Ns a b H₄ tr ∧ H'.Extends H₄ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        RunsAs sig ι P H₄ (f D' v) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))
  -- The relations of the canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`,
  -- and on the terms of whose skeletons the erased recursor evaluates as `Pk` states.
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
    intro A d hA hAn hAD hdA _ H₂ a H₃ _ hH₂ hev hvv ϖ'' H' hH'
    -- The depth is not reached, since the ancestors are fewer than the types of the block.
    have hlt := TypeDeclaration.length_ancestors_lt hacc (TypeDeclaration.name_mem_names hT') hA
      hAn hAD
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    -- The term of the skeleton unfolds into the constructor of the case of the type.
    obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
    rw [TypeDeclaration.skeleton_succ hnd I hT' rfl hcons
      (Entry.constructorCase_of_cases (hd.cases_nodup hdecl) hi)] at hev
    cases hev with
    | @ctor _ _ _ H₂₀ _ _ _ bs _ hall =>
    have hH₂₀ : H₂₀.Extends H' := (List.prefix_append H₂₀ _).trans hH'
    have hHH' : H.Extends H' := hH₂.trans (hall.extends.trans hH₂₀)
    have hbl : bs.length = (con.params I).length := by
      rw [EvalAll.length_ofList _ hall, List.length_map, Telescope.length_recursion]
    -- The fields of the term of the skeleton are stored at the multiplicity `0`, and the grade of
    -- the recursor has no use at run time.
    have hπv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
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
    -- The fields of the term of the skeleton are stored at the requirement `ω`, and the
    -- coefficients of their ownerships are `0`, since the grade of the recursor has no use at run
    -- time.
    have hκv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀ ϱ₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target Γ.length))
            | none => (.zero, .erased))).requirements[l]? = some ϱ₀ ∧
          (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀) := fun l p hlp => by
      obtain ⟨π₀, hπ₀, -⟩ := hπv l p hlp
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨π₀, .omega, hπ₀, ?_, (by decide : ∀ (r a q : Grade) (π : Multiplicity),
        r ∈ Mode.oneOne.erased → (a * (r * q)).run ≤ .omega * (r.run * π)) r _ _ _ hr⟩
      rw [Targets.requirements_ofList, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hl)]
      rfl
    obtain ⟨b, H₄, tr, hevr, hH₄, hrun⟩ := RunsAs.recursor_ctor hd ⟨hdecl, hT, rfl⟩ hv hadm has
      hCs hCv hus hns hrec husr hg hχ hs hσ hEV hE hj hcon hi hvc hvv hHH' ϖ''
      (hH'.getElem? List.getElem?_concat_length) hπv hκv
      (fun l hl => by
        -- The fields of the term of the skeleton, which the recursor does not use, state nothing of
        -- the requirement of its recursion.
        have hlt := Telescope.lt_of_mem_positions _ 0 hl
        rw [Telescope.length_recursion, Nat.zero_add] at hlt
        obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, -⟩ := hκv l _ (List.getElem?_eq_getElem hlt)
        exact ⟨π₀, ϱ₀, hπ₀, hϱ₀, fun hne => absurd ((by decide : ∀ (g : Grade) (π : Multiplicity),
          g ∈ Mode.oneOne.erased → g.run * π = .zero) r π₀ hr) hne⟩)
      (fun _ => rfl)
      fun ts' hfs _ _ => by
        rw [hfs]
        -- The fields are erased, at grades erased since the grade of the recursor is.
        refine ⟨RunsAsArgs.of_erased ts' bs _ (fun l p hl' => (by decide : ∀ r p g x : Grade,
          r ∈ Mode.oneOne.erased → r * p ≤ g + x * r → g ∈ Mode.oneOne.erased) r p.usage
          (gs i l) _ hr (hg i j T' con l p hi hl')) hbl, ?_⟩
        -- The recursive results used at run time, on the terms of the skeletons of the recursive
        -- fields.
        refine EvalAll.recAt _ (fun D'' hD'' t u ⟨v₁, w₁, hcv, hcw, hX₁⟩ ϖa Ha b' Hb Rb hHa hevb
          hHb ϖb H'' hH'' => ?_) (Telescope.length_recursion _ _) _ ts us' (List.prefix_refl _)
          hall hrX
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
          (by simp only [List.length_cons]; omega) ϖa Ha b' Hb Rb (hH₂.trans hHa) hevb
          (hvv₁.trans hvv₁.symm) ϖb H'' (hHb.trans (hH₂₀.trans hH''))
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
  obtain ⟨a, H₂, hev, hH₂⟩ :=
    (decl.skeleton I decl.names.length T.name).target_isData.eval P (ϖ₀ * r.run) H₁ E
  obtain ⟨b, H₃, tr, hevr, hH₃, hrun⟩ := hX.2.2 [] _ List.nodup_nil (fun _ h => nomatch h)
    (fun _ h => nomatch h) rfl _ H₁ a H₂ [] hH₁ hev (hww.trans hww.symm) ϖ₀ H₂
    (List.prefix_refl _)
  refine ⟨a, H₂, b, H₃, tr, ?_, hevr, hH₂.trans hH₃, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC
    hw₁.1 htv (hrun C ((hidx h' T hh).symm ▸ hC))⟩
  rw [hd.skeleton ⟨hdecl, hT, rfl⟩ hq hp]
  exact hev


-- ADE: the cases `natrecₘ`, `prodrecₘ`, `unitrecₘ` and `emptyrecₘ` of `fundamental`, in
-- `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- `(rec)` keeps the validity at run time: the erasure of the recursor evaluates its term, or the
term of the skeleton of its instance when its grade `r` is erased, then the branch of the case of
its value. A recursor on a block of propositions has no constructor, in the mode `11ᵐ`, so that no
term of its instance is true and none is substituted. -/
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
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hns : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ .inst ms)
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t,
      ValidTerm₀ sig ι t ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidTerm₀ sig ι (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)))
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : r ∉ Mode.oneOne.erased → RunValid sig ι P hΓ ctx γ t (.inst D qs ls ps as))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      Mode.oneOne.grade * r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hr : (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) → r.mode = .oneOne)
    (hprop : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases = []) :
    RunValid sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ χ) (.recursor r ς χ' D qs ls ps as t κ Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  intro w σ H E V hσ hEV hE
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS := Mode.erasesUncounted .oneOne
  have hEχ : RunsAsSubst sig ι P H ctx χ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  have hg' : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i) l) * r := fun i j T' con l p hi hl' => by
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
    obtain ⟨S, hP, hmono, -, -, -⟩ := hv.propRel hd hdecl hq hl hp hadm hasσ hs
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
    · -- The term of the skeleton of the instance stands for the term.
      have h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1 := fun T' hT' => by
        refine Nat.le_of_not_lt fun h2 => ?_
        exact (by decide : ∀ r : Grade, r ∈ Mode.oneOne.erased → r.mode ≠ .oneOne) r hrS
          (hr ⟨T', hT', h2⟩)
      obtain ⟨a, H₂, b, H₃, tr, hev, hevr, hH₃, hrun⟩ := RunsAs.recursor_skeleton hd h hv hadm
        has hh hC hCs hCv hus hns hrec husr hg' hχ hs hrS h1 hσ hEV hEχ (List.prefix_refl H) w htσ
      refine ⟨b, H₃, [] ++ tr, ?_, hH₃, hrun⟩
      show Eval P w H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _) b H₃ _
      rw [ite_eq_left hrS, ite_eq_left hrS]
      exact .recursor hev hevr
    · -- The term evaluates to the address of its value.
      have hγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h (hS.mul _ _ hrS (hS.add _ _ h'))) hE
      obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr hrS (w * r.run) σ H E V hσ hEV hγ
      obtain ⟨b, H₂, tr₂, hevr, hH₂, hrun⟩ := RunsAs.recursor hd h hv hadm has hh hC hCs hCv hus hns
        hrec husr hg' hχ hs hrS hσ hEV hEχ hH₁ w htσ hta
      refine ⟨b, H₂, tr₁ ++ tr₂, ?_, hH₁.trans hH₂, hrun⟩
      show Eval P w H E (.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _) b H₂ _
      rw [ite_eq_right hrS, ite_eq_right hrS]
      exact .recursor hev hevr

end

end Sic.Core
