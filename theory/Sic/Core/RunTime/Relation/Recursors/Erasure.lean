module

public import Sic.Core.RunTime.Relation
import Sic.Core.RunTime.Relation.Skeleton
import Sic.Core.Syntax.Signature

/-!
# Erasure of the Recursors at Run Time

The properties of the cases of a block of data types, of the erased branches of a recursor and of
the positions and the grades of its recursive results, which the relation of run time of the
recursors reads.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

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

end Sic.Core
