module

public import Sic.Core.RunTime.Relation
import Sic.Core.Erasure.Fields
import Sic.Core.RunTime.Relation.Skeleton
import Sic.Core.Syntax.Signature

/-!
# Erasure of the Recursors at Run Time

The properties of the cases of a block of data types, of the erased branches of a recursor and of
the recursions and the grades of its recursive results, which the relation of run time of the
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

/-- No recursion of the recursive results of the fields from the position `o`, each erased when its
grade is in `S`, runs on a field before `o`. -/
theorem RecursiveResult.recursionsAt_ofField_lt (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    {f : Nat → Option Name} {s : Nat → Option Shape} (ns : List (Nest Name)) {o x : Nat}
    (hx : x < o) : (es : List Grade) →
    recursionsAt (List.zipWith (fun e w => if e ∈ S then RecursiveResult.erased else w) es
      ((Telescope.nestPositions ns o).map fun l => RecursiveResult.ofField (f l) (s l) l))
      (es.map Grade.run) x = .zero := by
  generalize hws : ((Telescope.nestPositions ns o).map fun l =>
    RecursiveResult.ofField (f l) (s l) l) = ws
  have hmem : ∀ w ∈ ws, ∀ y, w.fieldPosition = some y → o ≤ y := fun w hw y hy =>
    RecursiveResult.le_of_mem_ofField (hws ▸ hw) hy
  clear hws
  induction ws with
  | nil => intro es; cases es <;> rfl
  | cons w ws ih =>
    intro es
    cases es with
    | nil => rfl
    | cons e es =>
      have hne : (if e ∈ S then RecursiveResult.erased else w).fieldPosition ≠ some x := by
        split
        · exact nofun
        · exact fun h => absurd (hmem w List.mem_cons_self x h) (by omega)
      simp only [List.zipWith_cons_cons, List.map_cons, recursionsAt, hne, ↓reduceIte,
        ih (fun w' hw' => hmem w' (List.mem_cons_of_mem _ hw')) es]
      rfl

/-- The recursion that the recursive result of the field at `o` runs on this field: its factor, at
the multiplicity of its grade. -/
theorem RecursiveResult.recursionsAt_ofField_self (r : Option Name) (s : Option Shape) (o : Nat)
    (m : Multiplicity) :
    (if (RecursiveResult.ofField r s o).fieldPosition = some o then
      m * (RecursiveResult.ofField r s o).factor else .zero) + .zero =
      m * (RecursiveResult.ofField r s o).factor := by
  cases r with
  | some D =>
    show (if some o = some o then _ else _) + _ = _
    rw [ite_eq_left rfl]
    exact (by decide : ∀ m n : Multiplicity, m * n + .zero = m * n) _ _
  | none =>
    cases s with
    | some σ =>
      show (if some o = some o then _ else _) + _ = _
      rw [ite_eq_left rfl]
      exact (by decide : ∀ m n : Multiplicity, m * n + .zero = m * n) _ _
    | none =>
      show (if (none : Option Nat) = some o then _ else _) + _ = m * .zero
      rw [ite_eq_right nofun]
      exact (by decide : ∀ m : Multiplicity, Multiplicity.zero + .zero = m * .zero) _

/-- `0` plus a multiplicity is this multiplicity. -/
theorem _root_.Sic.Grading.Multiplicity.zero_add' : ∀ m : Multiplicity, .zero + m = m := by
  decide

-- ADE: none.
/-- The recursions that the recursive results of the fields whose nestings are `ns`, from the
position `o`, each erased when its grade in `es` is in `S`, run on the field at `o + l`, at the
run-time multiplicities of their grades: the run-time multiplicity of the grade of the result of the
field times its factor in `πs`, when the grades of `S` have no use at run time and the factor of each
recursive result is the run-time multiplicity of the factor in `πs` at its index. -/
theorem Telescope.recursionsAt_results (S : Math.Set Grade) [DecidablePred (· ∈ S)]
    (hS : ∀ e ∈ S, e.run = .zero) (f : Nat → Option Name) (s : Nat → Option Shape) :
    (ns : List (Nest Name)) → (o : Nat) → (es πs : List Grade) →
    (∀ (j : Nat) (w : RecursiveResult), ((Telescope.nestPositions ns o).map fun l =>
      RecursiveResult.ofField (f l) (s l) l)[j]? = some w →
        ∃ π : Grade, πs[j]? = some π ∧ w.factor = π.run) → (l : Nat) →
    recursionsAt (List.zipWith (fun e w => if e ∈ S then RecursiveResult.erased else w) es
      ((Telescope.nestPositions ns o).map fun l => RecursiveResult.ofField (f l) (s l) l))
      (es.map Grade.run) (o + l) =
      (Telescope.resultGrades ns (List.zipWith (· * ·) es πs) l).run
  | [], _, es, _, _, _ => by cases es <;> rfl
  | .plain :: ns, o, es, πs, hf, l => by
    rw [Telescope.nestPositions_plain] at hf ⊢
    cases l with
    | zero => exact (RecursiveResult.recursionsAt_ofField_lt S ns (Nat.lt_succ_self o) es).trans rfl
    | succ l =>
      rw [show o + (l + 1) = o + 1 + l by omega]
      exact Telescope.recursionsAt_results S hS f s ns (o + 1) es πs hf l
  | .direct _ :: ns, o, es, πs, hf, l | .inst _ :: ns, o, es, πs, hf, l => by
    rw [Telescope.nestPositions_cons rfl, List.map_cons] at hf ⊢
    obtain ⟨π, hπ, hw⟩ := hf 0 _ rfl
    cases πs with
    | nil => cases hπ
    | cons π' πs =>
      cases hπ
      have hf' : ∀ (j : Nat) (w : RecursiveResult), ((Telescope.nestPositions ns (o + 1)).map
          fun l => RecursiveResult.ofField (f l) (s l) l)[j]? = some w →
          ∃ π : Grade, πs[j]? = some π ∧ w.factor = π.run := fun j w h => hf (j + 1) w h
      cases es with
      | nil => simp only [List.zipWith_nil_left, Telescope.resultGrades_nil]; rfl
      | cons e es =>
        simp only [List.zipWith_cons_cons, List.map_cons, recursionsAt]
        cases l with
        | zero =>
          show _ + recursionsAt _ _ o = (e * π).run
          rw [RecursiveResult.recursionsAt_ofField_lt S ns (Nat.lt_succ_self o)]
          rw [(Grade.run_op _ _).2.1]
          by_cases he : e ∈ S
          · simp only [he, ↓reduceIte, RecursiveResult.fieldPosition, hS e he]
            exact (by decide : ∀ m : Multiplicity, Multiplicity.zero + .zero = .zero * m) _
          · simp only [he, ↓reduceIte]
            rw [← hw]
            exact RecursiveResult.recursionsAt_ofField_self _ _ o _
        | succ l =>
          have hne : (if e ∈ S then RecursiveResult.erased
              else RecursiveResult.ofField (f o) (s o) o).fieldPosition ≠ some (o + (l + 1)) := by
            split
            · exact nofun
            · intro h
              have := RecursiveResult.fieldPosition_ofField _ _ _ h
              omega
          simp only [hne, ↓reduceIte]
          rw [show o + (l + 1) = o + 1 + l by omega,
            Telescope.recursionsAt_results S hS f s ns (o + 1) es πs hf' l,
            Multiplicity.zero_add']
          rfl

/-- The uses at run time of a field of the grade `p`, stored at a multiplicity `π` within it, that
a recursor of the grade `r` gives are within those that the branch makes of it, when its usage
bounds them by the grade `g` of its variable and the grade `x` of its recursions, its result times
its factor: by the variable of the field, at the multiplicity that the erasure gives it, and by the
recursions on it. -/
theorem _root_.Sic.Grading.Grade.run_mul_le_fieldMultiplicity :
    ∀ (π : Multiplicity) (r p x g : Grade), r.run * π ≤ r.run * p.run → r * p ≤ g + x * r →
      r.run * π ≤ ((r * p).run - (x * r).run) + r.run * x.run := by
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
