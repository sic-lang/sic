module

public import Sic.Core.Erasure
public import Sic.Core.Lifting.Extension
public import Sic.Core.Results
import Sic.Core.Shape.Results.Fields

/-!
# Multiplicities of the Fields of the Branches

The multiplicity that the erasure of annex 19 of RFC 36 gives the variable of a field of a branch
of a recursor, `(erase_ū.π)`, is the uses at run time of the field that the recursor gives minus
those of the recursion on it, read from the recursive result that names the field: its grade times
its factor times the grade of the recursor, as the usage of annex 17 counts them, when the factor of
each recursive result of the erasure is the run-time multiplicity of the factor that the typing
gives it.
The typing and the erasure give each recursive result the same factor, in a signature whose names
are distinct and that declares its liftings in order: `11ᵖ` for a recursive field, and the factor of
the shape of the lifting of the type of a nested field, which has one.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Factors of the Recursive Results -/

/-- The recursive result of a field recurses on this field, or on none. -/
theorem RecursiveResult.fieldPosition_ofField (r : Option Name) (s : Option Shape) (l : Nat)
    {y : Nat} (h : (RecursiveResult.ofField r s l).fieldPosition = some y) : y = l := by
  cases r <;> cases s <;> simp_all [RecursiveResult.ofField, RecursiveResult.fieldPosition]

/-- The recursive results of the fields whose nestings `ns` have a position, from the position `o`,
recurse on fields at `o` or after it. -/
theorem RecursiveResult.le_of_mem_ofField {f : Nat → Option Name} {s : Nat → Option Shape}
    {ns : List (Nest Name)} {o : Nat} {w : RecursiveResult}
    (hw : w ∈ (ns.zipIdx o).filterMap fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2))
    {y : Nat} (h : w.fieldPosition = some y) : o ≤ y := by
  obtain ⟨⟨n, l⟩, hy, hf⟩ := List.mem_filterMap.1 hw
  have hl := (List.mem_zipIdx hy).1
  split at hf
  · cases hf
  · cases hf
    exact RecursiveResult.fieldPosition_ofField _ _ _ h ▸ hl

/-- No recursive result of the fields from the position `o + 1` recurses on the field at `o`. -/
theorem RecursiveResult.find?_ofField_eq_none {f : Nat → Option Name} {s : Nat → Option Shape}
    {ns : List (Nest Name)} {o : Nat} (es : List Grade) :
    ((((ns.zipIdx (o + 1)).filterMap fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2)).zip
        es).find? fun x => x.1.fieldPosition == some o) = none :=
  List.find?_eq_none.2 fun x hx hp => by
    have h := RecursiveResult.le_of_mem_ofField (List.of_mem_zip hx).1 (beq_iff_eq.1 hp)
    omega

/-- The recursive results of fields the first of which has no position are those of the others. -/
theorem RecursiveResult.filterMap_ofField_plain (f : Nat → Option Name) (s : Nat → Option Shape)
    (ns : List (Nest Name)) (o : Nat) :
    ((Nest.plain :: ns).zipIdx o).filterMap (fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2)) =
    (ns.zipIdx (o + 1)).filterMap fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2) :=
  rfl

/-- The recursive results of fields the first of which has a position are its result, then those of
the others. -/
theorem RecursiveResult.filterMap_ofField_cons (f : Nat → Option Name) (s : Nat → Option Shape)
    {n : Nest Name} (h : n.isPlain = false) (ns : List (Nest Name)) (o : Nat) :
    ((n :: ns).zipIdx o).filterMap (fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2)) =
    RecursiveResult.ofField (f o) (s o) o :: (ns.zipIdx (o + 1)).filterMap fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2) := by
  cases n with
  | plain => cases h
  | direct _ | inst _ => rfl

/-- Taking nothing leaves a multiplicity as it is. -/
theorem _root_.Sic.Grading.Multiplicity.sub_zero_mul :
    ∀ (m : Multiplicity) (r : Grade), m = m - (Grade.zero * r).run := by
  decide

/-- A grade times a factor without use at run time has no use at run time. -/
theorem _root_.Sic.Grading.Grade.run_mul_mul_of_run_eq_zero :
    ∀ e π r : Grade, π.run = .zero → ((e * π) * r).run = .zero := by
  decide

/-- The uses at run time of a grade times a factor of the multiplicity `1` times a grade are those
of the two grades. -/
theorem _root_.Sic.Grading.Grade.run_mul_mul_of_run_eq_one :
    ∀ e π r : Grade, π.run = .one → ((e * π) * r).run = (e * r).run := by
  decide

/-- The uses at run time of a grade times a factor times a grade, the factor taken at run time. -/
theorem _root_.Sic.Grading.Grade.run_mul_mul (e π r : Grade) :
    ((e * π) * r).run = e.run * (π.run * r.run) := by
  rw [(Grade.run_op _ _).2.1, (Grade.run_op _ _).2.1,
    (Multiplicity.modality.semiring.mul_assoc _ _ _)]

-- ADE: none.
/-- The multiplicity that the erasure gives the variable of the field at the position `o + l`, of
the grade `p`, among the recursive results of the fields whose nestings are `ns` from the position
`o`, read with the grades `es` of the results, is the uses at run time of the field that the
recursor gives minus the uses of the recursion on it, its grade times its factor times the grade
`r` of the recursor, when the factor of each recursive result is the run-time multiplicity of the
factor in `πs` at its index: a result that does not recurse, of the factor `0`, takes no use. -/
theorem _root_.Sic.Grading.Grade.fieldMultiplicity_ofField (r p : Grade) (f : Nat → Option Name)
    (s : Nat → Option Shape) :
    (ns : List (Nest Name)) → (o : Nat) → (es πs : List Grade) →
    (∀ (j : Nat) (w : RecursiveResult), ((ns.zipIdx o).filterMap fun y =>
      if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2))[j]? =
        some w → ∃ π : Grade, πs[j]? = some π ∧ w.factor = π.run) → (l : Nat) →
    r.fieldMultiplicity (some p)
      ((((ns.zipIdx o).filterMap fun y =>
        if y.1.isPlain then none else some (RecursiveResult.ofField (f y.2) (s y.2) y.2)).zip
          es).find? fun x => x.1.fieldPosition == some (o + l)) =
      (r * p).run - ((Telescope.resultGrades ns (List.zipWith (· * ·) es πs) l) * r).run
  | [], _, _, _, _, l => Multiplicity.sub_zero_mul _ _
  | .plain :: ns, o, es, πs, hf, l => by
    rw [RecursiveResult.filterMap_ofField_plain] at hf ⊢
    cases l with
    | zero =>
      rw [Nat.add_zero, RecursiveResult.find?_ofField_eq_none]
      exact Multiplicity.sub_zero_mul _ _
    | succ l =>
      rw [show o + (l + 1) = o + 1 + l by omega]
      exact fieldMultiplicity_ofField r p f s ns (o + 1) es πs hf l
  | .direct _ :: ns, o, es, πs, hf, l | .inst _ :: ns, o, es, πs, hf, l => by
    rw [RecursiveResult.filterMap_ofField_cons f s rfl] at hf ⊢
    obtain ⟨π, hπ, hw⟩ := hf 0 _ rfl
    cases πs with
    | nil => cases hπ
    | cons π' πs =>
      cases hπ
      have hf' : ∀ (j : Nat) (w : RecursiveResult), ((ns.zipIdx (o + 1)).filterMap fun y =>
          if y.1.isPlain then none
          else some (RecursiveResult.ofField (f y.2) (s y.2) y.2))[j]? = some w →
          ∃ π : Grade, πs[j]? = some π ∧ w.factor = π.run := fun j w h => hf (j + 1) w h
      cases es with
      | nil =>
        simp only [List.zip_nil_right, List.find?_nil, List.zipWith_nil_left,
          Telescope.resultGrades_nil]
        exact Multiplicity.sub_zero_mul _ _
      | cons e es =>
        simp only [List.zip_cons_cons, List.zipWith_cons_cons]
        cases l with
        | zero =>
          rw [Nat.add_zero]
          show _ = _ - ((e * π) * r).run
          generalize f o = rec at hw ⊢
          generalize s o = shp at hw ⊢
          cases rec with
          | some D =>
            rw [List.find?_cons_of_pos (p := fun x => x.1.fieldPosition == some o)
              (a := (RecursiveResult.ofField (some D) shp o, e)) (beq_iff_eq.2 rfl)]
            rw [Grade.run_mul_mul_of_run_eq_one e π r hw.symm]
            rfl
          | none =>
            cases shp with
            | some σ =>
              rw [List.find?_cons_of_pos (p := fun x => x.1.fieldPosition == some o)
                (a := (RecursiveResult.ofField none (some σ) o, e)) (beq_iff_eq.2 rfl)]
              simp only [RecursiveResult.ofField, RecursiveResult.factor] at hw
              rw [Grade.run_mul_mul, ← hw]
              rfl
            | none =>
              rw [List.find?_cons_of_neg (p := fun x => x.1.fieldPosition == some o)
                  (a := (RecursiveResult.ofField none none o, e))
                  (fun h => by cases beq_iff_eq.1 h),
                RecursiveResult.find?_ofField_eq_none,
                Grade.run_mul_mul_of_run_eq_zero e π r hw.symm]
              exact (by decide : ∀ m : Multiplicity, m = m - .zero) _
        | succ l =>
          rw [List.find?_cons_of_neg (fun h => by
            have := RecursiveResult.fieldPosition_ofField _ _ _ (beq_iff_eq.1 h)
            exact (by omega : False))]
          rw [show o + (l + 1) = o + 1 + l by omega]
          exact fieldMultiplicity_ofField r p f s ns (o + 1) es πs hf' l

-- ADE: none.
/-- The multiplicity that the erasure gives the variable of the field `l` of the constructor `con`,
of the grade `p`, with the grades `es` of the recursive results, is the uses at run time of the
field that the recursor of the grade `r` gives minus the uses of the recursion on it, its grade
times its factor in `πs` times `r`, as the usage counts them, when the factor of each recursive
result of the erasure is the run-time multiplicity of the factor in `πs` at its index. -/
theorem _root_.Sic.Grading.Grade.fieldMultiplicity_results (r p : Grade) {j g k' : Nat} {Δ : Scope}
    {sig : Signature} {v : Lifting.Variables} {names : List Name} {qs : List Quality}
    {ps : List Grade} {χ : Grade} (con : Constructor j g k' Δ) (I : Instance j g)
    (es πs : List Grade)
    (hf : ∀ (i : Nat) (w : RecursiveResult), (con.recursiveResults sig v names qs ps χ I)[i]? =
      some w → ∃ π : Grade, πs[i]? = some π ∧ w.factor = π.run) (l : Nat) :
    r.fieldMultiplicity (some p) (((con.recursiveResults sig v names qs ps χ I).zip es).find?
      fun x => x.1.fieldPosition == some l) =
      (r * p).run - ((Telescope.resultGrades ((con.fields I).nest names)
        (List.zipWith (· * ·) es πs) l) * r).run := by
  have h := Grade.fieldMultiplicity_ofField r p ((con.fields I).recursionAt names)
    (fun l => (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]?.join)
    ((con.fields I).nest names) 0 es πs hf l
  rw [Nat.zero_add] at h
  exact h

-- ADE: none.
/-- The typing and the erasure give each recursive result of the constructor `con` the same factor,
the erasure at run time, in a signature whose names are distinct and that declares its liftings in
order: `11ᵖ` for the recursor on a recursive field, and the factor of the shape of the lifting of
the type of a nested field, which has one, for its corecursor. -/
theorem Constructor.ResultTypes.factors_recursiveResults {k : Nat} {sig : Signature}
    {v : Lifting.Variables} (hsig : sig.Distinct) (hord : sig.LiftsInOrder) {j g k' : Nat}
    {Δ Γ : Scope} {con : Constructor j g k' Δ} {I : Instance j g} {names : List Name}
    {ls : Fin k' → Level k} {as : InstanceArgs k Γ Δ} {qs : List Quality} {ls' : List (Level k)}
    {ps : List Grade} {lC : Level k} {χ : Grade} {Cs : Motives k Γ} {ps' : List Parameter}
    {R : Telescope k (Γ.extend (con.params I).length) ps'} {πs : List Grade}
    (h : Constructor.ResultTypes sig v con I names ls as
      (Lifting.ofMotives names qs ls' ps as lC χ Cs) R πs) :
    ∀ (i : Nat) (w : RecursiveResult), (con.recursiveResults sig v names qs ps χ I)[i]? = some w →
      ∃ π : Grade, πs[i]? = some π ∧ w.factor = π.run := by
  intro i w hw
  rw [Constructor.getElem?_recursiveResults] at hw
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨n, A, hn, hp, hA⟩ := Constructor.exists_nest_of_nestPositions ls as hl
  have hrec : (con.fields I).recursionAt names l = n.blockName := by
    rw [Telescope.recursionAt, Telescope.recursion_eq_map_nest, List.getElem?_map, hn]
    rfl
  rw [hrec]
  cases n with
  | plain => cases hp
  | direct D =>
    obtain ⟨hd, -⟩ := h.factor_shape (md := .oneOne) (ax := Grade.run) hsig hord
      (Lifting.ofMotives_shapes _) (Signature.blockShapes_of_block_liftN (sig := sig) _) 0 i l _
      A (by rw [Nat.zero_add]; exact hl) hn hA
    exact ⟨_, hd D rfl, rfl⟩
  | inst ms =>
    obtain ⟨σ, hσ⟩ := h.nestedShapes_isSome (md := .oneOne) (ax := Grade.run) hsig hord hl hn
    obtain ⟨π, hπ, he⟩ := h.factor_nested hsig hord hl hσ
    refine ⟨π, hπ, ?_⟩
    simp only [Nest.blockName, hσ, Option.join_some, RecursiveResult.ofField,
      RecursiveResult.factor]
    exact he

end Sic.Core
