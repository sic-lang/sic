module

public import Sic.Core.Erasure.Usage
public import Sic.Core.Lifting.Extension
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.Erasure.Fields
import Sic.Core.RunTime.Relation.Corecursors
import Sic.Core.Shape.Results.Fields
import Sic.Core.Syntax.Signature
import Sic.Core.Usage.Absence

/-!
# Usage of the Erasure

The preservation of the usage by the erasure of annex 19 of RFC 36: the erasure at run time of a
term checked in the mode `11ᵐ` reads its variables as the run-time multiplicities of their grades
allow, in the usage of the target language.
The erasure removes the positions whose grade has no use at run time, which the usage counts `0`
times at run time, keeps the others, which the mode `11ᵐ` checks in the mode `11ᵐ` again, and gives
each binder the multiplicity that the usage gives its variable at run time, or a lower one for the
variable of a field, which the recursion on the field also reads.
ADE have no such property: their erasure keeps no count of the uses.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-! ## Multiplicities -/

/-- A grade with a use at run time multiplies a multiplicity to a lower one: its run-time
multiplicity is `1` or `ω`. -/
theorem _root_.Sic.Grading.Grade.run_mul_le_of_not_erased :
    ∀ p : Grade, p ∉ Mode.oneOne.erased → ∀ π : Multiplicity, p.run * π ≤ π := by
  decide

/-- A vector multiplied by a grade with a use at run time is lower. -/
theorem _root_.Sic.Grading.MultiplicityVector.smul_le_of_not_erased {n : Nat} {p : Grade}
    (hp : p ∉ Mode.oneOne.erased) (ν : MultiplicityVector n) : p.run ·ᶜ ν ≤ᶜ ν :=
  fun x => Grade.run_mul_le_of_not_erased p hp (ν x)

/-- A product by a grade without use at run time has no use at run time. -/
theorem _root_.Sic.Grading.Grade.run_mul_of_erased :
    ∀ p q : Grade, p ∈ Mode.oneOne.erased → (p * q).run = .zero := by
  decide

/-- A vector multiplied by a grade without use at run time has no use at run time. -/
theorem _root_.Sic.Grading.GradeVector.run_smul_of_erased {n : Nat} {p : Grade}
    (hp : p ∈ Mode.oneOne.erased) (γ : GradeVector n) : GradeVector.run (p ·ᶜ γ) = 𝟘ᵛ :=
  funext fun x => Grade.run_mul_of_erased p (γ x) hp

/-! ## Uses of the Nested Fields -/

/-- A use at run time of a recursion that a branch runs on a field, at a grade `e` and a factor `π`,
is a use at run time of the field: the uses at run time of the field cover those of the recursion,
none of which is `0`. -/
theorem _root_.Sic.Grading.Multiplicity.used_of_recursion_used :
    ∀ a r q g e π : Multiplicity, a * r * q ≤ g + (e * π) * r → (a * r * e) * π ≠ .zero →
      a * r * q ≠ .zero := by
  decide

-- ADE: none.
/-- The arithmetic step of the premise `hused` of the rule of the recursor of the ownership, in
every mode: when the uses `⌜m⌝ · r · q` of a field of the grade `q` that the recursor of the grade
`r` gives are covered by the uses `g` of its variable plus those of the recursion through its
recursive result, of the grade `e` and the factor `π`, `(e · π) · r`, as the premise `hg` of the
rule of the recursor of the usage asks, a use at run time of the recursion,
`run(⌜m⌝ · r · e) · run(π)`, is a use at run time of the field; `Usage.recursor_used` composes it
with the factors of the shapes. -/
theorem _root_.Sic.Grading.Grade.used_of_usage (m : Mode) (r q g e π : Grade)
    (hg : m.grade * r * q ≤ g + (e * π) * r) :
    (m.grade * r * e).run * π.run ≠ .zero → (m.grade * r * q).run ≠ .zero := by
  have h := Grade.run_le hg
  simp only [(Grade.run_op _ _).1, (Grade.run_op _ _).2.1] at h ⊢
  exact Multiplicity.used_of_recursion_used _ _ _ _ _ _ h

-- ADE: none.
/-- The premises `hR` and `hg` of the rule of the recursor of the usage give the premise `hused` of
the rule of the recursor of the ownership, for the same mode `m`, grade `r`, branches `ūs` and
ownership `χ` of the results that are motives, in a signature whose names are distinct and that
declares its liftings in order: the factor of the shape of a nested field is the run-time
multiplicity of the factor `π` that the typing gives its result, so that the premise of the
ownership refuses no recursor that the usage accepts. -/
theorem Usage.recursor_used {sig : Signature} (hsig : sig.Distinct) (hord : sig.LiftsInOrder)
    {k : Nat} {Γ : Scope} {decl : TypeDeclaration} {qs : List Quality} {ls : List (Level k)}
    {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r ς χ : Grade} {κ : Universe k}
    {Cs : Motives k Γ} {us : Branches k Γ} {m : Mode} {gs : Nat → Nat → Grade}
    {πs : Nat → List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hR : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ R : Telescope k (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names),
        Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs) R (πs i))
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      m.grade * r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)) l) * r) :
    ∀ (i j : Nat) (T' : DataType decl.sorts decl.grades decl.levels decl.scope)
      (con : Constructor decl.sorts decl.grades decl.levels decl.scope),
      decl.cases[i]? = some (j, T', con) →
      ∀ (l : Nat) (σ : Shape) (p' : Parameter),
        (con.nestedShapes sig ⟨κ.quality, r, ς⟩ m Grade.run decl.names qs ps χ
          (.ofLists qs ps hq hp))[l]? = some (some σ) →
        (con.params (.ofLists qs ps hq hp))[l]? = some p' →
        (m.grade * r * Telescope.resultGrades
          ((con.fields (.ofLists qs ps hq hp)).nest decl.names) (us.grades i) l).run *
            σ.factor ≠ .zero →
        (m.grade * r * p'.usage).run ≠ .zero := by
  intro i j T' con hc l σ p' hσ hp' hu
  obtain ⟨R, hR'⟩ := hR i j T' con hc
  -- The field is nested, the `i'`-th of the fields whose nestings have a position.
  have hlen : l < ((con.fields (.ofLists qs ps hq hp)).nest decl.names).length := by
    rw [Telescope.length_nest]
    exact (List.getElem?_eq_some_iff.1 hp').1
  obtain ⟨n, hn⟩ : ∃ n, ((con.fields (.ofLists qs ps hq hp)).nest decl.names)[l]? = some n :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have hnp : n.isPlain = false := by
    cases n with
    | plain =>
      obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1
        ((Telescope.get_types_isSome (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) l).2
          (by rw [← Telescope.length_nest decl.names]; exact hlen))
      have h0 := Term.shape_eq_none_of_nest (v := ⟨κ.quality, r, ς⟩)
        (lookup := Signature.shapes ⟨κ.quality, r, ς⟩ m Grade.run sig)
        (block := sig.blockShapes decl.names qs ps χ) (ν := Nesting.plain) A
        (Term.nest_plain (fun _ _ => rfl) A)
      rw [Constructor.nestedShapes, Telescope.nestedShapes_types decl.names (ls.getFin hl)
        (con.fields (.ofLists qs ps hq hp)) as.toSubst l hA hn, Option.some.injEq, h0] at hσ
      cases hσ
    | direct _ | inst _ => rfl
  obtain ⟨i', hi'0⟩ := List.mem_iff_getElem?.1 (Telescope.mem_nestPositions.2 ⟨n, hn, hnp⟩ :
    0 + l ∈ Telescope.nestPositions ((con.fields (.ofLists qs ps hq hp)).nest decl.names) 0)
  obtain ⟨π, hπ, hf⟩ := hR'.factor_nested hsig hord ((Nat.zero_add l) ▸ hi'0) hσ
  cases he : (us.grades i)[i']? with
  | none =>
    rw [Telescope.resultGrades_of_nestPositions _ _ 0 i' l hi'0, List.getD_eq_getElem?_getD,
      he] at hu
    exact absurd (by
      show (m.grade * r * Grade.zero).run * σ.factor = .zero
      exact (by decide : ∀ (a b : Grade) (c : Multiplicity), (a * b * Grade.zero).run * c = .zero)
        _ _ _) hu
  | some e =>
    obtain ⟨hre, hrπ⟩ := Telescope.resultGrades_of_index ((Nat.zero_add l) ▸ hi'0) he hπ
    rw [hre, hf] at hu
    exact Grade.used_of_usage m r p'.usage (gs i l) e π (hrπ ▸ hg i j T' con l p' hc hp') hu

/-! ## Transports -/

/-- A term of the target language and a vector transported along the same equality of sizes keep
the usage. -/
theorem Target.Usage.cast {n n' : Nat} (h : n = n') {ν : MultiplicityVector n} {M : Target n}
    (hM : Target.Usage ν M) : Target.Usage (h ▸ ν) (h ▸ M) := by
  subst h
  exact hM

/-! ## Extensions -/

/-- The grades extended by a grade for each variable of a telescope give each new variable its
grade, the last one at `0`. -/
theorem _root_.Sic.Grading.GradeVector.extendGrades_lt {Γ : Scope} (γ : GradeVector Γ.length)
    (g : Nat → Grade) : (ps : List Parameter) → (i : Fin (Γ.extend ps.length).length) →
      (i : Nat) < ps.length → γ.extendGrades g ps i = g (ps.length - 1 - i)
  | [], _, h => nomatch h
  | p :: ps, i, h => by
    rw [GradeVector.extendGrades]
    by_cases h₁ : (i : Nat) < ps.length
    · rw [extendGrades_lt (Γ := .var :: Γ) _ _ ps i h₁]
      congr 1
      simp only [List.length_cons]
      omega
    · have e : i = ((⟨0, Nat.zero_lt_succ _⟩ : Fin (Scope.Entry.var :: Γ).length).addNat
          ps.length).cast (Scope.length_extend (.var :: Γ) ps.length).symm :=
        Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat, List.length_cons] at h ⊢; omega)
      have h₀ : (p :: ps).length - 1 - (i : Nat) = 0 := by
        simp only [List.length_cons] at h ⊢
        omega
      rw [h₀, e, GradeVector.extendGrades_addNat]
      rfl

/-- The grade `01ᵖ` of the types has no use at run time. -/
theorem Grade.noneLinear_erased : Grade.noneLinear ∈ Mode.oneOne.erased := by
  decide

/-- The variable of the mode `11ᵐ`, alone, has the multiplicity `1` at run time. -/
theorem GradeVector.run_update_zero {n : Nat} (x : Fin n) :
    GradeVector.run (GradeVector.update 𝟘ᶜ x Mode.oneOne.grade +ᶜ 𝟘ᶜ) =
      MultiplicityVector.update 𝟘ᵛ x .one :=
  funext fun y => by
    simp only [GradeVector.run, Sic.Math.Vector.add, Sic.Math.Vector.update,
      Sic.Math.Vector.zero]
    split <;> rfl

/-- The multiplicities of new variables below their grades at run time, and the old variables at
the multiplicities of their grades at run time, extend a vector of multiplicities below the
projection of the extended vector of grades, transported to the numbering of the binders of the
target language. -/
theorem _root_.Sic.Grading.MultiplicityVector.extendBinders_le_run {Γ : Scope}
    (δ : GradeVector Γ.length) (g e : Nat → Grade) (ps ps' : List Parameter)
    {πs : Fin ps.length → Multiplicity} {πs' : Fin ps'.length → Multiplicity}
    (hπ : ∀ l : Fin ps.length, πs l ≤ (g l).run) (hπ' : ∀ j : Fin ps'.length, πs' j ≤ (e j).run) :
    δ.run.extendBinders πs πs' ≤ᶜ
      (Scope.length_extend_extend Γ ps.length ps'.length ▸
        GradeVector.run ((δ.extendGrades g ps).extendGrades e ps')) := by
  intro x
  rw [MultiplicityVector.cast_apply]
  have hb := Scope.length_extend (Γ.extend ps.length) ps'.length
  have ha := Scope.length_extend Γ ps.length
  simp only [MultiplicityVector.extendBinders, GradeVector.run]
  by_cases h₁ : (x : Nat) < ps'.length
  · simp only [h₁, ↓reduceDIte]
    rw [GradeVector.extendGrades_lt _ _ ps' _ (by simpa using h₁), Fin.val_cast]
    exact hπ' ⟨ps'.length - 1 - x, by omega⟩
  · simp only [h₁, ↓reduceDIte]
    have ey : x.cast (Scope.length_extend_extend Γ ps.length ps'.length).symm =
        ((⟨x - ps'.length, by omega⟩ : Fin (Γ.extend ps.length).length).addNat
          ps'.length).cast hb.symm :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat]; omega)
    rw [ey, GradeVector.extendGrades_addNat]
    by_cases h₂ : (x : Nat) < ps.length + ps'.length
    · simp only [h₂, ↓reduceDIte]
      rw [GradeVector.extendGrades_lt _ _ ps _ (by simp only; omega)]
      exact hπ ⟨ps.length - 1 - (x - ps'.length), by omega⟩
    · simp only [h₂, ↓reduceDIte]
      have ez : (⟨x - ps'.length, by omega⟩ : Fin (Γ.extend ps.length).length) =
          ((⟨x - (ps.length + ps'.length), by omega⟩ : Fin Γ.length).addNat ps.length).cast
            ha.symm :=
        Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat]; omega)
      rw [ez, GradeVector.extendGrades_addNat]
      exact (Multiplicity.modality.meet.meet_idem _).symm

/-! ## Recursive Fields -/

/-- The sum of the grades of the recursive results of a branch has, at run time, a multiplicity
below the sum of multiplicities above those of their grades. -/
theorem Telescope.run_resultSum_le : (ns : List (Nest Name)) → (ps : List Parameter) →
    ns.length = ps.length → (es : List Grade) →
    es.length = (Telescope.nestResultParams ns ps).length →
    (πs : Fin (Telescope.nestResultParams ns ps).length → Multiplicity) →
    (∀ (j : Fin (Telescope.nestResultParams ns ps).length) (e : Grade), es[(j : Nat)]? = some e →
      e.run ≤ πs j) →
    (Telescope.resultSum (Telescope.resultGrades ns es) ns).run ≤ Multiplicity.sum πs
  | [], [], _, _, _, _, _ => by
    show Multiplicity.zero ≤ Multiplicity.zero
    decide
  | .plain :: ns, _ :: ps, hl, es, he, πs, hk => by
    show (Telescope.resultSum (fun l => Telescope.resultGrades (.plain :: ns) es (l + 1)) ns).run ≤
      _
    exact Telescope.run_resultSum_le ns ps (Nat.succ.inj hl) es he πs hk
  | .direct _ :: ns, _ :: ps, hl, [], he, _, _ | .inst _ :: ns, _ :: ps, hl, [], he, _, _ =>
    nomatch he
  | .direct _ :: ns, _ :: ps, hl, e :: es, he, πs, hk
  | .inst _ :: ns, _ :: ps, hl, e :: es, he, πs, hk => by
    let j₀ : Fin (Telescope.nestResultParams ns ps).length.succ := ⟨0, Nat.zero_lt_succ _⟩
    show (e + Telescope.resultSum (fun l => Telescope.resultGrades ns es l) ns).run ≤
      πs j₀ + Multiplicity.sum fun j => πs j.succ
    rw [(Grade.run_op _ _).1]
    exact Multiplicity.add_le_add' _ _ _ _ (hk j₀ e rfl)
      (Telescope.run_resultSum_le ns ps (Nat.succ.inj hl) es (Nat.succ.inj he)
        (fun j => πs j.succ) fun j e' h => hk j.succ e' (by simpa using h))

/-! ## Branches -/

/-- The erasure of the branches of a recursor reads the variables of the scope as `χ` allows when
the recursive results of each branch are those of `ws`, the erasure of each branch reads them as
some `δ` allows, and its new variables as the multiplicities that the erasure gives their binders
allow, `χ` bounds `δ` plus `χ` times the multiplicity of each recursive result times its factor, `0`
for a result that the branch does not compute, a result that the branch computes has a multiplicity
other than `0`, and the shape of each nested result fits the recursor. -/
theorem Branches.erase_usage {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade) (χ : MultiplicityVector Γ.length) :
    (us : Branches k Γ) → (ws : List (List RecursiveResult)) → (fs : List (List Parameter)) →
    (∀ i a b (gs : _root_.Vector Grade b) (u : Term k ((Γ.extend a).extend b)),
      us.get i = some ⟨a, b, u⟩ → us.grades i = gs.toList →
      ∃ δ : MultiplicityVector Γ.length,
        Target.Usage (δ.extendBinders
            (fun l => r.fieldMultiplicity (((fs.drop i).headD [])[(l : Nat)]?.map (·.usage))
              ((((ws.drop i).headD []).zip gs.toList).find?
                fun x => x.1.fieldPosition == some (l : Nat)))
            (fun (j : Fin b) => gs[j].run))
          (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b)) ∧
        χ ≤ᶜ δ +ᶜ (Multiplicity.sum (fun (j : Fin b) => gs[j].run *
          (if gs[j] ∈ S then RecursiveResult.erased
            else (((ws.drop i).headD [])[(j : Nat)]?).getD .erased).factor) ·ᶜ χ) ∧
        (∀ j : Fin b, gs[j] ∉ S → gs[j].run ≠ .zero) ∧
        ∀ (j : Fin b) (l : Nat) (σ : Shape),
          ((ws.drop i).headD [])[(j : Nat)]? = some (.nested l σ) → σ.Fits r.run) →
    TargetBranches.Usage r.run χ (us.erase sig S hΓ r ws fs)
  | .nil, _, _, _ => .nil
  | .cons a b gs u us, ws, fs, h => by
    obtain ⟨δ, hu, hχ, hk, hσ⟩ := h 0 a b gs u rfl rfl
    simp only [List.drop_zero] at hu hχ hσ
    have ih := Branches.erase_usage hΓ r χ us ws.tail fs.tail fun i a' b' gs' u' hg hgs => by
      have e₁ : ws.drop (i + 1) = ws.tail.drop i := by cases ws <;> simp
      have e₂ : fs.drop (i + 1) = fs.tail.drop i := by cases fs <;> simp
      have := h (i + 1) a' b' gs' u' hg hgs
      rwa [e₁, e₂] at this
    refine .cons (δ := δ) hu hχ (fun j hj => hk j fun hs => hj ?_) (fun j l σ hj => ?_) ih
    · show (if gs[j] ∈ S then RecursiveResult.erased else _) = _
      simp only [hs, ↓reduceIte]
    · change (if gs[j] ∈ S then RecursiveResult.erased else _) = _ at hj
      split at hj
      · cases hj
      · refine hσ j l σ ?_
        cases hw : (ws.headD [])[(j : Nat)]? with
        | none => rw [hw] at hj; cases hj
        | some w => rw [hw] at hj; cases hj; rfl

/-- The erasure of the branches of a corecursor reads the variables of the scope as `δ` allows when
each branch, without non-uniform parameters and with a grade, reads them as some `δᵢ` allows, and
its new variables as the multiplicities that the erasure gives their binders allow, `δ` being below
`δᵢ`, and below `δᵢ` plus `δ` when the branch resumes the corecursor. -/
theorem DestructorBranches.erase_usage {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (δ : MultiplicityVector Γ.length) :
    (vs : DestructorBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
    (pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)) →
    (∀ i, i < vs.length → ∃ (b c : Nat) (v : Term k ((Γ.extend b).extend c)) (p : Grade),
      vs.get i = some ⟨0, b, c, v⟩ ∧ ps[i]? = some p ∧
      ∃ δᵢ : MultiplicityVector Γ.length,
        Target.Usage (δᵢ.extendBinders
            (fun (l : Fin b) =>
              ((((pss.drop i).headD ([], ResultOwnership.noArguments)).1[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)
            (fun (l : Fin c) =>
              ((((pss.drop i).headD ([], ResultOwnership.noArguments)).2.1[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega))
          (if p ∈ S then .erased else
            Scope.length_extend_extend Γ b c ▸ v.erase sig S ((hΓ.extend b).extend c)) ∧
        δ ≤ᶜ δᵢ ∧ ((ks.drop i).headD .none ≠ .none → δ ≤ᶜ δᵢ +ᶜ δ)) →
    TargetCorecBranches.Usage δ (vs.erase sig S hΓ ps ks pss)
  | .nil, _, _, _, _ => .nil
  | .cons n b c v vs, ps, ks, pss, h => by
    obtain ⟨b', c', v', p, hg, hp, δᵢ, hu, hδ, hr⟩ := h 0 (Nat.zero_lt_succ _)
    simp only [DestructorBranches.get, Option.some.injEq] at hg
    have hn : n = 0 := by
      have := congrArg Sigma.fst hg
      simp only at this
      omega
    subst hn
    cases hg
    cases ps with
    | nil => nomatch hp
    | cons p' ps =>
      cases hp
      simp only [List.drop_zero] at hu hr
      refine .cons hu hδ hr (DestructorBranches.erase_usage hΓ δ vs ps ks.tail pss.tail
        fun i hi => ?_)
      obtain ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, δ₁, hu₁, hδ₁, hr₁⟩ := h (i + 1) (Nat.succ_lt_succ hi)
      have e₁ : ks.drop (i + 1) = ks.tail.drop i := by cases ks <;> simp
      have e₂ : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
      rw [e₁] at hr₁
      rw [e₂] at hu₁
      exact ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, δ₁, hu₁, hδ₁, hr₁⟩

/-- The grade of the mode of a destructor without use at run time has no use at run time. -/
theorem Mode.grade_odot_mul_of_erased :
    ∀ p q : Grade, p ∈ Mode.oneOne.erased → ((Mode.oneOne ⊙ p).grade * q).run = .zero := by
  decide

mutual

-- ADE: none.
/--
The erasure at run time of a term checked in the mode `11ᵐ` reads its variables as the run-time
multiplicities of their grades allow, in a signature whose names are distinct, so that the usage and
the erasure read the grades of the fields, of the arguments and of the branches in the same
declaration, and that declares its liftings in order, so that the factor that the usage gives the
recursive result of a nested field is that of the shape that the erasure gives it; the mode is a
premise `m = 11ᵐ`, so that the positions of the term, which the usage checks in the mode `m ⊙ p`,
are checked by the same theorem.
RFC: `\mathsf{erase}_{▶}`
-/
theorem Usage.erase_usage {sig : Signature} (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) {γ : GradeVector Γ.length} {m : Mode} {t : Term k Γ}
    (hm : m = .oneOne) :
    Usage sig γ m t → Target.Usage γ.run (t.erase sig Mode.oneOne.erased hΓ)
  | .var (e := .secondOrder ..) (x := y) _ => nomatch hΓ _ y.mem
  | .var (e := .var) (x := y) hts => by
    cases hts
    subst hm
    simp only [Term.erase]
    exact .sub (.var y.toFin) (MultiplicityVector.le_of_eq (GradeVector.run_update_zero _))
  | .const .. => by
    simp only [Term.erase]
    rw [GradeVector.run_commutes.run_zero]
    exact .const _ _ _
  | .sort => by
    simp only [Term.erase]
    rw [GradeVector.run_commutes.run_zero]
    exact .erased
  | .inst .. => by
    simp only [Term.erase]
    rw [GradeVector.run_smul_of_erased Grade.noneLinear_erased]
    exact .erased
  | .ctor (con := con) h hc hq hp hts => by
    obtain ⟨i, hi⟩ := Signature.constructorCase_of_mem h.1 h.2.1 hc
    rw [h.2.2] at hi
    simp only [Term.erase, hi, hd.fieldParams h hc hq hp, Option.getD_some]
    exact .ctor (UsageArgs.erase_usage hd hord hΓ hm hts)
  | .recursor (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (ς := ς) (χ' := χ') (κ := κ)
      (us := us) (χ := χ) (δs := δs) (gs := gs) (πs := πs) h hq _ hp _ ht hul hus hR hu hg hχ _ _ =>
      by
    -- The branches, whose binders have the multiplicities of their variables at run time.
    have hbr : TargetBranches.Usage r.run χ.run (us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
        ((sig.caseFieldParams D qs ps).getD [])) := by
      rw [hd.recursiveResults h hq hp, hd.caseFieldParams h hq hp, Option.getD_some]
      refine Branches.erase_usage hΓ r χ.run us _ _ fun i a b gs' u hget hgs' => ?_
      have hi : i < decl.cases.length := hul ▸ Branches.lt_length_of_get hget
      obtain ⟨⟨j, T', con⟩, hc⟩ : ∃ c, decl.cases[i]? = some c :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨u', hu'⟩ := hus i j T' con hc
      cases Option.some.inj (hget.symm.trans hu')
      have hfs := List.headD_drop (d := []) (l := decl.cases.map fun x =>
        x.2.2.params (.ofLists qs ps hq hp)) (i := i)
        (a := con.params (.ofLists qs ps hq hp)) (by simp [hc])
      have hws := List.headD_drop (d := [])
        (l := decl.recursiveResults sig ⟨κ.quality, r, ς⟩ qs ps χ' (.ofLists qs ps hq hp)) (i := i)
        (a := con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ'
          (.ofLists qs ps hq hp)) (by simp [TypeDeclaration.recursiveResults, hc])
      rw [hfs, hws]
      -- The typing and the erasure give each recursive result the same factor.
      obtain ⟨R, hR'⟩ := hR i j T' con hc
      have hf := hR'.factors_recursiveResults hd hord
      have hln := Telescope.length_nest decl.names (con.fields (.ofLists qs ps hq hp))
      have hπl : (πs i).length = (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length :=
        Terms.ResultTypes.length_factors hR'
      refine ⟨(δs i).run, ?_, ?_, fun j hj h0 => hj ((Mode.erased_values.1 _).2 h0),
        fun j l σ hj => ?_⟩
      · -- The erased branch reads the new variables below the grades that its usage gives them.
        have ih := Usage.erase_usage hd hord ((hΓ.extend _).extend _) hm
          (hu i j T' con u' hc hu')
        rw [hgs', GradeVector.extendResults_resultGrades] at ih
        refine .sub (Target.Usage.cast _ ih) (MultiplicityVector.extendBinders_le_run _ _ _ _ _
          (fun l => ?_) (fun l => ?_))
        · obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
            ⟨_, List.getElem?_eq_getElem l.2⟩
          have hgl := Grade.run_le (hg i j T' con l p' hc hp')
          rw [hgs', hm] at hgl
          simp only [Mode.grade, Grade.modality.semiring.one_mul] at hgl
          rw [(Grade.run_op _ _).1] at hgl
          simp only [hp', Option.map_some,
            Grade.fieldMultiplicity_results r p'.usage con _ gs'.toList (πs i) hf]
          exact Multiplicity.sub_best.1 _ _ _ hgl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some,
            _root_.Vector.getElem_toList]
          exact (Multiplicity.modality.meet.meet_idem _).symm
      · -- The bound of the recursions, each result at its factor.
        have hχi := GradeVector.run_commutes.run_le (hχ i j T' con hc)
        rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul, hgs'] at hχi
        refine MultiplicityVector.le_trans hχi (MultiplicityVector.add_le_add'
          (MultiplicityVector.le_refl _) fun x => Multiplicity.mul_le_mul_right' _ _ _ ?_)
        refine Telescope.run_resultSum_le _ _ hln _
          (by rw [List.length_zipWith, hπl]; simp) _ fun j' e he => ?_
        rw [List.getElem?_zipWith, List.getElem?_eq_getElem (by simp),
          _root_.Vector.getElem_toList] at he
        cases hπ : (πs i)[(j' : Nat)]? with
        | none => rw [hπ] at he; cases he
        | some π =>
          rw [hπ] at he
          cases Option.some.inj he
          rw [(Grade.run_op _ _).2.1]
          split
          · -- An erased result runs no recursion, and has no use at run time.
            rename_i hS
            have hz : gs'[j'].run = .zero := (Mode.erased_values.1 _).1 hS
            show gs'[j'].run * π.run ≤ gs'[j'].run * _
            rw [hz]
            exact (by decide : ∀ b c : Multiplicity, Multiplicity.zero * b ≤ .zero * c) _ _
          · -- A computed result runs the recursion at its factor.
            have hlt : (j' : Nat) < (con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ'
                (.ofLists qs ps hq hp)).length := by
              rw [Constructor.length_recursiveResults]
              exact j'.2
            obtain ⟨π', hπ', hw⟩ := hf j' _ (List.getElem?_eq_getElem hlt)
            rw [hπ] at hπ'
            cases Option.some.inj hπ'
            rw [List.getElem?_eq_getElem hlt, Option.getD_some, hw]
            exact Multiplicity.le_refl' _
      · -- The shape of a nested result fits the recursor.
        rw [Constructor.getElem?_recursiveResults] at hj
        obtain ⟨l', -, he⟩ := Option.map_eq_some_iff.1 hj
        obtain ⟨rfl, -, hs⟩ := RecursiveResult.ofField_eq_nested.1 he
        exact Constructor.nestedShapes_fits (Option.join_eq_some_iff.1 hs)
    simp only [Term.erase]
    rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul]
    by_cases hr : r ∈ Mode.oneOne.erased
    · simp only [hr, ↓reduceIte]
      refine .sub (.recursor (sig.skeleton _ _ _).target_isData.usage
        (fun _ => (sig.skeleton _ _ _).target_isData) hbr) (MultiplicityVector.le_of_eq ?_)
      rw [(Mode.erased_values.1 r).1 hr,
        (MultiplicityVector.module Multiplicity.modality).zero_smul,
        (MultiplicityVector.module Multiplicity.modality).zero_smul]
    · simp only [hr, ↓reduceIte]
      have hm' : m ⊙ r = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hr
      exact .recursor (Usage.erase_usage hd hord hΓ hm' ht)
        (fun h0 => absurd ((Mode.erased_values.1 r).2 h0) hr) hbr
  | .obs (d := d) h hq hp hpos ht hbs _ => by
    obtain ⟨i, hi⟩ := Signature.destructorCase_of_mem h.1 h.2.1 hpos.mem
    rw [h.2.2] at hi
    simp only [Term.erase, hi, hd.argumentParams h hq hp hpos, Option.getD_some]
    rw [GradeVector.run_commutes.run_add]
    exact .obs (Usage.erase_usage hd hord hΓ hm ht) (UsageArgs.erase_usage hd hord hΓ hm hbs)
  | .corec (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (Ss := Ss) (gs := vs)
      (δ := δ) (δs := δs) h hq hp hh hS _ hss hgl _ hSs hgs hgu hδ hδr => by
    simp only [Term.erase, hd.position h hh, Option.bind_some, hS, Option.elim]
    rw [GradeVector.run_commutes.run_add]
    refine .corec (UsageArgs.erase_usage_mul hd hord hΓ hm rfl hss)
      (DestructorBranches.erase_usage hΓ δ.run vs _ _ _ fun i hi => ?_)
    -- The branch of the destructor of the case `i`.
    obtain ⟨j, T', d, ps'', S', p, q, ς, ps₁, Ξ, Θ, B, ψ, g, hc, hSj, ⟨hpos⟩, hg, hpg, hargs,
      hres⟩ := hd.corecCase h hq hp hSs hgl hgs hi
    refine ⟨ps''.length, ps₁.length, g, p, hg, hpg, ?_⟩
    rw [hargs, hres]
    simp only [hSj]
    have hδp := GradeVector.run_commutes.run_le (hδ i j T' d p q ς ps₁ Ξ Θ B ψ hc hpos)
    rw [GradeVector.run_commutes.run_smul] at hδp
    by_cases hpS : p ∈ Mode.oneOne.erased
    · -- No observation runs the branch, whose variables have the multiplicity `0`.
      simp only [hpS, ↓reduceIte]
      rw [(Mode.erased_values.1 p).1 hpS,
        (MultiplicityVector.module Multiplicity.modality).zero_smul] at hδp
      refine ⟨𝟘ᵛ, .sub .erased (MultiplicityVector.le_of_eq (funext fun x => ?_)), hδp,
        fun _ => by rw [MultiplicityVector.zero_add]; exact MultiplicityVector.le_refl _⟩
      simp only [MultiplicityVector.extendBinders]
      split
      · rename_i hx
        simp only [List.getElem?_eq_getElem (show ps₁.length - 1 - (x : Nat) < ps₁.length by omega),
          Option.map_some, Option.getD_some, Mode.grade_odot_mul_of_erased _ _ hpS]
        rfl
      · split
        · rename_i hx hx'
          simp only [List.getElem?_map, List.getElem?_eq_getElem
              (show ps''.length - 1 - ((x : Nat) - ps₁.length) < ps''.length by omega),
            Option.map_some, Option.getD_some, Mode.grade_odot_mul_of_erased _ _ hpS]
          rfl
        · rfl
    · simp only [hpS, ↓reduceIte]
      have hm' : m ⊙ p = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hpS
      have ih := Usage.erase_usage hd hord ((hΓ.extend _).extend _) hm'
        (hgu i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hc hSj hpos hg)
      rw [GradeVector.extendParams_eq_extendGrades, GradeVector.extendParams_eq_extendGrades,
        hm'] at ih
      refine ⟨(δs i).run, .sub (Target.Usage.cast _ ih)
        (MultiplicityVector.extendBinders_le_run _ _ _ _ _ (fun l => ?_) (fun l => ?_)),
        MultiplicityVector.le_trans hδp (MultiplicityVector.smul_le_of_not_erased hpS _),
        fun hk => ?_⟩
      · rw [Mode.grade_odot_of_not_erased p hpS]
        simp only [List.getElem?_map, List.getElem?_eq_getElem l.2, Option.map_some,
          Option.getD_some, Parameter.grades_of_getElem? (List.getElem?_eq_getElem l.2),
          Mode.grade, Grade.modality.semiring.mul_assoc]
        exact (Multiplicity.modality.meet.meet_idem _).symm
      · rw [Mode.grade_odot_of_not_erased p hpS]
        simp only [List.getElem?_eq_getElem l.2, Option.map_some,
          Option.getD_some, Parameter.grades_of_getElem? (List.getElem?_eq_getElem l.2),
          Mode.grade]
        exact (Multiplicity.modality.meet.meet_idem _).symm
      · -- A branch that resumes the corecursor captures the scope again.
        cases hbn : B.blockName decl.names with
        | none => simp [hbn, Resumption.ofArity] at hk
        | some D' =>
          have h₂ := GradeVector.run_commutes.run_le
            (hδr i j T' d p q ς ps₁ Ξ Θ B ψ D' hc hpos hbn)
          rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul,
            GradeVector.run_commutes.run_smul] at h₂
          exact MultiplicityVector.le_trans h₂ (MultiplicityVector.add_le_add'
            (MultiplicityVector.smul_le_of_not_erased hpS _)
            (MultiplicityVector.smul_le_of_not_erased hpS _))
  | .sub h hle =>
    .sub (Usage.erase_usage hd hord hΓ hm h) (GradeVector.run_commutes.run_le hle)

-- ADE: none.
/-- The erasure at run time of the arguments of a telescope checked in the mode `11ᵐ`, each at the
parameter of its entry, reads their variables as the run-time multiplicities of their grades
allow. -/
theorem UsageArgs.erase_usage {sig : Signature} (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {m : Mode} (hm : m = .oneOne) {ps : List Parameter}
    {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m ts →
      Targets.Usage γ.run (ts.terms.erase sig Mode.oneOne.erased hΓ ps)
  | .nil => by
    simp only [Args.terms, Terms.erase]
    rw [GradeVector.run_commutes.run_zero]
    exact .nil
  | .cons (p := p) ht hts => by
    simp only [Args.terms, Terms.erase]
    rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul]
    by_cases hp : p.usage ∈ Mode.oneOne.erased
    · simp only [hp, ↓reduceIte]
      rw [(Mode.erased_values.1 p.usage).1 hp,
        (MultiplicityVector.module Multiplicity.modality).zero_smul]
      have h := Targets.Usage.cons (π := .zero) (ϱ := p.requirement.run) .erased
        (fun _ => .erased) (UsageArgs.erase_usage hd hord hΓ hm hts)
      rwa [(MultiplicityVector.module Multiplicity.modality).zero_smul] at h
    · simp only [hp, ↓reduceIte]
      have hm' : m ⊙ p.usage = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hp
      exact .cons (Usage.erase_usage hd hord hΓ hm' ht)
        (fun h0 => absurd ((Mode.erased_values.1 _).2 h0) hp)
        (UsageArgs.erase_usage hd hord hΓ hm hts)

-- ADE: none.
/-- The erasure at run time of the arguments of a telescope checked in the mode `11ᵐ ⊙ r`, each at
the parameter of its entry whose grade is multiplied by `r`, reads their variables as the run-time multiplicities of their
grades times `r` allow: the state of a corecursor. -/
theorem UsageArgs.erase_usage_mul {sig : Signature} (hd : sig.Distinct)
    (hord : sig.LiftsInOrder) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {m m' : Mode} (hm : m = .oneOne) {r : Grade} (hm' : m ⊙ r = m')
    {ps : List Parameter} {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m' ts → Targets.Usage (GradeVector.run (r ·ᶜ γ))
      (ts.terms.erase sig Mode.oneOne.erased hΓ (ps.map fun p => ⟨r * p.usage, p.requirement⟩))
  | .nil => by
    simp only [Args.terms, Terms.erase]
    rw [(GradeVector.module Grade.modality).smul_zero, GradeVector.run_commutes.run_zero]
    exact .nil
  | .cons (p := p) ht hts => by
    simp only [Args.terms, List.map_cons, Terms.erase]
    rw [(GradeVector.module Grade.modality).smul_add,
      ← (GradeVector.module Grade.modality).mul_smul, GradeVector.run_commutes.run_add,
      GradeVector.run_commutes.run_smul]
    by_cases hrp : r * p.usage ∈ Mode.oneOne.erased
    · simp only [hrp, ↓reduceIte]
      rw [(Mode.erased_values.1 _).1 hrp,
        (MultiplicityVector.module Multiplicity.modality).zero_smul]
      have h := Targets.Usage.cons (π := .zero) (ϱ := p.requirement.run) .erased
        (fun _ => .erased) (UsageArgs.erase_usage_mul hd hord hΓ hm hm' hts)
      rwa [(MultiplicityVector.module Multiplicity.modality).zero_smul] at h
    · simp only [hrp, ↓reduceIte]
      have hmp : m' ⊙ p.usage = .oneOne := by
        rw [← hm', hm]
        exact Mode.oneOne_odot_mul _ _ hrp
      exact .cons (Usage.erase_usage hd hord hΓ hmp ht)
        (fun h0 => absurd ((Mode.erased_values.1 _).2 h0) hrp)
        (UsageArgs.erase_usage_mul hd hord hΓ hm hm' hts)

end

end Sic.Core
