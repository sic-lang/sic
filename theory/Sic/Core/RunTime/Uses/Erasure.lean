module

public import Sic.Core.Erasure.Usage
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.RunTime.Corecursors
import Sic.Core.RunTime.Recursors
import Sic.Core.Syntax.Signature
import Sic.Core.Usage.Absence

/-!
# Usage of the Erasure

The preservation of the usage by the erasure of annex 16 of RFC 36: the erasure at run time of a
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

/-- The addition of the multiplicities is monotone. -/
theorem _root_.Sic.Grading.Multiplicity.add_le_add' :
    ∀ π₁ π₂ π₃ π₄ : Multiplicity, π₁ ≤ π₂ → π₃ ≤ π₄ → π₁ + π₃ ≤ π₂ + π₄ := by
  decide

/-- The multiplication of the multiplicities is monotone in its first factor. -/
theorem _root_.Sic.Grading.Multiplicity.mul_le_mul_right' :
    ∀ π₁ π₂ π : Multiplicity, π₁ ≤ π₂ → π₁ * π ≤ π₂ * π := by
  decide

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

/-- A grade is below `1` at run time when it has a use at run time, and `0` otherwise. -/
theorem _root_.Sic.Grading.Grade.run_le_indicator :
    ∀ e : Grade, e.run ≤ (if e ∈ Mode.oneOne.erased then .zero else .one) := by
  decide

/-- The sum of the grades of the recursive results of a branch has, at run time, a multiplicity
below that of the recursions that the branch runs, one for each result whose grade has a use at
run time. -/
theorem Telescope.run_resultSum_le : (rs : List (Option Name)) → (ps : List Parameter) →
    rs.length = ps.length → (es : List Grade) → es.length = (Telescope.resultParams rs ps).length →
    (ks : Fin (Telescope.resultParams rs ps).length → Option Nat) →
    (∀ (j : Fin (Telescope.resultParams rs ps).length) (e : Grade), es[(j : Nat)]? = some e →
      ((ks j).isSome ↔ e ∉ Mode.oneOne.erased)) →
    (Telescope.resultSum (Telescope.resultGrades rs es) rs).run ≤ recursions ks
  | [], [], _, _, _, _, _ => by
    show Multiplicity.zero ≤ Multiplicity.zero
    decide
  | none :: rs, _ :: ps, hl, es, he, ks, hk => by
    show (Telescope.resultSum (fun l => Telescope.resultGrades (none :: rs) es (l + 1)) rs).run ≤ _
    exact Telescope.run_resultSum_le rs ps (Nat.succ.inj hl) es he ks hk
  | some _ :: rs, _ :: ps, hl, [], he, _, _ => nomatch he
  | some _ :: rs, _ :: ps, hl, e :: es, he, ks, hk => by
    let j₀ : Fin (Telescope.resultParams rs ps).length.succ := ⟨0, Nat.zero_lt_succ _⟩
    have hr : recursions ks = (if (ks j₀).isSome then Multiplicity.one else .zero) +
        recursions fun j => ks j.succ := rfl
    rw [hr]
    show (e + Telescope.resultSum (fun l => Telescope.resultGrades rs es l) rs).run ≤ _
    have ih := Telescope.run_resultSum_le rs ps (Nat.succ.inj hl) es (Nat.succ.inj he)
      (fun j => ks j.succ) fun j e' h => hk j.succ e' (by simpa using h)
    have h₀ : e.run ≤ (if (ks j₀).isSome then Multiplicity.one else .zero) := by
      have := hk j₀ e rfl
      by_cases hs : (ks j₀).isSome
      · simpa [hs, this.1 hs] using Grade.run_le_indicator e
      · have he' : e ∈ Mode.oneOne.erased := Decidable.of_not_not fun h => hs (this.2 h)
        simpa [hs, he'] using Grade.run_le_indicator e
    exact Multiplicity.add_le_add' _ _ _ _ h₀ ih

/-! ## Branches -/

/-- The erasure of the branches of a recursor reads the variables of the scope as `χ` allows when
the erasure of each branch reads them as some `δ` allows, and its new variables as the
multiplicities that the erasure gives their binders allow, and `χ` bounds `δ` plus `χ` for each
recursive result that the branch computes. -/
theorem Branches.erase_usage {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade) (χ : MultiplicityVector Γ.length) :
    (us : Branches k Γ) → (es : List (List Nat)) → (fs : List (List Grade)) →
    (∀ i a b (gs : _root_.Vector Grade b) (u : Term k ((Γ.extend a).extend b)),
      us.get i = some ⟨a, b, u⟩ → us.grades i = gs.toList →
      ∃ δ : MultiplicityVector Γ.length,
        Target.Usage (δ.extendBinders
            (fun l => r.fieldMultiplicity ((fs.drop i).headD [])[(l : Nat)]?
              ((((es.drop i).headD []).idxOf? (l : Nat)).bind fun j => gs.toList[j]?))
            (fun (j : Fin b) => gs[j].run))
          (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b)) ∧
        χ ≤ᶜ δ +ᶜ (recursions (fun (j : Fin b) =>
          if gs[j] ∈ S then none else ((es.drop i).headD [])[(j : Nat)]?) ·ᶜ χ)) →
    TargetBranches.Usage χ (us.erase sig S hΓ r es fs)
  | .nil, _, _, _ => .nil
  | .cons a b gs u us, es, fs, h => by
    obtain ⟨δ, hu, hχ⟩ := h 0 a b gs u rfl rfl
    simp only [List.drop_zero] at hu hχ
    refine .cons hu hχ (Branches.erase_usage hΓ r χ us es.tail fs.tail
      fun i a' b' gs' u' hg hgs => ?_)
    have e₁ : es.drop (i + 1) = es.tail.drop i := by cases es <;> simp
    have e₂ : fs.drop (i + 1) = fs.tail.drop i := by cases fs <;> simp
    have := h (i + 1) a' b' gs' u' hg hgs
    rwa [e₁, e₂] at this

/-- The erasure of the branches of a corecursor reads the variables of the scope as `δ` allows when
each branch, without non-uniform parameters and with a grade, reads them as some `δᵢ` allows, and
its new variables as the multiplicities that the erasure gives their binders allow, `δ` being below
`δᵢ`, and below `δᵢ` plus `δ` when the branch resumes the corecursor. -/
theorem CorecBranches.erase_usage {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (δ : MultiplicityVector Γ.length) :
    (vs : CorecBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
    (pss : List (List Grade × List Grade)) →
    (∀ i, i < vs.length → ∃ (b c : Nat) (v : Term k ((Γ.extend b).extend c)) (p : Grade),
      vs.get i = some ⟨0, b, c, v⟩ ∧ ps[i]? = some p ∧
      ∃ δᵢ : MultiplicityVector Γ.length,
        Target.Usage (δᵢ.extendBinders
            (fun (l : Fin b) => ((((pss.drop i).headD ([], [])).1[(l : Nat)]?).map
              fun q => ((Mode.oneOne ⊙ p).grade * q).run).getD .omega)
            (fun (l : Fin c) => ((((pss.drop i).headD ([], [])).2[(l : Nat)]?).map
              fun q => ((Mode.oneOne ⊙ p).grade * q).run).getD .omega))
          (if p ∈ S then .erased else
            Scope.length_extend_extend Γ b c ▸ v.erase sig S ((hΓ.extend b).extend c)) ∧
        δ ≤ᶜ δᵢ ∧ ((ks.drop i).headD .none ≠ .none → δ ≤ᶜ δᵢ +ᶜ δ)) →
    TargetCorecBranches.Usage δ (vs.erase sig S hΓ ps ks pss)
  | .nil, _, _, _, _ => .nil
  | .cons n b c v vs, ps, ks, pss, h => by
    obtain ⟨b', c', v', p, hg, hp, δᵢ, hu, hδ, hr⟩ := h 0 (Nat.zero_lt_succ _)
    simp only [CorecBranches.get, Option.some.injEq] at hg
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
      refine .cons hu hδ hr (CorecBranches.erase_usage hΓ δ vs ps ks.tail pss.tail
        fun i hi => ?_)
      obtain ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, δ₁, hu₁, hδ₁, hr₁⟩ := h (i + 1) (Nat.succ_lt_succ hi)
      have e₁ : ks.drop (i + 1) = ks.tail.drop i := by cases ks <;> simp
      have e₂ : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
      rw [e₁] at hr₁
      rw [e₂] at hu₁
      exact ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, δ₁, hu₁, hδ₁, hr₁⟩

/-- A product of grades with a use at run time keeps the mode `11ᵐ`, factor by factor. -/
theorem Mode.oneOne_odot_mul :
    ∀ r p : Grade, r * p ∉ Mode.oneOne.erased → (Mode.oneOne ⊙ r) ⊙ p = .oneOne := by
  decide

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
declaration; the mode is a premise `m = 11ᵐ`, so that the positions of the term, which the usage
checks in the mode `m ⊙ p`, are checked by the same theorem.
RFC: `\mathsf{erase}_{▶}`
-/
theorem Usage.erase_usage {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {γ : GradeVector Γ.length} {m : Mode} {t : Term k Γ}
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
    simp only [Term.erase, hi, hd.fieldGrades h hc hq hp, Option.getD_some]
    exact .ctor (UsageArgs.erase_usage hd hΓ hm hts)
  | .recursor (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (us := us) (χ := χ)
      (δs := δs) (gs := gs) h hq hp _ ht hul hus hu hg hχ _ _ => by
    -- The branches, whose binders have the multiplicities of their variables at run time.
    have hbr : TargetBranches.Usage χ.run (us.erase sig Mode.oneOne.erased hΓ r
        ((sig.recursiveFields D qs ps).getD []) ((sig.caseFieldGrades D qs ps).getD [])) := by
      rw [hd.recursiveFields h hq hp, hd.caseFieldGrades h hq hp, Option.getD_some,
        Option.getD_some]
      refine Branches.erase_usage hΓ r χ.run us _ _ fun i a b gs' u hget hgs' => ?_
      have hi : i < decl.cases.length := hul ▸ Branches.lt_length_of_get hget
      obtain ⟨⟨j, T', con⟩, hc⟩ : ∃ c, decl.cases[i]? = some c :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨u', hu'⟩ := hus i j T' con hc
      cases Option.some.inj (hget.symm.trans hu')
      have hfs := List.headD_drop_of_getElem? (d := []) (l := decl.cases.map fun x =>
        (x.2.2.params (.ofLists qs ps hq hp)).map (·.usage)) (i := i)
        (x := (con.params (.ofLists qs ps hq hp)).map (·.usage)) (by simp [hc])
      have hes := List.headD_drop_of_getElem? (d := []) (l := decl.cases.map fun x =>
        ((x.2.2.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
          fun y => y.1.map fun _ => y.2) (i := i)
        (x := ((con.fields (.ofLists qs ps hq hp)).recursion decl.names).zipIdx.filterMap
          fun y => y.1.map fun _ => y.2) (by simp [hc])
      rw [hfs, hes]
      have hrg : us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) =
          Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)
            gs'.toList := by
        rw [Branches.resultGrades, hgs']
      have hlr := Telescope.length_recursion decl.names (con.fields (.ofLists qs ps hq hp))
      refine ⟨(δs i).run, ?_, ?_⟩
      · -- The erased branch reads the new variables below the grades that its usage gives them.
        have ih := Usage.erase_usage hd ((hΓ.extend _).extend _) hm
          (hu i j T' con u' hc hu')
        rw [hrg, GradeVector.extendResults_resultGrades] at ih
        refine .sub (Target.Usage.cast _ ih) (MultiplicityVector.extendBinders_le_run _ _ _ _ _
          (fun l => ?_) (fun l => ?_))
        · obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
            ⟨_, List.getElem?_eq_getElem l.2⟩
          have hgl := Grade.run_le (hg i j T' con l p' hc hp')
          rw [show (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
                us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) l
              else Grade.zero) = Telescope.resultGrades
                ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) gs'.toList l by
            rw [hrg]
            split
            · rfl
            · rename_i hn
              exact (Telescope.resultGrades_of_none _ _ _
                (by simpa [Telescope.recursionAt] using hn)).symm] at hgl
          rw [← Telescope.resultGrades_eq_idxOf _ _ 0 l, Nat.zero_add] at hgl
          rw [hm] at hgl
          simp only [Mode.grade, Grade.modality.semiring.one_mul] at hgl
          rw [(Grade.run_op _ _).1] at hgl
          simp only [List.getElem?_map, hp', Option.map_some, Grade.fieldMultiplicity]
          exact Multiplicity.sub_best.1 _ _ _ hgl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some,
            _root_.Vector.getElem_toList]
          exact (Multiplicity.modality.meet.meet_idem _).symm
      · -- The bound of the recursions.
        have hχi := GradeVector.run_commutes.run_le (hχ i j T' con hc)
        rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul, hrg] at hχi
        refine MultiplicityVector.le_trans hχi (MultiplicityVector.add_le_add'
          (MultiplicityVector.le_refl _) fun x => Multiplicity.mul_le_mul_right' _ _ _ ?_)
        refine Telescope.run_resultSum_le _ _ hlr _ (by simp) _ fun j' e he => ?_
        have hpos := Telescope.length_positions
          ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) hlr 0
        rw [List.getElem?_eq_getElem (by simp), _root_.Vector.getElem_toList] at he
        cases Option.some.inj he
        have hj : (j' : Nat) < (((con.fields (.ofLists qs ps hq hp)).recursion
            decl.names).zipIdx.filterMap fun y => y.1.map fun _ => y.2).length := by
          rw [hpos]
          exact j'.2
        by_cases hs : gs'[(j' : Nat)] ∈ Mode.oneOne.erased
        · simp [hs]
        · simp [hs, List.getElem?_eq_getElem hj]
    simp only [Term.erase]
    rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul]
    by_cases hr : r ∈ Mode.oneOne.erased
    · simp only [hr, ↓reduceIte]
      rw [(Mode.erased_values.1 r).1 hr,
        (MultiplicityVector.module Multiplicity.modality).zero_smul]
      exact .recursor (sig.skeleton_isSkeleton _ _ _).usage hbr
    · simp only [hr, ↓reduceIte]
      have hm' : m ⊙ r = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hr
      exact .sub (.recursor (Usage.erase_usage hd hΓ hm' ht) hbr)
        (MultiplicityVector.add_le_add' (MultiplicityVector.smul_le_of_not_erased hr _)
          (MultiplicityVector.le_refl _))
  | .obs (d := d) h hq hp hpos ht hbs _ => by
    obtain ⟨i, hi⟩ := Signature.destructorCase_of_mem h.1 h.2.1 hpos.mem
    rw [h.2.2] at hi
    simp only [Term.erase, hi, hd.argumentGrades h hq hp hpos, Option.getD_some]
    rw [GradeVector.run_commutes.run_add]
    exact .obs (Usage.erase_usage hd hΓ hm ht) (UsageArgs.erase_usage hd hΓ hm hbs)
  | .corec (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (Ss := Ss) (gs := vs)
      (δ := δ) (δs := δs) h hq hp hh hS _ hss hgl _ hSs hgs hgu hδ hδr => by
    obtain ⟨grs, hgrs, hgri⟩ := hd.destructorGrades h hq hp
    simp only [Term.erase, hd.position h hh, Option.bind_some, hS, Option.elim, hgrs,
      Option.getD_some, hd.resumedTypes h hq hp, hd.destructorArguments h hq hp]
    rw [GradeVector.run_commutes.run_add]
    refine .corec (UsageArgs.erase_usage_mul hd hΓ hm rfl hss)
      (CorecBranches.erase_usage hΓ δ.run vs _ _ _ fun i hi => ?_)
    -- The branch of the destructor of the case `i`.
    have hi' : i < decl.codataCases.length := hgl ▸ hi
    obtain ⟨⟨j, T', d⟩, hc⟩ : ∃ c, decl.codataCases[i]? = some c :=
      ⟨_, List.getElem?_eq_getElem hi'⟩
    have hcm := List.mem_of_getElem? hc
    obtain ⟨hT', hdm⟩ := TypeDeclaration.mem_casesFrom hcm
    have hj : decl.codataTypes[j]? = some T' := by
      have := (TypeDeclaration.getElem?_of_mem_casesFrom hcm).2
      rwa [Nat.sub_zero] at this
    obtain ⟨ps'', S', hSj⟩ := hSs j T' hj
    obtain ⟨p, q, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos (T'.body _) hdm
    have hnd := hd.destructors_nodup ⟨h.1, hT', rfl⟩
    have hpg := hgri i j T' d hc p (hpos.grade hnd)
    obtain ⟨g, hg⟩ := hgs i j T' d ps'' S' hc hSj p q ps₁ Ξ Θ B ψ hpos
    refine ⟨ps''.length, ps₁.length, g, p, hg, hpg, ?_⟩
    rw [List.headD_drop_of_getElem? (x := (ps''.map (r * ·.usage), ps₁.map (·.usage)))
        (by simp [hc, hSj, hpos.arguments hnd]),
      List.headD_drop_of_getElem? (x := Resumption.ofArity (decide (r ∈ Mode.oneOne.erased))
        (((B.blockName decl.names).bind decl.names.idxOf?).bind Ss.arity))
        (by simp [hc, hpos.resultName decl.names hnd])]
    have hδp := GradeVector.run_commutes.run_le (hδ i j T' d p q ps₁ Ξ Θ B ψ hc hpos)
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
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem (show ps₁.length - 1 - (x : Nat) < ps₁.length by omega),
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
      have ih := Usage.erase_usage hd ((hΓ.extend _).extend _) hm'
        (hgu i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hc hSj hpos hg)
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
        simp only [List.getElem?_map, List.getElem?_eq_getElem l.2, Option.map_some,
          Option.getD_some, Parameter.grades_of_getElem? (List.getElem?_eq_getElem l.2),
          Mode.grade]
        exact (Multiplicity.modality.meet.meet_idem _).symm
      · -- A branch that resumes the corecursor captures the scope again.
        cases hbn : B.blockName decl.names with
        | none => simp [hbn, Resumption.ofArity] at hk
        | some D' =>
          have h₂ := GradeVector.run_commutes.run_le
            (hδr i j T' d p q ps₁ Ξ Θ B ψ D' hc hpos hbn)
          rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul,
            GradeVector.run_commutes.run_smul] at h₂
          exact MultiplicityVector.le_trans h₂ (MultiplicityVector.add_le_add'
            (MultiplicityVector.smul_le_of_not_erased hpS _)
            (MultiplicityVector.smul_le_of_not_erased hpS _))
  | .sub h hle =>
    .sub (Usage.erase_usage hd hΓ hm h) (GradeVector.run_commutes.run_le hle)

-- ADE: none.
/-- The erasure at run time of the arguments of a telescope checked in the mode `11ᵐ`, each at the
grade of its entry, reads their variables as the run-time multiplicities of their grades allow. -/
theorem UsageArgs.erase_usage {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {m : Mode} (hm : m = .oneOne) {ps : List Parameter}
    {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m ts →
      Targets.Usage γ.run (ts.terms.erase sig Mode.oneOne.erased hΓ (ps.map (·.usage)))
  | .nil => by
    simp only [Args.terms, Terms.erase]
    rw [GradeVector.run_commutes.run_zero]
    exact .nil
  | .cons (p := p) ht hts => by
    simp only [Args.terms, List.map_cons, Terms.erase]
    rw [GradeVector.run_commutes.run_add, GradeVector.run_commutes.run_smul]
    by_cases hp : p.usage ∈ Mode.oneOne.erased
    · simp only [hp, ↓reduceIte]
      rw [(Mode.erased_values.1 p.usage).1 hp]
      rw [show Multiplicity.zero ·ᶜ GradeVector.run _ = 𝟘ᵛ from
        (MultiplicityVector.module Multiplicity.modality).zero_smul _]
      exact .cons .erased (UsageArgs.erase_usage hd hΓ hm hts)
    · simp only [hp, ↓reduceIte]
      have hm' : m ⊙ p.usage = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hp
      exact .cons (.sub (Usage.erase_usage hd hΓ hm' ht)
          (MultiplicityVector.smul_le_of_not_erased hp _))
        (UsageArgs.erase_usage hd hΓ hm hts)

-- ADE: none.
/-- The erasure at run time of the arguments of a telescope checked in the mode `11ᵐ ⊙ r`, each at
the grade of its entry times `r`, reads their variables as the run-time multiplicities of their
grades times `r` allow: the state of a corecursor. -/
theorem UsageArgs.erase_usage_mul {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {m m' : Mode} (hm : m = .oneOne) {r : Grade} (hm' : m ⊙ r = m')
    {ps : List Parameter} {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m' ts → Targets.Usage (GradeVector.run (r ·ᶜ γ))
      (ts.terms.erase sig Mode.oneOne.erased hΓ (ps.map (r * ·.usage)))
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
      exact .cons .erased (UsageArgs.erase_usage_mul hd hΓ hm hm' hts)
    · simp only [hrp, ↓reduceIte]
      have hmp : m' ⊙ p.usage = .oneOne := by
        rw [← hm', hm]
        exact Mode.oneOne_odot_mul _ _ hrp
      exact .cons (.sub (Usage.erase_usage hd hΓ hmp ht)
          (MultiplicityVector.smul_le_of_not_erased hrp _))
        (UsageArgs.erase_usage_mul hd hΓ hm hm' hts)

end

end Sic.Core
