module

public import Sic.Core.Erasure
public import Sic.Core.Usage
public import Sic.Grading.GradeSet
import Sic.Core.Syntax.Signature

/-!
# Absence of the Erased Variables

The absence of annex 16 of RFC 36: a variable whose grade is in a set of grades `S` does not occur
in the erasure by `S` of a term checked in a mode whose uses `S` does not erase.
The property is one of the usage, stated on the erasure, which reads no judgment: the erasure
follows the grades of the signature and of the terms alone, so that the property is with the usage,
and the erasure and the evaluation of its target language import no judgment.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- A term of the target language transported along an equality of the sizes of its scope has the
occurrences of the term, at the transported indices. -/
theorem Target.occurs_cast {n n' : Nat} (h : n = n') (M : Target n) (y : Fin n') :
    (h ▸ M).Occurs y → M.Occurs (y.cast h.symm) := by
  subst h
  exact id

/-- A variable occurs in the erasure of branches when it occurs, as an old variable of the scope
of a branch, in the erasure of the term of this branch. -/
theorem Branches.occurs_erase {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)] {k : Nat}
    {Γ : Scope} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} : (us : Branches k Γ) →
      (es : List (List Nat)) → (us.erase sig S hΓ es).Occurs x → ∃ i a b u, us.get i = some ⟨a, b, u⟩ ∧
        (u.erase sig S ((hΓ.extend a).extend b)).Occurs
          ((x.addNat (a + b)).cast (Scope.length_extend_extend Γ a b).symm)
  | .nil, _, h => nomatch h
  | .cons a b _ u us, es, h => by
    cases h with
    | head h => exact ⟨0, a, b, u, rfl, Target.occurs_cast _ _ _ h⟩
    | tail h =>
      obtain ⟨i, a', b', u', hu, ho⟩ := Branches.occurs_erase hΓ us es.tail h
      exact ⟨i + 1, a', b', u', hu, ho⟩

/-- The branch at a position of branches is before their end. -/
theorem Branches.lt_length_of_get {k : Nat} {Γ : Scope} :
    {us : Branches k Γ} → {i : Nat} → {a : Σ n m, Term k ((Γ.extend n).extend m)} →
      us.get i = some a → i < us.length
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, _ => Nat.zero_lt_succ _
  | .cons _ _ _ _ us, _ + 1, _, h => Nat.succ_lt_succ (Branches.lt_length_of_get (us := us) h)

/-- The grades extended by the variables of a telescope give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_addNat {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendParams r ps ((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm) =
        γ x
  | [], _ => rfl
  | p :: ps, x => by
    have h := extendParams_addNat (Γ := .var :: Γ) (γ ∙ (r * p.usage)) r ps x.succ
    have he : ((x.addNat (p :: ps).length).cast (Scope.length_extend Γ (p :: ps).length).symm :
        Fin (Γ.extend (p :: ps).length).length) =
        (x.succ.addNat ps.length).cast (Scope.length_extend (.var :: Γ) ps.length).symm :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat, Fin.val_succ, List.length_cons]; omega)
    rw [he]
    exact h

/-- A variable occurs in the erasure of the branches of a corecursor when it occurs, as an old
variable of the scope of a branch whose grade is not erased, in the erasure of the term of this
branch. -/
theorem CorecBranches.occurs_erase {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    (vs : CorecBranches k Γ) → (ps : List Grade) → (ks : List (Option Nat)) →
      (vs.erase sig S hΓ ps ks).Occurs x →
        ∃ i b c v p, vs.get i = some ⟨0, b, c, v⟩ ∧ ps[i]? = some p ∧ p ∉ S ∧
          (v.erase sig S ((hΓ.extend b).extend c)).Occurs
            ((x.addNat (b + c)).cast (Scope.length_extend_extend Γ b c).symm)
  | .nil, _, _, h => nomatch h
  | .cons 0 b c v vs, p :: ps, ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h =>
      by_cases hp : p ∈ S
      · simp only [hp, ↓reduceIte] at h
        exact nomatch h
      · simp only [hp, ↓reduceIte] at h
        exact ⟨0, b, c, v, p, rfl, rfl, hp, Target.occurs_cast _ _ _ h⟩
    | tail h =>
      obtain ⟨i, b', c', v', p', hv, hp, hpS, ho⟩ := CorecBranches.occurs_erase hΓ vs ps ks.tail h
      exact ⟨i + 1, b', c', v', p', hv, hp, hpS, ho⟩
  | .cons 0 _ _ _ vs, [], ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h => exact nomatch h
    | tail h =>
      obtain ⟨_, _, _, _, _, _, hp, _⟩ := CorecBranches.occurs_erase hΓ vs [] ks.tail h
      simp at hp
  | .cons (_ + 1) _ _ _ vs, ps, ks, h => by
    simp only [CorecBranches.erase] at h
    cases h with
    | head h => exact nomatch h
    | tail h =>
      obtain ⟨i, b', c', v', p', hv, hp, hpS, ho⟩ := CorecBranches.occurs_erase hΓ vs _ ks.tail h
      rw [List.getElem?_tail] at hp
      exact ⟨i + 1, b', c', v', p', hv, hp, hpS, ho⟩

/-- The branch at a position of the branches of a corecursor is before their end. -/
theorem CorecBranches.lt_length_of_get {k : Nat} {Γ : Scope} :
    {vs : CorecBranches k Γ} → {i : Nat} →
      {a : Σ n m a, Term k (((Γ.extend n).extend m).extend a)} → vs.get i = some a →
        i < vs.length
  | .nil, _, _, h => nomatch h
  | .cons .., 0, _, _ => Nat.zero_lt_succ _
  | .cons _ _ _ _ vs, _ + 1, _, h =>
    Nat.succ_lt_succ (CorecBranches.lt_length_of_get (vs := vs) h)

/-- The grades extended by the variables of two telescopes, one after the other, give each old
variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendParams_extendParams_addNat {Γ : Scope} (γ : GradeVector Γ.length)
    (r₁ r₂ : Grade) (ps₁ ps₂ : List Parameter) (x : Fin Γ.length) :
    (γ.extendParams r₁ ps₁).extendParams r₂ ps₂
        ((x.addNat (0 + ps₁.length + ps₂.length)).cast
          (Scope.length_extend_extend_extend Γ 0 ps₁.length ps₂.length).symm) = γ x := by
  have he : ((x.addNat (0 + ps₁.length + ps₂.length)).cast
      (Scope.length_extend_extend_extend Γ 0 ps₁.length ps₂.length).symm :
        Fin ((Γ.extend ps₁.length).extend ps₂.length).length) =
      ((((x.addNat ps₁.length).cast (Scope.length_extend Γ ps₁.length).symm).addNat
        ps₂.length).cast (Scope.length_extend (Γ.extend ps₁.length) ps₂.length).symm) :=
    Fin.ext (show x.val + (0 + ps₁.length + ps₂.length) = (x.val + ps₁.length) + ps₂.length by
      omega)
  rw [he, GradeVector.extendParams_addNat, GradeVector.extendParams_addNat]

/-- The grades extended by a grade for each variable of a telescope give each old variable its
grade. -/
theorem _root_.Sic.Grading.GradeVector.extendGrades_addNat {Γ : Scope} (γ : GradeVector Γ.length) (g : Nat → Grade) :
    (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendGrades g ps ((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm) =
        γ x
  | [], _ => rfl
  | p :: ps, x => by
    have h := extendGrades_addNat (Γ := .var :: Γ) (γ ∙ g 0) (fun l => g (l + 1)) ps
      x.succ
    have he : ((x.addNat (p :: ps).length).cast (Scope.length_extend Γ (p :: ps).length).symm :
        Fin (Γ.extend (p :: ps).length).length) =
        (x.succ.addNat ps.length).cast (Scope.length_extend (.var :: Γ) ps.length).symm :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_addNat, Fin.val_succ, List.length_cons]; omega)
    rw [he]
    exact h

/-- The grades extended by a grade for each recursive result give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendResults_addNat {Γ : Scope} (γ : GradeVector Γ.length) (e : Nat → Grade) :
    (rs : List (Option Name)) → (ps : List Parameter) → (x : Fin Γ.length) →
      γ.extendResults e rs ps ((x.addNat (Telescope.resultParams rs ps).length).cast
        (Scope.length_extend Γ _).symm) = γ x
  | some D :: rs, p :: ps, x => by
    have h := extendResults_addNat (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) rs
      ps x.succ
    have he : ((x.addNat (Telescope.resultParams (some D :: rs) (p :: ps)).length).cast
        (Scope.length_extend Γ _).symm :
          Fin (Γ.extend (Telescope.resultParams (some D :: rs) (p :: ps)).length).length) =
        (x.succ.addNat (Telescope.resultParams rs ps).length).cast
          (Scope.length_extend (.var :: Γ) _).symm :=
      Fin.ext (show x.val + ((Telescope.resultParams rs ps).length + 1) =
        (x.val + 1) + (Telescope.resultParams rs ps).length by omega)
    rw [he]
    exact h
  | none :: rs, _ :: ps, x => extendResults_addNat γ (fun l => e (l + 1)) rs ps x
  | [], _, _ | some _ :: _, [], _ | none :: _, [], _ => rfl

/-- The grades extended by a grade for each field, then for each recursive result, as in the scope
of a branch of a recursor, give each old variable its grade. -/
theorem _root_.Sic.Grading.GradeVector.extendGrades_extendResults_addNat {Γ : Scope} (γ : GradeVector Γ.length)
    (g e : Nat → Grade) (rs : List (Option Name)) (ps : List Parameter) (x : Fin Γ.length) :
    (γ.extendGrades g ps).extendResults e rs ps
        ((x.addNat (ps.length + (Telescope.resultParams rs ps).length)).cast
          (Scope.length_extend_extend Γ _ _).symm) = γ x := by
  have he : ((x.addNat (ps.length + (Telescope.resultParams rs ps).length)).cast
      (Scope.length_extend_extend Γ _ _).symm :
        Fin ((Γ.extend ps.length).extend (Telescope.resultParams rs ps).length).length) =
      ((((x.addNat ps.length).cast (Scope.length_extend Γ ps.length).symm).addNat
        (Telescope.resultParams rs ps).length).cast (Scope.length_extend _ _).symm) :=
    Fin.ext (show x.val + (ps.length + (Telescope.resultParams rs ps).length) =
      (x.val + ps.length) + (Telescope.resultParams rs ps).length by omega)
  rw [he, GradeVector.extendResults_addNat, GradeVector.extendGrades_addNat]

mutual

-- ADE: `erased-hasX`, in `Graded/Erasure/Extraction/Properties/Usage.agda`, for `S^{𝟙ᵐ}`.
/--
A variable whose grade is in `S` does not occur in the erasure by `S` of a term checked in a mode
`m` whose uses `S` does not erase, in a signature whose names are distinct, so that the usage and
the erasure of a constructor read the grades of its fields in the same declaration.
RFC: `\mathsf{absent}_S`
-/
theorem Usage.absent {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {γ : GradeVector Γ.length} {m : Mode} {t : Term k Γ} {S : Set Grade} [DecidablePred (· ∈ S)]
    (hS : ErasesUncounted m S) (hΓ : Γ.FirstOrder) {x : Fin Γ.length} :
    Usage sig γ m t → γ x ∈ S → ¬ (t.erase sig S hΓ).Occurs x
  | .var (e := .secondOrder ..) (x := y) _, _, _ => nomatch hΓ _ y.mem
  | .var (e := .var) (x := y) (δ := δ) _, hx, ho => by
    simp only [Term.erase] at ho
    cases ho
    have h : m.grade + δ y.toFin ∈ S := by
      simpa [GradeVector.add, GradeVector.update] using hx
    exact hS.grade (hS.add _ _ h)
  | .const .., _, ho => nomatch ho
  | .sort, _, ho => nomatch ho
  | .ctor h hc hq hp hts, hx, ho => by
    simp only [Term.erase, hd.fieldGrades h hc hq hp, Option.getD_some] at ho
    split at ho
    · cases ho with
      | ctor ho => exact UsageArgs.absent hd hS hΓ hts hx ho
    · exact nomatch ho
  | .recursor (γ := γ₁) (χ := χ) (δs := δs) (r := r) _ _ _ _ ht hul hus hu _ hχ _, hx, ho => by
    have hx' : r * γ₁ x + χ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Term.erase] at ho
    cases ho with
    | recursor ho =>
      by_cases hr : r ∈ S
      · simp only [hr, ↓reduceIte] at ho
        exact (sig.skeleton_isSkeleton _ _ _).not_occurs ho
      · simp only [hr, ↓reduceIte] at ho
        have hS' : ErasesUncounted (m ⊙ r) S := (hS.mode _ hr).symm ▸ hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hr (hS.add _ _ hx')) ho
    | branch ho =>
      obtain ⟨i, a, b, u, hget, ho⟩ := Branches.occurs_erase hΓ _ _ ho
      have hi : i < _ := hul ▸ Branches.lt_length_of_get hget
      obtain ⟨⟨j, T', con⟩, hc⟩ : ∃ c, _ = some c := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨u', hu'⟩ := hus i j T' con hc
      cases Option.some.inj (hget.symm.trans hu')
      have hχx : χ x ∈ S := hS.add _ _ (Grade.modality.semiring.add_comm _ _ ▸ hx')
      have hδ : δs i x ∈ S := by
        have h' := hS.le _ _ (hχ i j T' con hc x) hχx
        simp only [GradeVector.add, GradeVector.smul] at h'
        exact hS.add _ _ h'
      exact Usage.absent hd hS ((hΓ.extend _).extend _) (hu i j T' con u' hc hu')
        (by rw [GradeVector.extendGrades_extendResults_addNat]; exact hδ) ho
  | .obs (γ := γ₁) (δ := δ) h hq hp hpos ht hbs _, hx, ho => by
    have hx' : γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add] using hx
    simp only [Term.erase, hd.argumentGrades h hq hp hpos, Option.getD_some] at ho
    split at ho
    · cases ho with
      | obs ho => exact Usage.absent hd hS hΓ ht (hS.add _ _ hx') ho
      | arg ho =>
        rw [Grade.modality.semiring.add_comm] at hx'
        exact UsageArgs.absent hd hS hΓ hbs (hS.add _ _ hx') ho
    · exact nomatch ho
  | .corec (decl := decl) (γ := γ₁) (δ := δ) (δs := δs) (r := r) (qs := qs) (ps := ps) h hq hp hh
      hS₀ _ hss hgl _
      hSs hgs hgu hδ _, hx, ho => by
    have hx' : r * γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    obtain ⟨gr, hgr, hgri⟩ := hd.destructorGrades h hq hp
    simp only [Term.erase, hd.position h hh, Option.bind_some, hS₀, Option.elim, hgr,
      Option.getD_some] at ho
    cases ho with
    | corec ho => exact UsageArgs.absent_mul hd hS hΓ rfl hss (hS.add _ _ hx') ho
    | cobranch ho =>
      obtain ⟨i, b, c, v, p', hget, hgi, hpS, ho⟩ := CorecBranches.occurs_erase hΓ _ _ _ ho
      have hi : i < _ := hgl ▸ CorecBranches.lt_length_of_get hget
      obtain ⟨⟨j, T', d⟩, hc⟩ : ∃ c, _ = some c := ⟨_, List.getElem?_eq_getElem hi⟩
      have hcm := List.mem_of_getElem? hc
      obtain ⟨hT', hdm⟩ := TypeDeclaration.mem_casesFrom hcm
      have hj : decl.codataTypes[j]? = some T' := by
        have := (TypeDeclaration.getElem?_of_mem_casesFrom hcm).2
        rwa [Nat.sub_zero] at this
      obtain ⟨ps'', S', hSj⟩ := hSs j T' hj
      obtain ⟨p, q, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos (T'.body _) hdm
      have hpg := hgri i j T' d hc p (hpos.grade (hd.destructors_nodup ⟨h.1, hT', rfl⟩))
      rw [Option.some.inj (hgi.symm.trans hpg)] at hpS
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S' hc hSj p q ps₁ Ξ Θ B ψ hpos
      cases Option.some.inj (hget.symm.trans hg)
      have hδx : δ x ∈ S := hS.add _ _ (Grade.modality.semiring.add_comm _ _ ▸ hx')
      have hpδ : p * δs i x ∈ S := hS.le _ _ (hδ i j T' d p q ps₁ Ξ Θ B ψ hc hpos x) hδx
      have hS' : ErasesUncounted (m ⊙ p) S := (hS.mode _ hpS).symm ▸ hS
      have hidx : ((x.addNat (ps''.length + ps₁.length)).cast
          (Scope.length_extend_extend Γ ps''.length ps₁.length).symm :
            Fin ((Γ.extend ps''.length).extend ps₁.length).length) =
          (x.addNat (0 + ps''.length + ps₁.length)).cast
            (Scope.length_extend_extend_extend Γ 0 ps''.length ps₁.length).symm :=
        Fin.ext (by simp)
      rw [hidx] at ho
      exact Usage.absent hd hS' _ (hgu i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hc hSj hpos hg)
        ((GradeVector.extendParams_extendParams_addNat (δs i) _ _ ps'' ps₁ x).symm ▸
          hS.mul _ _ hpS hpδ) ho
  | .sub h hle, hx, ho => Usage.absent hd hS hΓ h (hS.le _ _ (hle x) hx) ho

-- ADE: none.
/-- A variable whose grade is in `S` does not occur in the erasure by `S` of the arguments of a
telescope checked in a mode `m` whose uses `S` does not erase, each at the grade of its entry. -/
theorem UsageArgs.absent {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {m : Mode} {S : Set Grade} [DecidablePred (· ∈ S)] (hS : ErasesUncounted m S)
    (hΓ : Γ.FirstOrder) {x : Fin Γ.length} {ps : List Parameter} {γ : GradeVector Γ.length}
    {ts : Args k Γ ps} :
    UsageArgs sig γ m ts → γ x ∈ S → ¬ (ts.terms.erase sig S hΓ (ps.map (·.usage))).Occurs x
  | .nil, _, ho => nomatch ho
  | .cons (p := p) (γ := γ₁) (δ := δ) ht hts, hx, ho => by
    have hx' : p.usage * γ₁ x + δ x ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Args.terms, List.map_cons, Terms.erase] at ho
    cases ho with
    | head ho =>
      by_cases hp : p.usage ∈ S
      · simp only [hp, ↓reduceIte] at ho
        exact nomatch ho
      · simp only [hp, ↓reduceIte] at ho
        have hS' : ErasesUncounted (m ⊙ p.usage) S := (hS.mode _ hp).symm ▸ hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hp (hS.add _ _ hx')) ho
    | tail ho =>
      rw [Grade.modality.semiring.add_comm] at hx'
      exact UsageArgs.absent hd hS hΓ hts (hS.add _ _ hx') ho

-- ADE: none.
/-- A variable whose grade, times `r`, is in `S` does not occur in the erasure by `S` of the
arguments of a telescope checked in the mode `m ⊙ r`, where `S` does not erase the uses of the mode
`m`, each at the grade of its entry times `r`: the state of a corecursor. -/
theorem UsageArgs.absent_mul {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {m m' : Mode} {S : Set Grade} [DecidablePred (· ∈ S)] (hS : ErasesUncounted m S)
    (hΓ : Γ.FirstOrder) {x : Fin Γ.length} {r : Grade} (hm : m ⊙ r = m') {ps : List Parameter}
    {γ : GradeVector Γ.length} {ts : Args k Γ ps} :
    UsageArgs sig γ m' ts → r * γ x ∈ S →
      ¬ (ts.terms.erase sig S hΓ (ps.map (r * ·.usage))).Occurs x
  | .nil, _, ho => nomatch ho
  | .cons (p := p) (γ := γ₁) (δ := δ) ht hts, hx, ho => by
    have hx' : r * (p.usage * γ₁ x + δ x) ∈ S := by
      simpa [GradeVector.add, GradeVector.smul] using hx
    simp only [Args.terms, List.map_cons, Terms.erase] at ho
    cases ho with
    | head ho =>
      by_cases hp : r * p.usage ∈ S
      · simp only [hp, ↓reduceIte] at ho
        exact nomatch ho
      · simp only [hp, ↓reduceIte] at ho
        have hr : r ∉ S := fun hr => hp (hS.factor _ _ (.inl hr))
        have hpu : p.usage ∉ S := fun hpu => hp (hS.factor _ _ (.inr hpu))
        have hS' : ErasesUncounted (m' ⊙ p.usage) S := by
          rw [← hm, hS.mode _ hr, hS.mode _ hpu]
          exact hS
        exact Usage.absent hd hS' hΓ ht (hS.mul _ _ hpu (hS.add _ _ (hS.mul _ _ hr hx'))) ho
    | tail ho =>
      have hδ : r * δ x ∈ S := by
        by_cases hr : r ∈ S
        · exact hS.factor _ _ (.inl hr)
        · have h₁ := hS.mul _ _ hr hx'
          rw [Grade.modality.semiring.add_comm] at h₁
          exact hS.factor _ _ (.inr (hS.add _ _ h₁))
      exact UsageArgs.absent_mul hd hS hΓ hm hts hδ ho

end

end Sic.Core
