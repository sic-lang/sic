module

public import Sic.Core.UsageWeakening
public import Sic.GradeMatrix

/-!
# Usage Substitution

The usage of a substituted term: when the matrix `Ψ` gives each variable the usage of the term that
the substitution `σ` puts for it, `Ψ ▶ₛ[γ] σ`, a term well used with the vector `γ` is substituted
into a term well used with `γ <* Ψ`.
Instantiating the variable of a binder follows, which the reduction of an application of an
abstraction does.

The substituted term of a variable is used in the mode of the grade of that variable, so the first
section moves a usage from a mode to another, and the well-formedness of a matrix from a vector to
another.

## Correspondence with the Formalization of ADE

ADE prove the same lemmas, `substₘ-lemma` and `sgSubstₘ-lemma₂`, with a well-formedness indexed by
a vector of modes, which is `⌞γ⌟ᶜ` for the vector `γ`; it is indexed by `γ` here, since no other
vector of modes is needed.
One lemma, `UsageSubst.mode_le`, moves the well-formedness to any vector whose modes are below,
where ADE has one lemma for each operation, such as `▶-≤`, `▶-⌞+ᶜ⌟ˡ` and `▶-⌞·ᶜ⌟`.
ADE prove the substitution by recursion on the derivation of the usage, which goes through a
derivation rescaled by `▸-·`, no subterm of it; it goes by induction on the term here, through the
inversions of `Sic.Core.Usage`.
-/

@[expose] public section

namespace Sic.Core

open Grade GradeVector Mode Term

/-! ## Changes of Mode -/

-- ADE: `▸-·`, in `Graded/Usage/Properties.agda`.
/-- A usage in the mode `m` is a usage in the mode `m' * m`, scaled by the grade of `m'`. -/
theorem Usage.smul (m' : Mode) {γ : GradeVector n} {t : Term k n} :
    γ ▶[m] t → ⌜m'⌝ • γ ▶[m' * m] t
  | .sub h hγ => .sub (h.smul m') (smul_mono (Grade.le_refl _) hγ)
  | .var => by rw [smul_update_zero, ← grade_mul]; exact .var
  | .univ => by rw [smul_zero]; exact .univ
  | .pi (p := p) hA hB => by
    have hA' := hA.smul m'
    have hB' := hB.smul m'
    rw [show m' * (m ⊙ p) = (m' * m) ⊙ p from (Mode.mul_assoc m' m ⌞p⌟).symm] at hA'
    rw [smul_cons, ← Grade.mul_assoc, ← grade_mul] at hB'
    rw [smul_add, ← mul_smul, grade_mul_comm m' p, mul_smul]
    exact .pi hA' hB'
  | .lam ht => by
    have ht' := ht.smul m'
    rw [smul_cons, ← Grade.mul_assoc, ← grade_mul] at ht'
    exact .lam ht'
  | .app (p := p) ht ha => by
    have ha' := ha.smul m'
    rw [show m' * (m ⊙ p) = (m' * m) ⊙ p from (Mode.mul_assoc m' m ⌞p⌟).symm] at ha'
    rw [smul_add, ← mul_smul, grade_mul_comm m' p, mul_smul]
    exact .app (ht.smul m') ha'

-- ADE: `▸-≤ᵐ`, in `Graded/Usage/Properties.agda`.
/--
A usage in the mode `m` is a usage in any mode `m'` below it, scaled by the grade of `m'`, where
`m'` is below `m` when `m' = m' * m`, the more erased mode being the lower.
-/
theorem Usage.mode_le (h : m' = m' * m) (ht : γ ▶[m] t) : ⌜m'⌝ • γ ▶[m'] t := by
  have := ht.smul m'
  rwa [← h] at this

-- ADE: `▸ᵐ`, in `Graded/Usage/Properties.agda`.
/-- A usage in the mode `m` is below its scaling by the grade of `m`. -/
theorem Usage.le_smul {γ : GradeVector n} {t : Term k n} : γ ▶[m] t → γ ≤ ⌜m⌝ • γ
  | .sub h hγ => fun x => le_grade_mul m _ _ (hγ x) (h.le_smul x)
  | .var => by rw [smul_update_zero, grade_mul_self]; exact le_refl _
  | .univ => by rw [smul_zero]; exact le_refl _
  | .pi (p := p) hA hB => by
    have hA' := smul_mono (Grade.le_refl p) hA.le_smul
    rw [← mul_smul, mul_grade_scale, mul_smul] at hA'
    rw [smul_add, ← mul_smul, grade_mul_comm m p, mul_smul]
    exact add_mono hA' fun x => hB.le_smul x.succ
  | .lam ht => fun x => ht.le_smul x.succ
  | .app (p := p) ht ha => by
    have ha' := smul_mono (Grade.le_refl p) ha.le_smul
    rw [← mul_smul, mul_grade_scale, mul_smul] at ha'
    rw [smul_add, ← mul_smul, grade_mul_comm m p, mul_smul]
    exact add_mono ht.le_smul ha'

/-! ## Well-Formed Matrices -/

-- ADE: `_▶[_]_`, in `Graded/Substitution.agda`.
/--
`Ψ ▶ₛ[γ] σ`: the row of each variable `x` in `Ψ` is a usage of the term `σ x`, in the mode of the
grade that `γ` gives `x`, and scaled by the grade of that mode.
-/
def UsageSubst (Ψ : GradeMatrix m n) (γ : GradeVector n) (σ : Subst k m n) : Prop :=
  ∀ x, ⌜⌞γ x⌟⌝ • Ψ x ▶[⌞γ x⌟] σ x

@[inherit_doc] notation:40 Ψ:41 " ▶ₛ[" γ "] " σ:41 => UsageSubst Ψ γ σ

-- ADE: none.
/-- A well-formed matrix is well formed for any vector whose modes are below those of `γ`. -/
theorem UsageSubst.mode_le (h : ∀ x, ⌞γ' x⌟ = ⌞γ' x⌟ * ⌞γ x⌟) (hσ : Ψ ▶ₛ[γ] σ) :
    Ψ ▶ₛ[γ'] σ := fun x => by
  have := (hσ x).mode_le (h x)
  rwa [← mul_smul, ← grade_mul, ← h x] at this

-- ADE: `wf-idSubstₘ`, in `Graded/Substitution/Properties.agda`.
/-- The identity matrix is well formed for the identity substitution. -/
theorem UsageSubst.id : (GradeMatrix.id : GradeMatrix n n) ▶ₛ[γ] (Term.var : Subst k n n) :=
  fun x => by
    show ⌜⌞γ x⌟⌝ • (𝟘ᶜ, x ≔ 𝟙) ▶[_] var x
    rw [smul_update_zero, Grade.mul_one]
    exact .var

-- ADE: `wf-consSubstₘ`, in `Graded/Substitution/Properties.agda`.
/-- A well-formed matrix extended by a usage of a term is well formed for the extended substitution. -/
theorem UsageSubst.cons (hσ : Ψ ▶ₛ[γ] σ) (ha : ⌜⌞p⌟⌝ • δ ▶[⌞p⌟] a) :
    Ψ.cons δ ▶ₛ[γ ∙ p] σ.cons a
  | ⟨0, _⟩ => ha
  | ⟨_ + 1, _⟩ => hσ _

-- ADE: `wf-liftSubstₘ`, in `Graded/Substitution/Properties.agda`.
/-- A well-formed matrix extended under a binder is well formed for the extended substitution. -/
theorem UsageSubst.lift {γ : GradeVector n} {Ψ : GradeMatrix m n} {σ : Subst k m n}
    (hσ : Ψ ▶ₛ[γ] σ) : Ψ.lift ▶ₛ[γ ∙ p] σ.lift
  | ⟨0, _⟩ => by
    show ⌜⌞p⌟⌝ • (𝟘ᶜ ∙ 𝟙) ▶[⌞p⌟] var 0
    rw [smul_cons, smul_zero, Grade.mul_one, ← update_zero_zero]
    exact .var
  | ⟨x + 1, h⟩ => by
    show ⌜⌞γ ⟨x, _⟩⌟⌝ • (Ψ ⟨x, _⟩ ∙ 𝟘) ▶[⌞γ ⟨x, _⟩⌟] (σ ⟨x, Nat.lt_of_succ_lt_succ h⟩).wk1
    rw [smul_cons, Grade.mul_zero]
    exact (hσ _).wk (.step .id)

/-! ## Substitution -/

/-- The mode of a subterm of grade `p` is unchanged when its grade is rescaled by the mode of `p`. -/
private theorem mode_mul_scale : ∀ (m : Mode) (p : Grade), ⌞p⌟ * (m ⊙ p) = m ⊙ p := by decide

/-- Rescaling a grade by the mode of `p` gives it the mode of its product by `p`. -/
private theorem mode_grade_mode_mul : ∀ p q : Grade, ⌞⌜⌞p⌟⌝ * q⌟ = ⌞p * q⌟ := by decide

-- ADE: `substₘ-lemma`, in `Graded/Substitution/Properties.agda`.
/--
A term well used with `γ`, substituted by `σ`, is well used with `γ <* Ψ`, when the matrix `Ψ` is
well formed for `σ`.
-/
theorem Usage.subst {γ : GradeVector n} {Ψ : GradeMatrix m n} {σ : Subst k m n} {t : Term k n}
    (ht : γ ▶[md] t) (hσ : Ψ ▶ₛ[γ] σ) : γ <* Ψ ▶[md] t.subst σ := by
  induction t generalizing m md with
  | var x =>
    have hγ := ht.inv_var
    have hx := hσ.mode_le (γ' := (𝟘ᶜ, x ≔ ⌜md⌝)) (fun y => Mode.mode_le _ _ (hγ y)) x
    rw [update_self, mode_grade] at hx
    exact .sub (by rw [update_zero_subst]; exact hx) (subst_mono Ψ hγ)
  | univ l => exact .sub (by rw [zero_subst]; exact .univ) (subst_mono Ψ ht.inv_univ)
  | pi p q A B ihA ihB =>
    obtain ⟨γA, δ, hA, hB, hγ⟩ := ht.inv_pi
    have hσ' := hσ.mode_le fun x => Mode.mode_le _ _ (hγ x)
    have hσA : Ψ ▶ₛ[⌜⌞p⌟⌝ • γA] σ := hσ'.mode_le fun x => by
      show ⌞⌜⌞p⌟⌝ * γA x⌟ = ⌞⌜⌞p⌟⌝ * γA x⌟ * ⌞(p * γA x) + δ x⌟
      rw [mode_grade_mode_mul]
      exact mode_add_left _ _
    have hA' := hA.smul ⌞p⌟
    rw [mode_mul_scale] at hA'
    have hB' := ihB hB (hσ'.mode_le fun x => mode_add_right _ _).lift
    rw [cons_subst_lift] at hB'
    have h := Usage.pi (ihA hA' hσA) hB'
    rw [← smul_subst, ← mul_smul, mul_grade_mode, ← add_subst] at h
    exact .sub h (subst_mono Ψ hγ)
  | lam p A t _ iht =>
    obtain ⟨δ, ht', hγ⟩ := ht.inv_lam
    have h := iht ht' (hσ.mode_le fun x => Mode.mode_le _ _ (hγ x)).lift
    rw [cons_subst_lift] at h
    exact .sub (.lam h) (subst_mono Ψ hγ)
  | app p t a iht iha =>
    obtain ⟨γt, δ, ht', ha, hγ⟩ := ht.inv_app
    have hσ' := hσ.mode_le fun x => Mode.mode_le _ _ (hγ x)
    have hσa : Ψ ▶ₛ[⌜⌞p⌟⌝ • δ] σ := hσ'.mode_le fun x => by
      show ⌞⌜⌞p⌟⌝ * δ x⌟ = ⌞⌜⌞p⌟⌝ * δ x⌟ * ⌞γt x + (p * δ x)⌟
      rw [mode_grade_mode_mul]
      exact mode_add_right _ _
    have ha' := ha.smul ⌞p⌟
    rw [mode_mul_scale] at ha'
    have h := Usage.app (iht ht' (hσ'.mode_le fun x => mode_add_left _ _)) (iha ha' hσa)
    rw [← smul_subst, ← mul_smul, mul_grade_mode, ← add_subst] at h
    exact .sub h (subst_mono Ψ hγ)

-- ADE: `sgSubstₘ-lemma₂`, in `Graded/Substitution/Properties.agda`.
/--
Instantiating the variable of a binder, used with the grade `p` by a body well used with `γ`, by a
term well used with `δ` gives a term well used with `γ + (p • δ)`, as `(∘_m)` counts the argument.
-/
theorem Usage.instantiate (ht : γ ∙ (⌜md⌝ * p) ▶[md] t) (ha : δ ▶[md ⊙ p] a) :
    γ + (p • δ) ▶[md] t.instantiate a := by
  have hσ : GradeMatrix.id.cons δ ▶ₛ[γ ∙ (⌜md⌝ * p)] Subst.cons Term.var a :=
    UsageSubst.id.cons (by rw [mode_grade_mul]; exact ha.mode_le (Mode.mul_self _).symm)
  have h := ht.subst hσ
  rw [cons_subst_cons, subst_id, GradeVector.add_comm] at h
  have hδ := smul_mono (Grade.le_refl p) ha.le_smul
  rw [← mul_smul, mul_grade_scale, ← grade_mul_comm] at hδ
  exact .sub h (add_mono (le_refl γ) hδ)

end Sic.Core
