module

public import Sic.Core.Substitution
public import Sic.Core.Usage
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels
import Sic.Core.Substitution.Rules

/-!
# Renaming of the Usage

The judgments of usage of annex 12 of RFC 36 are stable under the renamings: a term that uses the
variables of its scope as `γ` allows, renamed by `α`, uses them as the vector `α γ` allows, which
gives each variable the sum of the grades of the variables that `α` renames to it.

The usage has no context, so that every renaming keeps it, even one that renames two variables to
the same one, whose uses add up.
The proof states the judgments substituted by a substitution that gives each variable the
abstraction of its image, as the renaming of the typing does, so that the laws of the substitutions
give the premises of each rule; it is by mutual structural recursion on the derivations, in the
clause `where` of the theorem.

ADE weaken the usage by the renamings that keep the order of the variables, whose vectors give the
grade `𝟘` to the new variables; here the renamings are all of them.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

end Sic.Core

namespace Sic.Grading.GradeVector

open Sic.Core

/-! ## Renamed Vectors -/

-- ADE: `wkConₘ`, in `Graded/Context/Weakening.agda`, for the renamings that keep the order.
/-- `α γ`: the vector `γ` renamed by `α`, which gives each variable of `Γ` the sum of the grades
that `γ` gives the variables that `α` renames to it, the grade `𝟘` to a variable that is the image
of none.
RFC: `\mathsf{ren}_\gamma` -/
def rename {Γ : Scope} : {Δ : Scope} → GradeVector Δ.length → Ren Γ Δ →
    GradeVector Γ.length
  | [], _, _ => 𝟘ᶜ
  | _ :: _, γ, α => GradeVector.update 𝟘ᶜ (α .zero).toFin (γ (Var.toFin .zero)) +ᶜ
      GradeVector.rename (fun x => γ x.succ) (fun x => α (.succ x))

-- ADE: `wk-𝟘ᶜ`, `wk-+ᶜ`, `wk-·ᶜ`, `wk-≤ᶜ`, `wk-,≔` and `wkConₘ` of `lift`, in
-- `Graded/Context/Weakening.agda`.
/-- The renaming of the vectors commutes with their operations and keeps their order, so that the
renaming of the usage follows its rules one by one. -/
structure RenameCommutes : Prop where
  /-- The zero vector, renamed, is the zero vector.
  RFC: `\mathsf{ren}_\gamma.{00}` -/
  rename_zero : ∀ {Γ Δ : Scope} (α : Ren Γ Δ), rename (𝟘ᶜ : GradeVector Δ.length) α = 𝟘ᶜ
  /-- The sum of two vectors, renamed, is the sum of the vectors renamed.
  RFC: `\mathsf{ren}_\gamma.{+}` -/
  rename_add : ∀ {Γ Δ : Scope} (γ δ : GradeVector Δ.length) (α : Ren Γ Δ),
    rename (γ +ᶜ δ) α = γ.rename α +ᶜ δ.rename α
  /-- A vector multiplied by a grade, renamed, is the vector renamed multiplied by the grade.
  RFC: `\mathsf{ren}_\gamma.{\cdot}` -/
  rename_smul : ∀ {Γ Δ : Scope} (p : Grade) (γ : GradeVector Δ.length) (α : Ren Γ Δ),
    rename (p ·ᶜ γ) α = p ·ᶜ γ.rename α
  /-- The renaming keeps the order.
  RFC: `\mathsf{ren}_\gamma.{\le}` -/
  rename_le : ∀ {Γ Δ : Scope} {γ δ : GradeVector Δ.length} (α : Ren Γ Δ), γ ≤ᶜ δ →
    γ.rename α ≤ᶜ δ.rename α
  /-- The zero vector updated at a variable, renamed, is the zero vector updated at its image.
  RFC: `\mathsf{ren}_\gamma.\mathsf{update}` -/
  rename_update : ∀ {Γ Δ : Scope} {e : Scope.Entry} (x : Var Δ e) (p : Grade) (α : Ren Γ Δ),
    rename (update 𝟘ᶜ x.toFin p) α = update 𝟘ᶜ (α x).toFin p
  /-- An extended vector, renamed under the new variable, is the vector renamed, extended.
  RFC: `\mathsf{ren}_\gamma.{\bullet}` -/
  rename_extend : ∀ {Γ Δ : Scope} {e : Scope.Entry} (γ : GradeVector Δ.length) (p : Grade)
    (α : Ren Γ Δ), rename (Δ := e :: Δ) (γ ∙ p) (Ren.lift α) = γ.rename α ∙ p

-- ADE: `wk-𝟘ᶜ`, `wk-+ᶜ`, `wk-·ᶜ`, `wk-≤ᶜ`, `wk-,≔` and `wkConₘ` of `lift`, in
-- `Graded/Context/Weakening.agda`.
/-- The renaming of the vectors commutes with their operations and keeps their order.
RFC: `\mathsf{ren}_\gamma.{00}`
RFC: `\mathsf{ren}_\gamma.{+}`
RFC: `\mathsf{ren}_\gamma.{\cdot}`
RFC: `\mathsf{ren}_\gamma.{\le}`
RFC: `\mathsf{ren}_\gamma.\mathsf{update}`
RFC: `\mathsf{ren}_\gamma.{\bullet}` -/
theorem rename_commutes : RenameCommutes :=
  ⟨rename_zero, rename_add, rename_smul, rename_le, rename_update, rename_extend⟩
where
  rename_zero {Γ : Scope} : {Δ : Scope} → (α : Ren Γ Δ) → rename (𝟘ᶜ : GradeVector Δ.length) α = 𝟘ᶜ
    | [], _ => rfl
    | _ :: _, α => by
      show update 𝟘ᶜ _ _ +ᶜ rename 𝟘ᶜ _ = _
      rw [rename_zero]
      funext y
      simp only [add, update, zero]
      split <;> rfl
  rename_add {Γ : Scope} : {Δ : Scope} → (γ δ : GradeVector Δ.length) → (α : Ren Γ Δ) →
      rename (γ +ᶜ δ) α = γ.rename α +ᶜ δ.rename α
    | [], _, _, _ => funext fun _ => rfl
    | _ :: _, γ, δ, α => by
      show update 𝟘ᶜ _ _ +ᶜ rename ((fun x => γ x.succ) +ᶜ (fun x => δ x.succ)) _ = _
      rw [rename_add]
      funext y
      simp only [rename, add, update, zero]
      generalize γ (Var.toFin .zero) = a
      generalize δ (Var.toFin .zero) = b
      generalize rename (fun x => γ x.succ) (fun x => α (.succ x)) y = c
      generalize rename (fun x => δ x.succ) (fun x => α (.succ x)) y = d
      split <;> revert a b c d <;> decide
  rename_smul {Γ : Scope} : {Δ : Scope} → (p : Grade) → (γ : GradeVector Δ.length) → (α : Ren Γ Δ) →
      rename (p ·ᶜ γ) α = p ·ᶜ γ.rename α
    | [], p, _, _ => funext fun _ => (Grade.modality.semiring.mul_zero p).symm
    | _ :: _, p, γ, α => by
      show update 𝟘ᶜ _ _ +ᶜ rename (p ·ᶜ (fun x => γ x.succ)) _ = _
      rw [rename_smul]
      funext y
      simp only [rename, add, smul, update, zero]
      generalize γ (Var.toFin .zero) = a
      generalize rename (fun x => γ x.succ) (fun x => α (.succ x)) y = c
      split <;> revert p a c <;> decide
  rename_le {Γ : Scope} : {Δ : Scope} → {γ δ : GradeVector Δ.length} → (α : Ren Γ Δ) → γ ≤ᶜ δ →
      γ.rename α ≤ᶜ δ.rename α
    | [], _, _, _, _ => fun _ => Grade.le_refl _
    | _ :: _, _, _, α, h => by
      refine add_le_add Grade.modality (fun y => ?_) (rename_le (fun x => α (.succ x)) fun x => h x.succ)
      simp only [update]
      split
      · exact h _
      · exact Grade.le_refl _
  rename_update {Γ : Scope} : {Δ : Scope} → {e : Scope.Entry} → (x : Var Δ e) → (p : Grade) →
      (α : Ren Γ Δ) → rename (update 𝟘ᶜ x.toFin p) α = update 𝟘ᶜ (α x).toFin p
    | _ :: Δ, _, .zero, p, α => by
      show update 𝟘ᶜ _ _ +ᶜ rename (Δ := Δ) (fun y => update 𝟘ᶜ (Var.toFin .zero) p y.succ) _ = _
      rw [show (fun y : Fin Δ.length => update 𝟘ᶜ (Var.toFin (.zero (Γ := Δ))) p y.succ) = 𝟘ᶜ from
        funext fun y => by
          show (if _ then p else Grade.zero) = Grade.zero
          split
          · exact absurd (congrArg Fin.val ‹_›) (Nat.succ_ne_zero _)
          · rfl, rename_zero]
      funext y
      simp only [add, update, zero]
      split <;> revert p <;> decide
    | e₀ :: Δ, _, .succ x, p, α => by
      show update 𝟘ᶜ _ _ +ᶜ
        rename (Δ := Δ) (fun y => update 𝟘ᶜ (Var.toFin (.succ x)) p y.succ) _ = _
      rw [show (fun y : Fin Δ.length => update 𝟘ᶜ (Var.toFin (.succ x)) p y.succ) =
          update 𝟘ᶜ x.toFin p from funext fun y => by exact ite_succ y x.toFin p,
        rename_update x p (fun y => α (.succ y))]
      have hz : update 𝟘ᶜ (Var.toFin (.succ (e' := e₀) x)) p (Var.toFin (.zero (Γ := Δ))) =
          Grade.zero := by
        show (if _ then p else Grade.zero) = Grade.zero
        split
        · exact absurd (congrArg Fin.val ‹_›).symm (Nat.succ_ne_zero _)
        · rfl
      rw [hz, update_zero]
      exact (module Grade.modality).zero_add _
  rename_succ {Γ : Scope} : {Δ : Scope} → {e : Scope.Entry} → (γ : GradeVector Δ.length) →
      (α : Ren Γ Δ) → γ.rename (fun x => (α x).succ (e' := e)) = γ.rename α ∙ Grade.zero
    | [], _, _, _ => funext fun y => by cases y using Fin.cases <;> rfl
    | _ :: _, e, γ, α => by
      show update 𝟘ᶜ _ _ +ᶜ rename _ (fun x => (α (.succ x)).succ (e' := e)) = _
      rw [rename_succ (fun x => γ x.succ) (fun x => α (.succ x))]
      funext y
      cases y using Fin.cases with
      | zero =>
        simp only [add, update, zero, extend, Var.toFin, Fin.cases_zero]
        exact (congrArg (· + Grade.zero) (ite_zero_succ _ _)).trans
          (Grade.modality.semiring.zero_add _)
      | succ y =>
        simp only [add, update, zero, extend, Var.toFin, Fin.cases_succ]
        exact congrArg (· + _) (ite_succ _ _ _)
  rename_extend {Γ : Scope} {Δ : Scope} {e : Scope.Entry} (γ : GradeVector Δ.length) (p : Grade)
      (α : Ren Γ Δ) : rename (Δ := e :: Δ) (γ ∙ p) (Ren.lift α) = γ.rename α ∙ p := by
    show update 𝟘ᶜ _ p +ᶜ rename γ (fun x => (α x).succ (e' := e)) = _
    rw [rename_succ]
    funext y
    cases y using Fin.cases with
    | zero =>
      simp only [add, update, zero, extend, Ren.lift, Var.toFin, Fin.cases_zero]
      split
      · exact (Grade.modality.semiring.add_comm _ _).trans (Grade.modality.semiring.zero_add _)
      · exact absurd rfl ‹_›
    | succ y =>
      simp only [add, update, zero, extend, Ren.lift, Var.toFin, Fin.cases_succ]
      exact (congrArg (· + _) (ite_succ_zero _ _)).trans (Grade.modality.semiring.zero_add _)
  ite_succ {n : Nat} (y t : Fin n) (a : Grade) :
      (if y.succ = t.succ then a else Grade.zero) = (if y = t then a else Grade.zero) := by
    split <;> split <;> rename_i h₁ h₂
    · rfl
    · exact absurd (Fin.succ_inj.mp h₁) h₂
    · exact absurd (congrArg Fin.succ h₂) h₁
    · rfl
  ite_zero_succ {n : Nat} (t : Fin n) (a : Grade) :
      (if (0 : Fin (n + 1)) = t.succ then a else Grade.zero) = Grade.zero := by
    split
    · exact absurd ‹_› (Fin.succ_ne_zero t).symm
    · rfl
  ite_succ_zero {n : Nat} (y : Fin n) (a : Grade) :
      (if y.succ = ⟨0, Nat.zero_lt_succ n⟩ then a else Grade.zero) = Grade.zero := by
    split
    · exact absurd (congrArg Fin.val ‹_›) (Nat.succ_ne_zero _)
    · rfl
  update_zero {n : Nat} (i : Fin n) : update 𝟘ᶜ i Grade.zero = 𝟘ᶜ :=
    funext fun _ => by show (if _ then _ else _) = _; split <;> rfl

/-- A vector extended by the grades of the variables of a telescope, renamed under them, is the
vector renamed, extended. -/
theorem rename_extendParams {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) → (r : Grade) →
    (ps : List Parameter) → (α : Ren Γ Δ) →
      (γ.extendParams r ps).rename (Ren.liftN ps.length α) = (γ.rename α).extendParams r ps
  | _, _, _, [], _ => rfl
  | _, γ, r, p :: ps, α =>
    (rename_extendParams (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ (r * p.usage)) r ps
      (Ren.lift α)).trans
      (congrArg (fun δ => extendParams δ r ps) (rename_commutes.rename_extend γ _ α))

/-- A vector extended by the grades `g`, renamed under the new variables, is the vector renamed,
extended. -/
theorem rename_extendGrades {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) →
    (g : Nat → Grade) → (ps : List Parameter) → (α : Ren Γ Δ) →
      (γ.extendGrades g ps).rename (Ren.liftN ps.length α) = (γ.rename α).extendGrades g ps
  | _, _, _, [], _ => rfl
  | _, γ, g, _ :: ps, α =>
    (rename_extendGrades (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ g 0) (fun l => g (l + 1)) ps
      (Ren.lift α)).trans
      (congrArg (fun δ => extendGrades δ (fun l => g (l + 1)) ps)
        (rename_commutes.rename_extend γ _ α))

/-- A vector extended by the grades of the recursive results, renamed under them, is the vector
renamed, extended. -/
theorem rename_extendResults {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) →
    (e : Nat → Grade) → (rs : List (Option Name)) → (ps : List Parameter) → (α : Ren Γ Δ) →
      (γ.extendResults e rs ps).rename (Ren.liftN (Telescope.resultParams rs ps).length α) =
        (γ.rename α).extendResults e rs ps
  | _, γ, e, some _ :: rs, _ :: ps, α =>
    (rename_extendResults (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ e 0) (fun l => e (l + 1)) rs ps
      (Ren.lift α)).trans
      (congrArg (fun δ => extendResults δ (fun l => e (l + 1)) rs ps)
        (rename_commutes.rename_extend γ _ α))
  | _, γ, e, none :: rs, _ :: ps, α => rename_extendResults γ (fun l => e (l + 1)) rs ps α
  | _, _, _, [], _, _ | _, _, _, some _ :: _, [], _ | _, _, _, none :: _, [], _ => rfl

-- ADE: `wkConₘ` of `step`, in `Graded/Context/Weakening.agda`.
/-- A vector renamed by the weakening is the vector extended by the grade `𝟘` of the new variable,
which is the image of none. -/
theorem rename_weaken {Γ : Scope} {e : Scope.Entry} (γ : GradeVector Γ.length) :
    γ.rename (Ren.weaken (e := e)) = γ ∙ Grade.zero :=
  (rename_commutes.rename_succ γ (fun x => x)).trans (congrArg (· ∙ Grade.zero) (rename_id γ))
where
  rename_id : {Γ : Scope} → (γ : GradeVector Γ.length) → γ.rename (fun x => x) = γ
    | [], _ => funext fun y => nomatch y
    | _ :: _, γ => by
      show update 𝟘ᶜ _ _ +ᶜ rename (fun x => γ x.succ) (fun x => (.succ x : Var _ _)) = _
      rw [rename_commutes.rename_succ (fun x => γ x.succ) (fun x => x), rename_id]
      funext y
      cases y using Fin.cases with
      | zero =>
        show (if _ then γ (Var.toFin .zero) else Grade.zero) + Grade.zero = γ 0
        exact (congrArg (· + Grade.zero) (ite_eq_left rfl)).trans
          ((Grade.modality.semiring.add_comm _ _).trans (Grade.modality.semiring.zero_add _))
      | succ y =>
        simp only [add, update, zero, extend, Var.toFin, Fin.cases_succ]
        exact (congrArg (· + _) (rename_commutes.ite_succ_zero _ _)).trans
          (Grade.modality.semiring.zero_add _)

end Sic.Grading.GradeVector

namespace Sic.Core

open Sic.Grading

/-- The grades of the recursive results of branches substituted are those of the branches. -/
theorem Branches.resultGrades_subst {k : Nat} {Γ Δ : Scope} (θ : Subst k Γ Δ) (us : Branches k Δ) :
    (us.subst θ).resultGrades = us.resultGrades := by
  funext i rs
  simp only [Branches.resultGrades, Branches.grades_subst]

/-! ## Stability of the Usage -/

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/-- The judgments of usage are stable under the renamings. -/
structure UsageStableUnderRenaming : Prop where
  /-- A term, renamed, uses the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.t` -/
  usage : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {γ : GradeVector Δ.length} {m : Mode}
    {t : Term k Δ} (α : Ren Γ Δ), Usage sig γ m t → Usage sig (γ.rename α) m (t.rename α)
  /-- Arguments of a telescope, renamed, use the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\bar t` -/
  usageArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {γ : GradeVector Δ.length} {m : Mode} {ts : Args k Δ ps} (α : Ren Γ Δ),
    UsageArgs sig γ m ts → UsageArgs sig (γ.rename α) m (ts.rename α)
  /-- Arguments of an instance, renamed, use the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\bar a` -/
  usageInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {γ : GradeVector Δ.length}
    {m : Mode} {ζ : GradeVector Ψ.length} {as : InstanceArgs k Δ Ψ} (α : Ren Γ Δ),
    UsageInstanceArgs sig γ m ζ as → UsageInstanceArgs sig (γ.rename α) m ζ (as.rename α)
  /-- A telescope, renamed, uses the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\Theta` -/
  usageTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {γ : GradeVector Δ.length} {m : Mode} {Θ : Telescope k Δ ps} (α : Ren Γ Δ),
    UsageTelescope sig γ m Θ → UsageTelescope sig (γ.rename α) m (Θ.rename α)

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/-- The judgments of usage are stable under the renamings.
RFC: `\mathsf{ren}_{▶}.t`
RFC: `\mathsf{ren}_{▶}.\bar t`
RFC: `\mathsf{ren}_{▶}.\bar a`
RFC: `\mathsf{ren}_{▶}.\Theta` -/
theorem usageStableUnderRenaming : UsageStableUnderRenaming :=
  ⟨fun α h => by rw [Term.rename_eq_subst]; exact usage h fun _ => rfl,
    fun α h => by rw [Args.rename_eq_subst]; exact usageArgs h fun _ => rfl,
    fun α h => by rw [InstanceArgs.rename_eq_subst]; exact usageInstanceArgs h fun _ => rfl,
    fun α h => by rw [Telescope.rename_eq_subst]; exact usageTelescope h fun _ => rfl⟩
where
  usage {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {α : Ren Γ Δ}
      {γ : GradeVector Δ.length} {m : Mode} {t : Term k Δ} :
      Usage sig γ m t → (∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) →
        Usage sig (γ.rename α) m (t.subst θ)
    | .var (x := x) hts, hθ => by
      rw [Term.var_subst_of (hθ x), GradeVector.rename_commutes.rename_add,
        GradeVector.rename_commutes.rename_update]
      exact .var (usageArgs hts hθ)
    | .const h hm, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .const h hm
    | .sort, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .sort
    | .inst h hq hp has, hθ => .inst h hq hp (usageInstanceArgs has hθ)
    | .ctor h hc hq hp hts, hθ => by
      rw [Term.ctor_subst]
      exact .ctor h hc hq hp (usageArgs hts hθ)
    | .recursor (Cs := Cs) (us := us) (δs := δs) (gs := gs) h hq hp hC ht hul hus hu hg
        hχ hr hprop, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      refine .recursor (δs := fun i => (δs i).rename α) (gs := gs) h hq hp ?_
        (usage ht hθ) ((Branches.length_subst _ us).trans hul) ?_ ?_
        (by rw [Branches.resultGrades_subst]; exact hg) ?_ hr hprop
      · intro j n C hC'
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
        have ih := usage (hC j n C₀ hC₀) (Subst.liftN_eta_of _ hθ)
        simp only [GradeVector.rename_commutes.rename_zero] at ih
        exact ih
      · intro i j T' con hi
        obtain ⟨u, hu'⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst _ hu'⟩
      · intro i j T' con u hi hu'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv _ hu'
        have ih := usage (hu i j T' con u₀ hi hu₀)
          (Subst.liftN_eta_of _ (Subst.liftN_eta_of _ hθ))
        rw [GradeVector.rename_extendResults _ _ _ _ (Ren.liftN _ α),
          GradeVector.rename_extendGrades _ _ _ α] at ih
        rw [Branches.resultGrades_subst]
        exact ih
      · intro i j T' con hi
        have := GradeVector.rename_commutes.rename_le α (hχ i j T' con hi)
        rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul] at this
        rw [Branches.resultGrades_subst]
        exact this
    | .obs h hq hp hd ht hbs hm, hθ => by
      rw [Term.obs_subst, GradeVector.rename_commutes.rename_add]
      exact .obs h hq hp hd (usage ht hθ) (usageArgs hbs hθ) hm
    | .corec (Ss := Ss) (gs := gs) (δs := δs) h hq hp hh hS hSu hss hgl hSl hSs hgs hgu hδ hδr,
        hθ => by
      rw [Term.corec_subst, GradeVector.rename_commutes.rename_add,
        GradeVector.rename_commutes.rename_smul]
      refine .corec (δs := fun i => (δs i).rename α) h hq hp hh (States.get_subst _ hS) ?_
        (usageArgs hss hθ) ((CorecBranches.length_subst _ gs).trans hgl)
        ((States.length_subst _ Ss).trans hSl) ?_ ?_ ?_ ?_ ?_
      · intro j ps'' S' hS'
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        have ih := usageTelescope (hSu j ps'' S₀ hS₀) hθ
        rw [GradeVector.rename_commutes.rename_zero] at ih
        exact ih
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst _ hS'⟩
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst _ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv _ hg
        have ih := usage (hgu i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀)
          (Subst.liftN_eta_of _ (Subst.liftN_eta_of _ hθ))
        rw [GradeVector.rename_extendParams _ _ ps₁ (Ren.liftN ps''.length α),
          GradeVector.rename_extendParams _ _ ps'' α] at ih
        exact ih
      · intro i j T' d p q ps₁ Ξ Θ B ψ hi hd
        have := GradeVector.rename_commutes.rename_le α (hδ i j T' d p q ps₁ Ξ Θ B ψ hi hd)
        rw [GradeVector.rename_commutes.rename_smul] at this
        exact this
      · intro i j T' d p q ps₁ Ξ Θ B ψ D' hi hd hn
        have := GradeVector.rename_commutes.rename_le α (hδr i j T' d p q ps₁ Ξ Θ B ψ D' hi hd hn)
        rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul,
          GradeVector.rename_commutes.rename_smul] at this
        exact this
    | .sub h hle, hθ => .sub (usage h hθ) (GradeVector.rename_commutes.rename_le α hle)
  usageArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {α : Ren Γ Δ}
      {ps : List Parameter} {γ : GradeVector Δ.length} {m : Mode} {ts : Args k Δ ps} :
      UsageArgs sig γ m ts → (∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) →
        UsageArgs sig (γ.rename α) m (ts.subst θ)
    | .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .cons ht hts, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      exact .cons (usage ht hθ) (usageArgs hts hθ)
  usageInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {α : Ren Γ Δ}
      {γ : GradeVector Δ.length} {m : Mode} :
      {Ψ : Scope} → {ζ : GradeVector Ψ.length} → {as : InstanceArgs k Δ Ψ} →
      UsageInstanceArgs sig γ m ζ as → (∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) →
        UsageInstanceArgs sig (γ.rename α) m ζ (as.subst θ)
    -- A pattern of a rule elaborates only when the scope of the parameters is given its first
    -- entry, which the vector `ζ ∙ p` of the conclusion does not give the elaborator.
    | [], _, _, .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .var :: _, _, _, .var has ha, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      exact .var (usageInstanceArgs has hθ) (usage ha hθ)
    | .secondOrder _ _ :: _, _, _, .secondOrder has hB, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      have ih := usage hB (Subst.liftN_eta_of _ hθ)
      rw [GradeVector.rename_extendParams _ _ _ α] at ih
      exact .secondOrder (usageInstanceArgs has hθ) ih
  usageTelescope {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {α : Ren Γ Δ}
      {ps : List Parameter} {γ : GradeVector Δ.length} {m : Mode} {Θ : Telescope k Δ ps} :
      UsageTelescope sig γ m Θ → (∀ {a} (x : Var Δ a), θ x = Var.eta (α x)) →
        UsageTelescope sig (γ.rename α) m (Θ.subst θ)
    | .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .cons hA hΘ, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      have ih := usageTelescope hΘ (Subst.lift_eta_of hθ)
      rw [GradeVector.rename_commutes.rename_extend _ _ α] at ih
      exact .cons (usage hA hθ) ih
    | .sub h hle, hθ => .sub (usageTelescope h hθ) (GradeVector.rename_commutes.rename_le α hle)

end Sic.Core
