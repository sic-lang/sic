module

public import Sic.Core.Substitution
public import Sic.Core.Usage

/-!
# Renaming of the Usage

The judgments of usage of annex 11 of RFC 36 are stable under the renamings: a term that uses the
variables of its scope as `γ` allows, renamed by `ξ`, uses them as the vector `ξ γ` allows, which
gives each variable the sum of the grades of the variables that `ξ` renames to it.

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

/-! ## Renamed Vectors -/

-- ADE: `wkConₘ`, in `Graded/Context/Weakening.agda`, for the renamings that keep the order.
/-- `ξ γ`: the vector `γ` renamed by `ξ`, which gives each variable of `Γ` the sum of the grades
that `γ` gives the variables that `ξ` renames to it, the grade `𝟘` to a variable that is the image
of none.
RFC: `\mathsf{ren}_\gamma` -/
def GradeVector.rename {Γ : Scope} : {Δ : Scope} → GradeVector Δ.length → Ren Γ Δ →
    GradeVector Γ.length
  | [], _, _ => 𝟘ᶜ
  | _ :: _, γ, ξ => GradeVector.update 𝟘ᶜ (ξ .zero).toFin (γ (Var.toFin .zero)) +ᶜ
      GradeVector.rename (fun x => γ x.succ) (fun x => ξ (.succ x))

namespace GradeVector

-- ADE: `wk-𝟘ᶜ`, `wk-+ᶜ`, `wk-·ᶜ`, `wk-≤ᶜ`, `wk-,≔` and `wkConₘ` of `lift`, in
-- `Graded/Context/Weakening.agda`.
/-- The renaming of the vectors commutes with their operations and keeps their order, so that the
renaming of the usage follows its rules one by one. -/
structure RenameCommutes : Prop where
  /-- The zero vector, renamed, is the zero vector.
  RFC: `\mathsf{ren}_\gamma.{00}` -/
  rename_zero : ∀ {Γ Δ : Scope} (ξ : Ren Γ Δ), (𝟘ᶜ : GradeVector Δ.length).rename ξ = 𝟘ᶜ
  /-- The sum of two vectors, renamed, is the sum of the vectors renamed.
  RFC: `\mathsf{ren}_\gamma.{+}` -/
  rename_add : ∀ {Γ Δ : Scope} (γ δ : GradeVector Δ.length) (ξ : Ren Γ Δ),
    (γ +ᶜ δ).rename ξ = γ.rename ξ +ᶜ δ.rename ξ
  /-- A vector multiplied by a grade, renamed, is the vector renamed multiplied by the grade.
  RFC: `\mathsf{ren}_\gamma.{\cdot}` -/
  rename_smul : ∀ {Γ Δ : Scope} (p : Grade) (γ : GradeVector Δ.length) (ξ : Ren Γ Δ),
    (p ·ᶜ γ).rename ξ = p ·ᶜ γ.rename ξ
  /-- The renaming keeps the order.
  RFC: `\mathsf{ren}_\gamma.{\le}` -/
  rename_le : ∀ {Γ Δ : Scope} {γ δ : GradeVector Δ.length} (ξ : Ren Γ Δ), γ ≤ᶜ δ →
    γ.rename ξ ≤ᶜ δ.rename ξ
  /-- The zero vector updated at a variable, renamed, is the zero vector updated at its image.
  RFC: `\mathsf{ren}_\gamma.\mathsf{update}` -/
  rename_update : ∀ {Γ Δ : Scope} {e : Scope.Entry} (x : Var Δ e) (p : Grade) (ξ : Ren Γ Δ),
    (update 𝟘ᶜ x.toFin p).rename ξ = update 𝟘ᶜ (ξ x).toFin p
  /-- An extended vector, renamed under the new variable, is the vector renamed, extended.
  RFC: `\mathsf{ren}_\gamma.{\bullet}` -/
  rename_extend : ∀ {Γ Δ : Scope} {e : Scope.Entry} (γ : GradeVector Δ.length) (p : Grade)
    (ξ : Ren Γ Δ), rename (Δ := e :: Δ) (γ ∙ p) (Ren.lift ξ) = γ.rename ξ ∙ p

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
  rename_zero {Γ : Scope} : {Δ : Scope} → (ξ : Ren Γ Δ) → (𝟘ᶜ : GradeVector Δ.length).rename ξ = 𝟘ᶜ
    | [], _ => rfl
    | _ :: _, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ rename 𝟘ᶜ _ = _
      rw [rename_zero]
      funext y
      simp only [add, update, zero]
      split <;> rfl
  rename_add {Γ : Scope} : {Δ : Scope} → (γ δ : GradeVector Δ.length) → (ξ : Ren Γ Δ) →
      (γ +ᶜ δ).rename ξ = γ.rename ξ +ᶜ δ.rename ξ
    | [], _, _, _ => funext fun _ => rfl
    | _ :: _, γ, δ, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ rename ((fun x => γ x.succ) +ᶜ (fun x => δ x.succ)) _ = _
      rw [rename_add]
      funext y
      simp only [rename, add, update, zero]
      generalize γ (Var.toFin .zero) = a
      generalize δ (Var.toFin .zero) = b
      generalize rename (fun x => γ x.succ) (fun x => ξ (.succ x)) y = c
      generalize rename (fun x => δ x.succ) (fun x => ξ (.succ x)) y = d
      split <;> revert a b c d <;> decide
  rename_smul {Γ : Scope} : {Δ : Scope} → (p : Grade) → (γ : GradeVector Δ.length) → (ξ : Ren Γ Δ) →
      (p ·ᶜ γ).rename ξ = p ·ᶜ γ.rename ξ
    | [], p, _, _ => funext fun _ => (Grade.modality.semiring.mul_zero p).symm
    | _ :: _, p, γ, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ rename (p ·ᶜ (fun x => γ x.succ)) _ = _
      rw [rename_smul]
      funext y
      simp only [rename, add, smul, update, zero]
      generalize γ (Var.toFin .zero) = a
      generalize rename (fun x => γ x.succ) (fun x => ξ (.succ x)) y = c
      split <;> revert p a c <;> decide
  rename_le {Γ : Scope} : {Δ : Scope} → {γ δ : GradeVector Δ.length} → (ξ : Ren Γ Δ) → γ ≤ᶜ δ →
      γ.rename ξ ≤ᶜ δ.rename ξ
    | [], _, _, _, _ => fun _ => Grade.le_refl _
    | _ :: _, _, _, ξ, h => by
      refine add_le_add (fun y => ?_) (rename_le (fun x => ξ (.succ x)) fun x => h x.succ)
      simp only [update]
      split
      · exact h _
      · exact Grade.le_refl _
  rename_update {Γ : Scope} : {Δ : Scope} → {e : Scope.Entry} → (x : Var Δ e) → (p : Grade) →
      (ξ : Ren Γ Δ) → (update 𝟘ᶜ x.toFin p).rename ξ = update 𝟘ᶜ (ξ x).toFin p
    | _ :: Δ, _, .zero, p, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ rename (Δ := Δ) (fun y => update 𝟘ᶜ (Var.toFin .zero) p y.succ) _ = _
      rw [show (fun y : Fin Δ.length => update 𝟘ᶜ (Var.toFin (.zero (Γ := Δ))) p y.succ) = 𝟘ᶜ from
        funext fun y => by simp [update, Var.toFin, zero, Fin.ext_iff], rename_zero]
      funext y
      simp only [add, update, zero]
      split <;> revert p <;> decide
    | _ :: Δ, _, .succ x, p, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ
        rename (Δ := Δ) (fun y => update 𝟘ᶜ (Var.toFin (.succ x)) p y.succ) _ = _
      rw [show (fun y : Fin Δ.length => update 𝟘ᶜ (Var.toFin (.succ x)) p y.succ) =
          update 𝟘ᶜ x.toFin p from funext fun y => by simp [update, Var.toFin, zero],
        rename_update x p (fun y => ξ (.succ y))]
      funext y
      simp [add, update, zero, Var.toFin, Fin.ext_iff, Grade.modality.semiring.zero_add]
  rename_succ {Γ : Scope} : {Δ : Scope} → {e : Scope.Entry} → (γ : GradeVector Δ.length) →
      (ξ : Ren Γ Δ) → γ.rename (fun x => (ξ x).succ (e' := e)) = γ.rename ξ ∙ Grade.zero
    | [], _, _, _ => funext fun y => by cases y using Fin.cases <;> rfl
    | _ :: _, e, γ, ξ => by
      show update 𝟘ᶜ _ _ +ᶜ rename _ (fun x => (ξ (.succ x)).succ (e' := e)) = _
      rw [rename_succ (fun x => γ x.succ) (fun x => ξ (.succ x))]
      funext y
      cases y using Fin.cases with
      | zero =>
        simp [add, update, zero, extend, Var.toFin, Fin.ext_iff, Grade.modality.semiring.zero_add]
      | succ y => simp [add, update, zero, extend, rename, Var.toFin, Fin.ext_iff]
  rename_extend {Γ : Scope} {Δ : Scope} {e : Scope.Entry} (γ : GradeVector Δ.length) (p : Grade)
      (ξ : Ren Γ Δ) : rename (Δ := e :: Δ) (γ ∙ p) (Ren.lift ξ) = γ.rename ξ ∙ p := by
    show update 𝟘ᶜ _ p +ᶜ rename γ (fun x => (ξ x).succ (e' := e)) = _
    rw [rename_succ]
    funext y
    cases y using Fin.cases with
    | zero =>
      simp only [add, update, zero, extend, Ren.lift, Var.toFin, Fin.cases_zero]
      split
      · exact (Grade.modality.semiring.add_comm _ _).trans (Grade.modality.semiring.zero_add _)
      · exact absurd rfl ‹_›
    | succ y =>
      simp [add, update, zero, extend, Ren.lift, Var.toFin, Fin.ext_iff,
        Grade.modality.semiring.zero_add]

/-- A vector extended by the grades of the variables of a telescope, renamed under them, is the
vector renamed, extended. -/
theorem rename_extendParams {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) → (r : Grade) →
    (ps : List Parameter) → (ξ : Ren Γ Δ) →
      (γ.extendParams r ps).rename (Ren.liftN ps.length ξ) = (γ.rename ξ).extendParams r ps
  | _, _, _, [], _ => rfl
  | _, γ, r, p :: ps, ξ =>
    (rename_extendParams (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ (r * p.usage)) r ps
      (Ren.lift ξ)).trans
      (congrArg (fun δ => extendParams δ r ps) (rename_commutes.rename_extend γ _ ξ))

/-- A vector extended by the grades `g`, renamed under the new variables, is the vector renamed,
extended. -/
theorem rename_extendGrades {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) →
    (g : Nat → Grade) → (ps : List Parameter) → (ξ : Ren Γ Δ) →
      (γ.extendGrades g ps).rename (Ren.liftN ps.length ξ) = (γ.rename ξ).extendGrades g ps
  | _, _, _, [], _ => rfl
  | _, γ, g, _ :: ps, ξ =>
    (rename_extendGrades (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ g 0) (fun l => g (l + 1)) ps
      (Ren.lift ξ)).trans
      (congrArg (fun δ => extendGrades δ (fun l => g (l + 1)) ps)
        (rename_commutes.rename_extend γ _ ξ))

/-- A vector extended by the grades of the recursive results, renamed under them, is the vector
renamed, extended. -/
theorem rename_extendResults {Γ : Scope} : {Δ : Scope} → (γ : GradeVector Δ.length) →
    (e : Nat → Grade) → (rs : List (Option Name)) → (ps : List Parameter) → (ξ : Ren Γ Δ) →
      (γ.extendResults e rs ps).rename (Ren.liftN (Telescope.resultParams rs ps).length ξ) =
        (γ.rename ξ).extendResults e rs ps
  | _, γ, e, some _ :: rs, _ :: ps, ξ =>
    (rename_extendResults (Γ := .var :: Γ) (Δ := .var :: _) (γ ∙ e 0) (fun l => e (l + 1)) rs ps
      (Ren.lift ξ)).trans
      (congrArg (fun δ => extendResults δ (fun l => e (l + 1)) rs ps)
        (rename_commutes.rename_extend γ _ ξ))
  | _, γ, e, none :: rs, _ :: ps, ξ => rename_extendResults γ (fun l => e (l + 1)) rs ps ξ
  | _, _, _, [], _, _ | _, _, _, some _ :: _, [], _ | _, _, _, none :: _, [], _ => rfl

end GradeVector

/-! ## Stability of the Usage -/

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/-- The judgments of usage are stable under the renamings. -/
structure UsageStableUnderRenaming : Prop where
  /-- A term, renamed, uses the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.t` -/
  usage : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {γ : GradeVector Δ.length} {m : Mode}
    {t : Term k Δ} (ξ : Ren Γ Δ), Usage sig γ m t → Usage sig (γ.rename ξ) m (t.rename ξ)
  /-- Arguments of a telescope, renamed, use the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\bar t` -/
  usageArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {γ : GradeVector Δ.length} {m : Mode} {ts : Args k Δ ps} (ξ : Ren Γ Δ),
    UsageArgs sig γ m ts → UsageArgs sig (γ.rename ξ) m (ts.rename ξ)
  /-- Arguments of an instance, renamed, use the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\bar a` -/
  usageInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ Ψ : Scope} {γ : GradeVector Δ.length}
    {m : Mode} {ζ : GradeVector Ψ.length} {as : InstanceArgs k Δ Ψ} (ξ : Ren Γ Δ),
    UsageInstanceArgs sig γ m ζ as → UsageInstanceArgs sig (γ.rename ξ) m ζ (as.rename ξ)
  /-- A telescope, renamed, uses the variables as the vector renamed allows.
  RFC: `\mathsf{ren}_{▶}.\Theta` -/
  usageTelescope : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {γ : GradeVector Δ.length} {m : Mode} {Θ : Telescope k Δ ps} (ξ : Ren Γ Δ),
    UsageTelescope sig γ m Θ → UsageTelescope sig (γ.rename ξ) m (Θ.rename ξ)

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/-- The judgments of usage are stable under the renamings.
RFC: `\mathsf{ren}_{▶}.t`
RFC: `\mathsf{ren}_{▶}.\bar t`
RFC: `\mathsf{ren}_{▶}.\bar a`
RFC: `\mathsf{ren}_{▶}.\Theta` -/
theorem usageStableUnderRenaming : UsageStableUnderRenaming :=
  ⟨fun ξ h => by rw [Term.rename_eq_subst]; exact usage h fun _ => rfl,
    fun ξ h => by rw [Args.rename_eq_subst]; exact usageArgs h fun _ => rfl,
    fun ξ h => by rw [InstanceArgs.rename_eq_subst]; exact usageInstanceArgs h fun _ => rfl,
    fun ξ h => by rw [Telescope.rename_eq_subst]; exact usageTelescope h fun _ => rfl⟩
where
  usage {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {γ : GradeVector Δ.length} {m : Mode} {t : Term k Δ} :
      Usage sig γ m t → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        Usage sig (γ.rename ξ) m (t.subst θ)
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
    | .recursor (Cs := Cs) (us := us) (δs := δs) (gs := gs) (es := es) h hq hp hC ht hul hus hu hg
        hχ hr, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      refine .recursor (δs := fun i => (δs i).rename ξ) (gs := gs) (es := es) h hq hp ?_
        (usage ht hθ) ((Branches.length_subst _ us).trans hul) ?_ ?_ hg ?_ hr
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
        rw [GradeVector.rename_extendResults _ _ _ _ (Ren.liftN _ ξ),
          GradeVector.rename_extendGrades _ _ _ ξ] at ih
        exact ih
      · intro i j T' con hi
        have := GradeVector.rename_commutes.rename_le ξ (hχ i j T' con hi)
        rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul] at this
        exact this
    | .obs h hq hp hd ht hbs hm, hθ => by
      rw [Term.obs_subst, GradeVector.rename_commutes.rename_add]
      exact .obs h hq hp hd (usage ht hθ) (usageArgs hbs hθ) hm
    | .corec (Ss := Ss) (gs := gs) (δs := δs) h hq hp hh hS hSu hss hgl hSl hSs hgs hgu hδ, hθ => by
      rw [Term.corec_subst, GradeVector.rename_commutes.rename_add,
        GradeVector.rename_commutes.rename_smul]
      refine .corec (δs := fun i => (δs i).rename ξ) h hq hp hh (States.get_subst _ hS) ?_
        (usageArgs hss hθ) ((CorecBranches.length_subst _ gs).trans hgl)
        ((States.length_subst _ Ss).trans hSl) ?_ ?_ ?_ ?_
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
        rw [GradeVector.rename_extendParams _ _ ps₁ (Ren.liftN ps''.length ξ),
          GradeVector.rename_extendParams _ _ ps'' ξ] at ih
        exact ih
      · intro i j T' d p q ps₁ Ξ Θ B ψ hi hd
        have := GradeVector.rename_commutes.rename_le ξ (hδ i j T' d p q ps₁ Ξ Θ B ψ hi hd)
        rw [GradeVector.rename_commutes.rename_smul] at this
        exact this
    | .sub h hle, hθ => .sub (usage h hθ) (GradeVector.rename_commutes.rename_le ξ hle)
  usageArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ps : List Parameter} {γ : GradeVector Δ.length} {m : Mode} {ts : Args k Δ ps} :
      UsageArgs sig γ m ts → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        UsageArgs sig (γ.rename ξ) m (ts.subst θ)
    | .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .cons ht hts, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      exact .cons (usage ht hθ) (usageArgs hts hθ)
  usageInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {γ : GradeVector Δ.length} {m : Mode} :
      {Ψ : Scope} → {ζ : GradeVector Ψ.length} → {as : InstanceArgs k Δ Ψ} →
      UsageInstanceArgs sig γ m ζ as → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        UsageInstanceArgs sig (γ.rename ξ) m ζ (as.subst θ)
    -- A pattern of a rule elaborates only when the scope of the parameters is given its first
    -- entry, which the vector `ζ ∙ p` of the conclusion does not give the elaborator.
    | [], _, _, .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .var :: _, _, _, .var has ha, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      exact .var (usageInstanceArgs has hθ) (usage ha hθ)
    | .secondOrder _ _ :: _, _, _, .secondOrder has hB, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      have ih := usage hB (Subst.liftN_eta_of _ hθ)
      rw [GradeVector.rename_extendParams _ _ _ ξ] at ih
      exact .secondOrder (usageInstanceArgs has hθ) ih
  usageTelescope {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ps : List Parameter} {γ : GradeVector Δ.length} {m : Mode} {Θ : Telescope k Δ ps} :
      UsageTelescope sig γ m Θ → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        UsageTelescope sig (γ.rename ξ) m (Θ.subst θ)
    | .nil, _ => by rw [GradeVector.rename_commutes.rename_zero]; exact .nil
    | .cons hA hΘ, hθ => by
      rw [GradeVector.rename_commutes.rename_add, GradeVector.rename_commutes.rename_smul]
      have ih := usageTelescope hΘ (Subst.lift_eta_of hθ)
      rw [GradeVector.rename_commutes.rename_extend _ _ ξ] at ih
      exact .cons (usage hA hθ) ih
    | .sub h hle, hθ => .sub (usageTelescope h hθ) (GradeVector.rename_commutes.rename_le ξ hle)

end Sic.Core
