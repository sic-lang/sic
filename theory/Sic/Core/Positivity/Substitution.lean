module

public import Sic.Core.Positivity
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels

/-!
# Substitution of the Terms in Which Variables Do Not Occur

A term in which a variable does not occur, as the strict positivity of annex 14 of RFC 36 says it,
does not read what a substitution gives this variable: two substitutions give it the same term when
they give the same abstractions to the variables that occur in it, and so do they to a telescope.

A term in which a variable does not occur is a term of the scope without this variable, renamed, so
that the property holds for one variable by the composition of a renaming and a substitution; for
several variables, the substitutions are changed one variable at a time, in the order of the levels
of the variables, which tell them apart.

ADE have no declared types, and no strict positivity.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat}

/-! ## Levels of the Variables -/

/-- The level of a variable is below the length of its scope. -/
theorem Var.level_lt : {Γ : Scope} → {e : Scope.Entry} → (x : Var Γ e) → x.level < Γ.length
  | _ :: _, _, .zero => Nat.lt_succ_self _
  | _ :: _, _, .succ x => Nat.lt_succ_of_lt x.level_lt

/-- Each level below the length of a scope is that of one of its variables. -/
theorem Var.exists_level : (Γ : Scope) → (i : Nat) → i < Γ.length →
    ∃ (e : Scope.Entry) (x : Var Γ e), x.level = i
  | e :: Γ, i, h =>
    if hi : i = Γ.length then ⟨e, .zero, hi.symm⟩
    else
      have ⟨e', x, hx⟩ := Var.exists_level Γ i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hi)
      ⟨e', .succ x, hx⟩

/-- Two variables of a scope with the same level are the same variable. -/
theorem Var.eq_of_level : {Γ : Scope} → {e e' : Scope.Entry} → (x : Var Γ e) → (y : Var Γ e') →
    x.level = y.level → (⟨e, x⟩ : Σ e, Var Γ e) = ⟨e', y⟩
  | _ :: _, _, _, .zero, .zero, _ => rfl
  | _ :: _, _, _, .zero, .succ y, h => absurd h (Nat.ne_of_gt y.level_lt)
  | _ :: _, _, _, .succ x, .zero, h => absurd h (Nat.ne_of_lt x.level_lt)
  | _ :: _, _, _, .succ x, .succ y, h => by
    have := Var.eq_of_level x y h
    cases this
    rfl

/-- The renaming that skips a variable reaches no variable of its level. -/
theorem Var.skip_level_ne {e' : Scope.Entry} : {Γ : Scope} → {e : Scope.Entry} → (x : Var Γ e) →
    (y : Var (Scope.remove Γ x) e') → (x.skip y).level ≠ x.level
  | _ :: _, _, .zero, y => Nat.ne_of_lt y.level_lt
  | _ :: Γ, _, .succ x, y => by
    cases y with
    | zero => exact Nat.ne_of_gt x.level_lt
    | succ y => exact Var.skip_level_ne x y

/-! ## Substitutions That Differ at the Variables That Do Not Occur -/

/-- What reads two substitutions alike when they differ at one variable with the property `P` reads
them alike when they differ at any variables with this property: the first one is changed into the
second one a variable at a time, in the order of their levels. -/
theorem Subst.eq_of_each {β : Type} {Ξ Γ : Scope} (f : Subst k Ξ Γ → β)
    (P : ∀ {e : Scope.Entry}, Var Γ e → Prop)
    (hf : ∀ {e : Scope.Entry} (x : Var Γ e) (σ σ' : Subst k Ξ Γ), P x →
      (∀ {e' : Scope.Entry} (y : Var Γ e'), y.level ≠ x.level → σ y = σ' y) → f @σ = f @σ')
    {σ σ' : Subst k Ξ Γ} (h : ∀ {e : Scope.Entry} (x : Var Γ e), σ x = σ' x ∨ P x) :
    f @σ = f @σ' := by
  let mix : Nat → Subst k Ξ Γ := fun i _ x => if x.level < i then σ x else σ' x
  have hmix : ∀ i, f (mix i) = f @σ' := by
    intro i
    induction i with
    | zero =>
      have e : @Eq (Subst k Ξ Γ) (mix 0) @σ' := funext fun _ => funext fun x => ite_eq_right (Nat.not_lt_zero _)
      rw [e]
    | succ i ih =>
      rw [← ih]
      by_cases hi : i < Γ.length
      · obtain ⟨e, x, hx⟩ := Var.exists_level Γ i hi
        rcases h x with hσ | hP
        · have e' : @Eq (Subst k Ξ Γ) (mix (i + 1)) (mix i) := funext fun e' => funext fun y => by
            show (if y.level < i + 1 then σ y else σ' y) = if y.level < i then σ y else σ' y
            by_cases hy : y.level = i
            · have := Var.eq_of_level x y (hx.trans hy.symm)
              cases this
              rw [ite_eq_left (by omega), ite_eq_right (by omega)]
              exact hσ
            · by_cases hlt : y.level < i
              · rw [ite_eq_left (by omega), ite_eq_left hlt]
              · rw [ite_eq_right (by omega), ite_eq_right hlt]
          rw [e']
        · refine hf x (mix (i + 1)) (mix i) hP fun y hy => ?_
          show (if y.level < i + 1 then σ y else σ' y) = if y.level < i then σ y else σ' y
          by_cases hlt : y.level < i
          · rw [ite_eq_left (by omega), ite_eq_left hlt]
          · rw [ite_eq_right (by omega), ite_eq_right hlt]
      · have e' : @Eq (Subst k Ξ Γ) (mix (i + 1)) (mix i) := funext fun e' => funext fun y => by
          show (if y.level < i + 1 then σ y else σ' y) = if y.level < i then σ y else σ' y
          have := y.level_lt
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
        rw [e']
  have e : @Eq (Subst k Ξ Γ) (mix Γ.length) @σ := funext fun _ => funext fun x => ite_eq_left x.level_lt
  rw [← hmix Γ.length, e]

/-- Two substitutions that give the same abstractions to the variables that occur in a term give it
the same term. -/
theorem Term.subst_eq_of_avoids {Ξ Γ : Scope} {A : Term k Γ} {σ σ' : Subst k Ξ Γ}
    (h : ∀ {e : Scope.Entry} (x : Var Γ e), σ x = σ' x ∨ A.Avoids x) : A.subst σ = A.subst σ' :=
  Subst.eq_of_each (fun σ => A.subst σ) (fun x => A.Avoids x)
    (fun x σ σ' ⟨A', hA'⟩ hσ => by
      show A.subst σ = A.subst σ'
      rw [hA', Term.subst_rename_of (θ' := fun y => σ (x.skip y)) (fun _ => rfl),
        Term.subst_rename_of (θ' := fun y => σ (x.skip y))
          (fun y => (hσ (x.skip y) (Var.skip_level_ne x y)).symm)]) h

/-- Two substitutions that give the same abstractions to the variables that occur in a telescope
give it the same telescope. -/
theorem Telescope.subst_eq_of_avoids {Ξ Γ : Scope} {ps : List Parameter} {Θ : Telescope k Γ ps}
    {σ σ' : Subst k Ξ Γ} (h : ∀ {e : Scope.Entry} (x : Var Γ e), σ x = σ' x ∨ Θ.Avoids x) :
    Θ.subst σ = Θ.subst σ' :=
  Subst.eq_of_each (fun σ => Θ.subst σ) (fun x => Θ.Avoids x)
    (fun x σ σ' ⟨Θ', hΘ'⟩ hσ => by
      show Θ.subst σ = Θ.subst σ'
      rw [hΘ', Telescope.subst_rename_of (θ' := fun y => σ (x.skip y)) (fun _ => rfl),
        Telescope.subst_rename_of (θ' := fun y => σ (x.skip y))
          (fun y => (hσ (x.skip y) (Var.skip_level_ne x y)).symm)]) h

/-- Two substitutions that give the same abstractions to the variables that occur in arguments give
them the same arguments. -/
theorem Args.subst_eq_of_avoids {Ξ Γ : Scope} {ps : List Parameter} {ts : Args k Γ ps}
    {σ σ' : Subst k Ξ Γ} (h : ∀ {e : Scope.Entry} (x : Var Γ e), σ x = σ' x ∨ ts.Avoids x) :
    ts.subst σ = ts.subst σ' :=
  Subst.eq_of_each (fun σ => ts.subst σ) (fun x => ts.Avoids x)
    (fun x σ σ' ⟨ts', hts'⟩ hσ => by
      show ts.subst σ = ts.subst σ'
      rw [hts', Args.subst_rename_of (θ' := fun y => σ (x.skip y)) (fun _ => rfl),
        Args.subst_rename_of (θ' := fun y => σ (x.skip y))
          (fun y => (hσ (x.skip y) (Var.skip_level_ne x y)).symm)]) h

/-- Two substitutions that differ at variables with the property `P` give, under new variables, the
same abstractions to the variables that are not these. -/
theorem Subst.liftN_eq_or {Ξ Γ : Scope} {P : ∀ {e : Scope.Entry}, Var Γ e → Prop} :
    (n : Nat) → {σ σ' : Subst k Ξ Γ} → (∀ {e : Scope.Entry} (x : Var Γ e), σ x = σ' x ∨ P x) →
      ∀ {e : Scope.Entry} (z : Var (Γ.extend n) e),
        Subst.liftN n @σ z = Subst.liftN n @σ' z ∨ ∃ x : Var Γ e, z = x.weakenN n ∧ P x
  | 0, _, _, h, _, z => (h z).imp id fun hP => ⟨z, rfl, hP⟩
  | n + 1, σ, σ', h, _, z => by
    have h' := Subst.liftN_eq_or (Γ := .var :: Γ) (Ξ := .var :: Ξ)
      (P := fun {e} z => ∃ x : Var Γ e, z = .succ x ∧ P x) n (σ := Subst.lift (e := .var) @σ)
      (σ' := Subst.lift (e := .var) @σ')
      (fun z => by
        cases z with
        | zero => exact .inl rfl
        | succ x =>
          exact (h x).imp
            (fun hx => by
              show (σ x).rename _ = (σ' x).rename _
              rw [hx])
            fun hP => ⟨x, rfl, hP⟩) z
    exact h'.imp id fun ⟨_, hy, x, hx, hP⟩ => ⟨x, by rw [hy, hx]; rfl, hP⟩

/-! ## Levels of the Terms in Which a Variable Does Not Occur -/

/-- A variable that does not occur in a term does not occur in it at other levels. -/
theorem Term.Avoids.substLevels {k' : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e}
    {A : Term k Γ} (ls' : Fin k → Level k') : A.Avoids x → (A.substLevels ls').Avoids x
  | ⟨A', hA'⟩ => ⟨A'.substLevels ls', by rw [hA', Term.substLevels_rename]⟩

/-- A variable that does not occur in a telescope does not occur in it at other levels. -/
theorem Telescope.Avoids.substLevels {k' : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e}
    {ps : List Parameter} {Θ : Telescope k Γ ps} (ls' : Fin k → Level k') :
    Θ.Avoids x → (Θ.substLevels ls').Avoids x
  | ⟨Θ', hΘ'⟩ => ⟨Θ'.substLevels ls', by rw [hΘ', Telescope.substLevels_rename]⟩

/-- A variable that does not occur in arguments does not occur in them at other levels. -/
theorem Args.Avoids.substLevels {k' : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e}
    {ps : List Parameter} {ts : Args k Γ ps} (ls' : Fin k → Level k') :
    ts.Avoids x → (ts.substLevels ls').Avoids x
  | ⟨ts', hts'⟩ => ⟨ts'.substLevels ls', by rw [hts', Args.substLevels_rename]⟩

/-! ## Variables That Occur -/

/-- A variable occurs in its application to arguments. -/
theorem Term.not_avoids_var {Γ : Scope} {e : Scope.Entry} (x : Var Γ e)
    (ts : Args k Γ e.params) : ¬ (Term.var x ts).Avoids x := by
  intro ⟨A', hA'⟩
  have hl : ∀ t : Term k Γ, t = Term.var x ts →
      ∀ {e'} (y : Var Γ e') (us : Args k Γ e'.params), t = Term.var y us → y.level = x.level := by
    intro t ht e' y us hy
    rw [ht] at hy
    cases hy
    rfl
  cases A' with
  | var y us =>
    rw [Term.rename] at hA'
    exact Var.skip_level_ne x y (hl _ rfl _ _ hA')
  | _ => simp [Term.rename] at hA'

/-- A variable that does not occur in the application of a variable to arguments does not occur
in the arguments. -/
theorem Term.Avoids.var_args {Γ : Scope} {e e' : Scope.Entry} {y : Var Γ e'} {x : Var Γ e}
    {ts : Args k Γ e.params} : (Term.var x ts).Avoids y → ts.Avoids y := by
  intro ⟨A', hA'⟩
  cases A' with
  | var x' ts' =>
    rw [Term.rename] at hA'
    injection hA' with _ he _ hts
    subst he
    exact ⟨ts', eq_of_heq hts⟩
  | _ => simp [Term.rename] at hA'

end Sic.Core
