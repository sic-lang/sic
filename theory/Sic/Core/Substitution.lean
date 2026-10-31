module

public import Sic.Core.Syntax

/-!
# Substitution

The operations that move a term to another context, as in the formalization of ADE: a weakening adds
variables to the context, a substitution replaces each variable by a term, and an instantiation of
the levels replaces each level variable by a level.
A weakening is a first-order object, `Wk`, so that the logical relation quantifies over the
extensions of a context only, while a substitution is a function from the variables to terms.
The laws at the end let the metatheory compose these operations, as the σ-calculus does.
-/

@[expose] public section

namespace Sic.Core

/--
A weakening from a context of `n` variables to a context of `m`, which contains them in the same
order.
-/
inductive Wk : Nat → Nat → Type where
  /-- The weakening that keeps the context. -/
  | id : Wk n n
  /-- The weakening `ρ` followed by a new variable. -/
  | step (ρ : Wk m n) : Wk (m + 1) n
  /-- The weakening `ρ` extended under a binder, whose variable it keeps. -/
  | lift (ρ : Wk m n) : Wk (m + 1) (n + 1)

/-- The index in the larger context of the variable of index `x`. -/
def Wk.var : Wk m n → Fin n → Fin m
  | id, x => x
  | step ρ, x => (ρ.var x).succ
  | lift _, ⟨0, _⟩ => 0
  | lift ρ, ⟨x + 1, h⟩ => (ρ.var ⟨x, Nat.lt_of_succ_lt_succ h⟩).succ

/-- The weakening `ρ₂` followed by `ρ₁`, as ADE's `ρ₁ • ρ₂`. -/
def Wk.comp : Wk m l → Wk l n → Wk m n
  | id, ρ₂ => ρ₂
  | step ρ₁, ρ₂ => step (ρ₁.comp ρ₂)
  | lift ρ₁, id => lift ρ₁
  | lift ρ₁, step ρ₂ => step (ρ₁.comp ρ₂)
  | lift ρ₁, lift ρ₂ => lift (ρ₁.comp ρ₂)

/-- Two weakenings in a row move each variable as their composition does. -/
theorem Wk.var_comp : ∀ (ρ₁ : Wk m l) (ρ₂ : Wk l n) (x : Fin n),
    (ρ₁.comp ρ₂).var x = ρ₁.var (ρ₂.var x)
  | id, _, _ => rfl
  | step ρ₁, ρ₂, x => congrArg Fin.succ (var_comp ρ₁ ρ₂ x)
  | lift _, id, _ => rfl
  | lift ρ₁, step ρ₂, x => congrArg Fin.succ (var_comp ρ₁ ρ₂ x)
  | lift _, lift _, ⟨0, _⟩ => rfl
  | lift ρ₁, lift ρ₂, ⟨x + 1, h⟩ => congrArg Fin.succ (var_comp ρ₁ ρ₂ ⟨x, Nat.lt_of_succ_lt_succ h⟩)

/-- A substitution of terms over `m` variables for the `n` variables of a context. -/
abbrev Subst (k m n : Nat) := Fin n → Term k m

/-- The term `t` moved by the weakening `ρ`, which shifts its variables. -/
def Term.wk {m n : Nat} (ρ : Wk m n) : Term k n → Term k m
  | var x => var (ρ.var x)
  | univ l => univ l
  | pi p q A B => pi p q (A.wk ρ) (B.wk ρ.lift)
  | lam p A t => lam p (A.wk ρ) (t.wk ρ.lift)
  | app p t a => app p (t.wk ρ) (a.wk ρ)

/-- The term `t` moved to a context with one more variable. -/
abbrev Term.wk1 (t : Term k n) : Term k (n + 1) := t.wk (.step .id)

/-- The substitution `σ` extended by the term `a` for a new innermost variable. -/
def Subst.cons (σ : Subst k m n) (a : Term k m) : Subst k m (n + 1)
  | ⟨0, _⟩ => a
  | ⟨x + 1, h⟩ => σ ⟨x, Nat.lt_of_succ_lt_succ h⟩

/-- The substitution `σ` extended under a binder, which maps its variable to itself. -/
def Subst.lift (σ : Subst k m n) : Subst k (m + 1) (n + 1) :=
  Subst.cons (fun x => (σ x).wk1) (.var 0)

/-- Under a binder, the identity substitution stays the identity. -/
theorem Subst.lift_var : Subst.lift (.var : Subst k n n) = .var :=
  funext fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl

namespace Term

variable {j k l m n : Nat}

/-- The term `t` whose variables are replaced by the terms `σ`. -/
def subst {m n : Nat} (σ : Subst k m n) : Term k n → Term k m
  | var x => σ x
  | univ l => univ l
  | pi p q A B => pi p q (A.subst σ) (B.subst σ.lift)
  | lam p A t => lam p (A.subst σ) (t.subst σ.lift)
  | app p t a => app p (t.subst σ) (a.subst σ)

/-- `t[a/x]`: the term `t` whose innermost variable `x` is replaced by `a`. -/
def instantiate (t : Term k (n + 1)) (a : Term k n) : Term k n :=
  t.subst (Subst.cons var a)

/-- The term `t` whose level variables are replaced by the levels `σ`, over `j` other variables. -/
def substLevels {n : Nat} (σ : Fin k → Level j) : Term k n → Term j n
  | var x => var x
  | univ l => univ (l.subst σ)
  | pi p q A B => pi p q (A.substLevels σ) (B.substLevels σ)
  | lam p A t => lam p (A.substLevels σ) (t.substLevels σ)
  | app p t a => app p (t.substLevels σ) (a.substLevels σ)

/-!
The laws of the operations.
Each is proved by induction on the term; under a binder, the induction hypothesis applies to the
operations extended by `lift`, which the first step of each proof shows to agree, variable by
variable.
-/

/-- Two weakenings in a row are the weakening that moves each variable as both do. -/
theorem wk_wk {ρ₁ : Wk m l} {ρ₂ : Wk l n} {ρ : Wk m n} (h : ∀ x, ρ₁.var (ρ₂.var x) = ρ.var x)
    (t : Term k n) : (t.wk ρ₂).wk ρ₁ = t.wk ρ := by
  induction t generalizing m l with
  | var x => exact congrArg var (h x)
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h' : ∀ x, ρ₁.lift.var (ρ₂.lift.var x) = ρ.lift.var x :=
      fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => congrArg Fin.succ (h _)
    simp only [wk, ihA h, ihB h']
  | app _ _ _ iht iha => simp only [wk, iht h, iha h]

/-- Two weakenings in a row are their composition. -/
theorem wk_comp (ρ₁ : Wk m l) (ρ₂ : Wk l n) (t : Term k n) :
    (t.wk ρ₂).wk ρ₁ = t.wk (ρ₁.comp ρ₂) :=
  wk_wk (fun x => (Wk.var_comp ρ₁ ρ₂ x).symm) t

/-- A weakening is the substitution of the variables it moves to. -/
theorem wk_eq_subst (ρ : Wk m n) (t : Term k n) : t.wk ρ = t.subst fun x => var (ρ.var x) := by
  induction t generalizing m with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h : (Subst.lift fun x => (var (ρ.var x) : Term k _)) = fun x => var (ρ.lift.var x) :=
      funext fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl
    simp only [wk, subst, ihA, ihB, h]
  | app _ _ _ iht iha => simp only [wk, subst, iht, iha]

/-- A substitution after a weakening substitutes for the variables moved by the weakening. -/
theorem subst_wk (σ : Subst k m l) (ρ : Wk l n) (t : Term k n) :
    (t.wk ρ).subst σ = t.subst fun x => σ (ρ.var x) := by
  induction t generalizing m l with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h : (fun x => σ.lift (ρ.lift.var x)) = Subst.lift fun x => σ (ρ.var x) :=
      funext fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl
    simp only [wk, subst, ihA, ihB, h]
  | app _ _ _ iht iha => simp only [wk, subst, iht, iha]

/-- A weakening after a substitution weakens each substituted term. -/
theorem wk_subst (ρ : Wk m l) (σ : Subst k l n) (t : Term k n) :
    (t.subst σ).wk ρ = t.subst fun x => (σ x).wk ρ := by
  induction t generalizing m l with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h : (fun x => (σ.lift x).wk ρ.lift) = Subst.lift fun x => (σ x).wk ρ :=
      funext fun
        | ⟨0, _⟩ => rfl
        | ⟨_ + 1, _⟩ => (wk_wk (ρ := ρ.step) (fun _ => rfl) _).trans (wk_wk (fun _ => rfl) _).symm
    simp only [wk, subst, ihA, ihB, h]
  | app _ _ _ iht iha => simp only [wk, subst, iht, iha]

/-- Substituting each variable for itself leaves the term unchanged. -/
theorem subst_var (t : Term k n) : t.subst var = t := by
  induction t with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    simp only [subst, Subst.lift_var, ihA, ihB]
  | app _ _ _ iht iha => simp only [subst, iht, iha]

/-- The weakening `id` leaves the term unchanged. -/
theorem wk_id (t : Term k n) : t.wk .id = t :=
  (wk_eq_subst _ t).trans (subst_var t)

/-- Two substitutions in a row are the substitution of the substituted terms. -/
theorem subst_subst (σ : Subst k l n) (τ : Subst k m l) (t : Term k n) :
    (t.subst σ).subst τ = t.subst fun x => (σ x).subst τ := by
  induction t generalizing m l with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h : (fun x => (σ.lift x).subst τ.lift) =
        Subst.lift fun x => (σ x).subst τ :=
      funext fun
        | ⟨0, _⟩ => rfl
        | ⟨_ + 1, _⟩ => (subst_wk _ _ _).trans (wk_subst _ τ _).symm
    simp only [subst, ihA, ihB, h]
  | app _ _ _ iht iha => simp only [subst, iht, iha]

/-- Substituting in `t[a/x]` substitutes in `t`, under the binder of `x`, and in `a`. -/
theorem subst_instantiate (σ : Subst k m n) (t : Term k (n + 1)) (a : Term k n) :
    (t.instantiate a).subst σ = (t.subst σ.lift).instantiate (a.subst σ) := by
  simp only [instantiate, subst_subst]
  congr
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => exact ((subst_wk _ _ _).trans (subst_var _)).symm

/-- A weakening followed by a new variable moves the term, then moves it past that variable. -/
theorem wk_step (ρ : Wk m n) (t : Term k n) : t.wk ρ.step = (t.wk ρ).wk1 :=
  (wk_wk (ρ := ρ.step) (fun _ => rfl) t).symm

/-- Under a binder, a weakening moves a term moved past the bound variable as it moves the term. -/
theorem wk_lift_wk1 (ρ : Wk m n) (t : Term k n) : t.wk1.wk ρ.lift = (t.wk ρ).wk1 :=
  (wk_wk (ρ := ρ.step) (fun _ => rfl) t).trans (wk_step ρ t)

/-- Weakening `t[a/x]` weakens `t`, under the binder of `x`, and `a`. -/
theorem wk_instantiate (ρ : Wk m n) (t : Term k (n + 1)) (a : Term k n) :
    (t.instantiate a).wk ρ = (t.wk ρ.lift).instantiate (a.wk ρ) := by
  simp only [wk_eq_subst, subst_instantiate]
  congr 2
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Under a binder, a substitution moves a term moved past the bound variable as it moves the term. -/
theorem subst_lift_wk1 (σ : Subst k m n) (t : Term k n) : t.wk1.subst σ.lift = (t.subst σ).wk1 :=
  (subst_wk _ _ t).trans (wk_subst _ σ t).symm

/-- A substitution extended by a term leaves it unused in a term moved past its variable. -/
theorem subst_cons_wk1 (σ : Subst k m n) (a : Term k m) (t : Term k n) :
    t.wk1.subst (σ.cons a) = t.subst σ :=
  subst_wk _ _ t

/--
Inserting a variable before the innermost one, then replacing the innermost variable by the inserted
one, leaves the term unchanged.
-/
theorem instantiate_wk_lift_step (t : Term k (n + 1)) :
    (t.wk (Wk.step .id).lift).instantiate (var 0) = t := by
  rw [instantiate, wk_eq_subst, subst_subst]
  conv => rhs; rw [← subst_var t]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Instantiating a term substituted under a binder substitutes the instance for its variable. -/
theorem subst_lift_instantiate (σ : Subst k m n) (t : Term k (n + 1)) (a : Term k m) :
    (t.subst σ.lift).instantiate a = t.subst (σ.cons a) := by
  rw [instantiate, subst_subst]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => exact (subst_cons_wk1 _ _ _).trans (subst_var _)

/-- Under a binder, a weakening after a substitution weakens each substituted term. -/
theorem wk_lift_subst_lift (ρ : Wk m l) (σ : Subst k l n) (t : Term k (n + 1)) :
    (t.subst σ.lift).wk ρ.lift = t.subst (Subst.lift fun x => (σ x).wk ρ) := by
  rw [wk_subst]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => exact wk_lift_wk1 _ _

/-- Instantiating the levels commutes with a weakening. -/
theorem substLevels_wk (σ : Fin k → Level j) (ρ : Wk m n) (t : Term k n) :
    (t.wk ρ).substLevels σ = (t.substLevels σ).wk ρ := by
  induction t generalizing m with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB => simp only [wk, substLevels, ihA, ihB]
  | app _ _ _ iht iha => simp only [wk, substLevels, iht, iha]

/-- Instantiating the levels after a substitution also instantiates the substituted terms. -/
theorem substLevels_subst (θ : Fin k → Level j) (σ : Subst k m n) (t : Term k n) :
    (t.subst σ).substLevels θ = (t.substLevels θ).subst fun x => (σ x).substLevels θ := by
  induction t generalizing m with
  | var => rfl
  | univ => rfl
  | pi _ _ _ _ ihA ihB | lam _ _ _ ihA ihB =>
    have h : (fun x => (σ.lift x).substLevels θ) =
        Subst.lift fun x => (σ x).substLevels θ :=
      funext fun
        | ⟨0, _⟩ => rfl
        | ⟨_ + 1, _⟩ => substLevels_wk θ _ _
    simp only [subst, substLevels, ihA, ihB, h]
  | app _ _ _ iht iha => simp only [subst, substLevels, iht, iha]

end Term

end Sic.Core
