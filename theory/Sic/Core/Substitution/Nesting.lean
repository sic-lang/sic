module

public import Sic.Core.Nesting
public import Sic.Core.Substitution

/-!
# Nesting of the Renamed Types

A renaming keeps the nesting of a type of annex 14 of RFC 36, at the nestings of the variables that
it renames, and so the nestings of the fields of a block, whose variables have no position: the
fields after a recursive field, which do not depend on it, are renamed under it.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α : Type}

/-- The nestings of the variables that a renaming renames stay theirs under a new entry. -/
theorem Nesting.lift_rename {Γ Δ : Scope} {e₀ : Scope.Entry} {ρ : Ren Γ Δ} {ν : Nesting α Δ}
    {ν' : Nesting α Γ} (h : ∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Δ) e), Nesting.lift @ν' (Ren.lift @ρ x) = Nesting.lift @ν x :=
  fun _ x =>
    match x with
    | .zero => rfl
    | .succ x => h _ x

/-- The nestings of the variables that a renaming renames stay theirs under new variables. -/
theorem Nesting.liftN_rename :
    {Γ Δ : Scope} → (n : Nat) → {ρ : Ren Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) →
      ∀ (e : Scope.Entry) (x : Var (Δ.extend n) e),
        Nesting.liftN n @ν' (Ren.liftN n @ρ x) = Nesting.liftN n @ν x
  | _, _, 0, _, _, _, h => h
  | _, _, n + 1, _, _, _, h => Nesting.liftN_rename n (Nesting.lift_rename h)

mutual

/-- A renamed type has the nesting of the type, at the nestings of the variables renamed. -/
theorem Term.nest_rename (mark : Name → Option α) :
    {Γ Δ : Scope} → (ρ : Ren Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) → (A : Term k Δ) →
      (A.rename ρ).nest mark @ν' = A.nest mark @ν
  | _, _, _, _, _, h, .var x _ => h _ x
  | _, _, ρ, _, _, h, .inst _ _ _ _ as => by
    rw [Term.rename, Term.nest, Term.nest, InstanceArgs.nest_rename mark ρ h as]
  | _, _, _, _, _, _, .sort _ => rfl
  | _, _, _, _, _, _, .const _ _ _ _ => rfl
  | _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => rfl

/-- Renamed arguments of an instance have the nestings of the arguments, at the nestings of the
variables renamed. -/
theorem InstanceArgs.nest_rename (mark : Name → Option α) :
    {Γ Δ Ξ : Scope} → (ρ : Ren Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) → (as : InstanceArgs k Δ Ξ) →
      (as.rename ρ).nest mark @ν' = as.nest mark @ν
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, ρ, _, _, h, .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.nest, InstanceArgs.nest,
      Term.nest_rename mark (Ren.liftN _ ρ) (Nesting.liftN_rename _ h) B,
      InstanceArgs.nest_rename mark ρ h as]

end

/-- A renamed type of a field has the nesting of the type. -/
theorem Term.blockNest_rename {Γ Δ : Scope} (names : List Name) (ρ : Ren Γ Δ) (A : Term k Δ) :
    (A.rename ρ).blockNest names = A.blockNest names :=
  Term.nest_rename _ ρ (fun _ _ => rfl) A

/-- A renamed telescope has the nestings of the telescope. -/
theorem Telescope.nest_rename {Γ Δ : Scope} (names : List Name) :
    {ps : List Parameter} → (ρ : Ren Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.rename ρ).nest names = Θ.nest names
  | [], _, .nil => rfl
  | _ :: _, ρ, .cons _ _ A Θ => by
    rw [Telescope.rename, Telescope.nest, Telescope.nest, Term.blockNest_rename,
      Telescope.nest_rename names (Ren.lift ρ) Θ]

end Sic.Core
