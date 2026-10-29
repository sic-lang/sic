module

/-!
# Levels

The levels of RFC 24, the subscripts of the universes, over `k` level variables: the parameters of
a top-level definition, which no construct of the core binds.
Two levels are equal when they are equal whatever levels their variables take, so that a definition
checked once with its level variables holds at each of its uses, as `Equiv.subst` shows.
-/

@[expose] public section

namespace Sic

/-- The join, written as in Mathlib, on which this package does not depend. -/
infixl:68 " ⊔ " => max

namespace Core

/-- A level over `k` variables. -/
inductive Level (k : Nat) where
  /-- The level `0`. -/
  | zero
  /-- `l + 1`: the successor of the level `l`. -/
  | succ (l : Level k)
  /-- `l₁ ⊔ l₂`: the larger of two levels. -/
  | max (l₁ l₂ : Level k)
  /-- The level variable of index `i`. -/
  | var (i : Fin k)
  deriving DecidableEq

namespace Level

variable {j k : Nat}

/-- `l₁ ⊔ l₂`: the larger of two levels. -/
instance : Max (Level k) := ⟨max⟩

/-- The value of a level when its variables take the values `ρ`. -/
def eval (ρ : Fin k → Nat) : Level k → Nat
  | zero => 0
  | succ l => eval ρ l + 1
  | max l₁ l₂ => eval ρ l₁ ⊔ eval ρ l₂
  | var i => ρ i

theorem eval_max (ρ : Fin k → Nat) (l₁ l₂ : Level k) :
    eval ρ (l₁ ⊔ l₂) = eval ρ l₁ ⊔ eval ρ l₂ := rfl

/-- Two levels are equal when they are equal whatever levels their variables take. -/
def Equiv (l₁ l₂ : Level k) : Prop := ∀ ρ, eval ρ l₁ = eval ρ l₂

instance : HasEquiv (Level k) := ⟨Equiv⟩

/-- The level `l` whose variables are replaced by the levels `σ`, over `j` other variables. -/
def subst (σ : Fin k → Level j) : Level k → Level j
  | zero => zero
  | succ l => succ (subst σ l)
  | max l₁ l₂ => max (subst σ l₁) (subst σ l₂)
  | var i => σ i

/-!
The equality of levels is an equivalence, which the successor and instantiating the variables
preserve.
-/

section Equiv

variable {l₁ l₂ l₃ : Level k}

theorem Equiv.refl (l : Level k) : l ≈ l := fun _ => rfl
theorem Equiv.symm (h : l₁ ≈ l₂) : l₂ ≈ l₁ := fun ρ => (h ρ).symm
theorem Equiv.trans (h₁ : l₁ ≈ l₂) (h₂ : l₂ ≈ l₃) : l₁ ≈ l₃ := fun ρ => (h₁ ρ).trans (h₂ ρ)
theorem Equiv.succ (h : l₁ ≈ l₂) : l₁.succ ≈ l₂.succ := fun ρ => congrArg (· + 1) (h ρ)

theorem eval_subst (σ : Fin k → Level j) (ρ : Fin j → Nat) (l : Level k) :
    eval ρ (subst σ l) = eval (fun i => eval ρ (σ i)) l := by
  induction l <;> simp_all [eval, subst]

theorem Equiv.subst (σ : Fin k → Level j) (h : l₁ ≈ l₂) : subst σ l₁ ≈ subst σ l₂ := fun ρ => by
  rw [eval_subst, eval_subst]
  exact h _

end Equiv

end Level

end Core

end Sic
