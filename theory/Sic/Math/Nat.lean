module

/-!
# Natural Numbers

Properties of the natural numbers that Lean does not provide: a fact of every number restricted to
the numbers below a bound, as the recursions on a number read the facts of the numbers below it.

ADE have no counterpart of this restriction.
-/

@[expose] public section

/-- A fact of every number holds of the numbers below `n`. -/
theorem Nat.forall_lt {P : Nat → Prop} (h : ∀ m, P m) (n : Nat) : ∀ m, m < n → P m :=
  fun m _ => h m
