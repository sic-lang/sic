module

public import Sic.Core.Level
public import Sic.Grade

/-!
# Syntax

The terms of the core of RFC 24, so far its universes and its functions.
A variable is a de Bruijn index, as in the formalization of ADE: the number of binders between the
variable and its declaration, the innermost being `0`.
A term over `n` variables has the type `Term k n`, so that it can only use the variables in scope,
and its levels use the `k` level variables, the same throughout the term since no construct binds
them.
-/

@[expose] public section

namespace Sic.Core

/-- A term over `k` level variables and `n` variables. -/
inductive Term (k : Nat) : Nat → Type where
  /-- The variable of index `x`. -/
  | var (x : Fin n) : Term k n
  /-- `U_l`: the universe of level `l`. -/
  | univ (l : Level k) : Term k n
  /--
  `Π^q_p (x : A). B`: the type of the functions that use their argument with the grade `p`, and
  whose result `B` uses it with the grade `q`, in the order of ADE's `Π p , q ▷ A ▹ B`.
  -/
  | pi (p q : Grade) (A : Term k n) (B : Term k (n + 1)) : Term k n
  /-- `λ_p (x : A). t`: the function whose body `t` uses its argument with the grade `p`. -/
  | lam (p : Grade) (A : Term k n) (t : Term k (n + 1)) : Term k n
  /-- `t ∘_p a`: the application of `t` to the argument `a`, used with the grade `p`. -/
  | app (p : Grade) (t a : Term k n) : Term k n
  deriving DecidableEq

end Sic.Core
