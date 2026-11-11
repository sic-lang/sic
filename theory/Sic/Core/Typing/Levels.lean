module

public import Sic.Core.Typing

/-!
# Instantiation of the Levels in the Contexts

The entries of the contexts of annex 14 of RFC 36 under the instantiation `[l̄' / l̄]` of the level
variables: a variable declared in a context is declared, with its type instantiated, in the context
instantiated.

ADE have no level variables.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Instantiation of the Level Variables -/

/-- A variable declared in a context is declared, with its type instantiated, in the context
instantiated. -/
theorem Context.VarIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {x : Var Γ .var} {A : Term k Γ} :
    ctx.VarIn x A → (ctx.substLevels ls').VarIn x (A.substLevels ls')
  | .zero => by rw [Term.substLevels_rename]; exact .zero
  | .succVar h => by rw [Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by rw [Term.substLevels_rename]; exact .succSecondOrder (h.substLevels ls')

/-- A second-order variable declared in a context is declared, with its telescope and its type
instantiated, in the context instantiated. -/
theorem Context.SecondOrderIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)}
    {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
    ctx.SecondOrderIn X Θ A →
      (ctx.substLevels ls').SecondOrderIn X (Θ.substLevels ls') (A.substLevels ls')
  | .zero => by rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .zero
  | .succVar h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]
    exact .succSecondOrder (h.substLevels ls')

end Sic.Core
