module

import Sic.Core.ContextConversion
import Sic.Core.Injectivity

/-!
# The Universes: Context Conversion

A declaration that is not the last one gets an equal type: in the context
`X : U_{l ⊔ l}, x : X`, the variable `x` has the type `X`, and keeps it once `X` is declared in
`U_l`, an equal universe.
The declarations must get equal types: `X : U_l` and `X : U_{l + 1}` are not equal contexts.
-/

namespace SicTest.Universe.ContextConversion

open Sic.Core Sic.Core.Term

/-- The context `X : U_{l ⊔ l}, x : X`. -/
abbrev Γ : Con 1 2 := .empty ∙ univ (.var 0 ⊔ .var 0) ∙ var 0

/-- The context `X : U_l, x : X`. -/
abbrev Δ : Con 1 2 := .empty ∙ univ (.var 0) ∙ var 0

theorem wfCon_Γ : ⊢ Γ := .snoc (.univ (.var (.snoc (.univ (.univ .empty)))))

/-- The two contexts are equal: their first declarations are equal universes. -/
theorem conEq : ⊢ Γ ≡ Δ :=
  .snoc (.snoc .empty (.univ (.univ .empty fun _ => Nat.max_self _)))
    (.refl (.univ (.var (.snoc (.univ (.univ .empty))))))

/-- In the context `X : U_l, x : X`, the variable `x` has the type `X`. -/
example : Δ ⊢ var 0 : var 1 := (HasType.var (x := 0) wfCon_Γ).conv_con conEq

/--
The contexts `X : U_l` and `X : U_{l + 1}` are not equal: `l` and `l + 1` differ when `l` is `0`.
-/
example : ¬ ⊢ (.empty ∙ univ (.var 0) : Con 1 1) ≡ .empty ∙ univ (.succ (.var 0)) := fun h => by
  cases h with
  | snoc _ hAB =>
    have ⟨_, e, hl⟩ := hAB.inv_univ .univ
    cases e; exact nomatch hl fun _ => 0

end SicTest.Universe.ContextConversion
