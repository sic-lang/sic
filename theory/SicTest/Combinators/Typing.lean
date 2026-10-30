module

import Sic.Core.Typing
import all SicTest.Combinators.Syntax

/-!
# The Combinators K and S: Typing

The types of `K` and `S`, as derivations, and the type of the identity for `S K K`.
-/

namespace SicTest.Combinators.Typing

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Combinators.Syntax

/--
`K` has its type `Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, in
every well-formed context, since it is closed.
-/
theorem hasType_combinatorK (h : ⊢ Γ) : Γ ⊢ combinatorK : combinatorKType :=
  -- `U_l` in `Γ` and after `A`, `A` after `B`, `B` after `x`, and `A` after `y`.
  have hU : Γ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ h
  have hU' : Γ ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ (.snoc hU)
  have hA : Γ ∙ univ (.var 0) ∙ univ (.var 0) ⊢ var 1 : univ (.var 0) := .var (.snoc hU')
  have hB : Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hA' : Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ∙ var 1 ⊢ var 3 : univ (.var 0) :=
    .var (.snoc hB)
  have hy := HasType.pi hB hA'
  have hx := HasType.pi hA hy
  have hB' := HasType.pi hU' hx
  .lam (.pi hU hB') (.lam hB' (.lam hx (.lam hy (.var (.snoc hB)))))

/-- The context `A : U_l, B : U_l, C : U_l` of the bound types of `S`, after `Γ`. -/
def ΓS (Γ : Con 1 n) : Con 1 (n + 3) := Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ univ (.var 0)

theorem wfCon_ΓS (h : ⊢ Γ) : ⊢ ΓS Γ := .snoc (.univ (.snoc (.univ (.snoc (.univ h)))))

/-- The type `Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C` of `x`. -/
theorem hasType_combinatorS_x (h : ⊢ Γ) :
    ΓS Γ ⊢ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) : univ (.var 0 ⊔ (.var 0 ⊔ .var 0)) :=
  have hA : ΓS Γ ⊢ var 2 : univ (.var 0) := .var (wfCon_ΓS h)
  have hB : ΓS Γ ∙ var 2 ⊢ var 2 : univ (.var 0) := .var (.snoc hA)
  .pi hA (.pi hB (.var (.snoc hB)))

/-- The type `Π^𝟘_𝟙 (a : A). B` of `y`, after `x`. -/
theorem hasType_combinatorS_y (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ⊢ pi 𝟙 𝟘 (var 3) (var 3) :
      univ (.var 0 ⊔ .var 0) :=
  have hA : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ⊢ var 3 : univ (.var 0) :=
    .var (.snoc (hasType_combinatorS_x h))
  .pi hA (.var (.snoc hA))

/-- The type `A` of `z`, after `x` and `y`. -/
theorem hasType_combinatorS_z (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ⊢ var 4 :
      univ (.var 0) :=
  .var (.snoc (hasType_combinatorS_y h))

/--
The body `(x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)` of `S` has the type `C`: `x ∘_𝟙 z` is a function of `B`, of
which `y ∘_𝟙 z` is a term.
-/
theorem hasType_combinatorS_body (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      app 𝟘 (app 𝟙 (var 2) (var 0)) (app 𝟙 (var 1) (var 0)) : var 3 :=
  have h' := WfCon.snoc (hasType_combinatorS_z h)
  have hx : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 2 : pi 𝟙 𝟘 (var 5) (pi 𝟘 𝟘 (var 5) (var 5)) := .var h'
  have hy : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 1 : pi 𝟙 𝟘 (var 5) (var 5) := .var h'
  have hz : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 0 : var 5 := .var h'
  .app (.app hx hz) (.app hy hz)

/-- `S` has its type, in every well-formed context. -/
theorem hasType_combinatorS (h : ⊢ Γ) : Γ ⊢ combinatorS : combinatorSType :=
  have hU : Γ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ h
  have hU' : Γ ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ (.snoc hU)
  have hU'' : Γ ∙ univ (.var 0) ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) :=
    .univ (.snoc hU')
  have hz := HasType.pi (hasType_combinatorS_z h) (.var (.snoc (hasType_combinatorS_z h)))
  have hy := HasType.pi (hasType_combinatorS_y h) hz
  have hx := HasType.pi (hasType_combinatorS_x h) hy
  have hC := HasType.pi hU'' hx
  have hB := HasType.pi hU' hC
  .lam (.pi hU hB) (.lam hB (.lam hC (.lam hx (.lam hy (.lam hz (hasType_combinatorS_body h))))))

/-- The context `A : U_l` in which `S K K` is the identity of `A`. -/
def ΓA : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_ΓA : ⊢ ΓA := .snoc (.univ .empty)

/-- The type variable `A`. -/
theorem hasType_ΓA_var : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA

/--
`B = Π^𝟘_𝟘 (y : A). A`, the type of the argument that the first `K` discards, a type of `U_l` since
`l ⊔ l` equals `l`.
-/
def skkB : Term 1 1 := pi 𝟘 𝟘 (var 0) (var 1)

theorem hasType_skkB : ΓA ⊢ skkB : univ (.var 0) :=
  .conv (.pi hasType_ΓA_var (.var (.snoc hasType_ΓA_var)))
    (.univ wfCon_ΓA fun _ => Nat.max_self _)

/-- `K ∘_𝟘 A ∘_𝟘 B`, of the type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of `x` in `S`. -/
def skkX : Term 1 1 := app 𝟘 (app 𝟘 combinatorK (var 0)) skkB

/-- `K ∘_𝟘 A ∘_𝟘 A`, of the type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : A). A`, which is `Π^𝟘_𝟙 (a : A). B`. -/
def skkY : Term 1 1 := app 𝟘 (app 𝟘 combinatorK (var 0)) (var 0)

/-- `S ∘_𝟘 A ∘_𝟘 B ∘_𝟘 A ∘_𝟙 (K ∘_𝟘 A ∘_𝟘 B) ∘_𝟘 (K ∘_𝟘 A ∘_𝟘 A)`, the `S K K` of `A`. -/
def skk : Term 1 1 :=
  app 𝟘 (app 𝟙 (app 𝟘 (app 𝟘 (app 𝟘 combinatorS (var 0)) skkB) (var 0)) skkX) skkY

theorem hasType_skkX : ΓA ⊢ skkX : pi 𝟙 𝟘 (var 0) (pi 𝟘 𝟘 skkB.wk1 (var 2)) :=
  .app (.app (hasType_combinatorK wfCon_ΓA)
    hasType_ΓA_var) hasType_skkB

theorem hasType_skkY : ΓA ⊢ skkY : pi 𝟙 𝟘 (var 0) skkB.wk1 :=
  .app (.app (hasType_combinatorK wfCon_ΓA)
    hasType_ΓA_var) hasType_ΓA_var

/-- `S K K` has the type `Π^𝟘_𝟙 (z : A). A` of the identity of `A`. -/
theorem hasType_skk : ΓA ⊢ skk : pi 𝟙 𝟘 (var 0) (var 1) :=
  .app (.app (.app (.app (.app (hasType_combinatorS wfCon_ΓA) hasType_ΓA_var) hasType_skkB)
    hasType_ΓA_var) hasType_skkX) hasType_skkY

end SicTest.Combinators.Typing
