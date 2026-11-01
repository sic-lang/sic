module

public import Sic.Core.Typing
public import SicTest.Permission.Syntax

/-!
# A Permission Used Once: Typing

The three functions that receive a permission are well typed, as derivations: typing does not count
the uses of the permission, which only the usage rejects.
-/

@[expose] public section

namespace SicTest.Permission.Typing

open Sic.Core Sic.Grade Sic.Core.Term SicTest.Permission.Syntax

/-- The context `Perm : U₀, B : U₀, b : B` of the type of results. -/
def Γ₃ : Con 0 3 := .empty ∙ univ .zero ∙ univ .zero ∙ var 0

/-- The context of the example, `Γ₃` extended by the operations `close` and `commit`. -/
def Γ₅ : Con 0 5 := Γ₃ ∙ closeType ∙ commitType

theorem wfCon_Γ₃ : ⊢ Γ₃ :=
  have hB : Con.empty ∙ univ .zero ⊢ univ .zero : univ (.succ .zero) :=
    .univ (.snoc (.univ (.univ .empty)))
  .snoc (.univ (.var (.snoc (.univ hB))))

theorem hasType_closeType : Γ₃ ⊢ closeType : univ (.zero ⊔ .zero) :=
  have hPerm : Γ₃ ⊢ var 2 : univ .zero := .var wfCon_Γ₃
  .pi hPerm (.var (.snoc (.univ hPerm)))

theorem hasType_commitType : Γ₃ ∙ closeType ⊢ commitType : univ (.zero ⊔ (.zero ⊔ .zero)) :=
  -- `Perm` after `close`, `B` after `x`, and `B` after `y`.
  have hPerm : Γ₃ ∙ closeType ⊢ var 3 : univ .zero := .var (.snoc (.univ hasType_closeType))
  have hB : Γ₃ ∙ closeType ∙ var 3 ⊢ var 3 : univ .zero := .var (.snoc (.univ hPerm))
  .pi hPerm (.pi hB (.var (.snoc (.univ hB))))

theorem wfCon_Γ₅ : ⊢ Γ₅ := .snoc (.univ hasType_commitType)

theorem isType_consumerType : Γ₅ ⊢ consumerType :=
  have hPerm : Γ₅ ⊢ var 4 : univ .zero := .var wfCon_Γ₅
  .univ (.pi hPerm (.var (.snoc (.univ hPerm))))

/-- The context of the bodies, `Γ₅` extended by the permission `x : Perm`. -/
theorem wfCon_Γ₅_x : ⊢ Γ₅ ∙ var 4 :=
  .snoc (.univ (.var wfCon_Γ₅))

/-- The operations `close` and `commit` and the permission `x`, with their types after `x`. -/
theorem hasType_close : Γ₅ ∙ var 4 ⊢ var 2 : pi permission 𝟘 (var 5) (var 5) := .var wfCon_Γ₅_x

theorem hasType_commit : Γ₅ ∙ var 4 ⊢ var 1 : pi permission 𝟘 (var 5) (pi 𝟙 𝟘 (var 5) (var 6)) :=
  .var wfCon_Γ₅_x

theorem hasType_x : Γ₅ ∙ var 4 ⊢ var 0 : var 5 := .var wfCon_Γ₅_x

/-- The function that passes the permission on once is well typed. -/
theorem hasType_once : Γ₅ ⊢ once : consumerType :=
  .lam isType_consumerType (.app hasType_close hasType_x)

/-- The function that passes the permission to both operations is well typed. -/
theorem hasType_twice : Γ₅ ⊢ twice : consumerType :=
  .lam isType_consumerType (.app (.app hasType_commit hasType_x) (.app hasType_close hasType_x))

/-- The function that drops the permission is well typed. -/
theorem hasType_dropped : Γ₅ ⊢ dropped : consumerType :=
  .lam isType_consumerType (.var wfCon_Γ₅_x)

end SicTest.Permission.Typing
