module

import Sic.Core.Syntax

/-!
# A Permission Used Once

The example of RFC 24 of a permission used once, written as terms of `Sic.Core.Syntax`.
-/

namespace SicTest.Permission.Syntax

open Sic Sic.Core Sic.Grade Sic.Core.Term

/-- `⟨0, 1⟩`, the grade `none / linear` of a permission: used once, never at run time. -/
def permission : Grade := ⟨.zero, .one, by decide⟩

/-!
The context `Perm : U₀, B : U₀, b : B, close : Π^𝟘_⟨0, 1⟩ (x : Perm). B,
commit : Π^𝟘_⟨0, 1⟩ (x : Perm). Π^𝟘_𝟙 (y : B). B` declares the type of the permissions, a type of
results with one of its terms, and two operations that consume a permission, as in RFC 24.
-/

/-- The type `Π^𝟘_⟨0, 1⟩ (x : Perm). B` of `close`, after `Perm`, `B` and `b`. -/
def closeType : Term 0 3 := pi permission 𝟘 (var 2) (var 2)

/--
The type `Π^𝟘_⟨0, 1⟩ (x : Perm). Π^𝟘_𝟙 (y : B). B` of `commit`, after `Perm`, `B`, `b` and
`close`.
-/
def commitType : Term 0 4 := pi permission 𝟘 (var 3) (pi 𝟙 𝟘 (var 3) (var 4))

/-- The type `Π^𝟘_⟨0, 1⟩ (x : Perm). B` of the functions that receive a permission. -/
def consumerType : Term 0 5 := pi permission 𝟘 (var 4) (var 4)

/-- `λ_⟨0, 1⟩ (x : Perm). close ∘_⟨0, 1⟩ x`, which passes the permission on once. -/
def once : Term 0 5 := lam permission (var 4) (app permission (var 2) (var 0))

/--
`λ_⟨0, 1⟩ (x : Perm). (commit ∘_⟨0, 1⟩ x) ∘_𝟙 (close ∘_⟨0, 1⟩ x)`, which passes the permission to both
operations.
-/
def twice : Term 0 5 :=
  lam permission (var 4) (app 𝟙 (app permission (var 1) (var 0)) (app permission (var 2) (var 0)))

/-- `λ_⟨0, 1⟩ (x : Perm). b`, which drops the permission. -/
def dropped : Term 0 5 := lam permission (var 4) (var 3)

end SicTest.Permission.Syntax
