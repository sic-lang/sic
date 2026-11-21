module

public import Sic.Core.Typing

/-!
# Reflexivity

The reflexivity of the equality of the arguments of an instance of annex 15 of RFC 36, which no rule
gives: arguments of an instance are equal to themselves, as the reflexivity of the equality of the
terms and of the types gives each of them.

ADE have no instances.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Arguments of Instances -/

-- ADE: none.
/-- Arguments of an instance are equal to themselves. -/
theorem EqInstanceArgs.refl {Γ Δ : Scope} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {params : Context k Δ} (h : HasInstanceArgs sig ctx as params) :
    EqInstanceArgs sig ctx as as params :=
  match Δ, as, params, h with
  | _, _, _, .nil hctx => .nil hctx
  | _, _, _, .var has ha => .var (EqInstanceArgs.refl has) (.refl ha)
  | _, _, _, .secondOrder has hB => .secondOrder (EqInstanceArgs.refl has) (.refl hB)

end Sic.Core
