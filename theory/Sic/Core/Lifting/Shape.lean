module

public import Sic.Core.Lifting

/-!
# Shape of the Liftings

The parameters and the destructors that a lifting of annex 13 of RFC 36 keeps: the positions of
the arguments lifted of an instance are positions of its parameters, in order and distinct, with a
result each, and the destructors of a lifting are among those of the codata type that it lifts, in
their order.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Arguments That Are Lifted -/

/-- The positions of the arguments lifted are positions of the parameters. -/
theorem InstanceArgs.Lifts.lt {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} :
    {Δ : Scope} → {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} →
      {Δ' : Scope} → {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        ∀ i ∈ S, i < Δ.length
  | _, _, _, _, _, _, .nil, _, hi => nomatch hi
  | _, _, _, _, _, _, .lifted has _, i, hi => by
    rcases List.mem_append.1 hi with hi | hi
    · exact Nat.lt_succ_of_lt (has.lt i hi)
    · cases List.mem_singleton.1 hi
      exact Nat.lt_succ_self _
  | _, _, _, _, _, _, .absent has _ _, i, hi => Nat.lt_succ_of_lt (has.lt i hi)

/-- The arguments lifted have a result each. -/
theorem InstanceArgs.Lifts.length_eq {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} :
    {Δ : Scope} → {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} →
      {Δ' : Scope} → {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        ms.length = S.length
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, .lifted has _ => by
    rw [List.length_append, List.length_append, has.length_eq]
    rfl
  | _, _, _, _, _, _, .absent has _ _ => has.length_eq

/-- The positions of the arguments lifted are distinct. -/
theorem InstanceArgs.Lifts.nodup {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} :
    {Δ : Scope} → {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} →
      {Δ' : Scope} → {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        S.Nodup
  | _, _, _, _, _, _, .nil => List.nodup_nil
  | _, _, _, _, _, _, .lifted has _ =>
    List.nodup_append.2 ⟨has.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun i hi j hj he => by
        cases List.mem_singleton.1 hj
        exact Nat.lt_irrefl _ (he ▸ has.lt i hi)⟩
  | _, _, _, _, _, _, .absent has _ _ => has.nodup

/-! ## Destructors That Are Lifted -/

/-- The destructors lifted are among the destructors that are lifted, in their order. -/
theorem Destructors.Lifts.sublist {Γ₀ : Scope} {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)} :
    {Γ' : Scope} → {ρ : Lifting k Γ' Γ₀} → {Ξ : Scope} → {θ : Subst k Γ₀ Ξ} → {ns : List Name} →
      {ds : Destructors k Ξ ns} → {ns' : List Name} → {ds' : Destructors k Γ' ns'} →
      Destructors.Lifts sig v κ o ρ @θ ds ds' → ns'.Sublist ns
  | _, _, _, _, _, _, _, _, .nil => .slnil
  | _, _, _, _, _, _, _, _, .lifted _ _ h => (Destructors.Lifts.sublist h).cons_cons _
  | _, _, _, _, _, _, _, _, .absent _ h => (Destructors.Lifts.sublist h).cons _

end Sic.Core
