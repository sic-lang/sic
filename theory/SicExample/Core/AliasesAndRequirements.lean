module

public import Sic.Core.Ownership

/-!
# Aliases and Requirements

Examples of the ownership of the core, which RFC 36 will state with its examples: in a scope with a
variable `a`, the value of which has a given ownership, and three second-order variables, whose
signatures give the ownership of their results:

* `Id : (x : A ▶ 11ᵖ; 00ᵖ ◀ ωωᵖ ⊢ A ◀ x)`, whose result is its argument, has the coefficient `11ᵖ` and no
  constant, so that `Id[a]` has the ownership of `a`;
* `Choose : (x : A ▶ 11ᵖ; 00ᵖ ◀ ωωᵖ ⊢ A ◀ x ∧ 11ᵖ)`, whose result is its argument or a fresh value, has the coefficient
  `11ᵖ` and the constant `11ᵖ`, so that `Choose[a]` has the meet of the ownership of `a` and of
  `11ᵖ`;
* `Write : (x : A ▶ 11ᵖ; 00ᵖ ◀ 1ωᵖ ⊢ A ◀ 11ᵖ)`, which updates its argument in place and returns it as a fresh value,
  requires `1ωᵖ`, one path at run time and any number of paths in the proofs, has no coefficient
  and the constant `11ᵖ`, so that `Write[a]` is accepted at run time when `a` has no other path at
  run time, and refused when it may have several, while an erased occurrence, which is no path,
  requires nothing.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- The parameter of `Id` and of `Choose`: used once, without requirement, and whose argument the
result may be. -/
def aliasParameter : Parameter := ⟨.one, .unrestrictedUnrestricted, some .one⟩

/-- The parameter of `Write`: used once, with a single path at run time, and whose argument the
result is not. -/
def writeParameter : Parameter := ⟨.one, .linearUnrestricted, none⟩

/-- The scope `a, Choose, Write, Id`, the last entry first. -/
abbrev aliasScope : Scope :=
  [.secondOrder [aliasParameter] none, .secondOrder [writeParameter] (some .one),
    .secondOrder [aliasParameter] (some .one), .var]

/-- The variable `a`. -/
abbrev a : Var aliasScope .var := .succ (.succ (.succ .zero))

/-- The ownership `o` of `a`, the only variable of the scope. -/
def ownershipOfA (o : Grade) : Var aliasScope .var → Grade := fun _ => o

/-- `Id[a]`. -/
def idOfA : Term 0 aliasScope := .var (.zero : Var aliasScope (.secondOrder [aliasParameter] none))
  (.cons (.var₀ a) .nil)

/-- `Write[a]`. -/
def writeOfA : Term 0 aliasScope :=
  .var (.succ .zero : Var aliasScope (.secondOrder [writeParameter] (some .one)))
    (.cons (.var₀ a) .nil)

/-- `Choose[a]`. -/
def chooseOfA : Term 0 aliasScope :=
  .var (.succ (.succ .zero) : Var aliasScope (.secondOrder [aliasParameter] (some .one)))
    (.cons (.var₀ a) .nil)

/-- The ownership of `a` as the argument of a parameter. -/
theorem argument_a {sig : Signature} {m : Mode} {o : Grade} {p : Parameter}
    (hr : m ⊙ p.usage ≠ .zeroZero → p.requirement ≤ o) :
    OwnershipArgs sig (ownershipOfA o) m (.cons (.var₀ a) .nil : Args 0 aliasScope [p]) [o] :=
  .cons .var hr .nil

/-- `Id[a]` has the ownership `1ωᵖ` of `a`. -/
example : Ownership [] (ownershipOfA .linearUnrestricted) .oneOne .linearUnrestricted idOfA :=
  .secondOrder (argument_a (fun _ => by decide)) rfl

/-- `Choose[a]` has the ownership `1ωᵖ ⊓ 11ᵖ = 1ωᵖ` when `a` has the ownership `1ωᵖ`. -/
example : Ownership [] (ownershipOfA .linearUnrestricted) .oneOne .linearUnrestricted chooseOfA :=
  .secondOrder (argument_a (fun _ => by decide)) rfl

/-- `Choose[a]` has the ownership `ωωᵖ ⊓ 11ᵖ = ωωᵖ` when `a` has the ownership `ωωᵖ`. -/
example :
    Ownership [] (ownershipOfA .unrestrictedUnrestricted) .oneOne .unrestrictedUnrestricted
      chooseOfA :=
  .secondOrder (argument_a (fun _ => by decide)) rfl

/-- `Write[a]` is fresh at run time when `a` has a single path, `11ᵖ`. -/
example : Ownership [] (ownershipOfA .one) .oneOne .one writeOfA :=
  .secondOrder (argument_a (fun _ => by decide)) rfl

/-- `Write[a]` is fresh in an erased term whatever the ownership of `a`, since the requirement does
not apply in the mode `00ᵐ`. -/
example : Ownership [] (ownershipOfA .unrestrictedUnrestricted) .zeroZero .one writeOfA :=
  .secondOrder (argument_a (fun h => absurd rfl h)) rfl

/-- A derivation of the ownership of a variable gives it at most the ownership of its value. -/
theorem le_of_ownership_var {sig : Signature} {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {o : Grade} {x : Var Γ .var} :
    ∀ {t : Term k Γ}, Ownership sig φ m o t → t = .var₀ x → o ≤ φ x
  | _, .var, ht => by cases ht; exact Grade.le_refl _
  | _, .secondOrder _ _, ht => by cases ht
  | _, .const _, ht => by cases ht
  | _, .sort, ht => by cases ht
  | _, .sub h hle, ht => Grade.le_trans _ _ _ hle (le_of_ownership_var h ht)

/-- A derivation of an ownership of `Write[a]` at run time, when `a` may have several paths, `ωωᵖ`,
ends with the rule of the second-order variables, after uses of the rule `(sub)`, and its argument
has at most the ownership of `a`, which does not satisfy the requirement `1ωᵖ`. -/
theorem not_ownership_writeOfA_shared {φ : Var aliasScope .var → Grade} {m : Mode}
    (hφ : φ = ownershipOfA .unrestrictedUnrestricted) (hm : m = .oneOne) :
    ∀ {o : Grade} {t : Term 0 aliasScope}, Ownership [] φ m o t → t = writeOfA → False
  | _, _, .var, ht => by cases ht
  | _, _, .secondOrder (.cons ht' hr _) _, ht => by
    cases ht
    subst hφ hm
    exact absurd (Grade.le_trans _ _ _ (hr (by decide)) (le_of_ownership_var ht' rfl)) (by decide)
  | _, _, .const _, ht => by cases ht
  | _, _, .sort, ht => by cases ht
  | _, _, .sub h _, ht => not_ownership_writeOfA_shared hφ hm h ht

/-- `Write[a]` has no ownership at run time when `a` may have several paths, `ωωᵖ`. -/
theorem writeOfA_shared (o : Grade) :
    ¬ Ownership [] (ownershipOfA .unrestrictedUnrestricted) .oneOne o writeOfA :=
  fun h => not_ownership_writeOfA_shared rfl rfl h rfl

end SicExample.Core
