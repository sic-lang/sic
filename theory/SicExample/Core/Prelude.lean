module

public import Sic.Core.Prelude

/-!
# Packing a Telescope

The packing of annex 17 of RFC 36 on a telescope of two entries, a type and a term of it,
`(X : U_0 ▶ 00ᵖ; ωωᵖ ◀ ωωᵖ, x : X ▶ 11ᵖ; 00ᵖ ◀ 11ᵖ)`, whose entries live in `U_1` and `U_0`, packed
in `U_0`: the nested pairs of its entries, which end with the unit, at the levels that the sorts of
the entries give; and the packing of its arguments `(Unit, mk)`.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- The telescope `(X : U_0 ▶ 00ᵖ; ωωᵖ ◀ ωωᵖ, x : X ▶ 11ᵖ; 00ᵖ ◀ 11ᵖ)`. -/
def typeAndTerm : Telescope 0 []
    [⟨Grade.zero, .unrestrictedUnrestricted⟩, ⟨Grade.one, Grade.one⟩] :=
  .cons .unrestrictedUnrestricted ⟨Grade.zero, .unrestrictedUnrestricted⟩ (.sort ⟨.type, .zero⟩)
    (.cons Grade.zero ⟨Grade.one, Grade.one⟩ (.var₀ .zero) .nil)

/-- The sorts of its entries, `U_1` and `U_0`. -/
def typeAndTermSorts : List (Universe 0) := [⟨.type, .succ .zero⟩, ⟨.type, .zero⟩]

/-- The packing is a pair of the type, with its grades, and of a pair of the term and of the unit. -/
example : typeAndTerm.pack typeAndTermSorts .zero =
    .inst "Pair" [.type] [.succ .zero, .max .zero .zero] [Grade.zero, .unrestrictedUnrestricted]
      (Prelude.pairArgs (.sort ⟨.type, .zero⟩)
        (.inst "Pair" [.type] [.zero, .zero] [Grade.one, Grade.one]
          (Prelude.pairArgs (.var₀ .zero) (.inst "Unit" [] [.zero] [] .nil)))) := rfl

/-- The packing of the arguments `(Unit, mk)` nests the pairs of the packing, each at the rest of
the telescope instantiated by the arguments before it. -/
example (A : Term 0 []) (t : Term 0 []) :
    (Args.cons (p := ⟨Grade.zero, .unrestrictedUnrestricted⟩) A
      (.cons (p := ⟨Grade.one, Grade.one⟩) t .nil)).pack typeAndTerm typeAndTermSorts .zero =
    .ctor "Pair" [.type] [.succ .zero, .max .zero .zero] [Grade.zero, .unrestrictedUnrestricted]
      (Prelude.pairArgs (.sort ⟨.type, .zero⟩)
        (.inst "Pair" [.type] [.zero, .zero] [Grade.one, Grade.one]
          (Prelude.pairArgs (.var₀ .zero) (.inst "Unit" [] [.zero] [] .nil)))) "mk"
      (.cons A (.cons (.ctor "Pair" [.type] [.zero, .zero] [Grade.one, Grade.one]
        (Prelude.pairArgs A (.inst "Unit" [] [.zero] [] .nil)) "mk"
        (.cons t (.cons (.ctor "Unit" [] [.zero] [] .nil "mk" .nil) .nil))) .nil)) := rfl

end SicExample.Core
