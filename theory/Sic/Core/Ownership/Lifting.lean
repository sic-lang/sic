module

public import Sic.Core.Ownership
import Sic.Core.Lifting.Recursion

/-!
# Ownership of the Liftings

The ownership of the liftings of annex 13 of RFC 36: the judgment `⊢ Σ ◀` holds of a signature
followed by the lifting of a codata type without recursive destructor.
The judgment reads the recursive destructors of a block of codata types only, and such a lifting has
none: the result of each of its destructors is a motive, or an instance of the lifting of another
type.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- A signature whose entries have their ownerships, followed by the lifting of a codata type
without recursive destructor, has the ownerships of its entries.
RFC: `\mathsf{lift}_{◀}` -/
theorem OwnershipSig.lifting {sig : Signature} (hs : OwnershipSig sig) {decl : TypeDeclaration}
    {F : Name} {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hl : decl.Lifts sig F S body)
    (hF : ∀ ι, ∀ T ∈ decl.codataTypes, T.name = F →
      ∀ r ∈ (T.body ι).recursion decl.names, r = none) :
    OwnershipSig (.typeDeclaration (decl.lifting F S ns body) :: sig) := by
  refine .codata hs rfl fun ι T hT d p q ς ps Ξ Θ B ψ hpos hB => absurd ?_ hB
  cases List.mem_singleton.1 hT
  exact hl.blockName_pos ι (hF ι.lifted) hpos
