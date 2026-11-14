module

public import Sic.Core.Ownership

/-!
# Ownership of a Signature

The judgment `⊢ Σ ◀` of annex 13 of RFC 36 holds of each declaration of the signature: the
ownership of the result of each recursive destructor of a block of codata types of the signature is
a constant, at each instance, which the erasure keeps, so that the ownership of the target language
reads it in the branches of the corecursors.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- In a signature whose entries have their ownerships, the ownership of the result of each
recursive destructor of a block of codata types is a constant, at each instance. -/
theorem OwnershipSig.recursiveResult {sig : Signature} (hs : OwnershipSig sig)
    {decl : TypeDeclaration} (hm : .typeDeclaration decl ∈ sig)
    (ι : Instance decl.sorts decl.grades)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    {d : Name} {p q ς : Grade} {ps : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps} {B : Term decl.levels (Ξ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} (hpos : (T.body ι).Pos d p q ς Ξ Θ B ψ)
    (hB : B.blockName decl.names ≠ none) : ∃ χ, ψ = ⟨some χ, fun _ => none⟩ := by
  induction hs with
  | empty => nomatch hm
  | constantDefinition _ _ ih =>
    rcases List.mem_cons.1 hm with h | h
    · nomatch h
    · exact ih h
  | constantDeclaration _ ih =>
    rcases List.mem_cons.1 hm with h | h
    · nomatch h
    · exact ih h
  | data _ hb ih =>
    rcases List.mem_cons.1 hm with h | h
    · cases h
      simp [TypeDeclaration.codataTypes, hb] at hT
    · exact ih h
  | codata _ _ hψ ih =>
    rcases List.mem_cons.1 hm with h | h
    · cases h
      obtain ⟨χ, hχ, -⟩ := hψ ι T hT d p q ς ps Ξ Θ B ψ hpos hB
      exact ⟨χ, hχ⟩
    · exact ih h

end Sic.Core
