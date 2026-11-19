module

public import Sic.Core.Ownership
import Sic.Core.Shape.Results.Extension
import Sic.Core.Syntax.Signature

/-!
# Ownership of a Signature

The judgment `⊢ Σ ◀` of annex 18 of RFC 36 holds of each declaration of the signature: the
ownership of the result of each recursive destructor of a block of codata types of the signature is
a constant, at each instance, which the erasure keeps, so that the ownership of the target language
reads it in the branches of the corecursors.

The judgments of ownership hold in every signature that has more entries before theirs, all of
distinct names: the ownership reads its signature by the entries that it has, the constants, the
data types and the codata types, and by the shapes of the nested fields, which the requirement `r̂`
of the recursion of a recursor reads, so that such a signature gives the same premises.
The judgment `⊢ Σ ◀` checks the body of each constant definition in the signature before it, while
the program of a signature erases it in the whole signature, which has more entries.
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.

ADE have no signatures, and no ownership.
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

-- ADE: none.
/-- The judgments of ownership hold in every signature that has more entries before theirs, all of
distinct names: the requirement `r̂` of the recursion of a recursor reads the shapes of the nested
fields of its block, which such a signature keeps. -/
structure OwnershipStableUnderExtension : Prop where
  /-- The value of a term has the same ownership in a signature that has more entries before
  theirs, all of distinct names.
  RFC: `\mathsf{ext}_{◀}.t` -/
  ownership : ∀ {sig pre : Signature} {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode}
    {p : Grade} {t : Term k Γ}, (pre ++ sig).Distinct → Ownership sig φ m p t →
      Ownership (pre ++ sig) φ m p t
  /-- Arguments of a telescope have the same ownerships in a signature that has more entries
  before theirs, all of distinct names.
  RFC: `\mathsf{ext}_{◀}.\bar t` -/
  ownershipArgs : ∀ {sig pre : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {φ : Var Γ .var → Grade} {m : Mode} {ts : Args k Γ ps} {os : List Grade},
    (pre ++ sig).Distinct → OwnershipArgs sig φ m ts os → OwnershipArgs (pre ++ sig) φ m ts os

-- ADE: none.
/-- The judgments of ownership hold in every signature that has more entries before theirs, all of
distinct names, since the requirement `r̂` of the recursion reads the shapes, which such a
signature keeps.
RFC: `\mathsf{ext}_{◀}.t`
RFC: `\mathsf{ext}_{◀}.\bar t` -/
theorem ownershipStableUnderExtension : OwnershipStableUnderExtension :=
  ⟨ownership, ownershipArgs⟩
where
  ownership {sig pre : Signature} {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode}
      {p : Grade} {t : Term k Γ} (hds : (pre ++ sig).Distinct) :
      Ownership sig φ m p t → Ownership (pre ++ sig) φ m p t
    | .var => .var
    | .secondOrder hts hp hf => .secondOrder (ownershipArgs hds hts) hp hf
    | .const h => .const (h.mono fun _ h => List.mem_append_right pre h)
    | .sort => .sort
    | .inst => .inst
    | .ctor h hc hq hp hts =>
      .ctor ⟨List.mem_append_right pre h.1, h.2⟩ hc hq hp (ownershipArgs hds hts)
    | .recursor h hq hp ht hns hul hus hu hu' hmeets hused =>
      .recursor ⟨List.mem_append_right pre h.1, h.2⟩ hq hp (ownership hds ht)
        (hns.append hds h.1) hul hus
        (fun i j T' con u hi hget => by
          rw [TypeDeclaration.recursionRequirement_append hds h.1 hns]
          exact ownership hds (hu i j T' con u hi hget))
        (fun hN i j T' con u hi hget => by
          rw [TypeDeclaration.recursionRequirement_append hds h.1 hns]
          exact ownership hds (hu' hN i j T' con u hi hget))
        (fun i j T' con hi ax hxs l σ hσ => by
          rw [TypeDeclaration.recursionRequirement_append hds h.1 hns]
          rw [Constructor.nestedShapes_append hds h.1 _ _ _ (hns i j T' con hi ax hxs)] at hσ
          exact hmeets i j T' con hi ax hxs l σ hσ)
        (fun i j T' con hi l σ p' hσ hp' => by
          rw [Constructor.nestedShapes_append hds h.1 _ _ _
            (hns i j T' con hi Grade.run List.mem_cons_self)] at hσ
          exact hused i j T' con hi l σ p' hσ hp')
    | .obs h hq hp hd ht hbs hv hf hς =>
      .obs ⟨List.mem_append_right pre h.1, h.2⟩ hq hp hd (ownership hds ht) (ownershipArgs hds hbs)
        hv hf hς
    | .corec h hq hp hh hS hss hSl hSs hgl hgs hgo hgr =>
      .corec ⟨List.mem_append_right pre h.1, h.2⟩ hq hp hh hS (ownershipArgs hds hss) hSl hSs hgl
        hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hB os' v hA hv =>
          ownership hds (hgo i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hB os' v hA hv))
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g D' hi hS' hd hg hB os' hA =>
          ownership hds (hgr i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g D' hi hS' hd hg hB os' hA))
    | .sub h hle => .sub (ownership hds h) hle
  ownershipArgs {sig pre : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {φ : Var Γ .var → Grade} {m : Mode} {ts : Args k Γ ps} {os : List Grade}
      (hds : (pre ++ sig).Distinct) :
      OwnershipArgs sig φ m ts os → OwnershipArgs (pre ++ sig) φ m ts os
    | .nil => .nil
    | .cons ht hr hts => .cons (ownership hds ht) hr (ownershipArgs hds hts)

/-- The value of the body of each constant definition of a signature whose names are distinct and
whose entries have their ownerships has the ownership of the definition, in its mode, without
variable, in the whole signature, which has the entries of the signature before it. -/
theorem OwnershipSig.constantDefinition_ownership {sig : Signature} (hs : OwnershipSig sig)
    (hds : sig.Distinct) {d : ConstantDefinition} (hd : .constantDefinition d ∈ sig)
    (ι : Instance d.sorts d.grades) :
    Ownership sig (fun x : Var [] .var => nomatch x) d.mode d.ownership (d.body ι) := by
  induction hs with
  | empty => exact nomatch hd
  | constantDefinition _ ho ih =>
    rcases List.mem_cons.1 hd with he | hd'
    · cases he
      exact ownershipStableUnderExtension.ownership (pre := [_]) hds (ho ι)
    · exact ownershipStableUnderExtension.ownership (pre := [_]) hds (ih hds.1 hd')
  | constantDeclaration _ ih | data _ _ ih | codata _ _ _ ih =>
    rcases List.mem_cons.1 hd with he | hd'
    · exact nomatch he
    · exact ownershipStableUnderExtension.ownership (pre := [_]) hds (ih hds.1 hd')

end Sic.Core
