module

public import Sic.Core.Typing
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Presuppositions

/-!
# Well-Formed Signatures

Properties of the well-formed signatures of annex 14 of RFC 36: each type declaration of a
well-formed signature is well formed in the signature before it, so that a destructor of a block of
propositions has a grade without use at run time, as the rules `(d̄_κ|)` and `(d̄_κrec)` premise.

ADE have no type declarations: their types are built in.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- A type declaration of a well-formed signature is well formed in the signature before it. -/
theorem WfSig.wfTypeDeclaration {decl : TypeDeclaration} :
    {sig : Signature} → WfSig sig → .typeDeclaration decl ∈ sig →
      ∃ sig', WfTypeDeclaration sig' decl
  | [], _, he => nomatch he
  | _ :: _, h, he => by
    rcases List.mem_cons.1 he with he | he
    · subst he
      cases h with
      | typeDeclaration hdecl _ _ => exact ⟨_, hdecl⟩
    · exact (Presuppositions.tail presuppositions h).wfTypeDeclaration he

-- ADE: none.
/-- A destructor of destructors that live in a sort of propositions has a grade whose mode is not
`11ᵐ`. -/
theorem WfDestructors.mode_of_grade {sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {d : Name} {p : Grade} :
    {Γ : Scope} → {ns : List Name} → {as : InstanceArgs decl.levels Γ decl.scope} →
      {ctx : Context decl.levels Γ} → {ds : Destructors decl.levels Γ ns} →
      {κ : Universe decl.levels} → WfDestructors sig decl I as ctx ds κ → ds.grade d = some p →
        κ.quality = .prop → p.mode ≠ .oneOne
  | _, _, _, _, _, _, .nil _, hg, _ => nomatch hg
  | _, d' :: _, _, _, _, _, .cons _ _ _ hκ hp hds, hg, hq => by
    simp only [Destructors.grade] at hg
    split at hg
    · cases hg
      exact hp (hκ.1 hq)
    · exact hds.mode_of_grade hg hq
  | _, d' :: _, _, _, _, _, .recursive _ _ hp hds, hg, hq => by
    simp only [Destructors.grade, Destructors.grade_rename] at hg
    split at hg
    · cases hg
      exact hp hq
    · exact hds.mode_of_grade hg hq

-- ADE: none.
/-- A destructor of a codata type of a well-formed signature, at an instance that the constraint
admits, of a block of propositions, has a grade whose mode is not `11ᵐ`. -/
theorem WfSig.destructor_mode {sig : Signature} (h : WfSig sig) {D : Name}
    {decl : TypeDeclaration} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : sig.HasCodataType D decl T) {I : Instance decl.sorts decl.grades}
    (hI : decl.constraint I) {d : Name} {p q χ : Grade} {ps : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps} {B : Term decl.levels (Ξ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} (hpos : (T.body I).Pos d p q χ Ξ Θ B ψ) :
    (decl.sort I).quality = .prop → p.mode ≠ .oneOne := by
  obtain ⟨_, hdecl⟩ := h.wfTypeDeclaration hT.1
  cases hdecl with
  | data hb _ _ _ _ => exact absurd hT.2.1 (by simp [TypeDeclaration.codataTypes, hb])
  | codata hb _ _ hds _ =>
    exact (hds I hI T hT.2.1).mode_of_grade
      (hpos.grade (h.distinct.destructors_nodup hT))

end Sic.Core
