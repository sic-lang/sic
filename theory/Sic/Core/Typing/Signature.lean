module

public import Sic.Core.Syntax.Signature
public import Sic.Core.Typing
import Sic.Core.Typing.Extension
import Sic.Core.Typing.Presuppositions

/-!
# Well-Formed Signatures

Properties of the well-formed signatures of annex 15 of RFC 36: each type declaration of a
well-formed signature is well formed in the signature before it, so that its parameters form a
context of the signature, at each instance that its constraint admits, and a destructor of a block
of propositions has a grade without use at run time, as the rules `(d̄_κ|)` and `(d̄_κrec)` premise.

ADE have no type declarations: their types are built in.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- A type declaration of a well-formed signature is well formed in the signature before it: the
signature ends with the declaration, followed by this signature. -/
theorem WfSig.wfTypeDeclaration {decl : TypeDeclaration} :
    {sig : Signature} → WfSig sig → .typeDeclaration decl ∈ sig →
      ∃ sig', (.typeDeclaration decl :: sig') <:+ sig ∧ WfTypeDeclaration sig' decl
  | [], _, he => nomatch he
  | _ :: _, h, he => by
    rcases List.mem_cons.1 he with he | he
    · subst he
      exact ⟨_, List.suffix_refl _, h.typeDeclaration_inv.1⟩
    · obtain ⟨sig', hs, hdecl⟩ :=
        (Presuppositions.tail presuppositions h).wfTypeDeclaration he
      exact ⟨sig', hs.trans (List.suffix_cons _ _), hdecl⟩

-- ADE: none.
/-- A signature that ends a well-formed signature is well formed. -/
theorem WfSig.of_suffix {sig' : Signature} :
    {sig : Signature} → WfSig sig → sig' <:+ sig → WfSig sig'
  | [], h, hs => List.eq_nil_of_suffix_nil hs ▸ h
  | _ :: _, h, hs => by
    rcases List.suffix_cons_iff.1 hs with rfl | hs
    · exact h
    · exact (Presuppositions.tail presuppositions h).of_suffix hs

/-- The entries of the signature before an entry of a signature are entries of the signature. -/
theorem Signature.subset_of_cons_suffix {e : Entry} {sig' sig : Signature}
    (h : (e :: sig') <:+ sig) : sig' ⊆ sig :=
  fun _ he => h.subset (List.mem_cons_of_mem _ he)

-- ADE: none.
/-- The parameters of a type declaration of a well-formed signature, at an instance that its
constraint admits, form a context of the signature. -/
theorem WfSig.wfCtx_params {sig : Signature} (h : WfSig sig) {decl : TypeDeclaration}
    (hd : .typeDeclaration decl ∈ sig) {I : Instance decl.sorts decl.grades}
    (hI : decl.constraint I) : WfCtx sig (decl.params I) := by
  obtain ⟨_, hs, hdecl⟩ := h.wfTypeDeclaration hd
  cases hdecl with
  | data _ _ hΔ _ _ _ => exact stableUnderExtension.wfCtx (Signature.subset_of_cons_suffix hs) h (hΔ _ hI)
  | codata _ _ hΔ _ _ _ => exact stableUnderExtension.wfCtx (Signature.subset_of_cons_suffix hs) h (hΔ _ hI)

-- ADE: none.
/-- A destructor of destructors that live in a sort of propositions has a grade whose mode is not
`11ᵐ`. -/
theorem WfDestructors.mode_of_grade {sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {d : Name} {p : Grade} :
    {Γ : Scope} → {ns : List Name} → {ν : Nesting Nat Γ} →
      {as : InstanceArgs decl.levels Γ decl.scope} →
      {ctx : Context decl.levels Γ} → {ds : Destructors decl.levels Γ ns} →
      {κ : Universe decl.levels} → WfDestructors sig decl I @ν as ctx ds κ → ds.grade d = some p →
        κ.quality = .prop → p.mode ≠ .oneOne
  | _, _, _, _, _, _, _, .nil _, hg, _ => nomatch hg
  | _, d' :: _, _, _, _, _, _, .cons _ _ _ _ hκ hp hds, hg, hq => by
    simp only [Destructors.grade] at hg
    split at hg
    · cases hg
      exact hp (hκ.1 hq)
    · exact hds.mode_of_grade hg hq
  | _, d' :: _, _, _, _, _, _, .nested _ _ _ _ hκ hp hds, hg, hq => by
    simp only [Destructors.grade, Destructors.grade_rename] at hg
    split at hg
    · cases hg
      exact hp (hκ.1 hq)
    · exact hds.mode_of_grade hg hq
  | _, d' :: _, _, _, _, _, _, .recursive _ _ hp hds, hg, hq => by
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
    (hI : decl.constraint I) {d : Name} {p q ς : Grade} {ps : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps} {B : Term decl.levels (Ξ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} (hpos : (T.body I).Pos d p q ς Ξ Θ B ψ) :
    (decl.sort I).quality = .prop → p.mode ≠ .oneOne := by
  obtain ⟨_, _, hdecl⟩ := h.wfTypeDeclaration hT.1
  cases hdecl with
  | data hb _ _ _ _ _ _ => exact absurd hT.2.1 (by simp [TypeDeclaration.codataTypes, hb])
  | codata hb _ _ hds _ _ _ =>
    exact (hds I hI T hT.2.1).mode_of_grade
      (hpos.grade (h.distinct.destructors_nodup hT))

-- ADE: none.
/-- A destructor of a codata type of a well-formed signature, at an instance that the constraint
admits, of a block of propositions, has a grade without use at run time. -/
theorem WfSig.destructor_erased {sig : Signature} (h : WfSig sig) {D : Name}
    {decl : TypeDeclaration} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : sig.HasCodataType D decl T) {I : Instance decl.sorts decl.grades}
    (hI : decl.constraint I) {d : Name} {p q ς : Grade} {ps : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps} {B : Term decl.levels (Ξ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} (hpos : (T.body I).Pos d p q ς Ξ Θ B ψ)
    (hκ : (decl.sort I).quality = .prop) : p ∈ Mode.oneOne.erased :=
  (by decide : ∀ p : Grade, p.mode ≠ .oneOne → p ∈ Mode.oneOne.erased) p
    (h.destructor_mode hT hI hpos hκ)

-- ADE: none.
/-- A well-formed signature erases the destructors of its blocks of propositions. -/
theorem WfSig.erasesPropDestructors {sig : Signature} (h : WfSig sig) :
    sig.ErasesPropDestructors :=
  fun {_ _ _} hT {_ _} _ _ hI hκ {_ _ _ _ _ _ _ _ _} hpos => h.destructor_erased hT hI hpos hκ

end Sic.Core
