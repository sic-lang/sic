module

public import Sic.Core.Meaning

/-!
# Entries of the Signature

The soundness of the rules `(f)`, `(δ)` and `(f_≡)` reads an entry of the signature `Σ` of their
typing, while their meaning is in a signature `Σ'` that holds the entries of `Σ` and gives each of
them its meaning: the judgments typed in `Σ` are proved meaningful in every such `Σ'`, so that each
entry of a well-formed signature, typed in the signature before it, is meaningful in the whole
signature.

The meaning is not proved in the signature before the entry and then extended: a type declaration
quantifies over the closed terms of its fields, which a larger signature may add, so that a type
meaningful in a signature need not be in a larger one, while the typing ensures that it is.

ADE extend the typed judgments and the typed reductions along a well-formed extension of their
context of definitions, `» ∇′ ⊇ ∇`, on which their logical relation is defined.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- The signature `Σ` holds each entry of the signature `Σ_T` and gives it its meaning, so that the
judgments typed in `Σ_T` are meaningful in `Σ`. -/
def Signature.ValidEntries (ι : Interpretation) (sig sigT : Signature) : Prop :=
  ∀ e ∈ sigT, e ∈ sig ∧ ValidEntry sig ι e

/-- A meaningful signature gives its own entries their meaning. -/
theorem ValidSig.validEntries {ι : Interpretation} {sig : Signature} (h : ValidSig ι sig) :
    sig.ValidEntries ι sig :=
  fun e he => ⟨he, h.2 e he⟩

-- ADE: none.
/-- A constant of `Σ_T` unfolds in `Σ`, once the constants are interpreted, to a body that is a term
of its type at each instance of its sort and grade variables and each value of its level
variables: the body of a definition, or the interpretation of a declaration. -/
theorem Signature.ValidEntries.hasConstant {ι : Interpretation} {sig sigT : Signature}
    (h : sig.ValidEntries ι sigT) {f : Name} {j k' g : Nat} {m : Mode} {p : Grade}
    {A : Instance j g → Term k' []} :
    sigT.HasConstant f j k' g m p A →
      ∃ b : Instance j g → Term k' [],
        (∀ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (hq : qs.length = j)
            (hl : ls.length = k') (hp : ps.length = g),
          Red (sig.interpret ι) (Term.const (Γ := []) f qs ls ps)
            (Signature.instanceType b (.ofLists qs ps hq hp) (ls.getFin hl))) ∧
        ∀ inst ρ, ValidTerm₀ sig ι ((b inst).atLevels ρ) ((A inst).atLevels ρ)
  | .constantDefinition (d := d) hd =>
    have ⟨hmem, hv⟩ := h _ hd
    ⟨d.body, fun _ _ _ hq hl hp =>
      .delta (List.mem_map_of_mem (f := Entry.interpret ι) hmem) hq hl hp,
      ValidConstantDefinition.iff.1 hv⟩
  | .constantDeclaration (c := c) hc =>
    have ⟨hmem, hv⟩ := h _ hc
    ⟨ι c, fun _ _ _ hq hl hp =>
      .delta (d := ⟨c.name, c.sorts, c.levels, c.grades, c.mode, c.ownership, c.type, ι c⟩)
        (List.mem_map_of_mem (f := Entry.interpret ι) hmem) hq hl hp,
      ValidConstantDeclaration.iff.1 hv⟩

-- ADE: none.
/-- A signature whose entries a signature gives their meaning has no declared type in the core,
since the kinds of declarations give the meaning of their type declarations. -/
theorem Signature.ValidEntries.not_hasDeclaredType {ι : Interpretation} {sig sigT : Signature}
    (h : sig.ValidEntries ι sigT) {D : Name} {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} :
    ¬ sigT.HasDeclaredType D decl T :=
  fun ⟨hd, _⟩ => (h _ hd).2

end Sic.Core
