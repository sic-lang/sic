module

public import Sic.Core.Lifting
import Sic.Core.NestingFactors.Extension

/-!
# Liftings Along the Signatures

The liftings of annex 20 of RFC 36 hold in every signature that has the entries of theirs: the
relations read their signature only by the entries that it has, the declaration of the type of an
instance and that of its lifting, so that a signature that has these type declarations gives the same premises, as a signature with
more entries does, and as the signature of the meaning does, in which the constants alone change.

A lifting is checked in the signature before it, while a later entry reads it in its own
signature, which has more entries.
A signature declares its liftings in order when the destructors of each are lifted in the signature
before it: the proofs that follow the liftings that a lifting reads, as the existence of the
recursive results, go by induction on the entries of such a signature.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig sig' : Signature} {v : Lifting.Variables}

mutual

-- ADE: none.
/-- A type lifted is lifted likewise in a signature that has the type declarations of its
signature. -/
theorem Term.Lifts.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {l : Level k} → Term.Lifts sig v ρ n e A A' l →
        Term.Lifts sig' v ρ n e A A' l
  | _, _, _, _, _, _, _, _, .var hx hts => .var hx hts
  | _, _, _, _, _, _, _, _, .block hD => .block hD
  | _, _, _, _, _, _, _, _, .inst h hD hn hq hl hp has hS hL =>
    .inst (hs _ h) hD hn hq hl hp (has.ofTypeDeclarations hs) hS (hs _ hL)

-- ADE: none.
/-- The arguments of an instance lifted are lifted likewise in a signature that has the type
declarations of their signature. -/
theorem InstanceArgs.Lifts.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ls : List (Level k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ls as' →
        InstanceArgs.Lifts sig' v ρ ns as S ls as'
  | _, _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, _, _, .lifted has hB => .lifted (has.ofTypeDeclarations hs) (hB.ofTypeDeclarations hs)
  | _, _, _, _, _, _, _, _, _, _, .absent has hB hn => .absent (has.ofTypeDeclarations hs) hB hn

end

-- ADE: none.
/-- A type lifted is lifted likewise in a signature with more entries. -/
theorem Term.Lifts.extend (hs : sig ⊆ sig') {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n : Nest Name}
    {e : Term k Γ'} {A : Term k Γ} {A' : Term k Γ'} {l : Level k}
    (h : Term.Lifts sig v ρ n e A A' l) : Term.Lifts sig' v ρ n e A A' l :=
  h.ofTypeDeclarations fun _ h' => hs h'

-- ADE: none.
/-- The arguments of an instance lifted are lifted likewise in a signature with more entries. -/
theorem InstanceArgs.Lifts.extend (hs : sig ⊆ sig') {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} {Δ : Scope} {as : InstanceArgs k Γ Δ} {S : List Nat}
    {ls : List (Level k)} {Δ' : Scope} {as' : InstanceArgs k Γ' Δ'}
    (h : InstanceArgs.Lifts sig v ρ ns as S ls as') : InstanceArgs.Lifts sig' v ρ ns as S ls as' :=
  h.ofTypeDeclarations fun _ h' => hs h'

-- ADE: none.
/-- The destructors of a codata type lifted are lifted likewise in a signature with more
entries. -/
theorem Destructors.Lifts.extend (hs : sig ⊆ sig') {Γ₀ : Scope} {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)} {Γ' : Scope}
    {ρ : Lifting k Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} {ns : List Name} {ds : Destructors k Ξ ns}
    {ns' : List Name} {ds' : Destructors k Γ' ns'} (h : Destructors.Lifts sig v κ o ρ @θ ds ds') :
    Destructors.Lifts sig' v κ o ρ @θ ds ds' := by
  induction h with
  | nil => exact .nil
  | lifted hB hπ hκ _ ih => exact .lifted (hB.extend hs) (hπ.extend hs) hκ ih
  | absent hB _ ih => exact .absent hB ih

-- ADE: none.
/-- The destructors of the lifting of a type of a type declaration are those of this lifting in a
signature with more entries. -/
theorem TypeDeclaration.Lifts.extend (hs : sig ⊆ sig') {decl : TypeDeclaration} {F : Name}
    {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (h : decl.Lifts sig F S body) : decl.Lifts sig' F S body :=
  let ⟨T, hT, hn, hb⟩ := h
  ⟨T, hT, hn, fun I => (hb I).extend hs⟩

/-! ## Order of the Liftings -/

-- ADE: none.
/-- The signature declares each of its liftings after the destructors that it lifts: the lifting of
a type of one of its type declarations has the destructors of this type, lifted in the signature
before the lifting. -/
def Signature.LiftsInOrder (sig : Signature) : Prop :=
  ∀ (pre sig₁ : Signature) (decl : TypeDeclaration) (D : Name) (S : List Nat) (ns : List Name)
    (body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns),
    sig = pre ++ .typeDeclaration (decl.lifting D S ns body) :: sig₁ →
      .typeDeclaration decl ∈ sig → D ∈ decl.names → decl.Lifts sig₁ D S body

-- ADE: none.
/-- The liftings of a signature that declares each of them after the destructors that it lifts are
those of its types, in the whole signature. -/
theorem Signature.LiftsInOrder.lifts (h : sig.LiftsInOrder) {decl : TypeDeclaration} {D : Name}
    {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hd : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names)
    (hL : .typeDeclaration (decl.lifting D S ns body) ∈ sig) : decl.Lifts sig D S body := by
  obtain ⟨pre, sig₁, rfl⟩ := List.append_of_mem hL
  exact (h pre sig₁ decl D S ns body rfl hd hD).extend
    fun _ he => List.mem_append_right _ (List.mem_cons_of_mem _ he)

end Sic.Core
