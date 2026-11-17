module

public import Sic.Core.NestingFactors

/-!
# Factors Along the Signatures

The factors of annex 20 of RFC 36 hold in every signature that has the type declarations of theirs:
the relations read their signature only by the declarations of the liftings that they name.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig sig' : Signature}

mutual

-- ADE: none.
/-- A result of a destructor of a lifting has its factor likewise in a signature that has the type
declarations of its signature. -/
theorem Term.Factor.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig') :
    {k : Nat} → {Γ : Scope} → {B : Term k Γ} → {π : Grade} → Term.Factor sig B π →
      Term.Factor sig' B π
  | _, _, _, _, .var x ts => .var x ts
  | _, _, _, _, .inst h hq hp hds =>
    .inst ⟨hs _ h.1, h.2⟩ hq hp (hds.ofTypeDeclarations hs)

-- ADE: none.
/-- Destructors have their meet likewise in a signature that has the type declarations of their
signature. -/
theorem Destructors.Factor.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig') :
    {k : Nat} → {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} →
      {π : Option Grade} → Destructors.Factor sig ds π → Destructors.Factor sig' ds π
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons hB hds => .cons (hB.ofTypeDeclarations hs) (hds.ofTypeDeclarations hs)

end

-- ADE: none.
/-- A result of a destructor of a lifting has its factor likewise in a signature with more
entries. -/
theorem Term.Factor.extend (hs : sig ⊆ sig') {k : Nat} {Γ : Scope} {B : Term k Γ} {π : Grade}
    (h : Term.Factor sig B π) : Term.Factor sig' B π :=
  h.ofTypeDeclarations fun _ h' => hs h'

end Sic.Core
