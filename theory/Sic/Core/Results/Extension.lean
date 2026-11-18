module

public import Sic.Core.Results
import Sic.Core.Lifting.Extension

/-!
# Recursive Results Along the Signatures

The recursive results hold in every signature that has the type declarations of theirs: the
relations read their signature only by the declaration of the type of an instance and by that of
its lifting, as the liftings do.

The typing reads the results in its signature, while the meaning computes them in the signature
in which each constant has its interpretation, which has the same type declarations.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig sig' : Signature} {v : Lifting.Variables}

-- ADE: none.
/-- The recursive results of fields are their results in a signature that has the type
declarations of their signature. -/
theorem Terms.ResultTypes.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig')
    {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {ns : List (Nest Name)} {ps : List Parameter}
    {As xs : Terms k Δ} {ps' : List Parameter} {R : Telescope k Δ' ps'} {πs : List Grade}
    (h : Terms.ResultTypes sig v ρ ns ps As xs R πs) :
    Terms.ResultTypes sig' v ρ ns ps As xs R πs := by
  induction h with
  | nil => exact .nil
  | plain _ ih => exact .plain ih
  | recursive hD _ ih => exact .recursive hD ih
  | nested hA _ ih => exact .nested (hA.ofTypeDeclarations hs) ih

-- ADE: none.
/-- The recursive result of a term is its result in a signature that has the type declarations of
its signature. -/
theorem Term.NestedResult.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig')
    {Γ : Scope} {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} {n : Nest Name}
    {A t e : Term k Γ} (h : Term.NestedResult sig v ρ φ n A t e) :
    Term.NestedResult sig' v ρ φ n A t e := by
  induction h with
  | block hD => exact .block hD
  | inst h hn hq hl hp has hS hL hgl hgs _ ih =>
    exact .inst ⟨hs _ h.1, h.2⟩ hn hq hl hp (has.ofTypeDeclarations hs) hS (hs _ hL) hgl hgs ih

-- ADE: none.
/-- The recursive results of terms of fields are their results in a signature that has the type
declarations of their signature. -/
theorem Terms.ResultTerms.ofTypeDeclarations
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig')
    {Γ : Scope} {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} {ns : List (Nest Name)}
    {ps : List Parameter} {As ts : Terms k Γ} {ps' : List Parameter} {rs : Args k Γ ps'}
    (h : Terms.ResultTerms sig v ρ φ ns ps As ts rs) :
    Terms.ResultTerms sig' v ρ φ ns ps As ts rs := by
  induction h with
  | nil => exact .nil
  | plain _ ih => exact .plain ih
  | recursive _ ih => exact .recursive ih
  | nested he _ ih => exact .nested (he.ofTypeDeclarations hs) ih

end Sic.Core
