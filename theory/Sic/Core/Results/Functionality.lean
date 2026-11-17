module

public import Sic.Core.Results
import Sic.Core.Lifting.Functionality
import Sic.Core.Syntax.Signature
import Sic.Core.Syntax.Terms

/-!
# Functionality of the Recursive Results

In a signature whose names are distinct, the fields of a constructor have one telescope of
recursive results at most: the nesting of a field tells which rule gives its result, the motive of
a type of the block is the one that the lifting of the block gives its name, and the type of a
nested field has one lifting at most.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

-- ADE: none.
/-- Fields have one telescope of recursive results at most, in a signature whose names are
distinct. -/
theorem Terms.ResultTypes.unique (hd : sig.Distinct) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps₁ ps₂ : List Parameter} → {R₁ : Telescope k Δ' ps₁} →
      {R₂ : Telescope k Δ' ps₂} → Terms.ResultTypes sig v ρ ns ps As xs R₁ →
        Terms.ResultTypes sig v ρ ns ps As xs R₂ →
          (⟨ps₁, R₁⟩ : (ps' : List Parameter) × Telescope k Δ' ps') = ⟨ps₂, R₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, .nil, h₂ => by
    cases h₂
    rfl
  | _, _, _, _, _, _, _, _, _, _, _, .plain h₁, h₂ => by
    cases h₂ with
    | plain h₂ => exact Terms.ResultTypes.unique hd h₁ h₂
  | _, _, _, _, _, _, _, _, _, _, _, .recursive hD₁ h₁, h₂ => by
    cases h₂ with
    | recursive hD₂ h₂ =>
      cases hD₁.symm.trans hD₂
      cases Terms.ResultTypes.unique hd h₁ h₂
      rfl
  | _, _, _, _, _, _, _, _, _, _, _, .nested hA₁ h₁, h₂ => by
    cases h₂ with
    | nested hA₂ h₂ =>
      obtain ⟨rfl, -⟩ := Term.Lifts.unique hd hA₁ hA₂
      cases Terms.ResultTypes.unique hd h₁ h₂
      rfl

-- ADE: none.
/-- A term has one recursive result at most, at its type and at its nesting, in a signature whose
names are distinct. -/
theorem Term.NestedResult.unique (hd : sig.Distinct) :
    {Γ : Scope} → {ρ : Lifting k Γ Γ} → {φ : Name → Term k (.var :: Γ)} → {n : Nest Name} →
      {A t e₁ e₂ : Term k Γ} → Term.NestedResult sig v ρ φ n A t e₁ →
        Term.NestedResult sig v ρ φ n A t e₂ → e₁ = e₂
  | _, _, _, _, _, _, _, _, .block _, h₂ => by
    cases h₂ with
    | block => rfl
    | inst _ hn => exact absurd rfl (hn _)
  | _, _, _, _, _, _, _, _,
      .inst (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (S := S) h₁ hn₁ hq₁ hl₁ hp₁ has₁
        _ hL₁ hgl₁ hgs₁ hgt₁,
      h₂ => by
    generalize hA : Term.inst D qs ls ps as = A at h₂
    cases h₂ with
    | block =>
      injection hA with _ _ hD
      subst hD
      exact absurd rfl (hn₁ _)
    | inst h₂ _ hq₂ hl₂ hp₂ has₂ _ hL₂ hgl₂ hgs₂ hgt₂ =>
      injection hA with _ _ hD hqs hls hps has
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h₁ h₂
      cases eq_of_heq hT
      cases eq_of_heq has
      obtain ⟨rfl, rfl, has⟩ := InstanceArgs.Lifts.unique hd has₁ has₂
      cases has
      obtain rfl := TypeDeclaration.lifting_destructors (Entry.typeDeclaration.inj
        (hd.entry_unique hL₁ hL₂ (n := Lifting.name D S) List.mem_cons_self List.mem_cons_self))
      refine congrArg _ (CorecBranches.ext (hgl₁.trans hgl₂.symm) fun i hi => ?_)
      have hi' := hgl₁ ▸ hi
      obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd₁, g₁, hg₁⟩ := hgs₁ i _ (List.getElem?_eq_getElem hi')
      obtain ⟨_, _, _, ps₂, _, _, _, _, hd₂, g₂, hg₂⟩ := hgs₂ i _ (List.getElem?_eq_getElem hi')
      obtain ⟨-, rfl⟩ := hd₁.params_unique (hd.destructors_nodup h₁) hd₂
      obtain rfl := Term.NestedResult.unique hd
        (hgt₁ i _ p q ς ps₁ Ξ Θ B ψ g₁ (List.getElem?_eq_getElem hi') hd₁ hg₁)
        (hgt₂ i _ p q ς ps₁ Ξ Θ B ψ g₂ (List.getElem?_eq_getElem hi') hd₁ hg₂)
      exact hg₁.trans hg₂.symm

-- ADE: none.
/-- The terms of fields have one list of recursive results at most, in a signature whose names are
distinct. -/
theorem Terms.ResultTerms.unique (hd : sig.Distinct) {Γ : Scope} {ρ : Lifting k Γ Γ}
    {φ : Name → Term k (.var :: Γ)} :
    {ns : List (Nest Name)} → {ps : List Parameter} → {As ts : Terms k Γ} →
      {ps₁ ps₂ : List Parameter} → {rs₁ : Args k Γ ps₁} → {rs₂ : Args k Γ ps₂} →
      Terms.ResultTerms sig v ρ φ ns ps As ts rs₁ → Terms.ResultTerms sig v ρ φ ns ps As ts rs₂ →
        (⟨ps₁, rs₁⟩ : (ps' : List Parameter) × Args k Γ ps') = ⟨ps₂, rs₂⟩
  | _, _, _, _, _, _, _, _, .nil, h₂ => by
    cases h₂
    rfl
  | _, _, _, _, _, _, _, _, .plain h₁, h₂ => by
    cases h₂ with
    | plain h₂ => exact Terms.ResultTerms.unique hd h₁ h₂
  | _, _, _, _, _, _, _, _, .recursive h₁, h₂ => by
    cases h₂ with
    | recursive h₂ =>
      cases Terms.ResultTerms.unique hd h₁ h₂
      rfl
  | _, _, _, _, _, _, _, _, .nested he₁ h₁, h₂ => by
    cases h₂ with
    | nested he₂ h₂ =>
      cases Term.NestedResult.unique hd he₁ he₂
      cases Terms.ResultTerms.unique hd h₁ h₂
      rfl

end Sic.Core
