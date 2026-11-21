module

public import Sic.Core.Typing
import Sic.Core.Typing.Induction

/-!
# Presuppositions

The presuppositions of the judgments of annex 15 of RFC 36: every judgment holds in a well-formed
signature, and the signature that a well-formed signature extends is well formed, so that the names
of a well-formed signature are distinct.
The proof is by mutual structural recursion on the derivations, through a premise that is a judgment
in the same signature, down to the rule `(ctx_ε)`, whose premise is `⊢ Σ`, in the clause `where` of
the theorem, whose auxiliary theorems give the fields of the record.

ADE prove the well-formedness of the contexts of their judgments, for contexts of definitions.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Presuppositions

Every judgment holds in a well-formed signature, and the signature that a well-formed signature
extends is well formed: each rule has a premise that is a judgment in the same signature, down to the
rule `(ctx_ε)`, whose premise is `⊢ Σ`.
The proof is by mutual structural recursion on the derivations, through such a premise, in the
clause `where` of the theorem, whose auxiliary theorems give the fields of the record.
-/

-- ADE: none.
/-- An instance of `j` sort variables and `g` grade variables, which exists whatever `j` and `g`. -/
def Instance.default (j g : Nat) : Instance j g := ⟨fun _ => .type, fun _ => Grade.zero⟩

-- ADE: `wf` and `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`, for the contexts and
-- the judgments in a context of definitions.
/-- Every judgment holds in a well-formed signature, and the signature that a well-formed signature
extends is well formed. -/
structure Presuppositions : Prop where
  /-- A well-formed constant definition is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{def}` -/
  wfConstantDefinition : ∀ {sig : Signature} {d : ConstantDefinition},
    WfConstantDefinition sig d → WfSig sig
  /-- A well-formed constant declaration is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{decl}` -/
  wfConstantDeclaration : ∀ {sig : Signature} {c : ConstantDeclaration},
    WfConstantDeclaration sig c → WfSig sig
  /-- A well-formed context is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Gamma` -/
  wfCtx : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    WfCtx sig ctx → WfSig sig
  /-- A type is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ},
    WfType sig ctx A → WfSig sig
  /-- An equality of types is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ},
    EqType sig ctx A B → WfSig sig
  /-- A typing is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    HasType sig ctx t A → WfSig sig
  /-- An equality of terms is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ},
    EqTerm sig ctx t u A → WfSig sig
  /-- Arguments of a telescope are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, HasArgs sig ctx ts Θ → WfSig sig
  /-- Equal arguments of a telescope are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, EqArgs sig ctx ts us Θ → WfSig sig
  /-- Arguments of an instance are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    HasInstanceArgs sig ctx as params → WfSig sig
  /-- Equal arguments of instances are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    EqInstanceArgs sig ctx as₁ as₂ params → WfSig sig
  /-- A telescope in a sort is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {Θ : Telescope k Γ ps} {κ : Universe k}, WfTelescope sig ctx Θ κ → WfSig sig
  /-- A telescope in sorts is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k},
    WfTelescopeSorts sig ctx Θ κs l → WfSig sig
  /-- An equality of telescopes in a sort is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → WfSig sig
  /-- The fields of a constructor in a sort are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{fields}` -/
  wfFields : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
    {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
    {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels},
    WfFields sig decl ι as ctx Θ κ → WfSig sig
  /-- The destructors of a codata type in a sort are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar d` -/
  wfDestructors : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
    {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope}
    {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
    WfDestructors sig decl ι @ν as ctx ds κ → WfSig sig
  /-- A well-formed type declaration is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{data}`
  RFC: `\mathsf{presup}_\Sigma.\mathsf{codata}` -/
  wfTypeDeclaration : ∀ {sig : Signature} {decl : TypeDeclaration},
    WfTypeDeclaration sig decl → WfSig sig
  /-- The signature that a well-formed signature extends is well formed.
  RFC: `\mathsf{presup}_\Sigma.e` -/
  tail : ∀ {e : Entry} {sig : Signature}, WfSig (e :: sig) → WfSig sig

-- ADE: `wf` and `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`, for the contexts and
-- the judgments in a context of definitions.
/-- The judgments hold in well-formed signatures.
RFC: `\mathsf{presup}_\Sigma.\mathsf{def}`
RFC: `\mathsf{presup}_\Sigma.\mathsf{decl}`
RFC: `\mathsf{presup}_\Sigma.\Gamma`
RFC: `\mathsf{presup}_\Sigma.A`
RFC: `\mathsf{presup}_\Sigma.A_\equiv`
RFC: `\mathsf{presup}_\Sigma.t`
RFC: `\mathsf{presup}_\Sigma.t_\equiv`
RFC: `\mathsf{presup}_\Sigma.\bar t`
RFC: `\mathsf{presup}_\Sigma.\bar t_\equiv`
RFC: `\mathsf{presup}_\Sigma.\bar a`
RFC: `\mathsf{presup}_\Sigma.\bar a_\equiv`
RFC: `\mathsf{presup}_\Sigma.\Theta`
RFC: `\mathsf{presup}_\Sigma.\Theta_{\bar\kappa}`
RFC: `\mathsf{presup}_\Sigma.\Theta_\equiv`
RFC: `\mathsf{presup}_\Sigma.\mathsf{fields}`
RFC: `\mathsf{presup}_\Sigma.\bar d`
RFC: `\mathsf{presup}_\Sigma.\mathsf{data}`
RFC: `\mathsf{presup}_\Sigma.\mathsf{codata}`
RFC: `\mathsf{presup}_\Sigma.e` -/
theorem presuppositions : Presuppositions := by
  suffices H : Derivations.Conclusion
      (wfSig := fun l _ => WfSig l.tail)
      (wfConstantDefinition := fun sig _ _ => WfSig sig)
      (wfConstantDeclaration := fun sig _ _ => WfSig sig)
      (wfCtx := fun sig {k Γ} ctx _ => WfSig sig)
      (wfType := fun sig {k Γ} ctx A _ => WfSig sig)
      (eqType := fun sig {k Γ} ctx A B _ => WfSig sig)
      (hasType := fun sig {k Γ} ctx t A _ => WfSig sig)
      (eqTerm := fun sig {k Γ} ctx t u A _ => WfSig sig)
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => WfSig sig)
      (eqArgs := fun sig {k Γ ps} ctx ts us Θ _ => WfSig sig)
      (hasInstanceArgs := fun sig {k Γ Δ} ctx as params _ => WfSig sig)
      (eqInstanceArgs := fun sig {k Γ Δ} ctx as₁ as₂ params _ => WfSig sig)
      (wfTelescope := fun sig {k Γ ps} ctx Θ κ _ => WfSig sig)
      (wfTelescopeSorts := fun sig {k Γ ps} ctx Θ κs l _ => WfSig sig)
      (eqTelescope := fun sig {k Γ ps} ctx Θ₁ Θ₂ κ _ => WfSig sig)
      (wfFields := fun sig decl ι {Γ} as ctx {ps} Θ κ _ => WfSig sig)
      (wfDestructors := fun sig decl ι {Γ ns} ν as ctx ds κ _ => WfSig sig)
      (wfTypeDeclaration := fun sig decl _ => WfSig sig) from
    ⟨H.wfConstantDefinition, H.wfConstantDeclaration, H.wfCtx, H.wfType, H.eqType, H.hasType,
      H.eqTerm, H.hasArgs, H.eqArgs, H.hasInstanceArgs, H.eqInstanceArgs, H.wfTelescope,
      H.wfTelescopeSorts, H.eqTelescope, H.wfFields, H.wfDestructors, H.wfTypeDeclaration, H.wfSig⟩
  apply Derivations.induction
  case wfSig_empty => exact .empty
  case wfSig_constantDefinition => exact fun h fresh h_ih => h_ih
  case wfSig_constantDeclaration => exact fun h fresh h_ih => h_ih
  case wfSig_typeDeclaration => exact fun h hn hL h_ih => h_ih
  case wfSig_lifting => exact fun h hd hl h_ih => h_ih
  case wfConstantDefinition_intro => exact fun κ hA ht hA_ih ht_ih => hA_ih (.default _ _)
  case wfConstantDeclaration_intro => exact fun κ hA hA_ih => hA_ih (.default _ _)
  case wfCtx_empty => exact fun h h_ih => h
  case wfCtx_var => exact fun h h_ih => h_ih
  case wfCtx_secondOrder => exact fun h h_ih => h_ih
  case wfType_univType => exact fun h h_ih => h_ih
  case wfType_propType => exact fun h h_ih => h_ih
  case eqType_refl => exact fun h h_ih => h_ih
  case eqType_symm => exact fun h h_ih => h_ih
  case eqType_trans => exact fun h₁ h₂ h₁_ih h₂_ih => h₁_ih
  case eqType_univType => exact fun h h_ih => h_ih
  case eqType_propType => exact fun h h_ih => h_ih
  case hasType_var => exact fun hctx hx hctx_ih => hctx_ih
  case hasType_secondOrder => exact fun hX hts hts_ih => hts_ih
  case hasType_const => exact fun hctx h hq hl hp hctx_ih => hctx_ih
  case hasType_univ => exact fun hctx hctx_ih => hctx_ih
  case hasType_prop => exact fun hctx hctx_ih => hctx_ih
  case hasType_inst => exact fun h hq hl hp hadm has has_ih => has_ih
  case hasType_equality => exact fun hA ht hu hA_ih ht_ih hu_ih => hA_ih
  case hasType_reflProof => exact fun hA ht hA_ih ht_ih => hA_ih
  case hasType_transp =>
    exact fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
      hA_ih
  case hasType_propExt => exact fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => hA_ih
  case hasType_coind =>
    exact fun h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih
        ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih =>
      has_ih
  case hasType_ctor => exact fun h hc hq hl hp hadm has _ hts has_ih hts_ih => has_ih
  case hasType_recursor =>
    exact fun h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus _ hRs hut hκ has_ih ht_ih hCt_ih
        hut_ih =>
      has_ih
  case hasType_obs => exact fun h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih => has_ih
  case hasType_corec =>
    exact fun h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih hgt_ih
        =>
      has_ih
  case hasType_conv => exact fun ht h ht_ih h_ih => ht_ih
  case eqTerm_refl => exact fun h h_ih => h_ih
  case eqTerm_symm => exact fun h h_ih => h_ih
  case eqTerm_trans => exact fun h₁ h₂ h₁_ih h₂_ih => h₁_ih
  case eqTerm_conv => exact fun h hA h_ih hA_ih => h_ih
  case eqTerm_irr => exact fun ht hu hA ht_ih hu_ih hA_ih => ht_ih
  case eqTerm_secondOrder => exact fun hX hts hts_ih => hts_ih
  case eqTerm_delta => exact fun hctx h hq hl hp hctx_ih => hctx_ih
  case eqTerm_const => exact fun hctx h hq hl₁ hl₂ hp hls hctx_ih => hctx_ih
  case eqTerm_univ => exact fun hctx hl hctx_ih => hctx_ih
  case eqTerm_prop => exact fun hctx hl hctx_ih => hctx_ih
  case eqTerm_inst => exact fun h hq hl₁ hl₂ hp hadm has hls has_ih => has_ih
  case eqTerm_equality => exact fun hA ht hu hl hA_ih ht_ih hu_ih => hA_ih
  case eqTerm_transp => exact fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih => hA_ih
  case eqTerm_transpSame =>
    exact fun hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih =>
      hA_ih
  case eqTerm_ctor => exact fun h hc hq hl₁ hl₂ hp hadm has hls _ _ hts has_ih hts_ih => has_ih
  case eqTerm_recursor =>
    exact fun h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes
        _ _ hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_obs => exact fun h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih => has_ih
  case eqTerm_corec =>
    exact fun h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂
        hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih =>
      has_ih
  case eqTerm_iota =>
    exact fun h hc hq hl hp hadm _ has _ hts hi hC hu _ hrs hCl hCs hCt hul hus _ hRs hut hκ has_ih
        hts_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_etaCtor =>
    exact fun h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus _ hRs hut hκ has_ih ht_ih
        he_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_beta =>
    exact fun h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih hss_ih
        hbs_ih hSt_ih hgt_ih =>
      has_ih
  case eqTerm_etaObs =>
    exact fun h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih =>
      has_ih
  case hasArgs_nil => exact fun hctx hctx_ih => hctx_ih
  case hasArgs_cons => exact fun ht hts ht_ih hts_ih => ht_ih
  case eqArgs_nil => exact fun hctx hctx_ih => hctx_ih
  case eqArgs_cons => exact fun ht hts ht_ih hts_ih => ht_ih
  case hasInstanceArgs_nil => exact fun hctx hctx_ih => hctx_ih
  case hasInstanceArgs_var => exact fun has ha has_ih ha_ih => has_ih
  case hasInstanceArgs_secondOrder => exact fun has hB has_ih hB_ih => has_ih
  case eqInstanceArgs_nil => exact fun hctx hctx_ih => hctx_ih
  case eqInstanceArgs_var => exact fun has ha has_ih ha_ih => has_ih
  case eqInstanceArgs_secondOrder => exact fun has hB has_ih hB_ih => has_ih
  case wfTelescope_nil => exact fun hctx hctx_ih => hctx_ih
  case wfTelescope_cons => exact fun hA hκ hΘ hp hA_ih hΘ_ih => hA_ih
  case wfTelescopeSorts_nil => exact fun hctx hctx_ih => hctx_ih
  case wfTelescopeSorts_cons => exact fun hA hl hΘ hp hA_ih hΘ_ih => hA_ih
  case eqTelescope_nil => exact fun hctx hctx_ih => hctx_ih
  case eqTelescope_cons => exact fun hA hκ hΘ hp hA_ih hΘ_ih => hA_ih
  case wfFields_nil => exact fun hctx hctx_ih => hctx_ih
  case wfFields_cons => exact fun hn hA hκ hΘ hp hA_ih hΘ_ih => hA_ih
  case wfFields_recursive => exact fun hD hΘ hp hΘ_ih => hΘ_ih
  case wfFields_nested => exact fun hn hA₀ hκ hq hpos hpre hΘ hp hA₀_ih hΘ_ih => hΘ_ih
  case wfDestructors_nil => exact fun hctx hctx_ih => hctx_ih
  case wfDestructors_cons => exact fun hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih => hΘ_ih
  case wfDestructors_nested => exact fun hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih => hΘ_ih
  case wfDestructors_recursive => exact fun hD hΘ hp hds hΘ_ih hds_ih => hΘ_ih
  case wfTypeDeclaration_data =>
    refine fun hb hadm hΔ hΘ hp hc fresh hΔ_ih hΘ_ih => ?_
    obtain ⟨_, hadm⟩ := hadm; exact hΔ_ih _ hadm
  case wfTypeDeclaration_codata =>
    refine fun hb hadm hΔ hd hp hc fresh hΔ_ih hd_ih => ?_
    obtain ⟨_, hadm⟩ := hadm; exact hΔ_ih _ hadm

-- ADE: `wfTerm`, `wfEqTerm` and their kin, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Every judgment in a context holds in a well-formed context. -/
structure ContextPresuppositions : Prop where
  /-- A type is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ},
    WfType sig ctx A → WfCtx sig ctx
  /-- An equality of types is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ},
    EqType sig ctx A B → WfCtx sig ctx
  /-- A typing is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    HasType sig ctx t A → WfCtx sig ctx
  /-- An equality of terms is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ},
    EqTerm sig ctx t u A → WfCtx sig ctx
  /-- Arguments of a telescope are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, HasArgs sig ctx ts Θ → WfCtx sig ctx
  /-- Equal arguments of a telescope are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, EqArgs sig ctx ts us Θ → WfCtx sig ctx
  /-- Arguments of an instance are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    HasInstanceArgs sig ctx as params → WfCtx sig ctx
  /-- Equal arguments of instances are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    EqInstanceArgs sig ctx as₁ as₂ params → WfCtx sig ctx
  /-- A telescope in a sort is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {Θ : Telescope k Γ ps} {κ : Universe k}, WfTelescope sig ctx Θ κ → WfCtx sig ctx
  /-- A telescope in sorts is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k},
    WfTelescopeSorts sig ctx Θ κs l → WfCtx sig ctx
  /-- An equality of telescopes in a sort is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → WfCtx sig ctx

-- ADE: `wfTerm`, `wfEqTerm` and their kin, in `Definition/Typed/Properties/Well-formed.agda`.
/-- The judgments in a context hold in a well-formed context.
RFC: `\mathsf{presup}_\Gamma.A`
RFC: `\mathsf{presup}_\Gamma.A_\equiv`
RFC: `\mathsf{presup}_\Gamma.t`
RFC: `\mathsf{presup}_\Gamma.t_\equiv`
RFC: `\mathsf{presup}_\Gamma.\bar t`
RFC: `\mathsf{presup}_\Gamma.\bar t_\equiv`
RFC: `\mathsf{presup}_\Gamma.\bar a`
RFC: `\mathsf{presup}_\Gamma.\bar a_\equiv`
RFC: `\mathsf{presup}_\Gamma.\Theta`
RFC: `\mathsf{presup}_\Gamma.\Theta_{\bar\kappa}`
RFC: `\mathsf{presup}_\Gamma.\Theta_\equiv` -/
theorem contextPresuppositions : ContextPresuppositions := by
  suffices H : Derivations.Conclusion
      (wfSig := fun _ _ => True)
      (wfConstantDefinition := fun _ _ _ => True)
      (wfConstantDeclaration := fun _ _ _ => True)
      (wfCtx := fun _ _ _ _ _ => True)
      (wfType := fun sig {k Γ} ctx A _ => WfCtx sig ctx)
      (eqType := fun sig {k Γ} ctx A B _ => WfCtx sig ctx)
      (hasType := fun sig {k Γ} ctx t A _ => WfCtx sig ctx)
      (eqTerm := fun sig {k Γ} ctx t u A _ => WfCtx sig ctx)
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => WfCtx sig ctx)
      (eqArgs := fun sig {k Γ ps} ctx ts us Θ _ => WfCtx sig ctx)
      (hasInstanceArgs := fun sig {k Γ Δ} ctx as params _ => WfCtx sig ctx)
      (eqInstanceArgs := fun sig {k Γ Δ} ctx as₁ as₂ params _ => WfCtx sig ctx)
      (wfTelescope := fun sig {k Γ ps} ctx Θ κ _ => WfCtx sig ctx)
      (wfTelescopeSorts := fun sig {k Γ ps} ctx Θ κs l _ => WfCtx sig ctx)
      (eqTelescope := fun sig {k Γ ps} ctx Θ₁ Θ₂ κ _ => WfCtx sig ctx)
      (wfFields := fun _ _ _ _ _ _ _ _ _ _ => True)
      (wfDestructors := fun _ _ _ _ _ _ _ _ _ _ _ => True)
      (wfTypeDeclaration := fun _ _ _ => True) from
    ⟨H.wfType, H.eqType, H.hasType, H.eqTerm, H.hasArgs, H.eqArgs, H.hasInstanceArgs,
      H.eqInstanceArgs, H.wfTelescope, H.wfTelescopeSorts, H.eqTelescope⟩
  apply Derivations.induction
  case wfType_univType => exact fun h h_ih => h_ih
  case wfType_propType => exact fun h h_ih => h_ih
  case eqType_refl => exact fun h h_ih => h_ih
  case eqType_symm => exact fun h h_ih => h_ih
  case eqType_trans => exact fun h₁ h₂ h₁_ih h₂_ih => h₁_ih
  case eqType_univType => exact fun h h_ih => h_ih
  case eqType_propType => exact fun h h_ih => h_ih
  case hasType_var => exact fun hctx hx hctx_ih => hctx
  case hasType_secondOrder => exact fun hX hts hts_ih => hts_ih
  case hasType_const => exact fun hctx h hq hl hp hctx_ih => hctx
  case hasType_univ => exact fun hctx hctx_ih => hctx
  case hasType_prop => exact fun hctx hctx_ih => hctx
  case hasType_inst => exact fun h hq hl hp hadm has has_ih => has_ih
  case hasType_equality => exact fun hA ht hu hA_ih ht_ih hu_ih => hA_ih
  case hasType_reflProof => exact fun hA ht hA_ih ht_ih => hA_ih
  case hasType_transp =>
    exact fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
      hA_ih
  case hasType_propExt => exact fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => hA_ih
  case hasType_coind =>
    exact fun h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih
        ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih =>
      has_ih
  case hasType_ctor => exact fun h hc hq hl hp hadm has _ hts has_ih hts_ih => has_ih
  case hasType_recursor =>
    exact fun h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus _ hRs hut hκ has_ih ht_ih hCt_ih
        hut_ih =>
      has_ih
  case hasType_obs => exact fun h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih => has_ih
  case hasType_corec =>
    exact fun h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih hgt_ih
        =>
      has_ih
  case hasType_conv => exact fun ht h ht_ih h_ih => ht_ih
  case eqTerm_refl => exact fun h h_ih => h_ih
  case eqTerm_symm => exact fun h h_ih => h_ih
  case eqTerm_trans => exact fun h₁ h₂ h₁_ih h₂_ih => h₁_ih
  case eqTerm_conv => exact fun h hA h_ih hA_ih => h_ih
  case eqTerm_irr => exact fun ht hu hA ht_ih hu_ih hA_ih => ht_ih
  case eqTerm_secondOrder => exact fun hX hts hts_ih => hts_ih
  case eqTerm_delta => exact fun hctx h hq hl hp hctx_ih => hctx
  case eqTerm_const => exact fun hctx h hq hl₁ hl₂ hp hls hctx_ih => hctx
  case eqTerm_univ => exact fun hctx hl hctx_ih => hctx
  case eqTerm_prop => exact fun hctx hl hctx_ih => hctx
  case eqTerm_inst => exact fun h hq hl₁ hl₂ hp hadm has hls has_ih => has_ih
  case eqTerm_equality => exact fun hA ht hu hl hA_ih ht_ih hu_ih => hA_ih
  case eqTerm_transp => exact fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih => hA_ih
  case eqTerm_transpSame =>
    exact fun hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih =>
      hA_ih
  case eqTerm_ctor => exact fun h hc hq hl₁ hl₂ hp hadm has hls _ _ hts has_ih hts_ih => has_ih
  case eqTerm_recursor =>
    exact fun h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes
        _ _ hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_obs => exact fun h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih => has_ih
  case eqTerm_corec =>
    exact fun h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂
        hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih =>
      has_ih
  case eqTerm_iota =>
    exact fun h hc hq hl hp hadm _ has _ hts hi hC hu _ hrs hCl hCs hCt hul hus _ hRs hut hκ has_ih
        hts_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_etaCtor =>
    exact fun h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus _ hRs hut hκ has_ih ht_ih
        he_ih hCt_ih hut_ih =>
      has_ih
  case eqTerm_beta =>
    exact fun h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih hss_ih
        hbs_ih hSt_ih hgt_ih =>
      has_ih
  case eqTerm_etaObs =>
    exact fun h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih =>
      has_ih
  case hasArgs_nil => exact fun hctx hctx_ih => hctx
  case hasArgs_cons => exact fun ht hts ht_ih hts_ih => ht_ih
  case eqArgs_nil => exact fun hctx hctx_ih => hctx
  case eqArgs_cons => exact fun ht hts ht_ih hts_ih => ht_ih
  case hasInstanceArgs_nil => exact fun hctx hctx_ih => hctx
  case hasInstanceArgs_var => exact fun has ha has_ih ha_ih => has_ih
  case hasInstanceArgs_secondOrder => exact fun has hB has_ih hB_ih => has_ih
  case eqInstanceArgs_nil => exact fun hctx hctx_ih => hctx
  case eqInstanceArgs_var => exact fun has ha has_ih ha_ih => has_ih
  case eqInstanceArgs_secondOrder => exact fun has hB has_ih hB_ih => has_ih
  case wfTelescope_nil => exact fun hctx hctx_ih => hctx
  case wfTelescope_cons => exact fun hA hκ hΘ hp hA_ih hΘ_ih => hA_ih
  case wfTelescopeSorts_nil => exact fun hctx hctx_ih => hctx
  case wfTelescopeSorts_cons => exact fun hA hl hΘ hp hA_ih hΘ_ih => hA_ih
  case eqTelescope_nil => exact fun hctx hctx_ih => hctx
  case eqTelescope_cons => exact fun hA hκ hΘ hp hA_ih hΘ_ih => hA_ih
  case wfSig_empty | wfSig_constantDefinition | wfSig_constantDeclaration | wfSig_typeDeclaration |
      wfSig_lifting | wfConstantDefinition_intro | wfConstantDeclaration_intro | wfCtx_empty |
      wfCtx_var | wfCtx_secondOrder | wfFields_nil | wfFields_cons | wfFields_recursive |
      wfFields_nested | wfDestructors_nil | wfDestructors_cons | wfDestructors_nested |
      wfDestructors_recursive | wfTypeDeclaration_data | wfTypeDeclaration_codata => intros; trivial

-- ADE: none.
/-- A well-formed type declaration introduces names of types that no entry of the signature does. -/
theorem WfTypeDeclaration.fresh {sig : Signature} {decl : TypeDeclaration} :
    WfTypeDeclaration sig decl → ∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names
  | .data _ _ _ _ _ _ h => h
  | .codata _ _ _ _ _ _ h => h

-- ADE: none.
/-- The type declaration that ends a well-formed signature is well formed in the signature before
it, and names each of its types once. -/
theorem WfSig.typeDeclaration_inv {decl : TypeDeclaration} {sig : Signature} :
    WfSig (.typeDeclaration decl :: sig) → WfTypeDeclaration sig decl ∧ decl.names.Nodup
  | .typeDeclaration h hn _ => ⟨h, hn⟩
  | .lifting h _ _ => ⟨h, List.pairwise_singleton _ _⟩

-- ADE: none.
/-- The last entry of a well-formed signature introduces names that no entry before it does. -/
theorem WfSig.fresh {e : Entry} {sig : Signature} :
    WfSig (e :: sig) → ∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names
  | .constantDefinition _ h, e', he', n, hn => by
    simp only [Entry.names, List.mem_singleton] at hn
    exact hn ▸ h e' he'
  | .constantDeclaration _ h, e', he', n, hn => by
    simp only [Entry.names, List.mem_singleton] at hn
    exact hn ▸ h e' he'
  | .typeDeclaration h _ _, e', he', n, hn => h.fresh e' he' n hn
  | .lifting h _ _, e', he', n, hn => h.fresh e' he' n hn

-- ADE: none.
/-- The names of a well-formed signature are distinct.
RFC: `\mathsf{distinct}_\Sigma` -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨(Presuppositions.tail presuppositions h).distinct,
      by cases h with
        | typeDeclaration _ hn => exact hn
        | _ => exact List.pairwise_singleton _ _, h.fresh,
      by
        rename_i e _
        cases e with
        | typeDeclaration decl => cases h.typeDeclaration_inv.1 with
          | data hb _ _ _ _ hc _ =>
            refine ⟨hc, fun T hT => ?_⟩
            simp only [TypeDeclaration.codataTypes, hb] at hT
            nomatch hT
          | codata hb _ _ _ _ hc _ =>
            refine ⟨fun T hT => ?_, hc⟩
            simp only [TypeDeclaration.dataTypes, hb] at hT
            nomatch hT
        | _ => trivial⟩

end Sic.Core
