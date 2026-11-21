module

public import Sic.Core.Typing
import Sic.Core.Results.Extension
import Sic.Core.Syntax.Signature

/-!
# Typing Along the Signatures

The judgments in a context of annex 15 of RFC 36, and the judgment of the destructors of a block,
hold in every well-formed signature that has the entries of theirs: the typing reads its signature
only by the entries that it has, the constants, the declared types, the data types, the codata
types and the prelude, so that a signature with more entries gives the same premises, and the rule
of the empty context is the only one that asks that the signature be well formed.

The judgment `⊢ Σ` checks each entry in the signature before it, while a later entry reads it in
its own signature, which has more entries: the lifting of a codata type is declared after the
type, whose parameters and destructors it reads.
The proof is by induction on the derivations of all the judgments, `Derivable.extensionStable`.

ADE prove that their judgments hold in every extension of their context of definitions.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- What a judgment in a context, or the judgment of the destructors of a block, says in a
well-formed signature that has the entries of its own: that it holds there. -/
def Judgment.ExtensionStable : Judgment → Prop
  | wfCtx sig ctx => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' → WfCtx sig' ctx
  | wfType sig ctx A => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' → WfType sig' ctx A
  | eqType sig ctx A B => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' → EqType sig' ctx A B
  | hasType sig ctx t A => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' → HasType sig' ctx t A
  | eqTerm sig ctx t u A => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      EqTerm sig' ctx t u A
  | hasArgs sig ctx ts Θ => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      HasArgs sig' ctx ts Θ
  | eqArgs sig ctx ts us Θ => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      EqArgs sig' ctx ts us Θ
  | hasInstanceArgs sig ctx as params => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      HasInstanceArgs sig' ctx as params
  | eqInstanceArgs sig ctx as₁ as₂ params => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      EqInstanceArgs sig' ctx as₁ as₂ params
  | wfTelescope sig ctx Θ κ => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      WfTelescope sig' ctx Θ κ
  | wfTelescopeSorts sig ctx Θ κs l => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      WfTelescopeSorts sig' ctx Θ κs l
  | eqTelescope sig ctx Θ₁ Θ₂ κ => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      EqTelescope sig' ctx Θ₁ Θ₂ κ
  | wfDestructors sig decl ι ν as ctx ds κ => ∀ {sig' : Signature}, sig ⊆ sig' → WfSig sig' →
      WfDestructors sig' decl ι @ν as ctx ds κ
  | _ => True

-- ADE: none.
/-- The judgments in a context, and the judgment of the destructors of a block, hold in every
well-formed signature that has the entries of theirs, by induction on their derivations. -/
theorem Derivable.extensionStable {J : Judgment} (h : Derivable J) : J.ExtensionStable := by
  induction h with
  | WfCtx.empty _ _ =>
    intro sig' hs hw
    exact .empty hw
  | WfCtx.var h h_ih =>
    intro sig' hs hw
    exact .var (h_ih hs hw)
  | WfCtx.secondOrder h h_ih =>
    intro sig' hs hw
    exact .secondOrder (h_ih hs hw)
  | WfType.univType h h_ih =>
    intro sig' hs hw
    exact .univType (h_ih hs hw)
  | WfType.propType h h_ih =>
    intro sig' hs hw
    exact .propType (h_ih hs hw)
  | EqType.refl h h_ih =>
    intro sig' hs hw
    exact .refl (h_ih hs hw)
  | EqType.symm h h_ih =>
    intro sig' hs hw
    exact .symm (h_ih hs hw)
  | EqType.trans h₁ h₂ h₁_ih h₂_ih =>
    intro sig' hs hw
    exact .trans (h₁_ih hs hw) (h₂_ih hs hw)
  | EqType.univType h h_ih =>
    intro sig' hs hw
    exact .univType (h_ih hs hw)
  | EqType.propType h h_ih =>
    intro sig' hs hw
    exact .propType (h_ih hs hw)
  | HasType.var hctx hx hctx_ih =>
    intro sig' hs hw
    exact .var (hctx_ih hs hw) hx
  | HasType.secondOrder hX hts hts_ih =>
    intro sig' hs hw
    exact .secondOrder hX (hts_ih hs hw)
  | HasType.const hctx h hq hl hp hctx_ih =>
    intro sig' hs hw
    exact .const (hctx_ih hs hw) (h.mono hs) hq hl hp
  | HasType.univ hctx hctx_ih =>
    intro sig' hs hw
    exact .univ (hctx_ih hs hw)
  | HasType.prop hctx hctx_ih =>
    intro sig' hs hw
    exact .prop (hctx_ih hs hw)
  | HasType.inst h hq hl hp hadm has has_ih =>
    intro sig' hs hw
    exact
    .inst ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw)
  | HasType.equality hA ht hu hA_ih ht_ih hu_ih =>
    intro sig' hs hw
    exact .equality (hA_ih hs hw) (ht_ih hs hw) (hu_ih hs hw)
  | HasType.reflProof hA ht hA_ih ht_ih =>
    intro sig' hs hw
    exact .reflProof (hA_ih hs hw) (ht_ih hs hw)
  | HasType.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro sig' hs hw
    exact
    .transp (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
      (ht_ih hs hw) (hu_ih hs hw)
  | HasType.propExt hA hB ht hu hA_ih hB_ih ht_ih hu_ih =>
    intro sig' hs hw
    exact
    .propExt (hA_ih hs hw) (hB_ih hs hw) (ht_ih hs hw) (hu_ih hs hw)
  | HasType.coind h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih
      hAt_ih ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih =>
    intro sig' hs hw
    exact
    .coind ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw) hh hA hAl
      (fun j T' A' hj hA' => (hAt_ih j T' A' hj hA' hs hw)) (ht₁_ih hs hw)
      (ht₂_ih hs hw) (ht_ih hs hw) hgl hgs hΘ hB
      (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn =>
        (hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn hs hw))
      (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg =>
        (hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg hs hw))
      (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg =>
        (hgr_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg hs hw))
  | HasType.ctor h hc hq hl hp hadm has hts has_ih hts_ih =>
    intro sig' hs hw
    exact
    .ctor ⟨hs h.1, h.2⟩ hc hq hl hp hadm (has_ih hs hw) (hts_ih hs hw)
  | HasType.recursor h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus hRs hut hκ has_ih ht_ih hCt_ih
      hut_ih =>
    intro sig' hs hw
    exact
    .recursor ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw) (ht_ih hs hw) hh hC
      hCl hCs (fun j T' C' hj hC' => (hCt_ih j T' C' hj hC' hs hw)) hul hus
      (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
        Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
      (fun i j T' con C' u hi hC' hu => (hut_ih i j T' con C' u hi hC' hu hs hw)) hκ
  | HasType.obs h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih =>
    intro sig' hs hw
    exact
    .obs ⟨hs h.1, h.2⟩ hq hl hp hadm hd (has_ih hs hw) (ht_ih hs hw)
      (hbs_ih hs hw)
  | HasType.corec h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih
      hgt_ih =>
    intro sig' hs hw
    exact
    .corec ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
      (has_ih hs hw) hh hS (hss_ih hs hw) hSl hSs
      (fun j T' ps'' S' hj hS' => (hSt_ih j T' ps'' S' hj hS' hs hw)) hgl hgs
      (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
        (hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hs hw))
  | HasType.conv ht h ht_ih h_ih =>
    intro sig' hs hw
    exact .conv (ht_ih hs hw) (h_ih hs hw)
  | EqTerm.refl h h_ih =>
    intro sig' hs hw
    exact .refl (h_ih hs hw)
  | EqTerm.symm h h_ih =>
    intro sig' hs hw
    exact .symm (h_ih hs hw)
  | EqTerm.trans h₁ h₂ h₁_ih h₂_ih =>
    intro sig' hs hw
    exact .trans (h₁_ih hs hw) (h₂_ih hs hw)
  | EqTerm.conv h hA h_ih hA_ih =>
    intro sig' hs hw
    exact .conv (h_ih hs hw) (hA_ih hs hw)
  | EqTerm.irr ht hu hA ht_ih hu_ih hA_ih =>
    intro sig' hs hw
    exact .irr (ht_ih hs hw) (hu_ih hs hw) (hA_ih hs hw)
  | EqTerm.secondOrder hX hts hts_ih =>
    intro sig' hs hw
    exact .secondOrder hX (hts_ih hs hw)
  | EqTerm.delta hctx h hq hl hp hctx_ih =>
    intro sig' hs hw
    exact .delta (hctx_ih hs hw) (hs h) hq hl hp
  | EqTerm.const hctx h hq hl₁ hl₂ hp hls hctx_ih =>
    intro sig' hs hw
    exact
    .const (hctx_ih hs hw) (h.mono hs) hq hl₁ hl₂ hp hls
  | EqTerm.univ hctx hl hctx_ih =>
    intro sig' hs hw
    exact .univ (hctx_ih hs hw) hl
  | EqTerm.prop hctx hl hctx_ih =>
    intro sig' hs hw
    exact .prop (hctx_ih hs hw) hl
  | EqTerm.inst h hq hl₁ hl₂ hp hadm has hls has_ih =>
    intro sig' hs hw
    exact
    .inst ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
  | EqTerm.equality hA ht hu hl hA_ih ht_ih hu_ih =>
    intro sig' hs hw
    exact
    .equality (hA_ih hs hw) (ht_ih hs hw) (hu_ih hs hw) hl
  | EqTerm.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro sig' hs hw
    exact
    .transp (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
      (ht_ih hs hw) (hu_ih hs hw)
  | EqTerm.transpSame hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih =>
    intro sig' hs hw
    exact
    .transpSame (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
      (ht_ih hs hw) (hu_ih hs hw) (hCC_ih hs hw)
  | EqTerm.ctor h hc hq hl₁ hl₂ hp hadm has hls hts has_ih hts_ih =>
    intro sig' hs hw
    exact
    .ctor ⟨hs h.1, h.2⟩ hc hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
      (hts_ih hs hw)
  | EqTerm.recursor h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁
      hus₂ hes hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih =>
    intro sig' hs hw
    exact
    .recursor ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
      (ht_ih hs hw) hh hC hCl₁ hCl₂ hCs₁ hCs₂
      (fun j T' C₁' C₂' hj hC₁ hC₂ => (hCt_ih j T' C₁' C₂' hj hC₁ hC₂ hs hw)) hul₁ hul₂
      hus₁ hus₂ hes
      (fun i j T' con hi =>
        (hRs₁ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
      (fun i j T' con hi =>
        (hRs₂ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
      (fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ =>
        (hut_ih i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ hs hw)) hκ
  | EqTerm.obs h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih =>
    intro sig' hs hw
    exact
    .obs ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm hd (has_ih hs hw) hls (ht_ih hs hw)
      (hbs_ih hs hw)
  | EqTerm.corec h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁
      hgl₂ hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih =>
    intro sig' hs hw
    exact
    .corec ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (fun hr e he => hs (hpre hr e he))
      (has_ih hs hw) hls hh hS₁ hS₂ (hss_ih hs hw) hSl₁ hSl₂ hSs hSk
      (fun j T' ps'' S₁' hj hS' => (hSt_ih j T' ps'' S₁' hj hS' hs hw))
      (fun j T' ps'' S₁' S₂' hj hS₁' hS₂' =>
        (hSe_ih j T' ps'' S₁' S₂' hj hS₁' hS₂' hs hw)) hgl₁ hgl₂ hgs
      (fun i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂ =>
        (hgt_ih i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂ hs hw))
  | EqTerm.iota h hc hq hl hp hadm has hts hi hC hu hrs hCl hCs hCt hul hus hRs hut hκ has_ih hts_ih
      hCt_ih hut_ih =>
    intro sig' hs hw
    exact
    .iota ⟨hs h.1, h.2⟩ hc hq hl hp hadm (has_ih hs hw) (hts_ih hs hw) hi hC
      hu (Terms.ResultTerms.ofTypeDeclarations (fun _ h => hs h) hrs) hCl hCs
      (fun j T' C' hj hC' => (hCt_ih j T' C' hj hC' hs hw)) hul hus
      (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
        Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
      (fun i j T' con C' u hi hC' hu => (hut_ih i j T' con C' u hi hC' hu hs hw)) hκ
  | EqTerm.etaCtor h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus hRs hut hκ has_ih
      ht_ih he_ih hCt_ih hut_ih =>
    intro sig' hs hw
    exact
    .etaCtor ⟨hs h.1, h.2⟩ hc hq hl hp hadm hr (has_ih hs hw) (ht_ih hs hw)
      (he_ih hs hw) hi hC hu hCl hCs
      (fun j T' C' hj hC' => (hCt_ih j T' C' hj hC' hs hw)) hul hus
      (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
        Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
      (fun i j T' con C' u hi hC' hu => (hut_ih i j T' con C' u hi hC' hu hs hw)) hκ
  | EqTerm.beta h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih
      hss_ih hbs_ih hSt_ih hgt_ih =>
    intro sig' hs hw
    exact
    .beta ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
      (has_ih hs hw) hh hS (hss_ih hs hw) hi hd hg (hbs_ih hs hw) hSl hSs
      (fun j T' ps'' S' hj hS' => (hSt_ih j T' ps'' S' hj hS' hs hw)) hgl hgs
      (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
        (hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hs hw))
  | EqTerm.etaObs h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih =>
    intro sig' hs hw
    exact
    .etaObs ⟨hs h.1, h.2⟩ hq hl hp hadm hr (has_ih hs hw) (ht_ih hs hw)
      (hu_ih hs hw)
      (fun d p q ς ps' Ξ Θ B ψ hd => (hobs_ih d p q ς ps' Ξ Θ B ψ hd hs hw))
  | HasArgs.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | HasArgs.cons ht hts ht_ih hts_ih =>
    intro sig' hs hw
    exact .cons (ht_ih hs hw) (hts_ih hs hw)
  | EqArgs.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | EqArgs.cons ht hts ht_ih hts_ih =>
    intro sig' hs hw
    exact .cons (ht_ih hs hw) (hts_ih hs hw)
  | HasInstanceArgs.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | HasInstanceArgs.var has ha has_ih ha_ih =>
    intro sig' hs hw
    exact .var (has_ih hs hw) (ha_ih hs hw)
  | HasInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro sig' hs hw
    exact .secondOrder (has_ih hs hw) (hB_ih hs hw)
  | EqInstanceArgs.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | EqInstanceArgs.var has ha has_ih ha_ih =>
    intro sig' hs hw
    exact .var (has_ih hs hw) (ha_ih hs hw)
  | EqInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro sig' hs hw
    exact .secondOrder (has_ih hs hw) (hB_ih hs hw)
  | WfTelescope.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | WfTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro sig' hs hw
    exact .cons (hA_ih hs hw) hκ (hΘ_ih hs hw) hp
  | WfTelescopeSorts.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | WfTelescopeSorts.cons hA hl hΘ hp hA_ih hΘ_ih =>
    intro sig' hs hw
    exact .cons (hA_ih hs hw) hl (hΘ_ih hs hw) hp
  | EqTelescope.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | EqTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro sig' hs hw
    exact .cons (hA_ih hs hw) hκ (hΘ_ih hs hw) hp
  | WfDestructors.nil hctx hctx_ih =>
    intro sig' hs hw
    exact .nil (hctx_ih hs hw)
  | WfDestructors.cons hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih =>
    intro sig' hs hw
    exact
    .cons hn hν (hΘ_ih hs hw) (hB_ih hs hw) hκ hp (hds_ih hs hw)
  | WfDestructors.nested hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih =>
    intro sig' hs hw
    exact
    .nested hn hν (hΘ_ih hs hw) (hB_ih hs hw) hκ hp (hds_ih hs hw)
  | WfDestructors.recursive hD hΘ hp hds hΘ_ih hds_ih =>
    intro sig' hs hw
    exact
    .recursive hD (hΘ_ih hs hw) hp (hds_ih hs hw)
  | _ => trivial

-- ADE: `defn-wk′`, `defn-wk″`, `defn-wkTerm`, `defn-wkEq` and `defn-wkEqTerm`, in
-- `Definition/Typed/Weakening/Definition.agda`, for their judgments.
/-- The judgments in a context, and the judgment of the destructors of a block, hold in every
well-formed signature that has the entries of theirs. -/
structure StableUnderExtension : Prop where
  /-- A well-formed context is well formed in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\Gamma` -/
  wfCtx : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    sig ⊆ sig' → WfSig sig' → WfCtx sig ctx → WfCtx sig' ctx
  /-- A type is a type in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.A` -/
  wfType : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ},
    sig ⊆ sig' → WfSig sig' → WfType sig ctx A → WfType sig' ctx A
  /-- Equal types are equal in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.A_\equiv` -/
  eqType : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ},
    sig ⊆ sig' → WfSig sig' → EqType sig ctx A B → EqType sig' ctx A B
  /-- A term of a type is a term of it in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.t` -/
  hasType : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    sig ⊆ sig' → WfSig sig' → HasType sig ctx t A → HasType sig' ctx t A
  /-- Equal terms are equal in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.t_\equiv` -/
  eqTerm : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ},
    sig ⊆ sig' → WfSig sig' → EqTerm sig ctx t u A → EqTerm sig' ctx t u A
  /-- Arguments of a telescope are arguments of it in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\bar t` -/
  hasArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps},
    sig ⊆ sig' → WfSig sig' → HasArgs sig ctx ts Θ → HasArgs sig' ctx ts Θ
  /-- Equal arguments of a telescope are equal in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\bar t_\equiv` -/
  eqArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps},
    sig ⊆ sig' → WfSig sig' → EqArgs sig ctx ts us Θ → EqArgs sig' ctx ts us Θ
  /-- Arguments of an instance are arguments of its parameters in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\bar a` -/
  hasInstanceArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    sig ⊆ sig' → WfSig sig' → HasInstanceArgs sig ctx as params →
      HasInstanceArgs sig' ctx as params
  /-- Equal arguments of instances are equal in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    sig ⊆ sig' → WfSig sig' → EqInstanceArgs sig ctx as₁ as₂ params →
      EqInstanceArgs sig' ctx as₁ as₂ params
  /-- A telescope in a sort is in this sort in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\Theta` -/
  wfTelescope : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
    sig ⊆ sig' → WfSig sig' → WfTelescope sig ctx Θ κ → WfTelescope sig' ctx Θ κ
  /-- A telescope in sorts is in these sorts in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\Theta_{\bar\kappa}` -/
  wfTelescopeSorts : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k},
    sig ⊆ sig' → WfSig sig' → WfTelescopeSorts sig ctx Θ κs l →
      WfTelescopeSorts sig' ctx Θ κs l
  /-- Equal telescopes in a sort are equal in a signature with more entries.
  RFC: `\mathsf{ext}_\vdash.\Theta_\equiv` -/
  eqTelescope : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    sig ⊆ sig' → WfSig sig' → EqTelescope sig ctx Θ₁ Θ₂ κ → EqTelescope sig' ctx Θ₁ Θ₂ κ
  /-- The destructors of a codata type in a sort are in this sort in a signature with more
  entries.
  RFC: `\mathsf{ext}_\vdash.\bar d` -/
  wfDestructors : ∀ {sig sig' : Signature} {decl : TypeDeclaration}
    {ι : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
    sig ⊆ sig' → WfSig sig' → WfDestructors sig decl ι @ν as ctx ds κ →
      WfDestructors sig' decl ι @ν as ctx ds κ

-- ADE: `defn-wk′`, `defn-wk″`, `defn-wkTerm`, `defn-wkEq` and `defn-wkEqTerm`, in
-- `Definition/Typed/Weakening/Definition.agda`, for their judgments.
/-- The judgments in a context, and the judgment of the destructors of a block, hold in every
well-formed signature that has the entries of theirs.
RFC: `\mathsf{ext}_\vdash.\Gamma`
RFC: `\mathsf{ext}_\vdash.A`
RFC: `\mathsf{ext}_\vdash.A_\equiv`
RFC: `\mathsf{ext}_\vdash.t`
RFC: `\mathsf{ext}_\vdash.t_\equiv`
RFC: `\mathsf{ext}_\vdash.\bar t`
RFC: `\mathsf{ext}_\vdash.\bar t_\equiv`
RFC: `\mathsf{ext}_\vdash.\bar a`
RFC: `\mathsf{ext}_\vdash.\bar a_\equiv`
RFC: `\mathsf{ext}_\vdash.\Theta`
RFC: `\mathsf{ext}_\vdash.\Theta_{\bar\kappa}`
RFC: `\mathsf{ext}_\vdash.\Theta_\equiv`
RFC: `\mathsf{ext}_\vdash.\bar d` -/
theorem stableUnderExtension : StableUnderExtension :=
  ⟨fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw, fun hs hw h => h.extensionStable hs hw,
    fun hs hw h => h.extensionStable hs hw⟩

end Sic.Core
