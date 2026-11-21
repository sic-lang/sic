module

public import Sic.Core.Typing
import Sic.Core.Results.Extension
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Induction

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
The proof is by the induction on the derivations, `Derivations.induction`, with the fields of
`StableUnderExtension` as its motives.

ADE prove that their judgments hold in every extension of their context of definitions.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

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
theorem stableUnderExtension : StableUnderExtension := by
  suffices H : Derivations.Conclusion
      (wfSig := fun _ _ => True)
      (wfConstantDefinition := fun _ _ _ => True)
      (wfConstantDeclaration := fun _ _ _ => True)
      (wfCtx := fun sig {k Γ} ctx _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' → WfCtx sig' ctx)
      (wfType := fun sig {k Γ} ctx A _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' → WfType sig' ctx A)
      (eqType := fun sig {k Γ} ctx A B _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' → EqType sig' ctx A B)
      (hasType := fun sig {k Γ} ctx t A _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        HasType sig' ctx t A)
      (eqTerm := fun sig {k Γ} ctx t u A _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        EqTerm sig' ctx t u A)
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        HasArgs sig' ctx ts Θ)
      (eqArgs := fun sig {k Γ ps} ctx ts us Θ _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        EqArgs sig' ctx ts us Θ)
      (hasInstanceArgs := fun sig {k Γ Δ} ctx as params _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        HasInstanceArgs sig' ctx as params)
      (eqInstanceArgs := fun sig {k Γ Δ} ctx as₁ as₂ params _ => ∀ {sig'}, sig ⊆ sig' →
        WfSig sig' → EqInstanceArgs sig' ctx as₁ as₂ params)
      (wfTelescope := fun sig {k Γ ps} ctx Θ κ _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        WfTelescope sig' ctx Θ κ)
      (wfTelescopeSorts := fun sig {k Γ ps} ctx Θ κs l _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        WfTelescopeSorts sig' ctx Θ κs l)
      (eqTelescope := fun sig {k Γ ps} ctx Θ₁ Θ₂ κ _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        EqTelescope sig' ctx Θ₁ Θ₂ κ)
      (wfFields := fun _ _ _ _ _ _ _ _ _ _ => True)
      (wfDestructors := fun sig decl ι {Γ ns} ν as ctx ds κ _ => ∀ {sig'}, sig ⊆ sig' → WfSig sig' →
        WfDestructors sig' decl ι @ν as ctx ds κ)
      (wfTypeDeclaration := fun _ _ _ => True) from
    ⟨fun hs hw h => H.wfCtx h hs hw, fun hs hw h => H.wfType h hs hw,
      fun hs hw h => H.eqType h hs hw, fun hs hw h => H.hasType h hs hw,
      fun hs hw h => H.eqTerm h hs hw, fun hs hw h => H.hasArgs h hs hw,
      fun hs hw h => H.eqArgs h hs hw, fun hs hw h => H.hasInstanceArgs h hs hw,
      fun hs hw h => H.eqInstanceArgs h hs hw, fun hs hw h => H.wfTelescope h hs hw,
      fun hs hw h => H.wfTelescopeSorts h hs hw, fun hs hw h => H.eqTelescope h hs hw,
      fun hs hw h => H.wfDestructors h hs hw⟩
  apply Derivations.induction
  case wfCtx_empty => exact fun h h_ih => fun hs hw => .empty hw
  case wfCtx_var => exact fun h h_ih => fun hs hw => .var (h_ih hs hw)
  case wfCtx_secondOrder => exact fun h h_ih => fun hs hw => .secondOrder (h_ih hs hw)
  case wfType_univType => exact fun h h_ih => fun hs hw => .univType (h_ih hs hw)
  case wfType_propType => exact fun h h_ih => fun hs hw => .propType (h_ih hs hw)
  case eqType_refl => exact fun h h_ih => fun hs hw => .refl (h_ih hs hw)
  case eqType_symm => exact fun h h_ih => fun hs hw => .symm (h_ih hs hw)
  case eqType_trans =>
    exact fun h₁ h₂ h₁_ih h₂_ih => fun hs hw =>
      .trans (h₁_ih hs hw) (h₂_ih hs hw)
  case eqType_univType => exact fun h h_ih => fun hs hw => .univType (h_ih hs hw)
  case eqType_propType => exact fun h h_ih => fun hs hw => .propType (h_ih hs hw)
  case hasType_var => exact fun hctx hx hctx_ih => fun hs hw => .var (hctx_ih hs hw) hx
  case hasType_secondOrder => exact fun hX hts hts_ih => fun hs hw => .secondOrder hX (hts_ih hs hw)
  case hasType_const =>
    exact fun hctx h hq hl hp hctx_ih => fun hs hw =>
      .const (hctx_ih hs hw) (h.mono hs) hq hl hp
  case hasType_univ => exact fun hctx hctx_ih => fun hs hw => .univ (hctx_ih hs hw)
  case hasType_prop => exact fun hctx hctx_ih => fun hs hw => .prop (hctx_ih hs hw)
  case hasType_inst =>
    exact fun h hq hl hp hadm has has_ih => fun hs hw =>
      .inst ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw)
  case hasType_equality =>
    exact fun hA ht hu hA_ih ht_ih hu_ih => fun hs hw =>
      .equality (hA_ih hs hw) (ht_ih hs hw) (hu_ih hs hw)
  case hasType_reflProof =>
    exact fun hA ht hA_ih ht_ih => fun hs hw =>
      .reflProof (hA_ih hs hw) (ht_ih hs hw)
  case hasType_transp =>
    refine fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih => fun hs hw => ?_
    exact .transp (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
        (ht_ih hs hw) (hu_ih hs hw)
  case hasType_propExt =>
    exact fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => fun hs hw =>
      .propExt (hA_ih hs hw) (hB_ih hs hw) (ht_ih hs hw) (hu_ih hs hw)
  case hasType_coind =>
    refine fun h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih
        ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih => fun hs hw => ?_
    exact .coind ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw) hh hA hAl
        (fun j T' A' hj hA' => hAt_ih j T' A' hj hA' hs hw) (ht₁_ih hs hw)
        (ht₂_ih hs hw) (ht_ih hs hw) hgl hgs hΘ hB
        (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn =>
          hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn hs hw)
        (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg =>
          hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg hs hw)
        (fun i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg =>
          hgr_ih i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg hs hw)
  case hasType_ctor =>
    exact fun h hc hq hl hp hadm has _ hts has_ih hts_ih => fun hs hw =>
      .ctor ⟨hs h.1, h.2⟩ hc hq hl hp hadm (has_ih hs hw) (hts_ih hs hw)
  case hasType_recursor =>
    refine fun h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus _ hRs hut hκ has_ih ht_ih hCt_ih
        hut_ih => fun hs hw => ?_
    exact .recursor ⟨hs h.1, h.2⟩ hq hl hp hadm (has_ih hs hw) (ht_ih hs hw) hh hC
        hCl hCs (fun j T' C' hj hC' => hCt_ih j T' C' hj hC' hs hw) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hut_ih i j T' con C' u hi hC' hu hs hw) hκ
  case hasType_obs =>
    refine fun h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih => fun hs hw => ?_
    exact .obs ⟨hs h.1, h.2⟩ hq hl hp hadm hd (has_ih hs hw) (ht_ih hs hw)
        (hbs_ih hs hw)
  case hasType_corec =>
    refine fun h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih
        hgt_ih => fun hs hw => ?_
    exact .corec ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
        (has_ih hs hw) hh hS (hss_ih hs hw) hSl hSs
        (fun j T' ps'' S' hj hS' => hSt_ih j T' ps'' S' hj hS' hs hw) hgl hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
          hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hs hw)
  case hasType_conv => exact fun ht h ht_ih h_ih => fun hs hw => .conv (ht_ih hs hw) (h_ih hs hw)
  case eqTerm_refl => exact fun h h_ih => fun hs hw => .refl (h_ih hs hw)
  case eqTerm_symm => exact fun h h_ih => fun hs hw => .symm (h_ih hs hw)
  case eqTerm_trans =>
    exact fun h₁ h₂ h₁_ih h₂_ih => fun hs hw =>
      .trans (h₁_ih hs hw) (h₂_ih hs hw)
  case eqTerm_conv => exact fun h hA h_ih hA_ih => fun hs hw => .conv (h_ih hs hw) (hA_ih hs hw)
  case eqTerm_irr =>
    exact fun ht hu hA ht_ih hu_ih hA_ih => fun hs hw =>
      .irr (ht_ih hs hw) (hu_ih hs hw) (hA_ih hs hw)
  case eqTerm_secondOrder => exact fun hX hts hts_ih => fun hs hw => .secondOrder hX (hts_ih hs hw)
  case eqTerm_delta =>
    exact fun hctx h hq hl hp hctx_ih => fun hs hw =>
      .delta (hctx_ih hs hw) (hs h) hq hl hp
  case eqTerm_const =>
    exact fun hctx h hq hl₁ hl₂ hp hls hctx_ih => fun hs hw =>
      .const (hctx_ih hs hw) (h.mono hs) hq hl₁ hl₂ hp hls
  case eqTerm_univ => exact fun hctx hl hctx_ih => fun hs hw => .univ (hctx_ih hs hw) hl
  case eqTerm_prop => exact fun hctx hl hctx_ih => fun hs hw => .prop (hctx_ih hs hw) hl
  case eqTerm_inst =>
    exact fun h hq hl₁ hl₂ hp hadm has hls has_ih => fun hs hw =>
      .inst ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
  case eqTerm_equality =>
    exact fun hA ht hu hl hA_ih ht_ih hu_ih => fun hs hw =>
      .equality (hA_ih hs hw) (ht_ih hs hw) (hu_ih hs hw) hl
  case eqTerm_transp =>
    refine fun hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih => fun hs hw => ?_
    exact .transp (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
        (ht_ih hs hw) (hu_ih hs hw)
  case eqTerm_transpSame =>
    refine fun hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih => fun hs
        hw => ?_
    exact .transpSame (hA_ih hs hw) (ht₁_ih hs hw) (ht₂_ih hs hw) (hC_ih hs hw)
        (ht_ih hs hw) (hu_ih hs hw) (hCC_ih hs hw)
  case eqTerm_ctor =>
    refine fun h hc hq hl₁ hl₂ hp hadm has hls _ _ hts has_ih hts_ih => fun hs hw => ?_
    exact .ctor ⟨hs h.1, h.2⟩ hc hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
        (hts_ih hs hw)
  case eqTerm_recursor =>
    refine fun h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes
        _ _ hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih => fun hs hw => ?_
    exact .recursor ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (has_ih hs hw) hls
        (ht_ih hs hw) hh hC hCl₁ hCl₂ hCs₁ hCs₂
        (fun j T' C₁' C₂' hj hC₁ hC₂ => hCt_ih j T' C₁' C₂' hj hC₁ hC₂ hs hw) hul₁ hul₂
        hus₁ hus₂ hes
        (fun i j T' con hi =>
          (hRs₁ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con hi =>
          (hRs₂ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ =>
          hut_ih i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ hs hw) hκ
  case eqTerm_obs =>
    refine fun h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih => fun hs hw => ?_
    exact .obs ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm hd (has_ih hs hw) hls (ht_ih hs hw)
        (hbs_ih hs hw)
  case eqTerm_corec =>
    refine fun h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂
        hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih => fun hs hw => ?_
    exact .corec ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (fun hr e he => hs (hpre hr e he))
        (has_ih hs hw) hls hh hS₁ hS₂ (hss_ih hs hw) hSl₁ hSl₂ hSs hSk
        (fun j T' ps'' S₁' hj hS' => hSt_ih j T' ps'' S₁' hj hS' hs hw)
        (fun j T' ps'' S₁' S₂' hj hS₁' hS₂' =>
          hSe_ih j T' ps'' S₁' S₂' hj hS₁' hS₂' hs hw) hgl₁ hgl₂ hgs
        (fun i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂ =>
          hgt_ih i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂ hs hw)
  case eqTerm_iota =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ Cs us κ i j C h hc hq hl hp hadm u has ts hts
      hi hC hu rs hrs hCl hCs hCt hul hus Rs hRs hut hκ has_ih hts_ih hCt_ih hut_ih sig' hs hw
    exact .iota ⟨hs h.1, h.2⟩ hc hq hl hp hadm (has_ih hs hw) (hts_ih hs hw) hi hC
        hu (Terms.ResultTerms.ofTypeDeclarations (fun _ h => hs h) hrs) hCl hCs
        (fun j T' C' hj hC' => hCt_ih j T' C' hj hC' hs hw) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hut_ih i j T' con C' u hi hC' hu hs hw) hκ
  case eqTerm_etaCtor =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ t Cs us κ i j C e h hc hq hl hp hadm hr has ht
      he hi hC hu hCl hCs hCt hul hus Rs hRs hut hκ has_ih ht_ih he_ih hCt_ih hut_ih sig' hs hw
    exact .etaCtor ⟨hs h.1, h.2⟩ hc hq hl hp hadm hr (has_ih hs hw) (ht_ih hs hw)
        (he_ih hs hw) hi hC hu hCl hCs
        (fun j T' C' hj hC' => hCt_ih j T' C' hj hC' hs hw) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hut_ih i j T' con C' u hi hC' hu hs hw) hκ
  case eqTerm_beta =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' i ps' S ss d p q ς ps₀ Ξ₀ Θ₀ B₀ ψ₀ g bs h hq
      hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih hss_ih hbs_ih hSt_ih
      hgt_ih sig' hs hw
    exact .beta ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
        (has_ih hs hw) hh hS (hss_ih hs hw) hi hd hg (hbs_ih hs hw) hSl hSs
        (fun j T' ps'' S' hj hS' => hSt_ih j T' ps'' S' hj hS' hs hw) hgl hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
          hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg hs hw)
  case eqTerm_etaObs =>
    refine fun h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih => fun hs hw => ?_
    exact .etaObs ⟨hs h.1, h.2⟩ hq hl hp hadm hr (has_ih hs hw) (ht_ih hs hw)
        (hu_ih hs hw)
        (fun d p q ς ps' Ξ Θ B ψ hd => hobs_ih d p q ς ps' Ξ Θ B ψ hd hs hw)
  case hasArgs_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case hasArgs_cons =>
    exact fun ht hts ht_ih hts_ih => fun hs hw =>
      .cons (ht_ih hs hw) (hts_ih hs hw)
  case eqArgs_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case eqArgs_cons =>
    exact fun ht hts ht_ih hts_ih => fun hs hw =>
      .cons (ht_ih hs hw) (hts_ih hs hw)
  case hasInstanceArgs_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case hasInstanceArgs_var =>
    exact fun has ha has_ih ha_ih => fun hs hw =>
      .var (has_ih hs hw) (ha_ih hs hw)
  case hasInstanceArgs_secondOrder =>
    exact fun has hB has_ih hB_ih => fun hs hw =>
      .secondOrder (has_ih hs hw) (hB_ih hs hw)
  case eqInstanceArgs_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case eqInstanceArgs_var =>
    exact fun has ha has_ih ha_ih => fun hs hw =>
      .var (has_ih hs hw) (ha_ih hs hw)
  case eqInstanceArgs_secondOrder =>
    exact fun has hB has_ih hB_ih => fun hs hw =>
      .secondOrder (has_ih hs hw) (hB_ih hs hw)
  case wfTelescope_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case wfTelescope_cons =>
    exact fun hA hκ hΘ hp hA_ih hΘ_ih => fun hs hw =>
      .cons (hA_ih hs hw) hκ (hΘ_ih hs hw) hp
  case wfTelescopeSorts_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case wfTelescopeSorts_cons =>
    exact fun hA hl hΘ hp hA_ih hΘ_ih => fun hs hw =>
      .cons (hA_ih hs hw) hl (hΘ_ih hs hw) hp
  case eqTelescope_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case eqTelescope_cons =>
    exact fun hA hκ hΘ hp hA_ih hΘ_ih => fun hs hw =>
      .cons (hA_ih hs hw) hκ (hΘ_ih hs hw) hp
  case wfDestructors_nil => exact fun hctx hctx_ih => fun hs hw => .nil (hctx_ih hs hw)
  case wfDestructors_cons =>
    exact fun hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih => fun hs hw =>
      .cons hn hν (hΘ_ih hs hw) (hB_ih hs hw) hκ hp (hds_ih hs hw)
  case wfDestructors_nested =>
    exact fun hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih => fun hs hw =>
      .nested hn hν (hΘ_ih hs hw) (hB_ih hs hw) hκ hp (hds_ih hs hw)
  case wfDestructors_recursive =>
    exact fun hD hΘ hp hds hΘ_ih hds_ih => fun hs hw =>
      .recursive hD (hΘ_ih hs hw) hp (hds_ih hs hw)
  case wfSig_empty | wfSig_constantDefinition | wfSig_constantDeclaration | wfSig_typeDeclaration |
      wfSig_lifting | wfConstantDefinition_intro | wfConstantDeclaration_intro | wfFields_nil |
      wfFields_cons | wfFields_recursive | wfFields_nested | wfTypeDeclaration_data |
      wfTypeDeclaration_codata => intros; trivial

end Sic.Core
