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
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.

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
theorem stableUnderExtension : StableUnderExtension :=
  ⟨wfCtx, wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs,
    wfTelescope, wfTelescopeSorts, eqTelescope, wfDestructors⟩
where
  wfCtx {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hs : sig ⊆ sig')
      (hw : WfSig sig') : WfCtx sig ctx → WfCtx sig' ctx
    | .empty _ => .empty hw
    | .var h => .var (wfType hs hw h)
    | .secondOrder h => .secondOrder (wfType hs hw h)
  wfType {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (hs : sig ⊆ sig') (hw : WfSig sig') : WfType sig ctx A → WfType sig' ctx A
    | .univType h => .univType (hasType hs hw h)
    | .propType h => .propType (hasType hs hw h)
  eqType {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      (hs : sig ⊆ sig') (hw : WfSig sig') : EqType sig ctx A B → EqType sig' ctx A B
    | .refl h => .refl (wfType hs hw h)
    | .symm h => .symm (eqType hs hw h)
    | .trans h₁ h₂ => .trans (eqType hs hw h₁) (eqType hs hw h₂)
    | .univType h => .univType (eqTerm hs hw h)
    | .propType h => .propType (eqTerm hs hw h)
  hasType {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
      (hs : sig ⊆ sig') (hw : WfSig sig') : HasType sig ctx t A → HasType sig' ctx t A
    | .var hctx hx => .var (wfCtx hs hw hctx) hx
    | .secondOrder hX hts => .secondOrder hX (hasArgs hs hw hts)
    | .const hctx h hq hl hp => .const (wfCtx hs hw hctx) (h.mono hs) hq hl hp
    | .univ hctx => .univ (wfCtx hs hw hctx)
    | .prop hctx => .prop (wfCtx hs hw hctx)
    | .inst h hq hl hp hadm has =>
      .inst ⟨hs h.1, h.2⟩ hq hl hp hadm (hasInstanceArgs hs hw has)
    | .equality hA ht hu => .equality (hasType hs hw hA) (hasType hs hw ht) (hasType hs hw hu)
    | .reflProof hA ht => .reflProof (hasType hs hw hA) (hasType hs hw ht)
    | .transp hA ht₁ ht₂ hC ht hu =>
      .transp (hasType hs hw hA) (hasType hs hw ht₁) (hasType hs hw ht₂) (hasType hs hw hC)
        (hasType hs hw ht) (hasType hs hw hu)
    | .ctor h hc hq hl hp hadm has hts =>
      .ctor ⟨hs h.1, h.2⟩ hc hq hl hp hadm (hasInstanceArgs hs hw has) (hasArgs hs hw hts)
    | .recursor h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus hRs hut hκ =>
      .recursor ⟨hs h.1, h.2⟩ hq hl hp hadm (hasInstanceArgs hs hw has) (hasType hs hw ht) hh hC
        hCl hCs (fun j T' C' hj hC' => hasType hs hw (hCt j T' C' hj hC')) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hasType hs hw (hut i j T' con C' u hi hC' hu)) hκ
    | .obs h hq hl hp hadm hd has ht hbs =>
      .obs ⟨hs h.1, h.2⟩ hq hl hp hadm hd (hasInstanceArgs hs hw has) (hasType hs hw ht)
        (hasArgs hs hw hbs)
    | .corec h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt =>
      .corec ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
        (hasInstanceArgs hs hw has) hh hS (hasArgs hs hw hss) hSl hSs
        (fun j T' ps'' S' hj hS' => wfTelescopeSorts hs hw (hSt j T' ps'' S' hj hS')) hgl hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
          hasType hs hw (hgt i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg))
    | .conv ht h => .conv (hasType hs hw ht) (eqType hs hw h)
  eqTerm {sig sig' : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      (hs : sig ⊆ sig') (hw : WfSig sig') : EqTerm sig ctx t u A → EqTerm sig' ctx t u A
    | .refl h => .refl (hasType hs hw h)
    | .symm h => .symm (eqTerm hs hw h)
    | .trans h₁ h₂ => .trans (eqTerm hs hw h₁) (eqTerm hs hw h₂)
    | .conv h hA => .conv (eqTerm hs hw h) (eqType hs hw hA)
    | .irr ht hu hA => .irr (hasType hs hw ht) (hasType hs hw hu) (hasType hs hw hA)
    | .secondOrder hX hts => .secondOrder hX (eqArgs hs hw hts)
    | .delta hctx h hq hl hp => .delta (wfCtx hs hw hctx) (hs h) hq hl hp
    | .const hctx h hq hl₁ hl₂ hp hls =>
      .const (wfCtx hs hw hctx) (h.mono hs) hq hl₁ hl₂ hp hls
    | .univ hctx hl => .univ (wfCtx hs hw hctx) hl
    | .prop hctx hl => .prop (wfCtx hs hw hctx) hl
    | .inst h hq hl₁ hl₂ hp hadm has hls =>
      .inst ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (eqInstanceArgs hs hw has) hls
    | .equality hA ht hu hl =>
      .equality (eqTerm hs hw hA) (eqTerm hs hw ht) (eqTerm hs hw hu) hl
    | .transp hA ht₁ ht₂ hC ht hu =>
      .transp (eqTerm hs hw hA) (eqTerm hs hw ht₁) (eqTerm hs hw ht₂) (eqTerm hs hw hC)
        (eqTerm hs hw ht) (eqTerm hs hw hu)
    | .transpSame hA ht₁ ht₂ hC ht hu hCC =>
      .transpSame (hasType hs hw hA) (hasType hs hw ht₁) (hasType hs hw ht₂) (hasType hs hw hC)
        (hasType hs hw ht) (hasType hs hw hu) (eqTerm hs hw hCC)
    | .ctor h hc hq hl₁ hl₂ hp hadm has hls hts =>
      .ctor ⟨hs h.1, h.2⟩ hc hq hl₁ hl₂ hp hadm (eqInstanceArgs hs hw has) hls
        (eqArgs hs hw hts)
    | .recursor h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂
        hes hRs₁ hRs₂ hut hκ =>
      .recursor ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (eqInstanceArgs hs hw has) hls
        (eqTerm hs hw ht) hh hC hCl₁ hCl₂ hCs₁ hCs₂
        (fun j T' C₁' C₂' hj hC₁ hC₂ => eqTerm hs hw (hCt j T' C₁' C₂' hj hC₁ hC₂)) hul₁ hul₂
        hus₁ hus₂ hes
        (fun i j T' con hi =>
          (hRs₁ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con hi =>
          (hRs₂ i j T' con hi).imp fun _ => Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ =>
          eqTerm hs hw (hut i j T' con C' u₁ u₂ hi hC' hu₁ hu₂)) hκ
    | .obs h hq hl₁ hl₂ hp hadm hd has hls ht hbs =>
      .obs ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm hd (eqInstanceArgs hs hw has) hls (eqTerm hs hw ht)
        (eqArgs hs hw hbs)
    | .corec h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂
        hgs hgt =>
      .corec ⟨hs h.1, h.2⟩ hq hl₁ hl₂ hp hadm (fun hr e he => hs (hpre hr e he))
        (eqInstanceArgs hs hw has) hls hh hS₁ hS₂ (eqArgs hs hw hss) hSl₁ hSl₂ hSs hSk
        (fun j T' ps'' S₁' hj hS' => wfTelescopeSorts hs hw (hSt j T' ps'' S₁' hj hS'))
        (fun j T' ps'' S₁' S₂' hj hS₁' hS₂' =>
          eqTelescope hs hw (hSe j T' ps'' S₁' S₂' hj hS₁' hS₂')) hgl₁ hgl₂ hgs
        (fun i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂ =>
          eqTerm hs hw (hgt i j T' d ps'' S₁' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂))
    | .iota h hc hq hl hp hadm has hts hi hC hu hrs hCl hCs hCt hul hus hRs hut hκ =>
      .iota ⟨hs h.1, h.2⟩ hc hq hl hp hadm (hasInstanceArgs hs hw has) (hasArgs hs hw hts) hi hC
        hu (Terms.ResultTerms.ofTypeDeclarations (fun _ h => hs h) hrs) hCl hCs
        (fun j T' C' hj hC' => hasType hs hw (hCt j T' C' hj hC')) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hasType hs hw (hut i j T' con C' u hi hC' hu)) hκ
    | .etaCtor h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus hRs hut hκ =>
      .etaCtor ⟨hs h.1, h.2⟩ hc hq hl hp hadm hr (hasInstanceArgs hs hw has) (hasType hs hw ht)
        (hasType hs hw he) hi hC hu hCl hCs
        (fun j T' C' hj hC' => hasType hs hw (hCt j T' C' hj hC')) hul hus
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ =>
          Terms.ResultTypes.ofTypeDeclarations (fun _ h => hs h))
        (fun i j T' con C' u hi hC' hu => hasType hs hw (hut i j T' con C' u hi hC' hu)) hκ
    | .beta h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt =>
      .beta ⟨hs h.1, h.2⟩ hq hl hp hadm (fun hr e he => hs (hpre hr e he))
        (hasInstanceArgs hs hw has) hh hS (hasArgs hs hw hss) hi hd hg (hasArgs hs hw hbs) hSl hSs
        (fun j T' ps'' S' hj hS' => wfTelescopeSorts hs hw (hSt j T' ps'' S' hj hS')) hgl hgs
        (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg =>
          hasType hs hw (hgt i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg))
    | .etaObs h hq hl hp hadm hr has ht hu hobs =>
      .etaObs ⟨hs h.1, h.2⟩ hq hl hp hadm hr (hasInstanceArgs hs hw has) (hasType hs hw ht)
        (hasType hs hw hu)
        (fun d p q ς ps' Ξ Θ B ψ hd => eqTerm hs hw (hobs d p q ς ps' Ξ Θ B ψ hd))
  hasArgs {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} (hs : sig ⊆ sig') (hw : WfSig sig') :
      HasArgs sig ctx ts Θ → HasArgs sig' ctx ts Θ
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons ht hts => .cons (hasType hs hw ht) (hasArgs hs hw hts)
  eqArgs {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} (hs : sig ⊆ sig') (hw : WfSig sig') :
      EqArgs sig ctx ts us Θ → EqArgs sig' ctx ts us Θ
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons ht hts => .cons (eqTerm hs hw ht) (eqArgs hs hw hts)
  hasInstanceArgs {sig sig' : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} (hs : sig ⊆ sig') (hw : WfSig sig') :
      HasInstanceArgs sig ctx as params → HasInstanceArgs sig' ctx as params
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .var has ha => .var (hasInstanceArgs hs hw has) (hasType hs hw ha)
    | .secondOrder has hB => .secondOrder (hasInstanceArgs hs hw has) (hasType hs hw hB)
  eqInstanceArgs {sig sig' : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} (hs : sig ⊆ sig') (hw : WfSig sig') :
      EqInstanceArgs sig ctx as₁ as₂ params → EqInstanceArgs sig' ctx as₁ as₂ params
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .var has ha => .var (eqInstanceArgs hs hw has) (eqTerm hs hw ha)
    | .secondOrder has hB => .secondOrder (eqInstanceArgs hs hw has) (eqTerm hs hw hB)
  wfTelescope {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k} (hs : sig ⊆ sig')
      (hw : WfSig sig') : WfTelescope sig ctx Θ κ → WfTelescope sig' ctx Θ κ
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons hA hκ hΘ hp => .cons (hasType hs hw hA) hκ (wfTelescope hs hw hΘ) hp
  wfTelescopeSorts {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k}
      (hs : sig ⊆ sig') (hw : WfSig sig') :
      WfTelescopeSorts sig ctx Θ κs l → WfTelescopeSorts sig' ctx Θ κs l
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons hA hl hΘ hp => .cons (hasType hs hw hA) hl (wfTelescopeSorts hs hw hΘ) hp
  eqTelescope {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} (hs : sig ⊆ sig')
      (hw : WfSig sig') : EqTelescope sig ctx Θ₁ Θ₂ κ → EqTelescope sig' ctx Θ₁ Θ₂ κ
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons hA hκ hΘ hp => .cons (eqTerm hs hw hA) hκ (eqTelescope hs hw hΘ) hp
  wfDestructors {sig sig' : Signature} {decl : TypeDeclaration}
      {ι : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ}
      {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
      {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} (hs : sig ⊆ sig')
      (hw : WfSig sig') :
      WfDestructors sig decl ι @ν as ctx ds κ → WfDestructors sig' decl ι @ν as ctx ds κ
    | .nil hctx => .nil (wfCtx hs hw hctx)
    | .cons hn hν hΘ hB hκ hp hds =>
      .cons hn hν (wfTelescope hs hw hΘ) (hasType hs hw hB) hκ hp (wfDestructors hs hw hds)
    | .nested hn hν hΘ hB hκ hp hds =>
      .nested hn hν (wfTelescope hs hw hΘ) (hasType hs hw hB) hκ hp (wfDestructors hs hw hds)
    | .recursive hD hΘ hp hds =>
      .recursive hD (wfTelescope hs hw hΘ) hp (wfDestructors hs hw hds)

end Sic.Core
