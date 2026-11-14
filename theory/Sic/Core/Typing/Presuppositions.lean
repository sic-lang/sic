module

public import Sic.Core.Typing

/-!
# Presuppositions

The presuppositions of the judgments of annex 14 of RFC 36: every judgment holds in a well-formed
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
    {Γ : Scope} {ns : List Name} {as : InstanceArgs decl.levels Γ decl.scope}
    {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
    WfDestructors sig decl ι as ctx ds κ → WfSig sig
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
theorem presuppositions : Presuppositions :=
  ⟨wfConstantDefinition, wfConstantDeclaration, wfCtx, wfType, eqType, hasType, eqTerm, hasArgs,
    eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope, wfTelescopeSorts, eqTelescope, wfFields,
    wfDestructors, wfTypeDeclaration, tail⟩
where
  wfConstantDefinition {sig : Signature} {d : ConstantDefinition} :
      WfConstantDefinition sig d → WfSig sig
    | .intro _ hA _ => hasType (hA (.default _ _))
  wfConstantDeclaration {sig : Signature} {c : ConstantDeclaration} :
      WfConstantDeclaration sig c → WfSig sig
    | .intro _ hA => hasType (hA (.default _ _))
  wfCtx {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} : WfCtx sig ctx → WfSig sig
    | .empty h => h
    | .var h => wfType h
    | .secondOrder h => wfType h
  wfType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      WfType sig ctx A → WfSig sig
    | .univType h => hasType h
    | .propType h => hasType h
  eqType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ} :
      EqType sig ctx A B → WfSig sig
    | .refl h => wfType h
    | .symm h => eqType h
    | .trans h _ => eqType h
    | .univType h => eqTerm h
    | .propType h => eqTerm h
  hasType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ} :
      HasType sig ctx t A → WfSig sig
    | .var hctx _ => wfCtx hctx
    | .secondOrder _ hts => hasArgs hts
    | .const hctx _ _ _ _ => wfCtx hctx
    | .univ hctx => wfCtx hctx
    | .prop hctx => wfCtx hctx
    | .inst _ _ _ _ _ has => hasInstanceArgs has
    | .ctor _ _ _ _ _ _ has _ => hasInstanceArgs has
    | .recursor _ _ _ _ _ has .. => hasInstanceArgs has
    | .obs _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .conv ht _ => hasType ht
  eqTerm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ} :
      EqTerm sig ctx t u A → WfSig sig
    | .refl h => hasType h
    | .symm h => eqTerm h
    | .trans h _ => eqTerm h
    | .conv h _ => eqTerm h
    | .irr ht _ _ => hasType ht
    | .secondOrder _ hts => eqArgs hts
    | .delta hctx _ _ _ _ => wfCtx hctx
    | .const hctx .. => wfCtx hctx
    | .univ hctx _ => wfCtx hctx
    | .prop hctx _ => wfCtx hctx
    | .inst _ _ _ _ _ _ has _ => eqInstanceArgs has
    | .ctor _ _ _ _ _ _ _ has _ _ => eqInstanceArgs has
    | .recursor _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .obs _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .iota _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaCtor _ _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .beta _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaObs _ _ _ _ _ _ has .. => hasInstanceArgs has
  hasArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} : HasArgs sig ctx ts Θ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons ht _ => hasType ht
  eqArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} : EqArgs sig ctx ts us Θ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons ht _ => eqTerm ht
  hasInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
      HasInstanceArgs sig ctx as params → WfSig sig
    | .nil hctx => wfCtx hctx
    | .var has _ => hasInstanceArgs has
    | .secondOrder has _ => hasInstanceArgs has
  eqInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} :
      EqInstanceArgs sig ctx as₁ as₂ params → WfSig sig
    | .nil hctx => wfCtx hctx
    | .var has _ => eqInstanceArgs has
    | .secondOrder has _ => eqInstanceArgs has
  wfTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {κ : Universe k} : WfTelescope sig ctx Θ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons hA _ _ _ => hasType hA
  wfTelescopeSorts {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k} :
      WfTelescopeSorts sig ctx Θ κs l → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons hA _ _ _ => hasType hA
  eqTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} : EqTelescope sig ctx Θ₁ Θ₂ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons hA _ _ _ => eqTerm hA
  wfFields {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels} :
      WfFields sig decl ι as ctx Θ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons _ hA _ _ _ => hasType hA
    | .recursive _ hΘ _ => wfFields hΘ
  wfDestructors {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ns : List Name} {as : InstanceArgs decl.levels Γ decl.scope}
      {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} :
      WfDestructors sig decl ι as ctx ds κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons _ hΘ .. => wfTelescope hΘ
    | .recursive _ hΘ .. => wfTelescope hΘ
  wfTypeDeclaration {sig : Signature} {decl : TypeDeclaration} :
      WfTypeDeclaration sig decl → WfSig sig
    | .data _ ⟨_, hadm⟩ hΔ _ _ => wfCtx (hΔ _ hadm)
    | .codata _ ⟨_, hadm⟩ hΔ _ _ => wfCtx (hΔ _ hadm)
  tail {e : Entry} {sig : Signature} : WfSig (e :: sig) → WfSig sig
    | .constantDefinition h _ => wfConstantDefinition h
    | .constantDeclaration h _ => wfConstantDeclaration h
    | .typeDeclaration h _ _ => wfTypeDeclaration h

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
theorem contextPresuppositions : ContextPresuppositions :=
  ⟨wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope,
    wfTelescopeSorts, eqTelescope⟩
where
  wfType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      WfType sig ctx A → WfCtx sig ctx
    | .univType h => hasType h
    | .propType h => hasType h
  eqType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ} :
      EqType sig ctx A B → WfCtx sig ctx
    | .refl h => wfType h
    | .symm h => eqType h
    | .trans h _ => eqType h
    | .univType h => eqTerm h
    | .propType h => eqTerm h
  hasType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ} :
      HasType sig ctx t A → WfCtx sig ctx
    | .var hctx _ => hctx
    | .secondOrder _ hts => hasArgs hts
    | .const hctx _ _ _ _ => hctx
    | .univ hctx => hctx
    | .prop hctx => hctx
    | .inst _ _ _ _ _ has => hasInstanceArgs has
    | .ctor _ _ _ _ _ _ has _ => hasInstanceArgs has
    | .recursor _ _ _ _ _ has .. => hasInstanceArgs has
    | .obs _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .conv ht _ => hasType ht
  eqTerm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ} :
      EqTerm sig ctx t u A → WfCtx sig ctx
    | .refl h => hasType h
    | .symm h => eqTerm h
    | .trans h _ => eqTerm h
    | .conv h _ => eqTerm h
    | .irr ht _ _ => hasType ht
    | .secondOrder _ hts => eqArgs hts
    | .delta hctx _ _ _ _ => hctx
    | .const hctx .. => hctx
    | .univ hctx _ => hctx
    | .prop hctx _ => hctx
    | .inst _ _ _ _ _ _ has _ => eqInstanceArgs has
    | .ctor _ _ _ _ _ _ _ has _ _ => eqInstanceArgs has
    | .recursor _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .obs _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .iota _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaCtor _ _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .beta _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaObs _ _ _ _ _ _ has .. => hasInstanceArgs has
  hasArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} : HasArgs sig ctx ts Θ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons ht _ => hasType ht
  eqArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} : EqArgs sig ctx ts us Θ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons ht _ => eqTerm ht
  hasInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
      HasInstanceArgs sig ctx as params → WfCtx sig ctx
    | .nil hctx => hctx
    | .var has _ => hasInstanceArgs has
    | .secondOrder has _ => hasInstanceArgs has
  eqInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} :
      EqInstanceArgs sig ctx as₁ as₂ params → WfCtx sig ctx
    | .nil hctx => hctx
    | .var has _ => eqInstanceArgs has
    | .secondOrder has _ => eqInstanceArgs has
  wfTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {κ : Universe k} : WfTelescope sig ctx Θ κ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons hA _ _ _ => hasType hA
  wfTelescopeSorts {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k} :
      WfTelescopeSorts sig ctx Θ κs l → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons hA _ _ _ => hasType hA
  eqTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} : EqTelescope sig ctx Θ₁ Θ₂ κ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons hA _ _ _ => eqTerm hA

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
  | .typeDeclaration _ _ h, e', he', n, hn => h e' he' n hn

-- ADE: none.
/-- The names of a well-formed signature are distinct.
RFC: `\mathsf{distinct}_\Sigma` -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨(Presuppositions.tail presuppositions h).distinct,
      by cases h with
        | typeDeclaration _ hn _ => exact hn
        | _ => exact List.pairwise_singleton _ _, h.fresh,
      by cases h with
        | typeDeclaration hdecl _ _ => cases hdecl with
          | data hb _ _ _ hc =>
            refine ⟨hc, fun T hT => ?_⟩
            simp only [TypeDeclaration.codataTypes, hb] at hT
            nomatch hT
          | codata hb _ _ _ hc =>
            refine ⟨fun T hT => ?_, hc⟩
            simp only [TypeDeclaration.dataTypes, hb] at hT
            nomatch hT
        | _ => trivial⟩

end Sic.Core
