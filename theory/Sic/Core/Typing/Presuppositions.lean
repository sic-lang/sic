module

public import Sic.Core.Typing

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

-- ADE: none.
/-- The signature of a judgment. -/
def Judgment.signature : Judgment → Signature
  | .wfSig s .. => s
  | .wfConstantDefinition s .. => s
  | .wfConstantDeclaration s .. => s
  | .wfCtx s .. => s
  | .wfType s .. => s
  | .eqType s .. => s
  | .hasType s .. => s
  | .eqTerm s .. => s
  | .hasArgs s .. => s
  | .eqArgs s .. => s
  | .hasInstanceArgs s .. => s
  | .eqInstanceArgs s .. => s
  | .wfTelescope s .. => s
  | .wfTelescopeSorts s .. => s
  | .eqTelescope s .. => s
  | .wfFields s .. => s
  | .wfDestructors s .. => s
  | .wfTypeDeclaration s .. => s

-- ADE: none.
/-- Every judgment holds in its signature, which is well formed, by induction on its derivation. -/
theorem Derivable.wfSig {J : Judgment} (h : Derivable J) : WfSig J.signature := by
  induction h with
  | WfSig.empty => exact .empty
  | WfSig.constantDefinition h hf _ => exact .constantDefinition h hf
  | WfSig.constantDeclaration h hf _ => exact .constantDeclaration h hf
  | WfSig.typeDeclaration h hn hL _ => exact .typeDeclaration h hn hL
  | WfSig.lifting h hd hl _ => exact .lifting h hd hl
  | WfConstantDefinition.intro _ hA _ hA_ih _ => exact hA_ih (.default _ _)
  | WfConstantDeclaration.intro _ hA hA_ih => exact hA_ih (.default _ _)
  | WfCtx.empty h h_ih => exact h
  | WfCtx.var h h_ih => exact h_ih
  | WfCtx.secondOrder h h_ih => exact h_ih
  | WfType.univType h h_ih => exact h_ih
  | WfType.propType h h_ih => exact h_ih
  | EqType.refl h h_ih => exact h_ih
  | EqType.symm h h_ih => exact h_ih
  | EqType.trans h _ h_ih _ => exact h_ih
  | EqType.univType h h_ih => exact h_ih
  | EqType.propType h h_ih => exact h_ih
  | HasType.var hctx _ hctx_ih => exact hctx_ih
  | HasType.secondOrder _ hts hts_ih => exact hts_ih
  | HasType.const hctx _ _ _ _ hctx_ih => exact hctx_ih
  | HasType.univ hctx hctx_ih => exact hctx_ih
  | HasType.prop hctx hctx_ih => exact hctx_ih
  | HasType.inst _ _ _ _ _ has has_ih => exact has_ih
  | HasType.equality hA _ _ hA_ih _ _ => exact hA_ih
  | HasType.reflProof hA _ hA_ih _ => exact hA_ih
  | HasType.transp hA _ _ _ _ _ hA_ih _ _ _ _ _ => exact hA_ih
  | HasType.propExt hA _ _ _ hA_ih _ _ _ => exact hA_ih
  | HasType.coind _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ _ _ _ => exact has_ih
  | HasType.ctor _ _ _ _ _ _ has _ has_ih _ => exact has_ih
  | HasType.recursor _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | HasType.obs _ _ _ _ _ _ has _ _ has_ih _ _ => exact has_ih
  | HasType.corec _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | HasType.conv ht _ ht_ih _ => exact ht_ih
  | EqTerm.refl h h_ih => exact h_ih
  | EqTerm.symm h h_ih => exact h_ih
  | EqTerm.trans h _ h_ih _ => exact h_ih
  | EqTerm.conv h _ h_ih _ => exact h_ih
  | EqTerm.irr ht _ _ ht_ih _ _ => exact ht_ih
  | EqTerm.secondOrder _ hts hts_ih => exact hts_ih
  | EqTerm.delta hctx _ _ _ _ hctx_ih => exact hctx_ih
  | EqTerm.const hctx _ _ _ _ _ _ hctx_ih => exact hctx_ih
  | EqTerm.univ hctx _ hctx_ih => exact hctx_ih
  | EqTerm.prop hctx _ hctx_ih => exact hctx_ih
  | EqTerm.inst _ _ _ _ _ _ has _ has_ih => exact has_ih
  | EqTerm.equality hA _ _ _ hA_ih _ _ => exact hA_ih
  | EqTerm.transp hA _ _ _ _ _ hA_ih _ _ _ _ _ => exact hA_ih
  | EqTerm.transpSame hA _ _ _ _ _ _ hA_ih _ _ _ _ _ _ => exact hA_ih
  | EqTerm.ctor _ _ _ _ _ _ _ has _ _ has_ih _ => exact has_ih
  | EqTerm.recursor _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | EqTerm.obs _ _ _ _ _ _ _ has _ _ _ has_ih _ _ => exact has_ih
  | EqTerm.corec _ _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.iota _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | EqTerm.etaCtor _ _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.beta _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.etaObs _ _ _ _ _ _ has _ _ _ has_ih _ _ _ => exact has_ih
  | HasArgs.nil hctx hctx_ih => exact hctx_ih
  | HasArgs.cons ht _ ht_ih _ => exact ht_ih
  | EqArgs.nil hctx hctx_ih => exact hctx_ih
  | EqArgs.cons ht _ ht_ih _ => exact ht_ih
  | HasInstanceArgs.nil hctx hctx_ih => exact hctx_ih
  | HasInstanceArgs.var has _ has_ih _ => exact has_ih
  | HasInstanceArgs.secondOrder has _ has_ih _ => exact has_ih
  | EqInstanceArgs.nil hctx hctx_ih => exact hctx_ih
  | EqInstanceArgs.var has _ has_ih _ => exact has_ih
  | EqInstanceArgs.secondOrder has _ has_ih _ => exact has_ih
  | WfTelescope.nil hctx hctx_ih => exact hctx_ih
  | WfTelescope.cons hA _ _ _ hA_ih _ => exact hA_ih
  | WfTelescopeSorts.nil hctx hctx_ih => exact hctx_ih
  | WfTelescopeSorts.cons hA _ _ _ hA_ih _ => exact hA_ih
  | EqTelescope.nil hctx hctx_ih => exact hctx_ih
  | EqTelescope.cons hA _ _ _ hA_ih _ => exact hA_ih
  | WfFields.nil hctx hctx_ih => exact hctx_ih
  | WfFields.cons _ hA _ _ _ hA_ih _ => exact hA_ih
  | WfFields.recursive _ hΘ _ hΘ_ih => exact hΘ_ih
  | WfFields.nested _ _ _ _ _ _ hΘ _ _ hΘ_ih => exact hΘ_ih
  | WfDestructors.nil hctx hctx_ih => exact hctx_ih
  | WfDestructors.cons _ _ hΘ _ _ _ _ hΘ_ih _ _ => exact hΘ_ih
  | WfDestructors.nested _ _ hΘ _ _ _ _ hΘ_ih _ _ => exact hΘ_ih
  | WfDestructors.recursive _ hΘ _ _ hΘ_ih _ => exact hΘ_ih
  | WfTypeDeclaration.data _ _p4 hΔ _ _ _ _ hΔ_ih _ =>
    obtain ⟨_, hadm⟩ := _p4
    exact (hΔ_ih _ hadm)
  | WfTypeDeclaration.codata _ _p4 hΔ _ _ _ _ hΔ_ih _ =>
    obtain ⟨_, hadm⟩ := _p4
    exact (hΔ_ih _ hadm)

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
  ⟨(·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig),
    (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig), (·.wfSig),
    fun h => by
      cases h with
      | WfSig.constantDefinition h _ => exact h.wfSig
      | WfSig.constantDeclaration h _ => exact h.wfSig
      | WfSig.typeDeclaration h _ _ => exact h.wfSig
      | WfSig.lifting h _ _ => exact h.wfSig⟩

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

-- ADE: none.
/-- The well-formedness of the context of a judgment in a context. -/
def Judgment.ContextWf : Judgment → Prop
  | wfType sig ctx _ => WfCtx sig ctx
  | eqType sig ctx _ _ => WfCtx sig ctx
  | hasType sig ctx _ _ => WfCtx sig ctx
  | eqTerm sig ctx _ _ _ => WfCtx sig ctx
  | hasArgs sig ctx _ _ => WfCtx sig ctx
  | eqArgs sig ctx _ _ _ => WfCtx sig ctx
  | hasInstanceArgs sig ctx _ _ => WfCtx sig ctx
  | eqInstanceArgs sig ctx _ _ _ => WfCtx sig ctx
  | wfTelescope sig ctx _ _ => WfCtx sig ctx
  | wfTelescopeSorts sig ctx _ _ _ => WfCtx sig ctx
  | eqTelescope sig ctx _ _ _ => WfCtx sig ctx
  | _ => True

-- ADE: none.
/-- Every judgment in a context holds in a well-formed context, by induction on its derivation. -/
theorem Derivable.contextWf {J : Judgment} (h : Derivable J) : J.ContextWf := by
  induction h with
  | WfType.univType h h_ih => exact h_ih
  | WfType.propType h h_ih => exact h_ih
  | EqType.refl h h_ih => exact h_ih
  | EqType.symm h h_ih => exact h_ih
  | EqType.trans h _ h_ih _ => exact h_ih
  | EqType.univType h h_ih => exact h_ih
  | EqType.propType h h_ih => exact h_ih
  | HasType.var hctx _ hctx_ih => exact hctx
  | HasType.secondOrder _ hts hts_ih => exact hts_ih
  | HasType.const hctx _ _ _ _ hctx_ih => exact hctx
  | HasType.univ hctx hctx_ih => exact hctx
  | HasType.prop hctx hctx_ih => exact hctx
  | HasType.inst _ _ _ _ _ has has_ih => exact has_ih
  | HasType.equality hA _ _ hA_ih _ _ => exact hA_ih
  | HasType.reflProof hA _ hA_ih _ => exact hA_ih
  | HasType.transp hA _ _ _ _ _ hA_ih _ _ _ _ _ => exact hA_ih
  | HasType.propExt hA _ _ _ hA_ih _ _ _ => exact hA_ih
  | HasType.coind _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ _ _ _ => exact has_ih
  | HasType.ctor _ _ _ _ _ _ has _ has_ih _ => exact has_ih
  | HasType.recursor _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | HasType.obs _ _ _ _ _ _ has _ _ has_ih _ _ => exact has_ih
  | HasType.corec _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | HasType.conv ht _ ht_ih _ => exact ht_ih
  | EqTerm.refl h h_ih => exact h_ih
  | EqTerm.symm h h_ih => exact h_ih
  | EqTerm.trans h _ h_ih _ => exact h_ih
  | EqTerm.conv h _ h_ih _ => exact h_ih
  | EqTerm.irr ht _ _ ht_ih _ _ => exact ht_ih
  | EqTerm.secondOrder _ hts hts_ih => exact hts_ih
  | EqTerm.delta hctx _ _ _ _ hctx_ih => exact hctx
  | EqTerm.const hctx _ _ _ _ _ _ hctx_ih => exact hctx
  | EqTerm.univ hctx _ hctx_ih => exact hctx
  | EqTerm.prop hctx _ hctx_ih => exact hctx
  | EqTerm.inst _ _ _ _ _ _ has _ has_ih => exact has_ih
  | EqTerm.equality hA _ _ _ hA_ih _ _ => exact hA_ih
  | EqTerm.transp hA _ _ _ _ _ hA_ih _ _ _ _ _ => exact hA_ih
  | EqTerm.transpSame hA _ _ _ _ _ _ hA_ih _ _ _ _ _ _ => exact hA_ih
  | EqTerm.ctor _ _ _ _ _ _ _ has _ _ has_ih _ => exact has_ih
  | EqTerm.recursor _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | EqTerm.obs _ _ _ _ _ _ _ has _ _ _ has_ih _ _ => exact has_ih
  | EqTerm.corec _ _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.iota _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ => exact has_ih
  | EqTerm.etaCtor _ _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.beta _ _ _ _ _ _ has _ _ _ _ _ _ _ _ _ _ _ _ _ has_ih _ _ _ _ => exact has_ih
  | EqTerm.etaObs _ _ _ _ _ _ has _ _ _ has_ih _ _ _ => exact has_ih
  | HasArgs.nil hctx hctx_ih => exact hctx
  | HasArgs.cons ht _ ht_ih _ => exact ht_ih
  | EqArgs.nil hctx hctx_ih => exact hctx
  | EqArgs.cons ht _ ht_ih _ => exact ht_ih
  | HasInstanceArgs.nil hctx hctx_ih => exact hctx
  | HasInstanceArgs.var has _ has_ih _ => exact has_ih
  | HasInstanceArgs.secondOrder has _ has_ih _ => exact has_ih
  | EqInstanceArgs.nil hctx hctx_ih => exact hctx
  | EqInstanceArgs.var has _ has_ih _ => exact has_ih
  | EqInstanceArgs.secondOrder has _ has_ih _ => exact has_ih
  | WfTelescope.nil hctx hctx_ih => exact hctx
  | WfTelescope.cons hA _ _ _ hA_ih _ => exact hA_ih
  | WfTelescopeSorts.nil hctx hctx_ih => exact hctx
  | WfTelescopeSorts.cons hA _ _ _ hA_ih _ => exact hA_ih
  | EqTelescope.nil hctx hctx_ih => exact hctx
  | EqTelescope.cons hA _ _ _ hA_ih _ => exact hA_ih
  | _ => trivial

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
  ⟨(·.contextWf), (·.contextWf), (·.contextWf), (·.contextWf), (·.contextWf), (·.contextWf),
    (·.contextWf), (·.contextWf), (·.contextWf), (·.contextWf), (·.contextWf)⟩

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
  | .typeDeclaration h _ _, e', he', n, hn => (WfTypeDeclaration.fresh h) e' he' n hn
  | .lifting h _ _, e', he', n, hn => (WfTypeDeclaration.fresh h) e' he' n hn

-- ADE: none.
/-- The names of a well-formed signature are distinct.
RFC: `\mathsf{distinct}_\Sigma` -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨(Presuppositions.tail presuppositions h).distinct,
      by cases h with
        | WfSig.typeDeclaration _ hn => exact hn
        | _ => exact List.pairwise_singleton _ _, h.fresh,
      by
        rename_i e _
        cases e with
        | typeDeclaration decl => cases h.typeDeclaration_inv.1 with
          | WfTypeDeclaration.data hb _ _ _ _ hc _ =>
            refine ⟨hc, fun T hT => ?_⟩
            simp only [TypeDeclaration.codataTypes, hb] at hT
            nomatch hT
          | WfTypeDeclaration.codata hb _ _ _ _ hc _ =>
            refine ⟨fun T hT => ?_, hc⟩
            simp only [TypeDeclaration.dataTypes, hb] at hT
            nomatch hT
        | _ => trivial⟩

end Sic.Core
