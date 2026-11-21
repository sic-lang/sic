module

public import Sic.Core.Typing

/-!
# Induction on the Derivations of the Typing

The induction principle of the eighteen mutual judgments of `Sic/Core/Typing.lean`, by which the
proofs on their derivations are written: a motive for each judgment, and a hypothesis for each rule,
that the motive of its conclusion holds whenever the motives of its premises hold, give the motives
of every derivation.
Lean generates a recursor for each judgment, which gives the motive of that judgment alone and whose
minor premises are named after the rules, so that the rules of the same name in several judgments
cannot be told apart by their names; `Derivations.induction` gives the eighteen motives at once and
names each hypothesis after its judgment and its rule, as `hasType_conv`.

A proof applies `Derivations.induction` to the motives of its statement, then proves the hypotheses
as cases named after the rules, so that it gives each rule a case: a rule added to the judgments adds
its name to the hypotheses of `Derivations.induction` and a case to each proof.

ADE prove by recursion on their derivations, which Agda checks to terminate.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- The motives, one for each judgment, hold of every derivation of their judgments.
The arguments of each motive are those of its judgment, then a derivation of it. -/
structure Derivations.Conclusion
    (wfSig : ∀ (sig : Signature), WfSig sig → Prop)
    (wfConstantDefinition :
      ∀ (sig : Signature) (d : ConstantDefinition), WfConstantDefinition sig d → Prop)
    (wfConstantDeclaration :
      ∀ (sig : Signature) (c : ConstantDeclaration), WfConstantDeclaration sig c → Prop)
    (wfCtx : ∀ (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ), WfCtx sig ctx → Prop)
    (wfType :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ),
        WfType sig ctx A → Prop)
    (eqType :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A B : Term k Γ),
        EqType sig ctx A B → Prop)
    (hasType :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (t A : Term k Γ),
        HasType sig ctx t A → Prop)
    (eqTerm :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (t u A : Term k Γ),
        EqTerm sig ctx t u A → Prop)
    (hasArgs :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
        (ts : Args k Γ ps) (Θ : Telescope k Γ ps), HasArgs sig ctx ts Θ → Prop)
    (eqArgs :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
        (ts us : Args k Γ ps) (Θ : Telescope k Γ ps), EqArgs sig ctx ts us Θ → Prop)
    (hasInstanceArgs :
      ∀ (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ) (as : InstanceArgs k Γ Δ)
        (params : Context k Δ), HasInstanceArgs sig ctx as params → Prop)
    (eqInstanceArgs :
      ∀ (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ)
        (as₁ as₂ : InstanceArgs k Γ Δ) (params : Context k Δ),
        EqInstanceArgs sig ctx as₁ as₂ params → Prop)
    (wfTelescope :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
        (Θ : Telescope k Γ ps) (κ : Universe k), WfTelescope sig ctx Θ κ → Prop)
    (wfTelescopeSorts :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
        (Θ : Telescope k Γ ps) (κs : List (Universe k)) (l : Level k),
        WfTelescopeSorts sig ctx Θ κs l → Prop)
    (eqTelescope :
      ∀ (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
        (Θ₁ Θ₂ : Telescope k Γ ps) (κ : Universe k), EqTelescope sig ctx Θ₁ Θ₂ κ → Prop)
    (wfFields :
      ∀ (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
        {Γ : Scope} (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
        {ps : List Parameter} (Θ : Telescope decl.levels Γ ps) (κ : Universe decl.levels),
        WfFields sig decl ι as ctx Θ κ → Prop)
    (wfDestructors :
      ∀ (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
        {Γ : Scope} {ns : List Name} (ν : Nesting Nat Γ)
        (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
        (ds : Destructors decl.levels Γ ns) (κ : Universe decl.levels),
        WfDestructors sig decl ι ν as ctx ds κ → Prop)
    (wfTypeDeclaration :
      ∀ (sig : Signature) (decl : TypeDeclaration), WfTypeDeclaration sig decl → Prop) :
    Prop where
  /-- The motive of `WfSig` holds of its derivations. -/
  wfSig : ∀ {sig : Signature} (h : WfSig sig), wfSig sig h
  /-- The motive of `WfConstantDefinition` holds of its derivations. -/
  wfConstantDefinition : ∀ {sig : Signature} {d : ConstantDefinition}
      (h : WfConstantDefinition sig d), wfConstantDefinition sig d h
  /-- The motive of `WfConstantDeclaration` holds of its derivations. -/
  wfConstantDeclaration : ∀ {sig : Signature} {c : ConstantDeclaration}
      (h : WfConstantDeclaration sig c), wfConstantDeclaration sig c h
  /-- The motive of `WfCtx` holds of its derivations. -/
  wfCtx : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (h : WfCtx sig ctx),
      wfCtx sig ctx h
  /-- The motive of `WfType` holds of its derivations. -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A), wfType sig ctx A h
  /-- The motive of `EqType` holds of its derivations. -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      (h : EqType sig ctx A B), eqType sig ctx A B h
  /-- The motive of `HasType` holds of its derivations. -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
      (h : HasType sig ctx t A), hasType sig ctx t A h
  /-- The motive of `EqTerm` holds of its derivations. -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      (h : EqTerm sig ctx t u A), eqTerm sig ctx t u A h
  /-- The motive of `HasArgs` holds of its derivations. -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} (h : HasArgs sig ctx ts Θ), hasArgs sig ctx ts Θ h
  /-- The motive of `EqArgs` holds of its derivations. -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} (h : EqArgs sig ctx ts us Θ),
      eqArgs sig ctx ts us Θ h
  /-- The motive of `HasInstanceArgs` holds of its derivations. -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} (h : HasInstanceArgs sig ctx as params),
      hasInstanceArgs sig ctx as params h
  /-- The motive of `EqInstanceArgs` holds of its derivations. -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ}
      (h : EqInstanceArgs sig ctx as₁ as₂ params), eqInstanceArgs sig ctx as₁ as₂ params h
  /-- The motive of `WfTelescope` holds of its derivations. -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {κ : Universe k} (h : WfTelescope sig ctx Θ κ),
      wfTelescope sig ctx Θ κ h
  /-- The motive of `WfTelescopeSorts` holds of its derivations. -/
  wfTelescopeSorts : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)} {l : Level k}
      (h : WfTelescopeSorts sig ctx Θ κs l), wfTelescopeSorts sig ctx Θ κs l h
  /-- The motive of `EqTelescope` holds of its derivations. -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} (h : EqTelescope sig ctx Θ₁ Θ₂ κ),
      eqTelescope sig ctx Θ₁ Θ₂ κ h
  /-- The motive of `WfFields` holds of its derivations. -/
  wfFields : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
      {ps : List Parameter} {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels}
      (h : WfFields sig decl ι as ctx Θ κ), wfFields sig decl ι as ctx Θ κ h
  /-- The motive of `WfDestructors` holds of its derivations. -/
  wfDestructors : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope}
      {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels}
      (h : WfDestructors sig decl ι ν as ctx ds κ), wfDestructors sig decl ι ν as ctx ds κ h
  /-- The motive of `WfTypeDeclaration` holds of its derivations. -/
  wfTypeDeclaration : ∀ {sig : Signature} {decl : TypeDeclaration} (h : WfTypeDeclaration sig decl),
      wfTypeDeclaration sig decl h

-- ADE: none.
/-- Induction on the derivations of the judgments: the motives hold of every derivation,
`Derivations.Conclusion` of the motives, when each holds of the conclusion of each rule of its
judgment whenever they hold of its premises.
The hypothesis of the rule `r` of the judgment `J` is named `J_r`, as `hasType_conv`, and its type is
the minor premise of the rule `r` of the recursor of `J`: the motive of `J` holds of a derivation by
`r` whenever the motives hold of its premises. -/
theorem Derivations.induction :
    ∀ {wfSig wfConstantDefinition wfConstantDeclaration wfCtx wfType eqType hasType eqTerm hasArgs
        eqArgs hasInstanceArgs eqInstanceArgs wfTelescope wfTelescopeSorts eqTelescope wfFields
        wfDestructors wfTypeDeclaration}
      (wfSig_empty : _) (wfSig_constantDefinition : _) (wfSig_constantDeclaration : _)
        (wfSig_typeDeclaration : _) (wfSig_lifting : _)
      (wfConstantDefinition_intro : _)
      (wfConstantDeclaration_intro : _)
      (wfCtx_empty : _) (wfCtx_var : _) (wfCtx_secondOrder : _)
      (wfType_univType : _) (wfType_propType : _)
      (eqType_refl : _) (eqType_symm : _) (eqType_trans : _) (eqType_univType : _)
        (eqType_propType : _)
      (hasType_var : _) (hasType_secondOrder : _) (hasType_const : _) (hasType_univ : _)
        (hasType_prop : _) (hasType_inst : _) (hasType_equality : _) (hasType_reflProof : _)
        (hasType_transp : _) (hasType_propExt : _) (hasType_coind : _) (hasType_ctor : _)
        (hasType_recursor : _) (hasType_obs : _) (hasType_corec : _) (hasType_conv : _)
      (eqTerm_refl : _) (eqTerm_symm : _) (eqTerm_trans : _) (eqTerm_conv : _) (eqTerm_irr : _)
        (eqTerm_secondOrder : _) (eqTerm_delta : _) (eqTerm_const : _) (eqTerm_univ : _)
        (eqTerm_prop : _) (eqTerm_inst : _) (eqTerm_equality : _) (eqTerm_transp : _)
        (eqTerm_transpSame : _) (eqTerm_ctor : _) (eqTerm_recursor : _) (eqTerm_obs : _)
        (eqTerm_corec : _) (eqTerm_iota : _) (eqTerm_etaCtor : _) (eqTerm_beta : _)
        (eqTerm_etaObs : _)
      (hasArgs_nil : _) (hasArgs_cons : _)
      (eqArgs_nil : _) (eqArgs_cons : _)
      (hasInstanceArgs_nil : _) (hasInstanceArgs_var : _) (hasInstanceArgs_secondOrder : _)
      (eqInstanceArgs_nil : _) (eqInstanceArgs_var : _) (eqInstanceArgs_secondOrder : _)
      (wfTelescope_nil : _) (wfTelescope_cons : _)
      (wfTelescopeSorts_nil : _) (wfTelescopeSorts_cons : _)
      (eqTelescope_nil : _) (eqTelescope_cons : _)
      (wfFields_nil : _) (wfFields_cons : _) (wfFields_recursive : _) (wfFields_nested : _)
      (wfDestructors_nil : _) (wfDestructors_cons : _) (wfDestructors_nested : _)
        (wfDestructors_recursive : _)
      (wfTypeDeclaration_data : _) (wfTypeDeclaration_codata : _),
      -- The types of the hypotheses are those of the minor premises of the recursors, which Lean
      -- infers from the type of the conclusion, ascribed with the recursor of `WfSig` applied to the
      -- motives and to the hypotheses, so that the rules are read from `Sic/Core/Typing.lean` and
      -- not restated; the recursor applied is ascribed its full type, the motive of `WfSig` of every
      -- derivation, so that a hypothesis missing or extra fails here. The hypotheses are given in
      -- the order of the rules in `Sic/Core/Typing.lean`, the judgments in their order, then the
      -- rules of each judgment in their order, so that a rule added or moved there is added or moved
      -- here: a hypothesis out of this order would be given the type of another rule.
      (Derivations.Conclusion wfSig wfConstantDefinition wfConstantDeclaration wfCtx wfType eqType
          hasType eqTerm hasArgs eqArgs hasInstanceArgs eqInstanceArgs wfTelescope wfTelescopeSorts
          eqTelescope wfFields wfDestructors wfTypeDeclaration :
        (fun _ => Prop) (@WfSig.rec wfSig wfConstantDefinition wfConstantDeclaration wfCtx wfType
          eqType hasType eqTerm hasArgs eqArgs hasInstanceArgs eqInstanceArgs wfTelescope
          wfTelescopeSorts eqTelescope wfFields wfDestructors wfTypeDeclaration wfSig_empty
          wfSig_constantDefinition wfSig_constantDeclaration wfSig_typeDeclaration wfSig_lifting
          wfConstantDefinition_intro wfConstantDeclaration_intro wfCtx_empty wfCtx_var
          wfCtx_secondOrder wfType_univType wfType_propType eqType_refl eqType_symm eqType_trans
          eqType_univType eqType_propType hasType_var hasType_secondOrder hasType_const hasType_univ
          hasType_prop hasType_inst hasType_equality hasType_reflProof hasType_transp
          hasType_propExt hasType_coind hasType_ctor hasType_recursor hasType_obs hasType_corec
          hasType_conv eqTerm_refl eqTerm_symm eqTerm_trans eqTerm_conv eqTerm_irr
          eqTerm_secondOrder eqTerm_delta eqTerm_const eqTerm_univ eqTerm_prop eqTerm_inst
          eqTerm_equality eqTerm_transp eqTerm_transpSame eqTerm_ctor eqTerm_recursor eqTerm_obs
          eqTerm_corec eqTerm_iota eqTerm_etaCtor eqTerm_beta eqTerm_etaObs hasArgs_nil hasArgs_cons
          eqArgs_nil eqArgs_cons hasInstanceArgs_nil hasInstanceArgs_var hasInstanceArgs_secondOrder
          eqInstanceArgs_nil eqInstanceArgs_var eqInstanceArgs_secondOrder wfTelescope_nil
          wfTelescope_cons wfTelescopeSorts_nil wfTelescopeSorts_cons eqTelescope_nil
          eqTelescope_cons wfFields_nil wfFields_cons wfFields_recursive wfFields_nested
          wfDestructors_nil wfDestructors_cons wfDestructors_nested wfDestructors_recursive
          wfTypeDeclaration_data wfTypeDeclaration_codata :
          ∀ {sig : Signature} (h : WfSig sig), wfSig sig h)) := by
  intros
  constructor
  · apply WfSig.rec <;> assumption
  · apply WfConstantDefinition.rec <;> assumption
  · apply WfConstantDeclaration.rec <;> assumption
  · apply WfCtx.rec <;> assumption
  · apply WfType.rec <;> assumption
  · apply EqType.rec <;> assumption
  · apply HasType.rec <;> assumption
  · apply EqTerm.rec <;> assumption
  · apply HasArgs.rec <;> assumption
  · apply EqArgs.rec <;> assumption
  · apply HasInstanceArgs.rec <;> assumption
  · apply EqInstanceArgs.rec <;> assumption
  · apply WfTelescope.rec <;> assumption
  · apply WfTelescopeSorts.rec <;> assumption
  · apply EqTelescope.rec <;> assumption
  · apply WfFields.rec <;> assumption
  · apply WfDestructors.rec <;> assumption
  · apply WfTypeDeclaration.rec <;> assumption

end Sic.Core
