module

public import Sic.Core.Soundness.Rules

/-!
# Soundness of the Judgments

Every judgment of annex 13 of RFC 36 is meaningful, as annex 16 defines it, at every value of its
level variables, in a signature whose constant declarations the interpretation gives terms of their
types, `(hyp_ι)`.

The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem, whose auxiliary theorems give the fields of the record: each case takes the values `ρ` of
the level variables, instantiates the levels of its premises by them, which commutes with the
substitutions and the entries of the contexts and of the signature, and concludes by the rule of
the same name in `Rules`.
A premise that is not a subterm of the derivation, such as the well-formed signature that
`presuppositions` gives, would stop the recursion: the meaningful signature and context of a case
come from the meaning of one of its premises.

ADE prove the fundamental theorem for their judgments with a context of definitions and without
levels, whose definitions have bodies, so that they need no interpretation.
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- The interpretation `ι` gives each constant declaration of the signature a term of its type, in
the signature.
RFC: `\mathsf{hyp}_\iota` -/
def ValidInterpretation (ι : Interpretation) (sig : Signature) : Prop :=
  ∀ c, .constantDeclaration c ∈ sig → ValidConstantDeclaration sig ι c

/-! ## Judgments in a Signature That Gives Their Entries Their Meaning -/

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names are
distinct and that gives the entries of `Σ_T` their meaning. -/
structure SoundnessIn : Prop where
  /-- A well-formed constant definition. -/
  wfConstantDefinition : ∀ {ι : Interpretation} {sigM sig : Signature} {d : ConstantDefinition},
    sigM.Distinct → sigM.ValidEntries ι sig → WfConstantDefinition sig d →
      ValidConstantDefinition sigM ι d
  /-- A well-formed context. -/
  wfCtx : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    sigM.Distinct → sigM.ValidEntries ι sig → WfCtx sig ctx → ValidCtx sigM ι ctx
  /-- A type. -/
  wfType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {A : Term k Γ}, sigM.Distinct → sigM.ValidEntries ι sig →
      WfType sig ctx A → ValidType sigM ι ctx A
  /-- An equality of types. -/
  eqType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {A B : Term k Γ}, sigM.Distinct → sigM.ValidEntries ι sig →
      EqType sig ctx A B → ValidEqType sigM ι ctx A B
  /-- A typing. -/
  hasType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {t A : Term k Γ}, sigM.Distinct → sigM.ValidEntries ι sig →
      HasType sig ctx t A → ValidTerm sigM ι ctx t A
  /-- An equality of terms. -/
  eqTerm : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {t u A : Term k Γ}, sigM.Distinct → sigM.ValidEntries ι sig →
      EqTerm sig ctx t u A → ValidEqTerm sigM ι ctx t u A
  /-- Arguments of a telescope. -/
  hasArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps},
      sigM.Distinct → sigM.ValidEntries ι sig → HasArgs sig ctx ts Θ → ValidArgs sigM ι ctx ts Θ
  /-- Equal arguments of a telescope. -/
  eqArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps},
      sigM.Distinct → sigM.ValidEntries ι sig → EqArgs sig ctx ts us Θ →
        ValidEqArgs sigM ι ctx ts us Θ
  /-- Arguments of an instance. -/
  hasInstanceArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
      sigM.Distinct → sigM.ValidEntries ι sig → HasInstanceArgs sig ctx as params →
        ValidInstanceArgs sigM ι ctx as params
  /-- Equal arguments of instances. -/
  eqInstanceArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
      sigM.Distinct → sigM.ValidEntries ι sig → EqInstanceArgs sig ctx as₁ as₂ params →
        ValidEqInstanceArgs sigM ι ctx as₁ as₂ params
  /-- A telescope in a sort. -/
  wfTelescope : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
      sigM.Distinct → sigM.ValidEntries ι sig → WfTelescope sig ctx Θ κ →
        ValidTelescope sigM ι ctx Θ κ
  /-- A well-formed type declaration. -/
  wfTypeDeclaration : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration},
    sigM.Distinct → sigM.ValidEntries ι sig → WfTypeDeclaration sig decl →
      ValidTypeDeclaration sigM ι decl

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names are
distinct and that gives the entries of `Σ_T` their meaning. -/
theorem soundnessIn : SoundnessIn :=
  ⟨wfConstantDefinition, wfCtx, wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs,
    eqInstanceArgs, wfTelescope, wfTypeDeclaration⟩
where
  wfConstantDefinition {ι : Interpretation} {sigM sig : Signature} {d : ConstantDefinition}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfConstantDefinition sig d → ValidConstantDefinition sigM ι d
    | .intro _ _ ht _ _ => ValidConstantDefinition.intro fun inst => hasType hd hι (ht inst)
  wfCtx {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfCtx sig ctx → ValidCtx sigM ι ctx
    | .empty _ => fun _ => by
      show ValidCtx₀ sigM ι .empty
      rw [ValidCtx₀]
      exact hd
    | .var h => fun ρ => (validCtx₀_var _ _).2 (wfType hd hι h ρ)
    | .secondOrder h _ => fun ρ => by
      have hA := wfType hd hι h ρ
      simp only [Context.atLevels, Context.substLevels_append] at hA
      exact (validCtx₀_secondOrder _ _ _ _).2 hA
  wfType {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {A : Term k Γ} (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfType sig ctx A → ValidType sigM ι ctx A
    | .univType h => fun ρ => ValidEqTermΓ.univType (hasType hd hι h ρ)
    | .propType h => fun ρ => ValidEqTermΓ.propType (hasType hd hι h ρ)
  eqType {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {A B : Term k Γ} (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      EqType sig ctx A B → ValidEqType sigM ι ctx A B
    | .refl h => wfType hd hι h
    | .symm h => fun ρ => (eqType hd hι h ρ).symm
    | .trans h₁ h₂ => fun ρ => (eqType hd hι h₁ ρ).trans (eqType hd hι h₂ ρ)
    | .univType h => fun ρ => ValidEqTermΓ.univType (eqTerm hd hι h ρ)
    | .propType h => fun ρ => ValidEqTermΓ.propType (eqTerm hd hι h ρ)
  hasType {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {t A : Term k Γ} (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      HasType sig ctx t A → ValidTerm sigM ι ctx t A
    | .var hctx hx => fun ρ => ValidTermΓ.var (wfCtx hd hι hctx ρ) (hx.substLevels _)
    | .secondOrder hX hts => fun ρ => by
      have hts' := hasArgs hd hι hts ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
    | .const (ls := ls) hctx h hq hl hp => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have hc := ValidTermΓ.const (wfCtx hd hι hctx ρ) hι h hq hl' hp
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .univ hctx => fun ρ =>
      ValidEqTermΓ.sort (q := .type) (wfCtx hd hι hctx ρ) (Level.equivalence.refl _)
    | .prop hctx => fun ρ =>
      ValidEqTermΓ.sort (q := .prop) (wfCtx hd hι hctx ρ) (Level.equivalence.refl _)
    | .inst (ls := ls) h hq hl hp has => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hc := ValidEqTermΓ.inst hι h hq hl' hl' hp (by rw [List.getFin_map]; exact has')
        fun _ => Level.equivalence.refl _
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
    | .conv ht h => fun ρ => (hasType hd hι ht ρ).conv (eqType hd hι h ρ)
  eqTerm {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {t u A : Term k Γ} (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      EqTerm sig ctx t u A → ValidEqTerm sigM ι ctx t u A
    | .refl h => hasType hd hι h
    | .symm h => fun ρ => (eqTerm hd hι h ρ).symm
    | .trans h₁ h₂ => fun ρ => (eqTerm hd hι h₁ ρ).trans (eqTerm hd hι h₂ ρ)
    | .conv h hA => fun ρ => (eqTerm hd hι h ρ).conv (eqType hd hι hA ρ)
    | .irr ht hu hA => fun ρ =>
      ValidEqTermΓ.irr (hasType hd hι ht ρ) (hasType hd hι hu ρ) (hasType hd hι hA ρ)
    | .secondOrder hX hts => fun ρ => by
      have hts' := eqArgs hd hι hts ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
    | .delta (ls := ls) hctx h hq hl hp => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have hc := ValidEqTermΓ.delta (wfCtx hd hι hctx ρ) hι h hq hl' hp
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .const (ls₁ := ls₁) (ls₂ := ls₂) hctx h hq hl₁ hl₂ hp hls => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have hc := ValidEqTermΓ.const (wfCtx hd hι hctx ρ) hι h hq hl₁' hl₂' hp (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .univ hctx hl => fun ρ => ValidEqTermΓ.sort (wfCtx hd hι hctx ρ) (Level.subst_equal _ hl)
    | .prop hctx hl => fun ρ => ValidEqTermΓ.sort (wfCtx hd hι hctx ρ) (Level.subst_equal _ hl)
    | .inst (ls₁ := ls₁) (ls₂ := ls₂) h hq hl₁ hl₂ hp has hls => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hc := ValidEqTermΓ.inst hι h hq hl₁' hl₂' hp (by rw [List.getFin_map]; exact has') (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
  hasArgs {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : HasArgs sig ctx ts Θ → ValidArgs sigM ι ctx ts Θ
    | .nil hctx => fun ρ => ValidEqArgsΓ.nil (wfCtx hd hι hctx ρ)
    | .cons (t := t) ht hts => fun ρ => by
      have hts' := hasArgs hd hι hts ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (hasType hd hι ht ρ) hts'
  eqArgs {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : EqArgs sig ctx ts us Θ → ValidEqArgs sigM ι ctx ts us Θ
    | .nil hctx => fun ρ => ValidEqArgsΓ.nil (wfCtx hd hι hctx ρ)
    | .cons (t := t) ht hts => fun ρ => by
      have hts' := eqArgs hd hι hts ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (eqTerm hd hι ht ρ) hts'
  hasInstanceArgs {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
      {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      HasInstanceArgs sig ctx as params → ValidInstanceArgs sigM ι ctx as params
    | .nil hctx => fun ρ => ValidEqInstanceArgsΓ.nil (wfCtx hd hι hctx ρ)
    | .var (as := as) has ha => fun ρ => by
      have ha' := hasType hd hι ha ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (hasInstanceArgs hd hι has ρ) ha'
    | .secondOrder (as := as) has hB => fun ρ => by
      have hB' := hasType hd hι hB ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (hasInstanceArgs hd hι has ρ) hB'
  eqInstanceArgs {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
      {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      EqInstanceArgs sig ctx as₁ as₂ params → ValidEqInstanceArgs sigM ι ctx as₁ as₂ params
    | .nil hctx => fun ρ => ValidEqInstanceArgsΓ.nil (wfCtx hd hι hctx ρ)
    | .var (as₁ := as₁) has ha => fun ρ => by
      have ha' := eqTerm hd hι ha ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (eqInstanceArgs hd hι has ρ) ha'
    | .secondOrder (as₁ := as₁) has hB => fun ρ => by
      have hB' := eqTerm hd hι hB ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as₁))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (eqInstanceArgs hd hι has ρ) hB'
  wfTelescope {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfTelescope sig ctx Θ κ → ValidTelescope sigM ι ctx Θ κ
    | .nil hctx => fun ρ => ValidTelescopeΓ.nil (wfCtx hd hι hctx ρ)
    | .cons hA hκ hΘ _ => fun ρ =>
      ValidTelescopeΓ.cons (hasType hd hι hA ρ) (Universe.substLevels_bounded _ hκ)
        (wfTelescope hd hι hΘ ρ)
  wfTypeDeclaration {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      WfTypeDeclaration sig decl → ValidTypeDeclaration sigM ι decl
    | .intro _ hΘ _ hc => ⟨fun I T hT c hc' => wfTelescope hd hι (hΘ I T hT c hc'), hc⟩


/-! ## Signatures -/

-- ADE: `defn-valid`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- The entries of a well-formed suffix of a signature whose names are distinct are meaningful in
the whole signature, when the interpretation gives its constant declarations terms of their types:
each entry is typed in the signature before it, whose entries are meaningful by induction. -/
theorem WfSig.validEntries {ι : Interpretation} {sigM : Signature}
    (hι : ValidInterpretation ι sigM) (hd : sigM.Distinct) :
    (sig : Signature) → WfSig sig → sig <:+ sigM → sigM.ValidEntries ι sig
  | [], _, _ => fun _ he => nomatch he
  | e :: sig, h, hs => by
    have hrest := WfSig.validEntries hι hd sig (Presuppositions.tail presuppositions h)
      ((List.suffix_cons e sig).trans hs)
    have hmem : e ∈ sigM := hs.subset List.mem_cons_self
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · refine ⟨hmem, ?_⟩
      cases h with
      | constantDefinition hdef _ => exact soundnessIn.wfConstantDefinition hd hrest hdef
      | constantDeclaration _ _ => exact hι _ hmem
      | typeDeclaration hdecl _ _ => exact soundnessIn.wfTypeDeclaration hd hrest hdecl
    · exact hrest e' he'

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment is meaningful, in a signature whose constant declarations the interpretation
gives terms of their types. -/
structure Soundness : Prop where
  -- ADE: `defn-valid`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A well-formed signature is meaningful.
  RFC: `\mathsf{sound}.\Sigma` -/
  wfSig : ∀ {ι : Interpretation} {sig : Signature}, ValidInterpretation ι sig →
    WfSig sig → ValidSig ι sig
  -- ADE: none.
  /-- A well-formed constant definition is meaningful.
  RFC: `\mathsf{sound}.\mathsf{def}` -/
  wfConstantDefinition : ∀ {ι : Interpretation} {sig : Signature} {d : ConstantDefinition},
    ValidInterpretation ι sig → WfConstantDefinition sig d → ValidConstantDefinition sig ι d
  -- ADE: `valid`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A well-formed context is meaningful.
  RFC: `\mathsf{sound}.\Gamma` -/
  wfCtx : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    ValidInterpretation ι sig → WfCtx sig ctx → ValidCtx sig ι ctx
  -- ADE: `fundamental-⊩ᵛ`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A type is meaningful.
  RFC: `\mathsf{sound}.A` -/
  wfType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {A : Term k Γ}, ValidInterpretation ι sig → WfType sig ctx A → ValidType sig ι ctx A
  -- ADE: `fundamental-⊩ᵛ≡`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- An equality of types is meaningful.
  RFC: `\mathsf{sound}.A_\equiv` -/
  eqType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {A B : Term k Γ}, ValidInterpretation ι sig → EqType sig ctx A B → ValidEqType sig ι ctx A B
  -- ADE: `fundamental-⊩ᵛ∷`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A typing is meaningful.
  RFC: `\mathsf{sound}.t` -/
  hasType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t A : Term k Γ}, ValidInterpretation ι sig → HasType sig ctx t A → ValidTerm sig ι ctx t A
  -- ADE: `fundamental-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- An equality of terms is meaningful.
  RFC: `\mathsf{sound}.t_\equiv` -/
  eqTerm : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t u A : Term k Γ}, ValidInterpretation ι sig → EqTerm sig ctx t u A →
      ValidEqTerm sig ι ctx t u A
  -- ADE: none.
  /-- Arguments of a telescope are meaningful.
  RFC: `\mathsf{sound}.\bar t` -/
  hasArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      HasArgs sig ctx ts Θ → ValidArgs sig ι ctx ts Θ
  -- ADE: none.
  /-- Equal arguments of a telescope are meaningful.
  RFC: `\mathsf{sound}.\bar t_\equiv` -/
  eqArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      EqArgs sig ctx ts us Θ → ValidEqArgs sig ι ctx ts us Θ
  -- ADE: none.
  /-- Arguments of an instance are meaningful.
  RFC: `\mathsf{sound}.\bar a` -/
  hasInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → HasInstanceArgs sig ctx as params →
        ValidInstanceArgs sig ι ctx as params
  -- ADE: none.
  /-- Equal arguments of instances are meaningful.
  RFC: `\mathsf{sound}.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → EqInstanceArgs sig ctx as₁ as₂ params →
        ValidEqInstanceArgs sig ι ctx as₁ as₂ params
  -- ADE: none.
  /-- A telescope in a sort is meaningful.
  RFC: `\mathsf{sound}.\Theta` -/
  wfTelescope : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
      ValidInterpretation ι sig → WfTelescope sig ctx Θ κ → ValidTelescope sig ι ctx Θ κ
  -- ADE: none.
  /-- A well-formed type declaration is meaningful.
  RFC: `\mathsf{sound}.\mathsf{data}` -/
  wfTypeDeclaration : ∀ {ι : Interpretation} {sig : Signature} {decl : TypeDeclaration},
    ValidInterpretation ι sig → WfTypeDeclaration sig decl → ValidTypeDeclaration sig ι decl

/-- A well-formed signature is meaningful, when the interpretation gives its constant declarations
terms of their types. -/
theorem soundness_wfSig {ι : Interpretation} {sig : Signature} (hι : ValidInterpretation ι sig)
    (h : WfSig sig) : ValidSig ι sig :=
  ⟨h.distinct, fun e he => (WfSig.validEntries hι h.distinct sig h (List.suffix_refl _) e he).2⟩

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment is meaningful, in a signature whose constant declarations the interpretation
gives terms of their types: its signature is well formed, hence meaningful, and so gives its own
entries their meaning. -/
theorem soundness : Soundness where
  wfSig := soundness_wfSig
  wfConstantDefinition hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfConstantDefinition h)
    soundnessIn.wfConstantDefinition hs.1 hs.validEntries h
  wfCtx hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfCtx h)
    soundnessIn.wfCtx hs.1 hs.validEntries h
  wfType hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfType h)
    soundnessIn.wfType hs.1 hs.validEntries h
  eqType hι h :=
    have hs := soundness_wfSig hι (presuppositions.eqType h)
    soundnessIn.eqType hs.1 hs.validEntries h
  hasType hι h :=
    have hs := soundness_wfSig hι (presuppositions.hasType h)
    soundnessIn.hasType hs.1 hs.validEntries h
  eqTerm hι h :=
    have hs := soundness_wfSig hι (presuppositions.eqTerm h)
    soundnessIn.eqTerm hs.1 hs.validEntries h
  hasArgs hι h :=
    have hs := soundness_wfSig hι (presuppositions.hasArgs h)
    soundnessIn.hasArgs hs.1 hs.validEntries h
  eqArgs hι h :=
    have hs := soundness_wfSig hι (presuppositions.eqArgs h)
    soundnessIn.eqArgs hs.1 hs.validEntries h
  hasInstanceArgs hι h :=
    have hs := soundness_wfSig hι (presuppositions.hasInstanceArgs h)
    soundnessIn.hasInstanceArgs hs.1 hs.validEntries h
  eqInstanceArgs hι h :=
    have hs := soundness_wfSig hι (presuppositions.eqInstanceArgs h)
    soundnessIn.eqInstanceArgs hs.1 hs.validEntries h
  wfTelescope hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfTelescope h)
    soundnessIn.wfTelescope hs.1 hs.validEntries h
  wfTypeDeclaration hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfTypeDeclaration h)
    soundnessIn.wfTypeDeclaration hs.1 hs.validEntries h

end Sic.Core
