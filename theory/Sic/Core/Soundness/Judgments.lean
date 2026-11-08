module

public import Sic.Core.Soundness.Rules

/-!
# Soundness of the Judgments

Every judgment of annex 12 of RFC 36 is meaningful, as annex 15 defines it, at every value of its
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
/-- `(hyp_ι)`: the interpretation `ι` gives each constant declaration of the signature a term of its
type, whenever the signature before it is meaningful. -/
def ValidInterpretation (ι : Interpretation) : Signature → Prop
  | [] => True
  | .typeDeclaration _ :: sig => ValidInterpretation ι sig
  | .constantDefinition _ :: sig => ValidInterpretation ι sig
  | .constantDeclaration c :: sig => ValidInterpretation ι sig ∧ (ValidSig ι sig → c.Clause sig ι)

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment is meaningful, in a signature whose constant declarations the interpretation
gives terms of their types. -/
structure Soundness : Prop where
  -- ADE: `defn-valid`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A well-formed signature is meaningful. -/
  wfSig : ∀ {ι : Interpretation} {sig : Signature}, ValidInterpretation ι sig →
    WfSig sig → ValidSig ι sig
  -- ADE: none.
  /-- A well-formed constant definition is meaningful. -/
  wfConstantDefinition : ∀ {ι : Interpretation} {sig : Signature} {d : ConstantDefinition},
    ValidInterpretation ι sig → WfConstantDefinition sig d → ValidConstantDefinition sig ι d
  -- ADE: none.
  /-- A well-formed constant declaration is meaningful, when the interpretation gives it a term of
  its type. -/
  wfConstantDeclaration : ∀ {ι : Interpretation} {sig : Signature} {c : ConstantDeclaration},
    ValidInterpretation ι (.constantDeclaration c :: sig) → WfConstantDeclaration sig c →
      ValidConstantDeclaration sig ι c
  -- ADE: `valid`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A well-formed context is meaningful. -/
  wfCtx : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    ValidInterpretation ι sig → WfCtx sig ctx → ValidCtx sig ι ctx
  -- ADE: `fundamental-⊩ᵛ`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A type is meaningful. -/
  wfType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {A : Term k Γ}, ValidInterpretation ι sig → WfType sig ctx A → ValidType sig ι ctx A
  -- ADE: `fundamental-⊩ᵛ≡`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- An equality of types is meaningful. -/
  eqType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {A B : Term k Γ}, ValidInterpretation ι sig → EqType sig ctx A B → ValidEqType sig ι ctx A B
  -- ADE: `fundamental-⊩ᵛ∷`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- A typing is meaningful. -/
  hasType : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t A : Term k Γ}, ValidInterpretation ι sig → HasType sig ctx t A → ValidTerm sig ι ctx t A
  -- ADE: `fundamental-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Fundamental.agda`.
  /-- An equality of terms is meaningful. -/
  eqTerm : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t u A : Term k Γ}, ValidInterpretation ι sig → EqTerm sig ctx t u A →
      ValidEqTerm sig ι ctx t u A
  -- ADE: none.
  /-- Arguments of a telescope are meaningful. -/
  hasArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      HasArgs sig ctx ts Θ → ValidArgs sig ι ctx ts Θ
  -- ADE: none.
  /-- Equal arguments of a telescope are meaningful. -/
  eqArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      EqArgs sig ctx ts us Θ → ValidEqArgs sig ι ctx ts us Θ
  -- ADE: none.
  /-- Arguments of an instance are meaningful. -/
  hasInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → HasInstanceArgs sig ctx as params →
        ValidInstanceArgs sig ι ctx as params
  -- ADE: none.
  /-- Equal arguments of instances are meaningful. -/
  eqInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → EqInstanceArgs sig ctx as₁ as₂ params →
        ValidEqInstanceArgs sig ι ctx as₁ as₂ params
  -- ADE: none.
  /-- A telescope in a sort is meaningful. -/
  wfTelescope : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
      ValidInterpretation ι sig → WfTelescope sig ctx Θ κ → ValidTelescope sig ι ctx Θ κ

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment is meaningful, in a signature whose constant declarations the interpretation
gives terms of their types. -/
theorem soundness : Soundness :=
  ⟨wfSig, wfConstantDefinition, wfConstantDeclaration, wfCtx, wfType, eqType, hasType, eqTerm,
    hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope⟩
where
  wfSig {ι : Interpretation} {sig : Signature} (hι : ValidInterpretation ι sig) :
      WfSig sig → ValidSig ι sig
    | .empty => trivial
    | .constantDefinition (sig := sig') h fresh =>
      have hd := wfConstantDefinition (sig := sig') hι h
      ⟨hd.1, fresh, hd.2⟩
    | .constantDeclaration (sig := sig') h fresh =>
      have hd := wfConstantDeclaration (sig := sig') hι h
      ⟨hd.1, fresh, hd.2⟩
  wfConstantDefinition {ι : Interpretation} {sig : Signature} {d : ConstantDefinition}
      (hι : ValidInterpretation ι sig) : WfConstantDefinition sig d → ValidConstantDefinition sig ι d
    | .intro _ _ ht _ _ => ValidConstantDefinition.intro fun inst => hasType hι (ht inst)
  wfConstantDeclaration {ι : Interpretation} {sig : Signature} {c : ConstantDeclaration}
      (hι : ValidInterpretation ι (.constantDeclaration c :: sig)) :
      WfConstantDeclaration sig c → ValidConstantDeclaration sig ι c
    | .intro _ hA =>
      have hsig : ValidSig ι sig :=
        (hasType hι.1 (hA (.default _ _)) fun _ => 0).1.1.validSig
      ⟨hsig, hι.2 hsig⟩
  wfCtx {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      (hι : ValidInterpretation ι sig) : WfCtx sig ctx → ValidCtx sig ι ctx
    | .empty h => fun _ => by
      show ValidCtx₀ sig ι .empty
      rw [ValidCtx₀]
      exact wfSig hι h
    | .var h => fun ρ => (validCtx₀_var _ _).2 (wfType hι h ρ)
    | .secondOrder h _ => fun ρ => by
      have hA := wfType hι h ρ
      simp only [Context.atLevels, Context.substLevels_append] at hA
      exact (validCtx₀_secondOrder _ _ _ _).2 hA
  wfType {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {A : Term k Γ} (hι : ValidInterpretation ι sig) : WfType sig ctx A → ValidType sig ι ctx A
    | .univType h => fun ρ => ValidEqTermΓ.univType (hasType hι h ρ)
    | .propType h => fun ρ => ValidEqTermΓ.propType (hasType hι h ρ)
  eqType {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {A B : Term k Γ} (hι : ValidInterpretation ι sig) :
      EqType sig ctx A B → ValidEqType sig ι ctx A B
    | .refl h => wfType hι h
    | .symm h => fun ρ => (eqType hι h ρ).symm
    | .trans h₁ h₂ => fun ρ => (eqType hι h₁ ρ).trans (eqType hι h₂ ρ)
    | .univType h => fun ρ => ValidEqTermΓ.univType (eqTerm hι h ρ)
    | .propType h => fun ρ => ValidEqTermΓ.propType (eqTerm hι h ρ)
  hasType {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {t A : Term k Γ} (hι : ValidInterpretation ι sig) :
      HasType sig ctx t A → ValidTerm sig ι ctx t A
    | .var hctx hx => fun ρ => ValidTermΓ.var (wfCtx hι hctx ρ) (hx.substLevels _)
    | .secondOrder hX hts => fun ρ => by
      have hts' := hasArgs hι hts ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
    | .const (ls := ls) hctx h hq hl hp => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have hc := ValidTermΓ.const (wfCtx hι hctx ρ) h hq hl' hp
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .univ hctx => fun ρ =>
      ValidEqTermΓ.sort (q := .type) (wfCtx hι hctx ρ) (Level.equivalence.refl _)
    | .prop hctx => fun ρ =>
      ValidEqTermΓ.sort (q := .prop) (wfCtx hι hctx ρ) (Level.equivalence.refl _)
    | .inst h _ _ _ has => fun ρ =>
      absurd h (ValidSig.not_hasDeclaredType (hasInstanceArgs hι has ρ).1.validSig)
    | .conv ht h => fun ρ => (hasType hι ht ρ).conv (eqType hι h ρ)
  eqTerm {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      {t u A : Term k Γ} (hι : ValidInterpretation ι sig) :
      EqTerm sig ctx t u A → ValidEqTerm sig ι ctx t u A
    | .refl h => hasType hι h
    | .symm h => fun ρ => (eqTerm hι h ρ).symm
    | .trans h₁ h₂ => fun ρ => (eqTerm hι h₁ ρ).trans (eqTerm hι h₂ ρ)
    | .conv h hA => fun ρ => (eqTerm hι h ρ).conv (eqType hι hA ρ)
    | .irr ht hu hA => fun ρ =>
      ValidEqTermΓ.irr (hasType hι ht ρ) (hasType hι hu ρ) (hasType hι hA ρ)
    | .secondOrder hX hts => fun ρ => by
      have hts' := eqArgs hι hts ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
    | .delta (ls := ls) hctx h hq hl hp => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have hc := ValidEqTermΓ.delta (wfCtx hι hctx ρ) h hq hl' hp
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .const (ls₁ := ls₁) (ls₂ := ls₂) hctx h hq hl₁ hl₂ hp hls => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have hc := ValidEqTermΓ.const (wfCtx hι hctx ρ) h hq hl₁' hl₂' hp (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
    | .univ hctx hl => fun ρ => ValidEqTermΓ.sort (wfCtx hι hctx ρ) (Level.subst_equal _ hl)
    | .prop hctx hl => fun ρ => ValidEqTermΓ.sort (wfCtx hι hctx ρ) (Level.subst_equal _ hl)
    | .inst h _ _ _ _ has _ => fun ρ =>
      absurd h (ValidSig.not_hasDeclaredType (eqInstanceArgs hι has ρ).1.validSig)
  hasArgs {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps}
      (hι : ValidInterpretation ι sig) : HasArgs sig ctx ts Θ → ValidArgs sig ι ctx ts Θ
    | .nil hctx => fun ρ => ValidEqArgsΓ.nil (wfCtx hι hctx ρ)
    | .cons (t := t) ht hts => fun ρ => by
      have hts' := hasArgs hι hts ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (hasType hι ht ρ) hts'
  eqArgs {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}
      (hι : ValidInterpretation ι sig) : EqArgs sig ctx ts us Θ → ValidEqArgs sig ι ctx ts us Θ
    | .nil hctx => fun ρ => ValidEqArgsΓ.nil (wfCtx hι hctx ρ)
    | .cons (t := t) ht hts => fun ρ => by
      have hts' := eqArgs hι hts ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (eqTerm hι ht ρ) hts'
  hasInstanceArgs {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
      {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ}
      (hι : ValidInterpretation ι sig) :
      HasInstanceArgs sig ctx as params → ValidInstanceArgs sig ι ctx as params
    | .nil hctx => fun ρ => ValidEqInstanceArgsΓ.nil (wfCtx hι hctx ρ)
    | .var (as := as) has ha => fun ρ => by
      have ha' := hasType hι ha ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (hasInstanceArgs hι has ρ) ha'
    | .secondOrder (as := as) has hB => fun ρ => by
      have hB' := hasType hι hB ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (hasInstanceArgs hι has ρ) hB'
  eqInstanceArgs {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
      {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ}
      (hι : ValidInterpretation ι sig) :
      EqInstanceArgs sig ctx as₁ as₂ params → ValidEqInstanceArgs sig ι ctx as₁ as₂ params
    | .nil hctx => fun ρ => ValidEqInstanceArgsΓ.nil (wfCtx hι hctx ρ)
    | .var (as₁ := as₁) has ha => fun ρ => by
      have ha' := eqTerm hι ha ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (eqInstanceArgs hι has ρ) ha'
    | .secondOrder (as₁ := as₁) has hB => fun ρ => by
      have hB' := eqTerm hι hB ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as₁))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (eqInstanceArgs hι has ρ) hB'
  wfTelescope {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k}
      (hι : ValidInterpretation ι sig) : WfTelescope sig ctx Θ κ → ValidTelescope sig ι ctx Θ κ
    | .nil hctx => fun ρ => ValidTelescopeΓ.nil (wfCtx hι hctx ρ)
    | .cons hA hκ hΘ _ => fun ρ =>
      ValidTelescopeΓ.cons (hasType hι hA ρ) (Universe.substLevels_bounded _ hκ)
        (wfTelescope hι hΘ ρ)

end Sic.Core
