module

public import Sic.Core.Soundness.Corecursors
public import Sic.Core.Typing
import Sic.Core.Meaning.Judgments
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Rules
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Presuppositions

/-!
# Soundness of the Judgments

Every judgment of annex 14 of RFC 36 is meaningful, as annex 18 defines it, at every value of its
level variables, in a signature whose constant declarations the interpretation gives terms of their
types, `(hyp_ι)`.

The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem, whose auxiliary theorems give the fields of the record: each case takes the values `ρ` of
the level variables, instantiates the levels of its premises by them, which commutes with the
substitutions and the entries of the contexts and of the signature, and concludes by the rule of
the same name in `Rules`, `Recursors` or `Corecursors`.
A premise that is not a subterm of the derivation, such as the well-formed signature that
`presuppositions` gives, would stop the recursion: the meaningful signature and context of a case
come from the meaning of one of its premises.

ADE prove the fundamental theorem for their judgments with a context of definitions and without
levels, whose definitions have bodies, so that they need no interpretation.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

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
  /-- An equality of telescopes in a sort. -/
  eqTelescope : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
      sigM.Distinct → sigM.ValidEntries ι sig → EqTelescope sig ctx Θ₁ Θ₂ κ →
        ValidEqTelescope sigM ι ctx Θ₁ Θ₂ κ
  /-- The fields of a constructor in a sort. -/
  wfFields : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope}
    {ctx : Context decl.levels Γ} {ps : List Parameter} {Θ : Telescope decl.levels Γ ps}
    {κ : Universe decl.levels},
      sigM.Distinct → sigM.ValidEntries ι sig → WfFields sig decl I as ctx Θ κ →
        ValidFields sigM ι ctx (fun D => decl.blockInstance I D as) (Θ.recursionAt decl.names) Θ κ
  /-- The destructors of a codata type in a sort. -/
  wfDestructors : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
      sigM.Distinct → sigM.ValidEntries ι sig → WfDestructors sig decl I as ctx ds κ →
        ValidDestructors sigM ι ctx (fun D => decl.blockInstance I D as)
          (ds.recursionAt decl.names) ds κ
  /-- A well-formed type declaration. -/
  wfTypeDeclaration : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration},
    sigM.Distinct → sigM.ValidEntries ι sig → WfTypeDeclaration sig decl →
      ValidTypeDeclaration sigM ι decl

/-- The scope of a destructor at the corecursor from the variables of a state, at levels without
variables, is the scope of the destructor at the corecursor at these levels. -/
theorem Destructors.Pos.obsSubst_corecAt_atLevels {k k' : Nat} {Γ Δ : Scope} (ρ : Fin k → Nat)
    {d : Name} {p q : Grade} {ps₁ : List Parameter} {ns : List Name} {ds : Destructors k' Δ ns}
    {Ξ : Scope} {Θ : Telescope k' Ξ ps₁} {B : Term k' (Ξ.extend ps₁.length)}
    {ψ : ResultOwnership ps₁.length} (hpos : ds.Pos d p q Ξ Θ B ψ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (Ss : States k Γ) (gs : CorecBranches k Γ) (ps' : List Parameter) :
    ∀ {a} (x : Var Ξ a),
      (hpos.obsSubst ((Term.corecAt r D qs ls ps as Ss gs ps').observation D qs ls ps
          (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst x).substLevels
        (fun i => (.ofNat (ρ i) : Level 0)) =
      hpos.obsSubst ((Term.corecAt r D qs (ls.map (Level.subst fun i => .ofNat (ρ i))) ps
          (as.substLevels fun i => .ofNat (ρ i)) (Ss.substLevels fun i => .ofNat (ρ i))
          (gs.substLevels fun i => .ofNat (ρ i)) ps').observation D qs
          (ls.map (Level.subst fun i => .ofNat (ρ i))) ps
          ((as.substLevels fun i => .ofNat (ρ i)).rename (Ren.weakenN ps'.length)))
        ((as.substLevels fun i => .ofNat (ρ i)).rename (Ren.weakenN ps'.length)).toSubst x :=
  hpos.obsSubst_substLevels _ (fun d' ps'' => by
    rw [Term.observation_substLevels, Term.corecAt_substLevels, InstanceArgs.substLevels_rename])
    (fun x => by
      rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename])

/-- The premises of `(corec_≡)` on its branches, each pair of branches meaningful for every value of
the level variables, are meaningful at the levels without variables `ρ`. -/
theorem CorecBranchesEqValid.atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs₁ gs₂ : CorecBranches k Γ}
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
      (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
      ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
        gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩)
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
      (g₁ g₂ : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
      gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
      gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
      ValidEqTerm sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs ls
          ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst)))
        g₁ g₂
        (Term.branchResult decl.names B
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))))
    (ρ : Fin k → Nat) :
    CorecBranchesEqValid sig ι (ctx.atLevels ρ) decl qs
      (ls.map (Level.subst fun i => .ofNat (ρ i))) ps hq ((List.length_map _).trans hl) hp
      (as.substLevels fun i => .ofNat (ρ i)) r (Ss.substLevels fun i => .ofNat (ρ i))
      (gs₁.substLevels fun i => .ofNat (ρ i)) (gs₂.substLevels fun i => .ofNat (ρ i)) := by
  refine ⟨fun i j T' d ps'' S' hi hSj p q ps₁ Ξ Θ B ψ hpos => ?_,
    fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ => ?_⟩
  · obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
    obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hpos
    exact ⟨_, _, CorecBranches.get_substLevels_of _ hg₁, CorecBranches.get_substLevels_of _ hg₂⟩
  · obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
    obtain ⟨g₁₀, hg₁₀, rfl⟩ := CorecBranches.get_substLevels _ hg₁
    obtain ⟨g₂₀, hg₂₀, rfl⟩ := CorecBranches.get_substLevels _ hg₂
    have hb := hgt i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hpos hg₁₀ hg₂₀ ρ
    have hcl := fun (a : Scope.Entry) (x : Var Ξ a) =>
      hpos.obsSubst_corecAt_atLevels ρ r T'.name qs ls ps as Ss gs₁ ps'' x
    simp only [Context.atLevels, Context.substLevels_append,
      Telescope.substLevels_subst_of (fun x => hcl _ x), Telescope.substLevels_substLevels,
      Term.atLevels, Term.branchResult_substLevels, States.substLevels_rename,
      Universe.substLevels_substLevels,
      Term.substLevels_subst_of (Subst.liftN_substLevels_of _ (fun x => hcl _ x)),
      Term.substLevels_substLevels] at hb
    erw [Context.substLevels_append (fun i => (.ofNat (ρ i) : Level 0)) ctx S₀] at hb
    rw [List.getFin_map]
    exact hb

/-- The premises of `(corec)` on its branches, each branch meaningful for every value of the level
variables, are meaningful at the levels without variables `ρ`: those of `(corec_≡)` at the same
branches. -/
theorem CorecBranchesValid.atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs : CorecBranches k Γ}
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
      (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
      ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
      (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
      gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
      ValidTerm sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
          ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst))) g
        (Term.branchResult decl.names B
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))))
    (ρ : Fin k → Nat) :
    CorecBranchesValid sig ι (ctx.atLevels ρ) decl qs
      (ls.map (Level.subst fun i => .ofNat (ρ i))) ps hq ((List.length_map _).trans hl) hp
      (as.substLevels fun i => .ofNat (ρ i)) r (Ss.substLevels fun i => .ofNat (ρ i))
      (gs.substLevels fun i => .ofNat (ρ i)) :=
  CorecBranchesEqValid.atLevels hq hl hp
    (fun i j T' d ps'' S' hi hSj p q ps₁ Ξ Θ B ψ hpos =>
      have ⟨g, hg⟩ := hgs i j T' d ps'' S' hi hSj p q ps₁ Ξ Θ B ψ hpos
      ⟨g, g, hg, hg⟩)
    (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ => by
      cases CorecBranches.get_inj hg₁ hg₂
      exact hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ hi hSj hpos hg₁) ρ

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names are
distinct and that gives the entries of `Σ_T` their meaning. -/
theorem soundnessIn : SoundnessIn :=
  ⟨wfConstantDefinition, wfCtx, wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs,
    eqInstanceArgs, wfTelescope, eqTelescope, wfFields, wfDestructors, wfTypeDeclaration⟩
where
  wfConstantDefinition {ι : Interpretation} {sigM sig : Signature} {d : ConstantDefinition}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfConstantDefinition sig d → ValidConstantDefinition sigM ι d
    | .intro _ _ ht => ValidConstantDefinition.intro fun inst => hasType hd hι (ht inst)
  wfCtx {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) : WfCtx sig ctx → ValidCtx sigM ι ctx
    | .empty _ => fun _ => by
      show ValidCtx₀ sigM ι .empty
      rw [ValidCtx₀]
      exact hd
    | .var h => fun ρ => (validCtx₀_var _ _).2 (wfType hd hι h ρ)
    | .secondOrder h => fun ρ => by
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
    | .inst (ls := ls) h hq hl hp hadm has => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hc := ValidEqTermΓ.inst hι h hq hl' hl' hp hadm (by rw [List.getFin_map]; exact has')
        fun _ => Level.equivalence.refl _
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
    | .ctor (ls := ls) h hc hq hl hp hadm has hts => fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hts' := hasArgs hd hι hts ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hc' := ValidEqTermΓ.ctor hι h hc hq hl' hl' hp hadm (by rw [List.getFin_map]; exact has')
        (fun _ => Level.equivalence.refl _) (by rw [List.getFin_map]; exact hts')
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact hc'
    | .recursor (ls := ls) (T := T) (t := t) (C := C) h hq hl hp hadm has ht hh hC _ hCs hCt _ hus hut
        hκ =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := hasType hd hι ht ρ
      simp only [Context.atLevels, Term.atLevels, Term.substLevels] at ht'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact ValidEqTermΓ.recursor hι h hq hl' hp hadm (by rw [List.getFin_map]; exact has') ht' hh
        (Motives.get_substLevels_of _ hC)
        (fun j T' hj => let ⟨_, hC'⟩ := hCs j T' hj; ⟨_, Motives.get_substLevels_of _ hC'⟩)
        (fun j T' C' hj hC' => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          have hCv := hasType hd hι (hCt j T' C₀ hj hC₀) ρ
          simp only [Context.atLevels, Context.substLevels, Term.atLevels, Term.substLevels] at hCv
          exact hCv)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con C' R u₁ u₂ hi hC' hR hu₁ hu₂ => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_substLevels_inv _ hR
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
          obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
          cases Branches.get_inj hu₀ hu₀'
          have hb := hasType hd hι (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ
    | .obs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (Ξ := Ξ) h hq hl hp hadm hpos
        has ht hbs =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := hasType hd hι ht ρ
      simp only [Term.atLevels, Term.substLevels] at ht'
      have hbs' := hasArgs hd hι hbs ρ
      have hcl : ∀ {a} (x : Var Ξ a),
          ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).substLevels (fun i => (.ofNat (ρ i) : Level 0)) =
            hpos.obsSubst ((t.substLevels (fun i => (.ofNat (ρ i) : Level 0))).observation D qs (ls.map (Level.subst (fun i => (.ofNat (ρ i) : Level 0)))) ps
              (as.substLevels (fun i => (.ofNat (ρ i) : Level 0)))) (as.substLevels (fun i => (.ofNat (ρ i) : Level 0))).toSubst x := fun x =>
        hpos.obsSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0)) (fun d ps' => Term.observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps as t d ps')
          (InstanceArgs.toSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0)) as) x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      have hc := ValidEqTermΓ.obs hι h hq hl' hl' hp hadm hpos (by rw [List.getFin_map]; exact has')
        (fun _ => Level.equivalence.refl _) ht' (by rw [List.getFin_map]; exact hbs')
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact hc
    | .corec (ls := ls) (as := as) (S := S) h hq hl hp hadm hpre has hh hS hss _ hSs _ _ hgs hgt =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hss' := hasArgs hd hι hss ρ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact ValidTermΓ.corec hι h hq hl' hp hadm hpre (by rw [List.getFin_map]; exact has') hh
        (States.get_substLevels_of _ hS) hss'
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hq hl hp hgs
          (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
            hasType hd hι (hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
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
    | .inst (ls₁ := ls₁) (ls₂ := ls₂) h hq hl₁ hl₂ hp hadm has hls => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hc := ValidEqTermΓ.inst hι h hq hl₁' hl₂' hp hadm (by rw [List.getFin_map]; exact has') (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
    | .ctor (ls₁ := ls₁) (ls₂ := ls₂) h hc hq hl₁ hl₂ hp hadm has hls hts => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hts' := eqArgs hd hι hts ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hc' := ValidEqTermΓ.ctor hι h hc hq hl₁' hl₂' hp hadm (by rw [List.getFin_map]; exact has')
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        (by rw [List.getFin_map]; exact hts')
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact hc'
    | .recursor (ls₁ := ls₁) (T := T) (t₁ := t₁) (C₁ := C₁) h hq hl₁ _ hp hadm has _ ht hh hC _ _ hCs₁
        hCs₂ hCt _ _ hus₁ hus₂ _ hut hκ => fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := eqTerm hd hι ht ρ
      simp only [Context.atLevels, Term.atLevels, Term.substLevels] at ht'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact ValidEqTermΓ.recursor hι h hq hl₁' hp hadm (by rw [List.getFin_map]; exact has') ht' hh
        (Motives.get_substLevels_of _ hC)
        (fun j T' hj => let ⟨_, hC'⟩ := hCs₁ j T' hj; ⟨_, Motives.get_substLevels_of _ hC'⟩)
        (fun j T' C' hj hC' => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨C₂, hC₂⟩ := hCs₂ j T' hj
          have hCv := eqTerm hd hι (hCt j T' C₀ C₂ hj hC₀ hC₂) ρ
          simp only [Context.atLevels, Context.substLevels, Term.atLevels, Term.substLevels] at hCv
          exact hCv.trans hCv.symm)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus₁ i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus₂ i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con C' R u₁ u₂ hi hC' hR hu₁ hu₂ => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_substLevels_inv _ hR
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
          obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
          have hb := eqTerm hd hι (hut i j T' con C₀ R₀ u₀ u₀' hi hC₀ hR₀ hu₀ hu₀') ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ
    | .obs (D := D) (qs := qs) (ls₁ := ls₁) (ls₂ := ls₂) (ps := ps) (as₁ := as₁) (t₁ := t₁)
        (Ξ := Ξ) h hq hl₁ hl₂ hp hadm hpos has hls ht hbs =>
      fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := eqTerm hd hι ht ρ
      simp only [Term.atLevels, Term.substLevels] at ht'
      have hbs' := eqArgs hd hι hbs ρ
      have hcl : ∀ {a} (x : Var Ξ a),
          ((hpos.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst) x).substLevels (fun i => (.ofNat (ρ i) : Level 0)) =
            hpos.obsSubst ((t₁.substLevels (fun i => (.ofNat (ρ i) : Level 0))).observation D qs (ls₁.map (Level.subst (fun i => (.ofNat (ρ i) : Level 0)))) ps
              (as₁.substLevels (fun i => (.ofNat (ρ i) : Level 0)))) (as₁.substLevels (fun i => (.ofNat (ρ i) : Level 0))).toSubst x := fun x =>
        hpos.obsSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0))
          (fun d ps' => Term.observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls₁ ps as₁ t₁ d ps')
          (InstanceArgs.toSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0)) as₁) x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      have hc := ValidEqTermΓ.obs hι h hq hl₁' hl₂' hp hadm hpos (by rw [List.getFin_map]; exact has')
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        ht' (by rw [List.getFin_map]; exact hbs')
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact hc
    | .corec (ls₁ := ls₁) (ls₂ := ls₂) (as₁ := as₁) h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ _ hss
        _ _ hSs _ _ _ _ _ hgs hgt =>
      fun ρ => by
      have hl₁' : (ls₁.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₁
      have hl₂' : (ls₂.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl₂
      have has' := eqInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hss' := eqArgs hd hι hss ρ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact ValidEqTermΓ.corec hι h hq hl₁' hl₂' hp hadm hpre (by rw [List.getFin_map]; exact has')
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        hh (States.get_substLevels_of _ hS₁) hss'
        (fun j T' hj =>
          have ⟨ps'', S₁', S₂', hS₁', hS₂'⟩ := hSs j T' hj
          ⟨ps'', _, _, States.get_substLevels_of _ hS₁', States.get_substLevels_of _ hS₂'⟩)
        (CorecBranchesEqValid.atLevels hq hl₁ hp hgs
          (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ =>
            eqTerm hd hι (hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂)) ρ)
    | .iota (qs := qs) (ls := ls) (ps := ps) (as := as) (r := r) (Cs := Cs) (us := us) (T := T)
        (C := C) h hc hq hl hp hadm has hts hi hC hu _ hCs hCt _ hus hut hκ =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hts' := hasArgs hd hι hts ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (Term.substLevels (fun i => .ofNat (ρ i))
        (.ctor _ _ _ _ _ _ _))) (fun x => by cases x <;> rfl), Term.substLevels_instantiate,
        Term.substLevels_instantiate, Args.substLevels_rename,
        Args.results_substLevels (fun i => .ofNat (ρ i)) (f' := fun D' t => .recursor r D' qs
          (ls.map (Level.subst fun i => .ofNat (ρ i))) ps (as.substLevels fun i => .ofNat (ρ i)) t
          (Cs.substLevels fun i => .ofNat (ρ i)) (us.substLevels fun i => .ofNat (ρ i)))
          (fun _ _ => rfl)]
      simp only [Term.substLevels, ← Args.terms_substLevels]
      exact ValidEqTermΓ.iota hι h hc hq hl' hp hadm (by rw [List.getFin_map]; exact has')
        (by rw [List.getFin_map]; exact hts') hi (Motives.get_substLevels_of _ hC)
        (fun j T' hj => let ⟨_, hC'⟩ := hCs j T' hj; ⟨_, Motives.get_substLevels_of _ hC'⟩)
        (fun j T' C' hj hC' => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          have hCv := hasType hd hι (hCt j T' C₀ hj hC₀) ρ
          simp only [Context.atLevels, Term.atLevels, Term.substLevels] at hCv
          exact hCv)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con C' R u hi hC' hR hu => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨R₀, hR₀, rfl⟩ := Constructor.results_substLevels_inv _ hR
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu
          have hb := hasType hd hι (hut i j T' con C₀ R₀ u₀ hi hC₀ hR₀ hu₀) ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ (Branches.get_substLevels_of _ hu)
    | .etaCtor (ls := ls) (T := T) (t := t) (C := C) (e := e) h hc hq hl hp hadm hr has ht he hi hC hu
        _ _ hCt _ _ _ hκ =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      obtain ⟨-, hj⟩ := TypeDeclaration.getElem?_of_mem_casesFrom (List.mem_of_getElem? hi)
      rw [Nat.sub_zero] at hj
      have ht' := hasType hd hι ht ρ
      have he' := hasType hd hι he ρ
      have hCv := hasType hd hι (hCt _ T C hj hC) ρ
      simp only [Context.atLevels, Context.substLevels, Term.atLevels,
        Term.substLevels] at ht' he' hCv
      rw [h.2.2] at hCv
      have hu' := Branches.get_substLevels_of (fun i => (.ofNat (ρ i) : Level 0)) hu
      erw [Term.atCtor_substLevels] at hu'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
          (fun x => by cases x <;> rfl),
        Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
          (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact ValidEqTermΓ.etaCtor hι h hc hq hl' hp hadm hr (by rw [List.getFin_map]; exact has') ht' he'
        hCv hi hu' hκ
    | .beta (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (r := r) (Ss := Ss) (gs := gs)
        (ss := ss) (bs := bs) (Ξ₀ := Ξ₀) h hq hl hp hadm hpre has hh hS hss hi hpos hg hbs _ hSs _ _
        hgs hgt =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have hss' := hasArgs hd hι hss ρ
      have hbs' := hasArgs hd hι hbs ρ
      have hcl : ∀ {a} (x : Var Ξ₀ a),
          ((hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
            as.toSubst) x).substLevels (fun i => (.ofNat (ρ i) : Level 0)) =
            hpos.obsSubst ((Term.corec r D qs (ls.map (Level.subst fun i => .ofNat (ρ i))) ps
              (as.substLevels fun i => .ofNat (ρ i)) (ss.substLevels fun i => .ofNat (ρ i)).terms
              (Ss.substLevels fun i => .ofNat (ρ i)) (gs.substLevels fun i => .ofNat (ρ i))).observation
              D qs (ls.map (Level.subst fun i => .ofNat (ρ i))) ps
              (as.substLevels fun i => .ofNat (ρ i))) (as.substLevels fun i => .ofNat (ρ i)).toSubst x :=
        fun x => hpos.obsSubst_substLevels _ (fun d' ps' => by
          rw [Term.observation_substLevels]
          simp only [Term.substLevels, ← Args.terms_substLevels])
          (InstanceArgs.toSubst_substLevels _ as) x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      simp only [Term.atLevels, Term.observed_substLevels, Universe.substLevels_substLevels,
        Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Args.substLevels_rename]
      simp only [Term.substLevels, ← Args.terms_substLevels]
      have hc := ValidEqTermΓ.beta hι h hq hl' hp hadm hpre (by rw [List.getFin_map]; exact has')
        hh (States.get_substLevels_of _ hS) hss' hi hpos (CorecBranches.get_substLevels_of _ hg)
        (by rw [List.getFin_map]; exact hbs')
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hq hl hp hgs
          (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
            hasType hd hι (hgt i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hSj hpos hg)) ρ)
      rw [List.getFin_map] at hc
      exact hc
    | .etaObs (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (t := t) (u := u) h hq hl hp hadm
        _ has ht hu hobs =>
      fun ρ => by
      have hl' : (ls.map (Level.subst fun i => (.ofNat (ρ i) : Level 0))).length = _ :=
        (List.length_map _).trans hl
      have has' := hasInstanceArgs hd hι has ρ
      simp only [Context.atLevels, Context.substLevels_substLevels] at has'
      have ht' := hasType hd hι ht ρ
      have hu' := hasType hd hι hu ρ
      simp only [Term.atLevels, Term.substLevels] at ht' hu'
      refine ValidEqTermΓ.etaObs hι h hq hl' hp hadm (by rw [List.getFin_map]; exact has') ht' hu'
        fun d p q ps' Ξ Θ B ψ hpos => ?_
      have hb := eqTerm hd hι (hobs d p q ps' Ξ Θ B ψ hpos) ρ
      have hcl : ∀ {a} (x : Var Ξ a),
          ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).substLevels
              (fun i => (.ofNat (ρ i) : Level 0)) =
            hpos.obsSubst ((t.substLevels (fun i => (.ofNat (ρ i) : Level 0))).observation D qs
              (ls.map (Level.subst (fun i => (.ofNat (ρ i) : Level 0)))) ps
              (as.substLevels (fun i => (.ofNat (ρ i) : Level 0))))
              (as.substLevels (fun i => (.ofNat (ρ i) : Level 0))).toSubst x := fun x =>
        hpos.obsSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0))
          (fun d ps' => Term.observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps
            as t d ps')
          (InstanceArgs.toSubst_substLevels (fun i => (.ofNat (ρ i) : Level 0)) as) x
      simp only [Context.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of hcl, Telescope.substLevels_substLevels, Term.atLevels,
        Term.observation_substLevels, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl),
        Term.substLevels_substLevels] at hb
      rw [List.getFin_map]
      exact hb
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
    | .nil hctx => fun ρ => ValidEqTelescopeΓ.nil (wfCtx hd hι hctx ρ)
    | .cons hA hκ hΘ _ => fun ρ =>
      ValidEqTelescopeΓ.cons (hasType hd hι hA ρ) (Universe.substLevels_bounded _ hκ)
        (wfTelescope hd hι hΘ ρ)
  eqTelescope {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
      {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      EqTelescope sig ctx Θ₁ Θ₂ κ → ValidEqTelescope sigM ι ctx Θ₁ Θ₂ κ
    | .nil hctx => fun ρ => ValidEqTelescopeΓ.nil (wfCtx hd hι hctx ρ)
    | .cons hA hκ hΘ _ => fun ρ =>
      ValidEqTelescopeΓ.cons (eqTerm hd hι hA ρ) (Universe.substLevels_bounded _ hκ)
        (eqTelescope hd hι hΘ ρ)
  wfFields {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
      {I : Instance decl.sorts decl.grades} {Γ : Scope}
      {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
      {ps : List Parameter} {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      WfFields sig decl I as ctx Θ κ →
        ValidFields sigM ι ctx (fun D => decl.blockInstance I D as) (Θ.recursionAt decl.names) Θ κ
    | .nil hctx => fun ρ => ValidFieldsΓ.nil (wfCtx hd hι hctx ρ)
    | .cons (A := A) hn hA hκ hΘ _ => fun ρ => by
      have hΘ' := wfFields hd hι hΘ ρ
      rw [show (fun D => (decl.blockInstance I D (as.rename Ren.weaken)).atLevels ρ) =
          fun D => ((decl.blockInstance I D as).atLevels ρ).rename Ren.weaken from
        funext fun D => Term.substLevels_rename _ _ (decl.blockInstance I D as)] at hΘ'
      exact ValidFieldsΓ.cons (hasType hd hι hA ρ) (Universe.substLevels_bounded _ hκ)
        (by simp [Telescope.recursionAt, Telescope.recursion, hn]) hΘ'
    | .recursive (D := D) (Θ := Θ') (q := q) (p := p) hD hΘ _ => fun ρ => by
      have hΘ' := wfFields hd hι hΘ ρ
      show ValidFieldsΓ sigM ι _ _ _ (.cons _ _ ((decl.blockInstance I D as).atLevels ρ)
        ((Θ'.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Telescope.substLevels_rename]
      refine ValidFieldsΓ.recursive (D := D)
        (by simp [Telescope.recursionAt, Telescope.recursion, TypeDeclaration.blockInstance,
          Term.blockName, hD]) ?_
      have hr : (fun i => (Telescope.cons q p (decl.blockInstance I D as)
          (Θ'.rename Ren.weaken)).recursionAt decl.names (i + 1)) = Θ'.recursionAt decl.names := by
        funext i
        simp only [Telescope.recursionAt, Telescope.recursion, Telescope.recursion_rename,
          List.getElem?_cons_succ]
      rw [hr]
      exact hΘ'
  wfDestructors {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
      {I : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name}
      {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
      {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      WfDestructors sig decl I as ctx ds κ →
        ValidDestructors sigM ι ctx (fun D => decl.blockInstance I D as)
          (ds.recursionAt decl.names) ds κ
    | .nil hctx => fun ρ => ValidDestructorsΓ.nil (wfCtx hd hι hctx ρ)
    | .cons (ps := ps) (Θ := Θ) (B := B) (ψ := ψ) (ds := ds) hn hΘ hB hκ _ hds => fun ρ => by
      have hB' := hasType hd hι hB ρ
      simp only [Context.atLevels, Context.substLevels_append] at hB'
      have hds' := wfDestructors hd hι hds ρ
      rw [show (fun D => (decl.blockInstance I D (as.rename Ren.weaken)).atLevels ρ) =
          fun D => ((decl.blockInstance I D as).atLevels ρ).rename Ren.weaken from
        funext fun D => Term.substLevels_rename _ _ (decl.blockInstance I D as)] at hds'
      exact ValidDestructorsΓ.cons
        (by simp [Destructors.recursionAt, Destructors.recursion, hn])
        (wfTelescope hd hι hΘ ρ) hB' (Universe.substLevels_bounded _ hκ) hds'
    | .recursive (d := d) (D := D) (ps := ps) (Θ := Θ) (ψ := ψ) (ds := ds) (p := p) (q := q) hD hΘ
        _ hds => fun ρ => by
      have hds' := wfDestructors hd hι hds ρ
      show ValidDestructorsΓ sigM ι _ _ _ (.cons p q (Θ.substLevels fun i => .ofNat (ρ i))
        ((decl.blockInstance I D (as.rename (Ren.weakenN ps.length))).atLevels ρ) ψ
        ((ds.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Destructors.substLevels_rename,
        show (decl.blockInstance I D (as.rename (Ren.weakenN ps.length))).atLevels ρ =
          ((decl.blockInstance I D as).atLevels ρ).rename (Ren.weakenN ps.length) from
        Term.substLevels_rename _ _ (decl.blockInstance I D as)]
      refine ValidDestructorsΓ.recursive (D := D)
        (by simp [Destructors.recursionAt, Destructors.recursion, TypeDeclaration.blockInstance,
          Term.blockName, hD]) (wfTelescope hd hι hΘ ρ) ?_
      have hr : (fun i => (Destructors.cons (d := d) p q Θ
          (decl.blockInstance I D (as.rename (Ren.weakenN ps.length))) ψ
          (ds.rename Ren.weaken)).recursionAt decl.names (i + 1)) = ds.recursionAt decl.names := by
        funext i
        simp only [Destructors.recursionAt, Destructors.recursion, Destructors.recursion_rename,
          List.getElem?_cons_succ]
      rw [hr]
      exact hds'
  wfTypeDeclaration {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
      (hd : sigM.Distinct) (hι : sigM.ValidEntries ι sig) :
      WfTypeDeclaration sig decl → ValidTypeDeclaration sigM ι decl
    | .data hb _ _ hΘ _ => by
      unfold ValidTypeDeclaration
      rw [hb]
      exact fun I hI T hT c hc =>
        wfFields hd hι (hΘ I hI T (by simp only [TypeDeclaration.dataTypes, hb]; exact hT) c hc)
    | .codata hb _ _ hds _ => by
      unfold ValidTypeDeclaration
      rw [hb]
      exact fun I hI T hT =>
        wfDestructors hd hι (hds I hI T (by simp only [TypeDeclaration.codataTypes, hb]; exact hT))


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
  -- ADE: none.
  /-- A well-formed constant declaration is meaningful in the signature that it extends, when the
  interpretation gives it a term of its type, as `(hyp_ι)` asks.
  RFC: `\mathsf{sound}.\mathsf{decl}` -/
  wfConstantDeclaration : ∀ {ι : Interpretation} {sig : Signature} {c : ConstantDeclaration},
    ValidInterpretation ι (.constantDeclaration c :: sig) → WfConstantDeclaration sig c →
      ValidConstantDeclaration (.constantDeclaration c :: sig) ι c
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
  /-- An equality of telescopes in a sort is meaningful.
  RFC: `\mathsf{sound}.\Theta_\equiv` -/
  eqTelescope : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
      ValidInterpretation ι sig → EqTelescope sig ctx Θ₁ Θ₂ κ →
        ValidEqTelescope sig ι ctx Θ₁ Θ₂ κ
  -- ADE: none.
  /-- The destructors of a codata type in a sort are meaningful.
  RFC: `\mathsf{sound}.\bar d` -/
  wfDestructors : ∀ {ι : Interpretation} {sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
      ValidInterpretation ι sig → WfDestructors sig decl I as ctx ds κ →
        ValidDestructors sig ι ctx (fun D => decl.blockInstance I D as)
          (ds.recursionAt decl.names) ds κ
  -- ADE: none.
  /-- A well-formed type declaration is meaningful.
  RFC: `\mathsf{sound}.\mathsf{data}`
  RFC: `\mathsf{sound}.\mathsf{codata}` -/
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
  wfConstantDeclaration hι _ := hι _ List.mem_cons_self
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
  eqTelescope hι h :=
    have hs := soundness_wfSig hι (presuppositions.eqTelescope h)
    soundnessIn.eqTelescope hs.1 hs.validEntries h
  wfDestructors hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfDestructors h)
    soundnessIn.wfDestructors hs.1 hs.validEntries h
  wfTypeDeclaration hι h :=
    have hs := soundness_wfSig hι (presuppositions.wfTypeDeclaration h)
    soundnessIn.wfTypeDeclaration hs.1 hs.validEntries h

end Sic.Core
