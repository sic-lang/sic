module

public import Sic.Core.Lifting.Extension
public import Sic.Core.Soundness.Corecursors
public import Sic.Core.Soundness.Nesting
public import Sic.Core.Soundness.Recursors.Premises
import Sic.Core.Meaning.Judgments
import Sic.Core.Results.Extension
import Sic.Core.Results.Substitution
import Sic.Core.Soundness.Coinduction
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Transport
import Sic.Core.Substitution.Nesting
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Induction
import Sic.Core.Typing.Lifting
import Sic.Core.Typing.Presuppositions

/-!
# Soundness of the Judgments

Every judgment of annex 15 of RFC 36 is meaningful, as annex 21 defines it, at every value of its
level variables, in a signature whose constant declarations the interpretation gives terms of their
types, `(hyp_ι)`.

The proof is by the induction on the derivations, `Derivations.induction`, with the fields of the
record as its motives: each case takes the values `ρ` of the level variables, instantiates the
levels of its premises by them, which commutes with the substitutions and the entries of the
contexts and of the signature, and concludes by the rule of the same name in `Rules`, `Recursors`,
`Corecursors`, `Transport` or `Coinduction`.
A premise that is not a subterm of the derivation, such as the well-formed signature that
`presuppositions` gives, has no hypothesis of the induction: the meaningful signature and context
of a case come from the meaning of one of its premises.
The type declarations, their fields and their destructors have an induction of their own, after that
of the judgments in a context: a nested field reads the soundness of the typing on derivations that
are no subterms of its own, those of the types that it goes through.

ADE prove the fundamental theorem for their judgments with a context of definitions and without
levels, whose definitions have bodies, so that they need no interpretation.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

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
    sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → WfConstantDefinition sig d →
      ValidConstantDefinition sigM ι d
  /-- A well-formed context. -/
  wfCtx : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → WfCtx sig ctx → ValidCtx sigM ι ctx
  /-- A type. -/
  wfType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {A : Term k Γ}, sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig →
      WfType sig ctx A → ValidType sigM ι ctx A
  /-- An equality of types. -/
  eqType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {A B : Term k Γ}, sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig →
      EqType sig ctx A B → ValidEqType sigM ι ctx A B
  /-- A typing. -/
  hasType : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {t A : Term k Γ}, sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig →
      HasType sig ctx t A → ValidTerm sigM ι ctx t A
  /-- An equality of terms. -/
  eqTerm : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ctx : Context k Γ} {t u A : Term k Γ}, sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig →
      EqTerm sig ctx t u A → ValidEqTerm sigM ι ctx t u A
  /-- Arguments of a telescope. -/
  hasArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → HasArgs sig ctx ts Θ → ValidArgs sigM ι ctx ts Θ
  /-- Equal arguments of a telescope. -/
  eqArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → EqArgs sig ctx ts us Θ →
        ValidEqArgs sigM ι ctx ts us Θ
  /-- Arguments of an instance. -/
  hasInstanceArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → HasInstanceArgs sig ctx as params →
        ValidInstanceArgs sigM ι ctx as params
  /-- Equal arguments of instances. -/
  eqInstanceArgs : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → EqInstanceArgs sig ctx as₁ as₂ params →
        ValidEqInstanceArgs sigM ι ctx as₁ as₂ params
  /-- A telescope in a sort. -/
  wfTelescope : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → WfTelescope sig ctx Θ κ →
        ValidTelescope sigM ι ctx Θ κ
  /-- An equality of telescopes in a sort. -/
  eqTelescope : ∀ {ι : Interpretation} {sigM sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → EqTelescope sig ctx Θ₁ Θ₂ κ →
        ValidEqTelescope sigM ι ctx Θ₁ Θ₂ κ

/-- The scope of a destructor at the corecursor from the variables of a state, at levels without
variables, is the scope of the destructor at the corecursor at these levels. -/
theorem Destructors.Pos.obsSubst_corecAt_atLevels {k k' : Nat} {Γ Δ : Scope} (ρ : Fin k → Nat)
    {d : Name} {p q ς : Grade} {ps₁ : List Parameter} {ns : List Name} {ds : Destructors k' Δ ns}
    {Ξ : Scope} {Θ : Telescope k' Ξ ps₁} {B : Term k' (Ξ.extend ps₁.length)}
    {ψ : ResultOwnership Grade ps₁.length} (hpos : ds.Pos d p q ς Ξ Θ B ψ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (Ss : States k Γ) (gs : DestructorBranches k Γ) (ps' : List Parameter) :
    ∀ {a} (x : Var Ξ a),
      (hpos.obsSubst ((Term.corecAt r D qs ls ps as Ss gs ps').observation D qs ls ps
          (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst x).substLevels
        (fun i => (.ofNat (ρ i) : Level 0)) =
      hpos.obsSubst ((Term.corecAt r D qs (ls.map (Level.atLevels ρ)) ps
          (as.atLevels ρ) (Ss.substLevels fun i => .ofNat (ρ i))
          (gs.substLevels fun i => .ofNat (ρ i)) ps').observation D qs
          (ls.map (Level.atLevels ρ)) ps
          ((as.atLevels ρ).rename (Ren.weakenN ps'.length)))
        ((as.atLevels ρ).rename (Ren.weakenN ps'.length)).toSubst x :=
  hpos.obsSubst_substLevels _ (fun d' ps'' => by
    rw [Term.observation_substLevels, Term.corecAt_substLevels, InstanceArgs.substLevels_rename,
      Level.subst_ofNat, InstanceArgs.atLevels])
    (fun x => by
      rw [InstanceArgs.toSubst_substLevels, InstanceArgs.substLevels_rename, InstanceArgs.atLevels])

/-- The premises of `(corec_≡)` on its branches, each pair of branches meaningful for every value of
the level variables, are meaningful at the levels without variables `ρ`. -/
theorem CorecBranchesEqValid.atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs₁ gs₂ : DestructorBranches k Γ}
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
      (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ →
      ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
        gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩)
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (g₁ g₂ : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ) →
      gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
      gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
      ValidEqTerm sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs ls
          ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst)))
        g₁ g₂
        (Term.branchResult decl.names B
          ((decl.sort hqp.inst).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))))
    (ρ : Fin k → Nat) :
    CorecBranchesEqValid sig ι (ctx.atLevels ρ) decl qs
      (ls.map (Level.atLevels ρ)) ps hqp (Level.length_atLevels ρ hl)
      (as.atLevels ρ) r (Ss.substLevels fun i => .ofNat (ρ i))
      (gs₁.substLevels fun i => .ofNat (ρ i)) (gs₂.substLevels fun i => .ofNat (ρ i)) := by
  refine ⟨fun i j T' d ps'' S' hi hSj p q ς ps₁ Ξ Θ B ψ hpos => ?_,
    fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ => ?_⟩
  · obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
    obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hpos
    exact ⟨_, _, DestructorBranches.get_substLevels_of _ hg₁,
      DestructorBranches.get_substLevels_of _ hg₂⟩
  · obtain ⟨S₀, hS₀, rfl⟩ := States.get_substLevels _ hSj
    obtain ⟨g₁₀, hg₁₀, rfl⟩ := DestructorBranches.get_substLevels _ hg₁
    obtain ⟨g₂₀, hg₂₀, rfl⟩ := DestructorBranches.get_substLevels _ hg₂
    have hb := hgt i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hpos hg₁₀ hg₂₀ ρ
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

/-- The premises of `(rec)` on the motives and on the branches, each motive meaningful at the levels
without variables `ρ`, are meaningful at these levels: those of the motives and of the branches at
these levels. -/
theorem ValidRecursorPremises.atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {hqp : Instance.AsMany decl.sorts decl.grades qs ps}
    {as : InstanceArgs k Γ decl.scope} {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k}
    (ρ : Fin k → Nat)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCt : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι ((ctx.var (.inst T'.name qs ls ps as)).atLevels ρ) (C'.atLevels ρ)
        ((Term.sort κ).atLevels ρ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params hqp.inst).length,
        (con.nestResultParams hqp.inst decl.names).length, u⟩) :
    ValidRecursorPremises sig ι (ctx.atLevels ρ) decl qs (ls.map (Level.atLevels ρ)) ps hqp
      (as.atLevels ρ) (Cs.atLevels ρ) (us.atLevels ρ) (κ.atLevels ρ) where
  motives j T' hj := let ⟨_, hC'⟩ := hCs j T' hj; ⟨_, Motives.get_substLevels_of _ hC'⟩
  motives_valid j T' C' hj hC' := by
    obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
    have hCv := hCt j T' C₀ hj hC₀
    simp only [Context.atLevels, Context.substLevels, Term.atLevels, Term.substLevels] at hCv
    exact hCv
  branches i j T' con hi := let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩

/-- The types of the recursive results of a constructor at the motives of a recursor, in a
signature whose type declarations another signature has, are those of the other signature at the
levels `ls'`. -/
theorem Constructor.ResultTypes.substLevels_ofTypeDeclarations {sig sig' : Signature}
    {v : Lifting.Variables} {j g k' k k'' : Nat} {Δ' Δ : Scope} {c : Constructor j g k' Δ}
    {I : Instance j g} {names : List Name} {qs : List Quality} {ls : List (Level k)}
    {gs : List Grade} {as : InstanceArgs k Δ' Δ} {κ : Universe k} {Cs : Motives k Δ'}
    {ps' : List Parameter} {hl : ls.length = k'} {χ : Grade}
    {R : Telescope k (Δ'.extend (c.params I).length) ps'} {πs : List Grade}
    (hs : ∀ decl, Entry.typeDeclaration decl ∈ sig → Entry.typeDeclaration decl ∈ sig')
    (ls' : Fin k → Level k'')
    (h : Constructor.ResultTypes sig v c I names (ls.getFin hl) as
      (Lifting.ofMotives names qs ls gs as κ.level χ Cs) R πs) :
    Constructor.ResultTypes sig' v c I names
      ((ls.map (Level.subst ls')).getFin ((List.length_map _).trans hl)) (as.substLevels ls')
      (Lifting.ofMotives names qs (ls.map (Level.subst ls')) gs (as.substLevels ls')
        (κ.substLevels ls').level χ (Cs.substLevels ls'))
      (R.substLevels ls') πs :=
  Terms.ResultTypes.ofTypeDeclarations hs (Constructor.ResultTypes.substLevels_ofMotives _ h)

/-- The premises of `(corec)` on its branches, each branch meaningful for every value of the level
variables, are meaningful at the levels without variables `ρ`: those of `(corec_≡)` at the same
branches. -/
theorem CorecBranchesValid.atLevels {sig : Signature} {ι : Interpretation} {k : Nat}
    {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels) {as : InstanceArgs k Γ decl.scope}
    {r : Grade} {Ss : States k Γ} {gs : DestructorBranches k Γ}
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
      (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ →
      ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
    (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
      (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      (hd : (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ) →
      gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
      ValidTerm sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
          ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst))) g
        (Term.branchResult decl.names B
          ((decl.sort hqp.inst).substLevels (ls.getFin hl)) r
          (ψ.constant.getD .unrestrictedUnrestricted)
          ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
              ls ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))))
    (ρ : Fin k → Nat) :
    CorecBranchesValid sig ι (ctx.atLevels ρ) decl qs
      (ls.map (Level.atLevels ρ)) ps hqp (Level.length_atLevels ρ hl)
      (as.atLevels ρ) r (Ss.substLevels fun i => .ofNat (ρ i))
      (gs.substLevels fun i => .ofNat (ρ i)) :=
  CorecBranchesEqValid.atLevels hqp hl
    (fun i j T' d ps'' S' hi hSj p q ς ps₁ Ξ Θ B ψ hpos =>
      have ⟨g, hg⟩ := hgs i j T' d ps'' S' hi hSj p q ς ps₁ Ξ Θ B ψ hpos
      ⟨g, g, hg, hg⟩)
    (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ => by
      cases DestructorBranches.get_inj hg₁ hg₂
      exact hgt i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ hi hSj hpos hg₁) ρ

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names are
distinct and that gives the entries of `Σ_T` their meaning. -/
theorem soundnessIn : SoundnessIn := by
  suffices H : Derivations.Conclusion
      (wfConstantDefinition := fun sig d _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidConstantDefinition sigM ι d)
      (wfCtx := fun sig {k Γ} ctx _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidCtx sigM ι ctx)
      (wfType := fun sig {k Γ} ctx A _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidType sigM ι ctx A)
      (eqType := fun sig {k Γ} ctx A B _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidEqType sigM ι ctx A B)
      (hasType := fun sig {k Γ} ctx t A _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidTerm sigM ι ctx t A)
      (eqTerm := fun sig {k Γ} ctx t u A _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidEqTerm sigM ι ctx t u A)
      (hasArgs := fun sig {k Γ ps} ctx ts Θ _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidArgs sigM ι ctx ts Θ)
      (eqArgs := fun sig {k Γ ps} ctx ts us Θ _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidEqArgs sigM ι ctx ts us Θ)
      (hasInstanceArgs := fun sig {k Γ Δ} ctx as params _ => ∀ {ι sigM}, sigM.Distinct →
        sigM.LiftsInOrder → sigM.ValidEntries ι sig → ValidInstanceArgs sigM ι ctx as params)
      (eqInstanceArgs := fun sig {k Γ Δ} ctx as₁ as₂ params _ => ∀ {ι sigM}, sigM.Distinct →
        sigM.LiftsInOrder → sigM.ValidEntries ι sig → ValidEqInstanceArgs sigM ι ctx as₁ as₂ params)
      (wfTelescope := fun sig {k Γ ps} ctx Θ κ _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidTelescope sigM ι ctx Θ κ)
      (eqTelescope := fun sig {k Γ ps} ctx Θ₁ Θ₂ κ _ => ∀ {ι sigM}, sigM.Distinct →
        sigM.LiftsInOrder → sigM.ValidEntries ι sig → ValidEqTelescope sigM ι ctx Θ₁ Θ₂ κ) from
    ⟨fun hdis hord hι h => H.wfConstantDefinition h hdis hord hι,
      fun hdis hord hι h => H.wfCtx h hdis hord hι, fun hdis hord hι h => H.wfType h hdis hord hι,
      fun hdis hord hι h => H.eqType h hdis hord hι, fun hdis hord hι h => H.hasType h hdis hord hι,
      fun hdis hord hι h => H.eqTerm h hdis hord hι, fun hdis hord hι h => H.hasArgs h hdis hord hι,
      fun hdis hord hι h => H.eqArgs h hdis hord hι,
      fun hdis hord hι h => H.hasInstanceArgs h hdis hord hι,
      fun hdis hord hι h => H.eqInstanceArgs h hdis hord hι,
      fun hdis hord hι h => H.wfTelescope h hdis hord hι,
      fun hdis hord hι h => H.eqTelescope h hdis hord hι⟩
  apply Derivations.induction
  case wfConstantDefinition_intro =>
    exact fun κ hA ht hA_ih ht_ih => fun hdis hord hι =>
      ValidConstantDefinition.intro fun inst => ht_ih inst hdis hord hι
  case wfCtx_empty =>
    intro sig k h h_ih ι sigM hdis hord hι
    exact fun _ => by
      show ValidCtx₀ sigM ι .empty
      rw [ValidCtx₀]
      exact hdis
  case wfCtx_var =>
    exact fun h h_ih => fun hdis hord hι => fun ρ =>
      (validCtx₀_var _ _).2 (h_ih hdis hord hι ρ)
  case wfCtx_secondOrder =>
    refine fun h h_ih => fun hdis hord hι => ?_
    exact fun ρ => by
      have hA := h_ih hdis hord hι ρ
      simp only [Context.atLevels, Context.substLevels_append] at hA
      exact (validCtx₀_secondOrder _ _ _ _).2 hA
  case wfType_univType =>
    exact fun h h_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.univType (h_ih hdis hord hι ρ)
  case wfType_propType =>
    exact fun h h_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.propType (h_ih hdis hord hι ρ)
  case eqType_refl => exact fun h h_ih => fun hdis hord hι => h_ih hdis hord hι
  case eqType_symm => exact fun h h_ih => fun hdis hord hι => fun ρ => (h_ih hdis hord hι ρ).symm
  case eqType_trans =>
    exact fun h₁ h₂ h₁_ih h₂_ih => fun hdis hord hι => fun ρ =>
      (h₁_ih hdis hord hι ρ).trans (h₂_ih hdis hord hι ρ)
  case eqType_univType =>
    exact fun h h_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.univType (h_ih hdis hord hι ρ)
  case eqType_propType =>
    exact fun h h_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.propType (h_ih hdis hord hι ρ)
  case hasType_var =>
    exact fun hctx hx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidTermΓ.var (hctx_ih hdis hord hι ρ) (hx.substLevels _)
  case hasType_secondOrder =>
    refine fun hX hts hts_ih => fun hdis hord hι => ?_
    exact fun ρ => by
      have hts' := hts_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
  case hasType_const =>
    intro sig k Γ ctx f j k' g m p A qs ls ps hctx h hqp hl hctx_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have hc := ValidTermΓ.const (hctx_ih hdis hord hι ρ) hι h hqp hl'
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
  case hasType_univ =>
    refine fun hctx hctx_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTermΓ.sort (q := .type) (hctx_ih hdis hord hι ρ) (Level.equivalence.refl _)
  case hasType_prop =>
    refine fun hctx hctx_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTermΓ.sort (q := .prop) (hctx_ih hdis hord hι ρ) (Level.equivalence.refl _)
  case hasType_inst =>
    intro sig k Γ ctx decl D ζ qs ls ps as h hqp hl hadm has has_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hc := ValidEqTermΓ.inst hι h hqp hl' hl' hadm has'
        fun _ => Level.equivalence.refl _
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
  case hasType_equality =>
    refine fun hA ht hu hA_ih ht_ih hu_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTermΓ.equality (hA_ih hdis hord hι ρ) (ht_ih hdis hord hι ρ)
        (hu_ih hdis hord hι ρ) (Level.equivalence.refl _)
  case hasType_reflProof =>
    refine fun hA ht hA_ih ht_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidTermΓ.reflProof (hA_ih hdis hord hι ρ) (ht_ih hdis hord hι ρ)
  case hasType_transp =>
    intro sig k Γ ctx s l κ A t₁ t₂ t u C hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih
      ι sigM hdis hord hι
    exact fun ρ => by
      have hu' := hu_ih hdis hord hι ρ
      simp only [Term.atLevels] at hu' ⊢
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)] at hu'
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      exact ValidEqTermΓ.transp (hA_ih hdis hord hι ρ) (ht₁_ih hdis hord hι ρ)
        (ht₂_ih hdis hord hι ρ) (hC_ih hdis hord hι ρ) (ht_ih hdis hord hι ρ) hu'
  case hasType_propExt =>
    refine fun hA hB ht hu hA_ih hB_ih ht_ih hu_ih => fun hdis hord hι => ?_
    exact fun ρ => by
      have ht' := ht_ih hdis hord hι ρ
      have hu' := hu_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels_rename] at ht' hu'
      exact ValidTermΓ.propExt (hA_ih hdis hord hι ρ) (hB_ih hdis hord hι ρ) ht' hu'
  case hasType_coind =>
    intro sig k Γ ctx decl D T qs ls ps as l' t₁ t₂ t As gs h' A κs h hqp hl hadm has hh hA hAl
      hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih hAt_ih ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih
      hgr_ih ι sigM hdis hord hι
    exact fun ρ => by
      let L' : Fin k → Level 0 := fun i => .ofNat (ρ i)
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      let p₀ : Parameter := ⟨Grade.one, Grade.one⟩
      have hsort := congrArg Universe.level
        (Universe.substLevels_substLevels_getFin L' (decl.sort hqp.inst) ls hl)
      simp only [Term.atLevels]
      rw [Term.substLevels, show ((decl.sort hqp.inst).substLevels
        (ls.getFin hl)).level.subst L' = _ from hsort]
      refine ValidTermΓ.coind (l' := l'.atLevels ρ) (κs := fun i => (κs i).atLevels ρ) hι h hqp hl'
        hadm has' hh (Terms.get_substLevels_of _ hA)
        ((Terms.length_substLevels _ As).trans hAl) ?_ (ht₁_ih hdis hord hι ρ)
        (ht₂_ih hdis hord hι ρ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro j T' A' hj hA'
        obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels _ hA'
        have ih := hAt_ih j T' A₀ hj hA₀ hdis hord hι ρ
        simp only [Context.atLevels, Term.atLevels, Context.substLevels, Term.substLevels_rename]
          at ih
        exact ih
      · have ih := ht_ih hdis hord hι ρ
        simp only [Context.atLevels, Term.atLevels] at ih
        rw [show ((A.subst₀ (Subst₀.liftN 1 (Subst₀.single t₁))).subst₀ (Subst₀.single t₂)) =
            A.instantiate (Args.cons (p := p₀) t₁ (Args.cons (p := p₀) t₂ .nil)) from rfl,
          Term.substLevels_instantiate] at ih
        exact ih
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
        obtain ⟨g, hg⟩ := hgs i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
        exact ⟨_, DestructorBranches.get_substLevels_of _ hg⟩
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
        have e := congrArg (Telescope.substLevels L') (hΘ i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos)
        rw [Telescope.substLevels_subst_of
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
          Telescope.substLevels_subst_of
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ .zero) : Term k (Γ.extend 3))),
          Telescope.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at e
        exact e
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
        have e := congrArg (Term.substLevels L') (hB i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos)
        rw [Term.substLevels_subst_of (Subst.liftN_substLevels_of _
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ .zero) : Term k (Γ.extend 3)))),
          Term.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at e
        exact e
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hpos hn
        obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels _ hA'
        have ih := hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ hi hA₀ hpos hn hdis hord hι ρ
        simp only [Context.atLevels, Term.atLevels] at ih
        erw [Context.substLevels_append] at ih
        simp only [Context.substLevels, Term.substLevels_rename, Term.substLevels] at ih
        erw [Telescope.substLevels_subst_of
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
          Telescope.substLevels_substLevels_getFin,
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
          Term.substLevels_substLevels_getFin, InstanceArgs.substLevels_rename] at ih
        exact ih
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hpos hn hg
        obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels _ hA'
        obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels _ hg
        have ih := hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ g₀ hi hA₀ hpos hn hg₀ hdis hord hι ρ
        simp only [Context.atLevels, Term.atLevels] at ih
        erw [Context.substLevels_append] at ih
        simp only [Context.substLevels, Term.substLevels_rename, Term.substLevels] at ih
        erw [Telescope.substLevels_subst_of
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
          Telescope.substLevels_substLevels_getFin,
          Term.substLevels_subst_of (Subst.liftN_substLevels_of _
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)))),
          Term.substLevels_substLevels_getFin, Term.observation_substLevels,
          Term.observation_substLevels, InstanceArgs.substLevels_rename] at ih
        exact ih
      · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hpos hn hj' hA'' hg
        obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_substLevels _ hA'
        obtain ⟨A₀', hA₀', rfl⟩ := Terms.get_substLevels _ hA''
        obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_substLevels _ hg
        have ih := hgr_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ D' j' A₀' g₀ hi hA₀ hpos hn
          hj' hA₀' hg₀ hdis hord hι ρ
        simp only [Context.atLevels, Term.atLevels] at ih
        replace ih : ValidTermΓ sigM ι _ _ ((((A₀'.rename (Ren.liftN 2 (Ren.weakenN 3))).rename
            (Ren.liftN 2 (Ren.weakenN ps₁.length))).instantiate
              (Args.cons (p := p₀) ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)
              (Args.cons (p := p₀) ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁) .nil))).substLevels L') := ih
        erw [Term.substLevels_instantiate, Context.substLevels_append,
          Telescope.substLevels_subst_of
            (hpos.obsSubst_observation_substLevels L' T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) (Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3))),
          Telescope.substLevels_substLevels_getFin] at ih
        simp only [Context.substLevels, Term.substLevels_rename, Args.substLevels] at ih
        rw [Term.observation_substLevels, Term.observation_substLevels,
          InstanceArgs.substLevels_rename] at ih
        exact ih
  case hasType_ctor =>
    intro sig k Γ ctx decl D T con qs ls ps as h hc hqp hl hadm has ts hts has_ih hts_ih ι sigM
      hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hts' := hts_ih hdis hord hι ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hc' := ValidEqTermΓ.ctor hι h hc hqp hl' hl' hadm has'
        (fun _ => Level.equivalence.refl _) (by rw [List.getFin_map]; exact hts')
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact hc'
  case hasType_recursor =>
    intro sig k Γ ctx decl D T qs ls ps as r ς χ t Cs us κ h' C h hqp hl hadm has ht hh hC hCl hCs
      hCt hul hus Rs hRs hut hκ has_ih ht_ih hCt_ih hut_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have ht' := ht_ih hdis hord hι ρ
      rw [Term.atLevels_inst] at ht'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact ValidEqTermΓ.recursor hι hord h hqp hl' hl' hadm has'
        ht' hh
        (Motives.get_substLevels_of _ hC)
        (ValidRecursorPremises.atLevels ρ hCs
          (fun j T' C' hj hC' => hCt_ih j T' C' hj hC' hdis hord hι ρ) hus)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h)
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h)
        (fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
          obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
          cases Branches.get_inj hu₀ hu₀'
          have hb := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ hdis hord hι ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ
  case hasType_obs =>
    intro sig k Γ ctx decl D T qs ls ps as t d p q ς ps' Ξ Θ B ψ bs h hqp hl hadm hd has ht hbs
      has_ih ht_ih hbs_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have ht' := ht_ih hdis hord hι ρ
      rw [Term.atLevels_inst] at ht'
      have hbs' := hbs_ih hdis hord hι ρ
      have hcl := fun {a} (x : Var Ξ a) =>
        hd.obsSubst_observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps as t x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      have hc := ValidEqTermΓ.obs hι h hqp hl' hl' hadm hd has'
        (fun _ => Level.equivalence.refl _) ht' (by rw [List.getFin_map]; exact hbs')
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact hc
  case hasType_corec =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' ps' S ss h hqp hl hadm hpre has hh hS hss
      hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih hgt_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hss' := hss_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact ValidTermΓ.corec hι h hqp hl' hadm hpre has' hh
        (States.get_substLevels_of _ hS) hss'
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hqp hl hgs
          (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg =>
            hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hpos hg hdis hord hι) ρ)
  case hasType_conv =>
    exact fun ht h ht_ih h_ih => fun hdis hord hι => fun ρ =>
      (ht_ih hdis hord hι ρ).conv (h_ih hdis hord hι ρ)
  case eqTerm_refl => exact fun h h_ih => fun hdis hord hι => h_ih hdis hord hι
  case eqTerm_symm => exact fun h h_ih => fun hdis hord hι => fun ρ => (h_ih hdis hord hι ρ).symm
  case eqTerm_trans =>
    exact fun h₁ h₂ h₁_ih h₂_ih => fun hdis hord hι => fun ρ =>
      (h₁_ih hdis hord hι ρ).trans (h₂_ih hdis hord hι ρ)
  case eqTerm_conv =>
    exact fun h hA h_ih hA_ih => fun hdis hord hι => fun ρ =>
      (h_ih hdis hord hι ρ).conv (hA_ih hdis hord hι ρ)
  case eqTerm_irr =>
    refine fun ht hu hA ht_ih hu_ih hA_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTermΓ.irr (ht_ih hdis hord hι ρ) (hu_ih hdis hord hι ρ) (hA_ih hdis hord hι ρ)
  case eqTerm_secondOrder =>
    refine fun hX hts hts_ih => fun hdis hord hι => ?_
    exact fun ρ => by
      have hts' := hts_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels_instantiate]
      exact ValidEqTermΓ.secondOrder hts'.1 (hX.substLevels _) hts'
  case eqTerm_delta =>
    intro sig k Γ ctx d qs ls ps hctx h hqp hl hctx_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have hc := ValidEqTermΓ.delta (hctx_ih hdis hord hι ρ) hι h hqp hl'
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
  case eqTerm_const =>
    intro sig k Γ ctx f j k' g m p A qs ls₁ ls₂ ps hctx h hqp hl₁ hl₂ hls hctx_ih ι sigM hdis hord
      hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have hc := ValidEqTermΓ.const (hctx_ih hdis hord hι ρ) hι h hqp hl₁' hl₂' (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Signature.instanceType_substLevels]
      exact hc
  case eqTerm_univ =>
    exact fun hctx hl hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.sort (hctx_ih hdis hord hι ρ) (Level.subst_equal _ hl)
  case eqTerm_prop =>
    exact fun hctx hl hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqTermΓ.sort (hctx_ih hdis hord hι ρ) (Level.subst_equal _ hl)
  case eqTerm_inst =>
    intro sig k Γ ctx decl D ζ qs ls₁ ls₂ ps as₁ as₂ h hqp hl₁ hl₂ hadm has hls has_ih ι sigM hdis
      hord hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have has' := (has_ih hdis hord hι).atLevels hl₁ ρ
      have hc := ValidEqTermΓ.inst hι h hqp hl₁' hl₂' hadm has' (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels, Universe.substLevels_substLevels]
      exact hc
  case eqTerm_equality =>
    refine fun hA ht hu hl hA_ih ht_ih hu_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTermΓ.equality (hA_ih hdis hord hι ρ) (ht_ih hdis hord hι ρ)
        (hu_ih hdis hord hι ρ) (Level.subst_equal _ hl)
  case eqTerm_transp =>
    intro sig k Γ ctx s l κ A A' t₁ t₁' t₂ t₂' t t' u u' C C' hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih
      ht₂_ih hC_ih ht_ih hu_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hu' := hu_ih hdis hord hι ρ
      simp only [Term.atLevels] at hu' ⊢
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)] at hu'
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      exact ValidEqTermΓ.transp (hA_ih hdis hord hι ρ) (ht₁_ih hdis hord hι ρ)
        (ht₂_ih hdis hord hι ρ) (hC_ih hdis hord hι ρ) (ht_ih hdis hord hι ρ) hu'
  case eqTerm_transpSame =>
    intro sig k Γ ctx s l κ A t₁ t₂ t u C hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih
      hu_ih hCC_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hu' := hu_ih hdis hord hι ρ
      have hCC' := hCC_ih hdis hord hι ρ
      simp only [Term.atLevels] at hu' hCC' ⊢
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)] at hu' hCC'
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₂.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)] at hCC' ⊢
      exact ValidEqTermΓ.transpSame hu' hCC'
  case eqTerm_ctor =>
    intro sig k Γ ctx decl D T con qs ls₁ ls₂ ps as₁ as₂ h hc hqp hl₁ hl₂ hadm has hls ts us hts
      has_ih hts_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have has' := (has_ih hdis hord hι).atLevels hl₁ ρ
      have hts' := hts_ih hdis hord hι ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      have hc' := ValidEqTermΓ.ctor hι h hc hqp hl₁' hl₂' hadm has'
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        (by rw [List.getFin_map]; exact hts')
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact hc'
  case eqTerm_recursor =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ r ς χ t₁ t₂ Cs₁ Cs₂ us₁ us₂ κ h' C₁ h hqp hl₁
      hl₂ hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁ hus₂ hes Rs₁ Rs₂ hRs₁ hRs₂
      hut hκ has_ih ht_ih hCt_ih hut_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have has' := (has_ih hdis hord hι).atLevels hl₁ ρ
      have ht' := ht_ih hdis hord hι ρ
      rw [Term.atLevels_inst] at ht'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (t₁.substLevels fun i => .ofNat (ρ i)))
        (fun x => by cases x <;> rfl)]
      simp only [Term.substLevels]
      exact ValidEqTermΓ.recursor hι hord h hqp hl₁' hl₂' hadm
        has' ht' hh
        (Motives.get_substLevels_of _ hC)
        (ValidRecursorPremises.atLevels ρ hCs₁ (fun j T' C' hj hC' =>
          let ⟨_, hC₂⟩ := hCs₂ j T' hj
          have hCv := hCt_ih j T' C' _ hj hC' hC₂ hdis hord hι ρ
          hCv.trans hCv.symm) hus₁)
        (fun i j T' con hi => let ⟨_, hu⟩ := hus₂ i j T' con hi; ⟨_, Branches.get_substLevels_of _ hu⟩)
        (fun i j T' con hi => (hRs₁ i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h)
        (fun i j T' con hi => (hRs₂ i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h)
        (fun i j T' con C' u₁ u₂ hi hC' hu₁ hu₂ => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu₁
          obtain ⟨u₀', hu₀', rfl⟩ := Branches.get_substLevels _ hu₂
          have hb := hut_ih i j T' con C₀ u₀ u₀' hi hC₀ hu₀ hu₀' hdis hord hι ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ
  case eqTerm_obs =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ t₁ t₂ d p q ς ps' Ξ Θ B ψ bs₁ bs₂ h hqp hl₁ hl₂
      hadm hd has hls ht hbs has_ih ht_ih hbs_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have has' := (has_ih hdis hord hι).atLevels hl₁ ρ
      have ht' := ht_ih hdis hord hι ρ
      rw [Term.atLevels_inst] at ht'
      have hbs' := hbs_ih hdis hord hι ρ
      have hcl := fun {a} (x : Var Ξ a) =>
        hd.obsSubst_observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls₁ ps as₁ t₁ x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      have hc := ValidEqTermΓ.obs hι h hqp hl₁' hl₂' hadm hd has'
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        ht' (by rw [List.getFin_map]; exact hbs')
      rw [List.getFin_map] at hc
      simp only [Term.atLevels, Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Term.substLevels, ← Args.terms_substLevels]
      exact hc
  case eqTerm_corec =>
    intro sig k Γ ctx decl D T qs ls₁ ls₂ ps as₁ as₂ r Ss₁ Ss₂ gs₁ gs₂ h' ps' S₁ S₂ ss₁ ss₂ h hqp
      hl₁
      hl₂ hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁ hgl₂ hgs hgt has_ih
      hss_ih hSt_ih hSe_ih hgt_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl₁' := Level.length_atLevels (ls := ls₁) ρ hl₁
      have hl₂' := Level.length_atLevels (ls := ls₂) ρ hl₂
      have has' := (has_ih hdis hord hι).atLevels hl₁ ρ
      have hss' := hss_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels, ← Args.terms_substLevels]
      exact ValidEqTermΓ.corec hι h hqp hl₁' hl₂' hadm hpre has'
        (by
          rw [List.getFin_map, List.getFin_map]
          exact fun i => Level.subst_equal _ (hls i))
        hh (States.get_substLevels_of _ hS₁) hss'
        (fun j T' hj =>
          have ⟨ps'', S₁', S₂', hS₁', hS₂'⟩ := hSs j T' hj
          ⟨ps'', _, _, States.get_substLevels_of _ hS₁', States.get_substLevels_of _ hS₂'⟩)
        (CorecBranchesEqValid.atLevels hqp hl₁ hgs
          (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ =>
            hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂ hdis hord hι) ρ)
  case eqTerm_iota =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ Cs us κ i j C h hc hqp hl hadm u has ts hts
      hi hC hu rs hrs hCl hCs hCt hul hus Rs hRs hut hκ has_ih hts_ih hCt_ih hut_ih ι sigM hdis hord
      hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hts' := hts_ih hdis hord hι ρ
      simp only [Telescope.atLevels, Constructor.fieldsAt_substLevels] at hts'
      simp only [Term.atLevels]
      rw [Term.substLevels_subst₀_of (σ' := Subst₀.single (Term.substLevels (fun i => .ofNat (ρ i))
        (.ctor _ _ _ _ _ _ _))) (fun x => by cases x <;> rfl), Term.substLevels_instantiate,
        Term.substLevels_instantiate, Args.substLevels_rename]
      simp only [Term.substLevels, ← Args.terms_substLevels]
      exact ValidEqTermΓ.iota hι hord h hc hqp hl' hadm has'
        (by rw [List.getFin_map]; exact hts') hi (Motives.get_substLevels_of _ hC)
        (ValidRecursorPremises.atLevels ρ hCs
          (fun j T' C' hj hC' => hCt_ih j T' C' hj hC' hdis hord hι ρ) hus)
        (fun i j T' con hi => (hRs i j T' con hi).imp fun _ h =>
          Constructor.ResultTypes.substLevels_ofTypeDeclarations (fun _ he => (hι _ he).1) _ h)
        (fun i j T' con C' u hi hC' hu => by
          obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels _ hC'
          obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_substLevels _ hu
          have hb := hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ hdis hord hι ρ
          simp only [Context.atLevels, Context.substLevels_append, Term.atLevels,
            Constructor.fieldsAt_substLevels, Term.substLevels_rename] at hb
          erw [Term.atCtor_substLevels] at hb
          rw [List.getFin_map]
          exact hb)
        hκ (Branches.get_substLevels_of _ hu)
        (Terms.ResultTerms.ofTypeDeclarations (fun _ he => (hι _ he).1)
          (Constructor.ResultTerms.substLevels_recursorAt _ hrs))
  case eqTerm_etaCtor =>
    intro sig k Γ ctx decl D T con qs ls ps as r ς χ t Cs us κ i j C e h hc hqp hl hadm hr has ht
      he hi hC hu hCl hCs hCt hul hus Rs hRs hut hκ has_ih ht_ih he_ih hCt_ih hut_ih ι sigM hdis
      hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hj := TypeDeclaration.dataTypes_getElem?_of_cases (List.mem_of_getElem? hi)
      have ht' := ht_ih hdis hord hι ρ
      have he' := he_ih hdis hord hι ρ
      have hCv := hCt_ih _ T C hj hC hdis hord hι ρ
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
      exact ValidEqTermΓ.etaCtor hι h hc hqp hl' hadm hr has' ht' he'
        hCv hi hu' hκ
  case eqTerm_beta =>
    intro sig k Γ ctx decl D T qs ls ps as r Ss gs h' i ps' S ss d p q ς ps₀ Ξ₀ Θ₀ B₀ ψ₀ g bs h hqp
      hl hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih hss_ih hbs_ih hSt_ih
      hgt_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have hss' := hss_ih hdis hord hι ρ
      have hbs' := hbs_ih hdis hord hι ρ
      have hcl : ∀ {a} (x : Var Ξ₀ a),
          ((hd.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
            as.toSubst) x).substLevels (fun i => (.ofNat (ρ i) : Level 0)) =
            hd.obsSubst ((Term.corec r D qs (ls.map (Level.atLevels ρ)) ps
              (as.atLevels ρ) (ss.substLevels fun i => .ofNat (ρ i)).terms
              (Ss.substLevels fun i => .ofNat (ρ i)) (gs.substLevels fun i => .ofNat (ρ i))).observation
              D qs (ls.map (Level.atLevels ρ)) ps
              (as.atLevels ρ)) (as.atLevels ρ).toSubst x :=
        fun x => hd.obsSubst_substLevels _ (fun d' ps' => by
          rw [Term.observation_substLevels]
          simp only [Term.substLevels, ← Args.terms_substLevels, Level.subst_ofNat,
            InstanceArgs.atLevels])
          (InstanceArgs.toSubst_substLevels _ as) x
      simp only [Telescope.atLevels, Telescope.substLevels_subst_of hcl,
        Telescope.substLevels_substLevels] at hbs'
      simp only [Term.atLevels, Term.observed_substLevels, Universe.substLevels_substLevels,
        Term.substLevels_instantiate,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl), Term.substLevels_substLevels,
        Args.substLevels_rename]
      simp only [Term.substLevels, ← Args.terms_substLevels]
      have hc := ValidEqTermΓ.beta hι h hqp hl' hadm hpre has'
        hh (States.get_substLevels_of _ hS) hss' hi hd
            (DestructorBranches.get_substLevels_of _ hg)
        (by rw [List.getFin_map]; exact hbs')
        (fun j T' hj =>
          have ⟨ps'', S', hS'⟩ := hSs j T' hj
          ⟨ps'', _, States.get_substLevels_of _ hS'⟩)
        (CorecBranchesValid.atLevels hqp hl hgs
          (fun i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hd hg =>
            hgt_ih i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hSj hd hg hdis hord hι) ρ)
      rw [List.getFin_map] at hc
      exact hc
  case eqTerm_etaObs =>
    intro sig k Γ ctx decl D T qs ls ps as t u h hqp hl hadm hr has ht hu hobs has_ih ht_ih hu_ih
      hobs_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hl' := Level.length_atLevels (ls := ls) ρ hl
      have has' := (has_ih hdis hord hι).atLevels hl ρ
      have ht' := ht_ih hdis hord hι ρ
      have hu' := hu_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels] at ht' hu'
      refine ValidEqTermΓ.etaObs hι h hqp hl' hadm has' ht' hu'
        fun d p q ς ps' Ξ Θ B ψ hpos => ?_
      have hb := hobs_ih d p q ς ps' Ξ Θ B ψ hpos hdis hord hι ρ
      have hcl := fun {a} (x : Var Ξ a) =>
        hpos.obsSubst_observation_substLevels (fun i => (.ofNat (ρ i) : Level 0)) D qs ls ps as t x
      simp only [Context.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of hcl, Telescope.substLevels_substLevels, Term.atLevels,
        Term.observation_substLevels, Term.substLevels_subst_of (Subst.liftN_substLevels_of _ hcl),
        Term.substLevels_substLevels] at hb
      rw [List.getFin_map]
      exact hb
  case hasArgs_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqArgsΓ.nil (hctx_ih hdis hord hι ρ)
  case hasArgs_cons =>
    intro sig k Γ ps ctx q p t A ts Θ ht hts ht_ih hts_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hts' := hts_ih hdis hord hι ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (ht_ih hdis hord hι ρ) hts'
  case eqArgs_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqArgsΓ.nil (hctx_ih hdis hord hι ρ)
  case eqArgs_cons =>
    intro sig k Γ ps ctx q p t u A ts us Θ ht hts ht_ih hts_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hts' := hts_ih hdis hord hι ρ
      simp only [Telescope.atLevels] at hts'
      rw [Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.atLevels ρ))
        (fun x => by cases x <;> rfl)] at hts'
      exact ValidEqArgsΓ.cons (ht_ih hdis hord hι ρ) hts'
  case hasInstanceArgs_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqInstanceArgsΓ.nil (hctx_ih hdis hord hι ρ)
  case hasInstanceArgs_var =>
    intro sig k Γ Δ ctx as params a A has ha has_ih ha_ih ι sigM hdis hord hι
    exact fun ρ => by
      have ha' := ha_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (has_ih hdis hord hι ρ) ha'
  case hasInstanceArgs_secondOrder =>
    intro sig k Γ Δ ps ψ ctx as params Θ A B has hB has_ih hB_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hB' := hB_ih hdis hord hι ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (has_ih hdis hord hι ρ) hB'
  case eqInstanceArgs_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqInstanceArgsΓ.nil (hctx_ih hdis hord hι ρ)
  case eqInstanceArgs_var =>
    intro sig k Γ Δ ctx as₁ as₂ params a₁ a₂ A has ha has_ih ha_ih ι sigM hdis hord hι
    exact fun ρ => by
      have ha' := ha_ih hdis hord hι ρ
      simp only [Term.atLevels, Term.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁)]
        at ha'
      exact ValidEqInstanceArgsΓ.var (has_ih hdis hord hι ρ) ha'
  case eqInstanceArgs_secondOrder =>
    intro sig k Γ Δ ps ψ ctx as₁ as₂ params Θ A B₁ B₂ has hB has_ih hB_ih ι sigM hdis hord hι
    exact fun ρ => by
      have hB' := hB_ih hdis hord hι ρ
      simp only [Context.atLevels, Term.atLevels, Context.substLevels_append,
        Telescope.substLevels_subst_of (InstanceArgs.toSubst_substLevels _ as₁),
        Term.substLevels_subst_of
          (Subst.liftN_substLevels_of _ (InstanceArgs.toSubst_substLevels _ as₁))] at hB'
      exact ValidEqInstanceArgsΓ.secondOrder (has_ih hdis hord hι ρ) hB'
  case wfTelescope_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqTelescopeΓ.nil (hctx_ih hdis hord hι ρ)
  case wfTelescope_cons =>
    refine fun hA hκ hΘ hp hA_ih hΘ_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTelescopeΓ.cons (hA_ih hdis hord hι ρ) (Universe.substLevels_bounded _ hκ)
        (hΘ_ih hdis hord hι ρ)
  case eqTelescope_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidEqTelescopeΓ.nil (hctx_ih hdis hord hι ρ)
  case eqTelescope_cons =>
    refine fun hA hκ hΘ hp hA_ih hΘ_ih => fun hdis hord hι => ?_
    exact fun ρ =>
      ValidEqTelescopeΓ.cons (hA_ih hdis hord hι ρ) (Universe.substLevels_bounded _ hκ)
        (hΘ_ih hdis hord hι ρ)
  all_goals intros; trivial
/-- The soundness of the typing, in the signatures whose entries a signature whose names are
distinct gives their meaning. -/
theorem soundnessIn.typingSound {ι : Interpretation} {sigM : Signature} (hd : sigM.Distinct)
    (hord : sigM.LiftsInOrder) : TypingSound sigM ι where
  hasType hι h := soundnessIn.hasType hd hord hι h
  wfTelescope hι h := soundnessIn.wfTelescope hd hord hι h
  hasArgs hι h := soundnessIn.hasArgs hd hord hι h
  hasInstanceArgs hι h := soundnessIn.hasInstanceArgs hd hord hι h

/-! ## Type Declarations in a Signature That Gives Their Entries Their Meaning -/

/-- Every type declaration typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names
are distinct and that gives the entries of `Σ_T` their meaning, as its fields and its destructors
are. -/
structure DeclarationSoundnessIn : Prop where
  /-- The fields of a constructor in a sort. -/
  wfFields : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope}
    {ctx : Context decl.levels Γ} {ps : List Parameter} {Θ : Telescope decl.levels Γ ps}
    {κ : Universe decl.levels},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → (∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names) →
        WfFields sig decl I as ctx Θ κ →
          ValidFields sigM ι ctx decl.names (fun D => decl.blockInstance I D as)
          (Θ.nestAt decl.names) Θ κ
  /-- The destructors of a codata type in a sort. -/
  wfDestructors : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
      sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → WfDestructors sig decl I @ν as ctx ds κ →
        ValidDestructors sigM ι ctx (fun D => decl.blockInstance I D as)
          (ds.recursionAt decl.names) (ds.nestedAt @ν) ds κ
  /-- A well-formed type declaration. -/
  wfTypeDeclaration : ∀ {ι : Interpretation} {sigM sig : Signature} {decl : TypeDeclaration},
    sigM.Distinct → sigM.LiftsInOrder → sigM.ValidEntries ι sig → WfTypeDeclaration sig decl →
      ValidTypeDeclaration sigM ι decl

/-- Every type declaration typed in the signature `Σ_T` is meaningful in a signature `Σ` whose names
are distinct and that gives the entries of `Σ_T` their meaning. -/
theorem declarationSoundnessIn : DeclarationSoundnessIn := by
  suffices H : Derivations.Conclusion
      (wfFields := fun sig decl I {Γ} as ctx {ps} Θ κ _ => ∀ {ι sigM}, sigM.Distinct →
        sigM.LiftsInOrder → sigM.ValidEntries ι sig → (∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names) →
        ValidFields sigM ι ctx decl.names (fun D => decl.blockInstance I D as)
          (Θ.nestAt decl.names) Θ κ)
      (wfDestructors := fun sig decl I {Γ ns} ν as ctx ds κ _ => ∀ {ι sigM}, sigM.Distinct →
        sigM.LiftsInOrder → sigM.ValidEntries ι sig →
          ValidDestructors sigM ι ctx (fun D => decl.blockInstance I D as)
            (ds.recursionAt decl.names) (ds.nestedAt @ν) ds κ)
      (wfTypeDeclaration := fun sig decl _ => ∀ {ι sigM}, sigM.Distinct → sigM.LiftsInOrder →
        sigM.ValidEntries ι sig → ValidTypeDeclaration sigM ι decl) from
    ⟨fun hdis hord hι fresh h => H.wfFields h hdis hord hι fresh,
      fun hdis hord hι h => H.wfDestructors h hdis hord hι,
      fun hdis hord hι h => H.wfTypeDeclaration h hdis hord hι⟩
  apply Derivations.induction
  case wfFields_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι fresh => fun ρ =>
      ValidFieldsΓ.nil (soundnessIn.wfCtx hdis hord hι hctx ρ)
  case wfFields_cons =>
    intro sig decl I Γ as ctx ps q p A Θ κ₁ κ hn hA hκ hΘ hp hA_ih hΘ_ih ι sigM hdis hord hι fresh
    exact fun ρ => by
      have hΘ' := hΘ_ih hdis hord hι fresh ρ
      rw [show (fun D => (decl.blockInstance I D (as.rename Ren.weaken)).atLevels ρ) =
          fun D => ((decl.blockInstance I D as).atLevels ρ).rename Ren.weaken from
        funext fun D => Term.substLevels_rename _ _ (decl.blockInstance I D as)] at hΘ'
      exact ValidFieldsΓ.cons (soundnessIn.hasType hdis hord hι hA ρ) (Universe.substLevels_bounded _ hκ)
        hn hΘ'
  case wfFields_recursive =>
    intro sig decl I Γ as ctx ps q p D Θ κ hD hΘ hp hΘ_ih ι sigM hdis hord hι fresh
    exact fun ρ => by
      have hΘ' := hΘ_ih hdis hord hι fresh ρ
      show ValidFieldsΓ sigM ι _ _ _ _ (.cons _ _ ((decl.blockInstance I D as).atLevels ρ)
        ((Θ.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Telescope.substLevels_rename]
      refine ValidFieldsΓ.recursive (D := D)
        ((Term.blockNest_eq_direct _).2 (by simp [TypeDeclaration.blockInstance, Term.blockName,
          hD])) ?_
      have hr : (fun i => (Telescope.cons q p (decl.blockInstance I D as)
          (Θ.rename Ren.weaken)).nestAt decl.names (i + 1)) = Θ.nestAt decl.names := by
        funext i
        simp only [Telescope.nestAt, Telescope.nest, Telescope.nest_rename,
          List.getElem?_cons_succ]
      rw [hr]
      exact hΘ'
  case wfFields_nested =>
    intro sig decl I Γ as ctx ps q p A₀ Θ κ₁ κ νs hn hA₀ hκ hq hpos hpre hΘ hp hA₀_ih hΘ_ih ι sigM
      hdis hord hι fresh
    exact fun ρ => by
      have hΘ' := hΘ_ih hdis hord hι fresh ρ
      show ValidFieldsΓ sigM ι _ _ _ _ (.cons _ _ ((A₀.instantiate (decl.blockArgs I as)).atLevels ρ)
        ((Θ.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Telescope.substLevels_rename]
      refine ValidFieldsΓ.nested (νs := νs)
        (by simp [Telescope.nestAt, Telescope.nest, hn]) (fun σ₁ σ₂ hσ => ?_) ?_
      · have h := Term.validBlockNest (soundnessIn.typingSound hdis hord) hdis hι hpre fresh I as hA₀ hκ hq
          hpos ρ hσ
        rw [hn] at h
        exact ⟨h.1, fun _ => h.2.1, h.2.2⟩
      · have hr : (fun i => (Telescope.cons q p (A₀.instantiate (decl.blockArgs I as))
            (Θ.rename Ren.weaken)).nestAt decl.names (i + 1)) = Θ.nestAt decl.names := by
          funext i
          simp only [Telescope.nestAt, Telescope.nest, Telescope.nest_rename,
            List.getElem?_cons_succ]
        rw [hr]
        exact hΘ'
  case wfDestructors_nil =>
    exact fun hctx hctx_ih => fun hdis hord hι => fun ρ =>
      ValidDestructorsΓ.nil (soundnessIn.wfCtx hdis hord hι hctx ρ)
  case wfDestructors_cons =>
    intro sig decl I Γ ν as d ns ps ctx p q ς Θ B ψ ds κ₁ κ hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih
      ι sigM hdis hord hι
    exact fun ρ => by
      have hB' := soundnessIn.hasType hdis hord hι hB ρ
      simp only [Context.atLevels, Context.substLevels_append] at hB'
      have hds' := hds_ih hdis hord hι ρ
      rw [show (fun D => (decl.blockInstance I D (as.rename Ren.weaken)).atLevels ρ) =
          fun D => ((decl.blockInstance I D as).atLevels ρ).rename Ren.weaken from
        funext fun D => Term.substLevels_rename _ _ (decl.blockInstance I D as)] at hds'
      exact ValidDestructorsΓ.cons
        (by simp [Destructors.recursionAt, Destructors.recursion, hn])
        (by simp [Destructors.nestedAt, Destructors.nested, hν, Nest.isPlain])
        (soundnessIn.wfTelescope hdis hord hι hΘ ρ) hB' (Universe.substLevels_bounded _ hκ) hds'
  case wfDestructors_nested =>
    intro sig decl I Γ ν as d ns ps ctx p q ς Θ B ψ ds κ₁ κ hn hν hΘ hB hκ hp hds hΘ_ih hB_ih hds_ih
      ι sigM hdis hord hι
    exact fun ρ => by
      have hB' := soundnessIn.hasType hdis hord hι hB ρ
      simp only [Context.atLevels, Context.substLevels_append] at hB'
      have hds' := hds_ih hdis hord hι ρ
      show ValidDestructorsΓ sigM ι _ _ _ _ (.cons p q ς (Θ.substLevels fun i => .ofNat (ρ i))
        (B.substLevels fun i => .ofNat (ρ i)) ψ
        ((ds.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Destructors.substLevels_rename]
      refine ValidDestructorsΓ.nested
        (by simp [Destructors.recursionAt, Destructors.recursion, hn])
        (by simp [Destructors.nestedAt, Destructors.nested, Nest.isPlain_eq_false hν])
        (soundnessIn.wfTelescope hdis hord hι hΘ ρ) hB' (Universe.substLevels_bounded _ hκ) ?_
      have hr : (fun i => (Destructors.cons (d := d) p q ς Θ B ψ
          (ds.rename Ren.weaken)).recursionAt decl.names (i + 1)) = ds.recursionAt decl.names := by
        funext i
        simp only [Destructors.recursionAt, Destructors.recursion, Destructors.recursion_rename,
          List.getElem?_cons_succ]
      have hr' : (fun i => (Destructors.cons (d := d) p q ς Θ B ψ
          (ds.rename Ren.weaken)).nestedAt @ν (i + 1)) = ds.nestedAt @ν := by
        funext i
        simp only [Destructors.nestedAt, Destructors.nested,
          Destructors.nested_rename Ren.weaken (ν := @ν)
            (ν' := Nesting.lift (e := .secondOrder ps ψ) @ν)
            (fun _ _ => rfl),
          List.getElem?_cons_succ]
      rw [hr, hr']
      exact hds'
  case wfDestructors_recursive =>
    intro sig decl I Γ ν as d ns ps ctx p q ς Θ ψ D ds κ hD hΘ hp hds hΘ_ih hds_ih ι sigM hdis hord
      hι
    exact fun ρ => by
      have hds' := hds_ih hdis hord hι ρ
      show ValidDestructorsΓ sigM ι _ _ _ _ (.cons p q ς (Θ.substLevels fun i => .ofNat (ρ i))
        ((decl.blockInstance I D (as.rename (Ren.weakenN ps.length))).atLevels ρ) ψ
        ((ds.rename Ren.weaken).substLevels fun i => .ofNat (ρ i))) _
      rw [Destructors.substLevels_rename,
        show (decl.blockInstance I D (as.rename (Ren.weakenN ps.length))).atLevels ρ =
          ((decl.blockInstance I D as).atLevels ρ).rename (Ren.weakenN ps.length) from
        Term.substLevels_rename _ _ (decl.blockInstance I D as)]
      refine ValidDestructorsΓ.recursive (D := D)
        (by simp [Destructors.recursionAt, Destructors.recursion, TypeDeclaration.blockInstance,
          Term.blockName, hD]) (soundnessIn.wfTelescope hdis hord hι hΘ ρ) ?_
      have hr : (fun i => (Destructors.cons (d := d) p q ς Θ
          (decl.blockInstance I D (as.rename (Ren.weakenN ps.length))) ψ
          (ds.rename Ren.weaken)).recursionAt decl.names (i + 1)) = ds.recursionAt decl.names := by
        funext i
        simp only [Destructors.recursionAt, Destructors.recursion, Destructors.recursion_rename,
          List.getElem?_cons_succ]
      have hr' : (fun i => (Destructors.cons (d := d) p q ς Θ
          (decl.blockInstance I D (as.rename (Ren.weakenN ps.length))) ψ
          (ds.rename Ren.weaken)).nestedAt @ν (i + 1)) = ds.nestedAt @ν := by
        funext i
        simp only [Destructors.nestedAt, Destructors.nested,
          Destructors.nested_rename Ren.weaken (ν := @ν)
            (ν' := Nesting.lift (e := .secondOrder ps ψ) @ν)
            (fun _ _ => rfl),
          List.getElem?_cons_succ]
      rw [hr, hr']
      exact hds'
  case wfTypeDeclaration_data =>
    refine fun hb hadm hΔ hΘ hp hc fresh hΔ_ih hΘ_ih => fun hdis hord hι => ?_
    unfold ValidTypeDeclaration
    rw [hb]
    exact fun I hI T hT c hc =>
      hΘ_ih I hI T (by simp only [TypeDeclaration.dataTypes, hb]; exact hT) c hc hdis hord hι fresh
  case wfTypeDeclaration_codata =>
    refine fun hb hadm hΔ hd hp hc fresh hΔ_ih hd_ih => fun hdis hord hι => ?_
    unfold ValidTypeDeclaration
    rw [hb]
    exact fun I hI T hT =>
      hd_ih I hI T (by simp only [TypeDeclaration.codataTypes, hb]; exact hT) hdis hord hι
  all_goals intros; trivial
/-! ## Signatures -/

-- ADE: `defn-valid`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- The entries of a well-formed suffix of a signature whose names are distinct are meaningful in
the whole signature, when the interpretation gives its constant declarations terms of their types:
each entry is typed in the signature before it, whose entries are meaningful by induction. -/
theorem WfSig.validEntries {ι : Interpretation} {sigM : Signature}
    (hι : ValidInterpretation ι sigM) (hd : sigM.Distinct) (hord : sigM.LiftsInOrder) :
    (sig : Signature) → WfSig sig → sig <:+ sigM → sigM.ValidEntries ι sig
  | [], _, _ => fun _ he => nomatch he
  | e :: sig, h, hs => by
    have hrest := WfSig.validEntries hι hd hord sig (Presuppositions.tail presuppositions h)
      ((List.suffix_cons e sig).trans hs)
    have hmem : e ∈ sigM := hs.subset List.mem_cons_self
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · refine ⟨hmem, ?_⟩
      cases h with
      | constantDefinition hdef _ => exact soundnessIn.wfConstantDefinition hd hord hrest hdef
      | constantDeclaration _ _ => exact hι _ hmem
      | typeDeclaration hdecl _ _ =>
        exact declarationSoundnessIn.wfTypeDeclaration hd hord hrest hdecl
      | lifting hdecl _ _ => exact declarationSoundnessIn.wfTypeDeclaration hd hord hrest hdecl
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
  /-- A well-formed constant definition is meaningful.
  RFC: `\mathsf{sound}.\mathsf{def}` -/
  wfConstantDefinition : ∀ {ι : Interpretation} {sig : Signature} {d : ConstantDefinition},
    ValidInterpretation ι sig → WfConstantDefinition sig d → ValidConstantDefinition sig ι d
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
  /-- Arguments of a telescope are meaningful.
  RFC: `\mathsf{sound}.\bar t` -/
  hasArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      HasArgs sig ctx ts Θ → ValidArgs sig ι ctx ts Θ
  /-- Equal arguments of a telescope are meaningful.
  RFC: `\mathsf{sound}.\bar t_\equiv` -/
  eqArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, ValidInterpretation ι sig →
      EqArgs sig ctx ts us Θ → ValidEqArgs sig ι ctx ts us Θ
  /-- Arguments of an instance are meaningful.
  RFC: `\mathsf{sound}.\bar a` -/
  hasInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → HasInstanceArgs sig ctx as params →
        ValidInstanceArgs sig ι ctx as params
  /-- Equal arguments of instances are meaningful.
  RFC: `\mathsf{sound}.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ Δ : Scope}
    {ctx : Context k Γ} {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
      ValidInterpretation ι sig → EqInstanceArgs sig ctx as₁ as₂ params →
        ValidEqInstanceArgs sig ι ctx as₁ as₂ params
  /-- A telescope in a sort is meaningful.
  RFC: `\mathsf{sound}.\Theta` -/
  wfTelescope : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κ : Universe k},
      ValidInterpretation ι sig → WfTelescope sig ctx Θ κ → ValidTelescope sig ι ctx Θ κ
  /-- An equality of telescopes in a sort is meaningful.
  RFC: `\mathsf{sound}.\Theta_\equiv` -/
  eqTelescope : ∀ {ι : Interpretation} {sig : Signature} {k : Nat} {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
      ValidInterpretation ι sig → EqTelescope sig ctx Θ₁ Θ₂ κ →
        ValidEqTelescope sig ι ctx Θ₁ Θ₂ κ
  /-- The destructors of a codata type in a sort are meaningful.
  RFC: `\mathsf{sound}.\bar d` -/
  wfDestructors : ∀ {ι : Interpretation} {sig : Signature} {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades} {Γ : Scope} {ns : List Name} {ν : Nesting Nat Γ}
    {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
    {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
      ValidInterpretation ι sig → WfDestructors sig decl I @ν as ctx ds κ →
        ValidDestructors sig ι ctx (fun D => decl.blockInstance I D as)
          (ds.recursionAt decl.names) (ds.nestedAt @ν) ds κ
  /-- A well-formed type declaration is meaningful.
  RFC: `\mathsf{sound}.\mathsf{data}`
  RFC: `\mathsf{sound}.\mathsf{codata}` -/
  wfTypeDeclaration : ∀ {ι : Interpretation} {sig : Signature} {decl : TypeDeclaration},
    ValidInterpretation ι sig → WfTypeDeclaration sig decl → ValidTypeDeclaration sig ι decl

/-- A well-formed signature is meaningful, when the interpretation gives its constant declarations
terms of their types. -/
theorem soundness_wfSig {ι : Interpretation} {sig : Signature} (hι : ValidInterpretation ι sig)
    (h : WfSig sig) : ValidSig ι sig :=
  ⟨h.distinct, fun e he => (WfSig.validEntries hι h.distinct h.liftsInOrder sig h (List.suffix_refl _) e he).2⟩

-- ADE: `fundamental`, in `Definition/LogicalRelation/Fundamental.agda`, for the judgments in a
-- context.
/-- Every judgment is meaningful, in a signature whose constant declarations the interpretation
gives terms of their types: its signature is well formed, hence meaningful, and so gives its own
entries their meaning. -/
theorem soundness : Soundness where
  wfSig := soundness_wfSig
  wfConstantDefinition hι h :=
    have hw := presuppositions.wfConstantDefinition h
    have hs := soundness_wfSig hι hw
    soundnessIn.wfConstantDefinition hs.1 hw.liftsInOrder hs.validEntries h
  wfConstantDeclaration hι _ := hι _ List.mem_cons_self
  wfCtx hι h :=
    have hw := presuppositions.wfCtx h
    have hs := soundness_wfSig hι hw
    soundnessIn.wfCtx hs.1 hw.liftsInOrder hs.validEntries h
  wfType hι h :=
    have hw := presuppositions.wfType h
    have hs := soundness_wfSig hι hw
    soundnessIn.wfType hs.1 hw.liftsInOrder hs.validEntries h
  eqType hι h :=
    have hw := presuppositions.eqType h
    have hs := soundness_wfSig hι hw
    soundnessIn.eqType hs.1 hw.liftsInOrder hs.validEntries h
  hasType hι h :=
    have hw := presuppositions.hasType h
    have hs := soundness_wfSig hι hw
    soundnessIn.hasType hs.1 hw.liftsInOrder hs.validEntries h
  eqTerm hι h :=
    have hw := presuppositions.eqTerm h
    have hs := soundness_wfSig hι hw
    soundnessIn.eqTerm hs.1 hw.liftsInOrder hs.validEntries h
  hasArgs hι h :=
    have hw := presuppositions.hasArgs h
    have hs := soundness_wfSig hι hw
    soundnessIn.hasArgs hs.1 hw.liftsInOrder hs.validEntries h
  eqArgs hι h :=
    have hw := presuppositions.eqArgs h
    have hs := soundness_wfSig hι hw
    soundnessIn.eqArgs hs.1 hw.liftsInOrder hs.validEntries h
  hasInstanceArgs hι h :=
    have hw := presuppositions.hasInstanceArgs h
    have hs := soundness_wfSig hι hw
    soundnessIn.hasInstanceArgs hs.1 hw.liftsInOrder hs.validEntries h
  eqInstanceArgs hι h :=
    have hw := presuppositions.eqInstanceArgs h
    have hs := soundness_wfSig hι hw
    soundnessIn.eqInstanceArgs hs.1 hw.liftsInOrder hs.validEntries h
  wfTelescope hι h :=
    have hw := presuppositions.wfTelescope h
    have hs := soundness_wfSig hι hw
    soundnessIn.wfTelescope hs.1 hw.liftsInOrder hs.validEntries h
  eqTelescope hι h :=
    have hw := presuppositions.eqTelescope h
    have hs := soundness_wfSig hι hw
    soundnessIn.eqTelescope hs.1 hw.liftsInOrder hs.validEntries h
  wfDestructors hι h :=
    have hw := presuppositions.wfDestructors h
    have hs := soundness_wfSig hι hw
    declarationSoundnessIn.wfDestructors hs.1 hw.liftsInOrder hs.validEntries h
  wfTypeDeclaration hι h :=
    have hw := presuppositions.wfTypeDeclaration h
    have hs := soundness_wfSig hι hw
    declarationSoundnessIn.wfTypeDeclaration hs.1 hw.liftsInOrder hs.validEntries h

end Sic.Core
