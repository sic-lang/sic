module

public import Sic.Core.Meaning.RunTime

/-!
# Meaning

The meaning of the judgments of annex 18 of RFC 36, after the meaning explanations of Martin-Löf: a
closed judgment is true when its terms compute as it says, and a judgment in a context when it holds
under every pair of equal closed substitutions of the context.
Each judgment of the typing has a meaning, with the same objects: the signatures and their entries,
the contexts, the types, the terms, the arguments of the telescopes and of the instances, the
telescopes in a sort and the destructors in a sort.
The meaning ignores the modes and the ownerships, as the typing does outside the judgments of usage
and of ownership that the rule of the constant definitions reads, and it reads the grades only
through the relations of run time, which the equality of the types compares: two instances of a
declared type at different grades have the same equality of their terms, but not the same
relations of run time, and they are not equal types.
Each entry is meaningful in the whole signature, and a closed judgment requires the names of its
signature to be distinct, rather than its meaning, so that the soundness proves each entry
meaningful in the whole signature from its typing in the signature before it.

The relations of each level, the equality of the terms of its types, the truth of its propositions
and the relations of run time of its types, are defined together, after those of the levels below
it, by `levelRel`, which ties the graphs of `Sic.Core.Meaning.Equality` and of
`Sic.Core.Meaning.RunTime`.

ADE give no meaning to the judgments: their logical relation is defined on the typed reduction, for
the decidability of the conversion, and it is not a model of the type theory in the computations.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Relations of the Levels -/

/-- The relations of the sorts of the level `n`, defined after those of the levels below it. -/
def levelRel (sig : Signature) (ι : Interpretation) (n : Nat) : LevelRel :=
  ⟨UnivRel sig ι n fun m _ => levelRel sig ι m, PropRel sig ι n fun m _ => levelRel sig ι m,
    fun P => RunUnivRel sig ι P n fun m _ => levelRel sig ι m⟩
termination_by n
decreasing_by all_goals assumption

-- ADE: none.
/-- `eq(v) = R`: the closed canonical type `v` is a type of a sort, whose canonical terms are equal by
`R`, or a proposition, whose closed terms are equal by `R`. -/
inductive HasEq (sig : Signature) (ι : Interpretation) (v : Term 0 []) (R : TermRel) : Prop where
  /-- A type of the universe `U_n`.
  RFC: `\mathsf{eq}_{\mathsf{type}}` -/
  | univ (n : Nat) (h : (levelRel sig ι n).univ v R)
  /-- `(eq_true)` and `(eq_false)`: a proposition of `Ω_n` whose truth is `b`, whose closed terms are
  all equal proofs when it is true, and none when it is false.
  RFC: `\mathsf{eq}_{\mathsf{true}}`
  RFC: `\mathsf{eq}_{\mathsf{false}}` -/
  | prop (n : Nat) (b : Prop) (h : (levelRel sig ι n).prop v b) (hR : ∀ t u, R t u ↔ b)

-- ADE: none.
/-- `®(v) = R`: the closed canonical type `v` is a type of a sort, whose canonical terms are
related at run time by `R`, or a proposition, whose closed terms are related to every address. -/
inductive HasRun (sig : Signature) (ι : Interpretation) (P : Program) (v : Term 0 [])
    (R : RunRel) : Prop where
  /-- A type of the universe `U_n`.
  RFC: `\circledR_{\mathsf{type}}` -/
  | univ (n : Nat) (h : (levelRel sig ι n).run P v R)
  /-- A proposition of `Ω_n`, whose closed terms are related to every address.
  RFC: `\circledR_{\mathsf{prop}}` -/
  | prop (n : Nat) (b : Prop) (h : (levelRel sig ι n).prop v b) (hR : ∀ H t a, R H t a)

/-- `(prop_v)`: `v` is a proposition, a term of a universe of propositions.
RFC: `\mathsf{prop}_v` -/
def IsProp (sig : Signature) (ι : Interpretation) (v : Term 0 []) : Prop :=
  ∃ k b, (levelRel sig ι k).prop v b

/-- `(prop_⇓)`: the closed type `A` computes to a proposition.
RFC: `\mathsf{prop}_\Downarrow` -/
def ComputesToProp (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ∃ v, Computesι sig ι A v ∧ IsProp sig ι v

/-! ## Closed Judgments

The clauses of the closed judgments are stated without the meaning `⊨ Σ` of their signature, which
they require, so that the meaning of the signatures is defined from them. -/

/-- The clause of `(⊨_type≡)`: `A` and `B` compute to canonical types whose terms have the same
equality and, for each program, the same relations of run time. -/
def EqTypeClause (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  ∃ v w R, Computesι sig ι A v ∧ Computesι sig ι B w ∧ HasEq sig ι v R ∧ HasEq sig ι w R ∧
    ∀ P Q, HasRun sig ι P v Q ↔ HasRun sig ι P w Q

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` for the terms: `t` and `u` compute to equal canonical terms
of the canonical form of `A`, or are equal proofs of it when it is a proposition. -/
def EqTermClause (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  (¬ ComputesToProp sig ι A → ∃ v w₁ w₂ R, Computesι sig ι A v ∧ Computesι sig ι t w₁ ∧
    Computesι sig ι u w₂ ∧ HasEq sig ι v R ∧ R w₁ w₂) ∧
  (ComputesToProp sig ι A → ∃ v R, Computesι sig ι A v ∧ HasEq sig ι v R ∧ R t u)

/-- The clause of `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`: at each instance of the sort and grade
variables and each value of the level variables, the body is a term of the type; the meaning ignores
the mode and the ownership. -/
def ConstantDefinition.Clause (sig : Signature) (ι : Interpretation) (d : ConstantDefinition) :
    Prop :=
  ∀ inst (ρ : Fin d.levels → Nat),
    EqTypeClause sig ι ((d.type inst).atLevels ρ) ((d.type inst).atLevels ρ) ∧
      EqTermClause sig ι ((d.body inst).atLevels ρ) ((d.body inst).atLevels ρ)
        ((d.type inst).atLevels ρ)

/-- The clause of `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p`: at each instance of the sort and grade variables
and each value of the level variables, the interpretation of the constant is a term of its type; the
meaning ignores the mode and the ownership. -/
def ConstantDeclaration.Clause (sig : Signature) (ι : Interpretation) (c : ConstantDeclaration) :
    Prop :=
  ∀ inst (ρ : Fin c.levels → Nat),
    EqTypeClause sig ι ((c.type inst).atLevels ρ) ((c.type inst).atLevels ρ) ∧
      EqTermClause sig ι ((ι c inst).atLevels ρ) ((ι c inst).atLevels ρ)
        ((c.type inst).atLevels ρ)

-- ADE: none.
/-- `(⊨def)`: `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`, in a signature whose names are distinct. -/
def ValidConstantDefinition (sig : Signature) (ι : Interpretation) (d : ConstantDefinition) : Prop :=
  sig.Distinct ∧ d.Clause sig ι

-- ADE: none.
/-- `(⊨decl)`: `Σ ⊨ f.{s̄; l̄; p̄} : A ▶ m ◀ p`, in a signature whose names are distinct. -/
def ValidConstantDeclaration (sig : Signature) (ι : Interpretation) (c : ConstantDeclaration) :
    Prop :=
  sig.Distinct ∧ c.Clause sig ι

/-- `(⊨_type≡)`: `Σ ⊨ A ≡ B`.
RFC: `\vDash_{\mathsf{type}\equiv}` -/
def ValidEqType₀ (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  sig.Distinct ∧ EqTypeClause sig ι A B

/-- `(⊨_type)`: `Σ ⊨ A`.
RFC: `\vDash_{\mathsf{type}}` -/
def ValidType₀ (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ValidEqType₀ sig ι A A

/-- `(⊨_≡)` and `(⊨_≡Ω)`: `Σ ⊨ t ≡ u : A`.
RFC: `\vDash_\equiv`
RFC: `\vDash_{\equiv\Omega}` -/
def ValidEqTerm₀ (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  ValidType₀ sig ι A ∧ EqTermClause sig ι t u A

/-- `(⊨)`: `Σ ⊨ t : A`.
RFC: `\vDash` -/
def ValidTerm₀ (sig : Signature) (ι : Interpretation) (t A : Term 0 []) : Prop :=
  ValidEqTerm₀ sig ι t t A

/-! ## Hypothetical Judgments -/

/-- The substitution `σ` without its last entry. -/
def Subst.tail {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} (σ : Subst k Γ (e :: Δ)) : Subst k Γ Δ :=
  fun x => σ x.succ

-- ADE: none.
/--
`(σ₁, σ₂) ∈ eq(Γ)`: two equal closed substitutions of `Γ`, which give each variable equal closed
terms of its type, and each second-order variable abstractions whose instances by equal arguments are
equal terms of its type; the arguments of a telescope are the equal substitutions of the context it
forms.
RFC: `\mathsf{eq}_\varepsilon`
RFC: `\mathsf{eq}_x`
RFC: `\mathsf{eq}_X`
-/
def EqSubst (sig : Signature) (ι : Interpretation) :
    {Γ : Scope} → Context 0 Γ → Subst 0 [] Γ → Subst 0 [] Γ → Prop
  /- `(eq_ε)`. -/
  | _, .empty, _, _ => True
  /- `(eq_x)`. -/
  | _, .var ctx A, σ₁, σ₂ => EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ValidEqTerm₀ sig ι (σ₁ .zero) (σ₂ .zero) (A.subst (Subst.tail σ₁))
  /- `(eq_X)`. -/
  | _, .secondOrder ctx Θ A _, σ₁, σ₂ => EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst (Subst.tail σ₁))) τ₁ τ₂ →
        ValidEqTerm₀ sig ι ((σ₁ .zero).subst τ₁) ((σ₂ .zero).subst τ₂)
          ((A.subst (Subst.liftN _ (Subst.tail σ₁))).subst τ₁)
termination_by _ ctx => ctx.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

-- ADE: none.
/-- `Σ ⊨ Γ`, at levels without variables: the last type of the context is a type in the context
before it.
RFC: `{\vDash}\mathsf{ctx}_\varepsilon` -/
def ValidCtx₀ (sig : Signature) (ι : Interpretation) : {Γ : Scope} → Context 0 Γ → Prop
  /- `(⊨ctx_ε)`. -/
  | _, .empty => sig.Distinct
  /- `(⊨ctx_x)`: `Σ; Γ ⊨ A`. -/
  | _, .var ctx A => ValidCtx₀ sig ι ctx ∧
      ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (A.subst σ₂)
  /- `(⊨ctx_X)`: `Σ; Γ, Θ ⊨ A`. -/
  | _, .secondOrder ctx Θ A _ => ValidCtx₀ sig ι (ctx.append Θ) ∧
      ∀ σ₁ σ₂, EqSubst sig ι (ctx.append Θ) σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (A.subst σ₂)
termination_by _ ctx => ctx.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

/-- `(⊨Γ_type≡)`: `Σ; Γ ⊨ A ≡ B`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{type}\equiv}` -/
def ValidEqTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A B : Term 0 Γ) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (B.subst σ₂)

/-- `(⊨Γ_type)`: `Σ; Γ ⊨ A`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{type}}` -/
def ValidTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : Prop :=
  ValidEqTypeΓ sig ι ctx A A

/-- `(⊨Γ_≡)`: `Σ; Γ ⊨ t ≡ u : A`, at levels without variables.
RFC: `{\vDash}\Gamma_\equiv` -/
def ValidEqTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t u A : Term 0 Γ) : Prop :=
  ValidTypeΓ sig ι ctx A ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι (t.subst σ₁) (u.subst σ₂) (A.subst σ₁)

/-- `(⊨Γ)`: `Σ; Γ ⊨ t : A`, at levels without variables.
RFC: `{\vDash}\Gamma` -/
def ValidTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t A : Term 0 Γ) : Prop :=
  ValidEqTermΓ sig ι ctx t t A

-- ADE: none.
/-- `(⊨Γ_tel≡)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, at levels without variables: the arguments substituted by two
equal closed substitutions `σ₁` and `σ₂` of the context are equal substitutions of the context that
the telescope `Θ[σ₁]` forms.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\equiv}` -/
def ValidEqArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts us : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) (ts.subst σ₁).toSubst
        (us.subst σ₂).toSubst

/-- `(⊨Γ_tel)`: `Σ; Γ ⊨ t̄ : Θ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{tel}}` -/
def ValidArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidEqArgsΓ sig ι ctx ts ts Θ

-- ADE: none.
/-- `(⊨Γ_arg≡)`: `Σ; Γ ⊨ ā₁ ≡ ā₂ : Δ`, at levels without variables: the arguments substituted by
two equal closed substitutions of the context are equal substitutions of the parameters `Δ`.
RFC: `{\vDash}\Gamma_{\mathsf{arg}\equiv}` -/
def ValidEqInstanceArgsΓ (sig : Signature) (ι : Interpretation) {Γ Δ : Scope} (ctx : Context 0 Γ)
    (as₁ as₂ : InstanceArgs 0 Γ Δ) (params : Context 0 Δ) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      EqSubst sig ι params (as₁.subst σ₁).toSubst (as₂.subst σ₂).toSubst

/-- `(⊨Γ_arg)`: `Σ; Γ ⊨ ā : Δ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{arg}}` -/
def ValidInstanceArgsΓ (sig : Signature) (ι : Interpretation) {Γ Δ : Scope} (ctx : Context 0 Γ)
    (as : InstanceArgs 0 Γ Δ) (params : Context 0 Δ) : Prop :=
  ValidEqInstanceArgsΓ sig ι ctx as as params

/-! ## Telescopes -/

-- ADE: none.
/-- `Σ ⊨ Θ₁ ≡ Θ₂ : κ`: two closed telescopes are equal in the sort `κ`, their first types being
equal types of a sort that `κ` bounds, and the rest of them equal for every pair of equal terms of
these types; the meaning ignores their grades.
RFC: `{\vDash}\mathsf{tel}_{\kappa\varepsilon}`
RFC: `{\vDash}\mathsf{tel}_{\kappa,}` -/
def ValidEqTelescope₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0) :
    {ps : List Parameter} → Telescope 0 [] ps → Telescope 0 [] ps → Prop
  /- `(⊨tel_κε)`. -/
  | [], .nil, .nil => sig.Distinct
  /- `(⊨tel_κ,)`. -/
  | _ :: _, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂ =>
    (∃ κ₁, κ₁ ≼ κ ∧ ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) ∧
      ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ A₁ →
        ValidEqTelescope₀ sig ι κ (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))

-- ADE: none.
/-- `(⊨Γ_tel_κ≡)`: `Σ; Γ ⊨ Θ₁ ≡ Θ₂ : κ`, at levels without variables: the telescopes substituted by
two equal closed substitutions of the context give equal closed telescopes in the sort `κ`.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\kappa\equiv}` -/
def ValidEqTelescopeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (Θ₁ Θ₂ : Telescope 0 Γ ps) (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqTelescope₀ sig ι κ (Θ₁.subst σ₁) (Θ₂.subst σ₂)

/-- `(⊨Γ_tel_κ)`: `Σ; Γ ⊨ Θ : κ`, at levels without variables.
RFC: `{\vDash}\Gamma_{\mathsf{tel}\kappa}` -/
def ValidTelescopeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (κ : Universe 0) : Prop :=
  ValidEqTelescopeΓ sig ι ctx Θ Θ κ

-- ADE: none.
/-- `Σ ⊨ d̄[θ₁] ≡ d̄[θ₂] : κ` for the destructors of a codata type, whose recursive destructors `rs`
gives, of the instances `inst D` of the block: the destructors at two closed substitutions `θ₁` and
`θ₂` of their scope are equal in the sort `κ`; the arguments of each destructor are equal
telescopes in the universe of the level of `κ`; the results of a destructor that is not recursive
are equal types of a sort that `κ` bounds at equal arguments, and the destructors after it are equal
for every pair of abstractions for it whose instances at equal arguments are equal terms of its
result; the result of a recursive destructor of the type `D` is the instance `inst D` of the block,
and the destructors after it are equal for every pair of abstractions for it, on which they do not
depend.
The Lean carries the closed substitutions of the scope of the destructors, as the equality of the
abstractions for them does.
RFC: `{\vDash}\bar d_{\kappa\varepsilon}`
RFC: `{\vDash}\bar d_{\kappa|}`
RFC: `{\vDash}\bar d_{\kappa\mathsf{rec}}` -/
def ValidEqDestructors₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0) :
    {Γ : Scope} → {ns : List Name} → (Name → Term 0 Γ) → (Nat → Option Name) →
      Destructors 0 Γ ns → Subst 0 [] Γ → Subst 0 [] Γ → Prop
  /- `(⊨d̄_κε)`. -/
  | _, _, _, _, .nil, _, _ => sig.Distinct
  | _, _ :: _, inst, rs, .cons (ps := ps) _ _ _ Θ B ψ ds, θ₁, θ₂ =>
    ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂) ∧
    match rs 0 with
    /- `(⊨d̄_κ|)`. -/
    | none =>
      (∃ κ₁, κ₁ ≼ κ ∧ ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
          (.sort κ₁)) ∧
      ∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
        ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken) (fun i => rs (i + 1)) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂)
    /- `(⊨d̄_κrec)`. -/
    | some D => B = (inst D).rename (Ren.weakenN ps.length) ∧
      ∀ f₁ f₂, ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken)
        (fun i => rs (i + 1)) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁)
        (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂)

-- ADE: none.
/-- `Σ; Γ ⊨_𝒟 d̄ : κ`, at levels without variables, for the destructors of a codata type, whose
recursive destructors `rs` gives, of the instances `inst D` of the block: the destructors at two
equal closed substitutions of the context are equal in the sort `κ`.
RFC: `{\vDash}\Gamma_{\bar d}` -/
def ValidDestructorsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ns : List Name}
    (ctx : Context 0 Γ) (inst : Name → Term 0 Γ) (rs : Nat → Option Name)
    (ds : Destructors 0 Γ ns) (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧ ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqDestructors₀ sig ι κ inst rs ds σ₁ σ₂

-- ADE: none.
/-- `Σ ⊨ Θ₁ ≡ Θ₂ : κ` for the fields of two constructors, whose recursive fields `rs` gives: the
fields that are not recursive are equal types of a sort that `κ` bounds, the recursive fields of the
type `D` are the instances `inst₁ D` and `inst₂ D` of the block, and the rest of them are equal for
every pair of equal terms of the fields that are not recursive, and for every pair of terms of the
recursive ones, on which they do not depend; the meaning ignores their grades.
RFC: `{\vDash}\mathsf{fields}_\varepsilon`
RFC: `{\vDash}\mathsf{fields}_{,}`
RFC: `{\vDash}\mathsf{fields}_{\mathsf{rec}}` -/
def ValidEqFields₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0)
    (inst₁ inst₂ : Name → Term 0 []) :
    {ps : List Parameter} → (Nat → Option Name) → Telescope 0 [] ps → Telescope 0 [] ps → Prop
  /- `(⊨fields_ε)`. -/
  | [], _, .nil, .nil => sig.Distinct
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂ =>
    match rs 0 with
    /- `(⊨fields_,)`. -/
    | none => (∃ κ₁, κ₁ ≼ κ ∧ ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) ∧
      ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ A₁ →
        ValidEqFields₀ sig ι κ inst₁ inst₂ (fun i => rs (i + 1)) (Θ₁.subst₀ (Subst₀.single v₁))
          (Θ₂.subst₀ (Subst₀.single v₂))
    /- `(⊨fields_rec)`. -/
    | some D => A₁ = inst₁ D ∧ A₂ = inst₂ D ∧
      ∀ v₁ v₂, ValidEqFields₀ sig ι κ inst₁ inst₂ (fun i => rs (i + 1))
        (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))

-- ADE: none.
/-- `Σ; Γ ⊨ Θ : κ` for the fields of a constructor, whose recursive fields `rs` gives, of the
instances `inst D` of the block, at levels without variables: the fields substituted by two equal
closed substitutions of the context give equal closed fields in the sort `κ`.
RFC: `{\vDash}\Gamma_{\mathsf{fields}}` -/
def ValidFieldsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (inst : Name → Term 0 Γ) (rs : Nat → Option Name) (Θ : Telescope 0 Γ ps)
    (κ : Universe 0) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqFields₀ sig ι κ (fun D => (inst D).subst σ₁)
      (fun D => (inst D).subst σ₂) rs (Θ.subst σ₁) (Θ.subst σ₂)

/-! ## Level Variables -/

/-- `(⊨_ρ)`: `Σ ⊨ Γ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidCtx (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ) :
    Prop :=
  ∀ ρ, ValidCtx₀ sig ι (ctx.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A ≡ B`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A B : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ) (B.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A : Term k Γ) : Prop :=
  ∀ ρ, ValidTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t ≡ u : A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t u A : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (u.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t : A`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t A : Term k Γ) : Prop :=
  ∀ ρ, ValidTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts us : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidEqArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (us.atLevels ρ) (Θ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ : Θ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (Θ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ ā₁ ≡ ā₂ : Δ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqInstanceArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ Δ : Scope}
    (ctx : Context k Γ) (as₁ as₂ : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  ∀ ρ, ValidEqInstanceArgsΓ sig ι (ctx.atLevels ρ) (as₁.atLevels ρ) (as₂.atLevels ρ)
    (params.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ ā : Δ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidInstanceArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ Δ : Scope}
    (ctx : Context k Γ) (as : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  ∀ ρ, ValidInstanceArgsΓ sig ι (ctx.atLevels ρ) (as.atLevels ρ) (params.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ₁ ≡ Θ₂ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidEqTelescope (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ps : List Parameter} (ctx : Context k Γ) (Θ₁ Θ₂ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  ∀ ρ, ValidEqTelescopeΓ sig ι (ctx.atLevels ρ) (Θ₁.atLevels ρ) (Θ₂.atLevels ρ) (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ : κ`, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidTelescope (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ps : List Parameter} (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  ∀ ρ, ValidTelescopeΓ sig ι (ctx.atLevels ρ) (Θ.atLevels ρ) (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨_𝒟 d̄ : κ` for the destructors of a codata type, for every value of the level
variables.
RFC: `\vDash_\rho` -/
def ValidDestructors (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope}
    {ns : List Name} (ctx : Context k Γ) (inst : Name → Term k Γ) (rs : Nat → Option Name)
    (ds : Destructors k Γ ns) (κ : Universe k) : Prop :=
  ∀ ρ, ValidDestructorsΓ sig ι (ctx.atLevels ρ) (fun D => (inst D).atLevels ρ) rs (ds.atLevels ρ)
    (κ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ Θ : κ` for the fields of a constructor, for every value of the level variables.
RFC: `\vDash_\rho` -/
def ValidFields (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (inst : Name → Term k Γ) (rs : Nat → Option Name) (Θ : Telescope k Γ ps)
    (κ : Universe k) : Prop :=
  ∀ ρ, ValidFieldsΓ sig ι (ctx.atLevels ρ) (fun D => (inst D).atLevels ρ) rs (Θ.atLevels ρ)
    (κ.atLevels ρ)

/-! ## Signatures and Entries -/

-- ADE: none.
/-- `Σ ⊨ D`: the type declaration `D` is meaningful in the signature `Σ`.
`(⊨data)`: `Σ ⊨ data.{s̄; l̄; p̄ | C} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort and
grade variables that `C` admits, the fields of each constructor are fields in the sort `κ`, in the
context of the parameters, at each value of the level variables, whose recursive fields are the
types of the block at the parameters themselves.
`(⊨codata)`: `Σ ⊨ codata.{s̄; l̄; p̄ | C} Δ : κ where D₁ ▶ ζ₁ ≔ …; …`: at each instance of the sort
and grade variables that `C` admits, the destructors of each type are in the sort `κ`, in the
context of the parameters, at each value of the level variables, whose recursive destructors have
the types of the block at the parameters themselves as results.
The meaning ignores the grades, and the names of the constructors and of the destructors, distinct,
are those of the signature.
RFC: `{\vDash}\mathsf{data}`
RFC: `{\vDash}\mathsf{codata}` -/
def ValidTypeDeclaration (sig : Signature) (ι : Interpretation) (decl : TypeDeclaration) : Prop :=
  match decl.body with
  | .data Ts => ∀ I, decl.constraint I → ∀ T ∈ Ts, ∀ c ∈ T.constructors,
      ValidFields sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
        ((c.fields I).recursionAt decl.names) (c.fields I) (decl.sort I)
  | .codata Ts => ∀ I, decl.constraint I → ∀ T ∈ Ts,
      ValidDestructors sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
        ((T.body I).recursionAt decl.names) (T.body I) (decl.sort I)

-- ADE: none.
/-- `Σ ⊨ e`: the entry `e` is meaningful in the signature `Σ`. -/
def ValidEntry (sig : Signature) (ι : Interpretation) : Entry → Prop
  | .typeDeclaration decl => ValidTypeDeclaration sig ι decl
  | .constantDefinition d => ValidConstantDefinition sig ι d
  | .constantDeclaration c => ValidConstantDeclaration sig ι c

-- ADE: none.
/-- `⊨ Σ`: the names of the signature are distinct, and each of its entries is meaningful in the
whole signature.
RFC: `{\vDash}\mathsf{sig}` -/
def ValidSig (ι : Interpretation) (sig : Signature) : Prop :=
  sig.Distinct ∧ ∀ e ∈ sig, ValidEntry sig ι e

/-! ## Partial Equivalence Relations -/

/-- `R` is a partial equivalence relation: symmetric and transitive. -/
structure IsPer {α : Type} (R : α → α → Prop) : Prop where
  /-- `R` is symmetric. -/
  symm {t u : α} : R t u → R u t
  /-- `R` is transitive. -/
  trans {t u w : α} : R t u → R u w → R t w

/-- The relations of the sorts of a level give each type they relate a unique equality of its terms,
itself a partial equivalence relation, each proposition a unique truth, and each type a unique
relation of run time. -/
structure LevelRel.IsPer (L : LevelRel) : Prop where
  /-- The equality of the terms of a type of `U_n` is a partial equivalence relation. -/
  univ_isPer {v : Term 0 []} {R : TermRel} : L.univ v R → _root_.Sic.Core.IsPer R
  /-- `ty(U_n)` gives a type a unique equality of its terms. -/
  univ_unique {v : Term 0 []} {R R' : TermRel} : L.univ v R → L.univ v R' → ∀ t u, R t u ↔ R' t u
  /-- `ty(Ω_n)` gives a proposition a unique truth. -/
  prop_unique {v : Term 0 []} {b b' : Prop} : L.prop v b → L.prop v b' → (b ↔ b')
  /-- `rt(U_n)` gives a type a unique relation of run time. -/
  run_unique {P : Program} {v : Term 0 []} {R R' : RunRel} : L.run P v R → L.run P v R' →
    ∀ H t a, R H t a ↔ R' H t a

end Sic.Core
