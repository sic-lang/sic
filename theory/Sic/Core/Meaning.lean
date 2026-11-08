module

public import Sic.Core.Reduction

/-!
# Meaning

The meaning of the judgments of RFC 24, after the meaning explanations of Martin-Löf: a closed
judgment is true when its terms compute as it says, and a judgment in a context when it holds under
every pair of equal closed substitutions of the context.
A closed canonical type is known by the equality of its canonical terms, a partial equivalence
relation `eq(A₀)`, which the sorts give in the core: the universe `U_n` relates the sorts of the level
below it, and the universe of propositions `Ω_n` relates nothing, since only the kinds of
declarations, which the core does not have, build propositions.

The universes are defined one level after the other, and at each level by a least relation, which
gives the equality of the terms of each type it relates: this induction-recursion is encoded by its
graph, an inductive relation between two types and the equality of their terms, as the
formalization of Adjedj, Lennon-Bertrand, Maillard, Pédrot and Pujet does, in Coq, for its universes.
The levels of a closed term need not be numerals, since an instance of a definition may give `l ⊔ 0`
to its body, so that the sorts are related by the values of their levels.

The meaning computes each constant to its interpretation `ι(c)`: it computes in the signature whose
constants become definitions with these bodies, so that it has a single reduction, that of the
conversion.

ADE give no meaning to the judgments: their logical relation is defined on the typed reduction, for
the decidability of the conversion, and it is not a model of the type theory in the computations.
-/

@[expose] public section

namespace Sic.Core

/-! ## Interpretation of the Constants -/

-- ADE: none.
/-- `ι`: an interpretation, which gives each constant a body, for each instance of its sort and grade
variables. -/
abbrev Interpretation : Type :=
  (c : ConstantDeclaration) → Instance c.sorts c.grades → Term c.levels []

/-- The entry `e` in which a constant becomes the definition whose body is its interpretation. -/
def Entry.interpret (ι : Interpretation) : Entry → Entry
  | .constantDeclaration c =>
    .constantDefinition ⟨c.name, c.sorts, c.levels, c.grades, c.mode, c.ownership, c.type, ι c⟩
  | e => e

/-- The signature `Σ` in which each constant becomes the definition whose body is its
interpretation. -/
def Signature.interpret (ι : Interpretation) (sig : Signature) : Signature :=
  sig.map (Entry.interpret ι)

/-- `t ⇓ v` in the meaning: the closed term `t` computes to the canonical term `v`, each constant
computing to its interpretation. -/
def Computesι (sig : Signature) (ι : Interpretation) (t v : Term 0 []) : Prop :=
  Computes (sig.interpret ι) t v

/-! ## Levels Without Variables -/

/-- The level without variables whose value is `n`, written as this number. -/
def Level.ofNat {k : Nat} : Nat → Level k
  | 0 => .zero
  | n + 1 => .succ (Level.ofNat n)

/-- The value of a level without variables. -/
def Level.closedValue (l : Level 0) : Nat := l.value Fin.elim0

/-- `t[ρ]`: the term `t` in which each level variable `i` has the value `ρ i`. -/
def Term.atLevels {k : Nat} {Γ : Scope} (ρ : Fin k → Nat) (t : Term k Γ) : Term 0 Γ :=
  t.substLevels fun i => .ofNat (ρ i)

/-- `Γ[ρ]`: the context `Γ` in which each level variable `i` has the value `ρ i`. -/
def Context.atLevels {k : Nat} {Γ : Scope} (ρ : Fin k → Nat) (ctx : Context k Γ) : Context 0 Γ :=
  ctx.substLevels fun i => .ofNat (ρ i)

/-- `t̄[ρ]`: the arguments `t̄` in which each level variable `i` has the value `ρ i`. -/
def Args.atLevels {k : Nat} {Γ : Scope} {ps : List Parameter} (ρ : Fin k → Nat) (ts : Args k Γ ps) :
    Args 0 Γ ps :=
  ts.substLevels fun i => .ofNat (ρ i)

/-- `Θ[ρ]`: the telescope `Θ` in which each level variable `i` has the value `ρ i`. -/
def Telescope.atLevels {k : Nat} {Γ : Scope} {ps : List Parameter} (ρ : Fin k → Nat)
    (Θ : Telescope k Γ ps) : Telescope 0 Γ ps :=
  Θ.substLevels fun i => .ofNat (ρ i)

/-! ## The Sorts -/

/-- A relation between closed terms. -/
abbrev TermRel : Type := Term 0 [] → Term 0 [] → Prop

/-- The relations of the sorts of one level `n`, given by their graphs. -/
structure LevelRel where
  /-- `(A₀, B₀) ∈ eq(U_n)`, where `R` is the equality `eq(A₀)` of the terms of `A₀`. -/
  univ : Term 0 [] → Term 0 [] → TermRel → Prop
  /-- `(A₀, B₀) ∈ eq(Ω_n)`, two propositions whose truth is `b`. -/
  prop : Term 0 [] → Term 0 [] → Prop → Prop

/-- The relations of no sort, below the level `0`. -/
def LevelRel.empty : LevelRel := ⟨fun _ _ _ => False, fun _ _ _ => False⟩

-- ADE: none.
/--
`eq(U_n)`, the least relation of the clauses of the universes, given the relations `below` of the
level `n - 1`; the kinds of declarations add their clauses.
-/
inductive UnivRel (n : Nat) (below : LevelRel) : Term 0 [] → Term 0 [] → TermRel → Prop where
  /-- `(eq_U)`: the universe `U_k`, if `k + 1 = n`, whose terms are equal when they are equal in
  `eq(U_k)`. -/
  | univ {l₁ l₂ : Level 0} (h₁ : l₁.closedValue + 1 = n) (h₂ : l₂.closedValue + 1 = n) :
      UnivRel n below (.sort ⟨.type, l₁⟩) (.sort ⟨.type, l₂⟩) fun A B => ∃ R, below.univ A B R
  /-- `(eq_Ω)`: the universe of propositions `Ω_k`, if `k + 1 = n`, whose terms are equal when they
  are equal in `eq(Ω_k)`. -/
  | prop {l₁ l₂ : Level 0} (h₁ : l₁.closedValue + 1 = n) (h₂ : l₂.closedValue + 1 = n) :
      UnivRel n below (.sort ⟨.prop, l₁⟩) (.sort ⟨.prop, l₂⟩) fun P Q => ∃ b, below.prop P Q b

-- ADE: none.
/--
`eq(Ω_n)`, the least relation of the clauses of the kinds of declarations for their instances in
`Ω_n`, which relate two propositions when they have the same truth: it has no clause in the core.
-/
inductive PropRel : Term 0 [] → Term 0 [] → Prop → Prop where

/-- The relations of the sorts of the level `n`, defined after those of the level below it. -/
def levelRel : Nat → LevelRel
  | 0 => ⟨UnivRel 0 .empty, PropRel⟩
  | n + 1 => ⟨UnivRel (n + 1) (levelRel n), PropRel⟩

-- ADE: none.
/-- `eq(A₀) = R`: the closed canonical type `A₀` is a type of a sort, whose terms are equal by `R`. -/
inductive HasEq (A₀ : Term 0 []) (R : TermRel) : Prop where
  /-- A type of the universe `U_n`. -/
  | univ (n : Nat) (h : (levelRel n).univ A₀ A₀ R)
  /-- `(eq_true)` and `(eq_false)`: a proposition of `Ω_n` whose truth is `b`, whose closed terms are
  all equal proofs when it is true, and none when it is false. -/
  | prop (n : Nat) (b : Prop) (h : (levelRel n).prop A₀ A₀ b) (hR : ∀ t u, R t u ↔ b)

/-- `(prop)`: `A₀` is a proposition, a term of a universe of propositions. -/
def IsProp (A₀ : Term 0 []) : Prop := ∃ k b, (levelRel k).prop A₀ A₀ b

/-- `(prop_⇓)`: the closed type `A` computes to a proposition. -/
def ComputesToProp (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ∃ A₀, Computesι sig ι A A₀ ∧ IsProp A₀

/-! ## Closed Judgments

The clauses of the closed judgments are stated without the meaning `⊨ Σ` of their signature, which
they require, so that the meaning of the signatures is defined from them. -/

/-- The clause of `(⊨_type≡)`: `A` and `B` compute to canonical types whose terms have the same
equality. -/
def EqTypeClause (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  ∃ A₀ B₀ R, Computesι sig ι A A₀ ∧ Computesι sig ι B B₀ ∧ HasEq A₀ R ∧ HasEq B₀ R

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` for the terms: `t` and `u` compute to equal canonical terms
of the canonical form of `A`, or are equal proofs of it when it is a proposition. -/
def EqTermClause (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  (¬ ComputesToProp sig ι A → ∃ A₀ v w R, Computesι sig ι A A₀ ∧ Computesι sig ι t v ∧
    Computesι sig ι u w ∧ HasEq A₀ R ∧ R v w) ∧
  (ComputesToProp sig ι A → ∃ A₀ R, Computesι sig ι A A₀ ∧ HasEq A₀ R ∧ R t u)

-- ADE: none.
/-- `⊨ Σ`: each entry of the signature has a fresh name and is meaningful in the signature before
it, for each instance of its variables. -/
def ValidSig (ι : Interpretation) : Signature → Prop
  /- `(⊨sig_∅)`. -/
  | [] => True
  /- `(⊨sig_D)`: the kinds of declarations give the meaning of their declarations. -/
  | .typeDeclaration _ :: _ => False
  /- `(⊨sig_≔)`: the name is fresh and the body is a term of the type. -/
  | .constantDefinition d :: sig => ValidSig ι sig ∧ (∀ e ∈ sig, d.name ∉ e.names) ∧
      ∀ inst (ρ : Fin d.levels → Nat),
      EqTypeClause sig ι ((d.type inst).atLevels ρ) ((d.type inst).atLevels ρ) ∧
        EqTermClause sig ι ((d.body inst).atLevels ρ) ((d.body inst).atLevels ρ)
          ((d.type inst).atLevels ρ)
  /- `(⊨sig_c)`: the name is fresh and the interpretation is a term of the type. -/
  | .constantDeclaration c :: sig => ValidSig ι sig ∧ (∀ e ∈ sig, c.name ∉ e.names) ∧
      ∀ inst (ρ : Fin c.levels → Nat),
      EqTypeClause sig ι ((c.type inst).atLevels ρ) ((c.type inst).atLevels ρ) ∧
        EqTermClause sig ι ((ι c inst).atLevels ρ) ((ι c inst).atLevels ρ)
          ((c.type inst).atLevels ρ)

/-- `(⊨_type≡)`: `Σ ⊨ A ≡ B`. -/
def ValidEqType₀ (sig : Signature) (ι : Interpretation) (A B : Term 0 []) : Prop :=
  ValidSig ι sig ∧ EqTypeClause sig ι A B

/-- `(⊨_type)`: `Σ ⊨ A`. -/
def ValidType₀ (sig : Signature) (ι : Interpretation) (A : Term 0 []) : Prop :=
  ValidEqType₀ sig ι A A

/-- `(⊨_≡)` and `(⊨_≡Ω)`: `Σ ⊨ t ≡ u : A`. -/
def ValidEqTerm₀ (sig : Signature) (ι : Interpretation) (t u A : Term 0 []) : Prop :=
  ValidType₀ sig ι A ∧ EqTermClause sig ι t u A

/-- `(⊨)`: `Σ ⊨ t : A`. -/
def ValidTerm₀ (sig : Signature) (ι : Interpretation) (t A : Term 0 []) : Prop :=
  ValidEqTerm₀ sig ι t t A

/-! ## Hypothetical Judgments -/

/-- The substitution `σ` without its last entry. -/
def Subst.tail {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} (σ : Subst k Γ (e :: Δ)) : Subst k Γ Δ :=
  fun x => σ x.succ

/-- The number of the entries of a context, those of the telescope of a second-order variable
included. -/
def Context.size {k : Nat} : {Γ : Scope} → Context k Γ → Nat
  | _, .empty => 0
  | _, .var ctx _ => ctx.size + 1
  | _, .secondOrder (ps := ps) ctx _ _ _ => ctx.size + ps.length + 1

/-- The entries of `Γ, Θ` are those of `Γ` and of `Θ`. -/
theorem Context.size_append {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context k Γ) → (Θ : Telescope k Γ ps) →
      (ctx.append Θ).size = ctx.size + ps.length
  | _, [], _, .nil => rfl
  | _, _ :: _, ctx, .cons _ _ A Θ =>
    (Context.size_append (ctx.var A) Θ).trans (by simp only [Context.size, List.length_cons]; omega)

-- ADE: none.
/--
`(σ₁, σ₂) ∈ eq(Γ)`: two equal closed substitutions of `Γ`, which give each variable equal closed
terms of its type, and each second-order variable abstractions whose instances by equal arguments are
equal terms of its type; the arguments of a telescope are the equal substitutions of the context it
forms.
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
before it. -/
def ValidCtx₀ (sig : Signature) (ι : Interpretation) : {Γ : Scope} → Context 0 Γ → Prop
  /- `(⊨ctx_ε)`. -/
  | _, .empty => ValidSig ι sig
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

/-- `(⊨Γ_type≡)`: `Σ; Γ ⊨ A ≡ B`, at levels without variables. -/
def ValidEqTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A B : Term 0 Γ) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → ValidEqType₀ sig ι (A.subst σ₁) (B.subst σ₂)

/-- `(⊨Γ_type)`: `Σ; Γ ⊨ A`, at levels without variables. -/
def ValidTypeΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : Prop :=
  ValidEqTypeΓ sig ι ctx A A

/-- `(⊨Γ_≡)`: `Σ; Γ ⊨ t ≡ u : A`, at levels without variables. -/
def ValidEqTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t u A : Term 0 Γ) : Prop :=
  ValidTypeΓ sig ι ctx A ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι (t.subst σ₁) (u.subst σ₂) (A.subst σ₁)

/-- `(⊨Γ)`: `Σ; Γ ⊨ t : A`, at levels without variables. -/
def ValidTermΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (t A : Term 0 Γ) : Prop :=
  ValidEqTermΓ sig ι ctx t t A

-- ADE: none.
/-- `(⊨Γ_tel≡)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, at levels without variables: the arguments substituted by two
equal closed substitutions `σ₁` and `σ₂` of the context are equal substitutions of the context that
the telescope `Θ[σ₁]` forms.
RFC 24 gives no meaning to the judgment of the arguments, which its soundness needs for the rule of
`X[t̄]`. -/
def ValidEqArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts us : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidCtx₀ sig ι ctx ∧
    ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) (ts.subst σ₁).toSubst
        (us.subst σ₂).toSubst

/-- `(⊨Γ_tel)`: `Σ; Γ ⊨ t̄ : Θ`, at levels without variables. -/
def ValidArgsΓ (sig : Signature) (ι : Interpretation) {Γ : Scope} {ps : List Parameter}
    (ctx : Context 0 Γ) (ts : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ValidEqArgsΓ sig ι ctx ts ts Θ

/-- `(⊨ctx_x)`, as the RFC states it. -/
theorem validCtx₀_var {sig : Signature} {ι : Interpretation} {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : ValidCtx₀ sig ι (ctx.var A) ↔ ValidTypeΓ sig ι ctx A := by
  rw [ValidCtx₀]; rfl

/-- `(⊨ctx_X)`, as the RFC states it. -/
theorem validCtx₀_secondOrder {sig : Signature} {ι : Interpretation} {Γ : Scope}
    {ps : List Parameter} (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (A : Term 0 (Γ.extend ps.length))
    (c₀ : Option Grade) : ValidCtx₀ sig ι (ctx.secondOrder Θ A c₀) ↔ ValidTypeΓ sig ι (ctx.append Θ) A := by
  rw [ValidCtx₀]; rfl

/-! ## Telescopes -/

-- ADE: none.
/-- `Σ ⊨ Θ₁ ≡ Θ₂ : κ`: two closed telescopes are equal in the sort `κ`, their grades ignored. -/
def ValidEqTelescope₀ (sig : Signature) (ι : Interpretation) (κ : Universe 0) :
    {ps : List Parameter} → Telescope 0 [] ps → Telescope 0 [] ps → Prop
  /- `(⊨tel_κε)`. -/
  | [], .nil, .nil => ValidSig ι sig
  /- `(⊨tel_κ,)`. -/
  | _ :: _, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂ =>
    (∃ κ₁, κ₁ ≼ κ ∧ ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) ∧
      ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ A₁ →
        ValidEqTelescope₀ sig ι κ (Θ₁.subst₀ (Subst₀.single v₁)) (Θ₂.subst₀ (Subst₀.single v₂))

/-! ## Level Variables -/

/-- `(⊨_ρ)`: `Σ ⊨ Γ`, for every value of the level variables. -/
def ValidCtx (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ) :
    Prop :=
  ∀ ρ, ValidCtx₀ sig ι (ctx.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A ≡ B`, for every value of the level variables. -/
def ValidEqType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A B : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ) (B.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ A`, for every value of the level variables. -/
def ValidType (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (A : Term k Γ) : Prop :=
  ∀ ρ, ValidTypeΓ sig ι (ctx.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t ≡ u : A`, for every value of the level variables. -/
def ValidEqTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t u A : Term k Γ) : Prop :=
  ∀ ρ, ValidEqTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (u.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t : A`, for every value of the level variables. -/
def ValidTerm (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t A : Term k Γ) : Prop :=
  ∀ ρ, ValidTermΓ sig ι (ctx.atLevels ρ) (t.atLevels ρ) (A.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ ≡ ū : Θ`, for every value of the level variables. -/
def ValidEqArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts us : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidEqArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (us.atLevels ρ) (Θ.atLevels ρ)

/-- `(⊨_ρ)`: `Σ; Γ ⊨ t̄ : Θ`, for every value of the level variables. -/
def ValidArgs (sig : Signature) (ι : Interpretation) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (ts : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  ∀ ρ, ValidArgsΓ sig ι (ctx.atLevels ρ) (ts.atLevels ρ) (Θ.atLevels ρ)

/-! ## Partial Equivalence Relations

The equality `eq(A₀)` of the terms of a type is a partial equivalence relation, and it is unique.
These properties are proved level by level: those of the relations of a level, `LevelRel.IsPer`,
follow from those of the level below it, by cases on the clauses that relate two types, so that each
kind of declaration adds the cases of its clauses. -/

/-- `R` is a partial equivalence relation: symmetric and transitive. -/
structure TermRel.IsPer (R : TermRel) : Prop where
  /-- `R` is symmetric. -/
  symm {t u : Term 0 []} : R t u → R u t
  /-- `R` is transitive. -/
  trans {t u w : Term 0 []} : R t u → R u w → R t w

/-- The relations of the sorts of a level are partial equivalence relations, which give each type
they relate a unique equality of its terms, itself a partial equivalence relation. -/
structure LevelRel.IsPer (L : LevelRel) : Prop where
  /-- `eq(U_n)` is symmetric, with the same equality of terms. -/
  univ_symm {A B : Term 0 []} {R : TermRel} : L.univ A B R → L.univ B A R
  /-- `eq(U_n)` is transitive, with the equality of terms of the first type. -/
  univ_trans {A B C : Term 0 []} {R R' : TermRel} : L.univ A B R → L.univ B C R' → L.univ A C R
  /-- `eq(U_n)` gives a type a unique equality of its terms. -/
  univ_unique {A B C : Term 0 []} {R R' : TermRel} :
    L.univ A B R → L.univ A C R' → ∀ t u, R t u ↔ R' t u
  /-- The equality of the terms of a type of `U_n` is a partial equivalence relation. -/
  univ_isPer {A B : Term 0 []} {R : TermRel} : L.univ A B R → R.IsPer
  /-- `eq(Ω_n)` is symmetric, with the same truth. -/
  prop_symm {P Q : Term 0 []} {b : Prop} : L.prop P Q b → L.prop Q P b
  /-- `eq(Ω_n)` is transitive, with the truth of the first proposition. -/
  prop_trans {P Q S : Term 0 []} {b b' : Prop} : L.prop P Q b → L.prop Q S b' → L.prop P S b
  /-- `eq(Ω_n)` gives a proposition a unique truth. -/
  prop_unique {P Q S : Term 0 []} {b b' : Prop} : L.prop P Q b → L.prop P S b' → (b ↔ b')

/-- No sort is below the level `0`. -/
theorem LevelRel.empty_isPer : LevelRel.empty.IsPer where
  univ_symm h := h.elim
  univ_trans h := h.elim
  univ_unique h := h.elim
  univ_isPer h := h.elim
  prop_symm h := h.elim
  prop_trans h := h.elim
  prop_unique h := h.elim

/-- `eq(Ω_n)` is symmetric: it has no clause in the core. -/
theorem PropRel.symm {P Q : Term 0 []} {b : Prop} (h : PropRel P Q b) : PropRel Q P b := nomatch h

/-- `eq(Ω_n)` is transitive: it has no clause in the core. -/
theorem PropRel.trans {P Q S : Term 0 []} {b b' : Prop} (h : PropRel P Q b) (_h' : PropRel Q S b') :
    PropRel P S b := nomatch h

/-- `eq(Ω_n)` gives a proposition a unique truth: it has no clause in the core. -/
theorem PropRel.unique {P Q S : Term 0 []} {b b' : Prop} (h : PropRel P Q b)
    (_h' : PropRel P S b') : b ↔ b' := nomatch h

/-- The equality of the terms of the universe `U_k` relates the types that `eq(U_k)` relates. -/
theorem UnivRel.univ_isPer {below : LevelRel} (hb : below.IsPer) :
    TermRel.IsPer fun A B => ∃ R, below.univ A B R where
  symm := fun ⟨R, h⟩ => ⟨R, hb.univ_symm h⟩
  trans := fun ⟨R, h⟩ ⟨_, h'⟩ => ⟨R, hb.univ_trans h h'⟩

/-- The equality of the terms of the universe `Ω_k` relates the propositions that `eq(Ω_k)` relates.
-/
theorem UnivRel.prop_isPer {below : LevelRel} (hb : below.IsPer) :
    TermRel.IsPer fun P Q => ∃ b, below.prop P Q b where
  symm := fun ⟨b, h⟩ => ⟨b, hb.prop_symm h⟩
  trans := fun ⟨b, h⟩ ⟨_, h'⟩ => ⟨b, hb.prop_trans h h'⟩

/-- The relations of the level `n` are partial equivalence relations, if those of the level below it
are. -/
theorem UnivRel.isPer {n : Nat} {below : LevelRel} (hb : below.IsPer) :
    LevelRel.IsPer ⟨UnivRel n below, PropRel⟩ where
  univ_symm
    | .univ h₁ h₂ => .univ h₂ h₁
    | .prop h₁ h₂ => .prop h₂ h₁
  univ_trans
    | .univ h₁ _, .univ _ h₃ => .univ h₁ h₃
    | .prop h₁ _, .prop _ h₃ => .prop h₁ h₃
  univ_unique
    | .univ _ _, .univ _ _ => fun _ _ => .rfl
    | .prop _ _, .prop _ _ => fun _ _ => .rfl
  univ_isPer
    | .univ _ _ => UnivRel.univ_isPer hb
    | .prop _ _ => UnivRel.prop_isPer hb
  prop_symm := PropRel.symm
  prop_trans := PropRel.trans
  prop_unique := PropRel.unique

/-- The relations of every level are partial equivalence relations. -/
theorem levelRel_isPer : (n : Nat) → (levelRel n).IsPer
  | 0 => UnivRel.isPer LevelRel.empty_isPer
  | n + 1 => UnivRel.isPer (levelRel_isPer n)

/-- `eq(Ω_n)` has the same clauses at every level. -/
theorem levelRel_prop (n : Nat) : (levelRel n).prop = PropRel := by
  cases n <;> rfl

/-- `eq(A₀)` is a partial equivalence relation, symmetric and transitive. -/
theorem HasEq.isPer {A₀ : Term 0 []} {R : TermRel} : HasEq A₀ R → R.IsPer
  | .univ n h => (levelRel_isPer n).univ_isPer h
  | .prop _ _ _ hR => ⟨fun h => (hR _ _).2 ((hR _ _).1 h), fun h _ => (hR _ _).2 ((hR _ _).1 h)⟩

/-- A type of a universe is not a proposition. -/
theorem HasEq.univ_not_prop {A₀ : Term 0 []} {n k : Nat} {R : TermRel} {b : Prop}
    (_h : (levelRel n).univ A₀ A₀ R) (h' : (levelRel k).prop A₀ A₀ b) : False := by
  rw [levelRel_prop] at h'
  exact nomatch h'

/-- The level of a type of a universe is unique. -/
theorem HasEq.univ_level {A₀ : Term 0 []} {n n' : Nat} {R R' : TermRel}
    (h : (levelRel n).univ A₀ A₀ R) (h' : (levelRel n').univ A₀ A₀ R') : n = n' := by
  cases n <;> cases n' <;> cases h <;> cases h' <;> omega

/-- `eq(A₀)` is unique: two equalities of the terms of a type relate the same terms. -/
theorem HasEq.unique {A₀ : Term 0 []} {R R' : TermRel} :
    HasEq A₀ R → HasEq A₀ R' → ∀ t u, R t u ↔ R' t u
  | .univ n h, .univ n' h' => by
    cases HasEq.univ_level h h'
    exact (levelRel_isPer n).univ_unique h h'
  | .univ _ h, .prop _ _ h' _ => (HasEq.univ_not_prop h h').elim
  | .prop _ _ h _, .univ _ h' => (HasEq.univ_not_prop h' h).elim
  | .prop k _ h hR, .prop k' _ h' hR' => by
    rw [levelRel_prop] at h h'
    exact fun t u => (hR t u).trans ((PropRel.unique h h').trans (hR' t u).symm)

/-! ## Exactness of the Proofs -/

/-- The names of a signature stay distinct when its constants are interpreted. -/
theorem Signature.Distinct.interpret {ι : Interpretation} :
    {sig : Signature} → sig.Distinct → (sig.interpret ι).Distinct
  | [], _ => trivial
  | e :: _, ⟨h, hfresh⟩ => by
    have hnames : ∀ e : Entry, (e.interpret ι).names = e.names := by
      intro e; cases e <;> rfl
    refine ⟨h.interpret, fun e' he' n hn => ?_⟩
    obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 he'
    rw [hnames] at hn ⊢
    exact hfresh e'' he'' n hn

/-- The names of a meaningful signature are distinct. -/
theorem ValidSig.distinct {ι : Interpretation} : {sig : Signature} → ValidSig ι sig → sig.Distinct
  | [], _ => trivial
  | .constantDefinition _ :: _, ⟨h, hfresh, _⟩ => ⟨h.distinct, fun e he n hn => by
      simp only [Entry.names, List.mem_singleton] at hn
      exact hn ▸ hfresh e he⟩
  | .constantDeclaration _ :: _, ⟨h, hfresh, _⟩ => ⟨h.distinct, fun e he n hn => by
      simp only [Entry.names, List.mem_singleton] at hn
      exact hn ▸ hfresh e he⟩

/-- In a meaningful signature, a closed term computes to one canonical term at most. -/
theorem Computesι.det {sig : Signature} {ι : Interpretation} {t v₁ v₂ : Term 0 []}
    (hsig : ValidSig ι sig) (h₁ : Computesι sig ι t v₁) (h₂ : Computesι sig ι t v₂) : v₁ = v₂ :=
  Computes.det hsig.distinct.interpret h₁ h₂

/-- A sort computes to itself. -/
theorem Computes.sort (sig : Signature) (κ : Universe 0) : Computes sig (.sort κ) (.sort κ) :=
  ⟨.refl _, .sort κ⟩

/-- A sort computes to nothing else than itself. -/
theorem Computes.sort_inv {sig : Signature} {κ : Universe 0} {v : Term 0 []} :
    Computes sig (.sort κ) v → v = .sort κ
  | ⟨.refl _, _⟩ => rfl
  | ⟨.step h _, _⟩ => by
    obtain ⟨_, _, _, _, _, _, _, _, ht, _⟩ := h.inv
    cases ht

/-- The terms that the universe of propositions `Ω_l` relates are propositions. -/
theorem HasEq.prop_isProp {l : Level 0} {R : TermRel} {v w : Term 0 []}
    (hR : HasEq (.sort ⟨.prop, l⟩) R) (hvw : R v w) : IsProp v := by
  cases hR with
  | univ n h =>
    cases n with
    | zero => cases h with | prop h₁ => exact absurd h₁ (Nat.succ_ne_zero _)
    | succ m =>
      cases h with
      | prop =>
        obtain ⟨b, hb⟩ := hvw
        exact ⟨m, b, (levelRel_isPer m).prop_trans hb ((levelRel_isPer m).prop_symm hb)⟩
  | prop _ _ h _ => rw [levelRel_prop] at h; exact nomatch h

/-- A sort is not a proposition. -/
theorem not_isProp_sort {κ : Universe 0} : ¬ IsProp (.sort κ) := fun ⟨k, _, h⟩ => by
  rw [levelRel_prop] at h
  exact nomatch h

/-- A sort does not compute to a proposition. -/
theorem not_computesToProp_sort {sig : Signature} {ι : Interpretation} {κ : Universe 0} :
    ¬ ComputesToProp sig ι (.sort κ) := fun ⟨_, hc, hp⟩ => by
  cases hc.sort_inv
  exact not_isProp_sort hp

/-- `(exact_Ω)`: two closed terms are equal proofs of a proposition exactly when each of them is a
proof of it. -/
theorem exact_prop {sig : Signature} {ι : Interpretation} {A t u : Term 0 []} {l : Level 0}
    (hA : ValidTerm₀ sig ι A (.sort ⟨.prop, l⟩)) :
    ValidEqTerm₀ sig ι t u A ↔ ValidTerm₀ sig ι t A ∧ ValidTerm₀ sig ι u A := by
  obtain ⟨⟨hsig, -⟩, hcl, -⟩ := hA
  obtain ⟨A₀, v, w, R, hc, hv, -, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  have hvp := hR.prop_isProp hvw
  have hP : ComputesToProp sig ι A := ⟨v, hv, hvp⟩
  constructor
  · rintro ⟨hTA, -, hcl'⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htu⟩ := hcl' hP
    have hper := hR₁.isPer
    exact ⟨⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans htu (hper.symm htu)⟩⟩,
      ⟨hTA, fun h => absurd hP h, fun _ => ⟨A₁, R₁, hA₁, hR₁, hper.trans (hper.symm htu) htu⟩⟩⟩
  · rintro ⟨⟨hTA, -, hclt⟩, -⟩
    refine ⟨hTA, fun h => absurd hP h, fun _ => ?_⟩
    obtain ⟨A₁, R₁, hA₁, hR₁, htt⟩ := hclt hP
    cases Computesι.det hsig hA₁ hv
    obtain ⟨k, b, hb⟩ := hvp
    have hRb : ∀ t u, R₁ t u ↔ b := fun t u => hR₁.unique (.prop k b hb fun _ _ => .rfl) t u
    exact ⟨v, R₁, hA₁, hR₁, (hRb t u).2 ((hRb t t).1 htt)⟩

/-! ## Properties of the Core -/

/-- In the core, no type is a proposition, since only the kinds of declarations build propositions. -/
theorem not_isProp (A₀ : Term 0 []) : ¬ IsProp A₀ := fun ⟨k, _, h⟩ => by
  cases k <;> cases h

/-- In the core, no type computes to a proposition. -/
theorem not_computesToProp (sig : Signature) (ι : Interpretation) (A : Term 0 []) :
    ¬ ComputesToProp sig ι A := fun ⟨A₀, _, h⟩ => not_isProp A₀ h

/-! ## Examples -/

/-- `eq(U_n)`, the equality of the types of the universe `U_n`. -/
abbrev eqUniv (n : Nat) : TermRel := fun A B => ∃ R, (levelRel n).univ A B R

/-- `U_l`. -/
abbrev univ (l : Level 0) : Term 0 [] := .sort ⟨.type, l⟩

/-- `U_1` is a type whose terms are equal in `eq(U_1)`. -/
theorem hasEq_univ_one : HasEq (univ (.succ .zero)) (eqUniv 1) := .univ 2 (.univ rfl rfl)

/-- `Σ ⊨ U_0 : U_1`, in the empty signature, whatever the interpretation. -/
theorem valid_univ_zero (ι : Interpretation) :
    ValidTerm₀ [] ι (univ .zero) (univ (.succ .zero)) :=
  ⟨⟨trivial, _, _, _, Computes.sort _ _, Computes.sort _ _, hasEq_univ_one, hasEq_univ_one⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, Computes.sort _ _, Computes.sort _ _, hasEq_univ_one,
      _, .univ rfl rfl⟩,
    fun h => absurd h (not_computesToProp _ _ _)⟩

/-- `U_0` is not a term of itself: `eq(U_0)` relates no type, in the core. -/
theorem not_valid_univ_zero_univ_zero (ι : Interpretation) :
    ¬ ValidTerm₀ [] ι (univ .zero) (univ .zero) := by
  rintro ⟨-, h, -⟩
  obtain ⟨A₀, v, w, R, hA, hv, -, hR, hvw⟩ := h (not_computesToProp _ _ _)
  cases hA.sort_inv
  cases hv.sort_inv
  cases hR with
  | univ n hn =>
    cases n with
    | zero => cases hn with | univ h => cases h
    | succ m =>
      cases hn with
      | univ h =>
        obtain ⟨R', hR'⟩ := hvw
        cases m with
        | zero => cases hR' with | univ h' => cases h'
        | succ => cases h
  | prop _ _ hp => exact not_isProp _ ⟨_, _, hp⟩

/-- `Σ ⊨ U_{0 ⊔ 0} ≡ U_0`: two universes are equal types when their levels have the same value. -/
theorem valid_univ_max (ι : Interpretation) :
    ValidEqType₀ [] ι (univ (.max .zero .zero)) (univ .zero) :=
  ⟨trivial, _, _, eqUniv 0, Computes.sort _ _, Computes.sort _ _, .univ 1 (.univ rfl rfl),
    .univ 1 (.univ rfl rfl)⟩

/-- `T.{} : U_1 ▶ 11ᵐ ◀ ωωᵖ ≔ U_0`, a definition of a type. -/
def typeEntry : ConstantDefinition :=
  ⟨"T", 0, 0, 0, .oneOne, .unrestrictedUnrestricted, fun _ => univ (.succ .zero), fun _ => univ .zero⟩

/-- `T.{}`. -/
abbrev typeConst : Term 0 [] := .const "T" [] [] []

/-- `T.{}` computes to `U_0`, its body. -/
theorem computes_typeConst (ι : Interpretation) :
    Computesι [.constantDefinition typeEntry] ι typeConst (univ .zero) :=
  ⟨.step (.delta (d := typeEntry) (qs := []) (ls := []) (ps := []) (List.mem_singleton_self _) rfl rfl
    rfl) (.refl _), .sort _⟩

/-- `⊨ T.{} : U_1 ▶ 11ᵐ ◀ ωωᵖ ≔ U_0`: the definition is meaningful, whatever the interpretation. -/
theorem validSig_typeEntry (ι : Interpretation) : ValidSig ι [.constantDefinition typeEntry] :=
  ⟨trivial, fun _ h => (nomatch h), fun _ _ => ⟨(valid_univ_zero ι).1.2, (valid_univ_zero ι).2⟩⟩

/-- `Σ ⊨ T.{} ≡ U_0`: the definition is equal to its body. -/
theorem valid_typeConst (ι : Interpretation) :
    ValidEqType₀ [.constantDefinition typeEntry] ι typeConst (univ .zero) :=
  ⟨validSig_typeEntry ι, _, _, eqUniv 0, computes_typeConst ι, Computes.sort _ _,
    .univ 1 (.univ rfl rfl), .univ 1 (.univ rfl rfl)⟩

end Sic.Core
