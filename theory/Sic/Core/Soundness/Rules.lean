module

public import Sic.Core.Soundness.Signature
public import Sic.Core.Typing
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Relations
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature
import Sic.Core.Syntax.Terms

/-!
# Soundness of the Rules

Each rule of annex 14 of RFC 36 keeps the meaning of annex 18: when its premises are meaningful, in
the context of the rule at levels without variables, so is its conclusion; `Recursors` and
`Corecursors` prove it of the rules of the recursors and of those of the observations and the
corecursors, in the same way.
The proofs take the premises at two equal closed substitutions `σ₁` and `σ₂` of the context, and
draw the conclusion from the closed judgments, whose properties `Closed` gives; the symmetry and the
transitivity of `eq(Γ)` move a premise from one substitution to the other.

A rule whose conclusion is that of an other judgment of the same meaning has no proof of its own: the
reflexivity of types and terms is the meaning of their premise, as `Σ; Γ ⊨ A` is `Σ; Γ ⊨ A ≡ A` and
`Σ; Γ ⊨ t : A` is `Σ; Γ ⊨ t ≡ t : A`, and the proof of a rule of equality gives that of the rule of
typing of the same name, such as `(conv)` from `(conv_≡)`.
The rules of the contexts are the clauses of their meaning, such as `validCtx₀_var`, those of the
signatures make each entry meaningful in the whole signature, as `Judgments` proves, and the rule
`(decl)` asks the interpretation of the constant to be a term of its type, which the hypothesis
`(hyp_ι)` of the soundness gives.

ADE prove the validity of each rule in `Definition/LogicalRelation/Substitution/Introductions/`,
for their judgments with a context of definitions and without levels.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Equality of Types and of Terms -/

-- ADE: `sym-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(sym_type)` keeps the meaning. -/
theorem ValidEqTypeΓ.symm {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidEqTypeΓ sig ι ctx B A :=
  ⟨h.1, fun _ _ hσ => (h.2 _ _ (hσ.symm h.1)).symm⟩

-- ADE: `trans-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(trans_type)` keeps the meaning. -/
theorem ValidEqTypeΓ.trans {Γ : Scope} {ctx : Context 0 Γ} {A₁ A₂ A₃ : Term 0 Γ}
    (h₁ : ValidEqTypeΓ sig ι ctx A₁ A₂) (h₂ : ValidEqTypeΓ sig ι ctx A₂ A₃) :
    ValidEqTypeΓ sig ι ctx A₁ A₃ :=
  ⟨h₁.1, fun _ _ hσ => (h₁.2 _ _ hσ).trans (h₂.2 _ _ (hσ.right h₁.1))⟩

-- ADE: `wf-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `Σ; Γ ⊨ A ≡ B` gives `Σ; Γ ⊨ A`. -/
theorem ValidEqTypeΓ.left {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidTypeΓ sig ι ctx A :=
  h.trans h.symm

-- ADE: `wf-⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `Σ; Γ ⊨ A ≡ B` gives `Σ; Γ ⊨ B`. -/
theorem ValidEqTypeΓ.right {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ}
    (h : ValidEqTypeΓ sig ι ctx A B) : ValidTypeΓ sig ι ctx B :=
  h.symm.trans h

-- ADE: `sym-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(sym)` keeps the meaning: the equality at the substitutions swapped is at the type of the
second, which the type converts back to the first. -/
theorem ValidEqTermΓ.symm {Γ : Scope} {ctx : Context 0 Γ} {t u A : Term 0 Γ}
    (h : ValidEqTermΓ sig ι ctx t u A) : ValidEqTermΓ sig ι ctx u t A :=
  ⟨h.1, fun _ _ hσ =>
    (h.2 _ _ (hσ.symm h.1.1)).symm.conv (h.1.2 _ _ (hσ.symm h.1.1))⟩

-- ADE: `trans-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(trans)` keeps the meaning: the second equality, at the second substitution twice, is at its
type, which the type converts to that of the first. -/
theorem ValidEqTermΓ.trans {Γ : Scope} {ctx : Context 0 Γ} {t₁ t₂ t₃ A : Term 0 Γ}
    (h₁ : ValidEqTermΓ sig ι ctx t₁ t₂ A) (h₂ : ValidEqTermΓ sig ι ctx t₂ t₃ A) :
    ValidEqTermΓ sig ι ctx t₁ t₃ A :=
  ⟨h₁.1, fun _ _ hσ => (h₁.2 _ _ hσ).trans
    ((h₂.2 _ _ (hσ.right h₁.1.1)).conv (h₁.1.2 _ _ (hσ.symm h₁.1.1)))⟩

-- ADE: `conv-⊩ᵛ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(conv_≡)` keeps the meaning, and `(conv)` with it. -/
theorem ValidEqTermΓ.conv {Γ : Scope} {ctx : Context 0 Γ} {t u A B : Term 0 Γ}
    (h : ValidEqTermΓ sig ι ctx t u A) (hA : ValidEqTypeΓ sig ι ctx A B) :
    ValidEqTermΓ sig ι ctx t u B :=
  ⟨hA.right, fun _ _ hσ => (h.2 _ _ hσ).conv (hA.2 _ _ (hσ.left h.1.1))⟩

/-! ## Sorts -/

/-- A meaningful context is in a signature whose names are distinct, as `(⊨ctx_ε)` says for the
empty context. -/
theorem ValidCtx₀.distinct : {Γ : Scope} → {ctx : Context 0 Γ} → ValidCtx₀ sig ι ctx → sig.Distinct
  | _, .empty, h => by rw [ValidCtx₀] at h; exact h
  | _, .var ctx A, h => ValidCtx₀.distinct ((validCtx₀_var ctx A).1 h).1
  | _, .secondOrder ctx Θ A ψ, h =>
    ValidCtx₀.distinct (ValidCtx₀.append_left ((validCtx₀_secondOrder ctx Θ A ψ).1 h).1)

-- ADE: `⊩ᵛU≡U∷U`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/-- `(U_≡)` and `(Ω_≡)` keep the meaning, and `(U)` and `(Ω)` with them, at the equal levels `l` and
`l`. -/
theorem ValidEqTermΓ.sort {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx)
    {q : Quality} {l₁ l₂ : Level 0} (hl : l₁ ≈ l₂) :
    ValidEqTermΓ sig ι ctx (.sort ⟨q, l₁⟩) (.sort ⟨q, l₂⟩) (.sort ⟨.type, .succ l₁⟩) :=
  ⟨⟨hctx, fun _ _ _ => (ValidEqTerm₀.sort hctx.distinct (q := q) (Level.equivalence.refl l₁)).1⟩,
    fun _ _ _ => ValidEqTerm₀.sort hctx.distinct hl⟩

-- ADE: `⊩ᵛ≡∷U→⊩ᵛ≡`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/-- `(U_type≡)` keeps the meaning, and `(U_type)` with it. -/
theorem ValidEqTermΓ.univType {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ} {l : Level 0}
    (h : ValidEqTermΓ sig ι ctx A B (.sort ⟨.type, l⟩)) : ValidEqTypeΓ sig ι ctx A B :=
  ⟨h.1.1, fun _ _ hσ => (h.2 _ _ hσ).univType⟩

-- ADE: none.
/-- `(Ω_type≡)` keeps the meaning, and `(Ω_type)` with it. -/
theorem ValidEqTermΓ.propType {Γ : Scope} {ctx : Context 0 Γ} {A B : Term 0 Γ} {l : Level 0}
    (h : ValidEqTermΓ sig ι ctx A B (.sort ⟨.prop, l⟩)) : ValidEqTypeΓ sig ι ctx A B :=
  ⟨h.1.1, fun _ _ hσ => (h.2 _ _ hσ).propType⟩

-- ADE: none.
/-- `(irr)` keeps the meaning: at two equal substitutions, the first term is a proof of the
proposition at the first, and so is the second term, by conversion, so that `(exact_Ω)` makes them
equal proofs. -/
theorem ValidEqTermΓ.irr {Γ : Scope} {ctx : Context 0 Γ} {t u A : Term 0 Γ} {l : Level 0}
    (ht : ValidTermΓ sig ι ctx t A) (hu : ValidTermΓ sig ι ctx u A)
    (hA : ValidTermΓ sig ι ctx A (.sort ⟨.prop, l⟩)) : ValidEqTermΓ sig ι ctx t u A :=
  ⟨ht.1, fun _ _ hσ => (exact_prop (hA.2 _ _ (hσ.left ht.1.1))).2
    ⟨ht.2 _ _ (hσ.left ht.1.1),
      (hu.2 _ _ (hσ.right ht.1.1)).conv (ht.1.2 _ _ (hσ.symm ht.1.1))⟩⟩

/-! ## Variables and Arguments of Telescopes -/

-- ADE: `varᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Var.agda`.
/-- `(var)` keeps the meaning: equal substitutions give the variable equal terms of its type. -/
theorem ValidTermΓ.var {Γ : Scope} {ctx : Context 0 Γ} {x : Var Γ .var} {A : Term 0 Γ}
    (hctx : ValidCtx₀ sig ι ctx) (hx : ctx.VarIn x A) : ValidTermΓ sig ι ctx (.var₀ x) A :=
  ⟨hx.validTypeΓ hctx, fun _ _ h => EqSubst.varIn hx h⟩

-- ADE: none.
/-- `(var_X≡)` keeps the meaning, and `(var_X)` with it: equal substitutions give the second-order
variable equal abstractions, whose instances by the equal substitutions that the arguments give its
telescope are equal terms of its type.
The type at the arguments `t̄` substituted by `σ₁` and by `σ₂` is the type at `t̄[σ₁]` and at
`ū[σ₂]`, then at `ū[σ₂]` and at `t̄[σ₂]`, both equal by the meaning of the entry. -/
theorem ValidEqTermΓ.secondOrder {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {ctx : Context 0 Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope 0 Γ ps}
    {A : Term 0 (Γ.extend ps.length)} {ts us : Args 0 Γ ps} (hctx : ValidCtx₀ sig ι ctx)
    (hX : ctx.SecondOrderIn X Θ A) (hts : ValidEqArgsΓ sig ι ctx ts us Θ) :
    ValidEqTermΓ sig ι ctx (.var X ts) (.var X us) (A.instantiate ts) := by
  have hA : ∀ σ : Subst 0 [] Γ,
      (A.instantiate ts).subst σ = (A.subst (Subst.liftN _ σ)).subst (ts.subst σ).toSubst :=
    fun σ => (Term.instantiate_subst σ A ts).trans (Term.instantiate_eq_subst _ _)
  have hX' : ∀ (σ : Subst 0 [] Γ) (vs : Args 0 Γ ps),
      (Term.var X vs).subst σ = (σ X).subst (vs.subst σ).toSubst :=
    fun _ _ => Term.instantiate_eq_subst _ _
  refine ⟨⟨hctx, fun σ₁ σ₂ h => ?_⟩, fun σ₁ σ₂ h => ?_⟩
  · rw [hA, hA]
    exact (hX.validEqType hctx _ _ h _ _ (hts.2 _ _ h)).trans
      (hX.validEqType hctx _ _ (h.right hctx) _ _ (hts.2 _ _ (h.right hctx))).symm
  · rw [hA, hX', hX']
    exact EqSubst.secondOrderIn hX h _ _ (hts.2 _ _ h)

-- ADE: none.
/-- `(tel_ε≡)` keeps the meaning, and `(tel_ε)` with it: no arguments are equal substitutions of the
empty telescope. -/
theorem ValidEqArgsΓ.nil {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx) :
    ValidEqArgsΓ sig ι ctx .nil .nil .nil :=
  ⟨hctx, fun _ _ _ => (EqSubst.empty_iff _ _).2 trivial⟩

-- ADE: none.
/-- `(tel_,≡)` keeps the meaning, and `(tel_,)` with it: equal first arguments of `A`, and equal
arguments of `Θ[t / x]`, are equal arguments of `x : A, Θ`. -/
theorem ValidEqArgsΓ.cons {Γ : Scope} {ps : List Parameter} {ctx : Context 0 Γ} {q : Grade} {p : Parameter}
    {t u A : Term 0 Γ} {ts us : Args 0 Γ ps} {Θ : Telescope 0 (.var :: Γ) ps}
    (ht : ValidEqTermΓ sig ι ctx t u A)
    (hts : ValidEqArgsΓ sig ι ctx ts us (Θ.subst₀ (Subst₀.single t))) :
    ValidEqArgsΓ sig ι ctx (.cons t ts) (.cons u us) (.cons q p A Θ) := by
  refine ⟨hts.1, fun σ₁ σ₂ h => ?_⟩
  have d₁ : Subst.dropN ps.length (Subst.append (Subst.closedSingle (t.subst σ₁))
      (ts.subst σ₁).toSubst) .zero = t.subst σ₁ := Subst.dropN_append _ _ .zero
  have d₂ : Subst.dropN ps.length (Subst.append (Subst.closedSingle (u.subst σ₂))
      (us.subst σ₂).toSubst) .zero = u.subst σ₂ := Subst.dropN_append _ _ .zero
  refine (EqSubst.telescope_cons_iff q p A Θ σ₁
    (Subst.append (Subst.closedSingle (t.subst σ₁)) (ts.subst σ₁).toSubst)
    (Subst.append (Subst.closedSingle (u.subst σ₂)) (us.subst σ₂).toSubst)).2 ⟨?_, ?_⟩
  · rw [d₁, d₂]
    exact ht.2 σ₁ σ₂ h
  · rw [Telescope.subst₀_single_subst Θ t σ₁ _ d₁,
      EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))]
    exact hts.2 σ₁ σ₂ h

/-! ## Constants

A constant of the signature `Σ_T` of the typing unfolds, in a signature `Σ` that gives the entries of
`Σ_T` their meaning, once the constants are interpreted, to a body that is a term of its type at the
values of its levels, and so at levels of these values, which the meaning
does not tell apart: the constant is then a term of its type, as `(f)` says, which gives `(δ)` by a
step of reduction and `(f_≡)` at levels of the same values.
-/

-- ADE: none.
/-- `(f)`, closed: a constant of `Σ_T` at closed levels is a term of its type at these levels, in a
signature `Σ` that gives the entries of `Σ_T` their meaning. -/
theorem ValidTerm₀.const {sigT : Signature} (hd : sig.Distinct) (hent : sig.ValidEntries ι sigT)
    {f : Name} {j k' g : Nat} {m : Mode} {p : Grade}
    {A : Instance j g → Term k' []} (h : sigT.HasConstant f j k' g m p A) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = j) (hl : ls.length = k')
    (hp : ps.length = g) :
    ValidTerm₀ sig ι (.const f qs ls ps) ((A (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) := by
  obtain ⟨b, hred, hb⟩ := hent.hasConstant h
  have hb' := (hb (.ofLists qs ps hq hp) fun i => (ls.getFin hl i).closedValue).levelEquiv
    (Term.substLevels_levelEquiv_atLevels _ _).symm (Term.substLevels_levelEquiv_atLevels _ _).symm
    (Term.substLevels_levelEquiv_atLevels _ _).symm
  have hr := hred qs ls ps hq hl hp
  rw [Signature.instanceType, Term.weakenClosed_nil] at hr
  exact (ValidEqTerm₀.red_iff hd hr).2 ((ValidEqTerm₀.red_iff hd hr).2 hb').symm

-- ADE: `defnᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Definition.agda`.
/-- `(f)` keeps the meaning. -/
theorem ValidTermΓ.const {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hctx : ValidCtx₀ sig ι ctx) (hent : sig.ValidEntries ι sigT) {f : Name}
    {j k' g : Nat} {m : Mode} {p : Grade} {A : Instance j g → Term k' []}
    (h : sigT.HasConstant f j k' g m p A) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = j) (hl : ls.length = k') (hp : ps.length = g) :
    ValidTermΓ sig ι ctx (.const f qs ls ps)
      (Signature.instanceType A (.ofLists qs ps hq hp) (ls.getFin hl)) := by
  have hc := ValidTerm₀.const hctx.distinct hent h hq hl hp
  refine ⟨⟨hctx, fun _ _ _ => ?_⟩, fun _ _ _ => ?_⟩
  · simp only [Signature.instanceType, Term.subst_weakenClosed]
    exact hc.1
  · simp only [Signature.instanceType, Term.subst_weakenClosed]
    exact hc

-- ADE: `δ-redᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Definition.agda`.
/-- `(δ)` keeps the meaning: the constant is a term of its type, and steps to its body. -/
theorem ValidEqTermΓ.delta {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hctx : ValidCtx₀ sig ι ctx) (hent : sig.ValidEntries ι sigT)
    {d : ConstantDefinition} (h : .constantDefinition d ∈ sigT) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
    (hp : ps.length = d.grades) :
    ValidEqTermΓ sig ι ctx (.const d.name qs ls ps)
      (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))
      (Signature.instanceType d.type (.ofLists qs ps hq hp) (ls.getFin hl)) := by
  have hc := ValidTerm₀.const hctx.distinct hent (.constantDefinition h) hq hl hp
  have hr := (Red.delta (Γ := []) (hent _ h).1 hq hl hp).interpret (ι := ι)
  rw [Signature.instanceType, Term.weakenClosed_nil] at hr
  refine ⟨⟨hctx, fun _ _ _ => ?_⟩, fun _ _ _ => ?_⟩
  · simp only [Signature.instanceType, Term.subst_weakenClosed]
    exact hc.1
  · simp only [Signature.instanceType, Term.subst_weakenClosed]
    exact ((ValidEqTerm₀.red_iff hctx.distinct hr).1 hc).symm

-- ADE: none.
/-- `(f_≡)` keeps the meaning: the instances of the constant at levels of the same values are the same
term up to its levels. -/
theorem ValidEqTermΓ.const {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hctx : ValidCtx₀ sig ι ctx) (hent : sig.ValidEntries ι sigT) {f : Name}
    {j k' g : Nat} {m : Mode} {p : Grade} {A : Instance j g → Term k' []}
    (h : sigT.HasConstant f j k' g m p A) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = j) (hl₁ : ls₁.length = k') (hl₂ : ls₂.length = k')
    (hp : ps.length = g) (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
    ValidEqTermΓ sig ι ctx (.const f qs ls₁ ps) (.const f qs ls₂ ps)
      (Signature.instanceType A (.ofLists qs ps hq hp) (ls₁.getFin hl₁)) :=
  have hc := ValidTermΓ.const hctx hent h hq hl₁ hp
  ⟨hc.1, fun _ _ h => (hc.2 _ _ h).levelEquiv (Term.LevelEquiv.refl _)
    (.const f qs ps (Level.ListEquiv.of_getFin hl₁ hl₂ hls)) (Term.LevelEquiv.refl _)⟩

/-! ## Arguments of Instances -/

-- ADE: none.
/-- `(arg_ε≡)` keeps the meaning, and `(arg_ε)` with it: no arguments are equal substitutions of the
empty parameters. -/
theorem ValidEqInstanceArgsΓ.nil {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx) :
    ValidEqInstanceArgsΓ sig ι ctx .nil .nil .empty :=
  ⟨hctx, fun _ _ _ => (EqSubst.empty_iff _ _).2 trivial⟩

-- ADE: none.
/-- `(arg_x≡)` keeps the meaning, and `(arg_x)` with it: equal arguments of the parameters before a
variable, and equal arguments of its type, which the first ones instantiate, are equal substitutions
of the parameters. -/
theorem ValidEqInstanceArgsΓ.var {Γ Δ : Scope} {ctx : Context 0 Γ} {as₁ as₂ : InstanceArgs 0 Γ Δ}
    {params : Context 0 Δ} {a₁ a₂ : Term 0 Γ} {A : Term 0 Δ}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂ params)
    (ha : ValidEqTermΓ sig ι ctx a₁ a₂ (A.subst as₁.toSubst)) :
    ValidEqInstanceArgsΓ sig ι ctx (.snoc (e := .var) as₁ a₁) (.snoc (e := .var) as₂ a₂)
      (params.var A) := by
  refine ⟨has.1, fun σ₁ σ₂ h => (EqSubst.var_iff params A _ _).2 ⟨has.2 σ₁ σ₂ h, ?_⟩⟩
  show ValidEqTerm₀ sig ι (a₁.subst σ₁) (a₂.subst σ₂) (A.subst (as₁.subst σ₁).toSubst)
  rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst σ₁ as₁) A]
  exact ha.2 σ₁ σ₂ h

-- ADE: none.
/-- `(arg_X≡)` keeps the meaning, and `(arg_X)` with it: equal arguments of the parameters before a
second-order variable, and equal abstractions for it, under the variables of its telescope, which
the first ones instantiate, are equal substitutions of the parameters; the abstractions at equal
substitutions of the telescope are the abstractions at equal substitutions of the context extended
by it. -/
theorem ValidEqInstanceArgsΓ.secondOrder {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
    {ctx : Context 0 Γ} {as₁ as₂ : InstanceArgs 0 Γ Δ} {params : Context 0 Δ}
    {Θ : Telescope 0 Δ ps} {A : Term 0 (Δ.extend ps.length)} {B₁ B₂ : Term 0 (Γ.extend ps.length)}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂ params)
    (hB : ValidEqTermΓ sig ι (ctx.append (Θ.subst as₁.toSubst)) B₁ B₂
      (A.subst (Subst.liftN _ as₁.toSubst))) :
    ValidEqInstanceArgsΓ sig ι ctx (.snoc (e := .secondOrder ps ψ) as₁ B₁)
      (.snoc (e := .secondOrder ps ψ) as₂ B₂) (params.secondOrder Θ A ψ) := by
  refine ⟨has.1, fun σ₁ σ₂ h =>
    (EqSubst.secondOrder_iff params Θ A ψ _ _).2 ⟨has.2 σ₁ σ₂ h, fun τ₁ τ₂ hτ => ?_⟩⟩
  have hc : ∀ {a} (x : Var Δ a), (as₁.toSubst x).subst (Subst.liftN a.params.length σ₁) =
      (as₁.subst σ₁).toSubst x := InstanceArgs.toSubst_subst σ₁ as₁
  change EqSubst sig ι (Context.empty.append (Θ.subst (as₁.subst σ₁).toSubst)) τ₁ τ₂ at hτ
  change ValidEqTerm₀ sig ι ((B₁.subst (Subst.liftN ps.length σ₁)).subst τ₁)
    ((B₂.subst (Subst.liftN ps.length σ₂)).subst τ₂)
    ((A.subst (Subst.liftN ps.length (as₁.subst σ₁).toSubst)).subst τ₁)
  rw [← Telescope.subst_subst_of hc Θ] at hτ
  rw [← Term.subst_subst_of (Subst.liftN_subst_of _ hc) A]
  simp only [Term.subst_append]
  exact hB.2 _ _ ((EqSubst.append_append_iff ctx _ σ₁ σ₂ τ₁ τ₂).2 ⟨h, hτ⟩)

/-! ## Telescopes in a Sort -/

-- ADE: none.
/-- `(tel_κε≡)` keeps the meaning, and `(tel_κε)` with it. -/
theorem ValidEqTelescopeΓ.nil {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx)
    {κ : Universe 0} : ValidEqTelescopeΓ sig ι ctx .nil .nil κ :=
  ⟨hctx, fun _ _ _ => hctx.distinct⟩

-- ADE: none.
/-- `(tel_κ,≡)` keeps the meaning, and `(tel_κ,)` with it: the first types are equal types of the
sort `κ₁`, which `κ₂` bounds, and the rest of the telescopes at equal terms of them are the
telescopes at equal substitutions of the context extended by the first entry of the first one; the
meaning ignores the grades. -/
theorem ValidEqTelescopeΓ.cons {Γ : Scope} {ps : List Parameter} {ctx : Context 0 Γ}
    {q₁ q₂ : Grade} {p : Parameter} {A₁ A₂ : Term 0 Γ} {Θ₁ Θ₂ : Telescope 0 (.var :: Γ) ps}
    {κ₁ κ₂ : Universe 0} (hA : ValidEqTermΓ sig ι ctx A₁ A₂ (.sort κ₁)) (hκ : κ₁ ≼ κ₂)
    (hΘ : ValidEqTelescopeΓ sig ι (ctx.var A₁) Θ₁ Θ₂ κ₂) :
    ValidEqTelescopeΓ sig ι ctx (.cons q₁ p A₁ Θ₁) (.cons q₂ p A₂ Θ₂) κ₂ := by
  refine ⟨hA.1.1, fun σ₁ σ₂ h => ?_⟩
  show (∃ κ, κ ≼ κ₂ ∧ ValidEqTerm₀ sig ι (A₁.subst σ₁) (A₂.subst σ₂) (.sort κ)) ∧
    ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ (A₁.subst σ₁) →
      ValidEqTelescope₀ sig ι κ₂ ((Θ₁.subst (Subst.lift σ₁)).subst₀ (Subst₀.single v₁))
        ((Θ₂.subst (Subst.lift σ₂)).subst₀ (Subst₀.single v₂))
  refine ⟨⟨κ₁, hκ, hA.2 σ₁ σ₂ h⟩, fun v₁ v₂ hv => ?_⟩
  rw [Telescope.subst_lift_single, Telescope.subst_lift_single]
  exact hΘ.2 _ _ ((EqSubst.var_iff ctx A₁ _ _).2 ⟨h, hv⟩)

-- ADE: none.
/-- `(fields_ε)` keeps the meaning: no field. -/
theorem ValidFieldsΓ.nil {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx)
    {inst : Name → Term 0 Γ} {rs : Nat → Option Name} {κ : Universe 0} :
    ValidFieldsΓ sig ι ctx inst rs .nil κ :=
  ⟨hctx, fun _ _ _ => hctx.distinct⟩

-- ADE: none.
/-- `(fields_,)` keeps the meaning: a first field that is not recursive, whose type is a type of the
sort `κ₁`, which `κ` bounds, and the rest at equal terms of it, which are the fields at equal
substitutions of the context extended by it, at which the instances of the block are the same. -/
theorem ValidFieldsΓ.cons {Γ : Scope} {ps : List Parameter} {ctx : Context 0 Γ} {q : Grade}
    {p : Parameter} {A : Term 0 Γ} {Θ : Telescope 0 (.var :: Γ) ps} {κ₁ κ : Universe 0}
    {inst : Name → Term 0 Γ} {rs : Nat → Option Name} (hA : ValidTermΓ sig ι ctx A (.sort κ₁))
    (hκ : κ₁ ≼ κ) (hr : rs 0 = none)
    (hΘ : ValidFieldsΓ sig ι (ctx.var A) (fun D => (inst D).rename Ren.weaken)
      (fun i => rs (i + 1)) Θ κ) :
    ValidFieldsΓ sig ι ctx inst rs (.cons q p A Θ) κ := by
  refine ⟨hA.1.1, fun σ₁ σ₂ h => ?_⟩
  rw [Telescope.subst, Telescope.subst, ValidEqFields₀, hr]
  refine ⟨⟨κ₁, hκ, hA.2 σ₁ σ₂ h⟩, fun v₁ v₂ hv => ?_⟩
  rw [Telescope.subst_lift_single, Telescope.subst_lift_single]
  have := hΘ.2 _ _ ((EqSubst.var_iff ctx A (Subst.append (n := 1) σ₁ (Subst.closedSingle v₁))
    (Subst.append (n := 1) σ₂ (Subst.closedSingle v₂))).2 ⟨h, hv⟩)
  have heq : ∀ (σ : Subst 0 [] Γ) (v : Term 0 []) D,
      ((inst D).rename Ren.weaken).subst (Subst.append (n := 1) σ (Subst.closedSingle v)) =
        (inst D).subst σ :=
    fun σ _ D => Term.subst_rename_of (fun x => Subst.append_weakenN σ _ x) _
  rw [show (fun D => (inst D).subst σ₁) = fun D => ((inst D).rename Ren.weaken).subst
      (Subst.append (n := 1) σ₁ (Subst.closedSingle v₁)) from funext fun D => (heq σ₁ v₁ D).symm,
    show (fun D => (inst D).subst σ₂) = fun D => ((inst D).rename Ren.weaken).subst
      (Subst.append (n := 1) σ₂ (Subst.closedSingle v₂)) from funext fun D => (heq σ₂ v₂ D).symm]
  exact this

-- ADE: none.
/-- `(fields_rec)` keeps the meaning: a first field that is recursive, the instance of a type of the
block, and the rest, which does not depend on it, at any terms of it. -/
theorem ValidFieldsΓ.recursive {Γ : Scope} {ps : List Parameter} {ctx : Context 0 Γ} {q : Grade}
    {p : Parameter} {Θ : Telescope 0 Γ ps} {κ : Universe 0} {inst : Name → Term 0 Γ}
    {rs : Nat → Option Name} {D : Name} (hr : rs 0 = some D)
    (hΘ : ValidFieldsΓ sig ι ctx inst (fun i => rs (i + 1)) Θ κ) :
    ValidFieldsΓ sig ι ctx inst rs (.cons q p (inst D) (Θ.rename Ren.weaken)) κ := by
  refine ⟨hΘ.1, fun σ₁ σ₂ h => ?_⟩
  rw [Telescope.subst, Telescope.subst, ValidEqFields₀, hr]
  refine ⟨rfl, rfl, fun v₁ v₂ => ?_⟩
  have heq : ∀ (σ : Subst 0 [] Γ) (v : Term 0 []),
      (Θ.rename Ren.weaken).subst (Subst.append (n := 1) σ (Subst.closedSingle v)) = Θ.subst σ :=
    fun σ _ => Telescope.subst_rename_of (fun x => Subst.append_weakenN σ _ x) _
  rw [Telescope.subst_lift_single, Telescope.subst_lift_single, heq, heq]
  exact hΘ.2 σ₁ σ₂ h

/-! ## Destructors of a Block -/

/-- A closed substitution followed by closed arguments gives a renamed variable under the arguments
what a substitution that the renaming composes gives the variable. -/
theorem Subst.append_liftN_rename {Γ Δ : Scope} {n : Nat} (α : Ren Γ Δ) {θ : Subst 0 [] Γ}
    {θ' : Subst 0 [] Δ} (h : ∀ {a} (x : Var Δ a), θ (α x) = θ' x)
    (τ : Subst 0 [] (Scope.extend [] n)) {a : Scope.Entry} (x : Var (Δ.extend n) a) :
    Subst.append θ τ (Ren.liftN n α x) = Subst.append θ' τ x := by
  rcases Var.cases_extend n x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Ren.liftN_weakenN, Subst.append_weakenN, Subst.append_weakenN]
    exact h y
  · rw [Ren.liftN_comp_of n (α₃ := Ren.empty) (fun y => nomatch y) z, Subst.append_liftN_empty,
      Subst.append_liftN_empty]

/-- Renamed destructors, at closed substitutions that the renaming composes, are equal when the
destructors are, at the composed substitutions, with the instances of the block renamed. -/
theorem ValidEqDestructors₀.rename {κ : Universe 0} :
    {Γ Δ : Scope} → {ns : List Name} → (α : Ren Γ Δ) → {inst : Name → Term 0 Δ} →
      {rs : Nat → Option Name} → {ds : Destructors 0 Δ ns} → {θ₁ θ₂ : Subst 0 [] Γ} →
      {θ₁' θ₂' : Subst 0 [] Δ} → (∀ {a} (x : Var Δ a), θ₁ (α x) = θ₁' x) →
      (∀ {a} (x : Var Δ a), θ₂ (α x) = θ₂' x) →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁' θ₂' →
      ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename α) rs (ds.rename α) θ₁ θ₂
  | _, _, _, _, _, _, .nil, _, _, _, _, _, _, h => h
  | _, _, _, α, inst, rs, .cons (ps := ps) (ψ := ψ) _ _ Θ B ds, θ₁, θ₂, θ₁', θ₂', h₁, h₂, h => by
    rw [ValidEqDestructors₀] at h
    rw [Destructors.rename, ValidEqDestructors₀, Telescope.subst_rename_of h₁,
      Telescope.subst_rename_of h₂]
    obtain ⟨hΘ, h⟩ := h
    refine ⟨hΘ, ?_⟩
    have hB : ∀ (θ : Subst 0 [] _) (θ' : Subst 0 [] _), (∀ {a} (x : Var _ a), θ (α x) = θ' x) →
        ∀ τ, (B.rename (Ren.liftN ps.length α)).subst (Subst.append θ τ) =
          B.subst (Subst.append θ' τ) := fun θ θ' hθ τ =>
      Term.subst_rename_of (Subst.append_liftN_rename α hθ τ) B
    have hsnoc : ∀ (θ : Subst 0 [] _) (θ' : Subst 0 [] _), (∀ {a} (x : Var _ a), θ (α x) = θ' x) →
        ∀ f {a} (x : Var (.secondOrder ps ψ :: _) a),
          Subst.snoc (e := .secondOrder ps ψ) θ f (Ren.lift α x) =
            Subst.snoc (e := .secondOrder ps ψ) θ' f x := fun θ θ' hθ f a x => by
      cases x with
      | zero => rfl
      | succ x => exact hθ x
    have hinst : (fun D => ((inst D).rename α).rename Ren.weaken) =
        fun D => ((inst D).rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) α) :=
      funext fun D => (Term.rename_rename_of (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl)
        _).trans (Term.rename_rename_of (α₁ := Ren.lift α) (α₂ := Ren.weaken)
          (α₃ := fun x => Ren.weaken (α x)) (fun _ => rfl) _).symm
    split at h
    · obtain ⟨⟨κ₁, hκ, hBe⟩, hds⟩ := h
      refine ⟨⟨κ₁, hκ, fun τ₁ τ₂ hτ => ?_⟩, fun f₁ f₂ hf => ?_⟩
      · rw [hB θ₁ θ₁' h₁, hB θ₂ θ₂' h₂]
        exact hBe τ₁ τ₂ hτ
      · rw [hinst]
        refine ValidEqDestructors₀.rename (Ren.lift α) (hsnoc θ₁ θ₁' h₁ f₁) (hsnoc θ₂ θ₂' h₂ f₂)
          (hds f₁ f₂ fun τ₁ τ₂ hτ => ?_)
        rw [← hB θ₁ θ₁' h₁]
        exact hf τ₁ τ₂ hτ
    · rename_i D _
      obtain ⟨hBD, hds⟩ := h
      refine ⟨?_, fun f₁ f₂ => ?_⟩
      · rw [hBD, Term.rename_rename_of (α₁ := Ren.liftN ps.length α)
            (α₂ := Ren.weakenN ps.length) (α₃ := fun x => (α x).weakenN ps.length)
            (fun x => Ren.liftN_weakenN _ α x),
          Term.rename_rename_of (α₁ := Ren.weakenN ps.length) (α₂ := α)
            (α₃ := fun x => (α x).weakenN ps.length) (fun _ => rfl)]
      · rw [hinst]
        exact ValidEqDestructors₀.rename (Ren.lift α) (hsnoc θ₁ θ₁' h₁ f₁) (hsnoc θ₂ θ₂' h₂ f₂)
          (hds f₁ f₂)

/-- `(⊨d̄_κε)`, in a context. -/
theorem ValidDestructorsΓ.nil {Γ : Scope} {ctx : Context 0 Γ} {inst : Name → Term 0 Γ}
    {rs : Nat → Option Name} {κ : Universe 0} (hctx : ValidCtx₀ sig ι ctx) :
    ValidDestructorsΓ sig ι ctx inst rs .nil κ :=
  ⟨hctx, fun _ _ _ => by rw [ValidEqDestructors₀]; exact hctx.distinct⟩

/-- `(⊨d̄_κ|)`, in a context: the destructors after a destructor that is not recursive are in the
context extended by it. -/
theorem ValidDestructorsΓ.cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {ctx : Context 0 Γ} {p q : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {κ₁ κ : Universe 0} {inst : Name → Term 0 Γ} {rs : Nat → Option Name} (hr : rs 0 = none)
    (hΘ : ValidTelescopeΓ sig ι ctx Θ ⟨.type, κ.level⟩)
    (hB : ValidTermΓ sig ι (ctx.append Θ) B (.sort κ₁)) (hκ : κ₁ ≼ κ)
    (hds : ValidDestructorsΓ sig ι (ctx.secondOrder Θ B ψ) (fun D => (inst D).rename Ren.weaken)
      (fun i => rs (i + 1)) ds κ) :
    ValidDestructorsΓ sig ι ctx inst rs (.cons (d := d) p q Θ B ψ ds) κ := by
  refine ⟨hΘ.1, fun σ₁ σ₂ h => ?_⟩
  rw [ValidEqDestructors₀, hr]
  refine ⟨hΘ.2 σ₁ σ₂ h, ⟨κ₁, hκ, fun τ₁ τ₂ hτ =>
    hB.2 _ _ ((EqSubst.append_append_iff ctx Θ σ₁ σ₂ τ₁ τ₂).2 ⟨h, hτ⟩)⟩, fun f₁ f₂ hf => ?_⟩
  refine hds.2 _ _ ((EqSubst.secondOrder_iff ctx Θ B ψ _ _).2 ⟨h, fun τ₁ τ₂ hτ => ?_⟩)
  show ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) ((B.subst (Subst.liftN _ σ₁)).subst τ₁)
  rw [Term.subst_append]
  exact hf τ₁ τ₂ hτ

/-- `(⊨d̄_κrec)`, in a context: the destructors after a recursive destructor, which do not depend on
it, are in the same context. -/
theorem ValidDestructorsΓ.recursive {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {ctx : Context 0 Γ} {p q : Grade} {Θ : Telescope 0 Γ ps} {ψ : ResultOwnership ps.length}
    {ds : Destructors 0 Γ ns} {κ : Universe 0} {inst : Name → Term 0 Γ} {rs : Nat → Option Name}
    {D : Name} (hr : rs 0 = some D) (hΘ : ValidTelescopeΓ sig ι ctx Θ ⟨.type, κ.level⟩)
    (hds : ValidDestructorsΓ sig ι ctx inst (fun i => rs (i + 1)) ds κ) :
    ValidDestructorsΓ sig ι ctx inst rs
      (.cons (d := d) p q Θ ((inst D).rename (Ren.weakenN ps.length)) ψ (ds.rename Ren.weaken))
      κ := by
  refine ⟨hΘ.1, fun σ₁ σ₂ h => ?_⟩
  rw [ValidEqDestructors₀, hr]
  exact ⟨hΘ.2 σ₁ σ₂ h, rfl, fun f₁ f₂ =>
    ValidEqDestructors₀.rename (θ₁' := σ₁) (θ₂' := σ₂) Ren.weaken (fun _ => rfl) (fun _ => rfl)
      (hds.2 σ₁ σ₂ h)⟩

-- ADE: none.
/-- Destructors equal in a sort `κ` at two closed substitutions of their scope are destructors of the
graph of `κ` with the same equality of the abstractions for them, at these substitutions, whatever
the relations `Rf D` of the results of their recursive destructors of the type `D`, in a signature
whose names are distinct: the equality of the results of a destructor is defined from the graph at
the first substitution, rather than chosen, since the graph gives one at most, and so is that of the
destructors after it, at each abstraction for it; after a recursive destructor, on which they do not
depend, it is the one at any abstraction. -/
theorem ValidEqDestructors₀.desRel (hd : sig.Distinct) {κ : Universe 0} (Rf : Name → TermRel) :
    {Γ : Scope} → {ns : List Name} → {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} →
      {ds : Destructors 0 Γ ns} → {θ₁ θ₂ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁ θ₂ →
      ∃ S, DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) ds @θ₁ S ∧
        DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) ds @θ₂ S
  | _, _, _, _, .nil, _, _, _ => ⟨fun _ _ => True, .nil, .nil⟩
  | _, _, _, rs, .cons (d := d) (ps := ps) _ _ Θ B ψ ds, θ₁, θ₂, h => by
    rw [ValidEqDestructors₀] at h
    obtain ⟨hΘ, h⟩ := h
    have ih : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
    have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
      (fun _ _ h => by cases h)
    have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hT₁
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hB⟩, hds⟩ := h
      -- The results at the first substitution and equal arguments are equal types.
      have hBB : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
          ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst))
            (B.subst (Subst.append θ₁ us.toSubst)) (.sort κ₁) := fun ts us hts =>
        have huu := hSp.trans (hSp.symm hts) hts
        (hB _ _ ((hT ts us).1 hts)).trans (hB _ _ ((hT us us).1 huu)).symm
      let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
        ∃ w F', Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w F' ∧ F' t u
      have hFeq : ∀ (ts : Args 0 [] ps) w F₀,
          Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w →
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w F₀ →
          F ts.terms = F₀ := fun ts w F₀ hw hF₀ =>
        funext fun t => funext fun u => propext
          ⟨fun ⟨ts', hts', w', F', hw', hF', h'⟩ => by
            cases Args.terms_inj hts'
            cases Computesι.det hd hw hw'
            exact (FieldRel.unique hd ih hF' _ _ hF₀ t u).1 h',
          fun h' => ⟨ts, rfl, w, F₀, hw, hF₀, h'⟩⟩
      -- A type equal to the result at the first substitution and the arguments `ts` has the
      -- equality `F ts`.
      have hres : ∀ (ts : Args 0 [] ps) (A : Term 0 []),
          ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst)) A (.sort κ₁) →
          (∃ w, Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w) ∧
          ∀ v, Computesι sig ι A v →
            FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality v
              (F ts.terms) := fun ts A hA => by
        obtain ⟨w₁, w₂, F₀, hw₁, hw₂, hF₁, hF₂, -⟩ := hA.fieldRel hκ
        refine ⟨⟨w₁, hw₁⟩, fun v hv => ?_⟩
        cases Computesι.det hd hw₂ hv
        rw [hFeq ts w₁ F₀ hw₁ hF₁]
        exact hF₂
      have hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u := fun ts us hts t u => by
        obtain ⟨ts', us', rfl, rfl, -⟩ := hT₁.to_eqSubst hd
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
          _ _ hts
        have huu := hSp.trans (hSp.symm hts) hts
        obtain ⟨⟨w', hw'⟩, -⟩ := hres us' _ (hBB us' us' huu)
        rw [hFeq us' w' _ hw' ((hres ts' _ (hBB ts' us' hts)).2 w' hw')]
      -- Equal abstractions for the destructor have equal instances at equal arguments.
      have hcond : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ τ₁ τ₂,
          EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁)) :=
        fun f₁ f₂ hf τ₁ τ₂ hτ => by
          obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
            ⟨_, Subst.args_toSubst ps τ₁⟩
          obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
            ⟨_, Subst.args_toSubst ps τ₂⟩
          have hts := (hT ts us).2 hτ
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨⟨w, hw⟩, hF⟩ := hres ts _ (hBB ts ts htt)
          exact (hF w hw).validEqTerm hd hw (hf _ _ hts)
      let G : Term 0 (Scope.extend [] ps.length) → ObsRel := fun f o₁ o₂ => ∃ S',
        DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁ f) S' ∧
          S' o₁ o₂
      have hGeq : ∀ f S', DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁ f) S' →
          G f = S' := fun f S' hS' =>
        funext fun o₁ => funext fun o₂ => propext
          ⟨fun ⟨_, h', hs⟩ => (DesRel.unique hd ih h' _ _ hS' o₁ o₂).1 hs, fun hs => ⟨S', hS', hs⟩⟩
      have hG : ∀ f, AbstractionRel SΘ F f f →
          DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) ds (Subst.snoc (e := .secondOrder ps ψ) θ₁ f) (G f) ∧
          DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) ds (Subst.snoc (e := .secondOrder ps ψ) θ₂ f) (G f) :=
          fun f hf => by
        obtain ⟨S', h₁, h₂⟩ := ValidEqDestructors₀.desRel hd Rf (hds f f (hcond f f hf))
        rw [hGeq f S' h₁]
        exact ⟨h₁, h₂⟩
      have hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂ :=
        fun f₁ f₂ hf o₁ o₂ => by
          have hEp := AbstractionRel.isPer hSp (fun ts hts =>
            have ⟨⟨w, hw⟩, hF⟩ := hres ts _ (hBB ts ts hts)
            FieldRel.isPer hd ih (hF w hw)) hBresp
          obtain ⟨S', h₁, h₂⟩ := ValidEqDestructors₀.desRel hd Rf (hds f₁ f₂ (hcond f₁ f₂ hf))
          have hf₂ := hEp.trans (hEp.symm hf) hf
          obtain ⟨S'', h₁', h₂'⟩ := ValidEqDestructors₀.desRel hd Rf (hds f₂ f₂ (hcond f₂ f₂ hf₂))
          rw [hGeq f₁ S' h₁, hGeq f₂ S'' h₁']
          exact DesRel.unique hd ih h₂ _ _ h₂' o₁ o₂
      have hr' : (rs 0).map Rf = none := by rw [hr]; rfl
      refine ⟨_, .cons hT₁ F (fun ts hts => (hres ts _ (hBB ts ts hts)).1)
        (fun ts hts => (hres ts _ (hBB ts ts hts)).2) hBresp G (fun f hf => (hG f hf).1) hresp hr',
        .cons hT₂ F (fun ts hts => ?_) (fun ts hts => (hres ts _ (hB _ _ ((hT ts ts).1 hts))).2)
          hBresp G (fun f hf => (hG f hf).2) hresp hr'⟩
      obtain ⟨w₁, w₂, -, -, hw₂, -⟩ := (hB _ _ ((hT ts ts).1 hts)).fieldRel hκ
      exact ⟨w₂, hw₂⟩
    · rename_i D hr
      obtain ⟨-, hds⟩ := h
      let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
      obtain ⟨G, h₀₁, h₀₂⟩ := ValidEqDestructors₀.desRel hd Rf (hds f₀ f₀)
      have hr' : (rs 0).map Rf = some (Rf D) := by rw [hr]; rfl
      refine ⟨_, .recursive hr' hT₁ G fun f => ?_, .recursive hr' hT₂ G fun f => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := ValidEqDestructors₀.desRel hd Rf (hds f f₀)
        have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
          (DesRel.unique hd ih h₂ _ _ h₀₂ o₁ o₂)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := ValidEqDestructors₀.desRel hd Rf (hds f₀ f)
        have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
          (DesRel.unique hd ih h₁ _ _ h₀₁ o₁ o₂)
        exact hSG ▸ h₂

-- ADE: none.
/-- At equal closed arguments of the parameters of a meaningful type declaration, the destructors of
each of its codata types, at relations `Rf D` of its recursive destructors of the type `D`, are
destructors of the graph of its sort at the two arguments with one equality `S Rf T` of the
abstractions for them, defined from the graph rather than chosen, since the graph gives one at
most. -/
theorem ValidTypeDeclaration.destructorsRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ∃ S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
      ∀ Rf, ∀ T ∈ decl.codataTypes,
        DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₁.toSubst (S Rf T) ∧
        DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₂.toSubst (S Rf T) := by
  have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
    fun i => Level.ofNat_closedValue _
  have has' := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hn := Level.closedValue_subst_equiv hls (decl.sort (.ofLists qs ps hq hp)).level
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel :=
    fun Rf T o₁ o₂ => ∃ S',
      DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
        (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
        ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₁.toSubst S' ∧ S' o₁ o₂
  refine ⟨S, fun Rf T hT => ?_⟩
  obtain ⟨S', h₁, h₂⟩ :=
    ((hv.destructors _ hadm hT fun i => (ls.getFin hl i).closedValue).2 _ _ has').desRel hd Rf
  have hds := Destructors.substLevels_levelEquiv hls (T.body (.ofLists qs ps hq hp))
  have h₁' : DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
      ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₁.toSubst S' := by
    rw [← hn]
    exact DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₁ hds (Subst.LevelEquiv.refl _)
  have h₂' : DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
      ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₂.toSubst S' := by
    rw [← hn]
    exact DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₂ hds (Subst.LevelEquiv.refl _)
  have hS : S Rf T = S' := funext fun o₁ => funext fun o₂ => propext
    ⟨fun ⟨_, h', hs⟩ => (DesRel.unique hd ih h' _ _ h₁' o₁ o₂).1 hs, fun hs => ⟨S', h₁', hs⟩⟩
  rw [hS]
  exact ⟨h₁', h₂'⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of codata types in a universe, at equal closed
arguments of its parameters, are types of the graph of its sort whose equality is `(eq_ν)`, at the
equality `S` of the destructors that the graph gives, which grows with the relations of the
recursive destructors. -/
theorem ValidTypeDeclaration.codataUnivRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
      (∀ X, ∀ T ∈ decl.codataTypes,
        DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) .type
          (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₁.toSubst (S X T)) ∧
      (∀ T ∈ decl.codataTypes,
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (CodataType.blockRel decl.codataTypes S T.name) ∧
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (CodataType.blockRel decl.codataTypes S T.name)) := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.destructorsRel hd hv hq hl hp hadm has
  let S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel :=
    fun X => S₀ fun D => (X D).computed sig ι
  refine ⟨S, fun X T hT => hs ▸ (hS₀ _ T hT).1, fun T hT =>
    ⟨.codata ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' => hs ▸ (hS₀ _ T' hT').1,
      .codata ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' => hs ▸ (hS₀ _ T' hT').2⟩⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of codata types in a universe of propositions,
at equal closed arguments of its parameters, are propositions of the graph of its sort whose truth
is `(true_ν)`, at the equality `S` of the destructors that the graph gives, which grows with the
truths of the recursive destructors. -/
theorem ValidTypeDeclaration.codataPropRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop) :
    ∃ S : (Name → Prop) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
      (∀ B, ∀ T ∈ decl.codataTypes,
        DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) .prop
          (fun i => ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => fun _ _ => B D')
          ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as₁.toSubst (S B T)) ∧
      (∀ T ∈ decl.codataTypes,
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (CodataType.blockTruth decl.codataTypes S T.name) ∧
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (CodataType.blockTruth decl.codataTypes S T.name)) := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.destructorsRel hd hv hq hl hp hadm has
  let S : (Name → Prop) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel :=
    fun B => S₀ fun D _ _ => B D
  refine ⟨S, fun B T hT => hs ▸ (hS₀ _ T hT).1, fun T hT =>
    ⟨.codata ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' => hs ▸ (hS₀ _ T' hT').1,
      .codata ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' => hs ▸ (hS₀ _ T' hT').2⟩⟩

/-! ## Instances and Constructors

An instance of a codata type is a term of its sort, as `(D)` gives it, whose destructors are those
of the graph of its sort at equal arguments, and the rules of the instances and of the constructors
of the declared types keep the meaning. -/

-- ADE: none.
/-- `(D)`, closed, for a codata type: two instances of a codata type of `Σ`, whose type declaration
is meaningful, at the same levels and at equal arguments of its parameters, are equal terms of its
sort: the destructors of the types of its block at the two arguments are destructors of the graph
of the sort with the same equality of the abstractions for them. -/
theorem ValidEqTerm₀.instCodata (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := by
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : ∀ as : InstanceArgs 0 [] decl.scope,
      Computesι sig ι (.inst T.name qs ls ps as) (.inst T.name qs ls ps as) :=
    fun as => ⟨.refl _, .inst _ _ _ _ as⟩
  show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
    (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · obtain ⟨S, -, hU⟩ := hv.codataUnivRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofUniv hd (hw as₁) (hw as₂) (levelRel_univ_iff.2 (hU T hT).1)
      (levelRel_univ_iff.2 (hU T hT).2)
  · obtain ⟨S, -, hP⟩ := hv.codataPropRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofProp hd (hw as₁) (hw as₂) (levelRel_prop_iff.2 (hP T hT).1)
      (levelRel_prop_iff.2 (hP T hT).2)

-- ADE: none.
/-- `(D_≡)` keeps the meaning, and `(D)` with it: equal arguments give, at equal substitutions of the
context, equal arguments of the parameters, hence equal instances, and the second instance at levels
of the same values is the same term up to its levels. -/
theorem ValidEqTermΓ.inst {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length}
    (h : sigT.HasDeclaredType D decl ζ) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
    ValidEqTermΓ sig ι ctx (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁))) := by
  have hd := has.1.distinct
  have hc : ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι (.inst D qs ls₁ ps (as₁.subst σ₁)) (.inst D qs ls₁ ps (as₂.subst σ₂))
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁))) :=
    fun σ₁ σ₂ hσ => match h with
      | ⟨hm, .inl ⟨_, hT, hn, _⟩⟩ =>
        have ⟨h', hv⟩ := hent.hasDataType ⟨hm, hT, hn⟩
        ValidEqTerm₀.inst hd h' hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)
      | ⟨hm, .inr ⟨_, hT, hn, _⟩⟩ =>
        have ⟨h', hv⟩ := hent.hasCodataType ⟨hm, hT, hn⟩
        ValidEqTerm₀.instCodata hd h' hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)
  refine ⟨⟨has.1, fun σ₁ σ₂ hσ => (hc σ₁ σ₂ hσ).1⟩, fun σ₁ σ₂ hσ => ?_⟩
  exact (hc σ₁ σ₂ hσ).levelEquiv (Term.LevelEquiv.refl _)
    (.inst D qs ps (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _))
    (Term.LevelEquiv.refl _)

-- ADE: none.
/-- `(c_≡)` keeps the meaning, and `(c)` with it: equal arguments of the instance and of the fields
give, at equal substitutions of the context, equal arguments of the parameters and equal arguments
of the fields at the first ones, hence equal constructors, and the second constructor at levels of
the same values is the same term up to its levels. -/
theorem ValidEqTermΓ.ctor {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) (hc : con ∈ T.constructors) {qs : List Quality}
    {ls₁ ls₂ : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl₁ : ls₁.length = decl.levels) (hl₂ : ls₂.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
    {ts us : Args 0 Γ (con.params (.ofLists qs ps hq hp))}
    (hts : ValidEqArgsΓ sig ι ctx ts us (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)) :
    ValidEqTermΓ sig ι ctx (.ctor D qs ls₁ ps as₁ con.name ts.terms)
      (.ctor D qs ls₂ ps as₂ con.name us.terms) (.inst D qs ls₁ ps as₁) := by
  obtain ⟨h', hv⟩ := hent.hasDataType h
  have hd := has.1.distinct
  have hI : ValidEqTermΓ sig ι ctx (.inst D qs ls₁ ps as₁) (.inst D qs ls₁ ps as₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls₁.getFin hl₁)⟩) :=
    ValidEqTermΓ.inst hent h.hasDeclaredType hq hl₁ hl₁ hp hadm has fun _ => Level.equivalence.refl _
  have hA : ValidTypeΓ sig ι ctx (.inst D qs ls₁ ps as₁) := by
    cases hs : (decl.sort (.ofLists qs ps hq hp)).quality <;> rw [hs] at hI
    · exact hI.univType.left
    · exact hI.propType.left
  refine ⟨hA, fun σ₁ σ₂ hσ => ?_⟩
  have hc' := ValidEqTerm₀.ctor hd h' hv hc hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)
    (ts := ts.subst σ₁) (us := us.subst σ₂)
    (by rw [← Constructor.fieldsAt_subst]; exact hts.2 σ₁ σ₂ hσ)
  rw [Args.terms_subst, Args.terms_subst] at hc'
  exact hc'.levelEquiv (Term.LevelEquiv.refl _)
    (.ctor D qs ps con.name (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _)
      (Terms.LevelEquiv.refl _))
    (Term.LevelEquiv.refl _)

/-! ## Entries of the Signature -/

/-- A judgment in the empty context is its closed judgment, at the substitution of no variable. -/
theorem ValidEqTermΓ.empty {t u A : Term 0 []} (h : ValidEqTermΓ sig ι .empty t u A) :
    ValidEqTerm₀ sig ι t u A := by
  have h' := h.2 (fun x => nomatch x) (fun x => nomatch x) ((EqSubst.empty_iff _ _).2 trivial)
  rwa [Term.subst_empty, Term.subst_empty, Term.subst_empty] at h'

-- ADE: the case of a definition of `defn-valid`, in `Definition/LogicalRelation/Fundamental.agda`.
/-- `(def)` keeps the meaning: a body that is a term of the type in the empty context, at each
instance of the sort and grade variables and each value of the level variables, makes the definition
meaningful; the meaning ignores the mode and the ownership. -/
theorem ValidConstantDefinition.intro {d : ConstantDefinition}
    (ht : ∀ inst, ValidTerm sig ι .empty (d.body inst) (d.type inst)) :
    ValidConstantDefinition sig ι d :=
  ValidConstantDefinition.iff.2 fun inst ρ => (ht inst ρ).empty

end

end Sic.Core
