module

public import Sic.Core.Soundness.Levels
public import Sic.Core.Soundness.Signature
public import Sic.Core.Typing
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Substitution

/-!
# Soundness of the Rules

Each rule of annex 14 of RFC 36 keeps the meaning of annex 17: when its premises are meaningful, in
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


/-! ## Declared Types

An instance of a declared type is a type of the sort of its declaration, whose fields are those of
its declaration at its levels and its arguments: the meaning of the declaration makes them closed
telescopes equal in this sort for equal arguments, which the graph of the sort gives the same
equality of their terms, so that equal arguments give instances with the same equality of their
canonical terms, or the same truth.

The equality of the terms of the rest of a telescope is the one that the graph gives it at each
term of its first type: it is defined from the graph, as the relation that some equality of the
terms of the rest relates, rather than chosen among them, since the graph gives one at most.
The instance at levels of the same values then follows as for the constants. -/

/-- The type of the first field of two closed telescopes equal in the sort `κ`, as `(⊨tel_κ,)` gives
it, computes to a type of a sort that `κ` bounds, whose terms are equal by `F`, and so does the
other type, with the same `F`: the terms that `F` relates are equal terms of the type. -/
theorem ValidEqTerm₀.fieldRel {A₁ A₂ : Term 0 []} {κ₁ κ : Universe 0} (hκ : κ₁ ≼ κ)
    (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) :
    ∃ w₁ w₂ F, Computesι sig ι A₁ w₁ ∧ Computesι sig ι A₂ w₂ ∧
      FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w₁ F ∧
      FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w₂ F ∧
      ∀ a₁ a₂, F a₁ a₂ → ValidEqTerm₀ sig ι a₁ a₂ A₁ := by
  obtain ⟨s₁, l₁⟩ := κ₁
  have hd := h.1.1
  have hm : l₁.closedValue ≤ κ.level.closedValue := hκ.2 Fin.elim0
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ n hn =>
    cases levelRel_univ_iff.1 hn with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      subst hl
      obtain ⟨R', h₁, h₂⟩ := hvw
      have hs : κ.quality = .type := by
        have := hκ.1
        cases hq : κ.quality with
        | type => rfl
        | prop => exact nomatch this hq
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).univ w R' →
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w
            (R'.computed sig ι) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .univBelow hs _ hlt hw
        · exact .univ hs (heq ▸ levelRel_univ_iff.1 hw)
      refine ⟨w₁, w₂, R'.computed sig ι, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ ⟨v, w, ha₁, ha₂, hR'⟩ => ⟨(ValidEqTerm₀.univType h).left, fun _ =>
          ⟨w₁, v, w, R', hw₁, ha₁, ha₂, .univ _ h₁, hR'⟩, fun ⟨v', hv', hP⟩ => ?_⟩⟩
      cases Computesι.det hd hw₁ hv'
      obtain ⟨_, _, hP⟩ := hP
      exact (HasEq.univ_not_prop hd h₁ hP).elim
    | prop hl _ =>
      subst hl
      obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := hvw
      cases propext hb
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).prop w b₁ →
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w
            (fun _ _ => b₁) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .propBelow _ hlt hw
        · exact .prop (heq ▸ levelRel_prop_iff.1 hw)
      refine ⟨w₁, w₂, fun _ _ => b₁, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ hb₁ => ⟨(ValidEqTerm₀.propType h).left, fun hn => absurd ⟨w₁, hw₁, _, _, h₁⟩ hn,
          fun _ => ⟨w₁, fun _ _ => b₁, hw₁, .prop _ b₁ h₁ fun _ _ => .rfl, hb₁⟩⟩⟩

/-- Two closed telescopes equal in the sort `κ` are equal fields without recursive fields. -/
theorem ValidEqTelescope₀.toFields {κ : Universe 0} (inst₁ inst₂ : Name → Term 0 []) :
    {ps : List Parameter} → {Θ₁ Θ₂ : Telescope 0 [] ps} → ValidEqTelescope₀ sig ι κ Θ₁ Θ₂ →
      ValidEqFields₀ sig ι κ inst₁ inst₂ (fun _ => none) Θ₁ Θ₂
  | [], .nil, .nil, h => h
  | _ :: _, .cons _ _ _ _, .cons _ _ _ _, h => by
    rw [ValidEqTelescope₀] at h
    rw [ValidEqFields₀]
    exact ⟨h.1, fun v₁ v₂ hv => ValidEqTelescope₀.toFields inst₁ inst₂ (h.2 v₁ v₂ hv)⟩

/-- Two closed fields equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, whatever the relations `Rf D` of their recursive fields of
the type `D`, in a signature whose names are distinct: the equality of the rest after a recursive
field, on which it does not depend, is the one at any term. -/
theorem ValidEqFields₀.telRel (hd : sig.Distinct) {κ : Universe 0} {inst₁ inst₂ : Name → Term 0 []}
    (Rf : Name → TermRel) :
    {ps : List Parameter} → {rs : Nat → Option Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ inst₁ inst₂ rs Θ₁ Θ₂ →
      ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) Θ₁ S ∧
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) Θ₂ S
  | [], _, .nil, .nil, _ => ⟨FieldsRel.nil, .nil, .nil⟩
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂, h => by
    have ih : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    rw [ValidEqFields₀] at h
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
      obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ
      have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ ha => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂ (hFv a₁ a₂ ha))
      let G : Term 0 [] → FieldsRel := fun a ts us => ∃ S,
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S ∧ S ts us
      have hG : ∀ a S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S → G a = S :=
        fun a S hS => funext fun ts => funext fun us => propext
          ⟨fun ⟨_, hS', hs⟩ => (TelRel.unique hd ih hS' _ _ hS ts us).1 hs, fun hs => ⟨S, hS, hs⟩⟩
      have hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us := fun a₁ a₂ ha ts us => by
        have hFp := FieldRel.isPer hd ih hF₁
        obtain ⟨S, h₁, h₂⟩ := hcommon a₁ a₂ ha
        obtain ⟨S', h₁', h₂'⟩ := hcommon a₂ a₂ (hFp.trans (hFp.symm ha) ha)
        rw [hG a₁ S h₁, hG a₂ S' h₁']
        exact TelRel.unique hd ih h₂ _ _ h₂' ts us
      have hr' : (rs 0).map Rf = none := by rw [hr]; rfl
      refine ⟨FieldsRel.cons F G, .cons hc₁ hF₁ G (fun a ha => ?_) hresp hr',
        .cons hc₂ hF₂ G (fun a ha => ?_) hresp hr'⟩
      · obtain ⟨S, h₁, -⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₂
    · rename_i D hr
      obtain ⟨-, -, hΘ⟩ := h
      let a₀ : Term 0 [] := .sort ⟨.type, .zero⟩
      have hcommon : ∀ a₁ a₂, ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂)
      obtain ⟨G, h₀₁, h₀₂⟩ := hcommon a₀ a₀
      have hr' : (rs 0).map Rf = some (Rf D) := by rw [hr]; rfl
      refine ⟨FieldsRel.cons (Rf D) fun _ => G, .recursive hr' G fun a => ?_,
        .recursive hr' G fun a => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a₀
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₂ _ _ h₀₂ ts us)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a₀ a
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₁ _ _ h₀₁ ts us)
        exact hSG ▸ h₂

/-- Two closed telescopes equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.telRel (hd : sig.Distinct) {κ : Universe 0} {ps : List Parameter}
    {Θ₁ Θ₂ : Telescope 0 [] ps} (h : ValidEqTelescope₀ sig ι κ Θ₁ Θ₂) :
    ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => none)
        Θ₁ S ∧
      TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => none)
        Θ₂ S :=
  ValidEqFields₀.telRel hd (fun _ _ _ => False) (h.toFields (fun _ => .sort ⟨.type, .zero⟩)
    (fun _ => .sort ⟨.type, .zero⟩))

-- ADE: none.
/-- The recursive fields of a closed telescope, at the positions where `rs` gives a type `D` of the
block, are the instances `inst D`, the rest being so at every term of each field. -/
def Telescope.RecHeads (sig : Signature) (ι : Interpretation) (inst : Name → Term 0 []) :
    {ps : List Parameter} → (Nat → Option Name) → Telescope 0 [] ps → Prop
  | [], _, .nil => True
  | _ :: _, rs, .cons _ _ A Θ => (∀ D, rs 0 = some D → A = inst D) ∧
    ∀ a, ValidEqTerm₀ sig ι a a A →
      Telescope.RecHeads sig ι inst (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a))

/-- A telescope without recursive fields has their instances everywhere. -/
theorem Telescope.recHeads_none (inst : Name → Term 0 []) :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → Θ.RecHeads sig ι inst (fun _ => none)
  | [], .nil => trivial
  | _ :: _, .cons _ _ _ _ => by
    rw [Telescope.RecHeads]
    exact ⟨fun _ h => (by cases h), fun _ _ => Telescope.recHeads_none inst _⟩

/-- The first of two equal closed fields has the instances `inst₁` at its recursive fields. -/
theorem ValidEqFields₀.recHeads {κ : Universe 0} {inst₁ inst₂ : Name → Term 0 []} :
    {ps : List Parameter} → {rs : Nat → Option Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ inst₁ inst₂ rs Θ₁ Θ₂ → Θ₁.RecHeads sig ι inst₁ rs
  | [], _, .nil, .nil, _ => trivial
  | _ :: _, rs, .cons _ _ _ _, .cons _ _ _ _, h => by
    rw [ValidEqFields₀] at h
    rw [Telescope.RecHeads]
    split at h
    · rename_i hr
      refine ⟨fun D hD => ?_, fun a ha => ValidEqFields₀.recHeads (h.2 a a ha)⟩
      rw [hr] at hD
      cases hD
    · rename_i D hr
      refine ⟨fun D' hD' => ?_, fun a _ => ValidEqFields₀.recHeads (h.2.2 a a)⟩
      rw [hr] at hD'
      cases hD'
      exact h.1

/-- Equal closed terms of a type that computes to a type of a field, whose terms are equal by `F`,
are related by `F`: the converse of the last property of `ValidEqTerm₀.fieldRel`. -/
theorem FieldRel.of_validEqTerm {n : Nat} {s : Quality} {A v t u : Term 0 []} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F) (hA : Computesι sig ι A v)
    (h : ValidEqTerm₀ sig ι t u A) : F t u := by
  have hd := h.1.1
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u := fun m R hR => by
    have hnp : ¬ ComputesToProp sig ι A := fun ⟨v', hv', _, _, hP⟩ => by
      cases Computesι.det hd hA hv'
      exact HasEq.univ_not_prop hd hR hP
    obtain ⟨v', w₁, w₂, R', hv', ht, hu, hR', hw⟩ := h.2.1 hnp
    cases Computesι.det hd hA hv'
    exact ⟨w₁, w₂, ht, hu, (HasEq.unique hd hR' (.univ m hR) w₁ w₂).1 hw⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b := fun m b hb => by
    obtain ⟨v', R', hv', hR', hR⟩ := h.2.2 ⟨v, hA, m, b, hb⟩
    cases Computesι.det hd hA hv'
    exact (HasEq.unique hd hR' (.prop m b hb fun _ _ => .rfl) t u).1 hR
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU)
  | univBelow _ m _ hU => exact huniv m _ hU
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP)
  | propBelow m _ hP => exact hprop m _ hP

/-- Equal closed arguments of a closed telescope of the graph of a sort, whose fields have the
equality `S`, have terms related by `S`: the converse of `ValidEqTelescope₀.telRel`, for the
arguments. -/
theorem TelRel.of_eqSubst {n : Nat} {s : Quality} {inst : Name → Term 0 []} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} → {rs : Nat → Option Name} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → Θ.RecHeads sig ι inst rs →
      (∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
        ∀ t u, ValidEqTerm₀ sig ι t u (inst D) → R t u) →
      (ts us : Args 0 [] ps) →
      EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst → S ts.terms us.terms
  | [], .nil, _, _, _, .nil, _, _, .nil, .nil, _ => trivial
  | _ :: ps, .cons q p A Θ, _, _, _, h', hH, hR, .cons t ts, .cons u us, h => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    have hd : sig.Distinct := ht.1.1
    have htt := ht.trans ht.symm
    cases h' with
    | cons hA hF G hG _ _ =>
      have hFtu := hF.of_validEqTerm hA ht
      have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
      exact ⟨hFtu, TelRel.of_eqSubst (hG t (hFp.trans hFtu (hFp.symm hFtu))) (hH.2 t htt)
        (fun i R h => hR (i + 1) R h) ts us hts⟩
    | recursive hrs G hG =>
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      exact ⟨hRD t u (hH.1 D hD ▸ ht), TelRel.of_eqSubst (hG t) (hH.2 t htt)
        (fun i R h => hR (i + 1) R h) ts us hts⟩

/-- Two equal closed terms of the type of a field, whose terms are equal by `F`, are related by `F`:
the converse of `FieldRel.of_validEqTerm`. -/
theorem FieldRel.validEqTerm (hd : sig.Distinct) {n : Nat} {s : Quality} {A v t u : Term 0 []}
    {F : TermRel} (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F)
    (hA : Computesι sig ι A v) (htu : F t u) : ValidEqTerm₀ sig ι t u A := by
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u →
      ValidEqTerm₀ sig ι t u A := fun m R hR ⟨w₁, w₂, h₁, h₂, hw⟩ =>
    ⟨⟨hd, v, v, R, hA, hA, .univ m hR, .univ m hR⟩, fun _ => ⟨v, w₁, w₂, R, hA, h₁, h₂, .univ m hR, hw⟩,
      fun ⟨v', hv', _, _, hP⟩ => by
        cases Computesι.det hd hA hv'
        exact (HasEq.univ_not_prop hd hR hP).elim⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b → ValidEqTerm₀ sig ι t u A :=
    fun m b hP hb =>
      ⟨⟨hd, v, v, fun _ _ => b, hA, hA, .prop m b hP fun _ _ => .rfl,
        .prop m b hP fun _ _ => .rfl⟩, fun hn => absurd ⟨v, hA, m, b, hP⟩ hn,
        fun _ => ⟨v, fun _ _ => b, hA, .prop m b hP fun _ _ => .rfl, hb⟩⟩
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU) htu
  | univBelow _ m _ hU => exact huniv m _ hU htu
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP) htu
  | propBelow m _ hP => exact hprop m _ hP htu

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are the terms of equal arguments of the telescope: the converse of
`TelRel.of_eqSubst`. -/
theorem TelRel.to_eqSubst (hd : sig.Distinct) {n : Nat} {s : Quality} {inst : Name → Term 0 []} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} → {rs : Nat → Option Name} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → Θ.RecHeads sig ι inst rs →
      (∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
        ∀ t u, R t u → ValidEqTerm₀ sig ι t u (inst D)) →
      (ts us : Terms 0 []) → S ts us →
        ∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append Θ) ts'.toSubst us'.toSubst
  | [], .nil, _, _, _, .nil, _, _, .nil, .nil, _ =>
    ⟨.nil, .nil, rfl, rfl, (EqSubst.empty_iff _ _).2 trivial⟩
  | [], .nil, _, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, _, _, h', hH, hR, ts₀, us₀, hS => by
    have key : ∀ t u (ts us : Terms 0 []) (htu : ValidEqTerm₀ sig ι t u A),
        (∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append (Θ.subst₀ (Subst₀.single t))) ts'.toSubst
            us'.toSubst) →
        ∃ ts' us' : Args 0 [] (_ :: ps), ts'.terms = .cons t ts ∧ us'.terms = .cons u us ∧
          EqSubst sig ι (Context.empty.append (.cons q p A Θ)) ts'.toSubst us'.toSubst := by
      intro t u ts us htu ⟨ts', us', h₁, h₂, hτ⟩
      subst h₁ h₂
      exact ⟨.cons t ts', .cons u us', rfl, rfl, EqSubst.args_cons_iff.2 ⟨htu, hτ⟩⟩
    cases h' with
    | cons hA hF G hG _ _ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
        have hv := hF.validEqTerm hd hA htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t (hFp.trans htu (hFp.symm htu)))
          (hH.2 t (hv.trans hv.symm)) (fun i R h => hR (i + 1) R h) ts us hts)
    | recursive hrs G hG =>
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hv : ValidEqTerm₀ sig ι t u A := hH.1 D hD ▸ hRD t u htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t) (hH.2 t (hv.trans hv.symm))
          (fun i R h => hR (i + 1) R h) ts us hts)

/-- The terms `ts₁` and `ts₂` of fields are related by `Q D` at each recursive field of the type `D`
that the types `rs` of the block mark. -/
def Terms.RecRel (Q : Name → TermRel) : List (Option Name) → Terms 0 [] → Terms 0 [] → Prop
  | some D :: rs, .cons t₁ ts₁, .cons t₂ ts₂ => Q D t₁ t₂ ∧ Terms.RecRel Q rs ts₁ ts₂
  | none :: rs, .cons _ ts₁, .cons _ ts₂ => Terms.RecRel Q rs ts₁ ts₂
  | [], _, _ | _ :: _, .nil, _ | _ :: _, .cons _ _, .nil => True

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are related at its recursive fields, which `rs` marks, by the relations `Rf` that the
graph gives them. -/
theorem TelRel.recRel (hd : sig.Distinct) {n : Nat} {s : Quality} {Rf : Name → TermRel} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → (rs : List (Option Name)) →
      (∀ i, rs' i = (rs[i]?.join).map Rf) → (ts us : Terms 0 []) → S ts us →
        Terms.RecRel Rf rs ts us
  | [], .nil, _, _, .nil, rs, _, .nil, .nil, _ => by
    cases rs with
    | nil => trivial
    | cons o _ => cases o <;> trivial
  | [], .nil, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, rs', h', rs, hrs, ts₀, us₀, hS => by
    have htail : ∀ i, rs' (i + 1) = (rs.tail[i]?.join).map Rf := fun i => by
      rw [hrs (i + 1)]
      cases rs <;> rfl
    cases h' with
    | cons hA hF G hG _ hrs₀ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
        have ih := TelRel.recRel hd (hG t (hFp.trans htu (hFp.symm htu))) rs.tail htail ts us hts
        match rs, hrs with
        | [], _ => trivial
        | none :: _, _ => exact ih
        | some _ :: _, hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
    | recursive hrs₀ G hG =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have ih := TelRel.recRel hd (hG t) rs.tail htail ts us hts
        match rs, hrs with
        | [], hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
        | none :: _, hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
        | some D :: _, hrs =>
          have hR := (hrs 0).symm.trans hrs₀
          simp only [List.getElem?_cons_zero, Option.join_some, Option.map_some,
            Option.some.injEq] at hR
          exact ⟨hR ▸ htu, ih⟩

/-- Arguments related by the equality of the fields of a closed telescope of the graph of a sort are
equal arguments of the telescope, and conversely, when its recursive fields are instances whose
equality is the relation of these fields. -/
theorem TelRel.eqSubst_iff (hd : sig.Distinct) {n : Nat} {s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S : FieldsRel} {rs' : Nat → Option TermRel}
    {rs : Nat → Option Name} {inst : Name → Term 0 []}
    (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S) (hH : Θ.RecHeads sig ι inst rs)
    (hR : ∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
      ∀ t u, R t u ↔ ValidEqTerm₀ sig ι t u (inst D))
    (ts us : Args 0 [] ps) :
    S ts.terms us.terms ↔ EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst :=
  ⟨fun hS => by
    obtain ⟨ts', us', h₁, h₂, hτ⟩ := h.to_eqSubst hd hH (fun i R hi =>
      have ⟨D, hD, hRD⟩ := hR i R hi
      ⟨D, hD, fun t u => (hRD t u).1⟩) _ _ hS
    rw [Args.terms_inj h₁, Args.terms_inj h₂] at hτ
    exact hτ,
  fun hτ => h.of_eqSubst hH (fun i R hi =>
    have ⟨D, hD, hRD⟩ := hR i R hi
    ⟨D, hD, fun t u => (hRD t u).2⟩) ts us hτ⟩

/-- Two closed terms that compute to types of `U_l` with the same equality of their terms are equal
terms of `U_l`, in a signature whose names are distinct. -/
theorem ValidEqTerm₀.ofUniv (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {R : TermRel}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).univ v R) (hw : (levelRel sig ι l.closedValue).univ w R) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.type, l⟩) := by
  have hU : HasEq sig ι (.sort ⟨.type, l⟩)
      (fun A B => ∃ R, (levelRel sig ι l.closedValue).univ A R ∧
        (levelRel sig ι l.closedValue).univ B R) :=
    .univ (l.closedValue + 1) (levelRel_univ_iff.2 (.univ rfl rfl))
  exact ⟨⟨hd, _, _, _, Computes.sort _ _, Computes.sort _ _, hU, hU⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, ht, hu, hU, R, hv, hw⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

/-- Two closed terms that compute to propositions of `Ω_l` with the same truth are equal terms of
`Ω_l`, in a signature whose names are distinct. -/
theorem ValidEqTerm₀.ofProp (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {b : Prop}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).prop v b) (hw : (levelRel sig ι l.closedValue).prop w b) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.prop, l⟩) := by
  have hU : HasEq sig ι (.sort ⟨.prop, l⟩)
      (fun P Q => ∃ b₁ b₂, (levelRel sig ι l.closedValue).prop P b₁ ∧
        (levelRel sig ι l.closedValue).prop Q b₂ ∧ (b₁ ↔ b₂)) :=
    .univ (l.closedValue + 1) (levelRel_univ_iff.2 (.prop rfl rfl))
  exact ⟨⟨hd, _, _, _, Computes.sort _ _, Computes.sort _ _, hU, hU⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, ht, hu, hU, b, b, hv, hw, .rfl⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

-- ADE: none.
/-- The instance of a type of a block at the parameters themselves, at the values of the levels
`ls`, substituted by the arguments `ā`, is the instance of the type at `ls` and `ā`, up to the
levels. -/
theorem TypeDeclaration.blockInstance_atLevels_subst (decl : TypeDeclaration) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 [] decl.scope) (D : Name) :
    Term.LevelEquiv (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst) (.inst D qs ls ps as) := by
  show Term.LevelEquiv (.inst D (List.ofFn (qs.getFin hq))
    ((List.ofFn Level.var).map (Level.subst fun i => Level.ofNat (ls.getFin hl i).closedValue))
    (List.ofFn (ps.getFin hp))
    (((InstanceArgs.identity decl.scope).substLevels
      fun i => Level.ofNat (ls.getFin hl i).closedValue).subst as.toSubst)) _
  rw [List.ofFn_getFin, List.ofFn_getFin, InstanceArgs.identity_substLevels,
    InstanceArgs.identity_subst_toSubst]
  exact .inst D qs ps (Level.ListEquiv.of_getFin (by simp) hl fun i => by
      simp only [List.getFin, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Fin.val_cast,
        Level.subst]
      exact Level.ofNat_closedValue _) (InstanceArgs.LevelEquiv.refl as)

-- ADE: none.
/-- At equal closed arguments of the parameters of a meaningful type declaration, the fields of each
constructor of one of its types, at relations `Rf D` of its recursive fields of the type `D`, are
telescopes of the graph of its sort with one equality `S Rf c` of their terms, defined from the graph
rather than chosen, since the graph gives one at most; when the relations `Rf D` are the equalities
of the instances of the types of the block, at the first arguments, the equality relates the terms
of equal arguments of the fields, and only them. -/
theorem ValidTypeDeclaration.fieldsRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      ∀ Rf, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S Rf c) ∧
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S Rf c) ∧
        ((∀ D ∈ decl.names, ∀ t u, Rf D t u ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁)) →
          (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            S Rf c ts.terms us.terms ↔ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
          ∀ fs₁ fs₂, S Rf c fs₁ fs₂ → ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            ts.terms = fs₁ ∧ us.terms = fs₂ ∧ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) := by
  have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
    fun i => Level.ofNat_closedValue _
  have has' := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hn : (((decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue).level.closedValue)
      = ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue :=
    Level.subst_equiv hls _ Fin.elim0
  have hΘ : ∀ (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
      (as : InstanceArgs 0 [] decl.scope),
      Telescope.LevelEquiv (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) := fun _ _ =>
    (Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _)
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun Rf c ts us =>
    ∃ S', TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' ts us
  refine ⟨S, fun Rf T hT c hc => ?_⟩
  have hF := (hv.fields _ hadm hT hc fun i => (ls.getFin hl i).closedValue).2 _ _ has'
  obtain ⟨S', h₁, h₂⟩ := hF.telRel hd Rf
  have h₁' := hn ▸ TelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₁ (hΘ c as₁)
  have h₂' := hn ▸ TelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₂ (hΘ c as₂)
  have hS : S Rf c = S' := funext fun ts => funext fun us => propext
    ⟨fun ⟨_, h', hs⟩ => (TelRel.unique hd ih h' _ _ h₁' ts us).1 hs, fun hs => ⟨S', h₁', hs⟩⟩
  rw [hS]
  refine ⟨h₁', h₂', fun hRf => ?_⟩
  have hH := hF.recHeads
  have hinst : ∀ D t u, ValidEqTerm₀ sig ι t u (((decl.blockInstance (.ofLists qs ps hq hp) D
        (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
        as₁.toSubst) ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) := fun D t u =>
    have he := decl.blockInstance_atLevels_subst hq hl hp as₁ D
    ⟨fun h => h.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) he,
      fun h => h.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) he.symm⟩
  have hR : ∀ i R, ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf = some R →
      ∃ D, (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i = some D ∧
        ∀ t u, R t u ↔ ValidEqTerm₀ sig ι t u (((decl.blockInstance (.ofLists qs ps hq hp) D
          (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
          as₁.toSubst) := fun i R hi => by
    cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
    | none => rw [hr] at hi; cases hi
    | some D =>
      rw [hr] at hi
      cases hi
      exact ⟨D, rfl, fun t u =>
        (hRf D (Telescope.recursionAt_mem hr) t u).trans (hinst D t u).symm⟩
  have hE : ∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
      EqSubst sig ι (Context.empty.append (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as₁.toSubst)) ts.toSubst us.toSubst ↔
      EqSubst sig ι (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
        ts.toSubst us.toSubst := fun _ _ =>
    ⟨EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hΘ c as₁)),
      EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hΘ c as₁).symm)⟩
  refine ⟨fun ts us => (TelRel.eqSubst_iff hd h₁ hH hR ts us).trans (hE ts us),
    fun fs₁ fs₂ hs => ?_⟩
  obtain ⟨ts, us, rfl, rfl, hτ⟩ := TelRel.to_eqSubst hd h₁ hH (fun i R hi =>
    have ⟨D, hD, hRD⟩ := hR i R hi
    ⟨D, hD, fun t u => (hRD t u).1⟩) fs₁ fs₂ hs
  exact ⟨ts, us, rfl, rfl, (hE ts us).1 hτ⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe, at equal closed
arguments of its parameters, are types of the graph of its sort whose equality is `(eq_μ)`, at the
equality `S` of the fields that the graph gives, which grows with the relations of the recursive
fields; at the relations `(eq_μ)` of the recursive fields, `S` relates the terms of equal arguments
of the fields at the first arguments, and only them, and each of them to itself. -/
theorem ValidTypeDeclaration.univRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockRel decl.dataTypes S T.name) ∧
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockRel decl.dataTypes S T.name)) ∧
      (∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us) ∧
      (∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us →
        Terms.RecRel (fun D => (X D).computed sig ι)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockRel decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockRel decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun X => S₀ fun D => (X D).computed sig ι
  have hU : ∀ T ∈ decl.dataTypes,
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockRel decl.dataTypes S T.name) ∧
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockRel decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun X D => (X D).computed sig ι) (fun X T hT c hc => (hS₀ _ T hT c hc).1) X Y
      fun D _ _ => TermRel.computed_mono (hXY D)
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hF : ∀ T ∈ decl.dataTypes, FieldRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) .type (.inst T.name qs ls ps as₁)
      ((DataType.blockRel decl.dataTypes S T.name).computed sig ι) := fun T hT =>
    .univ rfl (hU T hT).1
  refine ⟨S, hU, hmono, fun X T hT c hc ts us h =>
    TelRel.recRel hd (hS₀ _ T hT c hc).1 _ (fun _ => rfl) ts us h, fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, ∀ t u,
      (DataType.blockRel decl.dataTypes S D).computed sig ι t u ↔
        ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) := fun D hD t u => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    exact ⟨fun h => (hF T' hT').validEqTerm hd (hI _) h,
      fun h => (hF T' hT').of_validEqTerm (hI _) h⟩
  obtain ⟨-, -, hiff⟩ := hS₀ (fun D => (DataType.blockRel decl.dataTypes S D).computed sig ι) T hT c hc
  obtain ⟨hof, hto⟩ := hiff hRf
  refine ⟨hof, hto, fun fs₁ fs₂ h => ?_⟩
  have hper : IsPer (S (DataType.blockRel decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i x hx => by
      cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D =>
        rw [hr] at hx
        cases hx
        obtain ⟨T', hT', rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.recursionAt_mem hr)
        exact FieldRel.isPer hd ih (hF T' hT')) (hS₀ _ T hT c hc).1
  exact hper.trans h (hper.symm h)

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe of propositions,
at equal closed arguments of its parameters, are propositions of the graph of its sort whose truth
is `(true_μ)`, at the equality `S` of the fields that the graph gives, which grows with the truths
of the recursive fields; at the truths `(true_μ)` of the recursive fields, `S` relates the terms of
equal arguments of the fields at the first arguments, and only them. -/
theorem ValidTypeDeclaration.propRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop) :
    ∃ S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockTruth decl.dataTypes S T.name) ∧
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockTruth decl.dataTypes S T.name)) ∧
      (∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us) ∧
      (∀ B, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us →
        Terms.RecRel (fun D _ _ => B D)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockTruth decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun B => S₀ fun D _ _ => B D
  have hP : ∀ T ∈ decl.dataTypes,
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockTruth decl.dataTypes S T.name) ∧
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockTruth decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us := fun B B' hB =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun B D (_ _ : Term 0 []) => B D) (fun B T hT c hc => (hS₀ _ T hT c hc).1) B B'
      fun D _ _ => hB D
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  refine ⟨S, hP, hmono, fun B T hT c hc ts us h =>
    TelRel.recRel hd (hS₀ _ T hT c hc).1 _ (fun _ => rfl) ts us h, fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, ∀ t u,
      DataType.blockTruth decl.dataTypes S D ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) :=
      fun D hD t u => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    have hF : FieldRel sig ι
        ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) .prop (.inst T'.name qs ls ps as₁)
        (fun _ _ => DataType.blockTruth decl.dataTypes S T'.name) := .prop (hP T' hT').1
    exact ⟨fun h => hF.validEqTerm hd (hI _) h, fun h => hF.of_validEqTerm (hI _) h⟩
  obtain ⟨hof, hto⟩ := (hS₀ (fun D _ _ => DataType.blockTruth decl.dataTypes S D) T hT c hc).2.2 hRf
  have hper : IsPer (S (DataType.blockTruth decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i x hx => by
      cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩) (hS₀ _ T hT c hc).1
  exact ⟨hof, hto, fun _ _ h => hper.trans h (hper.symm h)⟩

-- ADE: none.
/-- `(D)`, closed: two instances of a declared type of `Σ`, whose type declaration is meaningful, at
the same levels and at equal arguments of its parameters, are equal terms of its sort: the fields
of each constructor at the two arguments are telescopes of the graph of the sort with the same
equality of their terms. -/
theorem ValidEqTerm₀.inst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
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
  · obtain ⟨S, hU, -⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofUniv hd (hw as₁) (hw as₂) (levelRel_univ_iff.2 (hU T hT).1)
      (levelRel_univ_iff.2 (hU T hT).2)
  · obtain ⟨S, hP, -⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofProp hd (hw as₁) (hw as₂) (levelRel_prop_iff.2 (hP T hT).1)
      (levelRel_prop_iff.2 (hP T hT).2)

-- ADE: none.
/-- `(c)` and `(c_≡)`, closed: two applications of a constructor of a declared type of `Σ`, whose
type declaration is meaningful, at the same levels, at equal arguments of the parameters and at
equal arguments of its fields, are equal terms of the instance: canonical terms that `(eq_c)`
relates, or proofs of a proposition that the first one makes true. -/
theorem ValidEqTerm₀.ctor (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    {ts us : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
      ts.toSubst us.toSubst) :
    ValidEqTerm₀ sig ι (.ctor D qs ls ps as₁ con.name ts.terms)
      (.ctor D qs ls ps as₂ con.name us.terms) (.inst D qs ls ps as₁) := by
  have hI : ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩) :=
    ValidEqTerm₀.inst hd h hv hq hl hp hadm has
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : Computesι sig ι (.inst T.name qs ls ps as₁) (.inst T.name qs ls ps as₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  have hct : ∀ (as : InstanceArgs 0 [] decl.scope) (ts : Terms 0 []),
      Computesι sig ι (.ctor T.name qs ls ps as con.name ts)
        (.ctor T.name qs ls ps as con.name ts) :=
    fun _ _ => ⟨.refl _, .ctor _ _ _ _ _ _ _⟩
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · rw [hs] at hI
    obtain ⟨S, hU, hmono, hrec, hiff⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hrel : DataType.blockRel decl.dataTypes S T.name
        (.ctor T.name qs ls ps as₁ con.name ts.terms) (.ctor T.name qs ls ps as₂ con.name us.terms) :=
      DataType.blockRel_closed hmono hT ⟨con, hc, ts.terms, us.terms, ⟨qs, ls, ps, _, as₁, rfl⟩,
        ⟨qs, ls, ps, _, as₂, rfl⟩, ((hiff T hT con hc).1 ts us).2 hts⟩
    refine ⟨(ValidEqTerm₀.univType hI).left,
      fun _ => ⟨_, _, _, _, hw, hct _ _, hct _ _, .univ _ hU', hrel⟩, fun ⟨v, hv', _, _, hP⟩ => ?_⟩
    cases Computesι.det hd hw hv'
    exact (HasEq.univ_not_prop hd hU' hP).elim
  · rw [hs] at hI
    obtain ⟨S, hP, hmono, hrec, hiff⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      DataType.blockTruth_closed hmono hT ⟨con, hc, ts.terms,
        (hiff T hT con hc).2.2 _ _ (((hiff T hT con hc).1 ts us).2 hts)⟩
    refine ⟨(ValidEqTerm₀.propType hI).left, fun hn => absurd ⟨_, hw, _, _, hP'⟩ hn,
      fun _ => ⟨_, fun _ _ => DataType.blockTruth decl.dataTypes S T.name, hw,
        .prop _ _ hP' fun _ _ => .rfl, htrue⟩⟩

/-- The equality of the terms of an instance in a universe of a data type of `Σ` is `(eq_μ)`, at an
equality of the fields of the constructors of its block that the graph gives. -/
theorem HasEq.dataInst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {as : InstanceArgs 0 [] decl.scope}
    {R : TermRel} (hR : HasEq sig ι (.inst D qs ls ps as) R) :
    ∃ (n : Nat) (S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        FieldsRel),
      (∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) ∧
      ∀ t u, R t u ↔ DataType.blockRel decl.dataTypes S D t u := by
  cases hR with
  | univ n hU =>
    rw [levelRel_univ_iff] at hU
    cases hU with
    | data h' _ _ _ hv _ _ S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases has
      exact ⟨n, S, hS, fun _ _ => .rfl⟩
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim
  | prop n b hP _ =>
    rw [levelRel_prop_iff] at hP
    cases hP with
    | data h' _ _ _ hv hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

/-- A proposition that is an instance of a data type of `Σ` is an instance in a universe of
propositions. -/
theorem PropRel.dataInst_quality (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {n : Nat} {b : Prop}
    (hP : (levelRel sig ι n).prop (.inst D qs ls ps as) b) :
    (decl.sort (.ofLists qs ps hq hp)).quality = .prop := by
  rw [levelRel_prop_iff] at hP
  cases hP with
  | data h' _ _ _ hv hs' =>
    obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
    subst hD hqs hls hps
    obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
    exact hs'
  | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

-- ADE: none.
/-- Two equal terms of an instance in a universe of a data type of `Σ` whose constructors have no
recursive field compute to the same constructor of a type of the block, applied to equal arguments
of its fields: the canonical terms that `(eq_μ)` relates, which the equality of the instance, its
meaning as a type, gives. -/
theorem ValidEqTerm₀.ctor_inv {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hnr : ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors, ∀ i,
      (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i = none)
    {as : InstanceArgs 0 [] decl.scope} {t₁ t₂ : Term 0 []}
    (ht : ValidEqTerm₀ sig ι t₁ t₂ (.inst D qs ls ps as)) :
    ∃ T' ∈ decl.dataTypes, T'.name = D ∧ ∃ con ∈ T'.constructors,
      ∃ ts₁ ts₂ : Args 0 [] (con.params (.ofLists qs ps hq hp)),
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₁ (.ctor D qs' ls' ps' as' con.name ts₁.terms)) ∧
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₂ (.ctor D qs' ls' ps' as' con.name ts₂.terms)) ∧
        EqSubst sig ι
          (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
          ts₁.toSubst ts₂.toSubst := by
  obtain ⟨⟨hd, v, -, R, hv, -, hR, -⟩, hne, -⟩ := ht
  have hw : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  cases Computesι.det hd hw hv
  obtain ⟨n, S, hS, hiff⟩ := HasEq.dataInst hd h hq hl hp hs hR
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
      (F := fun X D => (X D).computed sig ι) hS X Y fun D _ _ => TermRel.computed_mono (hXY D)
  obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := hne fun ⟨v', hv', _, _, hP⟩ => by
    cases Computesι.det hd hw hv'
    exact nomatch hs.symm.trans (PropRel.dataInst_quality hd h hq hp hP)
  cases Computesι.det hd hw hv'
  have hrel' := (hiff w₁ w₂).1 ((HasEq.unique hd hR' hR w₁ w₂).1 hrel)
  obtain ⟨T', hT', hn, c, hc, fs₁, fs₂, ⟨qs₁, ls₁, ps₁, Δ₁, as₁, rfl⟩,
    ⟨qs₂, ls₂, ps₂, Δ₂, as₂, rfl⟩, hfs⟩ := DataType.blockRel_inv hmono hrel'
  obtain ⟨ts₁, ts₂, rfl, rfl, hts⟩ := (hS _ T' hT' c hc).to_eqSubst hd
    (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
    (fun i R hi => by rw [hnr T' hT' c hc i] at hi; cases hi) _ _ hfs
  exact ⟨T', hT', hn, c, hc, ts₁, ts₂, ⟨_, _, _, _, _, hn ▸ hw₁⟩, ⟨_, _, _, _, _, hn ▸ hw₂⟩, hts⟩

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
theorem Subst.append_liftN_rename {Γ Δ : Scope} {n : Nat} (ξ : Ren Γ Δ) {θ : Subst 0 [] Γ}
    {θ' : Subst 0 [] Δ} (h : ∀ {a} (x : Var Δ a), θ (ξ x) = θ' x)
    (τ : Subst 0 [] (Scope.extend [] n)) {a : Scope.Entry} (x : Var (Δ.extend n) a) :
    Subst.append θ τ (Ren.liftN n ξ x) = Subst.append θ' τ x := by
  rcases Var.cases_extend n x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [Ren.liftN_weakenN, Subst.append_weakenN, Subst.append_weakenN]
    exact h y
  · rw [Ren.liftN_comp_of n (ξ₃ := Ren.empty) (fun y => nomatch y) z, Subst.append_liftN_empty,
      Subst.append_liftN_empty]

/-- Renamed destructors, at closed substitutions that the renaming composes, are equal when the
destructors are, at the composed substitutions, with the instances of the block renamed. -/
theorem ValidEqDestructors₀.rename {κ : Universe 0} :
    {Γ Δ : Scope} → {ns : List Name} → (ξ : Ren Γ Δ) → {inst : Name → Term 0 Δ} →
      {rs : Nat → Option Name} → {ds : Destructors 0 Δ ns} → {θ₁ θ₂ : Subst 0 [] Γ} →
      {θ₁' θ₂' : Subst 0 [] Δ} → (∀ {a} (x : Var Δ a), θ₁ (ξ x) = θ₁' x) →
      (∀ {a} (x : Var Δ a), θ₂ (ξ x) = θ₂' x) →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁' θ₂' →
      ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename ξ) rs (ds.rename ξ) θ₁ θ₂
  | _, _, _, _, _, _, .nil, _, _, _, _, _, _, h => h
  | _, _, _, ξ, inst, rs, .cons (ps := ps) (ψ := ψ) _ _ Θ B ds, θ₁, θ₂, θ₁', θ₂', h₁, h₂, h => by
    rw [ValidEqDestructors₀] at h
    rw [Destructors.rename, ValidEqDestructors₀, Telescope.subst_rename_of h₁,
      Telescope.subst_rename_of h₂]
    obtain ⟨hΘ, h⟩ := h
    refine ⟨hΘ, ?_⟩
    have hB : ∀ (θ : Subst 0 [] _) (θ' : Subst 0 [] _), (∀ {a} (x : Var _ a), θ (ξ x) = θ' x) →
        ∀ τ, (B.rename (Ren.liftN ps.length ξ)).subst (Subst.append θ τ) =
          B.subst (Subst.append θ' τ) := fun θ θ' hθ τ =>
      Term.subst_rename_of (Subst.append_liftN_rename ξ hθ τ) B
    have hsnoc : ∀ (θ : Subst 0 [] _) (θ' : Subst 0 [] _), (∀ {a} (x : Var _ a), θ (ξ x) = θ' x) →
        ∀ f {a} (x : Var (.secondOrder ps ψ :: _) a),
          Subst.snoc (e := .secondOrder ps ψ) θ f (Ren.lift ξ x) =
            Subst.snoc (e := .secondOrder ps ψ) θ' f x := fun θ θ' hθ f a x => by
      cases x with
      | zero => rfl
      | succ x => exact hθ x
    have hinst : (fun D => ((inst D).rename ξ).rename Ren.weaken) =
        fun D => ((inst D).rename Ren.weaken).rename (Ren.lift (e := .secondOrder ps ψ) ξ) :=
      funext fun D => (Term.rename_rename_of (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl)
        _).trans (Term.rename_rename_of (ξ₁ := Ren.lift ξ) (ξ₂ := Ren.weaken)
          (ξ₃ := fun x => Ren.weaken (ξ x)) (fun _ => rfl) _).symm
    split at h
    · obtain ⟨⟨κ₁, hκ, hBe⟩, hds⟩ := h
      refine ⟨⟨κ₁, hκ, fun τ₁ τ₂ hτ => ?_⟩, fun f₁ f₂ hf => ?_⟩
      · rw [hB θ₁ θ₁' h₁, hB θ₂ θ₂' h₂]
        exact hBe τ₁ τ₂ hτ
      · rw [hinst]
        refine ValidEqDestructors₀.rename (Ren.lift ξ) (hsnoc θ₁ θ₁' h₁ f₁) (hsnoc θ₂ θ₂' h₂ f₂)
          (hds f₁ f₂ fun τ₁ τ₂ hτ => ?_)
        rw [← hB θ₁ θ₁' h₁]
        exact hf τ₁ τ₂ hτ
    · rename_i D _
      obtain ⟨hBD, hds⟩ := h
      refine ⟨?_, fun f₁ f₂ => ?_⟩
      · rw [hBD, Term.rename_rename_of (ξ₁ := Ren.liftN ps.length ξ)
            (ξ₂ := Ren.weakenN ps.length) (ξ₃ := fun x => (ξ x).weakenN ps.length)
            (fun x => Ren.liftN_weakenN _ ξ x),
          Term.rename_rename_of (ξ₁ := Ren.weakenN ps.length) (ξ₂ := ξ)
            (ξ₃ := fun x => (ξ x).weakenN ps.length) (fun _ => rfl)]
      · rw [hinst]
        exact ValidEqDestructors₀.rename (Ren.lift ξ) (hsnoc θ₁ θ₁' h₁ f₁) (hsnoc θ₂ θ₂' h₂ f₂)
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
