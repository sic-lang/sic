module

public import Sic.Core.Soundness.Levels
public import Sic.Core.Soundness.Signature
public import Sic.Core.Soundness.Substitution

/-!
# Soundness of the Rules

Each rule of annex 13 of RFC 36 keeps the meaning of annex 16: when its premises are meaningful, in
the context of the rule at levels without variables, so is its conclusion.
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
    let σ : Subst 0 [] [] := fun x => nomatch x
    have hc : Telescope.subst σ (.cons q p A Θ) = .cons q p A Θ :=
      Telescope.subst_id_of (fun x => by cases x) _
    have d₁ : Subst.dropN ps.length (Subst.append (Subst.closedSingle t) ts.toSubst) .zero = t :=
      Subst.dropN_append _ _ .zero
    have d₂ : Subst.dropN ps.length (Subst.append (Subst.closedSingle u) us.toSubst) .zero = u :=
      Subst.dropN_append _ _ .zero
    rw [← hc] at h
    obtain ⟨ht, hts⟩ := (EqSubst.telescope_cons_iff q p A Θ σ
      (Subst.append (Subst.closedSingle t) ts.toSubst)
      (Subst.append (Subst.closedSingle u) us.toSubst)).1 h
    rw [d₁, d₂, Term.subst_empty] at ht
    have hd : sig.Distinct := ht.1.1
    rw [Telescope.subst₀_single_subst Θ t σ _ (d₁.trans (Term.subst_empty σ t).symm),
      Telescope.subst_id_of (fun x => by cases x),
      EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))] at hts
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
      refine ⟨.cons t ts', .cons u us', rfl, rfl, ?_⟩
      let σ : Subst 0 [] [] := fun x => nomatch x
      have hc : Telescope.subst σ (.cons q p A Θ) = .cons q p A Θ :=
        Telescope.subst_id_of (fun x => by cases x) _
      have d₁ : Subst.dropN ps.length (Subst.append (Subst.closedSingle t) ts'.toSubst) .zero = t :=
        Subst.dropN_append _ _ .zero
      have d₂ : Subst.dropN ps.length (Subst.append (Subst.closedSingle u) us'.toSubst) .zero = u :=
        Subst.dropN_append _ _ .zero
      show EqSubst sig ι (Context.empty.append (.cons q p A Θ))
        (Subst.append (Subst.closedSingle t) ts'.toSubst)
        (Subst.append (Subst.closedSingle u) us'.toSubst)
      rw [← hc, EqSubst.telescope_cons_iff, d₁, d₂, Term.subst_empty,
        Telescope.subst₀_single_subst Θ t σ _ (d₁.trans (Term.subst_empty σ t).symm),
        Telescope.subst_id_of (fun x => by cases x),
        EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))]
      exact ⟨htu, hτ⟩
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


/-! ## Recursors

A recursor on two equal closed terms of an instance of a data type of a meaningful declaration
computes, by the reduction of their terms, then by `(ι_⟶)`, to the branches of the constructor that
both compute to, at the terms of their fields, which the equality of the instance relates; the
branches at equal substitutions of the fields are equal terms of the motive at the constructor,
which the motive makes equal to the motive at the term.
On a proposition, whose proofs need not compute, the truth of the instance gives a constructor with
terms of its fields, whose branch is a proof of the motive, then a proposition, at the constructor:
the motive is then true at the term, and the recursors are equal proofs of it. -/

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

/-! ## Arguments of Instances -/

/-- A recursor reduces as its term does. -/
theorem RedStar.recursor {sig' : Signature} {k : Nat} {Γ Δ : Scope} {r : Grade} {D : Name}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
    {Cs : Motives k Γ} {us : Branches k Γ} {t t' : Term k Γ} (h : RedStar sig' t t') :
    RedStar sig' (.recursor r D qs ls ps as t Cs us) (.recursor r D qs ls ps as t' Cs us) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.recursor h) ih

/-- `Σ ⊨ t ≡ u : A` holds exactly when `Σ ⊨ t' ≡ u : A` does, for steps `t ⟶* t'`. -/
theorem ValidEqTerm₀.redStar_iff (hd : sig.Distinct) {t t' u A : Term 0 []}
    (h : RedStar (sig.interpret ι) t t') :
    ValidEqTerm₀ sig ι t u A ↔ ValidEqTerm₀ sig ι t' u A := by
  induction h with
  | refl => exact .rfl
  | step h _ ih => exact (ValidEqTerm₀.red_iff hd h).trans ih

/-- `(ι_⟶)` steps a recursor whose branches are substituted by `σ`, on a constructor of a declared
type of `Σ` applied to the terms of closed arguments of its fields, to the branch of the
constructor substituted by `σ` followed by the arguments and by the recursive results, the
recursors on the arguments of the recursive fields. -/
theorem Red.iota_subst {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {i j : Nat} (hi : decl.cases[i]? = some (j, T, con))
    {Γ : Scope} (σ : Subst 0 [] Γ) {qs : List Quality} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    (ts : Args 0 [] (con.params (.ofLists qs ps hq hp))) {us : Branches 0 Γ}
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend
      (con.resultParams (.ofLists qs ps hq hp) decl.names).length)}
    (hu : us.get i = some ⟨_, _, u⟩) {r : Grade} {D' : Name} {qs'' : List Quality}
    {ls ls'' : List (Level 0)} {ps'' : List Grade} {Δ Δ' : Scope} {as : InstanceArgs 0 [] Δ}
    {as' : InstanceArgs 0 [] Δ'} {Cs : Motives 0 []} :
    Red (sig.interpret ι) (.recursor r D' qs ls ps as' (.ctor D qs'' ls'' ps'' as con.name ts.terms)
      Cs (us.subst σ)) (u.subst (Subst.append (Subst.append σ ts.toSubst)
        (ts.results (fun D'' t => .recursor r D'' qs ls ps as' t Cs (us.subst σ))
          ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)).toSubst)) :=
  .iota (List.mem_map_of_mem (f := Entry.interpret ι) h.1) hi h.2.2 rfl hq hp
    (Branches.get_subst σ hu)
    (by rw [← Args.results_terms]; exact Term.instantiateTerms₂_subst_append σ u ts _)

/-- `(ι_⟶)` steps a recursor whose branches are substituted by `σ`, on a constructor without
recursive field applied to the terms of closed arguments of its fields, to the branch of the
constructor substituted by `σ` followed by the arguments. -/
theorem Red.iota_subst₀ {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {i j : Nat} (hi : decl.cases[i]? = some (j, T, con))
    {Γ : Scope} (σ : Subst 0 [] Γ) {qs : List Quality} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    (ts : Args 0 [] (con.params (.ofLists qs ps hq hp))) {us : Branches 0 Γ}
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)}
    (hu : us.get i = some ⟨_, 0, u⟩) (h0 : con.resultParams (.ofLists qs ps hq hp) decl.names = [])
    {r : Grade} {D' : Name} {qs'' : List Quality} {ls ls'' : List (Level 0)} {ps'' : List Grade}
    {Δ Δ' : Scope} {as : InstanceArgs 0 [] Δ} {as' : InstanceArgs 0 [] Δ'} {Cs : Motives 0 []} :
    Red (sig.interpret ι) (.recursor r D' qs ls ps as' (.ctor D qs'' ls'' ps'' as con.name ts.terms)
      Cs (us.subst σ)) (u.subst (Subst.append σ ts.toSubst)) := by
  have hnil : ∀ {ps' : List Parameter} (a : Args 0 [] ps'), ps' = [] → a.terms = .nil := by
    intro _ a h; subst h; cases a; rfl
  refine .iota (List.mem_map_of_mem (f := Entry.interpret ι) h.1) hi h.2.2 rfl hq hp
    (Branches.get_subst σ hu) ?_
  rw [← Args.results_terms, hnil _ h0, Term.instantiateTerms₂]
  exact (Term.instantiateTerms_terms _ ts).trans
    (congrArg some ((Term.instantiate_eq_subst _ ts).trans (Term.subst_append σ _ u)))

/-- The recursive results `f₁(D, t̄₁)` and `f₂(D, t̄₂)` of closed arguments of fields are equal
substitutions of the recursive results of `t̄₁` at closed motives `C̄`, when each pair `f₁ D t₁`
and `f₂ D t₂` at the recursive fields are equal terms of the motive of `D` at `t₁`. -/
theorem EqSubst.results {names : List Name} {f₁ f₂ : Name → Term 0 [] → Term 0 []} :
    {Cs : Motives 0 []} → (rs : List (Option Name)) → {ps : List Parameter} →
      (ts₁ ts₂ : Args 0 [] ps) → {R : Telescope 0 [] (Telescope.resultParams rs ps)} →
      Motives.results names Cs rs ts₁.terms = some R →
      Terms.RecRel (fun D t₁ t₂ => ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        ValidEqTerm₀ sig ι (f₁ D t₁) (f₂ D t₂) (C.subst₀ (Subst₀.single t₁))) rs ts₁.terms
        ts₂.terms →
      EqSubst sig ι (Context.empty.append R) (ts₁.results f₁ rs).toSubst
        (ts₂.results f₂ rs).toSubst
  | Cs, some D :: rs, p :: ps, .cons t₁ ts₁, .cons t₂ ts₂, R, hR, hQQ => by
    obtain ⟨hQ, hQs⟩ := hQQ
    simp only [Args.terms] at hR
    unfold Motives.results at hR
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at hR; cases hR
    | some a =>
      obtain ⟨n, C⟩ := a
      cases n with
      | succ => simp only [hC] at hR; cases hR
      | zero =>
        simp only [hC] at hR
        obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 hR
        let σ : Subst 0 [] [] := fun x => nomatch x
        have hc : Telescope.subst σ (.cons Grade.zero p (C.subst₀ (Subst₀.single t₁)) R') =
            .cons Grade.zero p (C.subst₀ (Subst₀.single t₁)) R' :=
          Telescope.subst_id_of (fun x => by cases x) _
        have d₁ : Subst.dropN _ (Subst.append (Subst.closedSingle (f₁ D t₁))
            (ts₁.results f₁ rs).toSubst) .zero = f₁ D t₁ := Subst.dropN_append _ _ .zero
        have d₂ : Subst.dropN _ (Subst.append (Subst.closedSingle (f₂ D t₂))
            (ts₂.results f₂ rs).toSubst) .zero = f₂ D t₂ := Subst.dropN_append _ _ .zero
        show EqSubst sig ι (Context.empty.append (.cons Grade.zero p (C.subst₀ (Subst₀.single t₁)) R'))
          (Subst.append (Subst.closedSingle (f₁ D t₁)) (ts₁.results f₁ rs).toSubst)
          (Subst.append (Subst.closedSingle (f₂ D t₂)) (ts₂.results f₂ rs).toSubst)
        rw [← hc, EqSubst.telescope_cons_iff, d₁, d₂, Term.subst_empty,
          EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))]
        refine ⟨hQ C hC, ?_⟩
        have hR'' := Motives.results_subst names (Subst.dropN (Γ := [.var]) _
          (Subst.append (n := (Telescope.resultParams rs ps).length + 1) σ
            (Subst.append (Subst.closedSingle (f₁ D t₁)) (ts₁.results f₁ rs).toSubst))) rs hR'
        rw [Motives.subst_rename_of (θ' := σ) (fun x => by cases x),
          Motives.subst_id_of (fun x => by cases x), Terms.subst_rename_of (θ' := σ)
            (fun x => by cases x), Terms.subst_id_of (fun x => by cases x)] at hR''
        exact EqSubst.results rs ts₁ ts₂ hR'' hQs
  | Cs, none :: rs, _ :: ps, .cons _ ts₁, .cons _ ts₂, R, hR, hQs => by
    unfold Motives.results at hR
    exact EqSubst.results rs ts₁ ts₂ hR hQs
  | _, [], _, _, _, R, hR, _ | _, some _ :: _, [], .nil, .nil, R, hR, _
  | _, none :: _, [], .nil, .nil, R, hR, _ => by
    unfold Motives.results at hR
    cases hR
    exact (EqSubst.empty_iff _ _).2 trivial

/-- `C[T.c(x̄) / z][σ, t̄ / x̄] = C[σ⇑][T[σ].c(t̄) / z]`: the motive at a constructor, substituted by
`σ` followed by closed arguments of its fields, is the motive substituted by `σ` at the constructor
of the instance substituted, applied to the arguments. -/
theorem Term.atCtor_subst_append {Γ Δ : Scope} (σ : Subst 0 [] Γ) (C : Term 0 (.var :: Γ))
    (D : Name) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 Γ Δ)
    (c : Name) {fs : List Parameter} (ts : Args 0 [] fs) :
    (C.atCtor D qs ls ps as c fs).subst (Subst.append σ ts.toSubst) =
      (C.subst (Subst.lift σ)).subst₀ (Subst₀.single (.ctor D qs ls ps (as.subst σ) c ts.terms)) := by
  rw [← Term.subst_append, Term.atCtor_subst, ← Term.instantiate_eq_subst, Term.atCtor_instantiate]

/-- A motive of a sort, meaningful over a term of an instance, gives equal types at equal
substitutions and equal terms of the instance. -/
theorem ValidTermΓ.motive {Γ : Scope} {ctx : Context 0 Γ} {A : Term 0 Γ} {C : Term 0 (.var :: Γ)}
    {κ : Universe 0} (hC : ValidTermΓ sig ι (ctx.var A) C (.sort κ)) {σ₁ σ₂ : Subst 0 [] Γ}
    {a₁ a₂ : Term 0 []} (hσ : EqSubst sig ι ctx σ₁ σ₂) (ha : ValidEqTerm₀ sig ι a₁ a₂ (A.subst σ₁)) :
    ValidEqType₀ sig ι ((C.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a₁))
      ((C.subst (Subst.lift σ₂)).subst₀ (Subst₀.single a₂)) := by
  rw [Term.subst_lift_single, Term.subst_lift_single]
  have hC' := hC.2 _ _ ((EqSubst.var_iff ctx A (Subst.append (n := 1) σ₁ (Subst.closedSingle a₁))
    (Subst.append (n := 1) σ₂ (Subst.closedSingle a₂))).2 ⟨hσ, ha⟩)
  obtain ⟨s, l⟩ := κ
  cases s
  · exact ValidEqTerm₀.univType hC'
  · exact ValidEqTerm₀.propType hC'

/-- A motive of a universe of propositions, meaningful over a term of an instance, is a proposition
at a substitution and a term of the instance. -/
theorem ValidTermΓ.motive_prop {Γ : Scope} {ctx : Context 0 Γ} {A : Term 0 Γ}
    {C : Term 0 (.var :: Γ)} {l : Level 0} (hC : ValidTermΓ sig ι (ctx.var A) C (.sort ⟨.prop, l⟩))
    {σ : Subst 0 [] Γ} {a : Term 0 []} (hσ : EqSubst sig ι ctx σ σ)
    (ha : ValidEqTerm₀ sig ι a a (A.subst σ)) :
    ComputesToProp sig ι ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single a)) := by
  rw [Term.subst_lift_single]
  have hC' := hC.2 _ _ ((EqSubst.var_iff ctx A (Subst.append (n := 1) σ (Subst.closedSingle a))
    (Subst.append (n := 1) σ (Subst.closedSingle a))).2 ⟨hσ, ha⟩)
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, -, hR, hw⟩ := hC'.2.1 not_computesToProp_sort
  cases hc.sort_inv
  exact ⟨w₁, hw₁, HasEq.prop_isProp hR hw⟩

/-- Relations at the recursive fields grow with the relations. -/
theorem Terms.RecRel.mono {Q Q' : Name → TermRel} :
    (rs : List (Option Name)) → {ts₁ ts₂ : Terms 0 []} →
      (∀ D, some D ∈ rs → ∀ t₁ t₂, Q D t₁ t₂ → Q' D t₁ t₂) → Terms.RecRel Q rs ts₁ ts₂ →
        Terms.RecRel Q' rs ts₁ ts₂
  | some D :: rs, .cons _ _, .cons _ _, h, hqs => by
    simp only [Terms.RecRel] at hqs ⊢
    exact ⟨h D (List.mem_cons_self ..) _ _ hqs.1,
      Terms.RecRel.mono rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hqs.2⟩
  | none :: rs, .cons _ _, .cons _ _, h, hs =>
    Terms.RecRel.mono rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hs
  | [], _, _, _, _ | some _ :: _, .nil, _, _, _ | none :: _, .nil, _, _, _
  | some _ :: _, .cons _ _, .nil, _, _ | none :: _, .cons _ _, .nil, _, _ => trivial

/-- Two terms equal in a type that computes to a proposition make it true, so that any two terms are
equal in it. -/
theorem ValidEqTerm₀.prop_any (hd : sig.Distinct) {t u t' u' A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) (hA : ComputesToProp sig ι A) : ValidEqTerm₀ sig ι t' u' A := by
  obtain ⟨w, R, hw, hR, hrel⟩ := h.2.2 hA
  exact ⟨h.1, fun hn => absurd hA hn, fun _ => ⟨w, R, hw, hR, hR.prop_any hd (hA.isProp hd hw) hrel⟩⟩

-- ADE: `natrec-congᵛ`, `prodrec-congᵛ`, `unitrec-congᵛ` and `emptyrec-congᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(rec_≡)` keeps the meaning, and `(rec)` with it: at equal substitutions of the context, the
recursors on the canonical terms that `(eq_μ)` relates are equal terms of the motive, by induction on
`(eq_μ)`, the least relations closed under its clauses: the relations of the canonical terms that
`(eq_μ)` relates and on which the recursors are equal are closed, since the recursors on two
constructors step to their branches, at equal arguments of the fields and at recursive results that
these relations make equal. On a proposition, the truths of its instances whose motives are true at
every proof are closed likewise, so that the motive at the term is true. -/
theorem ValidEqTermΓ.recursor {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ : InstanceArgs 0 Γ decl.scope} {Δ₂ : Scope}
    {as₂ : InstanceArgs 0 Γ Δ₂} {r : Grade} {t₁ t₂ : Term 0 Γ} {Cs₁ Cs₂ : Motives 0 Γ}
    {us₁ us₂ : Branches 0 Γ} {κ : Universe 0} {h' : Nat} {C₁ : Term 0 (.var :: Γ)}
    {as₁' : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₁'
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (ht : ValidEqTermΓ sig ι ctx t₁ t₂ (.inst D qs ls₁ ps as₁)) (hh : decl.dataTypes[h']? = some T)
    (hC : Cs₁.get h' = some ⟨0, C₁⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs₁.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs₁.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls₁ ps as₁)) C' (.sort κ))
    (hus₁ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hus₂ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hut : ∀ i j T' con C' R u₁ u₂, decl.cases[i]? = some (j, T', con) →
      Cs₁.get j = some ⟨0, C'⟩ → con.results (.ofLists qs ps hq hp) decl.names Cs₁ = some R →
      us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
      us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
      ValidEqTermΓ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)).append R) u₁ u₂
        ((C'.atCtor T'.name qs ls₁ ps as₁ con.name (con.params (.ofLists qs ps hq hp))).rename
          (Ren.weakenN _)))
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop) :
    ValidEqTermΓ sig ι ctx (.recursor r D qs ls₁ ps as₁ t₁ Cs₁ us₁)
      (.recursor r D qs ls₂ ps as₂ t₂ Cs₂ us₂) (C₁.subst₀ (Subst₀.single t₁)) := by
  obtain ⟨hsig, hv⟩ := hent.hasDataType h
  obtain ⟨hdecl, hT, hD⟩ := id hsig
  subst hD
  have hctx := ht.1.1
  have hd := hctx.distinct
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have ht₁ := ht.trans ht.symm
  have hCv₀ := hCv h' T C₁ hh hC
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hCsN : ∀ D' ∈ decl.names, ∃ C, Cs₁.get (decl.names.idxOf D') = some ⟨0, C⟩ :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
      rw [hidx j T' hj]
      exact hCs j T' hj
  have hcase : ∀ T' ∈ decl.dataTypes, ∀ con ∈ T'.constructors,
      ∃ i j : Nat, decl.cases[i]? = some (j, T', con) ∧ decl.dataTypes[j]? = some T' := by
    intro T' hT' con hcon
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
    have hmem : (j, T', con) ∈ decl.cases := by
      have := TypeDeclaration.mem_casesFrom_of (i := 0) hj hcon
      rwa [Nat.zero_add] at this
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    exact ⟨i, j, hi, hj⟩
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
      Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
    exact hCv₀.motive hσ (ht₁.2 σ₁ σ₂ hσ)
  -- The motive of a type of the block in the motives substituted is its motive, substituted.
  have hK : ∀ τ : Subst 0 [] Γ, ∀ D' ∈ decl.names, ∀ C,
      (Cs₁.subst τ).get (decl.names.idxOf D') = some ⟨0, C⟩ → ∃ j T' C',
        decl.dataTypes[j]? = some T' ∧ T'.name = D' ∧ Cs₁.get j = some ⟨0, C'⟩ ∧
          C = C'.subst (Subst.lift τ) := by
    intro τ D' hD' C hC'
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
    obtain ⟨C', hC''⟩ := hCs j T' hj
    rw [hidx j T' hj, Motives.get_subst τ hC''] at hC'
    cases hC'
    exact ⟨j, T', C', hj, rfl, hC'', rfl⟩
  -- The branches of a constructor, at equal substitutions of the context, at equal arguments of its
  -- fields and at recursive results equal in their motives, are equal terms of the motive at the
  -- constructor, and the recursors on the constructor step to them.
  have hbranch : ∀ τ₁ τ₂ : Subst 0 [] Γ, EqSubst sig ι ctx τ₁ τ₂ → ∀ T' ∈ decl.dataTypes,
      ∀ con ∈ T'.constructors, ∀ C' : Term 0 (.var :: Γ),
      Cs₁.get (decl.names.idxOf T'.name) = some ⟨0, C'⟩ →
      ∀ ts₁ ts₂ : Args 0 [] (con.params (.ofLists qs ps hq hp)),
      EqSubst sig ι (Context.empty.append
        ((con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁).subst τ₁)) ts₁.toSubst
        ts₂.toSubst →
      Terms.RecRel (fun D' a₁ a₂ => ∀ C, (Cs₁.subst τ₁).get (decl.names.idxOf D') = some ⟨0, C⟩ →
          ValidEqTerm₀ sig ι
            (.recursor r D' qs ls₁ ps (as₁.subst τ₁) a₁ (Cs₁.subst τ₁) (us₁.subst τ₁))
            (.recursor r D' qs ls₂ ps (as₂.subst τ₂) a₂ (Cs₂.subst τ₂) (us₂.subst τ₂))
            (C.subst₀ (Subst₀.single a₁)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts₁.terms ts₂.terms →
      ∃ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ ((C'.subst (Subst.lift τ₁)).subst₀
          (Subst₀.single (.ctor T'.name qs ls₁ ps (as₁.subst τ₁) con.name ts₁.terms))) ∧
        (∀ {qs'' : List Quality} {ls'' : List (Level 0)} {ps'' : List Grade} {Δ'' : Scope}
          {as'' : InstanceArgs 0 [] Δ''},
          Red (sig.interpret ι) (.recursor r T'.name qs ls₁ ps (as₁.subst τ₁)
            (.ctor T'.name qs'' ls'' ps'' as'' con.name ts₁.terms) (Cs₁.subst τ₁)
            (us₁.subst τ₁)) v₁) ∧
        (∀ {qs'' : List Quality} {ls'' : List (Level 0)} {ps'' : List Grade} {Δ'' : Scope}
          {as'' : InstanceArgs 0 [] Δ''},
          Red (sig.interpret ι) (.recursor r T'.name qs ls₂ ps (as₂.subst τ₂)
            (.ctor T'.name qs'' ls'' ps'' as'' con.name ts₂.terms) (Cs₂.subst τ₂)
            (us₂.subst τ₂)) v₂) := by
    intro τ₁ τ₂ hτ T' hT' con hcon C' hC' ts₁ ts₂ hts hQ
    obtain ⟨i, j, hi, hj⟩ := hcase T' hT' con hcon
    rw [hidx j T' hj] at hC'
    obtain ⟨u₁, hu₁⟩ := hus₁ i j T' con hi
    obtain ⟨u₂, hu₂⟩ := hus₂ i j T' con hi
    obtain ⟨R, hR⟩ := Constructor.results_isSome con (.ofLists qs ps hq hp) hCsN
    have hres := EqSubst.results (sig := sig) (ι := ι) _ ts₁ ts₂
      (Constructor.results_subst_append hR τ₁ ts₁) hQ
    have hb := (hut i j T' con C' R u₁ u₂ hi hC' hR hu₁ hu₂).2 _ _
      ((EqSubst.append_append_iff _ R _ _ _ _).2
        ⟨(EqSubst.append_append_iff ctx _ τ₁ τ₂ _ _).2 ⟨hτ, hts⟩, hres⟩)
    rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hb
    have hsig' : sig.HasDataType T'.name decl T' := ⟨hdecl, hT', rfl⟩
    exact ⟨_, _, hb, Red.iota_subst hsig' hi τ₁ hq hp ts₁ hu₁,
      Red.iota_subst hsig' hi τ₂ hq hp ts₂ hu₂⟩
  have ht' := ht.2 σ₁ σ₂ hσ
  have hσ₁ := hσ.left hctx
  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls₁ ps (as₁.subst σ₁))
      (.inst D' qs ls₁ ps (as₁.subst σ₁)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht'.1.2
  cases Computesι.det hd hcv (hI T.name)
  have hasσ := has.2 σ₁ σ₁ hσ₁
  have htσ : ValidEqTerm₀ sig ι (t₁.subst σ₁) (t₁.subst σ₁)
      (.inst T.name qs ls₁ ps (as₁.subst σ₁)) := ht'.trans ht'.symm
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · -- An instance in a universe: induction on `(eq_μ)`.
    obtain ⟨S, hU, hmono, hrec, hiff⟩ := hv.univRel hd hdecl hq hl₁ hp hadm hasσ hs
    have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
        (DataType.blockRel decl.dataTypes S T'.name).computed sig ι a b →
          ValidEqTerm₀ sig ι a b (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
      fun T' hT' _ _ hab => (FieldRel.univ rfl (hU T' hT').1).validEqTerm hd (hI _) hab
    let X : Name → TermRel := fun D' a b => DataType.blockRel decl.dataTypes S D' a b ∧
      ∀ C' : Term 0 (.var :: Γ), Cs₁.get (decl.names.idxOf D') = some ⟨0, C'⟩ → ValidEqTerm₀ sig ι
        (.recursor r D' qs ls₁ ps (as₁.subst σ₁) a (Cs₁.subst σ₁) (us₁.subst σ₁))
        (.recursor r D' qs ls₂ ps (as₂.subst σ₂) b (Cs₂.subst σ₂) (us₂.subst σ₂))
        ((C'.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a))
    have hclosed : ∀ T' ∈ decl.dataTypes, ∀ a b, T'.ctorRel T'.name (S X) a b →
        X T'.name a b := by
      rintro T' hT' a b ⟨con, hcon, fs₁, fs₂, ⟨qs₁', ls₁', ps₁', Δ₁', as₁'', rfl⟩,
        ⟨qs₂', ls₂', ps₂', Δ₂', as₂'', rfl⟩, hS⟩
      have hSb := hmono X _ (fun _ _ _ h => h.1) T' hT' con hcon fs₁ fs₂ hS
      refine ⟨DataType.blockRel_closed hmono hT' ⟨con, hcon, fs₁, fs₂, ⟨_, _, _, _, _, rfl⟩,
        ⟨_, _, _, _, _, rfl⟩, hSb⟩, fun C' hC' => ?_⟩
      obtain ⟨ts₁, ts₂, rfl, rfl, hts⟩ := (hiff T' hT' con hcon).2.1 fs₁ fs₂ hSb
      have hQ : ∀ D', some D' ∈ (con.fields (.ofLists qs ps hq hp)).recursion decl.names →
          ∀ a₁ a₂, (X D').computed sig ι a₁ a₂ → ∀ C,
          (Cs₁.subst σ₁).get (decl.names.idxOf D') = some ⟨0, C⟩ → ValidEqTerm₀ sig ι
            (.recursor r D' qs ls₁ ps (as₁.subst σ₁) a₁ (Cs₁.subst σ₁) (us₁.subst σ₁))
            (.recursor r D' qs ls₂ ps (as₂.subst σ₂) a₂ (Cs₂.subst σ₂) (us₂.subst σ₂))
            (C.subst₀ (Subst₀.single a₁)) := by
        intro D' hD' a₁ a₂ hX C hC
        obtain ⟨j'', T'', C'', hj'', rfl, hC'', rfl⟩ :=
          hK σ₁ D' (Telescope.mem_recursion hD') C hC
        obtain ⟨v', w', hv', hw', hXvw⟩ := hX
        have hT'' := List.mem_of_getElem? hj''
        have hP := hXvw.2 C'' ((hidx j'' T'' hj'').symm ▸ hC'')
        have hvt : ValidEqTerm₀ sig ι v' a₁ (.inst T''.name qs ls₁ ps (as₁.subst σ₁)) := by
          have h₁₂ := hval T'' hT'' a₁ a₂ ⟨v', w', hv', hw', hXvw.1⟩
          exact (ValidEqTerm₀.redStar_iff hd hv'.1).1 (h₁₂.trans h₁₂.symm)
        have hP' := hP.conv ((hCv j'' T'' C'' hj'' hC'').motive hσ₁ hvt)
        exact (ValidEqTerm₀.redStar_iff hd (RedStar.recursor hv'.1)).2
          ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw'.1)).2 hP'.symm).symm
      obtain ⟨v₁, v₂, hb, hr₁, hr₂⟩ := hbranch σ₁ σ₂ hσ T' hT' con hcon C' hC' ts₁ ts₂
        (by rw [Constructor.fieldsAt_subst]; exact hts)
        (Terms.RecRel.mono _ hQ (hrec X T' hT' con hcon _ _ hS))
      obtain ⟨i, j, hi, hj⟩ := hcase T' hT' con hcon
      have hca : ValidEqTerm₀ sig ι (.ctor T'.name qs ls₁ ps (as₁.subst σ₁) con.name ts₁.terms)
          (.ctor T'.name qs₁' ls₁' ps₁' as₁'' con.name ts₁.terms)
          (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
        hval T' hT' _ _ ⟨_, _, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩,
          DataType.blockRel_closed hmono hT' ⟨con, hcon, ts₁.terms, ts₁.terms,
            ⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, rfl⟩, (hiff T' hT' con hcon).2.2 _ _ hSb⟩⟩
      have hb' := hb.conv ((hCv j T' C' hj ((hidx j T' hj) ▸ hC')).motive hσ₁ hca)
      exact (ValidEqTerm₀.red_iff hd hr₁).2 ((ValidEqTerm₀.red_iff hd hr₂).2 hb'.symm).symm
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hnp : ¬ ComputesToProp sig ι (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
      fun ⟨v, hv, k, b, hk⟩ => by
        cases Computesι.det hd (hI _) hv
        exact HasEq.univ_not_prop hd hU' hk
    obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht'.2.1 hnp
    cases Computesι.det hd (hI _) hv'
    have hrel' := (HasEq.unique hd hR' (.univ _ hU') w₁ w₂).1 hrel
    have hP := (hrel' X hclosed).2 C₁ ((hidx h' T hh).symm ▸ hC)
    have hwt : ValidEqTerm₀ sig ι w₁ (t₁.subst σ₁) (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
      (ValidEqTerm₀.redStar_iff hd hw₁.1).1 htσ
    have hP' := hP.conv (hCv₀.motive hσ₁ hwt)
    exact (ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₁.1)).2
      ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₂.1)).2 hP'.symm).symm
  · -- A proposition: induction on `(true_μ)`.
    obtain ⟨S, hP, hmono, hrec, hiff⟩ := hv.propRel hd hdecl hq hl₁ hp hadm hasσ hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have hprop : ComputesToProp sig ι (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
      ⟨_, hI _, _, _, hP'⟩
    obtain ⟨v', R', hv', hR', hrel⟩ := ht'.2.2 hprop
    cases Computesι.det hd (hI _) hv'
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      (HasEq.unique hd hR' (.prop _ _ hP' fun _ _ => .rfl) _ _).1 hrel
    obtain ⟨T₀, hT₀, -, con₀, hcon₀, -⟩ := DataType.blockTruth_inv hmono htrue
    obtain ⟨i₀, j₀, hi₀, -⟩ := hcase T₀ hT₀ con₀ hcon₀
    obtain ⟨s, l⟩ := κ
    have hs' : s = .prop := hκ hs (List.ne_nil_of_mem (List.mem_of_getElem? hi₀))
    subst hs'
    have hvalP : ∀ T' ∈ decl.dataTypes, ∀ a,
        DataType.blockTruth decl.dataTypes S T'.name →
          ValidEqTerm₀ sig ι a a (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
      fun T' hT' _ hb => (FieldRel.prop (hP T' hT').1 :
        FieldRel sig ι _ (fun m _ => levelRel sig ι m) .prop _
          (fun _ _ => DataType.blockTruth decl.dataTypes S T'.name)).validEqTerm hd (hI _) hb
    let B : Name → Prop := fun D' => DataType.blockTruth decl.dataTypes S D' ∧
      ∀ C' : Term 0 (.var :: Γ), Cs₁.get (decl.names.idxOf D') = some ⟨0, C'⟩ → ∀ a,
        ValidEqTerm₀ sig ι a a (.inst D' qs ls₁ ps (as₁.subst σ₁)) → ValidEqTerm₀ sig ι
          (.recursor r D' qs ls₁ ps (as₁.subst σ₁) a (Cs₁.subst σ₁) (us₁.subst σ₁))
          (.recursor r D' qs ls₁ ps (as₁.subst σ₁) a (Cs₁.subst σ₁) (us₁.subst σ₁))
          ((C'.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a))
    have hclosed : ∀ T' ∈ decl.dataTypes, T'.truth (S B) → B T'.name := by
      rintro T' hT' ⟨con, hcon, fs, hfs⟩
      have hSb := hmono B _ (fun _ h => h.1) T' hT' con hcon fs fs hfs
      refine ⟨DataType.blockTruth_closed hmono hT' ⟨con, hcon, fs, hSb⟩, fun C' hC' a ha => ?_⟩
      obtain ⟨ts₁, ts₂, rfl, h₂, hts⟩ := (hiff T' hT' con hcon).2.1 fs fs hSb
      cases Args.terms_inj h₂
      have hQ : ∀ D', some D' ∈ (con.fields (.ofLists qs ps hq hp)).recursion decl.names →
          ∀ a₁ a₂ : Term 0 [], B D' → ∀ C,
          (Cs₁.subst σ₁).get (decl.names.idxOf D') = some ⟨0, C⟩ → ValidEqTerm₀ sig ι
            (.recursor r D' qs ls₁ ps (as₁.subst σ₁) a₁ (Cs₁.subst σ₁) (us₁.subst σ₁))
            (.recursor r D' qs ls₂ ps (as₂.subst σ₁) a₂ (Cs₂.subst σ₁) (us₂.subst σ₁))
            (C.subst₀ (Subst₀.single a₁)) := by
        intro D' hD' a₁ a₂ hB C hC
        obtain ⟨j'', T'', C'', hj'', rfl, hC'', rfl⟩ :=
          hK σ₁ D' (Telescope.mem_recursion hD') C hC
        have ha₁ := hvalP T'' (List.mem_of_getElem? hj'') a₁ hB.1
        exact (hB.2 C'' ((hidx j'' T'' hj'').symm ▸ hC'') a₁ ha₁).prop_any hd
          ((hCv j'' T'' C'' hj'' hC'').motive_prop hσ₁ ha₁)
      obtain ⟨v₁, v₂, hb, -, -⟩ := hbranch σ₁ σ₁ hσ₁ T' hT' con hcon C' hC' ts₁ ts₁
        (by rw [Constructor.fieldsAt_subst]; exact hts)
        (Terms.RecRel.mono _ (fun D' hD' a₁ a₂ hB => hQ D' hD' a₁ a₂ hB)
          (hrec B T' hT' con hcon _ _ hfs))
      obtain ⟨i, j, hi, hj⟩ := hcase T' hT' con hcon
      have hCj := hCv j T' C' hj ((hidx j T' hj) ▸ hC')
      have hca : ValidEqTerm₀ sig ι (.ctor T'.name qs ls₁ ps (as₁.subst σ₁) con.name ts₁.terms) a
          (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
        ha.prop_any hd ⟨_, hI _, _, _, levelRel_prop_iff.2 (hP T' hT').1⟩
      exact (hb.conv (hCj.motive hσ₁ hca)).prop_any hd (hCj.motive_prop hσ₁ ha)
    exact ((htrue B hclosed).2 C₁ ((hidx h' T hh).symm ▸ hC) _ htσ).prop_any hd
      (hCv₀.motive_prop hσ₁ htσ)

-- ADE: `natrec-zeroᵛ`, `natrec-sucᵛ`, `prodrec-βᵛ` and `unitrec-βᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(ι)` keeps the meaning: at equal substitutions of the context, the recursors on the constructor
are equal terms of the motive, by `(rec_≡)`, and the second one steps to the substituted instance of
the branch by the arguments and by the recursive results. -/
theorem ValidEqTermΓ.iota {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) (hc : con ∈ T.constructors) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {ts : Args 0 Γ (con.params (.ofLists qs ps hq hp))}
    (hts : ValidArgsΓ sig ι ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
    {i j : Nat} (hi : decl.cases[i]? = some (j, T, con)) {r : Grade} {Cs : Motives 0 Γ}
    {us : Branches 0 Γ} {κ : Universe 0} {C : Term 0 (.var :: Γ)} (hC : Cs.get j = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hut : ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) →
      Cs.get j = some ⟨0, C'⟩ → con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
      us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
      ValidTermΓ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R) u
        ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
          (Ren.weakenN _)))
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop)
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend
      (con.resultParams (.ofLists qs ps hq hp) decl.names).length)}
    (hu : us.get i = some ⟨_, _, u⟩) :
    ValidEqTermΓ sig ι ctx (.recursor r D qs ls ps as (.ctor D qs ls ps as con.name ts.terms) Cs us)
      ((u.instantiate ((ts.results (fun D' t => .recursor r D' qs ls ps as t Cs us)
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)).rename
          (Ren.weakenN _))).instantiate ts)
      (C.subst₀ (Subst₀.single (.ctor D qs ls ps as con.name ts.terms))) := by
  obtain ⟨hsig, -⟩ := hent.hasDataType h
  have hD := h.2.2
  subst hD
  have hd := has.1.distinct
  have hct := ValidEqTermΓ.ctor hent h hc hq hl hl hp hadm has (fun _ => Level.equivalence.refl _) hts
  have hj : decl.dataTypes[j]? = some T := by
    have := (TypeDeclaration.getElem?_of_mem_casesFrom (List.mem_of_getElem? hi)).2
    rwa [Nat.sub_zero] at this
  have hrec := ValidEqTermΓ.recursor hent h hq hl hp hadm has hct hj hC hCs hCv hus hus
    (fun i j T' con C' R u₁ u₂ hi hC hR hu₁ hu₂ => by
      cases Branches.get_inj hu₁ hu₂
      exact hut i j T' con C' R u₁ hi hC hR hu₁) hκ (ls₂ := ls) (Cs₂ := Cs) (us₂ := us) (r := r)
    (as₂ := as)
  refine ⟨hrec.1, fun σ₁ σ₂ hσ => ?_⟩
  have hr := hrec.2 σ₁ σ₂ hσ
  rw [Term.instantiate_instantiate_subst_closed,
    Args.results_subst σ₂ (f' := fun D' t => .recursor r D' qs ls ps (as.subst σ₂) t (Cs.subst σ₂)
      (us.subst σ₂)) (fun _ _ => rfl)]
  have hred := Red.iota_subst (ι := ι) hsig hi σ₂ hq hp (ts.subst σ₂) hu (r := r) (ls := ls)
    (D' := T.name)
    (as' := as.subst σ₂) (Cs := Cs.subst σ₂) (as := as.subst σ₂) (ls'' := ls) (qs'' := qs)
    (ps'' := ps)
  rw [Args.terms_subst] at hred
  exact ((ValidEqTerm₀.red_iff hd hred).1 hr.symm).symm

-- ADE: `unitrec-β-ηᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Unit.agda`.
/-- `(η_c)` keeps the meaning: at equal substitutions of the context, the term `t` of an instance in
a universe computes to the single constructor of its type, at fields equal to those of the other
substitution, without recursive results since it has no recursive field, so that the recursor at the
other substitution steps to `e` at this constructor, equal to `e` at the term `t` since the two are
equal terms of the instance; on a proposition, the motive is a proposition, true since `e` proves
it. -/
theorem ValidEqTermΓ.etaCtor {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) (hc : T.constructors = [con]) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    (hr : ∀ R ∈ (con.fields (.ofLists qs ps hq hp)).recursion decl.names, R = none)
    {as : InstanceArgs 0 Γ decl.scope} {r : Grade} {t : Term 0 Γ} {Cs : Motives 0 Γ}
    {us : Branches 0 Γ} {κ : Universe 0} {i j : Nat} {C e : Term 0 (.var :: Γ)}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (he : ValidTermΓ sig ι (ctx.var (.inst D qs ls ps as)) e C)
    (hCv : ValidTermΓ sig ι (ctx.var (.inst D qs ls ps as)) C (.sort κ))
    (hi : decl.cases[i]? = some (j, T, con))
    (hu : us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0,
      e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))⟩)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop) :
    ValidEqTermΓ sig ι ctx (e.subst₀ (Subst₀.single t)) (.recursor r D qs ls ps as t Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  obtain ⟨hsig, hv⟩ := hent.hasDataType h
  obtain ⟨hdecl, hT, hD⟩ := id hsig
  subst hD
  have hctx := ht.1.1
  have hd := hctx.distinct
  have hcon : con ∈ T.constructors := hc ▸ List.mem_singleton_self con
  have h0 : con.resultParams (.ofLists qs ps hq hp) decl.names = [] :=
    Telescope.resultParams_of_none hr
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
      Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
    exact hCv.motive hσ (ht.2 σ₁ σ₂ hσ)
  have ht' := ht.2 σ₁ σ₂ hσ
  have hσ₁ := hσ.left hctx
  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
    Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
  have hI : Computesι sig ι (.inst T.name qs ls ps (as.subst σ₁))
      (.inst T.name qs ls ps (as.subst σ₁)) := ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht'.1.2
  cases Computesι.det hd hcv hI
  have hasσ := has.2 σ₁ σ₁ hσ₁
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · -- An instance in a universe: the term computes to the constructor, at both substitutions.
    obtain ⟨S, hU, hmono, hrec, hiff⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hnp : ¬ ComputesToProp sig ι (.inst T.name qs ls ps (as.subst σ₁)) :=
      fun ⟨v, hv, k, b, hk⟩ => by
        cases Computesι.det hd hI hv
        exact HasEq.univ_not_prop hd hU' hk
    obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht'.2.1 hnp
    cases Computesι.det hd hI hv'
    have hrel' := (HasEq.unique hd hR' (.univ _ hU') w₁ w₂).1 hrel
    obtain ⟨T', hT', hn, con', hcon', fs₁, fs₂, ⟨qs₁, ls₁, ps₁, Δ₁, as₁, rfl⟩,
      ⟨qs₂, ls₂, ps₂, Δ₂, as₂, rfl⟩, hS₁₂⟩ := DataType.blockRel_inv hmono hrel'
    cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hdecl)) hT' hT hn
    rw [hc, List.mem_singleton] at hcon'
    subst hcon'
    obtain ⟨ts₁, ts₂, rfl, rfl, -⟩ := (hiff T hT con' hcon).2.1 fs₁ fs₂ hS₁₂
    have hct : ValidEqTerm₀ sig ι (t.subst σ₁)
        (.ctor T.name qs ls ps (as.subst σ₂) con'.name ts₂.terms)
        (.inst T.name qs ls ps (as.subst σ₁)) :=
      ⟨ht'.1, fun _ => ⟨_, _, _, _, hI, hw₁, ⟨.refl _, .ctor _ _ _ _ _ _ _⟩, .univ _ hU',
        DataType.blockRel_closed hmono hT ⟨con', hcon, ts₁.terms, ts₂.terms,
          ⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, rfl⟩, hS₁₂⟩⟩,
        fun hp => absurd hp hnp⟩
    have hb := he.2 _ _ ((EqSubst.var_iff ctx _
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))
      (Subst.append (n := 1) σ₂ (Subst.closedSingle _))).2 ⟨hσ, hct⟩)
    have hbr : ValidEqTerm₀ sig ι ((e.subst (Subst.lift σ₁)).subst₀ (Subst₀.single (t.subst σ₁)))
        ((e.atCtor T.name qs ls ps as con'.name (con'.params (.ofLists qs ps hq hp))).subst
          (Subst.append σ₂ ts₂.toSubst))
        ((C.subst (Subst.lift σ₁)).subst₀ (Subst₀.single (t.subst σ₁))) := by
      rw [Term.atCtor_subst_append, Term.subst_lift_single, Term.subst_lift_single,
        Term.subst_lift_single]
      exact hb
    exact ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₂.1)).2
      ((ValidEqTerm₀.red_iff hd (Red.iota_subst₀ hsig hi σ₂ hq hp ts₂ hu h0)).2 hbr.symm)).symm
  · -- A proposition: the motive is one, which `e` proves.
    obtain ⟨s, l⟩ := κ
    have hs' : s = .prop := hκ hs (List.ne_nil_of_mem (List.mem_of_getElem? hi))
    subst hs'
    have ht₁ := ht.2 σ₁ σ₁ hσ₁
    have hCp := hCv.motive_prop hσ₁ ht₁
    have hb := he.2 _ _ ((EqSubst.var_iff ctx _
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))).2 ⟨hσ₁, ht₁⟩)
    rw [Term.subst_lift_single] at hCp
    rw [Term.subst_lift_single, Term.subst_lift_single]
    obtain ⟨w, R'', hw, hR'', hrel''⟩ := hb.2.2 hCp
    exact ⟨hb.1, fun hn => absurd hCp hn,
      fun _ => ⟨w, R'', hw, hR'', hR''.prop_any hd (hCp.isProp hd hw) hrel''⟩⟩

/-! ## Observations

An observation of two equal closed terms of an instance of a codata type of a meaningful declaration
computes, by the reduction of their terms, then by `(β_⟶)`, as the observations of the corecursors
that both compute to, which the equality of the instance relates, whatever the instance that an
observation carries; the destructors before the one observed are, in its telescope and its result,
the observations of the term, which compute as those of its corecursor, so that the equality of the
destructors relates them, from the first destructor to the observed one.
On a proposition, whose proofs need not compute, the truth of the instance gives abstractions that
its destructors relate, and every result is a proposition, whose truth holds of any term, so that
the observations of the proofs need not compute.
The results of the destructors are types at every pair of equal substitutions of their context,
which the destructors of a meaningful declaration give, so that the type of an observation is a
type. -/

/-- An observation reduces as its term does. -/
theorem RedStar.obs {sig' : Signature} {k : Nat} {Γ Δ : Scope} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {d : Name} {bs : Terms k Γ}
    {t t' : Term k Γ} (h : RedStar sig' t t') :
    RedStar sig' (.obs D qs ls ps as t d bs) (.obs D qs ls ps as t' d bs) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.obs h) ih

/-- A term computes to the canonical terms of the terms it reduces to, in a signature whose names
are distinct. -/
theorem Computesι.redStar_iff (hd : sig.Distinct) {t t' v : Term 0 []}
    (h : RedStar (sig.interpret ι) t t') : Computesι sig ι t v ↔ Computesι sig ι t' v := by
  induction h with
  | refl => exact .rfl
  | step h _ ih => exact (Computesι.red_iff hd h).trans ih

/-- An observation of a corecursor computes as the observation of the same corecursor by the same
destructor at the same arguments, whatever instance each observation carries, since `(β_⟶)` does
not read it, and the corecursor does not reduce. -/
theorem Computesι.obs_corec_iff {Δ₁ Δ₂ Δ : Scope} {D₁ D₂ D : Name} {qs₁ qs₂ qs : List Quality}
    {ls₁ ls₂ ls : List (Level 0)} {ps₁ ps₂ ps : List Grade} {as₁ : InstanceArgs 0 [] Δ₁}
    {as₂ : InstanceArgs 0 [] Δ₂} {as : InstanceArgs 0 [] Δ} {r : Grade} {ss : Terms 0 []}
    {Ss : States 0 []} {gs : CorecBranches 0 []} {d : Name} {bs : Terms 0 []} {v : Term 0 []} :
    Computesι sig ι (.obs D₁ qs₁ ls₁ ps₁ as₁ (.corec r D qs ls ps as ss Ss gs) d bs) v →
      Computesι sig ι (.obs D₂ qs₂ ls₂ ps₂ as₂ (.corec r D qs ls ps as ss Ss gs) d bs) v := by
  rintro ⟨hs, hv⟩
  cases hs with
  | refl => cases hv with | ne hn => cases hn with | obs hn => cases hn
  | step h hs =>
    cases h with
    | beta h hi hD hq hl hp hg hv' => exact ⟨.step (.beta h hi hD hq hl hp hg hv') hs, hv⟩
    | obs h => exact nomatch h

-- ADE: none.
/-- The observations `f` compute as the observations `o` at all closed arguments, or the quality `s`
is that of the propositions, whose proofs need not compute. -/
def ObsEquiv (sig : Signature) (ι : Interpretation) (s : Quality) (f o : Observations) : Prop :=
  s = .prop ∨ ∀ d ps (τ : Subst 0 [] (Scope.extend [] ps.length)) v,
    Computesι sig ι ((f d ps).subst τ) v ↔ Computesι sig ι ((o d ps).subst τ) v

/-- The equality of the terms of the type of a field relates the terms that compute as the terms it
relates, and any terms when the quality is that of the propositions. -/
theorem FieldRel.congr_computes {n : Nat} {s : Quality} {v : Term 0 []} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F) {a a' b b' : Term 0 []}
    (h : s = .prop ∨ ((∀ w, Computesι sig ι a w ↔ Computesι sig ι a' w) ∧
      ∀ w, Computesι sig ι b w ↔ Computesι sig ι b' w)) : F a b ↔ F a' b' := by
  cases hF with
  | univ hs _ | univBelow hs _ _ _ =>
    rcases h with h | ⟨ha, hb⟩
    · exact absurd (hs.symm.trans h) (by decide)
    · simp only [TermRel.computed, ha, hb]
  | prop _ | propBelow _ _ _ => exact .rfl

/-- The equality of the abstractions for a destructor relates the abstractions that compute as the
abstractions it relates, at all closed arguments, and any abstractions when the quality is that of
the propositions. -/
theorem AbstractionRel.congr_computes {n : Nat} {s : Quality} {ps : List Parameter}
    {SΘ : FieldsRel} {F : Terms 0 [] → TermRel} (hSp : IsPer SΘ)
    (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms))
    {f₁ f₂ g₁ g₂ : Term 0 (Scope.extend [] ps.length)}
    (h : s = .prop ∨ ((∀ τ w, Computesι sig ι (f₁.subst τ) w ↔ Computesι sig ι (g₁.subst τ) w) ∧
      ∀ τ w, Computesι sig ι (f₂.subst τ) w ↔ Computesι sig ι (g₂.subst τ) w)) :
    AbstractionRel SΘ F f₁ f₂ ↔ AbstractionRel SΘ F g₁ g₂ := by
  have key : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
      (F ts.terms (f₁.subst ts.toSubst) (f₂.subst us.toSubst) ↔
        F ts.terms (g₁.subst ts.toSubst) (g₂.subst us.toSubst)) := fun ts us hts => by
    obtain ⟨v, hv⟩ := hF ts (hSp.trans hts (hSp.symm hts))
    exact hv.congr_computes (h.imp_right fun ⟨h₁, h₂⟩ => ⟨h₁ _, h₂ _⟩)
  exact ⟨fun h' ts us hts => (key ts us hts).1 (h' ts us hts),
    fun h' ts us hts => (key ts us hts).2 (h' ts us hts)⟩

/-- At observations related by the equality of destructors, whose first destructor `d` is not
recursive, the observations `f₁` and `f₂` that compute as them are, for `d`, equal terms of its
result at equal arguments, and the equality of the destructors after `d`, with `f₁` for `d`, relates
them. -/
theorem DesRel.head (hd : sig.Distinct) {n : Nat} {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
    {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
    {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (.cons (d := d) p q Θ B ψ ds) @θ S)
    (hr : rs 0 = none) {o₁ o₂ f₁ f₂ : Observations} (hS : S o₁ o₂)
    (hf₁ : ObsEquiv sig ι s f₁ o₁) (hf₂ : ObsEquiv sig ι s f₂ o₂) :
    (∀ ts us : Args 0 [] ps, EqSubst sig ι (Context.empty.append (Θ.subst θ)) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)
        (B.subst (Subst.append θ ts.toSubst))) ∧
    ∃ S', DesRel sig ι n (fun m _ => levelRel sig ι m) s (fun i => rs (i + 1)) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ (f₁ d ps)) S' ∧ S' o₁ o₂ := by
  cases h with
  | recursive hrs => rw [hr] at hrs; cases hrs
  | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
    obtain ⟨hA, hGo⟩ := hS
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hFv : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts =>
      have ⟨v, hv⟩ := hB ts hts
      ⟨v, hF ts hts v hv⟩
    have hEp := AbstractionRel.isPer hSp (fun ts hts =>
      have ⟨_, hv⟩ := hFv ts hts
      FieldRel.isPer hd ih hv) hBresp
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    have hA' : AbstractionRel SΘ F (f₁ d ps) (f₂ d ps) :=
      (AbstractionRel.congr_computes hSp hFv (by
        rcases hc hf₁ with h₁ | h₁
        · exact .inl h₁
        rcases hc hf₂ with h₂ | h₂
        · exact .inl h₂
        exact .inr ⟨h₁, h₂⟩)).2 hA
    have ho₁ : AbstractionRel SΘ F (o₁ d ps) (o₁ d ps) := hEp.trans hA (hEp.symm hA)
    have hfo : AbstractionRel SΘ F (f₁ d ps) (o₁ d ps) :=
      (AbstractionRel.congr_computes hSp hFv (by
        rcases hc hf₁ with h₁ | h₁
        · exact .inl h₁
        exact .inr ⟨h₁, fun _ _ => .rfl⟩)).2 ho₁
    refine ⟨fun ts us hτ => ?_, G (f₁ d ps), hG _ (hEp.trans hfo (hEp.symm hfo)),
      (hresp _ _ hfo o₁ o₂).2 hGo⟩
    have hts := (TelRel.eqSubst_iff hd hΘ (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
      (fun _ _ h => by cases h) ts us).2 hτ
    have htt := hSp.trans hts (hSp.symm hts)
    obtain ⟨v, hv⟩ := hB ts htt
    exact (hF ts htt v hv).validEqTerm hd hv (hA' ts us hts)

/-- At observations related by the equality of destructors, whose first destructor `d` is recursive,
with results equal by `R`, the equality of the terms of a type of the graph, the observations `f₁`
and `f₂` that compute as them are, for `d`, related by `R` at equal arguments, and the equality of
the destructors after `d`, at any abstraction for `d`, relates them. -/
theorem DesRel.headRec (hd : sig.Distinct) {n : Nat} {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
    {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
    {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (.cons (d := d) p q Θ B ψ ds) @θ S)
    {R : TermRel} (hr : rs 0 = some R) {v : Term 0 []}
    (hR : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) {o₁ o₂ f₁ f₂ : Observations}
    (hS : S o₁ o₂) (hf₁ : ObsEquiv sig ι s f₁ o₁) (hf₂ : ObsEquiv sig ι s f₂ o₂) :
    (∀ ts us : Args 0 [] ps, EqSubst sig ι (Context.empty.append (Θ.subst θ)) ts.toSubst us.toSubst →
      R ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)) ∧
    ∀ f, ∃ S', DesRel sig ι n (fun m _ => levelRel sig ι m) s (fun i => rs (i + 1)) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ f) S' ∧ S' o₁ o₂ := by
  cases h with
  | cons _ _ _ _ _ _ _ _ hrs => rw [hr] at hrs; cases hrs
  | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R' hrs hΘ G hG =>
    rw [hr] at hrs
    cases hrs
    obtain ⟨hA, hGo⟩ := hS
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    refine ⟨fun ts us hτ => ?_, fun f => ⟨G, hG f, hGo⟩⟩
    have hts := (TelRel.eqSubst_iff hd hΘ (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
      (fun _ _ h => by cases h) ts us).2 hτ
    refine (hR.congr_computes ?_).1 (hA ts us hts)
    rcases hc hf₁ with h₁ | h₁
    · exact .inl h₁
    rcases hc hf₂ with h₂ | h₂
    · exact .inl h₂
    exact .inr ⟨fun w => (h₁ _ w).symm, fun w => (h₂ _ w).symm⟩

-- ADE: none.
/-- At a position of a destructor `d` in destructors equal in a sort `κ` at two closed substitutions
of their scope, whose recursive destructors `rs` gives, of the instances `inst D` of the block,
observations that compute as observations related by the equality of the destructors, at the
relations of the recursive destructors that are the equalities of the instances, give results of
`d` that are equal types at equal arguments, and are, for `d`, equal terms of its result at equal
arguments: the destructors before `d` are, one by one, equal abstractions for them, and a recursive
one, on which the destructors after it do not depend, gives terms of an instance. -/
theorem Destructors.Pos.sound (hd : sig.Distinct) {κ : Universe 0} {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hpos : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {θ₁ θ₂ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁ θ₂ → {rsR : Nat → Option TermRel} →
      (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R v, rsR i = some R ∧ Computesι sig ι ((inst D).subst θ₁) v ∧
        FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality v R) →
      (∀ i D, rs i = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι ((inst D).subst θ₁) ((inst D).subst θ₂) (.sort κ₁)) →
      {S : ObsRel} →
      DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality rsR ds @θ₁ S →
      {o₁ o₂ f₁ f₂ : Observations} → S o₁ o₂ → ObsEquiv sig ι κ.quality f₁ o₁ →
      ObsEquiv sig ι κ.quality f₂ o₂ →
      (∃ κ₁, ∀ ts us : Args 0 [] ps,
        EqSubst sig ι (Context.empty.append (Θ.subst (hpos.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι (B.subst (Subst.append (hpos.obsSubst f₁ θ₁) ts.toSubst))
          (B.subst (Subst.append (hpos.obsSubst f₂ θ₂) us.toSubst)) (.sort κ₁)) ∧
      ∀ ts us : Args 0 [] ps,
        EqSubst sig ι (Context.empty.append (Θ.subst (hpos.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)
          (B.subst (Subst.append (hpos.obsSubst f₁ θ₁) ts.toSubst))
  | _, _, _, _, _, B, _, .here, inst, rs, θ₁, θ₂, hv, rsR, hN, hR, hI, _, hS, _, _, _, _, ho, hf₁,
      hf₂ => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    split at hv
    · rename_i hr
      obtain ⟨⟨κ₁, -, hB⟩, -⟩ := hv
      exact ⟨⟨κ₁, fun ts us hτ => hB _ _ hτ⟩, (DesRel.head hd hS (hN 0 hr) ho hf₁ hf₂).1⟩
    · rename_i D hr
      obtain ⟨rfl, -⟩ := hv
      obtain ⟨R, v, hR0, hcv, hFv⟩ := hR 0 D hr
      obtain ⟨κ₁, hI0⟩ := hI 0 D hr
      have hhead := (DesRel.headRec hd hS hR0 hFv ho hf₁ hf₂).1
      refine ⟨⟨κ₁, fun ts us _ => ?_⟩, fun ts us hτ => ?_⟩
      · rw [Term.subst_append_rename_weakenN, Term.subst_append_rename_weakenN]
        exact hI0
      · rw [Term.subst_append_rename_weakenN]
        exact hFv.validEqTerm hd hcv (hhead ts us hτ)
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (Θ' := Θ') (B' := B') (ψ' := ψ') h, inst,
      rs, θ₁, θ₂, hv, rsR, hN, hR, hI, _, hS, _, _, f₁, f₂, ho, hf₁, hf₂ => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    have hsw : ∀ (θ : Subst 0 [] _) (f : Term 0 (Scope.extend [] ps'.length)) D,
        ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ f) =
          (inst D).subst θ := fun θ f D => Term.subst_rename_of (fun _ => rfl) _
    have hN' : ∀ i, rs (i + 1) = none → rsR (i + 1) = none := fun i => hN (i + 1)
    have hR' : ∀ (f : Term 0 (Scope.extend [] ps'.length)) i D, rs (i + 1) = some D → ∃ R v,
        rsR (i + 1) = some R ∧ Computesι sig ι
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ f)) v ∧
        FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality v R :=
      fun f i D hi => by rw [hsw]; exact hR (i + 1) D hi
    have hI' : ∀ (f₁ f₂ : Term 0 (Scope.extend [] ps'.length)) i D, rs (i + 1) = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ f₁))
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₂ f₂))
          (.sort κ₁) :=
      fun f₁ f₂ i D hi => by rw [hsw, hsw]; exact hI (i + 1) D hi
    split at hv
    · rename_i hr
      obtain ⟨-, hds⟩ := hv
      obtain ⟨hhead, S', hS', ho'⟩ := DesRel.head hd hS (hN 0 hr) ho hf₁ hf₂
      have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ'.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι ((f₁ d' ps').subst τ₁) ((f₂ d' ps').subst τ₂)
            (B'.subst (Subst.append θ₁ τ₁)) := fun τ₁ τ₂ hτ => by
        obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) ts.toSubst @τ₁ :=
          ⟨_, Subst.args_toSubst ps' τ₁⟩
        obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) us.toSubst @τ₂ :=
          ⟨_, Subst.args_toSubst ps' τ₂⟩
        exact hhead ts us hτ
      exact h.sound hd (hds _ _ hcond) hN' (hR' _) (hI' _ _) hS' ho' hf₁ hf₂
    · rename_i D hr
      obtain ⟨-, hds⟩ := hv
      obtain ⟨R, v, hR0, -, hFv⟩ := hR 0 D hr
      obtain ⟨-, hrest⟩ := DesRel.headRec hd hS hR0 hFv ho hf₁ hf₂
      obtain ⟨S', hS', ho'⟩ := hrest (f₁ d' ps')
      exact h.sound hd (hds (f₁ d' ps') (f₂ d' ps')) hN' (hR' _) (hI' _ _) hS' ho' hf₁ hf₂

/-- The equality of the canonical terms of an instance of a codata type of `Σ` is, at the equality
`S` of the destructors of the types of its block that the graph gives, `(eq_ν)` for an instance in
a universe, and the truth `(true_ν)` of the instance for a proposition, in a signature whose names
are distinct. -/
theorem HasEq.instCodata_inv (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {R : TermRel} (hR : HasEq sig ι (.inst D qs ls ps as) R) :
    ((decl.sort (.ofLists qs ps hq hp)).quality = .type ∧
      ∃ S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
        (∀ X, ∀ T' ∈ decl.codataTypes,
          DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
            (fun m _ => levelRel sig ι m) .type
            (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
              fun D' => (X D').computed sig ι)
            ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S X T')) ∧
        R = CodataType.blockRel decl.codataTypes S D) ∨
    ((decl.sort (.ofLists qs ps hq hp)).quality = .prop ∧
      ∃ S : (Name → Prop) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
        (∀ B, ∀ T' ∈ decl.codataTypes,
          DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
            (fun m _ => levelRel sig ι m) .prop
            (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
              fun D' => fun _ _ => B D')
            ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S B T')) ∧
        ∀ t u, R t u ↔ CodataType.blockTruth decl.codataTypes S D) := by
  cases hR with
  | univ n hU =>
    have hU' := levelRel_univ_iff.1 hU
    cases hU' with
    | data h' _ _ _ hv => exact (hd.inst_data_codata h' h hv.symm).elim
    | codata h' _ _ _ hv hs hn S hS =>
      have hD := congrArg (fun t : Term 0 [] => match t with | .inst D .. => D | _ => "") hv
      dsimp only at hD
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h (hD ▸ h')
      cases hT
      cases hv
      subst hn
      exact .inl ⟨hs, S, fun X T' hT' => hs ▸ hS X T' hT', rfl⟩
  | prop n b hP hRb =>
    have hP' := levelRel_prop_iff.1 hP
    cases hP' with
    | data h' _ _ _ hv => exact (hd.inst_data_codata h' h hv.symm).elim
    | codata h' _ _ _ hv hs hn S hS =>
      have hD := congrArg (fun t : Term 0 [] => match t with | .inst D .. => D | _ => "") hv
      dsimp only at hD
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h (hD ▸ h')
      cases hT
      cases hv
      subst hn
      exact .inr ⟨hs, S, fun B T' hT' => hs ▸ hS B T' hT', hRb⟩

/-- The observation of a closed term, substituted by closed arguments, is the observation by the
destructor applied to them. -/
theorem Term.observation_subst_args {Δ : Scope} (D : Name) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 [] Δ) (t : Term 0 []) (d : Name)
    {ps' : List Parameter} (ts : Args 0 [] ps') :
    (t.observation D qs ls ps as d ps').subst ts.toSubst = .obs D qs ls ps as t d ts.terms := by
  rw [← Term.instantiate_eq_subst, Term.observation_instantiate]

/-- The observations of a closed term that computes to a corecursor compute as the observations of
the corecursor, at the instance it carries. -/
theorem ObsEquiv.of_computes (hd : sig.Distinct) {s : Quality} {Δ : Scope} {D D' : Name}
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] Δ}
    {t w : Term 0 []} {o : Observations} (ht : Computesι sig ι t w)
    (hw : w.CorecObservations D' o) : ObsEquiv sig ι s (t.observation D qs ls ps as) o := by
  obtain ⟨r, qs', ls', ps', Δ', as', ss, Ss, gs, rfl, rfl⟩ := hw
  refine .inr fun d xs τ v => ?_
  obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] xs,
      @Eq (Subst 0 [] (Scope.extend [] xs.length)) ts.toSubst @τ :=
    ⟨_, Subst.args_toSubst xs τ⟩
  rw [Term.observation_subst_args, Term.observation_subst_args,
    Computesι.redStar_iff hd (RedStar.obs ht.1)]
  exact ⟨Computesι.obs_corec_iff, Computesι.obs_corec_iff⟩

-- ADE: none.
/-- `(d_≡)`, closed: the observations of two equal closed terms of an instance of a codata type of
`Σ`, whose type declaration is meaningful, at equal arguments of its parameters, by a destructor at
equal arguments of its telescope, are equal terms of its result, and their results are equal
types. -/
theorem ValidEqTerm₀.obs (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {d : Name} {p q : Grade}
    {ps' : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps'}
    {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {a₁ a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      a₁.toSubst a₂.toSubst)
    {t₁ t₂ : Term 0 []} (ht : ValidEqTerm₀ sig ι t₁ t₂ (.inst D qs ls ps a₁))
    {bs₁ bs₂ : Args 0 [] ps'}
    (hbs : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))) bs₁.toSubst bs₂.toSubst) :
    ValidEqTerm₀ sig ι (.obs D qs ls ps a₁ t₁ d bs₁.terms) (.obs D qs ls ps a₂ t₂ d bs₂.terms)
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))).instantiate
            bs₁) ∧
      ValidEqType₀ sig ι
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))).instantiate
            bs₁)
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₂.observation D qs ls ps a₂) a₂.toSubst))).instantiate
            bs₂) := by
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm h.2.1 ρ).2 _ _ hθ
  have hn := Level.closedValue_subst_equiv hls (decl.sort I).level
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : InstanceArgs 0 [] decl.scope → Name → Term 0 [] := fun a D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst a.toSubst
  have hX : ∀ a D', Term.LevelEquiv (X a D') (.inst D' qs ls ps a) := fun a D' =>
    decl.blockInstance_atLevels_subst hq hl hp a D'
  have hcX : ∀ a D', Computesι sig ι (X a D') (X a D') := fun _ _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hXeq : ∀ D' ∈ decl.names, ∃ κ₁, ValidEqTerm₀ sig ι (X a₁ D') (X a₂ D') (.sort κ₁) :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1 hD'
      exact ⟨_, (ValidEqTerm₀.instCodata hd ⟨h.1, hT', rfl⟩ hv hq hl hp hadm has).levelEquiv
        (hX a₁ _).symm (hX a₂ _).symm (Term.LevelEquiv.refl _)⟩
  -- The equality of the instance.
  have hI : Computesι sig ι (.inst D qs ls ps a₁) (.inst D qs ls ps a₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht.1.2
  cases Computesι.det hd hcv hI
  -- Observations related by the equality of the destructors, at the equalities of the instances
  -- for the recursive destructors, which those of the terms compute as.
  have hobs : ∃ (rsR : Nat → Option TermRel) (S : ObsRel) (o₁ o₂ : Observations),
      DesRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        ((decl.sort I).atLevels ρ).quality rsR ((T.body I).atLevels ρ) a₁.toSubst S ∧
      S o₁ o₂ ∧
      ObsEquiv sig ι (decl.sort I).quality (t₁.observation D qs ls ps a₁) o₁ ∧
      ObsEquiv sig ι (decl.sort I).quality (t₂.observation D qs ls ps a₂) o₂ ∧
      (∀ i, (T.body I).recursionAt decl.names i = none → rsR i = none) ∧
      (∀ i D', (T.body I).recursionAt decl.names i = some D' → ∃ R v, rsR i = some R ∧
        Computesι sig ι (X a₁ D') v ∧
        FieldRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
          ((decl.sort I).atLevels ρ).quality v R) := by
    have hlev : ∀ {s : Quality} {rs : Nat → Option TermRel} {S : ObsRel},
        DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
          ((T.body I).substLevels L) a₁.toSubst S →
        DesRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m) s
          rs ((T.body I).atLevels ρ) a₁.toSubst S := fun hS => by
      have e : ((decl.sort I).atLevels ρ).level.closedValue =
          ((decl.sort I).level.subst L).closedValue := hn
      rw [e]
      exact DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
        (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
        (Subst.LevelEquiv.refl _)
    have hF : ∀ {s : Quality} {R' : TermRel} {D' : Name},
        FieldRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s
          (.inst D' qs ls ps a₁) R' →
        FieldRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
          s (X a₁ D') R' := fun hF' => by
      have e : ((decl.sort I).atLevels ρ).level.closedValue =
          ((decl.sort I).level.subst L).closedValue := hn
      rw [e]
      exact FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hF' (hX a₁ _).symm
    rcases HasEq.instCodata_inv hd h hq hl hp hR with ⟨hs, S, hS, rfl⟩ | ⟨hs, S, hS, hRb⟩
    · have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
          (.inst D qs ls ps a₁) (CodataType.blockRel decl.codataTypes S D) :=
        levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
      have hnp : ¬ ComputesToProp sig ι (.inst D qs ls ps a₁) := fun ⟨v, hv, k, b, hk⟩ => by
        cases Computesι.det hd hI hv
        exact HasEq.univ_not_prop hd hU₀ hk
      obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht.2.1 hnp
      cases Computesι.det hd hI hv'
      have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
          ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
        fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
          fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
      have hrel' := (HasEq.unique hd hR' hR w₁ w₂).1 hrel
      rw [← h.2.2] at hrel'
      obtain ⟨o₁, o₂, hc₁, hc₂, ho⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel'
      refine ⟨_, _, o₁, o₂, hlev (hs ▸ hS _ T h.2.1), ho, ObsEquiv.of_computes hd hw₁ hc₁,
        ObsEquiv.of_computes hd hw₂ hc₂, fun i hi => by rw [hi]; rfl, fun i D' hi => ?_⟩
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
        (Destructors.recursionAt_mem hi)
      have hU : UnivRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps a₁)
          (CodataType.blockRel decl.codataTypes S T'.name) :=
        .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
      rw [hi]
      exact ⟨_, _, rfl, hcX _ _, hs ▸ hF (.univ rfl hU)⟩
    · have hP : PropRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst D qs ls ps a₁)
          (CodataType.blockTruth decl.codataTypes S D) :=
        .codata h hq hl hp rfl hs rfl S hS
      have hprop : ComputesToProp sig ι (.inst D qs ls ps a₁) :=
        ⟨_, hI, _, _, levelRel_prop_iff.2 hP⟩
      obtain ⟨v', R', hv', hR', hrel⟩ := ht.2.2 hprop
      cases Computesι.det hd hI hv'
      have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
          S B T' o₁ o₂ → S B' T' o₁ o₂ :=
        fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
          fun _ => Option.rel_map (fun D _ _ => hB D) _
      have htrue := (hRb _ _).1 ((HasEq.unique hd hR' hR _ _).1 hrel)
      rw [← h.2.2] at htrue
      obtain ⟨o, ho⟩ := CodataType.blockTruth_unfold hmono h.2.1 htrue
      refine ⟨_, _, o, o, hlev (hs ▸ hS _ T h.2.1), ho, .inl hs, .inl hs,
        fun i hi => by rw [hi]; rfl, fun i D' hi => ?_⟩
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
        (Destructors.recursionAt_mem hi)
      have hP' : PropRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps a₁)
          (CodataType.blockTruth decl.codataTypes S T'.name) :=
        .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
      rw [hi]
      exact ⟨_, _, rfl, hcX _ _, hs ▸ hF (.prop hP')⟩
  obtain ⟨rsR, S, o₁, o₂, hSρ, ho, hf₁, hf₂, hN, hRr⟩ := hobs
  obtain ⟨⟨κ₁, hBeq⟩, hres⟩ := (hpos.substLevels Lρ).sound hd hmean hN hRr
    (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi)) hSρ ho hf₁ hf₂
  -- The substitutions of the scope of the destructor, at the levels of the declaration and at the
  -- levels without variables, are the same.
  have hcE : ∀ {f : Observations} {a : InstanceArgs 0 [] decl.scope},
      Subst.LevelEquiv ((hpos.substLevels Lρ).obsSubst f a.toSubst) (hpos.obsSubst f a.toSubst) :=
    fun {f a} {_} x => by
      show Term.LevelEquiv ((hpos.substLevels Lρ).obsSubst f a.toSubst x)
        (hpos.obsSubst f a.toSubst x)
      rw [Destructors.Pos.obsSubst_posSubstLevels]
      exact Term.LevelEquiv.refl _
  have hbsρ := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
    (Telescope.LevelEquiv.subst hcE.symm
      (Telescope.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) Θ))) hbs
  have hBE : ∀ {f : Observations} {a : InstanceArgs 0 [] decl.scope}
      {τ : Subst 0 [] (Scope.extend [] ps'.length)},
      Term.LevelEquiv ((B.substLevels Lρ).subst
          (Subst.append ((hpos.substLevels Lρ).obsSubst f a.toSubst) τ))
        ((B.substLevels L).subst (Subst.append (hpos.obsSubst f a.toSubst) τ)) :=
    Term.LevelEquiv.subst (Subst.LevelEquiv.append hcE (Subst.LevelEquiv.refl _))
      (Term.substLevels_levelEquiv hls B)
  rw [Term.instantiate_eq_subst, Term.instantiate_eq_subst, Term.subst_append, Term.subst_append]
  refine ⟨?_, ?_⟩
  · have hr := hres bs₁ bs₂ hbsρ
    rw [Term.observation_subst_args, Term.observation_subst_args] at hr
    exact hr.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) hBE
  · have hB := hBeq bs₁ bs₂ hbsρ
    obtain ⟨s, l⟩ := κ₁
    cases s
    · exact (ValidEqTerm₀.univType hB).levelEquiv hBE hBE
    · exact (ValidEqTerm₀.propType hB).levelEquiv hBE hBE

-- ADE: `∘-congᵛ`, `fst-congᵛ` and `snd-congᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(d_≡)` keeps the meaning, and `(d)` with it: at equal substitutions of the context, the
observations of the terms, at the arguments of the instance and of the telescope substituted, are
the closed observations of `ValidEqTerm₀.obs`, since the observations of the term substituted are
those of the substituted term; the result is a type, since the results at two substitutions are
both equal to the result of the second observation at the second substitution; and the second
observation at levels of the same values is the same term up to its levels. -/
theorem ValidEqTermΓ.obs {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {d : Name} {p q : Grade}
    {ps' : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps'}
    {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) {t₁ t₂ : Term 0 Γ}
    (ht : ValidEqTermΓ sig ι ctx t₁ t₂ (.inst D qs ls₁ ps as₁)) {bs₁ bs₂ : Args 0 Γ ps'}
    (hbs : ValidEqArgsΓ sig ι ctx bs₁ bs₂ ((Θ.substLevels (ls₁.getFin hl₁)).subst
      (hpos.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))) :
    ValidEqTermΓ sig ι ctx (.obs D qs ls₁ ps as₁ t₁ d bs₁.terms)
      (.obs D qs ls₂ ps as₂ t₂ d bs₂.terms)
      (((B.substLevels (ls₁.getFin hl₁)).subst
        (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))).instantiate
          bs₁) := by
  obtain ⟨h', hv⟩ := hent.hasCodataType h
  have hctx := has.1
  have hd := hctx.distinct
  -- The scope of the destructor, substituted, is that of the observations of the terms substituted.
  have hc : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope) {a}
      (x : Var Ξ a), ((hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst) x).subst
        (Subst.liftN a.params.length σ) =
        hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ)) (as.subst σ).toSubst x :=
    fun σ t as => hpos.obsSubst_subst σ
      (fun d ps' => Term.observation_subst σ D qs ls₁ ps as t d ps')
      (InstanceArgs.toSubst_subst σ as)
  have hΘ : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope),
      ((Θ.substLevels (ls₁.getFin hl₁)).subst
        (hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst)).subst σ =
      (Θ.substLevels (ls₁.getFin hl₁)).subst
        (hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ)) (as.subst σ).toSubst) :=
    fun σ t as => Telescope.subst_subst_of (hc σ t as) _
  have hA : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope)
      (bs : Args 0 Γ ps'),
      (((B.substLevels (ls₁.getFin hl₁)).subst
        (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst))).instantiate
          bs).subst σ =
      ((B.substLevels (ls₁.getFin hl₁)).subst (Subst.liftN _
        (hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ))
          (as.subst σ).toSubst))).instantiate (bs.subst σ) :=
    fun σ t as bs => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _ (hc σ t as))]
  have hcl := fun σ₁ σ₂ (hσ : EqSubst sig ι ctx σ₁ σ₂) => by
    have hbs' := hbs.2 σ₁ σ₂ hσ
    rw [hΘ] at hbs'
    exact ValidEqTerm₀.obs hd h' hv hq hl₁ hp hadm hpos (has.2 σ₁ σ₂ hσ) (ht.2 σ₁ σ₂ hσ) hbs'
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [hA, hA]
    exact (hcl σ₁ σ₂ hσ).2.trans (hcl σ₂ σ₂ (hσ.right hctx)).2.symm
  · rw [hA]
    simp only [Term.subst, ← Args.terms_subst]
    exact (hcl σ₁ σ₂ hσ).1.levelEquiv (Term.LevelEquiv.refl _)
      (.obs D qs ps d (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _)
        (Term.LevelEquiv.refl _) (Terms.LevelEquiv.refl _))
      (Term.LevelEquiv.refl _)

/-! ## Corecursors

A corecursor is a canonical term of the instance it carries, and two corecursors of a codata type of
a meaningful declaration are equal when their observations are, destructor by destructor: the
destructors before the one observed are, in its telescope and its result, the observations of the
first corecursor, from the first destructor to the last one, as the equality of the destructors
reads them.
An observation of a corecursor computes, by `(β_⟶)`, as the branch of its destructor at the state
and the arguments, which the premises of `(corec)` make equal terms of the result of the
destructor, whose telescope and result, over the state, observe the corecursor from the state:
the corecursor itself, once the state is substituted.
On a proposition, the observations of the corecursor, related to themselves, make it true. -/

-- ADE: none.
/-- Observations equal, destructor by destructor, at equal arguments, are related by the equality
of the destructors, at instantiated levels, at relations of the recursive destructors that the
equalities of the instances of the block relate: the destructors before each destructor being the
observations `o₁`, as the equality of the destructors reads them, from the first one, and the
results of a recursive destructor being terms of an instance, as the meaning of the destructors
says. -/
theorem DesRel.of_obs (hd : sig.Distinct) {n : Nat} {s : Quality} {κ : Universe 0} {k' : Nat}
    (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {inst : Name → Term 0 Γ} →
      {rs : Nat → Option Name} → {θ θ' : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs (ds.substLevels L) θ θ' →
      {rsR : Nat → Option TermRel} → (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R v, rsR i = some R ∧ Computesι sig ι ((inst D).subst θ) v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) →
      {S : ObsRel} →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rsR (ds.substLevels L) @θ S →
      {o₁ o₂ : Observations} →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o₁ θ)))
          ts.toSubst us.toSubst →
        ValidEqTerm₀ sig ι ((o₁ d ps).subst ts.toSubst) ((o₂ d ps).subst us.toSubst)
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o₁ θ) ts.toSubst))) →
      S o₁ o₂
  | _, _, .nil, _, _, _, _, _, _, _, _, _, h, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q Θ B ψ ds, inst, rs, θ, θ', hm, rsR, hN, hR, _, h, o₁, o₂,
      hv => by
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    rw [Destructors.substLevels, ValidEqDestructors₀] at hm
    obtain ⟨-, hm⟩ := hm
    have hsw : ∀ (f : Term 0 (Scope.extend [] ps.length)) D,
        ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ f) =
          (inst D).subst θ := fun f D => Term.subst_rename_of (fun _ => rfl) _
    have hR' : ∀ (f : Term 0 (Scope.extend [] ps.length)) i D, rs (i + 1) = some D → ∃ R v,
        rsR (i + 1) = some R ∧ Computesι sig ι
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ f)) v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R :=
      fun f i D hi => by rw [hsw]; exact hR (i + 1) D hi
    have hv' : ∀ (d' : Name) (p' q' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope k' Ξ' ps') (B' : Term k' (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership ps'.length) (hpos : ds.Pos d' p' q' Ξ' Θ' B' ψ')
        (ts us : Args 0 [] ps'),
        EqSubst sig ι (Context.empty.append ((Θ'.substLevels L).subst
          (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι ((o₁ d' ps').subst ts.toSubst) ((o₂ d' ps').subst us.toSubst)
          ((B'.substLevels L).subst (Subst.append
            (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))) ts.toSubst)) :=
      fun d' p' q' ps' Ξ' Θ' B' ψ' hpos ts us hτ =>
        hv d' p' q' ps' Ξ' Θ' B' ψ' (.there hpos) ts us hτ
    split at hm
    · rename_i hr
      obtain ⟨-, hds⟩ := hm
      cases h with
      | recursive hrs => rw [hN 0 hr] at hrs; cases hrs
      | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
        have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
        have hEp := AbstractionRel.isPer hSp (fun ts hts =>
          have ⟨v, hv'⟩ := hB ts hts
          FieldRel.isPer hd ih (hF ts hts v hv')) hBresp
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        have hA : AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) := fun ts us hts => by
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv'⟩ := hB ts htt
          exact (hF ts htt v hv').of_validEqTerm hv' (hv d p q ps _ Θ B ψ .here ts us
            ((hT ts us).1 hts))
        have hff := hEp.trans hA (hEp.symm hA)
        have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst θ))
            τ₁ τ₂ → ValidEqTerm₀ sig ι ((o₁ d ps).subst τ₁) ((o₁ d ps).subst τ₂)
              ((B.substLevels L).subst (Subst.append θ τ₁)) := fun τ₁ τ₂ hτ => by
          obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
            ⟨_, Subst.args_toSubst ps τ₁⟩
          obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
            ⟨_, Subst.args_toSubst ps τ₂⟩
          have hts := (hT ts us).2 hτ
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv'⟩ := hB ts htt
          exact (hF ts htt v hv').validEqTerm hd hv' (hff ts us hts)
        exact ⟨hA, DesRel.of_obs hd L ds (hds _ _ hcond) (fun i => hN (i + 1)) (hR' _)
          (hG _ hff) hv'⟩
    · rename_i D hr
      obtain ⟨hBD, hds⟩ := hm
      obtain ⟨R, v, hR0, hcv, hFv⟩ := hR 0 D hr
      cases h with
      | cons _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R' hrs hΘ G hG =>
        rw [hR0] at hrs
        cases hrs
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        refine ⟨fun ts us hts => ?_, DesRel.of_obs hd L ds (hds (o₁ d ps) (o₁ d ps))
          (fun i => hN (i + 1)) (hR' _) (hG _) hv'⟩
        have he := hv d p q ps _ Θ B ψ .here ts us ((hT ts us).1 hts)
        have e : (B.substLevels L).subst (Subst.append θ ts.toSubst) = (inst D).subst θ := by
          rw [hBD, Term.subst_append_rename_weakenN]
        exact hFv.of_validEqTerm hcv (e ▸ he)

-- ADE: none.
/-- `(corec)`, closed: two corecursors of an instance of a codata type of `Σ`, whose type
declaration is meaningful, at the same levels and at equal arguments of its parameters, whose
observations by each destructor, at equal arguments of its telescope, are equal terms of its
result, are equal terms of the instance: canonical terms that `(eq_ν)` relates, since the
relation that `(eq_d)` gives them at `(eq_ν)` is consistent with the clauses of the destructors, or
proofs of a proposition that their observations make true. -/
theorem ValidEqTerm₀.corec (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {a₁ a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      a₁.toSubst a₂.toSubst)
    {r₁ r₂ : Grade} {ss₁ ss₂ : Terms 0 []} {Ss₁ Ss₂ : States 0 []} {gs₁ gs₂ : CorecBranches 0 []}
    (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst ((Term.corec r₁ D qs ls ps a₁ ss₁ Ss₁ gs₁).observation D qs ls ps a₁)
          a₁.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (.obs D qs ls ps a₁ (.corec r₁ D qs ls ps a₁ ss₁ Ss₁ gs₁) d ts.terms)
        (.obs D qs ls ps a₂ (.corec r₂ D qs ls ps a₂ ss₂ Ss₂ gs₂) d us.terms)
        ((B.substLevels (ls.getFin hl)).subst (Subst.append
          (hpos.obsSubst ((Term.corec r₁ D qs ls ps a₁ ss₁ Ss₁ gs₁).observation D qs ls ps a₁)
            a₁.toSubst) ts.toSubst))) :
    ValidEqTerm₀ sig ι (.corec r₁ D qs ls ps a₁ ss₁ Ss₁ gs₁) (.corec r₂ D qs ls ps a₂ ss₂ Ss₂ gs₂)
      (.inst D qs ls ps a₁) := by
  have hI : ValidEqTerm₀ sig ι (.inst D qs ls ps a₁) (.inst D qs ls ps a₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩) :=
    ValidEqTerm₀.instCodata hd h hv hq hl hp hadm has
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hn := TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm hT ρ).2 _ _ hθ
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the first arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst a₁.toSubst
  have hX : ∀ D', Term.LevelEquiv (X D') (.inst D' qs ls ps a₁) := fun D' =>
    decl.blockInstance_atLevels_subst hq hl hp a₁ D'
  have hcX : ∀ D', Computesι sig ι (X D') (X D') := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The observations at the levels without variables.
  let c₁ : Term 0 [] := .corec r₁ T.name qs ls ps a₁ ss₁ Ss₁ gs₁
  let c₂ : Term 0 [] := .corec r₂ T.name qs ls ps a₂ ss₂ Ss₂ gs₂
  have hobs' : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body I).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels Lρ).subst
        (hpos.obsSubst (c₁.observation T.name qs ls ps a₁) a₁.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (((c₁.observation T.name qs ls ps a₁) d ps').subst ts.toSubst)
        (((c₂.observation T.name qs ls ps a₂) d ps').subst us.toSubst)
        ((B.substLevels Lρ).subst (Subst.append
          (hpos.obsSubst (c₁.observation T.name qs ls ps a₁) a₁.toSubst) ts.toSubst)) :=
      fun d p q ps' Ξ Θ B ψ hpos ts us hτ => by
    rw [Term.observation_subst_args, Term.observation_subst_args]
    have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hls Θ))) hτ
    exact (hobs d p q ps' Ξ Θ B ψ hpos ts us hτ').levelEquiv (Term.LevelEquiv.refl _)
      (Term.LevelEquiv.refl _) (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
  have hlev : ∀ {s : Quality} {rs : Nat → Option TermRel} {S : ObsRel},
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels L) a₁.toSubst S →
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels Lρ) a₁.toSubst S := fun hS =>
    DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  have hw : Computesι sig ι (.inst T.name qs ls ps a₁) (.inst T.name qs ls ps a₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  have hct : ∀ (r : Grade) (a : InstanceArgs 0 [] decl.scope) (ss : Terms 0 []) (Ss : States 0 [])
      (gs : CorecBranches 0 []), Computesι sig ι (.corec r T.name qs ls ps a ss Ss gs)
        (.corec r T.name qs ls ps a ss Ss gs) :=
    fun _ _ _ _ _ => ⟨.refl _, .corec _ _ _ _ _ _ _ _ _⟩
  cases hs : (decl.sort I).quality
  · rw [hs] at hI
    obtain ⟨S, hS, hU⟩ := hv.codataUnivRel hd hdecl hq hl hp hadm has hs
    have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
        ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
      fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
        fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
    have hU' : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
        (.inst T.name qs ls ps a₁) (CodataType.blockRel decl.codataTypes S T.name) :=
      levelRel_univ_iff.2 (hU T hT).1
    have hrel : CodataType.blockRel decl.codataTypes S T.name c₁ c₂ :=
      CodataType.blockRel_fold hmono hn hT ⟨_, _, ⟨r₁, qs, ls, ps, _, a₁, ss₁, Ss₁, gs₁, rfl, rfl⟩,
        ⟨r₂, qs, ls, ps, _, a₂, ss₂, Ss₂, gs₂, rfl, rfl⟩,
        DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
          (fun i D' hi => by
            obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
              (Destructors.recursionAt_mem hi)
            rw [hi]
            exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
              (.univ rfl (hU T' hT').1) (hX _).symm⟩)
          (hlev (hS (CodataType.blockRel decl.codataTypes S) T hT)) hobs'⟩
    refine ⟨(ValidEqTerm₀.univType hI).left,
      fun _ => ⟨_, _, _, _, hw, hct _ _ _ _ _, hct _ _ _ _ _, .univ _ hU', hrel⟩,
      fun ⟨v, hv', _, _, hP⟩ => ?_⟩
    cases Computesι.det hd hw hv'
    exact (HasEq.univ_not_prop hd hU' hP).elim
  · rw [hs] at hI
    obtain ⟨S, hS, hP⟩ := hv.codataPropRel hd hdecl hq hl hp hadm has hs
    have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
        S B T' o₁ o₂ → S B' T' o₁ o₂ :=
      fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
        fun _ => Option.rel_map (fun D _ _ => hB D) _
    have hP' : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).prop
        (.inst T.name qs ls ps a₁) (CodataType.blockTruth decl.codataTypes S T.name) :=
      levelRel_prop_iff.2 (hP T hT).1
    have hS₁ := DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
      (fun i D' hi => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT
          (Destructors.recursionAt_mem hi)
        rw [hi]
        exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
          (.prop (hP T' hT').1) (hX _).symm⟩)
      (hlev (hS (CodataType.blockTruth decl.codataTypes S) T hT)) hobs'
    have hSp := DesRel.isPer hd ih (fun i x hx => by
      cases hr : (T.body I).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩)
      (hlev (hS (CodataType.blockTruth decl.codataTypes S) T hT))
    have htrue : CodataType.blockTruth decl.codataTypes S T.name :=
      CodataType.blockTruth_fold hmono hn hT ⟨_, hSp.trans hS₁ (hSp.symm hS₁)⟩
    refine ⟨(ValidEqTerm₀.propType hI).left, fun hn => absurd ⟨_, hw, _, _, hP'⟩ hn,
      fun _ => ⟨_, fun _ _ => CodataType.blockTruth decl.codataTypes S T.name, hw,
        .prop _ _ hP' fun _ _ => .rfl, htrue⟩⟩

/-- The scope of a destructor, over the state of a corecursor, at the corecursor from the state,
substituted by a closed substitution of the context followed by closed arguments of the state, is
the scope of the destructor at the corecursor from these arguments. -/
theorem Destructors.Pos.obsSubst_corecAt {k' : Nat} {Γ Δ : Scope} {d : Name} {p q : Grade}
    {ps₁ : List Parameter} {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope}
    {Θ : Telescope k' Ξ ps₁} {B : Term k' (Ξ.extend ps₁.length)} {ψ : ResultOwnership ps₁.length}
    (hpos : ds.Pos d p q Ξ Θ B ψ) (σ : Subst 0 [] Γ) (r : Grade) (D : Name) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 Γ Δ) (Ss : States 0 Γ)
    (gs : CorecBranches 0 Γ) {ps' : List Parameter} (ss : Args 0 [] ps')
    (hΔ : ∀ {a} (x : Var Δ a), ((as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) = (as.subst σ).toSubst x) :
    ∀ {a} (x : Var Ξ a),
      (hpos.obsSubst ((Term.corecAt r D qs ls ps as Ss gs ps').observation D qs ls ps
          (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) =
      hpos.obsSubst ((Term.corec r D qs ls ps (as.subst σ) ss.terms (Ss.subst σ)
        (gs.subst σ)).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
  hpos.obsSubst_subst (Subst.append σ ss.toSubst) (fun d' ps'' => by
    rw [Term.observation_subst, Term.corecAt_subst_append,
      InstanceArgs.subst_rename_of (ξ := Ren.weakenN ps'.length) (θ' := σ)
        (fun y => Subst.append_weakenN σ ss.toSubst y)])
    hΔ

-- ADE: none.
/-- The arguments of an instance, renamed under the variables of a state, substituted by a closed
substitution followed by closed arguments of the state, are the arguments substituted, as a
substitution of the parameters. -/
theorem InstanceArgs.toSubst_rename_subst_append {Γ Δ : Scope} (σ : Subst 0 [] Γ)
    (as : InstanceArgs 0 Γ Δ) {ps' : List Parameter} (ss : Args 0 [] ps') {a : Scope.Entry}
    (x : Var Δ a) :
    ((as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) = (as.subst σ).toSubst x := by
  rw [InstanceArgs.toSubst_subst,
    InstanceArgs.subst_rename_of (ξ := Ren.weakenN ps'.length) (θ' := σ)
      (fun y => Subst.append_weakenN σ ss.toSubst y)]

-- ADE: none.
/-- An observation of a corecursor of a codata type of `Σ`, whose type declaration is meaningful,
from a state equal to a second one, with a branch equal to a second one, as the premises of
`(corec)` and of `(corec_≡)` make them meaningful, at equal substitutions `σ₁` and `σ₂` of the
context and equal arguments of the telescope of its destructor, is equal to the second branch at
the second substitution, the second state and the second arguments, as a term of the result of the
destructor: it computes, by `(β_⟶)`, to the first branch at the first ones, which the equality of
the branches makes equal to it. -/
theorem ValidEqTerm₀.obs_corec {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 Γ decl.scope} {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ}
    {h' i : Nat} {ps' : List Parameter} {S : Telescope 0 Γ ps'} {ss₁ ss₂ : Args 0 Γ ps'}
    (hss : ValidEqArgsΓ sig ι ctx ss₁ ss₂ S) (hi : decl.codataCases[i]? = some (h', T, d))
    {p q : Grade} {ps₁ : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
    {ψ : ResultOwnership ps₁.length} (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {g₁ g₂ : Term 0 ((Γ.extend ps'.length).extend ps₁.length)}
    (hg : gs.get i = some ⟨0, ps'.length, ps₁.length, g₁⟩)
    (hnr : B.blockName decl.names = none)
    (hgv : ValidEqTermΓ sig ι ((ctx.append S).append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corecAt r T.name qs ls ps as Ss gs ps').observation T.name qs ls
        ps (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst)))
      g₁ g₂
      (Term.branchResult decl.names B
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted)
        ((Ss.rename (Ren.weakenN ps'.length)).rename (Ren.weakenN ps₁.length))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hpos.obsSubst ((Term.corecAt r T.name qs ls ps as Ss gs ps').observation T.name qs ls
            ps (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst)))))
    {σ₁ σ₂ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ₁ σ₂) {ts us : Args 0 [] ps₁}
    (hts : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corec r D qs ls ps (as.subst σ₁) (ss₁.subst σ₁).terms (Ss.subst σ₁)
        (gs.subst σ₁)).observation D qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst)))
      ts.toSubst us.toSubst) :
    ValidEqTerm₀ sig ι
      (.obs D qs ls ps (as.subst σ₁) (.corec r D qs ls ps (as.subst σ₁) (ss₁.subst σ₁).terms
        (Ss.subst σ₁) (gs.subst σ₁)) d ts.terms)
      (g₂.subst (Subst.append (Subst.append σ₂ (ss₂.subst σ₂).toSubst) us.toSubst))
      ((B.substLevels (ls.getFin hl)).subst (Subst.append
        (hpos.obsSubst ((Term.corec r D qs ls ps (as.subst σ₁) (ss₁.subst σ₁).terms (Ss.subst σ₁)
          (gs.subst σ₁)).observation D qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst)
        ts.toSubst)) := by
  simp only [Term.branchResult, hnr] at hgv
  obtain ⟨h₀, -⟩ := hent.hasCodataType h
  have hd := hss.1.distinct
  have hD : T.name = D := h.2.2
  subst hD
  -- The scope of the destructor at the first state substituted.
  have hc := fun (a : Scope.Entry) (x : Var Ξ a) =>
    hpos.obsSubst_corecAt σ₁ r T.name qs ls ps as Ss gs (ss₁.subst σ₁)
      (InstanceArgs.toSubst_rename_subst_append σ₁ as (ss₁.subst σ₁)) x
  -- The context of the branch at the substitutions and the states substituted.
  have hstate : EqSubst sig ι (ctx.append S) (Subst.append σ₁ (ss₁.subst σ₁).toSubst)
      (Subst.append σ₂ (ss₂.subst σ₂).toSubst) :=
    (EqSubst.append_append_iff ctx S _ _ _ _).2 ⟨hσ, hss.2 σ₁ σ₂ hσ⟩
  have hτ := (EqSubst.append_append_iff (ctx.append S) _ _ _ _ _).2
    ⟨hstate, by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hts⟩
  have hb := hgv.2 _ _ hτ
  conv at hb =>
    arg 5
    rw [← Term.subst_append, Term.subst_subst_of (Subst.liftN_subst_of _ (fun x => hc _ x)),
      Term.subst_append]
  -- The observation computes to the first branch at the first substitution.
  have hred : Red (sig.interpret ι)
      (.obs T.name qs ls ps (as.subst σ₁) (.corec r T.name qs ls ps (as.subst σ₁)
        (ss₁.subst σ₁).terms (Ss.subst σ₁) (gs.subst σ₁)) d ts.terms)
      (g₁.subst (Subst.append (Subst.append σ₁ (ss₁.subst σ₁).toSubst) ts.toSubst)) := by
    have he : g₁.subst (Subst.append (Subst.append σ₁ (ss₁.subst σ₁).toSubst) ts.toSubst) =
        Term.observed decl.names ((T.body (.ofLists qs ps hq hp)).resultName decl.names d) r qs ls
          ps (as.subst σ₁) (Ss.subst σ₁) (gs.subst σ₁)
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
          (((T.body (.ofLists qs ps hq hp)).resultConstant d).getD .unrestrictedUnrestricted)
          (g₁.subst (Subst.append (Subst.append σ₁ (ss₁.subst σ₁).toSubst) ts.toSubst)) := by
      rw [hpos.resultName decl.names (hd.destructors_nodup h₀), hnr]
      rfl
    rw [he]
    exact .beta (List.mem_map_of_mem (f := Entry.interpret ι) h₀.1) hi rfl hq hl hp
      (CorecBranches.get_subst σ₁ hg) (Term.instantiateTerms₂_subst_append σ₁ g₁ _ _)
  exact (ValidEqTerm₀.red_iff hd hred).2 hb

-- ADE: none.
/-- The branches `gs₁` and `gs₂` of two corecursors are equal terms of the results of their
destructors, as `(corec_≡)` premises them, over the states `Ss` and the corecursors of the first
branches: the premise that the Lean of `(corec_≡)` reads, at the levels without variables. -/
def CorecBranchesEqValid (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade)
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ)
    (gs₁ gs₂ : CorecBranches 0 Γ) : Prop :=
  (∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps''),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
    (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
    ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
      gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩) ∧
  ∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps'') (p q : Grade)
    (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
    (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
    (g₁ g₂ : Term 0 ((Γ.extend ps''.length).extend ps₁.length)),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
    gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
    gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
    ValidEqTermΓ sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
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
            (as.rename (Ren.weakenN ps''.length)).toSubst))))

/-- The branches of a corecursor are terms of the results of their destructors, as `(corec)`
premises them: the premise that the Lean of `(corec)` and of `(β)` reads, at the levels without
variables. -/
def CorecBranchesValid (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade)
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ) (gs : CorecBranches 0 Γ) :
    Prop :=
  CorecBranchesEqValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs gs

-- ADE: `prod-congᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Sigma.agda`.
/-- `(corec_≡)` keeps the meaning: at equal substitutions of the context, the corecursors are
canonical terms whose observations by each destructor compute, by `(β_⟶)`, as the branches of the
destructor, which the premises make equal, the second corecursor at the levels of the first one,
which its levels equal; the instance is a type, as `(D)` gives it. The meaning reads the states of
the first corecursor only, as the contexts of its branches. -/
theorem ValidEqTermΓ.corec {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
    {r : Grade} {Ss₁ Ss₂ : States 0 Γ} {gs₁ gs₂ : CorecBranches 0 Γ} {h' : Nat}
    {ps' : List Parameter} {S₁ : Telescope 0 Γ ps'} {ss₁ ss₂ : Args 0 Γ ps'}
    (hh : decl.codataTypes[h']? = some T) (hS₁ : Ss₁.get h' = some ⟨0, ps', S₁⟩)
    (hss : ValidEqArgsΓ sig ι ctx ss₁ ss₂ S₁)
    (hg : CorecBranchesEqValid sig ι ctx decl qs ls₁ ps hq hl₁ hp as₁ r Ss₁ gs₁ gs₂) :
    ValidEqTermΓ sig ι ctx (.corec r D qs ls₁ ps as₁ ss₁.terms Ss₁ gs₁)
      (.corec r D qs ls₂ ps as₂ ss₂.terms Ss₂ gs₂) (.inst D qs ls₁ ps as₁) := by
  obtain ⟨h₀, hv⟩ := hent.hasCodataType h
  have hctx := has.1
  have hd := hctx.distinct
  have hcl : ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι
        (.corec r D qs ls₁ ps (as₁.subst σ₁) (ss₁.subst σ₁).terms (Ss₁.subst σ₁) (gs₁.subst σ₁))
        (.corec r D qs ls₁ ps (as₂.subst σ₂) (ss₂.subst σ₂).terms (Ss₂.subst σ₂) (gs₂.subst σ₂))
        (.inst D qs ls₁ ps (as₁.subst σ₁)) := fun σ₁ σ₂ hσ =>
    ValidEqTerm₀.corec hd h₀ hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)
      fun d p q ps₁ Ξ Θ B ψ hpos ts us hτ => by
        have hmem : (h', T, d) ∈ decl.codataCases := by
          have := TypeDeclaration.mem_casesFrom_of (f := CodataType.destructors) (i := 0) hh
            hpos.mem
          rwa [Nat.zero_add] at this
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
        obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hg.1 i h' T d ps' S₁ hi hS₁ p q ps₁ Ξ Θ B ψ hpos
        cases hnr : B.blockName decl.names with
        | some _ => sorry
        | none =>
        have h₁ := ValidEqTerm₀.obs_corec hent h hq hl₁ hp hss hi hpos hg₁ hnr
          (hg.2 i h' T d ps' S₁ p q ps₁ Ξ Θ B ψ g₁ g₂ hi hS₁ hpos hg₁ hg₂) hσ hτ
        have hred₂ : Red (sig.interpret ι)
            (.obs D qs ls₁ ps (as₂.subst σ₂) (.corec r D qs ls₁ ps (as₂.subst σ₂)
              (ss₂.subst σ₂).terms (Ss₂.subst σ₂) (gs₂.subst σ₂)) d us.terms)
            (g₂.subst (Subst.append (Subst.append σ₂ (ss₂.subst σ₂).toSubst) us.toSubst)) := by
          have he : g₂.subst (Subst.append (Subst.append σ₂ (ss₂.subst σ₂).toSubst) us.toSubst) =
              Term.observed decl.names ((T.body (.ofLists qs ps hq hp)).resultName decl.names d) r
                qs ls₁ ps (as₂.subst σ₂) (Ss₂.subst σ₂) (gs₂.subst σ₂)
                ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁))
                (((T.body (.ofLists qs ps hq hp)).resultConstant d).getD .unrestrictedUnrestricted)
                (g₂.subst (Subst.append (Subst.append σ₂ (ss₂.subst σ₂).toSubst) us.toSubst)) := by
            rw [hpos.resultName decl.names (hd.destructors_nodup h₀), hnr]
            rfl
          rw [he]
          exact .beta (List.mem_map_of_mem (f := Entry.interpret ι) h₀.1) hi h.2.2 hq hl₁ hp
            (CorecBranches.get_subst σ₂ hg₂) (Term.instantiateTerms₂_subst_append σ₂ g₂ _ _)
        exact ((ValidEqTerm₀.red_iff hd hred₂).2 h₁.symm).symm
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · have hI := (ValidEqTerm₀.instCodata hd h₀ hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)).trans
      (ValidEqTerm₀.instCodata hd h₀ hv hq hl₁ hp hadm (has.2 σ₂ σ₂ (hσ.right hctx))).symm
    show ValidEqType₀ sig ι (.inst D qs ls₁ ps (as₁.subst σ₁)) (.inst D qs ls₁ ps (as₁.subst σ₂))
    revert hI
    show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
      (decl.sort (.ofLists qs ps hq hp)).level.subst (ls₁.getFin hl₁)⟩) → _
    cases (decl.sort (.ofLists qs ps hq hp)).quality
    · exact ValidEqTerm₀.univType
    · exact ValidEqTerm₀.propType
  · rw [Term.corec_subst, Term.corec_subst]
    exact (hcl σ₁ σ₂ hσ).levelEquiv (Term.LevelEquiv.refl _)
      (.corec r D qs ps (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _)
        (Terms.LevelEquiv.refl _) (States.LevelEquiv.refl _) (CorecBranches.LevelEquiv.refl _))
      (Term.LevelEquiv.refl _)

-- ADE: none.
/-- `(corec)` keeps the meaning: it is `(corec_≡)` at the same corecursor. -/
theorem ValidTermΓ.corec {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {h' : Nat} {ps' : List Parameter}
    {S : Telescope 0 Γ ps'} {ss : Args 0 Γ ps'} (hh : decl.codataTypes[h']? = some T)
    (hS : Ss.get h' = some ⟨0, ps', S⟩) (hss : ValidArgsΓ sig ι ctx ss S)
    (hg : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs) :
    ValidTermΓ sig ι ctx (.corec r D qs ls ps as ss.terms Ss gs) (.inst D qs ls ps as) :=
  ValidEqTermΓ.corec hent h hq hl hl hp hadm has (fun _ => Level.equivalence.refl _) hh hS hss hg

-- ADE: `β-redᵛ`, `Σ-β₁ᵛ` and `Σ-β₂ᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(β)` keeps the meaning: the observation is a term of its result, as `(d)` and `(corec)` give
it, and, at equal substitutions of the context, it computes, by `(β_⟶)`, to the branch of its
destructor at the first substitution, which the premises make equal to the branch at the second
one, the right-hand side substituted. -/
theorem ValidEqTermΓ.beta {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {h' i : Nat} {ps' : List Parameter}
    {S : Telescope 0 Γ ps'} {ss : Args 0 Γ ps'} {d : Name} {p q : Grade} {ps₀ : List Parameter}
    {Ξ₀ : Scope} {Θ₀ : Telescope decl.levels Ξ₀ ps₀} {B₀ : Term decl.levels (Ξ₀.extend ps₀.length)}
    {ψ₀ : ResultOwnership ps₀.length} {g : Term 0 ((Γ.extend ps'.length).extend ps₀.length)}
    {bs : Args 0 Γ ps₀} (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
    (hss : ValidArgsΓ sig ι ctx ss S) (hi : decl.codataCases[i]? = some (h', T, d))
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ₀ Θ₀ B₀ ψ₀)
    (hgi : gs.get i = some ⟨0, ps'.length, ps₀.length, g⟩)
    (hbs : ValidArgsΓ sig ι ctx bs ((Θ₀.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
        as.toSubst)))
    (hg : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs) :
    ValidEqTermΓ sig ι ctx (.obs D qs ls ps as (.corec r D qs ls ps as ss.terms Ss gs) d bs.terms)
      (Term.observed decl.names (B₀.blockName decl.names) r qs ls ps as Ss gs
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
        (ψ₀.constant.getD .unrestrictedUnrestricted)
        ((g.instantiate (bs.rename (Ren.weakenN ps'.length))).instantiate ss))
      (((B₀.substLevels (ls.getFin hl)).subst
        (Subst.liftN _ (hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D
          qs ls ps as) as.toSubst))).instantiate bs) := by
  have hc := ValidTermΓ.corec hent h hq hl hp hadm has hh hS hss hg
  have hobs := ValidEqTermΓ.obs hent h hq hl hl hp hadm hpos has (fun _ => Level.equivalence.refl _)
    hc hbs
  -- The scope of the destructor, substituted, is that of the observations of the corecursor
  -- substituted.
  have hsc : ∀ (σ : Subst 0 [] Γ) {a} (x : Var Ξ₀ a),
      ((hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
        as.toSubst) x).subst (Subst.liftN a.params.length σ) =
      hpos.obsSubst ((Term.corec r D qs ls ps (as.subst σ) (ss.subst σ).terms (Ss.subst σ)
        (gs.subst σ)).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
    fun σ => hpos.obsSubst_subst σ (fun d' ps'' => by
      rw [Term.observation_subst, Term.corec_subst]) (InstanceArgs.toSubst_subst σ as)
  cases hnr : B₀.blockName decl.names with
  | some _ => sorry
  | none =>
  simp only [Term.observed]
  refine ⟨hobs.1, fun σ₁ σ₂ hσ => ?_⟩
  have hts := hbs.2 σ₁ σ₂ hσ
  rw [Telescope.subst_subst_of (hsc σ₁)] at hts
  have hb := ValidEqTerm₀.obs_corec hent h hq hl hp hss hi hpos hgi hnr
    (hg.2 i h' T d ps' S p q ps₀ Ξ₀ Θ₀ B₀ ψ₀ g g hi hS hpos hgi hgi) hσ hts
  rw [Term.instantiate_instantiate_subst_closed, Term.instantiate_subst,
    Term.subst_subst_of (Subst.liftN_subst_of _ (hsc σ₁)), Term.instantiate_eq_subst,
    Term.subst_append]
  simp only [Term.subst, ← Args.terms_subst]
  exact hb

/-! ## Extensionality of the Codata Types

Two terms of an instance of a codata type whose observations are equal, destructor by destructor,
are equal: the equality of the destructors relates their observations, as it relates those of two
corecursors, and then the observations of the corecursors they compute to, which compute as theirs.
On a proposition, the observations of the first term, related to themselves, make it true. -/

-- ADE: none.
/-- The equality of destructors relates the observations `o₁` and `o₂` when it relates observations
`f₁` and `f₂` that compute as them, at relations of the recursive destructors that are equalities
of the terms of types of the graph: the abstractions for each destructor compute as each other, so
that the equality of its result relates them, and the destructors after it are the same for
abstractions that the equality of the destructor relates. -/
theorem DesRel.obsEquiv (hd : sig.Distinct) {n : Nat} {s : Quality} :
    {rs : Nat → Option TermRel} → {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} →
      {θ : Subst 0 [] Γ} → {S : ObsRel} →
      (∀ i R, rs i = some R → ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S →
      {f₁ f₂ o₁ o₂ : Observations} → S f₁ f₂ → ObsEquiv sig ι s f₁ o₁ →
      ObsEquiv sig ι s f₂ o₂ → S o₁ o₂
  | _, _, _, .nil, _, _, _, h, _, _, _, _, _, _, _ => by
    cases h
    trivial
  | rs, _, _, .cons (d := d) (ps := ps) _ _ _ _ _ _, _, _, hRF, h, f₁, f₂, o₁, o₂, hS, hf₁, hf₂ => by
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    have hRF' : ∀ i R, rs (i + 1) = some R →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R := fun i => hRF (i + 1)
    cases h with
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
      obtain ⟨hA, hGf⟩ := hS
      have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
      have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
      have hFv : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
          ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts =>
        have ⟨v, hv⟩ := hB ts hts
        ⟨v, hF ts hts v hv⟩
      have hEp := AbstractionRel.isPer hSp (fun ts hts =>
        have ⟨_, hv⟩ := hFv ts hts
        FieldRel.isPer hd ih hv) hBresp
      have hA' : AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) :=
        (AbstractionRel.congr_computes hSp hFv (by
          rcases hc hf₁ with h₁ | h₁
          · exact .inl h₁
          rcases hc hf₂ with h₂ | h₂
          · exact .inl h₂
          exact .inr ⟨h₁, h₂⟩)).1 hA
      have hff : AbstractionRel SΘ F (f₁ d ps) (f₁ d ps) := hEp.trans hA (hEp.symm hA)
      have hfo : AbstractionRel SΘ F (f₁ d ps) (o₁ d ps) :=
        (AbstractionRel.congr_computes hSp hFv (by
          rcases hc hf₁ with h₁ | h₁
          · exact .inl h₁
          exact .inr ⟨fun _ _ => .rfl, h₁⟩)).1 hff
      exact ⟨hA', (hresp _ _ hfo o₁ o₂).1 (DesRel.obsEquiv hd hRF' (hG _ hff) hGf hf₁ hf₂)⟩
    | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R hrs hΘ G hG =>
      obtain ⟨hA, hGf⟩ := hS
      obtain ⟨v, hv⟩ := hRF 0 R hrs
      refine ⟨fun ts us hts => (hv.congr_computes ?_).1 (hA ts us hts),
        DesRel.obsEquiv hd hRF' (hG (o₁ d ps)) hGf hf₁ hf₂⟩
      rcases hc hf₁ with h₁ | h₁
      · exact .inl h₁
      rcases hc hf₂ with h₂ | h₂
      · exact .inl h₂
      exact .inr ⟨h₁ _, h₂ _⟩

-- ADE: none.
/-- `(η_d)`, closed: two closed terms of an instance of a codata type of `Σ`, whose type
declaration is meaningful, at arguments of its parameters, whose observations by each destructor,
at equal arguments of its telescope, are equal terms of its result, whatever the instance that the
second observation carries, are equal terms of the instance: canonical terms that `(eq_ν)` relates,
since the relation that `(eq_d)` gives the corecursors they compute to at `(eq_ν)` is consistent with
the clauses of the destructors, or proofs of a proposition that their observations make true. -/
theorem ValidEqTerm₀.etaObs (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst) {t u : Term 0 []}
    (ht : ValidTerm₀ sig ι t (.inst D qs ls ps as)) (hu : ValidTerm₀ sig ι u (.inst D qs ls ps as))
    (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (.obs D qs ls ps as t d ts.terms) (.obs D qs ls ps a₂ u d us.terms)
        ((B.substLevels (ls.getFin hl)).subst (Subst.append
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst))) :
    ValidEqTerm₀ sig ι t u (.inst D qs ls ps as) := by
  have hI : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht.1.2
  cases Computesι.det hd hcv hI
  have hnd := TypeDeclaration.codataTypes_nodup (hd.nodup h.1)
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm h.2.1 ρ).2 _ _ hθ
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst as.toSubst
  have hX : ∀ D', Term.LevelEquiv (X D') (.inst D' qs ls ps as) := fun D' =>
    decl.blockInstance_atLevels_subst hq hl hp as D'
  have hcX : ∀ D', Computesι sig ι (X D') (X D') := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The observations at the levels without variables.
  have hobs' : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body I).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels Lρ).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (((t.observation D qs ls ps as) d ps').subst ts.toSubst)
        (((u.observation D qs ls ps a₂) d ps').subst us.toSubst)
        ((B.substLevels Lρ).subst (Subst.append
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst)) :=
      fun d p q ps' Ξ Θ B ψ hpos ts us hτ => by
    rw [Term.observation_subst_args, Term.observation_subst_args]
    have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hls Θ))) hτ
    exact (hobs d p q ps' Ξ Θ B ψ hpos ts us hτ').levelEquiv (Term.LevelEquiv.refl _)
      (Term.LevelEquiv.refl _) (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
  have hlev : ∀ {s : Quality} {rs : Nat → Option TermRel} {S : ObsRel},
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels L) as.toSubst S →
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels Lρ) as.toSubst S := fun hS =>
    DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  rcases HasEq.instCodata_inv hd h hq hl hp hR with ⟨hs, S, hS, rfl⟩ | ⟨hs, S, hS, hRb⟩
  · -- An instance in a universe: the terms compute to corecursors, whose observations are theirs.
    have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
        ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
      fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
        fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
    have hU : ∀ T' ∈ decl.codataTypes, UnivRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (CodataType.blockRel decl.codataTypes S T'.name) := fun T' hT' =>
      .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
    have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
        (.inst D qs ls ps as) (CodataType.blockRel decl.codataTypes S D) :=
      levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
    have hnp : ¬ ComputesToProp sig ι (.inst D qs ls ps as) := fun ⟨v, hv, k, b, hk⟩ => by
      cases Computesι.det hd hI hv
      exact HasEq.univ_not_prop hd hU₀ hk
    have hDS := hlev (hS (CodataType.blockRel decl.codataTypes S) T h.2.1)
    have hS₁ := DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
      (fun i D' hi => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
          (Destructors.recursionAt_mem hi)
        rw [hi]
        exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
          (.univ rfl (hU T' hT')) (hX _).symm⟩)
      hDS hobs'
    obtain ⟨v₁, w₁, w₁', R₁, hv₁, hw₁, -, hR₁, hrel₁⟩ := ht.2.1 hnp
    cases Computesι.det hd hI hv₁
    have hrel₁' := (HasEq.unique hd hR₁ hR w₁ w₁').1 hrel₁
    rw [← h.2.2] at hrel₁'
    obtain ⟨o₁, -, hc₁, -, -⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel₁'
    obtain ⟨v₂, w₂, w₂', R₂, hv₂, hw₂, -, hR₂, hrel₂⟩ := hu.2.1 hnp
    cases Computesι.det hd hI hv₂
    have hrel₂' := (HasEq.unique hd hR₂ hR w₂ w₂').1 hrel₂
    rw [← h.2.2] at hrel₂'
    obtain ⟨o₂, -, hc₂, -, -⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel₂'
    have hS₂ := DesRel.obsEquiv hd (fun i R' hi => by
        cases hr : (T.body I).recursionAt decl.names i with
        | none => rw [hr] at hi; cases hi
        | some D' =>
          rw [hr] at hi
          cases hi
          obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
            (Destructors.recursionAt_mem hr)
          exact ⟨_, .univ rfl (hU T' hT')⟩)
      hDS hS₁ (ObsEquiv.of_computes hd hw₁ hc₁) (ObsEquiv.of_computes hd hw₂ hc₂)
    have hrel := CodataType.blockRel_fold hmono hnd h.2.1 ⟨o₁, o₂, hc₁, hc₂, hS₂⟩
    rw [h.2.2] at hrel
    exact ⟨ht.1, fun _ => ⟨_, w₁, w₂, _, hI, hw₁, hw₂, hR, hrel⟩, fun hp => absurd hp hnp⟩
  · -- A proposition: the observations of the first term make it true.
    have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
        S B T' o₁ o₂ → S B' T' o₁ o₂ :=
      fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
        fun _ => Option.rel_map (fun D _ _ => hB D) _
    have hP : ∀ T' ∈ decl.codataTypes, PropRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (CodataType.blockTruth decl.codataTypes S T'.name) := fun T' hT' =>
      .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
    have hP₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).prop
        (.inst D qs ls ps as) (CodataType.blockTruth decl.codataTypes S D) :=
      levelRel_prop_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
    have hDS := hlev (hS (CodataType.blockTruth decl.codataTypes S) T h.2.1)
    have hS₁ := DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
      (fun i D' hi => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
          (Destructors.recursionAt_mem hi)
        rw [hi]
        exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
          (.prop (hP T' hT')) (hX _).symm⟩)
      hDS hobs'
    have hSp := DesRel.isPer hd ih (fun i x hx => by
      cases hr : (T.body I).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩) hDS
    have htrue := CodataType.blockTruth_fold hmono hnd h.2.1 ⟨_, hSp.trans hS₁ (hSp.symm hS₁)⟩
    rw [h.2.2] at htrue
    exact ⟨ht.1, fun hn => absurd ⟨_, hI, _, _, hP₀⟩ hn,
      fun _ => ⟨_, R, hI, hR, (hRb _ _).2 htrue⟩⟩

-- ADE: `η-eqᵛ`, `Σ-ηᵛ` and `η-unitᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(η_d)` keeps the meaning: at equal substitutions of the context, the observations of the terms,
at the arguments of the instance substituted, are the closed observations of
`ValidEqTerm₀.etaObs`, since the observations of a term substituted are those of the substituted
term; the second term at the first substitution is equal to itself at the second one. -/
theorem ValidEqTermΓ.etaObs {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) {t u : Term 0 Γ}
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (hu : ValidTermΓ sig ι ctx u (.inst D qs ls ps as))
    (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ),
      ValidEqTermΓ sig ι (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))
        (t.observation D qs ls ps as d ps') (u.observation D qs ls ps as d ps')
        ((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))) :
    ValidEqTermΓ sig ι ctx t u (.inst D qs ls ps as) := by
  obtain ⟨h', hv⟩ := hent.hasCodataType h
  have hctx := ht.1.1
  have hd := hctx.distinct
  refine ⟨ht.1, fun σ₁ σ₂ hσ => ?_⟩
  have hu' := hu.2 σ₁ σ₂ hσ
  refine ValidEqTerm₀.etaObs (a₂ := as.subst σ₂) hd h' hv hq hl hp hadm
    (has.2 σ₁ σ₁ (hσ.left hctx)) (ht.2 σ₁ σ₁ (hσ.left hctx))
    hu'.right
    fun d p q ps' Ξ Θ B ψ hpos ts us hτ => ?_
  -- The scope of the destructor, substituted, is that of the observations of the term substituted.
  have hc : ∀ {a} (x : Var Ξ a),
      ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
        (Subst.liftN a.params.length σ₁) =
      hpos.obsSubst ((t.subst σ₁).observation D qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst x :=
    hpos.obsSubst_subst σ₁ (fun d ps' => Term.observation_subst σ₁ D qs ls ps as t d ps')
      (InstanceArgs.toSubst_subst σ₁ as)
  have hb := (hobs d p q ps' Ξ Θ B ψ hpos).2 _ _
    ((EqSubst.append_append_iff ctx _ σ₁ σ₂ ts.toSubst us.toSubst).2
      ⟨hσ, by rw [Telescope.subst_subst_of hc]; exact hτ⟩)
  rw [← Term.subst_append, ← Term.subst_append, ← Term.subst_append, Term.observation_subst,
    Term.observation_subst, Term.observation_subst_args, Term.observation_subst_args,
    Term.subst_subst_of (Subst.liftN_subst_of _ hc), Term.subst_append] at hb
  exact hb

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
