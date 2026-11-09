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
  | _, .secondOrder ctx Θ A χ₀, h =>
    ValidCtx₀.distinct (ValidCtx₀.append_left ((validCtx₀_secondOrder ctx Θ A χ₀).1 h).1)

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
theorem ValidEqTermΓ.secondOrder {Γ : Scope} {ps : List Parameter} {χ₀ : Option Grade}
    {ctx : Context 0 Γ} {X : Var Γ (.secondOrder ps χ₀)} {Θ : Telescope 0 Γ ps}
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

/-- Two closed telescopes equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.telRel (hd : sig.Distinct) {κ : Universe 0} :
    {ps : List Parameter} → {Θ₁ Θ₂ : Telescope 0 [] ps} → ValidEqTelescope₀ sig ι κ Θ₁ Θ₂ →
      ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality Θ₁ S ∧
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality Θ₂ S
  | [], .nil, .nil, _ => ⟨FieldsRel.nil, .nil, .nil⟩
  | _ :: _, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂, h => by
    rw [ValidEqTelescope₀] at h
    obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
    obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ
    have ih : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (Θ₂.subst₀ (Subst₀.single a₂)) S :=
      fun a₁ a₂ ha => ValidEqTelescope₀.telRel hd (hΘ a₁ a₂ (hFv a₁ a₂ ha))
    let G : Term 0 [] → FieldsRel := fun a ts us => ∃ S,
      TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
        (Θ₁.subst₀ (Subst₀.single a)) S ∧ S ts us
    have hG : ∀ a S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
        (Θ₁.subst₀ (Subst₀.single a)) S → G a = S := fun a S hS =>
      funext fun ts => funext fun us => propext
        ⟨fun ⟨_, hS', hs⟩ => (TelRel.unique hd ih hS' _ _ hS ts us).1 hs, fun hs => ⟨S, hS, hs⟩⟩
    have hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us := fun a₁ a₂ ha ts us => by
      have hFp := FieldRel.isPer hd ih hF₁
      obtain ⟨S, h₁, h₂⟩ := hcommon a₁ a₂ ha
      obtain ⟨S', h₁', h₂'⟩ := hcommon a₂ a₂ (hFp.trans (hFp.symm ha) ha)
      rw [hG a₁ S h₁, hG a₂ S' h₁']
      exact TelRel.unique hd ih h₂ _ _ h₂' ts us
    refine ⟨FieldsRel.cons F G, .cons hc₁ hF₁ G (fun a ha => ?_) hresp,
      .cons hc₂ hF₂ G (fun a ha => ?_) hresp⟩
    · obtain ⟨S, h₁, -⟩ := hcommon a a ha
      rw [hG a S h₁]
      exact h₁
    · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
      rw [hG a S h₁]
      exact h₂

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
/-- `(D)`, closed: two instances of a declared type of `Σ`, whose type declaration is meaningful, at
the same levels and at equal arguments of its parameters, are equal terms of its sort: the fields
of each constructor at the two arguments are telescopes of the graph of the sort with the same
equality of their terms. -/
theorem ValidEqTerm₀.inst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDeclaredType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := by
  have hT := h.2.1
  have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
    fun i => Level.ofNat_closedValue _
  have has' := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hfields : ∀ c ∈ T.constructors, ValidEqTelescope₀ sig ι
      ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁)
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) := fun c hc =>
    ValidEqTelescope₀.levelEquiv
      (κ := (decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue)
      (κ' := (decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) rfl
      (Level.subst_equiv hls _)
      ((hv.1 _ T hT c hc fun i => (ls.getFin hl i).closedValue).2 _ _ has')
      ((Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _))
      ((Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _))
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel := fun c ts us =>
    ∃ S', TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' ts us
  have hS : ∀ c ∈ T.constructors,
      TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S c) ∧
      TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S c) := fun c hc => by
    obtain ⟨S', h₁, h₂⟩ := (hfields c hc).telRel hd
    have hS' : S c = S' := funext fun ts => funext fun us => propext
      ⟨fun ⟨_, h', hs⟩ => (TelRel.unique hd ih h' _ _ h₁ ts us).1 hs, fun hs => ⟨S', h₁, hs⟩⟩
    rw [hS']
    exact ⟨h₁, h₂⟩
  have hc := hv.2 T hT
  have hw : ∀ as : InstanceArgs 0 [] decl.scope, Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    fun as => ⟨.refl _, .inst _ _ _ _ as⟩
  show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
    (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · exact ValidEqTerm₀.ofUniv hd (hw as₁) (hw as₂)
      (levelRel_univ_iff.2 (.data h hq hl hp rfl hs rfl hc S fun c hc' => hs ▸ (hS c hc').1))
      (levelRel_univ_iff.2 (.data h hq hl hp rfl hs rfl hc S fun c hc' => hs ▸ (hS c hc').2))
  · exact ValidEqTerm₀.ofProp hd (hw as₁) (hw as₂)
      (levelRel_prop_iff.2 (.data h hq hl hp rfl hs rfl hc S fun c hc' => hs ▸ (hS c hc').1))
      (levelRel_prop_iff.2 (.data h hq hl hp rfl hs rfl hc S fun c hc' => hs ▸ (hS c hc').2))

-- ADE: none.
/-- `(D_≡)` keeps the meaning, and `(D)` with it: equal arguments give, at equal substitutions of the
context, equal arguments of the parameters, hence equal instances, and the second instance at levels
of the same values is the same term up to its levels. -/
theorem ValidEqTermΓ.inst {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDeclaredType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
    ValidEqTermΓ sig ι ctx (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁))) := by
  obtain ⟨h', hv⟩ := hent.hasDeclaredType h
  have hd := has.1.distinct
  have hc : ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι (.inst D qs ls₁ ps (as₁.subst σ₁)) (.inst D qs ls₁ ps (as₂.subst σ₂))
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁))) :=
    fun σ₁ σ₂ hσ => ValidEqTerm₀.inst hd h' hv hq hl₁ hp (has.2 σ₁ σ₂ hσ)
  refine ⟨⟨has.1, fun σ₁ σ₂ hσ => (hc σ₁ σ₂ hσ).1⟩, fun σ₁ σ₂ hσ => ?_⟩
  exact (hc σ₁ σ₂ hσ).levelEquiv (Term.LevelEquiv.refl _)
    (.inst D qs ps (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _))
    (Term.LevelEquiv.refl _)

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
theorem ValidEqInstanceArgsΓ.secondOrder {Γ Δ : Scope} {ps : List Parameter} {χ₀ : Option Grade}
    {ctx : Context 0 Γ} {as₁ as₂ : InstanceArgs 0 Γ Δ} {params : Context 0 Δ}
    {Θ : Telescope 0 Δ ps} {A : Term 0 (Δ.extend ps.length)} {B₁ B₂ : Term 0 (Γ.extend ps.length)}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂ params)
    (hB : ValidEqTermΓ sig ι (ctx.append (Θ.subst as₁.toSubst)) B₁ B₂
      (A.subst (Subst.liftN _ as₁.toSubst))) :
    ValidEqInstanceArgsΓ sig ι ctx (.snoc (e := .secondOrder ps χ₀) as₁ B₁)
      (.snoc (e := .secondOrder ps χ₀) as₂ B₂) (params.secondOrder Θ A χ₀) := by
  refine ⟨has.1, fun σ₁ σ₂ h =>
    (EqSubst.secondOrder_iff params Θ A χ₀ _ _).2 ⟨has.2 σ₁ σ₂ h, fun τ₁ τ₂ hτ => ?_⟩⟩
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
/-- `(tel_κε)` keeps the meaning. -/
theorem ValidTelescopeΓ.nil {Γ : Scope} {ctx : Context 0 Γ} (hctx : ValidCtx₀ sig ι ctx)
    {κ : Universe 0} : ValidTelescopeΓ sig ι ctx .nil κ :=
  ⟨hctx, fun _ _ _ => hctx.distinct⟩

-- ADE: none.
/-- `(tel_κ,)` keeps the meaning: the first types are equal types of the sort `κ₁`, which `κ₂`
bounds, and the rest of the telescope at equal terms of them is the telescope at equal substitutions
of the context extended by its first entry; the meaning ignores the grades. -/
theorem ValidTelescopeΓ.cons {Γ : Scope} {ps : List Parameter} {ctx : Context 0 Γ} {q : Grade}
    {p : Parameter} {A : Term 0 Γ} {Θ : Telescope 0 (.var :: Γ) ps} {κ₁ κ₂ : Universe 0}
    (hA : ValidTermΓ sig ι ctx A (.sort κ₁)) (hκ : κ₁ ≼ κ₂)
    (hΘ : ValidTelescopeΓ sig ι (ctx.var A) Θ κ₂) : ValidTelescopeΓ sig ι ctx (.cons q p A Θ) κ₂ := by
  refine ⟨hA.1.1, fun σ₁ σ₂ h => ?_⟩
  show (∃ κ, κ ≼ κ₂ ∧ ValidEqTerm₀ sig ι (A.subst σ₁) (A.subst σ₂) (.sort κ)) ∧
    ∀ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ (A.subst σ₁) →
      ValidEqTelescope₀ sig ι κ₂ ((Θ.subst (Subst.lift σ₁)).subst₀ (Subst₀.single v₁))
        ((Θ.subst (Subst.lift σ₂)).subst₀ (Subst₀.single v₂))
  refine ⟨⟨κ₁, hκ, hA.2 σ₁ σ₂ h⟩, fun v₁ v₂ hv => ?_⟩
  rw [Telescope.subst_lift_single, Telescope.subst_lift_single]
  exact hΘ.2 _ _ ((EqSubst.var_iff ctx A _ _).2 ⟨h, hv⟩)

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
