module

public import Sic.Core.Soundness.Closed

/-!
# Equal Substitutions

The properties of the equal closed substitutions `eq(Γ)` of a context that the soundness of the
rules uses.

A substitution of the context `Γ, Θ` is a substitution `σ` of `Γ` followed by a substitution `τ` of
the variables of `Θ`, written `(σ, τ)`, which `Subst.append` builds and `Subst.dropN` and
`Subst.topN` take apart; `eq(Γ, Θ)` relates `(σ₁, τ₁)` and `(σ₂, τ₂)` when `eq(Γ)` relates `σ₁` and
`σ₂` and `eq(Θ[σ₁])` relates `τ₁` and `τ₂`, as the clause `(eq_X)` of a second-order variable
reads it.

The relation `eq(Γ)` of a meaningful context is a partial equivalence relation, as the meaning of a
hypothetical judgment needs for the rules `(sym)` and `(trans)`.
The clause `(eq_X)` takes the arguments of a second-order variable in `eq(Θ[σ₁])`, at the first of
the two substitutions, so that its symmetry needs `eq(Θ[σ₁]) = eq(Θ[σ₂])`: a meaningful telescope has
the same equal substitutions at equal substitutions of its context.

ADE prove the symmetry and the transitivity of their equal substitutions in
`Definition/LogicalRelation/Substitution.agda`, by recursion on the context, whose variables are of
the first order only, so that no telescope occurs there.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat}

/-! ## Substitutions of a Context Extended by a Telescope -/

/-- The renaming of the empty scope, which has no variable. -/
def Ren.empty {Γ : Scope} : Ren Γ [] := fun x => nomatch x

/-- A variable of a scope whose entries have no telescope has none either, under new variables. -/
theorem Var.extend_grades {Γ : Scope} (hΓ : ∀ {b}, Var Γ b → b = []) :
    (n : Nat) → {b : List Grade} → Var (Γ.extend n) b → b = []
  | 0, _, x => hΓ x
  | n + 1, _, x => Var.extend_grades (Γ := [] :: Γ)
      (fun y => match y with
        | .zero => rfl
        | .succ y => hΓ y) n x

/-- The substitution `σ` of the scope `Γ` extended by `n` variables, on the variables of `Γ`. -/
def Subst.dropN {Ξ Γ : Scope} (n : Nat) (σ : Subst k Ξ (Γ.extend n)) : Subst k Ξ Γ :=
  fun x => σ (x.weakenN n)

/-- The substitution `σ` of the scope `Γ` extended by `n` variables, on these variables. -/
def Subst.topN {Ξ Γ : Scope} (n : Nat) (σ : Subst k Ξ (Γ.extend n)) :
    Subst k Ξ (Scope.extend [] n) :=
  fun x => σ (Ren.liftN n Ren.empty x)

/-- `(σ, τ)`: the closed substitution `σ` of the scope `Γ` followed by the closed substitution `τ`
of `n` new variables. -/
def Subst.append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ) (τ : Subst k [] (Scope.extend [] n)) :
    Subst k [] (Γ.extend n) :=
  fun x => (Subst.liftN n σ x).subst (Subst.liftN _ τ)

/-- Substitutions that agree on every variable are equal. -/
theorem Subst.ext {Ξ Γ : Scope} {σ σ' : Subst k Ξ Γ} (h : ∀ {a} (x : Var Γ a), σ x = σ' x) :
    @Eq (Subst k Ξ Γ) σ σ' := by
  funext a x
  exact h x

/-- A substitution of the empty scope changes no term, under new variables. -/
theorem Term.subst_liftN_empty {a : Nat} (σ : Subst k [] []) (t : Term k (Scope.extend [] a)) :
    t.subst (Subst.liftN a σ) = t :=
  Term.subst_id_of (Subst.liftN_id_of a fun x => by cases x) t

/-- A substitution of the empty scope changes no closed term. -/
theorem Term.subst_empty (σ : Subst k [] []) (t : Term k []) : t.subst σ = t :=
  Term.subst_liftN_empty (a := 0) σ t

/-- `A[σ⇑][τ] = A[σ, τ]`. -/
theorem Term.subst_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) (t : Term k (Γ.extend n)) :
    (t.subst (Subst.liftN n σ)).subst τ = t.subst (Subst.append σ τ) :=
  Term.subst_subst_of (fun _ => rfl) t

/-- `(σ, τ)` gives the variables of `Γ` what `σ` gives them. -/
theorem Subst.dropN_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) {a : List Grade} (x : Var Γ a) :
    Subst.dropN n (Subst.append σ τ) x = σ x := by
  show (Subst.liftN n σ (x.weakenN n)).subst (Subst.liftN a.length τ) = σ x
  rw [Subst.liftN_weakenN, Term.subst_rename_of (Subst.liftN_rename_of a.length
    (ρ := Ren.weakenN n) (σ' := fun y => τ (y.weakenN n)) fun _ => rfl)]
  exact Term.subst_liftN_empty _ _

/-- `(σ, τ)` gives the new variables what `τ` gives them. -/
theorem Subst.topN_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) {a : List Grade} (x : Var (Scope.extend [] n) a) :
    Subst.topN n (Subst.append σ τ) x = τ x := by
  obtain rfl := Var.extend_grades (fun y => by cases y) n x
  show (Subst.liftN n σ (Ren.liftN n Ren.empty x)).subst (Subst.liftN 0 τ) = τ x
  rw [Subst.liftN_rename_of n (σ' := fun y => σ (Ren.empty y)) (fun _ => rfl),
    Subst.liftN_id_of n (fun y => by cases y)]
  rfl

/-- `(σ, τ)` without its last `n` entries is `σ⇑` substituted by `τ` without its last `n` entries:
both give the variables of `Γ` what `σ` gives them, and `x` what `τ` gives it. -/
theorem Subst.dropN_append_succ {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [[]] n)) {a : List Grade} (x : Var ([] :: Γ) a) :
    (Subst.lift σ x).subst (Subst.liftN a.length (Subst.dropN n τ)) =
      Subst.dropN n (Subst.append (n := n + 1) σ τ) x := by
  show _ = (Subst.liftN n (Subst.lift σ) (x.weakenN n)).subst (Subst.liftN a.length τ)
  rw [Subst.liftN_weakenN, Term.subst_rename_of (Subst.liftN_rename_of a.length
    (ρ := Ren.weakenN n) (σ' := Subst.dropN n τ) fun _ => rfl)]

/-- `(σ, τ)` gives the first new variable what `τ` gives it. -/
theorem Subst.dropN_append_zero {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [[]] n)) :
    Subst.dropN n (Subst.append (n := n + 1) σ τ) .zero = Subst.dropN n τ .zero :=
  (Subst.dropN_append_succ σ τ .zero).symm

/-- The substitution `σ` without its last `n + 1` entries, on its first new variable, is `σ` without
its last `n` entries. -/
theorem Subst.dropN_topN_zero {Γ : Scope} {n : Nat} (σ : Subst k [] (Scope.extend ([] :: Γ) n)) :
    Subst.dropN n (Subst.topN (Γ := Γ) (n + 1) σ) .zero = Subst.dropN n σ .zero := by
  show σ (Ren.liftN n (Ren.lift Ren.empty) (Var.weakenN n .zero)) = σ (Var.weakenN n .zero)
  rw [Ren.liftN_weakenN]
  rfl

/-- The last `n` variables of the last `n + 1` variables are the last `n` variables. -/
theorem Subst.topN_topN {Γ : Scope} {n : Nat} (σ : Subst k [] (Scope.extend ([] :: Γ) n)) :
    @Eq (Subst k [] (Scope.extend [] n)) (Subst.topN n (Subst.topN (Γ := Γ) (n + 1) σ))
      (Subst.topN n σ) :=
  Subst.ext fun x => congrArg (fun y => σ y)
    (Ren.liftN_comp_of n (ρ₃ := Ren.empty) (fun y => by cases y) x)

/-! ## Equal Substitutions -/

section

variable {sig : Signature} {ι : Interpretation}

/-- `(eq_ε)`. -/
theorem EqSubst.empty_iff (σ₁ σ₂ : Subst 0 [] []) : EqSubst sig ι .empty σ₁ σ₂ ↔ True := by
  rw [EqSubst]

-- ADE: `⊩ˢ≡∷∙⇔`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(eq_x)`. -/
theorem EqSubst.var_iff {Γ : Scope} (ctx : Context 0 Γ) (A : Term 0 Γ)
    (σ₁ σ₂ : Subst 0 [] ([] :: Γ)) :
    EqSubst sig ι (ctx.var A) σ₁ σ₂ ↔ EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ValidEqTerm₀ sig ι (σ₁ .zero) (σ₂ .zero) (A.subst (Subst.tail σ₁)) := by
  rw [EqSubst]

/-- `(eq_X)`. -/
theorem EqSubst.secondOrder_iff {Γ : Scope} {ps : List Grade} (ctx : Context 0 Γ)
    (Θ : Telescope 0 Γ ps) (A : Term 0 (Γ.extend ps.length)) (σ₁ σ₂ : Subst 0 [] (ps :: Γ)) :
    EqSubst sig ι (ctx.secondOrder Θ A) σ₁ σ₂ ↔ EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst (Subst.tail σ₁))) τ₁ τ₂ →
        ValidEqTerm₀ sig ι ((σ₁ .zero).subst τ₁) ((σ₂ .zero).subst τ₂)
          ((A.subst (Subst.liftN _ (Subst.tail σ₁))).subst τ₁) := by
  rw [EqSubst]

/-- `eq(Γ)` depends on the substitutions only through what they give each variable. -/
theorem EqSubst.congr {Γ : Scope} {ctx : Context 0 Γ} {σ₁ σ₁' σ₂ σ₂' : Subst 0 [] Γ}
    (h₁ : @Eq (Subst 0 [] Γ) σ₁ σ₁') (h₂ : @Eq (Subst 0 [] Γ) σ₂ σ₂') :
    EqSubst sig ι ctx σ₁ σ₂ ↔ EqSubst sig ι ctx σ₁' σ₂' :=
  h₁ ▸ h₂ ▸ Iff.rfl

/-- `eq(Γ, Θ)` relates the substitutions whose substitutions of `Γ` are in `eq(Γ)`, and whose
substitutions of the variables of `Θ` are in `eq(Θ[σ₁])`, at the first substitution `σ₁` of `Γ`. -/
theorem EqSubst.append_iff :
    {Γ : Scope} → {ps : List Grade} → (ctx : Context 0 Γ) → (Θ : Telescope 0 Γ ps) →
      (σ₁ σ₂ : Subst 0 [] (Γ.extend ps.length)) →
      (EqSubst sig ι (ctx.append Θ) σ₁ σ₂ ↔
        EqSubst sig ι ctx (Subst.dropN _ σ₁) (Subst.dropN _ σ₂) ∧
          EqSubst sig ι (Context.empty.append (Θ.subst (Subst.dropN _ σ₁)))
            (Subst.topN _ σ₁) (Subst.topN _ σ₂))
  | _, [], ctx, .nil, σ₁, σ₂ => by
    exact ⟨fun h => ⟨h, (EqSubst.empty_iff _ _).2 trivial⟩, fun h => h.1⟩
  | Γ, _ :: ps, ctx, .cons q p A Θ, σ₁, σ₂ => by
    have h₁ := EqSubst.append_iff (ctx.var A) Θ σ₁ σ₂
    have h₂ := EqSubst.append_iff (Context.empty.var (A.subst (Subst.dropN (ps.length + 1) σ₁)))
      (Θ.subst (Subst.lift (Subst.dropN (ps.length + 1) σ₁)))
      (Subst.topN (Γ := Γ) (ps.length + 1) σ₁) (Subst.topN (Γ := Γ) (ps.length + 1) σ₂)
    have hΘ : (Θ.subst (Subst.lift (Subst.dropN (ps.length + 1) σ₁))).subst
        (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₁)) =
          Θ.subst (Subst.dropN ps.length σ₁) := by
      refine Telescope.subst_subst_of (fun x => ?_) Θ
      cases x with
      | zero => exact Subst.dropN_topN_zero σ₁
      | succ y =>
        show ((Subst.dropN (ps.length + 1) σ₁ y).rename (Ren.liftN _ Ren.weaken)).subst _ = _
        rw [Term.subst_rename_of (Subst.liftN_rename_of _ (ρ := Ren.weaken)
          (σ' := Subst.tail (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₁)))
          fun _ => rfl)]
        exact Term.subst_liftN_empty _ _
    show EqSubst sig ι ((ctx.var A).append Θ) σ₁ σ₂ ↔
      EqSubst sig ι ctx (Subst.dropN (ps.length + 1) σ₁) (Subst.dropN (ps.length + 1) σ₂) ∧
      EqSubst sig ι ((Context.empty.var (A.subst (Subst.dropN (ps.length + 1) σ₁))).append
        (Θ.subst (Subst.lift (Subst.dropN (ps.length + 1) σ₁))))
        (Subst.topN (Γ := Γ) (ps.length + 1) σ₁) (Subst.topN (Γ := Γ) (ps.length + 1) σ₂)
    have hv : ∀ A' : Term 0 [],
        ValidEqTerm₀ sig ι (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₁) .zero)
          (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₂) .zero) A' ↔
        ValidEqTerm₀ sig ι (Subst.dropN ps.length σ₁ .zero) (Subst.dropN ps.length σ₂ .zero) A' := by
      intro A'
      rw [Subst.dropN_topN_zero σ₁, Subst.dropN_topN_zero σ₂]
    have hA : (A.subst (Subst.dropN (ps.length + 1) σ₁)).subst
        (Subst.tail (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₁))) =
          A.subst (Subst.tail (Subst.dropN ps.length σ₁)) :=
      Term.subst_empty _ _
    have hτ := EqSubst.congr (sig := sig) (ι := ι)
      (ctx := Context.empty.append (Θ.subst (Subst.dropN ps.length σ₁)))
      (Subst.topN_topN σ₁) (Subst.topN_topN σ₂)
    rw [h₁, h₂, EqSubst.var_iff, EqSubst.var_iff, EqSubst.empty_iff, hΘ, hτ, hA, hv]
    exact ⟨fun ⟨⟨hσ, hv⟩, hτ⟩ => ⟨hσ, ⟨trivial, hv⟩, hτ⟩, fun ⟨hσ, ⟨_, hv⟩, hτ⟩ => ⟨⟨hσ, hv⟩, hτ⟩⟩

/-- `((σ₁, τ₁), (σ₂, τ₂)) ∈ eq(Γ, Θ)` when `(σ₁, σ₂) ∈ eq(Γ)` and `(τ₁, τ₂) ∈ eq(Θ[σ₁])`. -/
theorem EqSubst.append_append_iff {Γ : Scope} {ps : List Grade} (ctx : Context 0 Γ)
    (Θ : Telescope 0 Γ ps) (σ₁ σ₂ : Subst 0 [] Γ) (τ₁ τ₂ : Subst 0 [] (Scope.extend [] ps.length)) :
    EqSubst sig ι (ctx.append Θ) (Subst.append σ₁ τ₁) (Subst.append σ₂ τ₂) ↔
      EqSubst sig ι ctx σ₁ σ₂ ∧ EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) τ₁ τ₂ := by
  have e₁ : @Eq (Subst 0 [] Γ) (Subst.dropN _ (Subst.append σ₁ τ₁)) σ₁ :=
    Subst.ext (Subst.dropN_append σ₁ τ₁)
  have e₂ : @Eq (Subst 0 [] Γ) (Subst.dropN _ (Subst.append σ₂ τ₂)) σ₂ :=
    Subst.ext (Subst.dropN_append σ₂ τ₂)
  have f₁ : @Eq (Subst 0 [] (Scope.extend [] ps.length)) (Subst.topN _ (Subst.append σ₁ τ₁)) τ₁ :=
    Subst.ext (Subst.topN_append σ₁ τ₁)
  have f₂ : @Eq (Subst 0 [] (Scope.extend [] ps.length)) (Subst.topN _ (Subst.append σ₂ τ₂)) τ₂ :=
    Subst.ext (Subst.topN_append σ₂ τ₂)
  rw [EqSubst.append_iff, e₁, e₂, f₁, f₂]

/-- The substitutions of the variables of `x : A, Θ`, at a substitution `σ` of the context `Γ` of
the telescope: equal terms of `A[σ]`, followed by equal substitutions of `Θ[σ, v₁]`. -/
theorem EqSubst.telescope_cons_iff {Γ : Scope} {ps : List Grade} (q p : Grade) (A : Term 0 Γ)
    (Θ : Telescope 0 ([] :: Γ) ps) (σ : Subst 0 [] Γ)
    (τ₁ τ₂ : Subst 0 [] (Scope.extend [[]] ps.length)) :
    EqSubst sig ι (Context.empty.append ((Telescope.cons q p A Θ).subst σ)) τ₁ τ₂ ↔
      ValidEqTerm₀ sig ι (Subst.dropN _ τ₁ .zero) (Subst.dropN _ τ₂ .zero) (A.subst σ) ∧
        EqSubst sig ι
          (Context.empty.append (Θ.subst (Subst.dropN (Γ := [] :: Γ) ps.length (Subst.append (n := ps.length + 1) σ τ₁))))
          (Subst.topN _ τ₁) (Subst.topN _ τ₂) := by
  have hΘ : (Θ.subst (Subst.lift σ)).subst (Subst.dropN ps.length τ₁) =
      Θ.subst (Subst.dropN (Γ := [] :: Γ) ps.length (Subst.append (n := ps.length + 1) σ τ₁)) :=
    Telescope.subst_subst_of (Subst.dropN_append_succ σ τ₁) Θ
  have hA : (A.subst σ).subst (Subst.tail (Subst.dropN ps.length τ₁)) = A.subst σ :=
    Term.subst_empty _ _
  show EqSubst sig ι ((Context.empty.var (A.subst σ)).append (Θ.subst (Subst.lift σ))) τ₁ τ₂ ↔ _
  rw [EqSubst.append_iff, EqSubst.var_iff, EqSubst.empty_iff, hΘ, hA, true_and]

/-- A meaningful context is meaningful before the entries of a telescope. -/
theorem ValidCtx₀.append_left :
    {Γ : Scope} → {ps : List Grade} → {ctx : Context 0 Γ} → {Θ : Telescope 0 Γ ps} →
      ValidCtx₀ sig ι (ctx.append Θ) → ValidCtx₀ sig ι ctx
  | _, [], _, .nil, h => h
  | _, _ :: _, ctx, .cons _ _ A _, h => ((validCtx₀_var ctx A).1 (ValidCtx₀.append_left h)).1

/-- A meaningful telescope has the same equal substitutions at two equal substitutions of its
context: `eq(Θ[σ₁]) = eq(Θ[σ₂])` when `(σ₁, σ₂) ∈ eq(Γ)` and `Σ ⊨ Γ, Θ`. -/
theorem EqSubst.telescope_iff :
    {Γ : Scope} → {ps : List Grade} → {ctx : Context 0 Γ} → {Θ : Telescope 0 Γ ps} →
      ValidCtx₀ sig ι (ctx.append Θ) → {σ₁ σ₂ : Subst 0 [] Γ} → EqSubst sig ι ctx σ₁ σ₂ →
      (τ₁ τ₂ : Subst 0 [] (Scope.extend [] ps.length)) →
      (EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) τ₁ τ₂ ↔
        EqSubst sig ι (Context.empty.append (Θ.subst σ₂)) τ₁ τ₂)
  | _, [], _, .nil, _, _, _, _, _, _ => Iff.rfl
  | _, _ :: ps, ctx, .cons q p A Θ, hV, σ₁, σ₂, hσ, τ₁, τ₂ => by
    have hA := ((validCtx₀_var ctx A).1 (ValidCtx₀.append_left (Θ := Θ) hV)).2 σ₁ σ₂ hσ
    have hv : ValidEqTerm₀ sig ι (Subst.dropN ps.length τ₁ .zero) (Subst.dropN ps.length τ₁ .zero)
          (A.subst σ₁) →
        (EqSubst sig ι (Context.empty.append (Θ.subst
            (Subst.dropN (Γ := [] :: _) ps.length (Subst.append (n := ps.length + 1) σ₁ τ₁))))
            (Subst.topN (Γ := [[]]) ps.length τ₁) (Subst.topN (Γ := [[]]) ps.length τ₂) ↔
          EqSubst sig ι (Context.empty.append (Θ.subst
            (Subst.dropN (Γ := [] :: _) ps.length (Subst.append (n := ps.length + 1) σ₂ τ₁))))
            (Subst.topN (Γ := [[]]) ps.length τ₁) (Subst.topN (Γ := [[]]) ps.length τ₂)) := by
      intro hv
      refine EqSubst.telescope_iff (ctx := ctx.var A) (Θ := Θ) hV ((EqSubst.var_iff ctx A _ _).2 ⟨?_, ?_⟩) _ _
      · exact (EqSubst.congr (Subst.ext (Subst.dropN_append σ₁ τ₁)).symm
          (Subst.ext (Subst.dropN_append σ₂ τ₁)).symm).1 hσ
      · show ValidEqTerm₀ sig ι
          (Subst.dropN ps.length (Subst.append (n := ps.length + 1) σ₁ τ₁) .zero)
          (Subst.dropN ps.length (Subst.append (n := ps.length + 1) σ₂ τ₁) .zero)
          (A.subst (Subst.dropN (ps.length + 1) (Subst.append (n := ps.length + 1) σ₁ τ₁)))
        rw [Subst.dropN_append_zero σ₁ τ₁, Subst.dropN_append_zero σ₂ τ₁,
          Term.subst_congr (Subst.dropN_append (n := ps.length + 1) σ₁ τ₁) A]
        exact hv
    refine (EqSubst.telescope_cons_iff q p A Θ σ₁ τ₁ τ₂).trans
      (Iff.trans ⟨fun ⟨h, e⟩ => ⟨h.conv hA, (hv h.left).1 e⟩,
        fun ⟨h, e⟩ => ⟨h.conv hA.symm, (hv (h.conv hA.symm).left).2 e⟩⟩
        (EqSubst.telescope_cons_iff q p A Θ σ₂ τ₁ τ₂).symm)

/-- `eq(Γ)` is a partial equivalence relation when `Σ ⊨ Γ`: by recursion on the size of the
context, since the clause `(eq_X)` of a second-order variable `X : (Θ ⊢ A)` uses `eq(Γ, Θ)`, whose
properties give those of `eq(Θ[σ])` through `EqSubst.append_append_iff`. -/
theorem EqSubst.isPer : {Γ : Scope} → (ctx : Context 0 Γ) → ValidCtx₀ sig ι ctx →
    (∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ → EqSubst sig ι ctx σ₂ σ₁) ∧
      ∀ σ₁ σ₂ σ₃, EqSubst sig ι ctx σ₁ σ₂ → EqSubst sig ι ctx σ₂ σ₃ → EqSubst sig ι ctx σ₁ σ₃
  | _, .empty, _ =>
    ⟨fun _ _ _ => (EqSubst.empty_iff _ _).2 trivial, fun _ _ _ _ _ => (EqSubst.empty_iff _ _).2 trivial⟩
  | _, .var ctx A, hV => by
    obtain ⟨hctx, hA⟩ := (validCtx₀_var ctx A).1 hV
    obtain ⟨symmΓ, transΓ⟩ := EqSubst.isPer ctx hctx
    refine ⟨fun σ₁ σ₂ h => ?_, fun σ₁ σ₂ σ₃ h₁₂ h₂₃ => ?_⟩
    · obtain ⟨hσ, hv⟩ := (EqSubst.var_iff ctx A σ₁ σ₂).1 h
      exact (EqSubst.var_iff ctx A σ₂ σ₁).2 ⟨symmΓ _ _ hσ, hv.symm.conv (hA _ _ hσ)⟩
    · obtain ⟨hσ₁₂, hv₁₂⟩ := (EqSubst.var_iff ctx A σ₁ σ₂).1 h₁₂
      obtain ⟨hσ₂₃, hv₂₃⟩ := (EqSubst.var_iff ctx A σ₂ σ₃).1 h₂₃
      exact (EqSubst.var_iff ctx A σ₁ σ₃).2
        ⟨transΓ _ _ _ hσ₁₂ hσ₂₃, hv₁₂.trans (hv₂₃.conv (hA _ _ hσ₁₂).symm)⟩
  | _, .secondOrder (ps := ps) ctx Θ A, hV => by
    obtain ⟨hΘ, hA⟩ := (validCtx₀_secondOrder ctx Θ A).1 hV
    obtain ⟨symmΓ, transΓ⟩ := EqSubst.isPer ctx (ValidCtx₀.append_left hΘ)
    obtain ⟨symmΓΘ, transΓΘ⟩ := EqSubst.isPer (ctx.append Θ) hΘ
    have app := fun {σ₁ σ₂ τ₁ τ₂} h hτ =>
      (EqSubst.append_append_iff (sig := sig) (ι := ι) ctx Θ σ₁ σ₂ τ₁ τ₂).2 ⟨h, hτ⟩
    have unapp := fun {σ₁ σ₂ τ₁ τ₂} h =>
      ((EqSubst.append_append_iff (sig := sig) (ι := ι) ctx Θ σ₁ σ₂ τ₁ τ₂).1 h).2
    -- `eq(Θ[σ])` is a partial equivalence relation when `(σ, σ) ∈ eq(Γ)`.
    have symΘ : ∀ {σ τ₁ τ₂}, EqSubst sig ι ctx σ σ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ)) τ₁ τ₂ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ)) τ₂ τ₁ :=
      fun hσ hτ => unapp (symmΓΘ _ _ (app hσ hτ))
    have transΘ : ∀ {σ τ₁ τ₂ τ₃}, EqSubst sig ι ctx σ σ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ)) τ₁ τ₂ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ)) τ₂ τ₃ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ)) τ₁ τ₃ :=
      fun hσ h₁₂ h₂₃ => unapp (transΓΘ _ _ _ (app hσ h₁₂) (app hσ h₂₃))
    -- `A[σ₁⇑][τ₁] ≡ A[σ₂⇑][τ₂]` for equal substitutions of `Γ, Θ`.
    have hAapp : ∀ {σ₁ σ₂ τ₁ τ₂}, EqSubst sig ι ctx σ₁ σ₂ →
        EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) τ₁ τ₂ →
        ValidEqType₀ sig ι ((A.subst (Subst.liftN ps.length σ₁)).subst τ₁)
          ((A.subst (Subst.liftN ps.length σ₂)).subst τ₂) := by
      intro σ₁ σ₂ τ₁ τ₂ h hτ
      rw [Term.subst_append σ₁ τ₁ A, Term.subst_append σ₂ τ₂ A]
      exact hA _ _ (app h hτ)
    refine ⟨fun σ₁ σ₂ h => ?_, fun σ₁ σ₂ σ₃ h₁₂ h₂₃ => ?_⟩
    · obtain ⟨hσ, hB⟩ := (EqSubst.secondOrder_iff ctx Θ A σ₁ σ₂).1 h
      have hσ₁ := transΓ _ _ _ hσ (symmΓ _ _ hσ)
      refine (EqSubst.secondOrder_iff ctx Θ A σ₂ σ₁).2 ⟨symmΓ _ _ hσ, fun τ₁ τ₂ hτ => ?_⟩
      have hτ' := symΘ hσ₁ ((EqSubst.telescope_iff hΘ hσ τ₁ τ₂).2 hτ)
      exact (hB τ₂ τ₁ hτ').symm.conv (hAapp hσ hτ')
    · obtain ⟨hσ₁₂, hB₁₂⟩ := (EqSubst.secondOrder_iff ctx Θ A σ₁ σ₂).1 h₁₂
      obtain ⟨hσ₂₃, hB₂₃⟩ := (EqSubst.secondOrder_iff ctx Θ A σ₂ σ₃).1 h₂₃
      have hσ₁ := transΓ _ _ _ hσ₁₂ (symmΓ _ _ hσ₁₂)
      refine (EqSubst.secondOrder_iff ctx Θ A σ₁ σ₃).2 ⟨transΓ _ _ _ hσ₁₂ hσ₂₃, fun τ₁ τ₂ hτ => ?_⟩
      have hτ₂ := (EqSubst.telescope_iff hΘ hσ₁₂ τ₂ τ₂).1 (transΘ hσ₁ (symΘ hσ₁ hτ) hτ)
      exact (hB₁₂ τ₁ τ₂ hτ).trans ((hB₂₃ τ₂ τ₂ hτ₂).conv (hAapp hσ₁₂ hτ).symm)
termination_by _ ctx => ctx.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

-- ADE: `sym-⊩ˢ≡∷`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `eq(Γ)` is symmetric when `Σ ⊨ Γ`. -/
theorem EqSubst.symm {Γ : Scope} {ctx : Context 0 Γ} {σ₁ σ₂ : Subst 0 [] Γ}
    (hctx : ValidCtx₀ sig ι ctx) (h : EqSubst sig ι ctx σ₁ σ₂) : EqSubst sig ι ctx σ₂ σ₁ :=
  (EqSubst.isPer ctx hctx).1 _ _ h

-- ADE: `trans-⊩ˢ≡`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `eq(Γ)` is transitive when `Σ ⊨ Γ`. -/
theorem EqSubst.trans {Γ : Scope} {ctx : Context 0 Γ} {σ₁ σ₂ σ₃ : Subst 0 [] Γ}
    (hctx : ValidCtx₀ sig ι ctx) (h : EqSubst sig ι ctx σ₁ σ₂) (h' : EqSubst sig ι ctx σ₂ σ₃) :
    EqSubst sig ι ctx σ₁ σ₃ :=
  (EqSubst.isPer ctx hctx).2 _ _ _ h h'

/-- `(σ₁, σ₂) ∈ eq(Γ)` gives `(σ₁, σ₁) ∈ eq(Γ)` when `Σ ⊨ Γ`. -/
theorem EqSubst.left {Γ : Scope} {ctx : Context 0 Γ} {σ₁ σ₂ : Subst 0 [] Γ}
    (hctx : ValidCtx₀ sig ι ctx) (h : EqSubst sig ι ctx σ₁ σ₂) : EqSubst sig ι ctx σ₁ σ₁ :=
  h.trans hctx (h.symm hctx)

/-- `(σ₁, σ₂) ∈ eq(Γ)` gives `(σ₂, σ₂) ∈ eq(Γ)` when `Σ ⊨ Γ`. -/
theorem EqSubst.right {Γ : Scope} {ctx : Context 0 Γ} {σ₁ σ₂ : Subst 0 [] Γ}
    (hctx : ValidCtx₀ sig ι ctx) (h : EqSubst sig ι ctx σ₁ σ₂) : EqSubst sig ι ctx σ₂ σ₂ :=
  (h.symm hctx).trans hctx h

/-! ## Entries of a Context under Equal Substitutions -/

/-- `A[↑][σ] = A[σ without its last entry]`: a type weakened past the last entry of a context, at a
substitution of that context. -/
theorem Term.subst_weaken {Γ : Scope} {ps : List Grade} (σ : Subst k [] (ps :: Γ)) (A : Term k Γ) :
    (A.rename Ren.weaken).subst σ = A.subst (Subst.tail σ) :=
  Term.subst_rename_of (fun _ => rfl) A

/-- `A[↑⇑][σ⇑] = A[(σ without its last entry)⇑]`: a type in the scope of a telescope weakened past
the last entry of a context, at a substitution of that context. -/
theorem Term.subst_liftN_weaken {Γ : Scope} {ps : List Grade} (n : Nat) (σ : Subst k [] (ps :: Γ))
    (A : Term k (Γ.extend n)) :
    (A.rename (Ren.liftN n Ren.weaken)).subst (Subst.liftN n σ) =
      A.subst (Subst.liftN n (Subst.tail σ)) :=
  Term.subst_rename_of (Subst.liftN_rename_of n fun _ => rfl) A

/-- `Θ[↑][σ] = Θ[σ without its last entry]`: a telescope weakened past the last entry of a context,
at a substitution of that context. -/
theorem Telescope.subst_weaken {Γ : Scope} {ps qs : List Grade} (σ : Subst k [] (ps :: Γ))
    (Θ : Telescope k Γ qs) : (Θ.rename Ren.weaken).subst σ = Θ.subst (Subst.tail σ) :=
  Telescope.subst_rename_of (fun _ => rfl) Θ

-- ADE: the substitutions in `varᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Var.agda`.
/-- `(σ₁, σ₂) ∈ eq(Γ)` gives the variable `x : A ∈ Γ` equal closed terms of the type `A[σ₁]`. -/
theorem EqSubst.varIn {Γ : Scope} {ctx : Context 0 Γ} {x : Var Γ []} {A : Term 0 Γ}
    (hx : ctx.VarIn x A) {σ₁ σ₂ : Subst 0 [] Γ} (h : EqSubst sig ι ctx σ₁ σ₂) :
    ValidEqTerm₀ sig ι (σ₁ x) (σ₂ x) (A.subst σ₁) := by
  induction hx with
  | @zero _ ctx A =>
    rw [Term.subst_weaken]
    exact ((EqSubst.var_iff ctx A σ₁ σ₂).1 h).2
  | @succVar _ ctx _ A B _ ih =>
    rw [Term.subst_weaken]
    exact ih ((EqSubst.var_iff ctx B σ₁ σ₂).1 h).1
  | @succSecondOrder _ _ ctx _ A Θ B _ ih =>
    rw [Term.subst_weaken]
    exact ih ((EqSubst.secondOrder_iff ctx Θ B σ₁ σ₂).1 h).1

-- ADE: none.
/-- `(σ₁, σ₂) ∈ eq(Γ)` gives the second-order variable `X : (Θ ⊢ A) ∈ Γ` abstractions whose
instances by arguments in `eq(Θ[σ₁])` are equal closed terms of the type `A[σ₁⇑]` at these
arguments. -/
theorem EqSubst.secondOrderIn {Γ : Scope} {ps : List Grade} {ctx : Context 0 Γ} {X : Var Γ ps}
    {Θ : Telescope 0 Γ ps} {A : Term 0 (Γ.extend ps.length)} (hX : ctx.SecondOrderIn X Θ A)
    {σ₁ σ₂ : Subst 0 [] Γ} (h : EqSubst sig ι ctx σ₁ σ₂) :
    ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst σ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι ((σ₁ X).subst τ₁) ((σ₂ X).subst τ₂)
        ((A.subst (Subst.liftN _ σ₁)).subst τ₁) := by
  induction hX with
  | @zero _ _ ctx Θ A =>
    rw [Telescope.subst_weaken, Term.subst_liftN_weaken]
    exact ((EqSubst.secondOrder_iff ctx Θ A σ₁ σ₂).1 h).2
  | @succVar _ _ ctx _ Θ A B _ ih =>
    rw [Telescope.subst_weaken, Term.subst_liftN_weaken]
    exact ih ((EqSubst.var_iff ctx B σ₁ σ₂).1 h).1
  | @succSecondOrder _ _ _ ctx _ Θ A Θ' B _ ih =>
    rw [Telescope.subst_weaken, Term.subst_liftN_weaken]
    exact ih ((EqSubst.secondOrder_iff ctx Θ' B σ₁ σ₂).1 h).1

end

end Sic.Core
