module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Judgments
import Sic.Core.Soundness.Closed

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

open Sic.Grading

variable {k : Nat}

/-! ## Substitutions of a Context Extended by a Telescope -/

/-- The substitution `σ` of the scope `Γ` extended by `n` variables, on the variables of `Γ`. -/
def Subst.dropN {Ξ Γ : Scope} (n : Nat) (σ : Subst k Ξ (Γ.extend n)) : Subst k Ξ Γ :=
  fun x => σ (x.weakenN n)

/-- The substitution `σ` of the scope `Γ` extended by `n` variables, on these variables. -/
def Subst.topN {Ξ Γ : Scope} (n : Nat) (σ : Subst k Ξ (Γ.extend n)) :
    Subst k Ξ (Scope.extend [] n) :=
  fun x => σ (Ren.liftN n Ren.empty x)

/-- Substitutions that agree on every variable are equal. -/
theorem Subst.ext {Ξ Γ : Scope} {σ σ' : Subst k Ξ Γ} (h : ∀ {a} (x : Var Γ a), σ x = σ' x) :
    @Eq (Subst k Ξ Γ) σ σ' := by
  funext a x
  exact h x

/-- A substitution of the empty scope changes no closed term. -/
theorem Term.subst_empty (σ : Subst k [] []) (t : Term k []) : t.subst σ = t :=
  Term.subst_liftN_empty (a := 0) σ t

/-- `A[σ⇑][τ] = A[σ, τ]`. -/
theorem Term.subst_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) (t : Term k (Γ.extend n)) :
    (t.subst (Subst.liftN n σ)).subst τ = t.subst (Subst.append σ τ) :=
  Term.subst_subst_of (fun x => (Subst.append_eq_liftN σ τ x).symm) t

/-- `t̄[σ⇑][τ] = t̄[σ, τ]`. -/
theorem Args.subst_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) {ps : List Parameter} (ts : Args k (Γ.extend n) ps) :
    (ts.subst (Subst.liftN n σ)).subst τ = ts.subst (Subst.append σ τ) :=
  Args.subst_subst_of (fun x => (Subst.append_eq_liftN σ τ x).symm) ts

/-- The variables of a telescope, substituted by closed arguments of it, are these arguments. -/
theorem Args.bound_subst_toSubst :
    {ps : List Parameter} → (ts : Args k [] ps) → (Args.bound (Γ := []) ps).subst ts.toSubst = ts
  | [], .nil => rfl
  | _ :: ps, .cons t ts => by
    show Args.cons ((Term.var₀ (Var.weakenN ps.length .zero)).subst
        (Subst.append (Subst.closedSingle t) ts.toSubst))
      ((Args.bound (Γ := [.var]) ps).subst (Subst.append (Subst.closedSingle t) ts.toSubst)) = _
    rw [← Args.subst_append, Args.bound_subst, Args.bound_subst_toSubst ts]
    congr 1
    show (Subst.append (Subst.closedSingle t) ts.toSubst (Var.weakenN ps.length .zero)).instantiate
      .nil = t
    rw [Subst.append_weakenN]
    rfl

/-- The variables of a telescope, substituted by a closed substitution `σ` of its context followed by
closed arguments of it, are these arguments. -/
theorem Args.bound_subst_append {Γ : Scope} (σ : Subst k [] Γ) {ps : List Parameter}
    (ts : Args k [] ps) : (Args.bound (Γ := Γ) ps).subst (Subst.append σ ts.toSubst) = ts := by
  rw [← Args.subst_append, Args.bound_subst, Args.bound_subst_toSubst]

/-- The recursive results of the fields of a constructor, substituted by a closed substitution `σ` of
the context followed by closed arguments of the fields, are those of the arguments, at the motives
substituted by `σ`. -/
theorem Constructor.results_subst_append {j g k' : Nat} {Δ Γ : Scope}
    {c : Constructor j g k' Δ} {I : Instance j g} {names : List Name} {Cs : Motives k Γ}
    {R : Telescope k (Γ.extend (c.params I).length) (c.resultParams I names)}
    (h : c.results I names Cs = some R) (σ : Subst k [] Γ) (ts : Args k [] (c.params I)) :
    Motives.results names (Cs.subst σ) ((c.fields I).recursion names) ts.terms =
      some (R.subst (Subst.append σ ts.toSubst)) := by
  have h' := Motives.results_subst names (Subst.append σ ts.toSubst) _ h
  rwa [Motives.subst_rename_of (α := Ren.weakenN (c.params I).length) (θ' := σ)
      (fun x => Subst.append_weakenN σ _ x), ← Args.terms_subst,
    Args.bound_subst_append] at h'

/-- A term renamed under `n` new variables, substituted by `σ` followed by a substitution of them,
is the term substituted by `σ`. -/
theorem Term.subst_append_rename_weakenN {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) (t : Term k Γ) :
    (t.rename (Ren.weakenN n)).subst (Subst.append σ τ) = t.subst σ :=
  Term.subst_rename_of (fun x => Subst.append_weakenN σ τ x) t

/-- `(σ, τ)` gives the variables of `Γ` what `σ` gives them. -/
theorem Subst.dropN_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) {a : Scope.Entry} (x : Var Γ a) :
    Subst.dropN n (Subst.append σ τ) x = σ x :=
  Subst.append_weakenN σ τ x

/-- `(σ, τ)` gives the new variables what `τ` gives them. -/
theorem Subst.topN_append {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [] n)) {a : Scope.Entry} (x : Var (Scope.extend [] n) a) :
    Subst.topN n (Subst.append σ τ) x = τ x :=
  Subst.append_liftN_empty σ τ x

/-- `(σ, τ)` without its last `n` entries is `σ⇑` substituted by `τ` without its last `n` entries:
both give the variables of `Γ` what `σ` gives them, and `x` what `τ` gives it. -/
theorem Subst.dropN_append_succ {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [.var] n)) {a : Scope.Entry} (x : Var (.var :: Γ) a) :
    (Subst.lift σ x).subst (Subst.liftN a.params.length (Subst.dropN n τ)) =
      Subst.dropN n (Subst.append (n := n + 1) σ τ) x := by
  refine Eq.trans ?_
    (Subst.append_eq_liftN (n := n + 1) σ τ (Var.weakenN (Γ := .var :: Γ) n x)).symm
  show _ = (Subst.liftN n (Subst.lift σ) (x.weakenN n)).subst (Subst.liftN a.params.length τ)
  rw [Subst.liftN_weakenN, Term.subst_rename_of (Subst.liftN_rename_of a.params.length
    (α := Ren.weakenN n) (θ' := Subst.dropN n τ) fun _ => rfl)]

/-- `(σ, τ)` gives the first new variable what `τ` gives it. -/
theorem Subst.dropN_append_zero {Γ : Scope} {n : Nat} (σ : Subst k [] Γ)
    (τ : Subst k [] (Scope.extend [.var] n)) :
    Subst.dropN n (Subst.append (n := n + 1) σ τ) .zero = Subst.dropN n τ .zero :=
  (Subst.dropN_append_succ σ τ .zero).symm

/-- The substitution `σ` without its last `n + 1` entries, on its first new variable, is `σ` without
its last `n` entries. -/
theorem Subst.dropN_topN_zero {Γ : Scope} {n : Nat} (σ : Subst k [] (Scope.extend (.var :: Γ) n)) :
    Subst.dropN n (Subst.topN (Γ := Γ) (n + 1) σ) .zero = Subst.dropN n σ .zero := by
  show σ (Ren.liftN n (Ren.lift Ren.empty) (Var.weakenN n .zero)) = σ (Var.weakenN n .zero)
  rw [Ren.liftN_weakenN]
  rfl

/-- The last `n` variables of the last `n + 1` variables are the last `n` variables. -/
theorem Subst.topN_topN {Γ : Scope} {n : Nat} (σ : Subst k [] (Scope.extend (.var :: Γ) n)) :
    @Eq (Subst k [] (Scope.extend [] n)) (Subst.topN n (Subst.topN (Γ := Γ) (n + 1) σ))
      (Subst.topN n σ) :=
  Subst.ext fun x => congrArg (fun y => σ y)
    (Ren.liftN_comp_of n (α₃ := Ren.empty) (fun y => by cases y) x)

/-- The arguments of a telescope that a closed substitution of its variables gives them, the first
one first. -/
def Subst.args : (ps : List Parameter) → Subst k [] (Scope.extend [] ps.length) → Args k [] ps
  | [], _ => .nil
  | _ :: ps, τ =>
    .cons (Subst.dropN (Γ := [.var]) ps.length τ .zero) (Subst.args ps (Subst.topN ps.length τ))

/-- A closed substitution of the variables of a telescope is the substitution of its arguments. -/
theorem Subst.args_toSubst : (ps : List Parameter) → (τ : Subst k [] (Scope.extend [] ps.length)) →
    @Eq (Subst k [] (Scope.extend [] ps.length)) (Subst.args ps τ).toSubst τ
  | [], _ => Subst.ext fun x => nomatch x
  | _ :: ps, τ => Subst.ext fun x => by
    show Subst.append (Subst.closedSingle _) (Subst.args ps _).toSubst x = τ x
    rcases Var.cases_extend (Γ := [.var]) ps.length x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Subst.append_weakenN]
      cases y with
      | zero => rfl
      | succ y => nomatch y
    · rw [Subst.append_liftN_empty]
      exact congrArg (fun θ : Subst k [] (Scope.extend [] ps.length) => θ z)
        (Subst.args_toSubst ps (Subst.topN ps.length τ))

/-! ## Corecursors at Closed States -/

/-- The terms of renamed arguments are their terms renamed. -/
theorem Args.terms_rename {Γ Δ : Scope} (α : Ren Γ Δ) :
    {ps : List Parameter} → (ts : Args k Δ ps) → (ts.rename α).terms = ts.terms.rename α
  | [], .nil => rfl
  | _ :: _, .cons _ ts => congrArg _ (Args.terms_rename α ts)

/-- `(corec_r T from ȳ return Θ̄ with ḡ)[σ, t̄ / ȳ] = corec_r T[σ] from t̄ return Θ̄[σ] with ḡ[σ]`: the
corecursor at the variables of a state, substituted by `σ` followed by closed arguments of the
state, is the corecursor substituted by `σ`, from these arguments. -/
theorem Term.corecAt_subst_append {Γ Δ : Scope} (σ : Subst k [] Γ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Γ Δ)
    (Ss : States k Γ) (gs : CorecBranches k Γ) {ps' : List Parameter} (ss : Args k [] ps') :
    (Term.corecAt r D qs ls ps as Ss gs ps').subst (Subst.append σ ss.toSubst) =
      .corec r D qs ls ps (as.subst σ) ss.terms (Ss.subst σ) (gs.subst σ) := by
  rw [← Term.subst_append, Term.corecAt_subst, ← Term.instantiate_eq_subst,
    Term.corecAt_instantiate]

/-- Closed arguments renamed under the variables of a state, then substituted by closed arguments
of the state, are themselves. -/
theorem Args.rename_weakenN_subst {ps ps' : List Parameter} (ts : Args k [] ps)
    (ss : Args k [] ps') : (ts.rename (Ren.weakenN ps'.length)).subst ss.toSubst = ts :=
  (Args.subst_rename_of (θ' := fun x => Var.eta x) (fun x => by cases x) ts).trans
    (Args.subst_id_of (fun _ => rfl) ts)

/-- The motive at a position of motives renamed is the motive renamed, under its variables. -/
theorem Motives.get_rename {Γ Δ : Scope} (α : Ren Γ Δ) :
    {Cs : Motives k Δ} → {j n : Nat} → {C : Term k (Δ.extend (n + 1))} → Cs.get j = some ⟨n, C⟩ →
      (Cs.rename α).get j = some ⟨n, C.rename (Ren.liftN (n + 1) α)⟩
  | .nil, _, _, _, h => nomatch h
  | .cons .., 0, _, _, h => by cases h; rfl
  | .cons _ _ Cs, _ + 1, _, _, h => Motives.get_rename α (Cs := Cs) h

/-- Fields have recursive results when the motives have a motive without non-uniform parameters for
each type of the block. -/
theorem Motives.results_isSome (names : List Name) :
    {Δ : Scope} → {Cs : Motives k Δ} →
      (∀ D ∈ names, ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩) → (rs : List (Option Name)) →
      {ps : List Parameter} → (xs : Args k Δ ps) → rs.length = ps.length →
      (∀ D, some D ∈ rs → D ∈ names) →
        ∃ R, Motives.results names Cs rs (ps := ps) xs.terms = some R
  | _, Cs, hCs, some D :: rs, p :: ps, .cons x xs, hl, hrs => by
    obtain ⟨C, hC⟩ := hCs D (hrs D (List.mem_cons_self ..))
    obtain ⟨R, hR⟩ := Motives.results_isSome names (Cs := Cs.rename Ren.weaken)
      (fun D hD => let ⟨_, hC⟩ := hCs D hD; ⟨_, Motives.get_rename _ hC⟩) rs (xs.rename Ren.weaken)
      (Nat.succ.inj hl) (fun D hD => hrs D (List.mem_cons_of_mem _ hD))
    rw [Args.terms_rename] at hR
    refine ⟨.cons Grade.zero p (C.subst₀ (Subst₀.single x)) R, ?_⟩
    unfold Motives.results
    simp only [Args.terms, hC, hR]
    rfl
  | _, Cs, hCs, none :: rs, _ :: ps, .cons _ xs, hl, hrs => by
    obtain ⟨R, hR⟩ := Motives.results_isSome names hCs rs xs (Nat.succ.inj hl)
      (fun D hD => hrs D (List.mem_cons_of_mem _ hD))
    exact ⟨R, by unfold Motives.results; exact hR⟩
  | _, _, _, [], _, _, _, _ => ⟨.nil, by unfold Motives.results; rfl⟩
  | _, _, _, _ :: _, [], .nil, hl, _ => nomatch hl

/-- A constructor has recursive results when the motives have a motive without non-uniform
parameters for each type of the block. -/
theorem Constructor.results_isSome {j g k' : Nat} {Δ Γ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) {names : List Name} {Cs : Motives k Γ}
    (hCs : ∀ D ∈ names, ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩) :
    ∃ R, c.results I names Cs = some R :=
  Motives.results_isSome names (fun D hD => let ⟨_, hC⟩ := hCs D hD; ⟨_, Motives.get_rename _ hC⟩)
    _ (Args.bound (c.params I)) (Telescope.length_recursion names _)
    (fun _ hD => Telescope.mem_recursion hD)

/-- `g[σ⇑⇑][t̄ / z̄][s̄ / ȳ] = g[σ, s̄, t̄]`: a branch of a corecursor, substituted by a closed
substitution `σ` under the variables `ȳ` of its state and `z̄` of its arguments, instantiated by
closed arguments `t̄`, renamed under `ȳ`, then by closed arguments `s̄` of the state, is substituted
by `σ` followed by `s̄` and `t̄`. -/
theorem Term.instantiate_instantiate_subst {Γ : Scope} (σ : Subst k [] Γ) {ps' ps₁ : List Parameter}
    (g : Term k ((Γ.extend ps'.length).extend ps₁.length)) (ss : Args k [] ps')
    (ts : Args k [] ps₁) :
    ((g.subst (Subst.liftN ps₁.length (Subst.liftN ps'.length σ))).instantiate
        (ts.rename (Ren.weakenN ps'.length))).instantiate ss =
      g.subst (Subst.append (Subst.append σ ss.toSubst) ts.toSubst) := by
  rw [Term.instantiate_eq_subst, Term.instantiate_subst, Args.rename_weakenN_subst,
    Term.instantiate_eq_subst,
    Term.subst_subst_of (Subst.liftN_subst_of ps₁.length
      (fun x => (Subst.append_eq_liftN σ ss.toSubst x).symm)),
    Term.subst_append]

/-- `(β_⟶)` substitutes the closed arguments of the state and of the destructor in a branch
substituted by a closed substitution `σ`: `g[σ⇑⇑][s̄ / ȳ, t̄ / z̄] = g[σ, s̄, t̄]`. -/
theorem Term.instantiateTerms₂_subst_append {Γ : Scope} (σ : Subst k [] Γ)
    {ps' ps₁ : List Parameter} (g : Term k ((Γ.extend ps'.length).extend ps₁.length))
    (ss : Args k [] ps') (ts : Args k [] ps₁) :
    (g.subst (Subst.liftN ps₁.length (Subst.liftN ps'.length σ))).instantiateTerms₂ ss.terms
        ts.terms = some (g.subst (Subst.append (Subst.append σ ss.toSubst) ts.toSubst)) := by
  rw [Term.instantiateTerms₂, ← Args.terms_rename, Term.instantiateTerms_terms, Option.bind_some,
    Term.instantiateTerms_terms, Term.instantiate_instantiate_subst]

/-- `g[t̄ / z̄][s̄ / ȳ][σ] = g[σ, s̄[σ], t̄[σ]]`: a branch of a corecursor instantiated by arguments `t̄`,
renamed under the variables `ȳ` of its state, then by arguments `s̄` of the state, substituted by a
closed substitution `σ`, is substituted by `σ` followed by the arguments substituted. -/
theorem Term.instantiate_instantiate_subst_closed {Γ : Scope} (σ : Subst k [] Γ)
    {ps' ps₁ : List Parameter} (g : Term k ((Γ.extend ps'.length).extend ps₁.length))
    (ss : Args k Γ ps') (ts : Args k Γ ps₁) :
    ((g.instantiate (ts.rename (Ren.weakenN ps'.length))).instantiate ss).subst σ =
      g.subst (Subst.append (Subst.append σ (ss.subst σ).toSubst) (ts.subst σ).toSubst) := by
  have h : (ts.rename (Ren.weakenN ps'.length)).subst (Subst.liftN ps'.length σ) =
      (ts.subst σ).rename (Ren.weakenN ps'.length) :=
    (Args.subst_rename_of (fun x => Subst.liftN_weakenN _ σ x) ts).trans
      (Args.rename_subst_of (fun _ => rfl) ts).symm
  rw [Term.instantiate_subst, Term.instantiate_subst, h, Term.instantiate_instantiate_subst]

/-! ## Equal Substitutions -/

section

variable {sig : Signature} {ι : Interpretation}

/-- `(eq_ε)`. -/
theorem EqSubst.empty_iff (σ₁ σ₂ : Subst 0 [] []) : EqSubst sig ι .empty σ₁ σ₂ ↔ True := by
  rw [EqSubst]

-- ADE: `⊩ˢ≡∷∙⇔`, in `Definition/LogicalRelation/Substitution.agda`.
/-- `(eq_x)`. -/
theorem EqSubst.var_iff {Γ : Scope} (ctx : Context 0 Γ) (A : Term 0 Γ)
    (σ₁ σ₂ : Subst 0 [] (.var :: Γ)) :
    EqSubst sig ι (ctx.var A) σ₁ σ₂ ↔ EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
      ValidEqTerm₀ sig ι (σ₁ .zero) (σ₂ .zero) (A.subst (Subst.tail σ₁)) := by
  rw [EqSubst]

/-- `(eq_X)`. -/
theorem EqSubst.secondOrder_iff {Γ : Scope} {ps : List Parameter} (ctx : Context 0 Γ)
    (Θ : Telescope 0 Γ ps) (A : Term 0 (Γ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
    (σ₁ σ₂ : Subst 0 [] (.secondOrder ps ψ :: Γ)) :
    EqSubst sig ι (ctx.secondOrder Θ A ψ) σ₁ σ₂ ↔ EqSubst sig ι ctx (Subst.tail σ₁) (Subst.tail σ₂) ∧
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
    {Γ : Scope} → {ps : List Parameter} → (ctx : Context 0 Γ) → (Θ : Telescope 0 Γ ps) →
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
        rw [Term.subst_rename_of (Subst.liftN_rename_of _ (α := Ren.weaken)
          (θ' := Subst.tail (Subst.dropN ps.length (Subst.topN (Γ := Γ) (ps.length + 1) σ₁)))
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
theorem EqSubst.append_append_iff {Γ : Scope} {ps : List Parameter} (ctx : Context 0 Γ)
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
theorem EqSubst.telescope_cons_iff {Γ : Scope} {ps : List Parameter} (q : Grade) (p : Parameter) (A : Term 0 Γ)
    (Θ : Telescope 0 (.var :: Γ) ps) (σ : Subst 0 [] Γ)
    (τ₁ τ₂ : Subst 0 [] (Scope.extend [.var] ps.length)) :
    EqSubst sig ι (Context.empty.append ((Telescope.cons q p A Θ).subst σ)) τ₁ τ₂ ↔
      ValidEqTerm₀ sig ι (Subst.dropN _ τ₁ .zero) (Subst.dropN _ τ₂ .zero) (A.subst σ) ∧
        EqSubst sig ι
          (Context.empty.append (Θ.subst (Subst.dropN (Γ := .var :: Γ) ps.length (Subst.append (n := ps.length + 1) σ τ₁))))
          (Subst.topN _ τ₁) (Subst.topN _ τ₂) := by
  have hΘ : (Θ.subst (Subst.lift σ)).subst (Subst.dropN ps.length τ₁) =
      Θ.subst (Subst.dropN (Γ := .var :: Γ) ps.length (Subst.append (n := ps.length + 1) σ τ₁)) :=
    Telescope.subst_subst_of (Subst.dropN_append_succ σ τ₁) Θ
  have hA : (A.subst σ).subst (Subst.tail (Subst.dropN ps.length τ₁)) = A.subst σ :=
    Term.subst_empty _ _
  show EqSubst sig ι ((Context.empty.var (A.subst σ)).append (Θ.subst (Subst.lift σ))) τ₁ τ₂ ↔ _
  rw [EqSubst.append_iff, EqSubst.var_iff, EqSubst.empty_iff, hΘ, hA, true_and]

/-- A meaningful context is meaningful before the entries of a telescope. -/
theorem ValidCtx₀.append_left :
    {Γ : Scope} → {ps : List Parameter} → {ctx : Context 0 Γ} → {Θ : Telescope 0 Γ ps} →
      ValidCtx₀ sig ι (ctx.append Θ) → ValidCtx₀ sig ι ctx
  | _, [], _, .nil, h => h
  | _, _ :: _, ctx, .cons _ _ A _, h => ((validCtx₀_var ctx A).1 (ValidCtx₀.append_left h)).1

/-- A meaningful telescope has the same equal substitutions at two equal substitutions of its
context: `eq(Θ[σ₁]) = eq(Θ[σ₂])` when `(σ₁, σ₂) ∈ eq(Γ)` and `Σ ⊨ Γ, Θ`. -/
theorem EqSubst.telescope_iff :
    {Γ : Scope} → {ps : List Parameter} → {ctx : Context 0 Γ} → {Θ : Telescope 0 Γ ps} →
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
            (Subst.dropN (Γ := .var :: _) ps.length (Subst.append (n := ps.length + 1) σ₁ τ₁))))
            (Subst.topN (Γ := [.var]) ps.length τ₁) (Subst.topN (Γ := [.var]) ps.length τ₂) ↔
          EqSubst sig ι (Context.empty.append (Θ.subst
            (Subst.dropN (Γ := .var :: _) ps.length (Subst.append (n := ps.length + 1) σ₂ τ₁))))
            (Subst.topN (Γ := [.var]) ps.length τ₁) (Subst.topN (Γ := [.var]) ps.length τ₂)) := by
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
  | _, .secondOrder (ps := ps) ctx Θ A ψ, hV => by
    obtain ⟨hΘ, hA⟩ := (validCtx₀_secondOrder ctx Θ A ψ).1 hV
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
    · obtain ⟨hσ, hB⟩ := (EqSubst.secondOrder_iff ctx Θ A _ σ₁ σ₂).1 h
      have hσ₁ := transΓ _ _ _ hσ (symmΓ _ _ hσ)
      refine (EqSubst.secondOrder_iff ctx Θ A _ σ₂ σ₁).2 ⟨symmΓ _ _ hσ, fun τ₁ τ₂ hτ => ?_⟩
      have hτ' := symΘ hσ₁ ((EqSubst.telescope_iff hΘ hσ τ₁ τ₂).2 hτ)
      exact (hB τ₂ τ₁ hτ').symm.conv (hAapp hσ hτ')
    · obtain ⟨hσ₁₂, hB₁₂⟩ := (EqSubst.secondOrder_iff ctx Θ A _ σ₁ σ₂).1 h₁₂
      obtain ⟨hσ₂₃, hB₂₃⟩ := (EqSubst.secondOrder_iff ctx Θ A _ σ₂ σ₃).1 h₂₃
      have hσ₁ := transΓ _ _ _ hσ₁₂ (symmΓ _ _ hσ₁₂)
      refine (EqSubst.secondOrder_iff ctx Θ A _ σ₁ σ₃).2 ⟨transΓ _ _ _ hσ₁₂ hσ₂₃, fun τ₁ τ₂ hτ => ?_⟩
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

/-! ## Arguments of a Telescope

The arguments `t̄` of a telescope `Θ` in a context `Γ` mean, at two equal closed substitutions `σ₁`
and `σ₂` of `Γ`, equal substitutions `[t̄[σ₁] / x̄]` and `[ū[σ₂] / x̄]` of the context that `Θ[σ₁]`
forms, as `(⊨Γ_tel≡)` says; the substitution of the first argument `t` then of `σ₁` is the
substitution of `σ₁` followed by `t[σ₁]`, as the rule `(tel_,≡)` needs.
-/

/-- `Θ[t / x][σ] = Θ[σ, t[σ]]`, where `(σ, τ)` gives `x` the closed term `t[σ]`. -/
theorem Telescope.subst₀_single_subst {Γ : Scope} {ps : List Parameter} (Θ : Telescope 0 (.var :: Γ) ps)
    (t : Term 0 Γ) (σ : Subst 0 [] Γ) (τ : Subst 0 [] (Scope.extend [.var] ps.length))
    (ht : Subst.dropN ps.length τ .zero = t.subst σ) :
    Θ.subst (Subst.dropN (Γ := .var :: Γ) ps.length (Subst.append (n := ps.length + 1) σ τ)) =
      (Θ.subst₀ (Subst₀.single t)).subst σ := by
  refine Eq.symm ((Telescope.subst_subst₀_of (σ' := Subst₀.id) ⟨fun x y e => ?_, fun x u e => ?_⟩
    Θ).trans (Telescope.subst₀_id_of (fun _ => rfl) _))
  · cases x with
    | zero => cases e
    | succ x =>
      cases e
      exact (Term.subst₀_id_of (Subst₀.liftN_id_of _ fun _ => rfl) _).trans
        ((Subst.dropN_append_succ σ τ y.succ).symm.trans
          ((Term.subst_rename_of (Subst.liftN_rename_of _
            (θ' := fun y => Subst.dropN ps.length τ y.succ) fun _ => rfl) (σ y)).trans
            (Term.subst_liftN_empty _ _)))
  · cases x with
    | zero =>
      cases e
      exact (Term.subst₀_id _).trans ((Subst.dropN_append_zero σ τ).trans ht)
    | succ x => cases e

/-- Closed arguments of a closed telescope `x : A, Θ` are equal when their first terms are equal
terms of `A` and the rest are equal arguments of `Θ` at the first term of the first ones. -/
theorem EqSubst.args_cons_iff {ps : List Parameter} {q : Grade} {p : Parameter} {A : Term 0 []}
    {Θ : Telescope 0 [.var] ps} {t u : Term 0 []} {ts us : Args 0 [] ps} :
    EqSubst sig ι (Context.empty.append (.cons q p A Θ)) (Args.cons t ts).toSubst
        (Args.cons u us).toSubst ↔
      ValidEqTerm₀ sig ι t u A ∧
        EqSubst sig ι (Context.empty.append (Θ.subst₀ (Subst₀.single t))) ts.toSubst us.toSubst := by
  let σ : Subst 0 [] [] := fun x => nomatch x
  have hc : Telescope.subst σ (.cons q p A Θ) = .cons q p A Θ :=
    Telescope.subst_id_of (fun x => by cases x) _
  have d₁ : Subst.dropN ps.length (Subst.append (Subst.closedSingle t) ts.toSubst) .zero = t :=
    Subst.dropN_append _ _ .zero
  have d₂ : Subst.dropN ps.length (Subst.append (Subst.closedSingle u) us.toSubst) .zero = u :=
    Subst.dropN_append _ _ .zero
  show EqSubst sig ι (Context.empty.append (.cons q p A Θ))
    (Subst.append (Subst.closedSingle t) ts.toSubst)
    (Subst.append (Subst.closedSingle u) us.toSubst) ↔ _
  rw [← hc, EqSubst.telescope_cons_iff, d₁, d₂, Term.subst_empty,
    Telescope.subst₀_single_subst Θ t σ _ (d₁.trans (Term.subst_empty σ t).symm),
    Telescope.subst_id_of (fun x => by cases x),
    EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))]

/-! ## Entries of a Context under Equal Substitutions -/

/-- `A[↑][σ] = A[σ without its last entry]`: a type weakened past the last entry of a context, at a
substitution of that context. -/
theorem Term.subst_weaken {Γ : Scope} {e : Scope.Entry} (σ : Subst k [] (e :: Γ)) (A : Term k Γ) :
    (A.rename Ren.weaken).subst σ = A.subst (Subst.tail σ) :=
  Term.subst_rename_of (fun _ => rfl) A

/-- `A[↑⇑][σ⇑] = A[(σ without its last entry)⇑]`: a type in the scope of a telescope weakened past
the last entry of a context, at a substitution of that context. -/
theorem Term.subst_liftN_weaken {Γ : Scope} {e : Scope.Entry} (n : Nat) (σ : Subst k [] (e :: Γ))
    (A : Term k (Γ.extend n)) :
    (A.rename (Ren.liftN n Ren.weaken)).subst (Subst.liftN n σ) =
      A.subst (Subst.liftN n (Subst.tail σ)) :=
  Term.subst_rename_of (Subst.liftN_rename_of n fun _ => rfl) A

/-- `Θ[↑][σ] = Θ[σ without its last entry]`: a telescope weakened past the last entry of a context,
at a substitution of that context. -/
theorem Telescope.subst_weaken {Γ : Scope} {e : Scope.Entry} {qs : List Parameter} (σ : Subst k [] (e :: Γ))
    (Θ : Telescope k Γ qs) : (Θ.rename Ren.weaken).subst σ = Θ.subst (Subst.tail σ) :=
  Telescope.subst_rename_of (fun _ => rfl) Θ

end

end Sic.Core
