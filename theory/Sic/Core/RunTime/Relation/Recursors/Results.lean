module

public import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Lifting.Substitution
import Sic.Core.Soundness.Substitution

/-!
# Recursive Results of the Constructors Without Nested Field

The typing and the reduction give a branch of a recursor a recursive result for each recursive field
and for each field nested below a codata type, as `Results` defines them, while the run time
computes the results of the recursive fields only, `res_C̄` and `f(D, t̄)`, which this module
defines, where a nested field leaves them undefined.
The usage of a recursor excludes the nested fields, so that the two definitions then agree, which is
what this module proves, so that the run time of the recursors reads the typing and the reduction.

The Lean keeps `res_C̄` and `f(D, t̄)` until the run time computes the results of the nested fields;
this module then has no reader.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Recursive Results of the Run Time -/

-- ADE: none.
/-- `res_C̄(x̄)`: the recursive results of the fields `x̄`, whose entries have the parameters `ps` and
whose nestings in the block whose types have the names `names` are `ns`, a variable
`y : C_D[x / z]` for each recursive field `x` of the type `D`, at the motive `C_D` of `D` in `C̄`,
in order, if no field is nested and `C̄` has a motive without non-uniform parameters for each of
these types: the results of the recursive fields, which the run time reads.
They are not definitions of the RFC, which defines the recursive results as a relation: the run time
reads them until it computes the results of the nested fields. -/
def Motives.results (names : List Name) : {Δ : Scope} → Motives k Δ → (ns : List (Nest Name)) →
    {ps : List Parameter} → Terms k Δ → Option (Telescope k Δ (Telescope.nestResultParams ns ps))
  | _, Cs, .direct D :: ns, p :: ps, .cons x xs =>
    match Cs.get (names.idxOf D) with
    | some ⟨0, C⟩ => (Motives.results names (Cs.rename Ren.weaken) ns (ps := ps)
        (xs.rename Ren.weaken)).map (Telescope.cons Grade.zero p (C.subst₀ (Subst₀.single x)))
    | _ => none
  | _, Cs, .plain :: ns, _ :: ps, .cons _ xs => Motives.results names Cs ns (ps := ps) xs
  | _, _, .inst _ :: _, _ :: _, _ => none
  | _, _, .direct _ :: _, _ :: _, .nil | _, _, .plain :: _, _ :: _, .nil => none
  | _, _, [], _, _ | _, _, .direct _ :: _, [], _ | _, _, .plain :: _, [], _
  | _, _, .inst _ :: _, [], _ => some .nil

-- ADE: none.
/-- `f(D, t̄)` for the arguments `t̄` of a telescope whose entries have the parameters `ps`: the term
`f D t` for each term `t` of a recursive field of the type `D`, whose nesting in `ns` holds `D`, in
order, if no field is nested: the arguments of the results of the recursive fields, which the run
time reads.
They are not definitions of the RFC, which defines the recursive results as a relation: the run time
reads them until it computes the results of the nested fields. -/
def Args.results {Γ : Scope} (f : Name → Term k Γ → Term k Γ) :
    (ns : List (Nest Name)) → {ps : List Parameter} → Args k Γ ps →
      Option (Args k Γ (Telescope.nestResultParams ns ps))
  | .direct D :: ns, _ :: _, .cons t ts => (Args.results f ns ts).map (.cons (f D t))
  | .plain :: ns, _ :: _, .cons _ ts => Args.results f ns ts
  | .inst _ :: _, _ :: _, _ => none
  | [], _, _ | .direct _ :: _, [], .nil | .plain :: _, [], .nil | .inst _ :: _, [], .nil =>
    some .nil

-- ADE: none.
/-- `res_C̄(Θ_c)`: the recursive results of the fields of the constructor `c` at the instance `I`, in
a block whose types have the names `names`, in the scope `Γ` extended by its fields, for the motives
`C̄` in `Γ`.
They are not definitions of the RFC, which defines the recursive results as a relation: the run time
reads them until it computes the results of the nested fields. -/
def Constructor.results {j g k' : Nat} {Δ Γ : Scope} (c : Constructor j g k' Δ) (I : Instance j g)
    (names : List Name) (Cs : Motives k Γ) :
    Option (Telescope k (Γ.extend (c.params I).length) (c.nestResultParams I names)) :=
  Motives.results names (Cs.rename (Ren.weakenN _)) ((c.fields I).nest names)
    (Args.bound (Γ := Γ) (c.params I)).terms

/-- The recursive results of terms, substituted, are those of the terms substituted, at the motives
substituted. -/
theorem Motives.results_subst (names : List Name) :
    {Γ Δ : Scope} → (θ : Subst k Γ Δ) → {Cs : Motives k Δ} → (ns : List (Nest Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} →
      {R : Telescope k Δ (Telescope.nestResultParams ns ps)} →
      Motives.results names Cs ns xs = some R →
        Motives.results names (Cs.subst θ) ns (xs.subst θ) = some (R.subst θ)
  | _, _, θ, Cs, .direct D :: ns, p :: ps, .cons x xs, R, h => by
    unfold Motives.results at h
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at h; cases h
    | some a =>
      obtain ⟨n, C⟩ := a
      cases n with
      | succ => simp only [hC] at h; cases h
      | zero =>
        simp only [hC] at h
        obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 h
        have ih := Motives.results_subst names (Subst.lift θ) ns hR'
        rw [Motives.subst_lift_rename_weaken, Terms.subst_lift_rename_weaken] at ih
        unfold Motives.results
        simp only [Terms.subst, Motives.get_subst θ hC]
        simp only [ih, Telescope.subst]
        rw [Term.subst_subst₀_of (Subst₀.Swaps.single x θ) C]
        rfl
  | _, _, θ, Cs, .plain :: ns, _ :: ps, .cons _ xs, R, h => by
    unfold Motives.results at h ⊢
    exact Motives.results_subst names θ ns h
  | _, _, _, _, .inst _ :: _, _ :: _, _, _, h => by
    unfold Motives.results at h; cases h
  | _, _, _, _, .direct _ :: _, _ :: _, .nil, _, h
  | _, _, _, _, .plain :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, _, _, [], _, _, R, h | _, _, _, _, .direct _ :: _, [], _, R, h
  | _, _, _, _, .plain :: _, [], _, R, h | _, _, _, _, .inst _ :: _, [], _, R, h => by
    unfold Motives.results at h ⊢
    cases h
    rfl

/-- Recursive results of terms whose levels are instantiated, at the motives instantiated, are those
of the terms, instantiated. -/
theorem Motives.results_substLevels_inv {k' : Nat} (ls' : Fin k → Level k') (names : List Name) :
    {Δ : Scope} → {Cs : Motives k Δ} → (ns : List (Nest Name)) →
      {ps : List Parameter} → {xs : Terms k Δ} →
      {R' : Telescope k' Δ (Telescope.nestResultParams ns ps)} →
      Motives.results names (Cs.substLevels ls') ns (xs.substLevels ls') = some R' →
        ∃ R, Motives.results names Cs ns xs = some R ∧ R' = R.substLevels ls'
  | _, Cs, .direct D :: ns, p :: ps, .cons x xs, R', h => by
    unfold Motives.results at h
    simp only [Terms.substLevels] at h
    cases hC' : (Cs.substLevels ls').get (names.idxOf D) with
    | none => simp only [hC'] at h; cases h
    | some a =>
      obtain ⟨n, C'⟩ := a
      cases n with
      | succ => simp only [hC'] at h; cases h
      | zero =>
        obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_substLevels ls' hC'
        simp only [hC'] at h
        obtain ⟨R'', hR'', rfl⟩ := Option.map_eq_some_iff.1 h
        rw [← Motives.substLevels_rename, ← Terms.substLevels_rename] at hR''
        obtain ⟨R₀, hR₀, rfl⟩ := Motives.results_substLevels_inv ls' names ns hR''
        refine ⟨.cons Grade.zero p (C₀.subst₀ (Subst₀.single x)) R₀, ?_, ?_⟩
        · unfold Motives.results
          simp only [hC₀, hR₀]
          rfl
        · show Telescope.cons Grade.zero p _ _ = Telescope.cons Grade.zero p _ _
          rw [Term.substLevels_subst₀_of (σ := Subst₀.single x)
            (σ' := Subst₀.single (x.substLevels ls')) (fun y => by cases y <;> rfl) C₀]
          rfl
  | _, Cs, .plain :: ns, _ :: ps, .cons _ xs, R', h => by
    unfold Motives.results at h ⊢
    exact Motives.results_substLevels_inv ls' names ns h
  | _, _, .inst _ :: _, _ :: _, _, _, h => by
    unfold Motives.results at h; cases h
  | _, _, .direct _ :: _, _ :: _, .nil, _, h | _, _, .plain :: _, _ :: _, .nil, _, h => by
    unfold Motives.results at h; cases h
  | _, _, [], _, _, R', h | _, _, .direct _ :: _, [], _, R', h
  | _, _, .plain :: _, [], _, R', h | _, _, .inst _ :: _, [], _, R', h => by
    unfold Motives.results at h
    cases h
    exact ⟨.nil, by unfold Motives.results; rfl, rfl⟩

/-- The recursive results of a constructor at motives whose levels are instantiated are its
recursive results at the motives, instantiated. -/
theorem Constructor.results_substLevels_inv {k' : Nat} (ls' : Fin k → Level k') {j g k'' : Nat}
    {Δ Γ : Scope} {c : Constructor j g k'' Δ} {I : Instance j g} {names : List Name}
    {Cs : Motives k Γ}
    {R' : Telescope k' (Γ.extend (c.params I).length) (c.nestResultParams I names)}
    (h : c.results I names (Cs.substLevels ls') = some R') :
    ∃ R, c.results I names Cs = some R ∧ R' = R.substLevels ls' := by
  unfold Constructor.results at h ⊢
  rw [← Motives.substLevels_rename, ← Args.substLevels_bound ls' (c.params I),
    Args.terms_substLevels] at h
  exact Motives.results_substLevels_inv ls' names _ h

/-- The recursive results of the fields of a constructor, substituted by a closed substitution `σ` of
the context followed by closed arguments of the fields, are those of the arguments, at the motives
substituted by `σ`. -/
theorem Constructor.results_subst_append {j g k' : Nat} {Δ Γ : Scope}
    {c : Constructor j g k' Δ} {I : Instance j g} {names : List Name} {Cs : Motives k Γ}
    {R : Telescope k (Γ.extend (c.params I).length) (c.nestResultParams I names)}
    (h : c.results I names Cs = some R) (σ : Subst k [] Γ) (ts : Args k [] (c.params I)) :
    Motives.results names (Cs.subst σ) ((c.fields I).nest names) ts.terms =
      some (R.subst (Subst.append σ ts.toSubst)) := by
  have h' := Motives.results_subst names (Subst.append σ ts.toSubst) _ h
  rwa [Motives.subst_rename_of (α := Ren.weakenN (c.params I).length) (θ' := σ)
      (fun x => Subst.append_weakenN σ _ x), ← Args.terms_subst,
    Args.bound_subst_append] at h'

/-- Fields none of which is nested have recursive results when the motives have a motive without
non-uniform parameters for each type of the block. -/
theorem Motives.results_isSome (names : List Name) :
    {Δ : Scope} → {Cs : Motives k Δ} →
      (∀ D ∈ names, ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩) → (ns : List (Nest Name)) →
      {ps : List Parameter} → (xs : Args k Δ ps) → ns.length = ps.length →
      (∀ D, .direct D ∈ ns → D ∈ names) → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
        ∃ R, Motives.results names Cs ns (ps := ps) xs.terms = some R
  | _, Cs, hCs, .direct D :: ns, p :: ps, .cons x xs, hl, hns, hn => by
    obtain ⟨C, hC⟩ := hCs D (hns D (List.mem_cons_self ..))
    obtain ⟨R, hR⟩ := Motives.results_isSome names (Cs := Cs.rename Ren.weaken)
      (fun D hD => let ⟨_, hC⟩ := hCs D hD; ⟨_, Motives.get_rename _ hC⟩) ns (xs.rename Ren.weaken)
      (Nat.succ.inj hl) (fun D hD => hns D (List.mem_cons_of_mem _ hD))
      (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))
    rw [Args.terms_rename] at hR
    refine ⟨.cons Grade.zero p (C.subst₀ (Subst₀.single x)) R, ?_⟩
    unfold Motives.results
    simp only [Args.terms, hC, hR]
    rfl
  | _, Cs, hCs, .plain :: ns, _ :: ps, .cons _ xs, hl, hns, hn => by
    obtain ⟨R, hR⟩ := Motives.results_isSome names hCs ns xs (Nat.succ.inj hl)
      (fun D hD => hns D (List.mem_cons_of_mem _ hD)) (fun ν hν => hn ν (List.mem_cons_of_mem _ hν))
    exact ⟨R, by unfold Motives.results; exact hR⟩
  | _, _, _, .inst ms :: _, _ :: _, _, _, _, hn => absurd rfl (hn _ List.mem_cons_self ms)
  | _, _, _, [], _, _, _, _, _ => ⟨.nil, by unfold Motives.results; rfl⟩
  | _, _, _, _ :: _, [], .nil, hl, _, _ => nomatch hl

/-- A constructor none of whose fields is nested has recursive results when the motives have a
motive without non-uniform parameters for each type of the block. -/
theorem Constructor.results_isSome {j g k' : Nat} {Δ Γ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) {names : List Name} {Cs : Motives k Γ}
    (hCs : ∀ D ∈ names, ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩)
    (hn : ∀ ν ∈ (c.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    ∃ R, c.results I names Cs = some R :=
  Motives.results_isSome names (fun D hD => let ⟨_, hC⟩ := hCs D hD; ⟨_, Motives.get_rename _ hC⟩)
    _ (Args.bound (c.params I)) (Telescope.length_nest names _)
    (fun _ hD => Telescope.mem_names_of_direct_mem hD) hn

/-- The recursive results `f₁(D, t̄₁)` and `f₂(D, t̄₂)` of closed arguments of fields are equal
substitutions of the recursive results of `t̄₁` at closed motives `C̄`, when each pair `f₁ D t₁`
and `f₂ D t₂` at the recursive fields are equal terms of the motive of `D` at `t₁`. -/
theorem EqSubst.results {ι : Interpretation} {names : List Name} {f₁ f₂ : Name → Term 0 [] → Term 0 []} :
    {Cs : Motives 0 []} → (ns : List (Nest Name)) → {ps : List Parameter} →
      (ts₁ ts₂ : Args 0 [] ps) → {R : Telescope 0 [] (Telescope.nestResultParams ns ps)} →
      {rs₁ rs₂ : Args 0 [] (Telescope.nestResultParams ns ps)} →
      Motives.results names Cs ns ts₁.terms = some R → ts₁.results f₁ ns = some rs₁ →
      ts₂.results f₂ ns = some rs₂ →
      Terms.RecRel (fun D t₁ t₂ => ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        ValidEqTerm₀ sig ι (f₁ D t₁) (f₂ D t₂) (C.subst₀ (Subst₀.single t₁)))
        (ns.map Nest.blockName) ts₁.terms ts₂.terms →
      EqSubst sig ι (Context.empty.append R) rs₁.toSubst rs₂.toSubst
  | Cs, .direct D :: ns, p :: ps, .cons t₁ ts₁, .cons t₂ ts₂, R, rs₁, rs₂, hR, hrs₁, hrs₂,
      hQQ => by
    obtain ⟨hQ, hQs⟩ := hQQ
    obtain ⟨rs₁', hrs₁', rfl⟩ := Option.map_eq_some_iff.1 hrs₁
    obtain ⟨rs₂', hrs₂', rfl⟩ := Option.map_eq_some_iff.1 hrs₂
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
            rs₁'.toSubst) .zero = f₁ D t₁ := Subst.dropN_append _ _ .zero
        have d₂ : Subst.dropN _ (Subst.append (Subst.closedSingle (f₂ D t₂))
            rs₂'.toSubst) .zero = f₂ D t₂ := Subst.dropN_append _ _ .zero
        show EqSubst sig ι (Context.empty.append (.cons Grade.zero p (C.subst₀ (Subst₀.single t₁)) R'))
          (Subst.append (Subst.closedSingle (f₁ D t₁)) rs₁'.toSubst)
          (Subst.append (Subst.closedSingle (f₂ D t₂)) rs₂'.toSubst)
        rw [← hc, EqSubst.telescope_cons_iff, d₁, d₂, Term.subst_empty,
          EqSubst.congr (Subst.ext (Subst.topN_append _ _)) (Subst.ext (Subst.topN_append _ _))]
        refine ⟨hQ C hC, ?_⟩
        have hR'' := Motives.results_subst names (Subst.dropN (Γ := [.var]) _
          (Subst.append (n := (Telescope.nestResultParams ns ps).length + 1) σ
            (Subst.append (Subst.closedSingle (f₁ D t₁)) rs₁'.toSubst))) ns hR'
        rw [Motives.subst_rename_of (θ' := σ) (fun x => by cases x),
          Motives.subst_id_of (fun x => by cases x), Terms.subst_rename_of (θ' := σ)
            (fun x => by cases x), Terms.subst_id_of (fun x => by cases x)] at hR''
        exact EqSubst.results ns ts₁ ts₂ hR'' hrs₁' hrs₂' hQs
  | Cs, .plain :: ns, _ :: ps, .cons _ ts₁, .cons _ ts₂, R, rs₁, rs₂, hR, hrs₁, hrs₂, hQs => by
    unfold Motives.results at hR
    exact EqSubst.results ns ts₁ ts₂ hR hrs₁ hrs₂ hQs
  | _, .inst _ :: _, _ :: _, _, _, _, _, _, hR, _, _, _ => by
    unfold Motives.results at hR; cases hR
  | _, [], _, _, _, R, _, _, hR, _, _, _ | _, .direct _ :: _, [], .nil, .nil, R, _, _, hR, _, _, _
  | _, .plain :: _, [], .nil, .nil, R, _, _, hR, _, _, _
  | _, .inst _ :: _, [], .nil, .nil, R, _, _, hR, _, _, _ => by
    unfold Motives.results at hR
    cases hR
    exact (EqSubst.empty_iff _ _).2 trivial

/-! ## Recursive Results -/

-- ADE: none.
/-- The recursive results of fields none of which is nested are their recursive results `res_C̄`,
at motives that hold the motive of each type of the block that the lifting gives a motive. -/
theorem Terms.ResultTypes.results (names : List Name) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} → {πs : List Grade} →
      Terms.ResultTypes sig v ρ ns ps As xs R πs → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
      ∀ Cs : Motives k Δ',
        (∀ D b, ρ.block D = some b → Cs.get (names.idxOf D) = some ⟨0, b.motive⟩) →
        ∃ R', Motives.results names Cs ns (ps := ps) (xs.rename ρ.ren) = some R' ∧
          (⟨_, R'⟩ : (ps'' : List Parameter) × Telescope k Δ' ps'') = ⟨ps', R⟩
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _ => ⟨.nil, by unfold Motives.results; rfl, rfl⟩
  | _, _, _, _, _, _, _, _, _, _, .plain h, hns, Cs, hCs => by
    obtain ⟨R', hR', he⟩ := h.results names (fun ν hν => hns ν (List.mem_cons_of_mem _ hν)) Cs hCs
    refine ⟨R', ?_, he⟩
    rw [Terms.rename]
    unfold Motives.results
    exact hR'
  | _, _, ρ, _, _, _, _, _, _, _, .recursive (D := D) (p := p) (x := x) (xs := xs) (b := b) hD h,
      hns, Cs, hCs => by
    obtain ⟨R', hR', he⟩ := h.results names (fun ν hν => hns ν (List.mem_cons_of_mem _ hν))
      (Cs.rename Ren.weaken) (fun D' b' hb' => by
        obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb'
        exact Motives.get_rename Ren.weaken (hCs D' b₀ hb₀))
    cases he
    refine ⟨.cons Grade.zero p (b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))) R', ?_, rfl⟩
    rw [Terms.rename]
    unfold Motives.results
    have e : (xs.rename ρ.ren).rename (Ren.weaken (e := .var)) =
        xs.rename (ρ.weaken (e := .var)).ren :=
      Terms.rename_rename_of (fun _ => rfl) xs
    rw [← e] at hR'
    simp only [hCs D b hD, hR']
    rfl
  | _, _, _, _, _, _, _, _, _, _, .nested (ms := ms) _ _, hns, _, _ =>
    absurd rfl (hns _ List.mem_cons_self ms)

-- ADE: none.
/-- The terms `f(D, t̄)` of the recursive fields are the recursive results of the terms of fields
none of which is nested, where `f` at a type of the block and at a term is the result of this term
that the computation gives. -/
theorem Telescope.resultTerms_results {k' : Nat} {Γ : Scope} {ρ : Lifting k Γ Γ}
    {φ : Name → Term k (.var :: Γ)} (names : List Name) :
    {Ξ : Scope} → {ps : List Parameter} → (Θ' : Telescope k' Ξ ps) → (Θ : Telescope k Γ ps) →
      (ts : Args k Γ ps) → (∀ ν ∈ Θ'.nest names, ∀ ms, ν ≠ .inst ms) →
        ∃ rs, ts.results (fun D t => (φ D).subst₀ (Subst₀.single t)) (Θ'.nest names) = some rs ∧
          Terms.ResultTerms sig v ρ φ (Θ'.nest names) ps (Θ.typesAt ts) ts.terms rs
  | _, [], .nil, .nil, .nil, _ => ⟨.nil, rfl, .nil⟩
  | _, _ :: _, .cons _ _ A Θ', .cons _ _ _ Θ, .cons t ts, h => by
    obtain ⟨rs, hrs, ih⟩ := Telescope.resultTerms_results (ρ := ρ) (φ := φ) names Θ'
      (Θ.subst₀ (Subst₀.single t)) ts fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    have hA := h (A.blockNest names) List.mem_cons_self
    show ∃ rs', Args.results _ (A.blockNest names :: Θ'.nest names) (.cons t ts) = some rs' ∧
      Terms.ResultTerms sig v ρ φ (A.blockNest names :: Θ'.nest names) _ (.cons _ _) (.cons _ _) rs'
    cases hN : A.blockNest names with
    | plain => exact ⟨rs, hrs, .plain ih⟩
    | direct D => exact ⟨_, by show Option.map _ (Args.results _ _ ts) = _; rw [hrs]; rfl,
      .recursive ih⟩
    | inst ms => exact absurd hN (hA ms)

/-! ## Recursive Results of a Constructor -/

section

variable {j g k' : Nat} {Δ Γ : Scope} {c : Constructor j g k' Δ} {I : Instance j g}
  {names : List Name}

-- ADE: none.
/-- The recursive results of the fields of a constructor none of which is nested, in a recursor,
are their recursive results `res_C̄` at the motives of the recursor. -/
theorem Constructor.ResultTypes.results {ls : Fin k' → Level k} {as : InstanceArgs k Γ Δ}
    {Ξ : Scope} {qs : List Quality} {ls' : List (Level k)} {gs : List Grade}
    {as' : InstanceArgs k Γ Ξ} {l : Level k} {χ : Grade} {Cs : Motives k Γ}
    {R : Telescope k (Γ.extend (c.params I).length) (c.nestResultParams I names)} {πs : List Grade}
    (h : Constructor.ResultTypes sig v c I names ls as (Lifting.ofMotives names qs ls' gs as' l χ Cs)
      R πs)
    (hns : ∀ ν ∈ (c.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    c.results I names Cs = some R := by
  obtain ⟨R', hR', he⟩ := Terms.ResultTypes.results names h hns
    (Cs.rename (Ren.weakenN (c.params I).length)) (fun D b hb => by
      rw [Lifting.liftN_block] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨-, C, hC, rfl⟩ := Lifting.ofMotives_block_inv hb₀
      exact Motives.get_rename _ hC)
  have e : (Args.bound (k := k) (Γ := Γ) (c.params I)).terms.rename
      ((Lifting.ofMotives names qs ls' gs as' l χ Cs).liftN (c.params I).length).ren =
      (Args.bound (c.params I)).terms := by
    rw [Lifting.liftN_ren]
    exact Terms.rename_id_of (Ren.liftN_id_of _ fun _ => rfl) _
  rw [e] at hR'
  cases he
  exact hR'

-- ADE: none.
/-- The terms `f(D, t̄)` of the recursive fields of a constructor none of whose fields is nested are
the recursive results of the terms of its fields. -/
theorem Constructor.resultTerms_results (ls : Fin k' → Level k) (as : InstanceArgs k Γ Δ)
    (ρ : Lifting k Γ Γ) (φ : Name → Term k (.var :: Γ)) (ts : Args k Γ (c.params I))
    (hns : ∀ ν ∈ (c.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    ∃ rs, ts.results (fun D t => (φ D).subst₀ (Subst₀.single t)) ((c.fields I).nest names) =
        some rs ∧ Constructor.ResultTerms sig v c I names ls as ρ φ ts rs :=
  Telescope.resultTerms_results names (c.fields I) (c.fieldsAt I ls as) ts hns

end

end Sic.Core
