module

public import Sic.Core.Results
public import Sic.Core.Lifting.Substitution
public import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels
import Sic.Core.Substitution.Rules

/-!
# Substitution of the Recursive Results

The recursive results of fields, their types and their terms, substituted, are those of the fields
substituted: the lifting of the block of a recursor lifts no variable, so that a substitution only
changes the arguments that the types of the fields keep, the instances of the types of the block
and their motives.
They are those of the fields at instantiated levels in the same way, once levels replace their
level variables.
The recursive results of the fields of a constructor follow: the types of its fields, at the
arguments of an instance substituted, are these types substituted under the fields.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Block of a Recursor -/

/-- The lifting of the block of a recursor, substituted, is the lifting of the block at the
arguments and at the motives substituted. -/
theorem Lifting.ofMotives_substitutes {Γ Δ Ξ : Scope} (θ : Subst k Γ Δ) (names : List Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (l : Level k) (Cs : Motives k Δ) :
    Lifting.Substitutes θ θ (Lifting.ofMotives names qs ls ps as l Cs)
      (Lifting.ofMotives names qs ls ps (as.subst θ) l (Cs.subst θ)) where
  ren := fun x => (Term.rename_id_of (Ren.liftN_id_of _ fun _ => rfl) (θ x)).symm
  motive := fun _ => rfl
  motive' := fun _ => rfl
  block := fun D => by
    unfold Lifting.ofMotives
    by_cases hD : D ∈ names
    · simp only [hD, ↓reduceIte]
      cases hC : Cs.get (names.idxOf D) with
      | none =>
        cases hC' : (Cs.subst θ).get (names.idxOf D) with
        | none => rfl
        | some a =>
          obtain ⟨C₀, hC₀, -⟩ := Motives.get_subst_inv θ hC'
          rw [hC] at hC₀
          cases hC₀
      | some a =>
        obtain ⟨n, C⟩ := a
        rw [Motives.get_subst θ hC]
        cases n with
        | zero =>
          show some (Lifting.BlockMotive.mk _ _ _) = some (Lifting.BlockMotive.mk _ _ _)
          rw [Term.subst]
          rfl
        | succ => rfl
    · simp only [hD, ↓reduceIte]
      rfl

/-! ## Types of the Fields -/

/-- A term renamed under new variables, substituted under them by a substitution of the first
order, is the term substituted, renamed under them. -/
theorem Term.subst₀_liftN_rename_weakenN {Γ Δ : Scope} (n : Nat) (σ : Subst₀ k Γ Δ)
    (t : Term k Δ) :
    (t.rename (Ren.weakenN n)).subst₀ (Subst₀.liftN n σ) = (t.subst₀ σ).rename (Ren.weakenN n) :=
  (Term.subst₀_rename_of (fun _ => rfl) t).trans
    (Term.rename_subst₀_of (fun x => (Subst₀.liftN_weakenN n σ x).symm) t).symm

/-- The types of the entries of a telescope substituted are the types of its entries, substituted
under the entries. -/
theorem Telescope.types_subst : {Γ Δ : Scope} → {ps : List Parameter} → (θ : Subst k Γ Δ) →
    (Θ : Telescope k Δ ps) → (Θ.subst θ).types = Θ.types.subst (Subst.liftN ps.length θ)
  | _, _, [], _, .nil => rfl
  | _, _, _ :: ps, θ, .cons _ _ A Θ => by
    show Terms.cons _ (Θ.subst (Subst.lift θ)).types = Terms.cons _ _
    rw [Telescope.types_subst (Subst.lift θ) Θ]
    exact congrArg (Terms.cons · _) (Term.subst_liftN_rename_weakenN (ps.length + 1) θ A).symm

/-- The types of the entries of a telescope substituted by a substitution of the first order are
the types of its entries, substituted under the entries. -/
theorem Telescope.types_subst₀ : {Γ Δ : Scope} → {ps : List Parameter} → (σ : Subst₀ k Γ Δ) →
    (Θ : Telescope k Δ ps) → (Θ.subst₀ σ).types = Θ.types.subst₀ (Subst₀.liftN ps.length σ)
  | _, _, [], _, .nil => rfl
  | _, _, _ :: ps, σ, .cons _ _ A Θ => by
    show Terms.cons _ (Θ.subst₀ (Subst₀.lift σ)).types = Terms.cons _ _
    rw [Telescope.types_subst₀ (Subst₀.lift σ) Θ]
    exact congrArg (Terms.cons · _) (Term.subst₀_liftN_rename_weakenN (ps.length + 1) σ A).symm

/-- The types of the entries of a telescope, at arguments of the telescope, are the types of its
entries at these arguments. -/
theorem Telescope.types_toSubst₀ : {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) →
    (ts : Args k Γ ps) → Θ.types.subst₀ ts.toSubst₀ = Θ.typesAt ts
  | _, [], .nil, .nil => rfl
  | _, p :: ps, .cons _ _ A Θ, .cons t ts => by
    have e₁ := Term.subst₀_rename_of (α := Ren.weakenN (ps.length + 1)) (σ' := Subst₀.id)
      (fun x => Args.toSubst₀_weakenN (Args.cons (p := p) t ts) x) A
    have e₂ : Terms.subst₀ (Δ := Scope.extend (.var :: _) ps.length) (Args.toSubst₀ (Args.cons (p := p) t ts))
        Θ.types = (Θ.subst₀ (Subst₀.single t)).typesAt ts := by
      rw [← Telescope.types_toSubst₀ (Θ.subst₀ (Subst₀.single t)) ts, Telescope.types_subst₀]
      exact (Terms.subst₀_subst₀_of (fun _ => rfl) Θ.types).symm
    exact (congrArg (Terms.cons · _) (e₁.trans (Term.subst₀_id A))).trans (congrArg _ e₂)

/-- The types of the entries of a telescope at arguments, substituted, are the types of the
entries of the telescope substituted, at the arguments substituted. -/
theorem Telescope.typesAt_subst {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → (ts : Args k Δ ps) →
      (Θ.typesAt ts).subst θ = (Θ.subst θ).typesAt (ts.subst θ)
  | [], .nil, .nil => rfl
  | _ :: _, .cons _ _ A Θ, .cons t ts => by
    rw [Telescope.typesAt, Terms.subst, Telescope.typesAt_subst θ (Θ.subst₀ (Subst₀.single t)) ts,
      Telescope.subst_subst₀_of (Subst₀.Swaps.single t θ) Θ]
    rfl

/-! ## Types of the Recursive Results -/

-- ADE: none.
/-- The recursive results of fields, substituted, are those of the fields and of their types
substituted, at the lifting of the block substituted. -/
theorem Terms.ResultTypes.subst :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} →
      Terms.ResultTypes sig v ρ ns ps As xs R →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ},
        Lifting.Substitutes θ θ' ρ ρ' →
          Terms.ResultTypes sig v ρ' ns ps (As.subst θ) (xs.subst θ) (R.subst θ')
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _ => .nil
  | _, _, _, _, _, _, _, _, _, .plain h, _, _, _, _, _, hs => by
    rw [Terms.subst, Terms.subst]
    exact .plain (h.subst hs)
  | _, _, _, _, _, _, _, _, _, .recursive (x := x) (b := b) hD h, _, _, θ, θ', _, hs => by
    rw [Terms.subst, Terms.subst, Telescope.subst,
      Term.subst_subst₀_of (Subst₀.Swaps.single _ θ') b.motive, hs.subst_rename₀ x]
    exact .recursive (b := b.subst θ θ') (by rw [hs.block, hD]; rfl) (h.subst hs.weaken)
  | _, _, _, _, _, _, _, _, _, .nested (x := x) hA h, _, _, _, _, _, hs => by
    have hA' := hA.subst hs
    rw [hs.subst_rename₀ x] at hA'
    rw [Terms.subst, Terms.subst, Telescope.subst]
    exact .nested hA' (h.subst hs.weaken)

/-! ## Terms of the Recursive Results -/

/-- The result of a term of a type of the block, renamed under the arguments of a destructor and
then substituted under them, is this result substituted and then renamed. -/
theorem Term.subst_lift_liftN_rename_lift_weakenN {Γ Δ : Scope} (n : Nat) (θ : Subst k Γ Δ)
    (t : Term k (.var :: Δ)) :
    (t.rename (Ren.lift (Ren.weakenN n))).subst (Subst.lift (Subst.liftN n θ)) =
      (t.subst (Subst.lift θ)).rename (Ren.lift (Ren.weakenN n)) :=
  (Term.subst_rename_of (fun _ => rfl) t).trans
    (Term.rename_subst_of
      (fun x => (Subst.lift_rename_comm_of (θ₁ := Subst.liftN n θ) (α₁ := Ren.weakenN n)
        (θ₂ := θ) (α₂ := Ren.weakenN n) (fun x => Subst.liftN_weakenN n θ x) x).symm) t).symm

-- ADE: none.
/-- The recursive result of a term, substituted, is that of the term substituted, at its type
substituted, at the lifting of the block substituted, where the result of a term of a type of the
block is substituted under this term. -/
theorem Term.NestedResult.subst :
    {Δ : Scope} → {ρ : Lifting k Δ Δ} → {φ : Name → Term k (.var :: Δ)} → {n : Nest Name} →
      {A t e : Term k Δ} → Term.NestedResult sig v ρ φ n A t e →
      ∀ {Γ : Scope} {θ : Subst k Γ Δ} {ρ' : Lifting k Γ Γ}, Lifting.Substitutes θ θ ρ ρ' →
        Term.NestedResult sig v ρ' (fun E => (φ E).subst (Subst.lift θ)) n (A.subst θ)
          (t.subst θ) (e.subst θ)
  | _, _, φ, _, _, _, _, .block (D := D) (b := b) hD hT, _, θ, _, hs => by
    rw [Term.subst, Term.subst_subst₀_of (Subst₀.Swaps.single _ θ) (φ D)]
    refine Term.NestedResult.block (b := b.subst θ θ) ?_ ?_
    · rw [hs.block, hD]
      rfl
    · show b.type.subst θ = _
      rw [hT, Term.subst]
  | _, _, φ, _, _, _, _,
      .inst (t := t) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (gs := gs) h hn hq hl hp
        has hS hL hgl hgs hgt,
      _, θ, _, hs => by
    rw [Term.subst, Term.subst]
    simp only [InstanceArgs.subst, States.subst, Telescope.subst]
    refine Term.NestedResult.inst h hn hq hl hp (has.subst hs) hS hL
      ((CorecBranches.length_subst θ gs).trans hgl) ?_ ?_
    · intro i d hi
      obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, g, hg⟩ := hgs i d hi
      exact ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, _, CorecBranches.get_subst θ hg⟩
    · intro i d p q ς ps₁ Ξ Θ B ψ g' hi hd hg'
      obtain ⟨g, hg, rfl⟩ := CorecBranches.get_subst_inv θ hg'
      have ih := (hgt i d p q ς ps₁ Ξ Θ B ψ g hi hd hg).subst (hs.liftN ps₁.length)
      rw [Term.observation_subst,
        Term.subst_subst_of (Subst.liftN_subst_of ps₁.length
          (hd.obsSubst_observation_subst θ D qs ls ps as t)),
        funext fun E => Term.subst_lift_liftN_rename_lift_weakenN ps₁.length θ (φ E)] at ih
      exact ih

-- ADE: none.
/-- The recursive results of the terms of fields, substituted, are those of the terms and of their
types substituted, at the lifting of the block substituted. -/
theorem Terms.ResultTerms.subst {Δ : Scope} {ρ : Lifting k Δ Δ}
    {φ : Name → Term k (.var :: Δ)} {Γ : Scope} {θ : Subst k Γ Δ} {ρ' : Lifting k Γ Γ}
    (hs : Lifting.Substitutes θ θ ρ ρ') :
    {ns : List (Nest Name)} → {ps : List Parameter} → {As ts : Terms k Δ} →
      {ps' : List Parameter} → {rs : Args k Δ ps'} → Terms.ResultTerms sig v ρ φ ns ps As ts rs →
        Terms.ResultTerms sig v ρ' (fun E => (φ E).subst (Subst.lift θ)) ns ps (As.subst θ)
          (ts.subst θ) (rs.subst θ)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .plain h => by
    rw [Terms.subst, Terms.subst]
    exact .plain (h.subst hs)
  | _, _, _, _, _, _, .recursive (D := D) h => by
    rw [Terms.subst, Terms.subst, Args.subst,
      Term.subst_subst₀_of (Subst₀.Swaps.single _ θ) (φ D)]
    exact .recursive (h.subst hs)
  | _, _, _, _, _, _, .nested he h => by
    rw [Terms.subst, Terms.subst, Args.subst]
    exact .nested (he.subst hs) (h.subst hs)

/-! ## Recursive Results of a Constructor -/

section

variable {j g k' : Nat} {Ξ Δ Γ : Scope} {c : Constructor j g k' Ξ} {I : Instance j g}
  {names : List Name} {ls : Fin k' → Level k} {as : InstanceArgs k Δ Ξ} {ρ : Lifting k Δ Δ}
  {ps' : List Parameter} {θ : Subst k Γ Δ} {ρ' : Lifting k Γ Γ}

-- ADE: none.
/-- The recursive results of the fields of a constructor, substituted under the fields, are those
of its fields at the arguments substituted, at the lifting of the block substituted. -/
theorem Constructor.ResultTypes.subst {R : Telescope k (Δ.extend (c.params I).length) ps'}
    (h : Constructor.ResultTypes sig v c I names ls as ρ R) (hs : Lifting.Substitutes θ θ ρ ρ') :
    Constructor.ResultTypes sig v c I names ls (as.subst θ) ρ'
      (R.subst (Subst.liftN (c.params I).length θ)) := by
  have h' := Terms.ResultTypes.subst h (hs.liftN (c.params I).length)
  rw [← Telescope.types_subst, Constructor.fieldsAt_subst, ← Args.terms_subst,
    Args.bound_subst] at h'
  exact h'

-- ADE: none.
/-- The recursive results of the terms of the fields of a constructor, substituted, are those of
the terms substituted, at the arguments substituted, at the lifting of the block substituted. -/
theorem Constructor.ResultTerms.subst {φ : Name → Term k (.var :: Δ)}
    {ts : Args k Δ (c.params I)} {rs : Args k Δ ps'}
    (h : Constructor.ResultTerms sig v c I names ls as ρ φ ts rs)
    (hs : Lifting.Substitutes θ θ ρ ρ') :
    Constructor.ResultTerms sig v c I names ls (as.subst θ) ρ'
      (fun E => (φ E).subst (Subst.lift θ)) (ts.subst θ) (rs.subst θ) := by
  have h' := Terms.ResultTerms.subst hs h
  rw [Telescope.typesAt_subst, Constructor.fieldsAt_subst, ← Args.terms_subst] at h'
  exact h'

end

/-! ## Instantiated Levels -/

/-- The lifting of the block of a recursor, at instantiated levels, is the lifting of the block at
the levels, at the arguments and at the motives instantiated. -/
theorem Lifting.ofMotives_substLevels {k' : Nat} {Γ Δ : Scope} (ls' : Fin k → Level k')
    (names : List Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
    (as : InstanceArgs k Γ Δ) (l : Level k) (Cs : Motives k Γ) :
    (Lifting.ofMotives names qs ls ps as l Cs).substLevels ls' =
      Lifting.ofMotives names qs (ls.map (Level.subst ls')) ps (as.substLevels ls')
        (l.subst ls') (Cs.substLevels ls') :=
  Lifting.ext_of (fun _ => rfl) (fun _ => rfl) fun D => by
    show Option.map _ ((Lifting.ofMotives names qs ls ps as l Cs).block D) = _
    unfold Lifting.ofMotives
    by_cases hD : D ∈ names
    · simp only [hD, ↓reduceIte]
      cases hC : Cs.get (names.idxOf D) with
      | none =>
        cases hC' : (Cs.substLevels ls').get (names.idxOf D) with
        | none => rfl
        | some a =>
          obtain ⟨C₀, hC₀, -⟩ := Motives.get_substLevels ls' hC'
          rw [hC] at hC₀
          cases hC₀
      | some a =>
        obtain ⟨n, C⟩ := a
        rw [Motives.get_substLevels_of ls' hC]
        cases n with
        | zero =>
          show some (Lifting.BlockMotive.mk _ _ _) = some (Lifting.BlockMotive.mk _ _ _)
          rw [Term.substLevels]
          rfl
        | succ => rfl
    · simp only [hD, ↓reduceIte]
      rfl

/-- The types of the entries of a telescope at instantiated levels are the types of its entries at
these levels. -/
theorem Telescope.types_substLevels {k' : Nat} (ls' : Fin k → Level k') :
    {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      (Θ.substLevels ls').types = Θ.types.substLevels ls'
  | _, [], .nil => rfl
  | _, _ :: _, .cons _ _ A Θ => by
    show Terms.cons _ (Θ.substLevels ls').types = Terms.cons _ _
    rw [Telescope.types_substLevels ls' Θ, Term.substLevels_rename]
    rfl

/-- The types of the entries of a telescope at arguments, at instantiated levels, are the types of
the entries of the telescope at these levels, at the arguments at these levels. -/
theorem Telescope.typesAt_substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope} :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (ts : Args k Γ ps) →
      (Θ.typesAt ts).substLevels ls' = (Θ.substLevels ls').typesAt (ts.substLevels ls')
  | [], .nil, .nil => rfl
  | _ :: _, .cons _ _ A Θ, .cons t ts => by
    rw [Telescope.typesAt, Terms.substLevels,
      Telescope.typesAt_substLevels ls' (Θ.subst₀ (Subst₀.single t)) ts,
      Telescope.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun y => by cases y <;> rfl) Θ]
    rfl

-- ADE: none.
/-- The recursive results of fields, at instantiated levels, are those of the fields and of their
types at these levels, at the lifting of the block at these levels. -/
theorem Terms.ResultTypes.substLevels {k' : Nat} (ls' : Fin k → Level k') :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} →
      Terms.ResultTypes sig v ρ ns ps As xs R →
        Terms.ResultTypes sig v (ρ.substLevels ls') ns ps (As.substLevels ls')
          (xs.substLevels ls') (R.substLevels ls')
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, _, .plain h => by
    rw [Terms.substLevels, Terms.substLevels]
    exact .plain (h.substLevels ls')
  | _, _, ρ, _, _, _, _, _, _, .recursive (D := D) (x := x) (b := b) hD h => by
    have ih := h.substLevels ls'
    rw [Lifting.substLevels_weaken] at ih
    rw [Terms.substLevels, Terms.substLevels, Telescope.substLevels,
      Term.substLevels_subst₀_of (σ' := Subst₀.single ((x.rename ρ.ren).substLevels ls'))
        (fun y => by cases y <;> rfl) b.motive,
      Term.substLevels_rename]
    refine .recursive (b := b.substLevels ls') ?_ ih
    show (ρ.block D).map _ = _
    rw [hD]
    rfl
  | _, _, _, _, _, _, _, _, _, .nested hA h => by
    have hA' := hA.substLevels ls'
    rw [Term.substLevels_rename] at hA'
    have ih := h.substLevels ls'
    rw [Lifting.substLevels_weaken] at ih
    rw [Terms.substLevels, Terms.substLevels, Telescope.substLevels]
    exact .nested hA' ih

-- ADE: none.
/-- The recursive result of a term, at instantiated levels, is that of the term at these levels, at
its type at these levels, at the lifting of the block at these levels, where the result of a term
of a type of the block is at these levels. -/
theorem Term.NestedResult.substLevels {k' : Nat} (ls' : Fin k → Level k') :
    {Γ : Scope} → {ρ : Lifting k Γ Γ} → {φ : Name → Term k (.var :: Γ)} → {n : Nest Name} →
      {A t e : Term k Γ} → Term.NestedResult sig v ρ φ n A t e →
        Term.NestedResult sig v (ρ.substLevels ls') (fun E => (φ E).substLevels ls') n
          (A.substLevels ls') (t.substLevels ls') (e.substLevels ls')
  | _, ρ, φ, _, _, t, _, .block (D := D) (b := b) hD hT => by
    rw [Term.substLevels, Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
      (fun y => by cases y <;> rfl) (φ D)]
    refine Term.NestedResult.block (b := b.substLevels ls') ?_ ?_
    · show (ρ.block D).map _ = _
      rw [hD]
      rfl
    · show b.type.substLevels ls' = _
      rw [hT, Term.substLevels]
  | _, _, φ, _, _, _, _,
      .inst (t := t) (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) (gs := gs) h hn hq hl hp
        has hS hL hgl hgs hgt => by
    simp only [Term.substLevels, InstanceArgs.substLevels, States.substLevels,
      Telescope.substLevels, List.map_append, List.map_nil]
    refine Term.NestedResult.inst h hn hq ((List.length_map _).trans hl) hp (has.substLevels ls')
      hS hL ((CorecBranches.length_substLevels ls' gs).trans hgl) ?_ ?_
    · intro i d hi
      obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, g, hg⟩ := hgs i d hi
      exact ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, _, CorecBranches.get_substLevels_of ls' hg⟩
    · intro i d p q ς ps₁ Ξ Θ B ψ g' hi hd hg'
      obtain ⟨g, hg, rfl⟩ := CorecBranches.get_substLevels ls' hg'
      have ho {a : Scope.Entry} (x : Var Ξ a) :=
        hd.obsSubst_substLevels ls' (Term.observation_substLevels ls' D qs ls ps as t)
          (fun x => InstanceArgs.toSubst_substLevels ls' as x) x
      have ih := (hgt i d p q ς ps₁ Ξ Θ B ψ g hi hd hg).substLevels ls'
      rw [Lifting.substLevels_liftN, Term.observation_substLevels,
        Term.substLevels_subst_of (Subst.liftN_substLevels_of _ ho),
        Term.substLevels_substLevels_getFin] at ih
      simp only [Term.substLevels_rename] at ih
      exact ih

-- ADE: none.
/-- The recursive results of the terms of fields, at instantiated levels, are those of the terms
and of their types at these levels, at the lifting of the block at these levels. -/
theorem Terms.ResultTerms.substLevels {k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} :
    {ns : List (Nest Name)} → {ps : List Parameter} → {As ts : Terms k Γ} →
      {ps' : List Parameter} → {rs : Args k Γ ps'} → Terms.ResultTerms sig v ρ φ ns ps As ts rs →
        Terms.ResultTerms sig v (ρ.substLevels ls') (fun E => (φ E).substLevels ls') ns ps
          (As.substLevels ls') (ts.substLevels ls') (rs.substLevels ls')
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .plain h => by
    rw [Terms.substLevels, Terms.substLevels]
    exact .plain (h.substLevels ls')
  | _, _, _, .cons t _, _, _, .recursive (D := D) h => by
    rw [Terms.substLevels, Terms.substLevels, Args.substLevels,
      Term.substLevels_subst₀_of (σ' := Subst₀.single (t.substLevels ls'))
        (fun y => by cases y <;> rfl) (φ D)]
    exact .recursive (h.substLevels ls')
  | _, _, _, _, _, _, .nested he h => by
    rw [Terms.substLevels, Terms.substLevels, Args.substLevels]
    exact .nested (he.substLevels ls') (h.substLevels ls')

section

variable {j g k' k'' : Nat} {Δ Γ : Scope} {c : Constructor j g k' Δ} {I : Instance j g}
  {names : List Name} {ls : Fin k' → Level k} {as : InstanceArgs k Γ Δ} {ρ : Lifting k Γ Γ}
  {ps' : List Parameter}

-- ADE: none.
/-- The recursive results of the fields of a constructor, at instantiated levels, are those of its
fields at the levels and at the arguments at these levels, at the lifting of the block at these
levels. -/
theorem Constructor.ResultTypes.substLevels (ls' : Fin k → Level k'')
    {R : Telescope k (Γ.extend (c.params I).length) ps'}
    (h : Constructor.ResultTypes sig v c I names ls as ρ R) :
    Constructor.ResultTypes sig v c I names (fun i => (ls i).subst ls') (as.substLevels ls')
      (ρ.substLevels ls') (R.substLevels ls') := by
  have h' := Terms.ResultTypes.substLevels ls' h
  rw [Lifting.substLevels_liftN, ← Telescope.types_substLevels, Constructor.fieldsAt_substLevels,
    ← Args.terms_substLevels, Args.bound_substLevels] at h'
  exact h'

-- ADE: none.
/-- The recursive results of the terms of the fields of a constructor, at instantiated levels, are
those of the terms at these levels, at the levels and at the arguments at these levels, at the
lifting of the block at these levels. -/
theorem Constructor.ResultTerms.substLevels (ls' : Fin k → Level k'')
    {φ : Name → Term k (.var :: Γ)} {ts : Args k Γ (c.params I)} {rs : Args k Γ ps'}
    (h : Constructor.ResultTerms sig v c I names ls as ρ φ ts rs) :
    Constructor.ResultTerms sig v c I names (fun i => (ls i).subst ls') (as.substLevels ls')
      (ρ.substLevels ls') (fun E => (φ E).substLevels ls') (ts.substLevels ls')
      (rs.substLevels ls') := by
  have h' := Terms.ResultTerms.substLevels ls' h
  rw [Telescope.typesAt_substLevels, Constructor.fieldsAt_substLevels,
    ← Args.terms_substLevels] at h'
  exact h'

end

end Sic.Core
