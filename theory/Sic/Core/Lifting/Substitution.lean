module

public import Sic.Core.Lifting
import Sic.Core.Positivity.Substitution
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels

/-!
# Substitution of the Liftings

The parts of the declaration of a lifting of annex 20 of RFC 36 under the renamings, the
substitutions and the instantiation of the level variables: a telescope followed by an entry, as
the telescope of a motive is, and the parameters, the type of the parameter `y` and the sort of the
lifting at an instance of its variables, where the levels of the motives are those of the arguments
lifted.

The renaming of the parameters in the parameters lifted does not read the levels of the motives.

The lifting of a type is stable under the instantiation of the level variables, and, when the
lifting of the scope lifts no variable, as the one of the block of a recursor, under a
substitution: the lifting substituted gives the types of the block their motives substituted, and
its renaming commutes with the substitutions of both scopes.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Telescopes Followed by an Entry -/

/-- A telescope followed by an entry, renamed, is the telescope renamed followed by the entry
renamed. -/
theorem Telescope.rename_snoc {Γ Δ : Scope} {p : Parameter} (q : Grade) (α : Ren Γ Δ) :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → (A : Term k (Δ.extend ps.length)) →
      (Θ.snoc (p := p) q A).rename α = (Θ.rename α).snoc q (A.rename (Ren.liftN ps.length α))
  | [], .nil, _ => rfl
  | _ :: _, .cons q' p' A' Θ, A =>
    congrArg (Telescope.cons q' p' (A'.rename α)) (Telescope.rename_snoc q (Ren.lift α) Θ A)

/-- A telescope followed by an entry, substituted, is the telescope substituted followed by the
entry substituted. -/
theorem Telescope.subst₀_snoc {Γ Δ : Scope} {p : Parameter} (q : Grade) (σ : Subst₀ k Γ Δ) :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → (A : Term k (Δ.extend ps.length)) →
      (Θ.snoc (p := p) q A).subst₀ σ =
        (Θ.subst₀ σ).snoc q (A.subst₀ (Subst₀.liftN ps.length σ))
  | [], .nil, _ => rfl
  | _ :: _, .cons q' p' A' Θ, A =>
    congrArg (Telescope.cons q' p' (A'.subst₀ σ)) (Telescope.subst₀_snoc q (Subst₀.lift σ) Θ A)

/-- A telescope followed by an entry, substituted at the second order, is the telescope substituted
followed by the entry substituted. -/
theorem Telescope.subst_snoc {Γ Δ : Scope} {p : Parameter} (q : Grade) (θ : Subst k Γ Δ) :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → (A : Term k (Δ.extend ps.length)) →
      (Θ.snoc (p := p) q A).subst θ = (Θ.subst θ).snoc q (A.subst (Subst.liftN ps.length θ))
  | [], .nil, _ => rfl
  | _ :: _, .cons q' p' A' Θ, A =>
    congrArg (Telescope.cons q' p' (A'.subst θ)) (Telescope.subst_snoc q (Subst.lift θ) Θ A)

/-- A telescope followed by an entry, at instantiated levels, is the telescope followed by the
entry, both at these levels. -/
theorem Telescope.substLevels_snoc {k' : Nat} {Γ : Scope} {p : Parameter} (q : Grade)
    (ls' : Fin k → Level k') :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (A : Term k (Γ.extend ps.length)) →
      (Θ.snoc (p := p) q A).substLevels ls' = (Θ.substLevels ls').snoc q (A.substLevels ls')
  | [], .nil, _ => rfl
  | _ :: _, .cons q' p' A' Θ, A =>
    congrArg (Telescope.cons q' p' (A'.substLevels ls')) (Telescope.substLevels_snoc q ls' Θ A)

/-! ## Renaming of the Parameters -/

/-- The renaming of a lifting under `n` new variables is its renaming under these variables. -/
theorem Lifting.liftN_ren {Γ' Γ : Scope} (n : Nat) (ρ : Lifting k Γ' Γ) :
    @Lifting.ren k _ _ (ρ.liftN n) = fun {_} x => Ren.liftN n ρ.ren x := by
  funext a x
  exact go n ρ x
where
  /-- The equality at a variable, by recursion on the number of the variables. -/
  go {Γ' Γ : Scope} : (n : Nat) → (ρ : Lifting k Γ' Γ) →
      ∀ {a} (x : Var (Γ.extend n) a), (ρ.liftN n).ren x = Ren.liftN n ρ.ren x
    | 0, _, _, _ => rfl
    | n + 1, ρ, _, x => go n ρ.lift x

/-- Motives of a type of a block are equal when their instances and their motives are. -/
theorem Lifting.BlockMotive.mk_congr {Γ' Γ : Scope} {T T' : Term k Γ} {C C' : Term k (.var :: Γ')}
    (l : Level k) (hT : T = T') (hC : C = C') :
    Lifting.BlockMotive.mk (Γ' := Γ') T C l = Lifting.BlockMotive.mk T' C' l := by
  rw [hT, hC]

/-- The motive of a type of a block, in a lifting under `n` new variables, is its motive in the
lifting, renamed under these variables. -/
theorem Lifting.liftN_block : (n : Nat) → {Γ' Γ : Scope} → (ρ : Lifting k Γ' Γ) → (D : Name) →
    (ρ.liftN n).block D = (ρ.block D).map fun b =>
      ⟨b.type.rename (Ren.weakenN n), b.motive.rename (Ren.lift (Ren.weakenN n)), b.level⟩
  | 0, _, _, ρ, D => by
    show ρ.block D = _
    cases ρ.block D with
    | none => rfl
    | some b =>
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level
        (Term.rename_id_of (fun _ => rfl) b.type).symm
        (Term.rename_id_of (Ren.lift_id_of fun _ => rfl) b.motive).symm)
  | n + 1, _, _, ρ, D => by
    show (ρ.lift.liftN n).block D = _
    rw [Lifting.liftN_block n ρ.lift D]
    show ((ρ.block D).map Lifting.BlockMotive.lift).map _ = _
    cases ρ.block D with
    | none => rfl
    | some b =>
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level
        (Term.rename_rename_of (α₁ := Ren.weakenN n) (α₂ := Ren.weaken)
          (α₃ := Ren.weakenN (n + 1)) (fun _ => rfl) b.type)
        (Term.rename_rename_of (α₁ := Ren.lift (Ren.weakenN n)) (α₂ := Ren.lift Ren.weaken)
          (α₃ := Ren.lift (Ren.weakenN (n + 1))) (fun x => by cases x <;> rfl) b.motive))

/-- The renamings of two liftings extended by a parameter are the same when those of the liftings
are, whatever the levels of the motives. -/
theorem Lifting.cons_ren_congr {k' : Nat} {Δ' Δ : Scope} {e : Scope.Entry} (l : Level k)
    (l' : Level k') {ρ : Lifting k Δ' Δ} {ρ' : Lifting k' Δ' Δ}
    (h : ∀ {a} (x : Var Δ a), ρ.ren x = ρ'.ren x) :
    (b : Bool) → ∀ {a} (x : Var (e :: Δ) a),
      (Lifting.cons l b ρ).ren x = (Lifting.cons l' b ρ').ren x
  | true, _, .zero => rfl
  | true, _, .succ x => congrArg (fun y => Var.succ (Var.succ y)) (h x)
  | false, _, .zero => rfl
  | false, _, .succ x => congrArg Var.succ (h x)

/-- The renaming of the parameters in the parameters lifted does not read the levels of the
motives. -/
theorem Lifting.base_ren {k' : Nat} (S : List Nat) (lv : Nat → Level k) (lv' : Nat → Level k')
    (Δ : Scope) :
    @Lifting.ren k _ _ (Lifting.base S lv Δ) = @Lifting.ren k' _ _ (Lifting.base S lv' Δ) := by
  funext a x
  exact go Δ x
where
  /-- The equality at a variable, by recursion on the parameters. -/
  go : (Δ : Scope) → ∀ {a} (x : Var Δ a),
      (Lifting.base S lv Δ).ren x = (Lifting.base S lv' Δ).ren x
    | [], _, x => nomatch x
    | _ :: Δ, _, x => Lifting.cons_ren_congr _ _ (go Δ) _ x

/-! ## Instances of the Variables -/

/-- The levels of a join, instantiated, are joined. -/
theorem Level.subst_joins {k' : Nat} (ls' : Fin k → Level k') :
    (ls : List (Level k)) → (l : Level k) →
      (l.joins ls).subst ls' = (l.subst ls').joins (ls.map (Level.subst ls'))
  | [], _ => rfl
  | l' :: ls, l => Level.subst_joins ls' ls (.max l l')

/-- The level of the motive of the parameter at a position of `S`, at the levels of an instance of
the lifting, is the level after those of the type declaration at this position in `S`. -/
theorem Lifting.motiveLevel_subst {k' : Nat} {S : List Nat} (hS : S.Nodup)
    {ls ls' : List (Level k')} (hl : ls.length = k) (hl' : ls'.length = S.length)
    (h : (ls ++ ls').length = k + S.length) (j : Nat) (hj : j < S.length) (hj' : j < ls'.length) :
    (Lifting.motiveLevel k S S[j]).subst ((ls ++ ls').getFin h) = ls'[j] := by
  have hi : S.idxOf S[j] = j := hS.idxOf_getElem j hj
  unfold Lifting.motiveLevel
  split
  · show (ls ++ ls').getFin h (Fin.natAdd k ⟨S.idxOf S[j], _⟩) = ls'[j]
    rw [List.getFin_append_natAdd ls ls' hl hl' h]
    simp [List.getFin, hi]
  · next hn => exact absurd (hi.symm ▸ hj) hn

/-- The instance of the variables of a type declaration that an instance of the variables of its
lifting holds, given by lists, is given by the lists without the variables that the lifting
adds. -/
theorem Instance.lifted_ofLists {j g : Nat} (qs : List Quality) (ps : List Grade) (s : Quality)
    (r ς χ : Grade) (hq : qs.length = j) (hp : ps.length = g) (hq' : (qs ++ [s]).length = j + 1)
    (hp' : (ps ++ [r, ς, χ]).length = g + 3) :
    (Instance.ofLists (qs ++ [s]) (ps ++ [r, ς, χ]) hq' hp').lifted =
      Instance.ofLists qs ps hq hp := by
  unfold Instance.lifted Instance.ofLists
  congr 1
  · funext i
    exact List.getFin_append_castAdd qs [s] hq hq' i
  · funext i
    exact List.getFin_append_castAdd ps [r, ς, χ] hp hp' i

/-- The quality of the sorts of the motives, at an instance of the variables of a lifting given by
lists, is the last quality. -/
theorem Instance.sorts_last_ofLists {j g : Nat} (qs : List Quality) (ps : List Grade)
    (s : Quality) (hq : qs.length = j) (hq' : (qs ++ [s]).length = j + 1) (hp : ps.length = g) :
    (Instance.ofLists (qs ++ [s]) ps hq' hp).sorts (Fin.last j) = s :=
  List.getFin_append_natAdd qs [s] hq rfl hq' 0

/-- The variables that a lifting adds, at an instance of its variables given by lists, are the last
quality and the last three grades. -/
theorem Instance.liftingVariables_ofLists {j g : Nat} (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (hq : qs.length = j) (hp : ps.length = g)
    (hq' : (qs ++ [v.quality]).length = j + 1)
    (hp' : (ps ++ [v.recursion, v.requirement, v.ownership]).length = g + 3) :
    (Instance.ofLists (qs ++ [v.quality]) (ps ++ [v.recursion, v.requirement, v.ownership]) hq'
      hp').liftingVariables = v := by
  obtain ⟨s, r, ς, χ⟩ := v
  exact congr (congr (congr (congrArg Lifting.Variables.mk
      (Instance.sorts_last_ofLists qs _ s hq hq' hp'))
    (List.getFin_append_natAdd ps [r, ς, χ] hp rfl hp' 0))
    (List.getFin_append_natAdd ps [r, ς, χ] hp rfl hp' 1))
    (List.getFin_append_natAdd ps [r, ς, χ] hp rfl hp' 2)

/-- The level variables of a type declaration, among those of its lifting, at the levels of an
instance of the lifting, are the levels of the instance of the type declaration. -/
theorem Level.lifted_subst {k' n : Nat} (ls ls' : List (Level k')) (hl : ls.length = k)
    (h : (ls ++ ls').length = k + n) :
    (fun i => (Level.lifted n i).subst ((ls ++ ls').getFin h)) = ls.getFin hl :=
  funext fun i => List.getFin_append_castAdd ls ls' hl h i

/-- The sort of a lifting, at an instance of its variables, has the quality of the sorts of the
motives, and the level of the type declaration at its instance joined to the levels of the
motives. -/
theorem TypeDeclaration.liftingSort_substLevels (decl : TypeDeclaration) (S : List Nat)
    {qs : List Quality} {ps : List Grade} {s : Quality} {r ς χ : Grade} {ls ls' : List (Level k)}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades) (hl : ls.length = decl.levels)
    (hl' : ls'.length = S.length) (hq' : (qs ++ [s]).length = decl.sorts + 1)
    (hp' : (ps ++ [r, ς, χ]).length = decl.grades + 3)
    (h : (ls ++ ls').length = decl.levels + S.length) :
    (decl.liftingSort S (.ofLists (qs ++ [s]) (ps ++ [r, ς, χ]) hq' hp')).substLevels
        ((ls ++ ls').getFin h) =
      ⟨s, ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).joins ls'⟩ := by
  have e : (List.ofFn fun i : Fin S.length => Level.var (Fin.natAdd decl.levels i)).map
      (Level.subst ((ls ++ ls').getFin h)) = ls' := by
    rw [List.map_ofFn]
    exact (congrArg List.ofFn (funext fun i => List.getFin_append_natAdd ls ls' hl hl' h i)).trans
      (List.ofFn_getFin ls' hl')
  unfold TypeDeclaration.liftingSort Universe.substLevels
  rw [Instance.lifted_ofLists qs ps s r ς χ hq hp, Instance.sorts_last_ofLists qs _ s hq,
    Level.subst_joins, Level.subst_subst, Level.lifted_subst ls ls' hl h, e]

/-- The type of the parameter `y` of a lifting, at an instance of its variables, is the instance of
the type lifted at the instance of the type declaration. -/
theorem TypeDeclaration.liftedInstance_substLevels {Γ : Scope} (decl : TypeDeclaration) (F : Name)
    {n : Nat} {qs : List Quality} {ps : List Grade} {ls ls' : List (Level k)}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades) (hl : ls.length = decl.levels)
    (h : (ls ++ ls').length = decl.levels + n)
    (as : InstanceArgs (decl.levels + n) Γ decl.scope) :
    (decl.liftedInstance F n (.ofLists qs ps hq hp) as).substLevels ((ls ++ ls').getFin h) =
      .inst F qs ls ps (as.substLevels ((ls ++ ls').getFin h)) := by
  unfold TypeDeclaration.liftedInstance Instance.ofLists
  rw [Term.substLevels, List.ofFn_getFin, List.ofFn_getFin, List.map_ofFn]
  exact congrArg (fun ls₀ => Term.inst F qs ls₀ ps _)
    ((congrArg List.ofFn (Level.lifted_subst ls ls' hl h)).trans (List.ofFn_getFin ls hl))

/-! ## Parameters of a Lifting -/

/-- A context extended by a variable, followed by its motive if it is lifted, at instantiated
levels. -/
theorem Context.liftedVar_substLevels {k' : Nat} {Δ' : Scope} (ls' : Fin k → Level k')
    (κ : Universe k) (ctx : Context k Δ') (A : Term k Δ') :
    (b : Bool) → (Context.liftedVar κ b ctx A).substLevels ls' =
      Context.liftedVar (κ.substLevels ls') b (ctx.substLevels ls') (A.substLevels ls')
  | true => rfl
  | false => rfl

/-- A context extended by a second-order variable, followed by its motive if it is lifted, at
instantiated levels. -/
theorem Context.liftedSecondOrder_substLevels {k' : Nat} {Δ' : Scope} {ps : List Parameter}
    (ls' : Fin k → Level k') (κ : Universe k) (ctx : Context k Δ') (Θ : Telescope k Δ' ps)
    (A : Term k (Δ'.extend ps.length)) (ψ : ResultOwnership Grade ps.length) :
    (b : Bool) → (Context.liftedSecondOrder κ b ctx Θ A ψ).substLevels ls' =
      Context.liftedSecondOrder (κ.substLevels ls') b (ctx.substLevels ls') (Θ.substLevels ls')
        (A.substLevels ls') ψ
  | true => by
    show Context.secondOrder _ (Telescope.substLevels ls' (Telescope.snoc _ _ _)) _ _ = _
    rw [Telescope.substLevels_snoc, Telescope.substLevels_rename, Var.eta_substLevels]
    rfl
  | false => rfl

/-- The parameters of a lifting, at instantiated levels, are the parameters at these levels, lifted
with motives at the levels instantiated. -/
theorem Context.lifted_substLevels {k' : Nat} (S : List Nat) (s : Quality) (lv : Nat → Level k)
    (ls' : Fin k → Level k') : {Δ : Scope} → (ctx : Context k Δ) →
      (ctx.lifted S s lv).substLevels ls' =
        (ctx.substLevels ls').lifted S s fun i => (lv i).subst ls'
  | _, .empty => rfl
  | _, .var (Γ := Δ) ctx A => by
    show (Context.liftedVar _ _ _ _).substLevels ls' = Context.liftedVar _ _ _ _
    rw [Context.liftedVar_substLevels, Context.lifted_substLevels S s lv ls' ctx,
      Term.substLevels_rename, Lifting.base_ren S lv (fun i => (lv i).subst ls') Δ]
    rfl
  | _, .secondOrder (Γ := Δ) ctx Θ A ψ => by
    show (Context.liftedSecondOrder _ _ _ _ _ _).substLevels ls' =
      Context.liftedSecondOrder _ _ _ _ _ _
    rw [Context.liftedSecondOrder_substLevels, Context.lifted_substLevels S s lv ls' ctx,
      Term.substLevels_rename, Telescope.substLevels_rename,
      Lifting.base_ren S lv (fun i => (lv i).subst ls') Δ]
    rfl

/-! ## Liftings Substituted -/

/-- The motive of a type of a block, substituted: its instance by `θ`, and its motive by `θ'`,
under the term that it is over. -/
def Lifting.BlockMotive.subst {Γ' Γ Δ' Δ : Scope} (θ : Subst k Γ Δ) (θ' : Subst k Γ' Δ')
    (b : Lifting.BlockMotive k Δ' Δ) : Lifting.BlockMotive k Γ' Γ :=
  ⟨b.type.subst θ, b.motive.subst (Subst.lift θ'), b.level⟩

/-- The lifting `ρ'` is the lifting `ρ`, which lifts no variable, substituted by `θ` in the scope
that it lifts and by `θ'` in the scope in which it lifts it: `ρ'` lifts no variable either, what
`θ'` gives the variable that a variable is, is what `θ` gives this variable, renamed, and the types
of the block have their motives substituted. -/
structure Lifting.Substitutes {Γ' Γ Δ' Δ : Scope} (θ : Subst k Γ Δ) (θ' : Subst k Γ' Δ')
    (ρ : Lifting k Δ' Δ) (ρ' : Lifting k Γ' Γ) : Prop where
  /-- The substitutions commute with the renamings of the liftings. -/
  ren : ∀ {a} (x : Var Δ a), θ' (ρ.ren x) = (θ x).rename (Ren.liftN a.params.length ρ'.ren)
  /-- The lifting lifts no variable. -/
  motive : ∀ {a} (x : Var Δ a), ρ.motive x = none
  /-- The lifting substituted lifts no variable. -/
  motive' : ∀ {a} (x : Var Γ a), ρ'.motive x = none
  /-- The types of the block have their motives substituted. -/
  block : ∀ D, ρ'.block D = (ρ.block D).map (Lifting.BlockMotive.subst θ θ')

/-- A motive over a term, substituted under it and then renamed in a scope extended by an entry
below it, is the motive renamed and then substituted under this entry. -/
theorem Term.subst_lift_rename_lift_weaken {Γ Δ : Scope} {e e' : Scope.Entry} (θ : Subst k Γ Δ)
    (t : Term k (e' :: Δ)) :
    (t.subst (Subst.lift θ)).rename (Ren.lift (Ren.weaken (e := e))) =
      (t.rename (Ren.lift Ren.weaken)).subst (Subst.lift (Subst.lift θ)) :=
  (Term.rename_subst_of (fun _ => rfl) t).trans
    ((Term.subst_rename_of
      (fun x => Subst.lift_rename_comm_of (θ₁ := Subst.lift θ) (α₁ := Ren.weaken) (θ₂ := θ)
        (α₂ := Ren.weaken) (fun _ => rfl) x) t).symm)

/-- A lifting substituted, under a new entry of both scopes. -/
theorem Lifting.Substitutes.lift {Γ' Γ Δ' Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ}
    (h : Lifting.Substitutes θ θ' ρ ρ') :
    Lifting.Substitutes (Subst.lift (e := e) θ) (Subst.lift θ') ρ.lift ρ'.lift where
  ren := Subst.lift_rename_comm_of h.ren
  motive := fun x =>
    match x with
    | .zero => rfl
    | .succ x => by
      show (ρ.motive x).map _ = none
      rw [h.motive x]
      rfl
  motive' := fun x =>
    match x with
    | .zero => rfl
    | .succ x => by
      show (ρ'.motive x).map _ = none
      rw [h.motive' x]
      rfl
  block := fun D => by
    show (ρ'.block D).map _ = ((ρ.block D).map _).map _
    rw [h.block D, Option.map_map, Option.map_map]
    refine congrArg (fun f => Option.map f (ρ.block D)) (funext fun b => ?_)
    show Lifting.BlockMotive.mk ((b.type.subst θ).rename Ren.weaken)
        ((b.motive.subst (Subst.lift θ')).rename (Ren.lift Ren.weaken)) b.level =
      Lifting.BlockMotive.mk ((b.type.rename Ren.weaken).subst (Subst.lift θ))
        ((b.motive.rename (Ren.lift Ren.weaken)).subst (Subst.lift (Subst.lift θ'))) b.level
    rw [Term.subst_lift_rename_lift_weaken, Term.subst_lift_rename_weaken]

/-- A lifting substituted, under `n` new variables of both scopes. -/
theorem Lifting.Substitutes.liftN {Γ' Γ Δ' Δ : Scope} :
    (n : Nat) → {θ : Subst k Γ Δ} → {θ' : Subst k Γ' Δ'} → {ρ : Lifting k Δ' Δ} →
      {ρ' : Lifting k Γ' Γ} → Lifting.Substitutes θ θ' ρ ρ' →
        Lifting.Substitutes (Subst.liftN n θ) (Subst.liftN n θ') (ρ.liftN n) (ρ'.liftN n)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h =>
    Lifting.Substitutes.liftN (Γ' := .var :: Γ') (Γ := .var :: Γ) (Δ' := .var :: Δ')
      (Δ := .var :: Δ) n h.lift

/-- A lifting substituted, in scopes extended by a new entry. -/
theorem Lifting.Substitutes.weaken {Γ' Γ Δ' Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ}
    (h : Lifting.Substitutes θ θ' ρ ρ') :
    Lifting.Substitutes θ (Subst.lift (e := e) θ') ρ.weaken ρ'.weaken where
  ren := fun {a} x => by
    show (θ' (ρ.ren x)).rename (Ren.liftN a.params.length Ren.weaken) = _
    rw [h.ren x]
    exact Term.rename_rename_of (Ren.liftN_comp_of _ (α₁ := Ren.weaken) (α₂ := ρ'.ren)
      (α₃ := fun y => (ρ'.ren y).succ) fun _ => rfl) _
  motive := fun x => by
    show (ρ.motive x).map _ = none
    rw [h.motive x]
    rfl
  motive' := fun x => by
    show (ρ'.motive x).map _ = none
    rw [h.motive' x]
    rfl
  block := fun D => by
    show (ρ'.block D).map _ = ((ρ.block D).map _).map _
    rw [h.block D, Option.map_map, Option.map_map]
    refine congrArg (fun f => Option.map f (ρ.block D)) (funext fun b => ?_)
    exact congrArg (fun C => Lifting.BlockMotive.mk (b.type.subst θ) C b.level)
      (Term.subst_lift_rename_lift_weaken θ' b.motive)

/-- A term renamed by a lifting and then substituted is the term substituted and then renamed by
the lifting substituted, under `n` new variables. -/
theorem Lifting.Substitutes.subst_rename {Γ' Γ Δ' Δ : Scope} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ}
    (h : Lifting.Substitutes θ θ' ρ ρ') (n : Nat) (t : Term k (Δ.extend n)) :
    (t.rename (Ren.liftN n ρ.ren)).subst (Subst.liftN n θ') =
      (t.subst (Subst.liftN n θ)).rename (Ren.liftN n ρ'.ren) :=
  (Term.subst_rename_of (fun _ => rfl) t).trans
    (Term.rename_subst_of (fun x => (Subst.liftN_rename_comm_of n h.ren x).symm) t).symm

/-- A term renamed by a lifting and then substituted is the term substituted and then renamed by
the lifting substituted. -/
theorem Lifting.Substitutes.subst_rename₀ {Γ' Γ Δ' Δ : Scope} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ}
    (h : Lifting.Substitutes θ θ' ρ ρ') (t : Term k Δ) :
    (t.rename ρ.ren).subst θ' = (t.subst θ).rename ρ'.ren :=
  h.subst_rename 0 t

/-- A lifting substituted, and then substituted again, is the lifting substituted by the
substitutions that give each variable what the first ones give it, substituted by the second
ones. -/
theorem Lifting.Substitutes.comp {Γ' Γ Δ' Δ Ξ' Ξ : Scope} {θ₁ : Subst k Δ Ξ}
    {θ₁' : Subst k Δ' Ξ'} {θ₂ : Subst k Γ Δ} {θ₂' : Subst k Γ' Δ'} {ρ₁ : Lifting k Ξ' Ξ}
    {ρ₂ : Lifting k Δ' Δ} {ρ₃ : Lifting k Γ' Γ} (h₁ : Lifting.Substitutes θ₁ θ₁' ρ₁ ρ₂)
    (h₂ : Lifting.Substitutes θ₂ θ₂' ρ₂ ρ₃) :
    Lifting.Substitutes (fun {a} x => (θ₁ x).subst (Subst.liftN a.params.length θ₂))
      (fun {a} x => (θ₁' x).subst (Subst.liftN a.params.length θ₂')) ρ₁ ρ₃ where
  ren := fun {a} x => by
    rw [h₁.ren x]
    exact h₂.subst_rename a.params.length (θ₁ x)
  motive := h₁.motive
  motive' := h₂.motive'
  block := fun D => by
    rw [h₂.block D, h₁.block D, Option.map_map]
    refine congrArg (fun f => Option.map f (ρ₁.block D)) (funext fun b => ?_)
    exact Lifting.BlockMotive.mk_congr b.level (Term.subst_subst_of (fun _ => rfl) b.type)
      (Term.subst_subst_of (Subst.lift_subst_of fun _ => rfl) b.motive)

/-- A lifting that lifts no variable is itself, substituted by the substitutions that give each
variable itself. -/
theorem Lifting.Substitutes.refl {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) :
    Lifting.Substitutes (fun x => Var.eta x) (fun x => Var.eta x) ρ ρ where
  ren := fun x => (Var.eta_rename ρ.ren x).symm
  motive := hρ
  motive' := hρ
  block := fun D => by
    cases ρ.block D with
    | none => rfl
    | some b =>
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level
        (Term.subst_id_of (fun _ => rfl) b.type).symm
        (Term.subst_id_of (Subst.lift_id_of fun _ => rfl) b.motive).symm)

/-- A lifting substituted, in a scope extended by a new entry, which the substitution of this
scope gives any abstraction. -/
theorem Lifting.Substitutes.ofSnoc {Γ' Γ Δ' Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ}
    {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ} {ρ' : Lifting k Γ' Γ}
    (h : Lifting.Substitutes θ θ' ρ ρ') (u : Term k (Γ'.extend e.params.length)) :
    Lifting.Substitutes θ (Subst.snoc (e := e) θ' u) ρ.weaken ρ' where
  ren := fun x => h.ren x
  motive := fun x => by
    show (ρ.motive x).map _ = none
    rw [h.motive x]
    rfl
  motive' := h.motive'
  block := fun D => by
    show ρ'.block D = ((ρ.block D).map _).map _
    rw [h.block D, Option.map_map]
    refine congrArg (fun f => Option.map f (ρ.block D)) (funext fun b => ?_)
    exact Lifting.BlockMotive.mk_congr b.level rfl
      (Term.subst_rename_of (fun x => by cases x <;> rfl) b.motive).symm

/-- The motive of a parameter lifted, in the scope of its telescope followed by a term, substituted
under this telescope, is this motive substituted under the telescope and under the term. -/
theorem Term.subst_extend_snoc : {Γ Δ : Scope} → (ps : List Parameter) → (p : Parameter) →
    (θ : Subst k Γ Δ) → (B : Term k (.var :: Δ.extend ps.length)) →
      (Scope.extend_snoc Δ ps p ▸ B).subst (Subst.liftN (ps ++ [p]).length θ) =
        Scope.extend_snoc Γ ps p ▸ B.subst (Subst.lift (Subst.liftN ps.length θ))
  | _, _, [], _, _, _ => rfl
  | Γ, Δ, _ :: ps, p, θ, B =>
    Term.subst_extend_snoc (Γ := .var :: Γ) (Δ := .var :: Δ) ps p (Subst.lift θ) B

/-- The first variable, substituted under itself, is itself. -/
theorem Term.var₀_zero_subst_lift {Γ Δ : Scope} (θ : Subst k Γ Δ) :
    (Term.var₀ (.zero : Var (.var :: Δ) .var)).subst (Subst.lift θ) = .var₀ .zero := by
  rw [Term.var₀, Term.subst]
  exact Var.eta_instantiate (.zero : Var (.var :: Γ) .var) _

mutual

-- ADE: none.
/-- A type lifted by a lifting that lifts no variable, substituted, is the type substituted,
lifted by the lifting substituted, at the term substituted and at the same nesting, of the same
level. -/
theorem Term.Lifts.subst {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {l : Level k} → Term.Lifts sig v ρ n e A A' l →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ},
        Lifting.Substitutes θ θ' ρ ρ' →
          Term.Lifts sig v ρ' n (e.subst θ') (A.subst θ) (A'.subst θ') l
  | _, _, _, _, _, _, _, _, .var hx _, _, _, _, _, _, hs =>
    nomatch (hs.motive _).symm.trans hx
  | _, _, _, _, e, _, _, _, .block (b := b) hD hT, _, _, θ, θ', _, hs => by
    rw [Term.subst, Term.subst_subst₀_of (Subst₀.Swaps.single e θ') b.motive]
    refine Term.Lifts.block (b := b.subst θ θ') ?_ ?_
    · rw [hs.block, hD]
      rfl
    · show b.type.subst θ = _
      rw [hT, Term.subst]
  | _, _, _, _, _, _, _, _, .inst h hD hn hq hl hp has hS hL, _, _, _, _, _, hs => by
    simp only [Term.subst, InstanceArgs.subst]
    exact Term.Lifts.inst h hD hn hq hl hp (has.subst hs) hS hL

-- ADE: none.
/-- The arguments of an instance lifted by a lifting that lifts no variable, substituted, are the
arguments substituted, lifted by the lifting substituted, at the same nestings, at the same
parameters and of the same levels. -/
theorem InstanceArgs.Lifts.subst {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ls : List (Level k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig v ρ ns as S ls as' →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ},
        Lifting.Substitutes θ θ' ρ ρ' →
          InstanceArgs.Lifts sig v ρ' ns (as.subst θ) S ls (as'.subst θ')
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _ => .nil
  | _, _, _, _, _, _, _, _, _, _, .lifted (a := a) (B := B) (B' := B') has hB, _, _, θ, θ', _,
      hs => by
    have hB' := hB.subst (hs.liftN a.params.length).weaken
    rw [Term.var₀_zero_subst_lift] at hB'
    rw [InstanceArgs.subst, InstanceArgs.subst, InstanceArgs.subst,
      hs.subst_rename a.params.length B,
      Term.subst_extend_snoc a.params Lifting.termParam θ' B']
    exact InstanceArgs.Lifts.lifted (has.subst hs) hB'
  | _, _, _, _, _, _, _, _, _, _, .absent (a := a) (B := B) has _ hn, _, _, _, _, _, hs => by
    rw [InstanceArgs.subst, InstanceArgs.subst, hs.subst_rename a.params.length B]
    exact InstanceArgs.Lifts.absent (has.subst hs)
      (fun y hy => nomatch ((hs.liftN a.params.length).motive' y).symm.trans
        (Option.eq_some_of_isSome hy))
      hn

end

/-! ## Liftings at Instantiated Levels -/

/-- The motive of a type of a block, at instantiated levels. -/
def Lifting.BlockMotive.substLevels {k' : Nat} {Γ' Γ : Scope} (ls' : Fin k → Level k')
    (b : Lifting.BlockMotive k Γ' Γ) : Lifting.BlockMotive k' Γ' Γ :=
  ⟨b.type.substLevels ls', b.motive.substLevels ls', b.level.subst ls'⟩

/-- The lifting `ρ` at instantiated levels: the levels of the motives of the variables lifted, and
the motives of the types of the block, are instantiated. -/
def Lifting.substLevels {k' : Nat} {Γ' Γ : Scope} (ls' : Fin k → Level k')
    (ρ : Lifting k Γ' Γ) : Lifting k' Γ' Γ where
  ren := ρ.ren
  motive := fun x => (ρ.motive x).map (Prod.map id (Level.subst ls'))
  block := fun D => (ρ.block D).map (Lifting.BlockMotive.substLevels ls')

/-- Liftings are the same when their renamings, their variables lifted and the motives of their
types of the block are. -/
theorem Lifting.ext_of {Γ' Γ : Scope} {ρ₁ ρ₂ : Lifting k Γ' Γ}
    (hr : ∀ {a} (x : Var Γ a), ρ₁.ren x = ρ₂.ren x)
    (hm : ∀ {a} (x : Var Γ a), ρ₁.motive x = ρ₂.motive x)
    (hb : ∀ D, ρ₁.block D = ρ₂.block D) : ρ₁ = ρ₂ := by
  obtain ⟨r₁, m₁, b₁⟩ := ρ₁
  obtain ⟨r₂, m₂, b₂⟩ := ρ₂
  have hr' : @r₁ = @r₂ := funext fun _ => funext fun x => hr x
  have hm' : @m₁ = @m₂ := funext fun _ => funext fun x => hm x
  have hb' : b₁ = b₂ := funext hb
  subst hr' hm' hb'
  rfl

/-- A lifting under a new entry of both scopes, at instantiated levels. -/
theorem Lifting.substLevels_lift {k' : Nat} {Γ' Γ : Scope} {e : Scope.Entry}
    (ls' : Fin k → Level k') (ρ : Lifting k Γ' Γ) :
    (ρ.lift (e := e)).substLevels ls' = (ρ.substLevels ls').lift :=
  Lifting.ext_of (fun _ => rfl)
    (fun x =>
      match x with
      | .zero => rfl
      | .succ x => by
        show ((ρ.motive x).map _).map _ = ((ρ.motive x).map _).map _
        cases ρ.motive x <;> rfl)
    (fun D => by
      show ((ρ.block D).map _).map _ = ((ρ.block D).map _).map _
      cases ρ.block D with
      | none => rfl
      | some b =>
        show some (Lifting.BlockMotive.mk ((b.type.rename Ren.weaken).substLevels ls')
            ((b.motive.rename (Ren.lift Ren.weaken)).substLevels ls') (b.level.subst ls')) =
          some (Lifting.BlockMotive.mk ((b.type.substLevels ls').rename Ren.weaken)
            ((b.motive.substLevels ls').rename (Ren.lift Ren.weaken)) (b.level.subst ls'))
        rw [Term.substLevels_rename, Term.substLevels_rename])

/-- A lifting under `n` new variables of both scopes, at instantiated levels. -/
theorem Lifting.substLevels_liftN {k' : Nat} (ls' : Fin k → Level k') {Γ' Γ : Scope} :
    (n : Nat) → (ρ : Lifting k Γ' Γ) → (ρ.liftN n).substLevels ls' = (ρ.substLevels ls').liftN n
  | 0, _ => rfl
  | n + 1, ρ => by
    show (ρ.lift.liftN n).substLevels ls' = (ρ.substLevels ls').lift.liftN n
    rw [Lifting.substLevels_liftN ls' n ρ.lift, Lifting.substLevels_lift]

/-- A lifting in a scope extended by a new entry, at instantiated levels. -/
theorem Lifting.substLevels_weaken {k' : Nat} {Γ' Γ : Scope} {e : Scope.Entry}
    (ls' : Fin k → Level k') (ρ : Lifting k Γ' Γ) :
    (ρ.weaken (e := e)).substLevels ls' = (ρ.substLevels ls').weaken :=
  Lifting.ext_of (fun _ => rfl)
    (fun x => by
      show ((ρ.motive x).map _).map _ = ((ρ.motive x).map _).map _
      cases ρ.motive x <;> rfl)
    (fun D => by
      show ((ρ.block D).map _).map _ = ((ρ.block D).map _).map _
      cases ρ.block D with
      | none => rfl
      | some b =>
        show some (Lifting.BlockMotive.mk (b.type.substLevels ls')
            ((b.motive.rename (Ren.lift Ren.weaken)).substLevels ls') (b.level.subst ls')) =
          some (Lifting.BlockMotive.mk (b.type.substLevels ls')
            ((b.motive.substLevels ls').rename (Ren.lift Ren.weaken)) (b.level.subst ls'))
        rw [Term.substLevels_rename])

/-- A lifting extended by a parameter, at instantiated levels. -/
theorem Lifting.cons_substLevels {k' : Nat} {Δ' Δ : Scope} {e : Scope.Entry}
    (ls' : Fin k → Level k') (l : Level k) :
    (b : Bool) → (ρ : Lifting k Δ' Δ) →
      (Lifting.cons (e := e) l b ρ).substLevels ls' =
        Lifting.cons (l.subst ls') b (ρ.substLevels ls')
  | false, ρ => Lifting.substLevels_lift ls' ρ
  | true, ρ =>
    Lifting.ext_of (fun _ => rfl)
      (fun x =>
        match x with
        | .zero => rfl
        | .succ x => by
          show ((ρ.motive x).map _).map _ = ((ρ.motive x).map _).map _
          cases ρ.motive x <;> rfl)
      (fun D => by
        show (((ρ.lift (e := e)).weaken (e := e.motive)).substLevels ls').block D =
          (((ρ.substLevels ls').lift (e := e)).weaken (e := e.motive)).block D
        rw [Lifting.substLevels_weaken, Lifting.substLevels_lift])

/-- The lifting of parameters, at instantiated levels, has motives at the levels instantiated. -/
theorem Lifting.base_substLevels {k' : Nat} (S : List Nat) (lv : Nat → Level k)
    (ls' : Fin k → Level k') :
    (Δ : Scope) →
      (Lifting.base S lv Δ).substLevels ls' = Lifting.base S (fun i => (lv i).subst ls') Δ
  | [] => Lifting.ext_of (fun x => nomatch x) (fun x => nomatch x) (fun _ => rfl)
  | _ :: Δ => by
    show (Lifting.cons _ _ (Lifting.base S lv Δ)).substLevels ls' =
      Lifting.cons _ _ (Lifting.base S (fun i => (lv i).subst ls') Δ)
    rw [Lifting.cons_substLevels, Lifting.base_substLevels S lv ls' Δ]

/-- A variable lifted by a lifting at instantiated levels is lifted by the lifting. -/
theorem Lifting.isSome_of_substLevels {k' : Nat} {Γ' Γ : Scope} {a : Scope.Entry}
    {ls' : Fin k → Level k'} {ρ : Lifting k Γ' Γ} {x : Var Γ a}
    (h : ((ρ.substLevels ls').motive x).isSome) : (ρ.motive x).isSome := by
  rwa [show (ρ.substLevels ls').motive x = (ρ.motive x).map (Prod.map id (Level.subst ls'))
    from rfl, Option.isSome_map] at h

/-- Arguments followed by one more, at instantiated levels. -/
theorem Args.substLevels_snoc {k' : Nat} {Γ : Scope} {p : Parameter} (ls' : Fin k → Level k') :
    {ps : List Parameter} → (ts : Args k Γ ps) → (t : Term k Γ) →
      (ts.snoc (p := p) t).substLevels ls' = (ts.substLevels ls').snoc (t.substLevels ls')
  | [], .nil, _ => rfl
  | _ :: _, .cons u us, t => congrArg (Args.cons (u.substLevels ls')) (Args.substLevels_snoc ls' us t)

/-- A term of a scope equal to another, at instantiated levels. -/
theorem Term.substLevels_cast {k' : Nat} {Γ₁ Γ₂ : Scope} (ls' : Fin k → Level k')
    (h : Γ₁ = Γ₂) (t : Term k Γ₁) : (h ▸ t).substLevels ls' = h ▸ t.substLevels ls' := by
  subst h
  rfl

mutual

-- ADE: none.
/-- A type lifted, at instantiated levels, is the type at these levels, lifted by the lifting at
these levels, at the term at these levels and at the same nesting, of the level instantiated. -/
theorem Term.Lifts.substLevels {k' : Nat} {sig : Signature} {v : Lifting.Variables}
    (ls' : Fin k → Level k') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {l : Level k} → Term.Lifts sig v ρ n e A A' l →
        Term.Lifts sig v (ρ.substLevels ls') n (e.substLevels ls') (A.substLevels ls')
          (A'.substLevels ls') (l.subst ls')
  | _, _, ρ, _, _, _, _, _, .var (x := x) hx hts => by
    rw [Term.substLevels, Term.substLevels, Args.substLevels_snoc, Args.substLevels_rename]
    refine Term.Lifts.var ?_ fun z hz => (hts z (Lifting.isSome_of_substLevels hz)).substLevels ls'
    show (ρ.motive x).map _ = _
    rw [hx]
    rfl
  | _, _, ρ, _, e, _, _, _, .block (D := D) (b := b) hD hT => by
    rw [Term.substLevels, Term.substLevels_subst₀_of
      (σ' := Subst₀.single (e.substLevels ls')) (fun x => by cases x <;> rfl) b.motive]
    refine Term.Lifts.block (b := b.substLevels ls') ?_ ?_
    · show (ρ.block D).map _ = _
      rw [hD]
      rfl
    · show b.type.substLevels ls' = _
      rw [hT, Term.substLevels]
  | _, _, _, _, _, _, _, _, .inst (ls := ls) h hD hn hq hl hp has hS hL => by
    simp only [Term.substLevels, InstanceArgs.substLevels, List.map_append]
    rw [Level.subst_joins, Level.subst_subst, ← Level.getFin_map_subst ls' ls hl]
    exact Term.Lifts.inst h hD hn hq ((List.length_map _).trans hl) hp (has.substLevels ls') hS hL

-- ADE: none.
/-- The arguments of an instance lifted, at instantiated levels, are the arguments at these levels,
lifted by the lifting at these levels, at the same nestings and at the same parameters, of the
levels instantiated. -/
theorem InstanceArgs.Lifts.substLevels {k' : Nat} {sig : Signature} {v : Lifting.Variables}
    (ls' : Fin k → Level k') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ls : List (Level k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ls as' →
        InstanceArgs.Lifts sig v (ρ.substLevels ls') ns (as.substLevels ls') S
          (ls.map (Level.subst ls')) (as'.substLevels ls')
  | _, _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, ρ, _, _, _, _, _, _, _, .lifted (a := a) has hB => by
    have hB' := hB.substLevels ls'
    rw [Lifting.substLevels_weaken, Lifting.substLevels_liftN] at hB'
    simp only [InstanceArgs.substLevels, List.map_append, List.map_cons, List.map_nil]
    rw [Term.substLevels_rename, Term.substLevels_cast]
    exact InstanceArgs.Lifts.lifted (has.substLevels ls') hB'
  | _, _, ρ, _, _, _, _, _, _, _, .absent (a := a) has hB hn => by
    simp only [InstanceArgs.substLevels]
    rw [Term.substLevels_rename]
    refine InstanceArgs.Lifts.absent (has.substLevels ls') (fun y hy => ?_) hn
    rw [← Lifting.substLevels_liftN] at hy
    exact (hB y (Lifting.isSome_of_substLevels hy)).substLevels ls'

end

end Sic.Core
