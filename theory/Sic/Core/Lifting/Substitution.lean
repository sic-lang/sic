module

public import Sic.Core.Lifting
import Sic.Core.Substitution.Levels

/-!
# Substitution of the Liftings

The parts of the declaration of a lifting of annex 20 of RFC 36 under the renamings, the
substitutions and the instantiation of the level variables: a telescope followed by an entry, as
the telescope of a motive is, and the parameters, the type of the parameter `y` and the sort of the
lifting at an instance of its variables, where the levels of the motives are those of the arguments
lifted.

The renaming of the parameters in the parameters lifted does not read the levels of the motives.

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

end Sic.Core
