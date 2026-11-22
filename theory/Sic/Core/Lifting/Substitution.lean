module

public import Sic.Core.Lifting
import Sic.Core.Positivity.Substitution
import Sic.Core.Substitution.Composition
import Sic.Core.Substitution.Levels

/-!
# Substitution of the Liftings

The parts of the declaration of a lifting of annex 13 of RFC 36 under the renamings, the
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

/-! ## Factors of the Instances -/

/-- An instance of a lifting has its factor at any lifting of the scope, at any levels and at any
arguments: the factor of an instance reads its name, its qualities and its grades, and the motives
of the lifting of the scope of its declaration only. -/
theorem Term.Factor.inst_congr {sig : Signature} {k' : Nat} {Γ₁' Γ₁ Γ₂' Γ₂ Δ₁ Δ₂ : Scope}
    {ρ₁ : Lifting k Γ₁' Γ₁} (ρ₂ : Lifting k' Γ₂' Γ₂) {D : Name} {qs : List Quality}
    {ls₁ : List (Level k)} (ls₂ : List (Level k')) {ps : List Grade} {as₁ : InstanceArgs k Γ₁' Δ₁}
    (as₂ : InstanceArgs k' Γ₂' Δ₂) {π : Grade} (h : Term.Factor sig ρ₁ (.inst D qs ls₁ ps as₁) π) :
    Term.Factor sig ρ₂ (.inst D qs ls₂ ps as₂) π := by
  cases h with
  | inst hdecl hD h hqp hds => exact .inst hdecl hD h hqp hds

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
    (l : Level k) (χ : Grade) (hT : T = T') (hC : C = C') :
    Lifting.BlockMotive.mk (Γ' := Γ') T C l χ = Lifting.BlockMotive.mk T' C' l χ := by
  rw [hT, hC]

/-- The motive of a type of a block, in a lifting under `n` new variables, is its motive in the
lifting, renamed under these variables. -/
theorem Lifting.liftN_block : (n : Nat) → {Γ' Γ : Scope} → (ρ : Lifting k Γ' Γ) → (D : Name) →
    (ρ.liftN n).block D = (ρ.block D).map fun b =>
      ⟨b.type.rename (Ren.weakenN n), b.motive.rename (Ren.lift (Ren.weakenN n)), b.level,
        b.ownership⟩
  | 0, _, _, ρ, D => by
    show ρ.block D = _
    cases ρ.block D with
    | none => rfl
    | some b =>
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level b.ownership
        (Term.rename_id_of (fun _ => rfl) b.type).symm
        (Term.rename_id_of (Ren.lift_id_of fun _ => rfl) b.motive).symm)
  | n + 1, _, _, ρ, D => by
    show (ρ.lift.liftN n).block D = _
    rw [Lifting.liftN_block n ρ.lift D]
    show ((ρ.block D).map Lifting.BlockMotive.lift).map _ = _
    cases ρ.block D with
    | none => rfl
    | some b =>
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level b.ownership
        (Term.rename_rename_of (α₁ := Ren.weakenN n) (α₂ := Ren.weaken)
          (α₃ := Ren.weakenN (n + 1)) (fun _ => rfl) b.type)
        (Term.rename_rename_of (α₁ := Ren.lift (Ren.weakenN n)) (α₂ := Ren.lift Ren.weaken)
          (α₃ := Ren.lift (Ren.weakenN (n + 1))) (fun x => by cases x <;> rfl) b.motive))

/-- The renamings of two liftings extended by a parameter are the same when those of the liftings
are, whatever the motives give the results. -/
theorem Lifting.cons_ren_congr {k' : Nat} {Δ' Δ : Scope} {e : Scope.Entry} (m : Lifting.Result k)
    (m' : Lifting.Result k') {ρ : Lifting k Δ' Δ} {ρ' : Lifting k' Δ' Δ}
    (h : ∀ {a} (x : Var Δ a), ρ.ren x = ρ'.ren x) :
    (b : Bool) → ∀ {a} (x : Var (e :: Δ) a),
      (Lifting.cons m b ρ).ren x = (Lifting.cons m' b ρ').ren x
  | true, _, .zero => rfl
  | true, _, .succ x => congrArg (fun y => Var.succ (Var.succ y)) (h x)
  | false, _, .zero => rfl
  | false, _, .succ x => congrArg Var.succ (h x)

/-- The lifting of parameters lifts no type of a block. -/
theorem Lifting.base_block (S : List Nat) (mv : Nat → Lifting.Result k) :
    (Δ : Scope) → ∀ D, (Lifting.base S mv Δ).block D = none
  | [], _ => rfl
  | e :: Δ, D => by
    show (Lifting.cons (e := e) (mv Δ.length) (decide (Δ.length ∈ S)) (Lifting.base S mv Δ)).block D
      = none
    cases decide (Δ.length ∈ S) with
    | true =>
      show (((Lifting.base S mv Δ).block D).map _).map _ = none
      rw [Lifting.base_block S mv Δ D]
      rfl
    | false =>
      show ((Lifting.base S mv Δ).block D).map _ = none
      rw [Lifting.base_block S mv Δ D]
      rfl

/-- The renaming of the parameters in the parameters lifted does not read what the motives give the
results. -/
theorem Lifting.base_ren {k' : Nat} (S : List Nat) (mv : Nat → Lifting.Result k)
    (mv' : Nat → Lifting.Result k') (Δ : Scope) :
    @Lifting.ren k _ _ (Lifting.base S mv Δ) = @Lifting.ren k' _ _ (Lifting.base S mv' Δ) := by
  funext a x
  exact go Δ x
where
  /-- The equality at a variable, by recursion on the parameters. -/
  go : (Δ : Scope) → ∀ {a} (x : Var Δ a),
      (Lifting.base S mv Δ).ren x = (Lifting.base S mv' Δ).ren x
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
theorem Instance.lifted_ofLists {j g n : Nat} (qs : List Quality) (ps : List Grade) (s : Quality)
    (gs : List Grade) (hq : qs.length = j) (hp : ps.length = g) (hq' : (qs ++ [s]).length = j + 1)
    (hp' : (ps ++ gs).length = g + (2 + 2 * n)) :
    (Instance.ofLists (qs ++ [s]) (ps ++ gs) hq' hp').lifted = Instance.ofLists qs ps hq hp := by
  unfold Instance.lifted Instance.ofLists
  congr 1
  · funext i
    exact List.getFin_append_castAdd qs [s] hq hq' i
  · funext i
    exact List.getFin_append_castAdd ps gs hp hp' i

/-- The quality of the sorts of the motives, at an instance of the variables of a lifting given by
lists, is the last quality. -/
theorem Instance.sorts_last_ofLists {j g : Nat} (qs : List Quality) (ps : List Grade)
    (s : Quality) (hq : qs.length = j) (hq' : (qs ++ [s]).length = j + 1) (hp : ps.length = g) :
    (Instance.ofLists (qs ++ [s]) ps hq' hp).sorts (Fin.last j) = s :=
  List.getFin_append_natAdd qs [s] hq rfl hq' 0

/-- The grades of the results `m̄` are two for each. -/
theorem Lifting.Result.length_grades (ms : List (Lifting.Result k)) :
    (Lifting.Result.grades ms).length = 2 * ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [Lifting.Result.grades, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- The grades of an instance of a lifting are as many as its grade variables. -/
theorem Lifting.Variables.length_grades (v : Lifting.Variables) {g n : Nat} {ps : List Grade}
    {ms : List (Lifting.Result k)} (hp : ps.length = g) (hm : ms.length = n) :
    (v.grades ps ms).length = g + (2 + 2 * n) := by
  simp only [Lifting.Variables.grades, List.length_append, List.length_cons,
    Lifting.Result.length_grades, hp, hm]
  omega

/-- The variables that a lifting adds, at an instance of its variables given by lists, but those of
its motives, are the last quality and the two grades after those of the type declaration. -/
theorem Instance.liftingVariables_ofLists {j g n : Nat} (qs : List Quality) (ps : List Grade)
    (v : Lifting.Variables) (ms : List (Lifting.Result k)) (hq : qs.length = j) (hp : ps.length = g)
    (hq' : (qs ++ [v.quality]).length = j + 1) (hp' : (v.grades ps ms).length = g + (2 + 2 * n)) :
    (Instance.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp').liftingVariables = v := by
  obtain ⟨s, r, ς⟩ := v
  have hm : (r :: ς :: Lifting.Result.grades ms).length = 2 + 2 * n := by
    simp only [Lifting.Variables.grades, List.length_append, hp] at hp'
    omega
  exact congr (congr (congrArg Lifting.Variables.mk
      (Instance.sorts_last_ofLists qs _ s hq hq' hp'))
    (List.getFin_append_natAdd ps _ hp hm hp' ⟨0, by omega⟩))
    (List.getFin_append_natAdd ps _ hp hm hp' ⟨1, by omega⟩)

/-- The grade `2 · j + o` of the results `m̄` is the factor (`o = 0`) or the ownership (`o = 1`) of
the result at the position `j`. -/
theorem Lifting.Result.getElem_grades (o : Fin 2) :
    (ms : List (Lifting.Result k)) → (j : Nat) → (hj : j < ms.length) →
      (h : 2 * j + o < (Lifting.Result.grades ms).length) →
        (Lifting.Result.grades ms)[2 * j + o] = [ms[j].factor, ms[j].ownership][o]
  | [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | m :: ms, 0, _, _ =>
    match o with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  | m :: ms, j + 1, hj, h => by
    have e : 2 * (j + 1) + o = (2 * j + o) + 2 := by omega
    simp only [e, Lifting.Result.grades, List.flatMap_cons, List.cons_append, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_succ]
    exact Lifting.Result.getElem_grades o ms j (Nat.lt_of_succ_lt_succ hj) _

/-- The factor (`o = 0`) or the ownership (`o = 1`) of the motive of the parameter at the position
`j` of `S`, at an instance of the variables of a lifting given by lists, is the factor or the
ownership of the result at the position `j` of the results of the instance. -/
theorem Lifting.motiveGrade_ofLists {j' g : Nat} {S : List Nat} (hS : S.Nodup) (qs : List Quality)
    (ps : List Grade) (v : Lifting.Variables) (ms : List (Lifting.Result k))
    (hq : qs.length = j') (hp : ps.length = g) (hm : ms.length = S.length)
    (hp' : (v.grades ps ms).length = g + (2 + 2 * S.length)) (o : Fin 2) (j : Nat)
    (hj : j < S.length) :
    Lifting.motiveGrade S (.ofLists qs (v.grades ps ms) hq hp') o S[j] =
      [ms[j].factor, ms[j].ownership][o] := by
  have hi : S.idxOf S[j] = j := hS.idxOf_getElem j hj
  have hm' : (v.recursion :: v.requirement :: Lifting.Result.grades ms).length =
      2 + 2 * S.length := by
    rw [List.length_cons, List.length_cons, Lifting.Result.length_grades, hm]
    omega
  unfold Lifting.motiveGrade
  split
  case isFalse hn => exact absurd (hi.symm ▸ hj) hn
  show (ps ++ (v.recursion :: v.requirement :: Lifting.Result.grades ms)).getFin hp' _ = _
  rw [List.getFin_append_natAdd ps _ hp hm' hp']
  have e : 2 + 2 * S.idxOf S[j] + o = (2 * j + o) + 2 := by omega
  simp only [List.getFin, List.get_eq_getElem, Fin.val_cast, e, List.getElem_cons_succ]
  exact Lifting.Result.getElem_grades o ms j (hm ▸ hj) _

/-- What a type lifted gives the result of a destructor, at instantiated levels: the level of its
sort at these levels, with the same factor and ownership. -/
def Lifting.Result.substLevels {k' : Nat} (ls' : Fin k → Level k') (m : Lifting.Result k) :
    Lifting.Result k' :=
  ⟨m.level.subst ls', m.factor, m.ownership⟩

/-- The motive of the parameter at the position `j` of `S`, at an instance of the variables of the
lifting given by lists, at the levels of this instance, is the result at the position `j` of the
results of the instance: its level, its factor and its ownership. -/
theorem TypeDeclaration.liftingMotive_ofLists {decl : TypeDeclaration} {S : List Nat}
    (hS : S.Nodup) {v : Lifting.Variables} {qs : List Quality} {ls : List (Level k)}
    {ms : List (Lifting.Result k)} {ps : List Grade}
    (hq' : (qs ++ [v.quality]).length = decl.sorts + 1) (hl : ls.length = decl.levels)
    (hm : ms.length = S.length) (hl' : (ls ++ ms.map (·.level)).length = decl.levels + S.length)
    (hp : ps.length = decl.grades) (hp' : (v.grades ps ms).length = decl.liftingGrades S)
    (j : Nat) (h₁ : j < S.length) (h₂ : j < ms.length) :
    (decl.liftingMotive S (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp') S[j]).substLevels
        ((ls ++ ms.map (·.level)).getFin hl') = ms[j] := by
  have hlv := Lifting.motiveLevel_subst hS hl (by rw [List.length_map, hm]) hl' j h₁
    (by rw [List.length_map]; exact h₂)
  have hf := Lifting.motiveGrade_ofLists hS (qs ++ [v.quality]) ps v ms hq' hp hm hp' 0 j h₁
  have ho := Lifting.motiveGrade_ofLists hS (qs ++ [v.quality]) ps v ms hq' hp hm hp' 1 j h₁
  simp only [TypeDeclaration.liftingMotive, Lifting.Result.substLevels, hlv, hf, ho,
    List.getElem_map]
  rfl

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
    {qs : List Quality} {ps : List Grade} {s : Quality} {gs : List Grade}
    {ls ls' : List (Level k)}
    (hqp : decl.AsMany qs ps) (hl : ls.length = decl.levels)
    (hl' : ls'.length = S.length) (hq' : (qs ++ [s]).length = decl.sorts + 1)
    (hp' : (ps ++ gs).length = decl.liftingGrades S)
    (h : (ls ++ ls').length = decl.levels + S.length) :
    (decl.liftingSort S (.ofLists (qs ++ [s]) (ps ++ gs) hq' hp')).substLevels
        ((ls ++ ls').getFin h) =
      ⟨s, ((decl.sort hqp.inst).level.subst (ls.getFin hl)).joins ls'⟩ := by
  have e : (List.ofFn fun i : Fin S.length => Level.var (Fin.natAdd decl.levels i)).map
      (Level.subst ((ls ++ ls').getFin h)) = ls' := by
    rw [List.map_ofFn]
    exact (congrArg List.ofFn (funext fun i => List.getFin_append_natAdd ls ls' hl hl' h i)).trans
      (List.ofFn_getFin ls' hl')
  unfold TypeDeclaration.liftingSort Universe.substLevels
  rw [Instance.lifted_ofLists qs ps s gs hqp.sorts hqp.grades,
    Instance.sorts_last_ofLists qs _ s hqp.sorts,
    Level.subst_joins, Level.subst_subst, Level.lifted_subst ls ls' hl h, e]

/-- The type of the parameter `y` of a lifting, at an instance of its variables, is the instance of
the type lifted at the instance of the type declaration. -/
theorem TypeDeclaration.liftedInstance_substLevels {Γ : Scope} (decl : TypeDeclaration) (F : Name)
    {n : Nat} {qs : List Quality} {ps : List Grade} {ls ls' : List (Level k)}
    (hqp : decl.AsMany qs ps) (hl : ls.length = decl.levels)
    (h : (ls ++ ls').length = decl.levels + n)
    (as : InstanceArgs (decl.levels + n) Γ decl.scope) :
    (decl.liftedInstance F n hqp.inst as).substLevels ((ls ++ ls').getFin h) =
      .inst F qs ls ps (as.substLevels ((ls ++ ls').getFin h)) := by
  unfold TypeDeclaration.liftedInstance TypeDeclaration.AsMany.inst Instance.ofLists
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
theorem Context.lifted_substLevels {k' : Nat} (S : List Nat) (s : Quality)
    (mv : Nat → Lifting.Result k) (ls' : Fin k → Level k') : {Δ : Scope} → (ctx : Context k Δ) →
      (ctx.lifted S s mv).substLevels ls' =
        (ctx.substLevels ls').lifted S s fun i => (mv i).substLevels ls'
  | _, .empty => rfl
  | _, .var (Γ := Δ) ctx A => by
    show (Context.liftedVar _ _ _ _).substLevels ls' = Context.liftedVar _ _ _ _
    rw [Context.liftedVar_substLevels, Context.lifted_substLevels S s mv ls' ctx,
      Term.substLevels_rename, Lifting.base_ren S mv (fun i => (mv i).substLevels ls') Δ]
    rfl
  | _, .secondOrder (Γ := Δ) ctx Θ A ψ => by
    show (Context.liftedSecondOrder _ _ _ _ _ _).substLevels ls' =
      Context.liftedSecondOrder _ _ _ _ _ _
    rw [Context.liftedSecondOrder_substLevels, Context.lifted_substLevels S s mv ls' ctx,
      Term.substLevels_rename, Telescope.substLevels_rename,
      Lifting.base_ren S mv (fun i => (mv i).substLevels ls') Δ]
    rfl

/-! ## Liftings Substituted -/

/-- The motive of a type of a block, substituted: its instance by `θ`, and its motive by `θ'`,
under the term that it is over. -/
def Lifting.BlockMotive.subst {Γ' Γ Δ' Δ : Scope} (θ : Subst k Γ Δ) (θ' : Subst k Γ' Δ')
    (b : Lifting.BlockMotive k Δ' Δ) : Lifting.BlockMotive k Γ' Γ :=
  ⟨b.type.subst θ, b.motive.subst (Subst.lift θ'), b.level, b.ownership⟩

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
        ((b.motive.subst (Subst.lift θ')).rename (Ren.lift Ren.weaken)) b.level b.ownership =
      Lifting.BlockMotive.mk ((b.type.rename Ren.weaken).subst (Subst.lift θ))
        ((b.motive.rename (Ren.lift Ren.weaken)).subst (Subst.lift (Subst.lift θ'))) b.level b.ownership
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
    exact congrArg (fun C => Lifting.BlockMotive.mk (b.type.subst θ) C b.level b.ownership)
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
    exact Lifting.BlockMotive.mk_congr b.level b.ownership (Term.subst_subst_of (fun _ => rfl) b.type)
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
      exact congrArg some (Lifting.BlockMotive.mk_congr b.level b.ownership
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
    exact Lifting.BlockMotive.mk_congr b.level b.ownership rfl
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

/-- A type lifted by a lifting that lifts no variable, substituted, is the type substituted,
lifted by the lifting substituted, at the term substituted and at the same nesting, of the same
result. -/
theorem Term.Lifts.subst {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ},
        Lifting.Substitutes θ θ' ρ ρ' →
          Term.Lifts sig v ρ' n (e.subst θ') (A.subst θ) (A'.subst θ') m
  | _, _, _, _, _, _, _, _, .var hx _, _, _, _, _, _, hs =>
    nomatch (hs.motive _).symm.trans hx
  | _, _, _, _, e, _, _, _, .block (b := b) hD, _, _, θ, θ', _, hs => by
    rw [Term.subst, Term.subst_subst₀_of (Subst₀.Swaps.single e θ') b.motive]
    refine Term.Lifts.block (b := b.subst θ θ') ?_
    rw [hs.block, hD]
    rfl
  | _, _, _, _, _, _, _, _, .inst h hD hn hqp hl has hS hL hπ, _, _, _, _, _, hs => by
    simp only [Term.subst, InstanceArgs.subst]
    exact Term.Lifts.inst h hD hn hqp hl (has.subst hs) hS hL (hπ.inst_congr _ _ _)

/-- The arguments of an instance lifted by a lifting that lifts no variable, substituted, are the
arguments substituted, lifted by the lifting substituted, at the same nestings, at the same
parameters and of the same results. -/
theorem InstanceArgs.Lifts.subst {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ},
        Lifting.Substitutes θ θ' ρ ρ' →
          InstanceArgs.Lifts sig v ρ' ns (as.subst θ) S ms (as'.subst θ')
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
  ⟨b.type.substLevels ls', b.motive.substLevels ls', b.level.subst ls', b.ownership⟩

/-- The levels of the results `m̄` at instantiated levels are their levels instantiated. -/
theorem Lifting.Result.levels_substLevels {k' : Nat} (ls' : Fin k → Level k')
    (ms : List (Lifting.Result k)) :
    (ms.map (Lifting.Result.substLevels ls')).map (·.level) =
      (ms.map (·.level)).map (Level.subst ls') := by
  rw [List.map_map, List.map_map]
  rfl

/-- The grades of the results `m̄` at instantiated levels are their grades. -/
theorem Lifting.Result.grades_substLevels {k' : Nat} (ls' : Fin k → Level k')
    (ms : List (Lifting.Result k)) :
    Lifting.Result.grades (ms.map (Lifting.Result.substLevels ls')) = Lifting.Result.grades ms := by
  simp only [Lifting.Result.grades, List.flatMap_map]
  rfl

/-- The grades of an instance of a lifting at the results `m̄` at instantiated levels are its grades
at `m̄`. -/
theorem Lifting.Variables.grades_substLevels {k' : Nat} (v : Lifting.Variables) (ps : List Grade)
    (ls' : Fin k → Level k') (ms : List (Lifting.Result k)) :
    v.grades ps (ms.map (Lifting.Result.substLevels ls')) = v.grades ps ms := by
  rw [Lifting.Variables.grades, Lifting.Result.grades_substLevels]

/-- The lifting `ρ` at instantiated levels: the levels of the motives of the variables lifted, and
the motives of the types of the block, are instantiated. -/
def Lifting.substLevels {k' : Nat} {Γ' Γ : Scope} (ls' : Fin k → Level k')
    (ρ : Lifting k Γ' Γ) : Lifting k' Γ' Γ where
  ren := ρ.ren
  motive := fun x => (ρ.motive x).map (Prod.map id (Lifting.Result.substLevels ls'))
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
            ((b.motive.rename (Ren.lift Ren.weaken)).substLevels ls') (b.level.subst ls') b.ownership) =
          some (Lifting.BlockMotive.mk ((b.type.substLevels ls').rename Ren.weaken)
            ((b.motive.substLevels ls').rename (Ren.lift Ren.weaken)) (b.level.subst ls') b.ownership)
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
            ((b.motive.rename (Ren.lift Ren.weaken)).substLevels ls') (b.level.subst ls') b.ownership) =
          some (Lifting.BlockMotive.mk (b.type.substLevels ls')
            ((b.motive.substLevels ls').rename (Ren.lift Ren.weaken)) (b.level.subst ls') b.ownership)
        rw [Term.substLevels_rename])

/-- A lifting extended by a parameter, at instantiated levels. -/
theorem Lifting.cons_substLevels {k' : Nat} {Δ' Δ : Scope} {e : Scope.Entry}
    (ls' : Fin k → Level k') (m : Lifting.Result k) :
    (b : Bool) → (ρ : Lifting k Δ' Δ) →
      (Lifting.cons (e := e) m b ρ).substLevels ls' =
        Lifting.cons (m.substLevels ls') b (ρ.substLevels ls')
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
theorem Lifting.base_substLevels {k' : Nat} (S : List Nat) (mv : Nat → Lifting.Result k)
    (ls' : Fin k → Level k') :
    (Δ : Scope) →
      (Lifting.base S mv Δ).substLevels ls' = Lifting.base S (fun i => (mv i).substLevels ls') Δ
  | [] => Lifting.ext_of (fun x => nomatch x) (fun x => nomatch x) (fun _ => rfl)
  | _ :: Δ => by
    show (Lifting.cons _ _ (Lifting.base S mv Δ)).substLevels ls' =
      Lifting.cons _ _ (Lifting.base S (fun i => (mv i).substLevels ls') Δ)
    rw [Lifting.cons_substLevels, Lifting.base_substLevels S mv ls' Δ]

/-- A variable lifted by a lifting at instantiated levels is lifted by the lifting. -/
theorem Lifting.isSome_of_substLevels {k' : Nat} {Γ' Γ : Scope} {a : Scope.Entry}
    {ls' : Fin k → Level k'} {ρ : Lifting k Γ' Γ} {x : Var Γ a}
    (h : ((ρ.substLevels ls').motive x).isSome) : (ρ.motive x).isSome := by
  rwa [show (ρ.substLevels ls').motive x =
      (ρ.motive x).map (Prod.map id (Lifting.Result.substLevels ls'))
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

/-- A type lifted, at instantiated levels, is the type at these levels, lifted by the lifting at
these levels, at the term at these levels and at the same nesting, of the result at these levels. -/
theorem Term.Lifts.substLevels {k' : Nat} {sig : Signature} {v : Lifting.Variables}
    (ls' : Fin k → Level k') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m →
        Term.Lifts sig v (ρ.substLevels ls') n (e.substLevels ls') (A.substLevels ls')
          (A'.substLevels ls') (m.substLevels ls')
  | _, _, ρ, _, _, _, _, _, .var (x := x) hx hts => by
    rw [Term.substLevels, Term.substLevels, Args.substLevels_snoc, Args.substLevels_rename]
    refine Term.Lifts.var ?_ fun z hz => (hts z (Lifting.isSome_of_substLevels hz)).substLevels ls'
    show (ρ.motive x).map _ = _
    rw [hx]
    rfl
  | _, _, ρ, _, e, _, _, _, .block (D := D) (b := b) hD => by
    rw [Term.substLevels, Term.substLevels_subst₀_of
      (σ' := Subst₀.single (e.substLevels ls')) (fun x => by cases x <;> rfl) b.motive]
    refine Term.Lifts.block (b := b.substLevels ls') ?_
    show (ρ.block D).map _ = _
    rw [hD]
    rfl
  | _, _, _, _, _, _, _, _, .inst (ls := ls) (ms := ms) h hD hn hqp hl has hS hL hπ => by
    simp only [Term.substLevels, InstanceArgs.substLevels, List.map_append, Lifting.Result.substLevels]
    rw [Level.subst_joins, Level.subst_subst, ← Level.getFin_map_subst ls' ls hl,
      ← Lifting.Result.levels_substLevels ls' ms]
    rw [← Lifting.Variables.grades_substLevels v _ ls' ms] at hπ ⊢
    exact Term.Lifts.inst h hD hn hqp ((List.length_map _).trans hl) (has.substLevels ls') hS hL
      (hπ.inst_congr _ _ _)

/-- The arguments of an instance lifted, at instantiated levels, are the arguments at these levels,
lifted by the lifting at these levels, at the same nestings and at the same parameters, of the
results at these levels. -/
theorem InstanceArgs.Lifts.substLevels {k' : Nat} {sig : Signature} {v : Lifting.Variables}
    (ls' : Fin k → Level k') :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        InstanceArgs.Lifts sig v (ρ.substLevels ls') ns (as.substLevels ls') S
          (ms.map (Lifting.Result.substLevels ls')) (as'.substLevels ls')
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
