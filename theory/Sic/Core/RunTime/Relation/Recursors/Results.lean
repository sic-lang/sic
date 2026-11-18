module

public import Sic.Core.Results
public import Sic.Core.Substitution.Rules
import Sic.Core.Lifting.Substitution
import Sic.Core.Soundness.Substitution

/-!
# Recursive Results of the Constructors Without Nested Field

The typing and the reduction give a branch of a recursor a recursive result for each recursive field
and for each field nested below a codata type, as `Results` defines them, while the usage, the
erasure and the run time still give it one for each recursive field only, by `res_C̄` and `f(D, t̄)`.
A recursor that both the typing and the usage accept has branches of both numbers of results, so
that no field of the constructors of its block is nested: the two definitions then agree, which is
what this module proves, so that the run time of the recursors reads the typing and the reduction.

The Lean keeps the two definitions until the usage and the run time read the nested fields; this
module then has no reader.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Recursive Fields Among the Nestings -/

/-- The type of the block that a field whose type has the nesting `ν` is a recursive field of: the
type that its position holds, and none for the other nestings. -/
def Nest.blockName : Nest Name → Option Name
  | .direct D => some D
  | _ => none

/-- The recursive fields of a telescope are its fields whose nestings are positions. -/
theorem Telescope.recursion_eq_map_nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      Θ.recursion names = (Θ.nest names).map Nest.blockName
  | [], .nil => rfl
  | _ :: _, .cons _ _ A Θ => by
    show A.blockName names :: Θ.recursion names =
      Nest.blockName (A.blockNest names) :: (Θ.nest names).map Nest.blockName
    rw [Telescope.recursion_eq_map_nest names Θ]
    congr 1
    cases hN : A.blockNest names with
    | direct D => exact (Term.blockNest_eq_direct A).1 hN
    | plain | inst _ =>
      cases hA : A.blockName names with
      | none => rfl
      | some D => rw [(Term.blockNest_eq_direct A).2 hA] at hN; cases hN

/-- The nestings of the entries of a telescope are as many as its entries. -/
theorem Telescope.length_nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (Θ.nest names).length = ps.length
  | [], .nil => rfl
  | _ :: _, .cons _ _ _ Θ => congrArg (· + 1) (Telescope.length_nest names Θ)

/-- The recursive fields have a recursive result among those of the fields whose nestings have a
position. -/
theorem Telescope.length_resultParams_le :
    (ns : List (Nest Name)) → (ps : List Parameter) →
      (Telescope.resultParams (ns.map Nest.blockName) ps).length ≤
        (Telescope.nestResultParams ns ps).length
  | [], _ | .plain :: _, [] | .direct _ :: _, [] | .inst _ :: _, [] => Nat.le_refl _
  | .plain :: ns, _ :: ps => Telescope.length_resultParams_le ns ps
  | .direct _ :: ns, _ :: ps => Nat.succ_le_succ (Telescope.length_resultParams_le ns ps)
  | .inst _ :: ns, _ :: ps => Nat.le_succ_of_le (Telescope.length_resultParams_le ns ps)

/-- Fields that have as many recursive results as recursive fields have no nested field. -/
theorem Telescope.not_inst_of_length_eq :
    (ns : List (Nest Name)) → (ps : List Parameter) → ns.length = ps.length →
      (Telescope.nestResultParams ns ps).length =
        (Telescope.resultParams (ns.map Nest.blockName) ps).length →
      ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms
  | [], _, _, _ => fun _ hν => nomatch hν
  | .plain :: ns, _ :: ps, hl, h => fun ν hν ms => by
    rcases List.mem_cons.1 hν with rfl | hν
    · exact fun e => nomatch e
    · exact Telescope.not_inst_of_length_eq ns ps (Nat.succ.inj hl) h ν hν ms
  | .direct _ :: ns, _ :: ps, hl, h => fun ν hν ms => by
    rcases List.mem_cons.1 hν with rfl | hν
    · exact fun e => nomatch e
    · exact Telescope.not_inst_of_length_eq ns ps (Nat.succ.inj hl) (Nat.succ.inj h) ν hν ms
  | .inst _ :: ns, _ :: ps, _, h => by
    have hle := Telescope.length_resultParams_le ns ps
    have h' : (Telescope.nestResultParams ns ps).length + 1 =
        (Telescope.resultParams (ns.map Nest.blockName) ps).length := h
    omega

/-! ## Recursive Results -/

-- ADE: none.
/-- The recursive results of fields none of which is nested are their recursive results `res_C̄`,
at motives that hold the motive of each type of the block that the lifting gives a motive. -/
theorem Terms.ResultTypes.results (names : List Name) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} →
      Terms.ResultTypes sig v ρ ns ps As xs R → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
      ∀ Cs : Motives k Δ',
        (∀ D b, ρ.block D = some b → Cs.get (names.idxOf D) = some ⟨0, b.motive⟩) →
        ∃ R', Motives.results names Cs (ns.map Nest.blockName) (ps := ps) (xs.rename ρ.ren) =
            some R' ∧
          (⟨_, R'⟩ : (ps'' : List Parameter) × Telescope k Δ' ps'') = ⟨ps', R⟩
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _ => ⟨.nil, by unfold Motives.results; rfl, rfl⟩
  | _, _, _, _, _, _, _, _, _, .plain h, hns, Cs, hCs => by
    obtain ⟨R', hR', he⟩ := h.results names (fun ν hν => hns ν (List.mem_cons_of_mem _ hν)) Cs hCs
    refine ⟨R', ?_, he⟩
    rw [Terms.rename]
    show Motives.results names Cs (none :: _) _ = _
    unfold Motives.results
    exact hR'
  | _, _, ρ, _, _, _, _, _, _, .recursive (D := D) (p := p) (x := x) (xs := xs) (b := b) hD h,
      hns, Cs, hCs => by
    obtain ⟨R', hR', he⟩ := h.results names (fun ν hν => hns ν (List.mem_cons_of_mem _ hν))
      (Cs.rename Ren.weaken) (fun D' b' hb' => by
        obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb'
        exact Motives.get_rename Ren.weaken (hCs D' b₀ hb₀))
    cases he
    refine ⟨.cons Grade.zero p (b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))) R', ?_, rfl⟩
    rw [Terms.rename]
    show Motives.results names Cs (some D :: _) _ = _
    unfold Motives.results
    have e : (xs.rename ρ.ren).rename (Ren.weaken (e := .var)) =
        xs.rename (ρ.weaken (e := .var)).ren :=
      Terms.rename_rename_of (fun _ => rfl) xs
    rw [← e] at hR'
    simp only [hCs D b hD, hR']
    rfl
  | _, _, _, _, _, _, _, _, _, .nested (ms := ms) _ _, hns, _, _ =>
    absurd rfl (hns _ List.mem_cons_self ms)

-- ADE: none.
/-- The terms `f(D, t̄)` of the recursive fields are the recursive results of the terms of fields
none of which is nested, where `f` at a type of the block and at a term is the result of this term
that the computation gives. -/
theorem Telescope.resultTerms_results {k' : Nat} {Γ : Scope} {ρ : Lifting k Γ Γ}
    {φ : Name → Term k (.var :: Γ)} (names : List Name) :
    {Ξ : Scope} → {ps : List Parameter} → (Θ' : Telescope k' Ξ ps) → (Θ : Telescope k Γ ps) →
      (ts : Args k Γ ps) → (∀ ν ∈ Θ'.nest names, ∀ ms, ν ≠ .inst ms) →
        Terms.ResultTerms sig v ρ φ (Θ'.nest names) ps (Θ.typesAt ts) ts.terms
          (ts.results (fun D t => (φ D).subst₀ (Subst₀.single t))
            ((Θ'.nest names).map Nest.blockName))
  | _, [], .nil, .nil, .nil, _ => .nil
  | _, _ :: _, .cons _ _ A Θ', .cons _ _ _ Θ, .cons t ts, h => by
    have ih := Telescope.resultTerms_results (ρ := ρ) (φ := φ) names Θ'
      (Θ.subst₀ (Subst₀.single t)) ts fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    have hA := h (A.blockNest names) List.mem_cons_self
    show Terms.ResultTerms sig v ρ φ (A.blockNest names :: Θ'.nest names) _ (.cons _ _)
      (.cons _ _)
      (Args.results _ (Nest.blockName (A.blockNest names) :: (Θ'.nest names).map Nest.blockName)
        (.cons _ ts))
    cases hN : A.blockNest names with
    | plain => exact .plain ih
    | direct D => exact .recursive ih
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
    {ps' : List Parameter}
    {R : Telescope k (Γ.extend (c.params I).length) ps'}
    (h : Constructor.ResultTypes sig v c I names ls as (Lifting.ofMotives names qs ls' gs as' l χ Cs)
      R)
    (hns : ∀ ν ∈ (c.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    ∃ R', c.results I names Cs = some R' ∧
      (⟨_, R'⟩ : (ps'' : List Parameter) × Telescope k (Γ.extend (c.params I).length) ps'') =
        ⟨ps', R⟩ := by
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
  revert R'
  rw [← Telescope.recursion_eq_map_nest]
  exact fun R' hR' he => ⟨R', hR', he⟩

-- ADE: none.
/-- The terms `f(D, t̄)` of the recursive fields of a constructor none of whose fields is nested are
the recursive results of the terms of its fields. -/
theorem Constructor.resultTerms_results (ls : Fin k' → Level k) (as : InstanceArgs k Γ Δ)
    (ρ : Lifting k Γ Γ) (φ : Name → Term k (.var :: Γ)) (ts : Args k Γ (c.params I))
    (hns : ∀ ν ∈ (c.fields I).nest names, ∀ ms, ν ≠ .inst ms) :
    Constructor.ResultTerms sig v c I names ls as ρ φ ts
      (ts.results (fun D t => (φ D).subst₀ (Subst₀.single t)) ((c.fields I).recursion names)) := by
  rw [Telescope.recursion_eq_map_nest]
  exact Telescope.resultTerms_results names (c.fields I) (c.fieldsAt I ls as) ts hns

end

end Sic.Core
