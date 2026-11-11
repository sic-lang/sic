module

public import Sic.Core.Syntax

/-!
# Properties of the Terms

Properties of the terms of annex 08 of RFC 36: the terms of the arguments determine them, the
recursive occurrences of the types of a block in a telescope, the positions of the branches and of
the states, and the lengths of the scopes extended.

ADE have no telescopes, no blocks and no second-order variables.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Terms -/

/-- Arguments with the same terms are the same arguments. -/
theorem Args.terms_inj {k : Nat} {Γ : Scope} :
    {ps : List Parameter} → {ts us : Args k Γ ps} → ts.terms = us.terms → ts = us
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
    simp only [Args.terms, Terms.cons.injEq] at h
    obtain ⟨rfl, h₂⟩ := h
    rw [Args.terms_inj h₂]

/-- Fields without recursive fields have no recursive results. -/
theorem Telescope.resultParams_of_none : {rs : List (Option Name)} → {ps : List Parameter} →
    (∀ R ∈ rs, R = none) → Telescope.resultParams rs ps = []
  | [], _, _ | some _ :: _, [], _ | none :: _, [], _ => rfl
  | some _ :: _, _ :: _, h => by cases h _ List.mem_cons_self
  | none :: rs, _ :: ps, h =>
    Telescope.resultParams_of_none (rs := rs) (ps := ps) fun R hR => h R (List.mem_cons_of_mem _ hR)

/-- The type that the type of a recursive field is an instance of is a type of the block. -/
theorem Term.blockName_mem {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {A : Term k Γ} → A.blockName names = some D → D ∈ names
  | .inst D' _ _ _ _, h => by
    by_cases hm : D' ∈ names
    · simp only [Term.blockName, hm, ↓reduceIte, Option.some.injEq] at h
      exact h ▸ hm
    · simp only [Term.blockName, hm, ↓reduceIte, reduceCtorEq] at h
  | .var .., h | .sort _, h | .const .., h | .ctor .., h | .recursor .., h | .obs .., h
  | .corec .., h => by cases h

/-- The type of a recursive field of a telescope is a type of the block. -/
theorem Telescope.recursionAt_mem {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → {Θ : Telescope k Γ ps} → {i : Nat} → Θ.recursionAt names i = some D →
      D ∈ names
  | [], .nil, _, h => by simp [Telescope.recursionAt, Telescope.recursion] at h
  | _ :: _, .cons _ _ A _, 0, h => Term.blockName_mem (by simpa [Telescope.recursionAt,
      Telescope.recursion] using h)
  | _ :: _, .cons _ _ _ Θ, i + 1, h => Telescope.recursionAt_mem (Θ := Θ) (i := i)
      (by simpa [Telescope.recursionAt, Telescope.recursion] using h)

/-- A telescope has a type of the block or none for each of its entries. -/
theorem Telescope.length_recursion {k : Nat} {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (Θ.recursion names).length = ps.length
  | [], .nil => rfl
  | _ :: _, .cons _ _ _ Θ => congrArg (· + 1) (Telescope.length_recursion names Θ)

/-- The types of the recursive fields of a telescope are types of the block. -/
theorem Telescope.mem_recursion {k : Nat} {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → {Θ : Telescope k Γ ps} → some D ∈ Θ.recursion names → D ∈ names
  | [], .nil, h => nomatch h
  | _ :: _, .cons _ _ A Θ, h => by
    rcases List.mem_cons.1 h with h | h
    · exact Term.blockName_mem h.symm
    · exact Telescope.mem_recursion h

/-- The branch at a position of branches is one term. -/
theorem Branches.get_inj {k : Nat} {Γ : Scope} {us : Branches k Γ} {i n m : Nat}
    {u₁ u₂ : Term k ((Γ.extend n).extend m)} (h₁ : us.get i = some ⟨n, m, u₁⟩)
    (h₂ : us.get i = some ⟨n, m, u₂⟩) : u₁ = u₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- The branch at a position of the branches of a corecursor is one term. -/
theorem CorecBranches.get_inj {k : Nat} {Γ : Scope} {vs : CorecBranches k Γ} {i n m a : Nat}
    {v₁ v₂ : Term k (((Γ.extend n).extend m).extend a)} (h₁ : vs.get i = some ⟨n, m, a, v₁⟩)
    (h₂ : vs.get i = some ⟨n, m, a, v₂⟩) : v₁ = v₂ := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-! ## Scopes -/

/-- The length of the scope `Γ` extended by `a` variables. -/
theorem Scope.length_extend (Γ : Scope) : (a : Nat) → (Γ.extend a).length = Γ.length + a
  | 0 => rfl
  | a + 1 => (Scope.length_extend (.var :: Γ) a).trans (Nat.succ_add _ _)

/-- The length of the scope `Γ` extended by `a`, then `b` variables, as the scope of a branch of a
recursor is. -/
theorem Scope.length_extend_extend (Γ : Scope) (a b : Nat) :
    ((Γ.extend a).extend b).length = Γ.length + (a + b) := by
  rw [Scope.length_extend, Scope.length_extend]
  omega

/-- The length of the scope `Γ` extended by `a`, then `b`, then `c` variables, as the scope of a
branch of a corecursor is. -/
theorem Scope.length_extend_extend_extend (Γ : Scope) (a b c : Nat) :
    (((Γ.extend a).extend b).extend c).length = Γ.length + (a + b + c) := by
  rw [Scope.length_extend, Scope.length_extend, Scope.length_extend]
  omega

end Sic.Core
