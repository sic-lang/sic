module

import Sic.Core.Substitution
import all Sic.Core.Syntax.Validation

/-!
# Validation of the Substitution

The definitions of `Sic.Core.Substitution` checked against RFC 24, on the examples of the
literature, and against their meaning.
-/

namespace Sic.Core.Substitution.Validation

open Grade Syntax.Validation Term

/-! The claims and examples of RFC 24. -/

/--
`B[a/x]` renames the bound variables of `B` that `a` would capture: in the context `x : U₀`,
`(Π^𝟘_𝟙 (x : A). A)[x/A]` is `Π^𝟘_𝟙 (y : x). x`, whose bound variable `var 0` differs from the
free `x`, which is `var 1` under the binder.
-/
example : (pi 𝟙 𝟘 (var 0) (var 1) : Term 0 2).instantiate (var 0) = pi 𝟙 𝟘 (var 0) (var 1) := rfl

/--
The rule `(β)` applies the constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` to `a`:
`(λ_𝟘 (y : B). x)[a/x]` is `λ_𝟘 (y : B). a`, where `a` is moved under the binder of `y`.
-/
example (a : Term 0 2) : (lam 𝟘 (var 1) (var 1)).instantiate a = lam 𝟘 (var 0) a.wk1 := rfl

/-- The polymorphic identity, over the level variable `l`, instantiated at the level `0`. -/
example : identityType.substLevels (fun _ => (.zero : Level 0)) =
    pi 𝟘 (𝟙 + 𝟙) (univ .zero) (pi 𝟙 𝟘 (var 0) (var 1)) := rfl

/-! The examples of the literature. -/

/--
The type of `K` at the type `Nat_l`: `(Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A)[Nat_l/A]` is
`Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : Nat_l). Π^𝟘_𝟘 (y : B). Nat_l`, where the closed `Nat_l` moves under the
binders unchanged.
-/
example : (pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 (var 1) (pi 𝟘 𝟘 (var 1) (var 3))) : Term 1 1).instantiate
    churchNat = pi 𝟘 𝟙 (univ (.var 0)) (pi 𝟙 𝟘 churchNat (pi 𝟘 𝟘 (var 1) churchNat)) := rfl

/--
The step `succ ∘_𝟙 1` of the Church numerals replaces `m` by `1` under the binders of `X`, `f` and
`x`: the body of `succ` becomes `λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X).
f ∘_𝟙 (1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)`.
-/
example : (lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1)
      (app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 (var 3) (var 2)) (var 1)) (var 0))))) :
      Term 1 1).instantiate churchOne =
    lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1)
      (app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchOne (var 2)) (var 1)) (var 0))))) := rfl

/-! The laws that the reductions of the examples use. -/

/--
Instantiating the variable of a body under a substitution is substituting it with the substitution
extended by the argument, as `(β)` does when it applies an abstraction that a substitution moved.
-/
theorem subst_lift_instantiate (σ : Subst k m n) (t : Term k (n + 1)) (a : Term k m) :
    (t.subst σ.lift).instantiate a = t.subst (σ.cons a) := by
  rw [instantiate, subst_subst]
  congr 1
  funext x
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨x + 1, _⟩ =>
    show (Term.wk1 _).subst _ = _
    rw [subst_cons_wk1, subst_var]
    rfl

/-- A term that does not use the variable `x` is unchanged by `t[a/x]`. -/
theorem instantiate_wk1 (t : Term k n) (a : Term k n) : t.wk1.instantiate a = t :=
  (subst_wk _ _ t).trans (subst_var t)

/-!
The meaning of the weakenings: a weakening keeps the variables of the smaller context in the same
order, so it denotes a strictly increasing map between the indices, and every such map is the
meaning of a weakening.
Several weakenings may denote the same map, as `id` and `lift id` do.
-/

/-- The map `f` between indices is strictly increasing. -/
def StrictMono (f : Fin n → Fin m) : Prop := ∀ x y, x < y → f x < f y

theorem var_strictMono : ∀ ρ : Wk m n, StrictMono ρ.var
  | .id, _, _, h => h
  | .step ρ, x, y, h => Nat.succ_lt_succ (var_strictMono ρ x y h)
  | .lift _, ⟨0, _⟩, ⟨0, _⟩, h => absurd h (Nat.lt_irrefl 0)
  | .lift _, ⟨0, _⟩, ⟨_ + 1, _⟩, _ => Nat.succ_pos _
  | .lift _, ⟨_ + 1, _⟩, ⟨0, _⟩, h => absurd h (Nat.not_lt_zero _)
  | .lift ρ, ⟨_ + 1, _⟩, ⟨_ + 1, _⟩, h =>
    Nat.succ_lt_succ (var_strictMono ρ _ _ (Nat.lt_of_succ_lt_succ h))

/-!
How completeness is proved, by induction on the size `m` of the larger context: if the map sends
the innermost variable `0` to `0`, it is a `lift` of the map on the other variables, shifted down
by one, and otherwise none of its values is `0`, so it is a `step` of the map shifted down by one.
-/

theorem exists_wk : ∀ {m n : Nat} (f : Fin n → Fin m), StrictMono f → ∃ ρ : Wk m n, ρ.var = f
  | 0, 0, f, _ => ⟨.id, funext (·.elim0)⟩
  | 0, _ + 1, f, _ => (f 0).elim0
  | m + 1, n, f, hf => by
    by_cases h0 : ∃ h : 0 < n, (f ⟨0, h⟩).val = 0
    · obtain ⟨hn, h0⟩ := h0
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have pos : ∀ x : Fin n, 0 < (f x.succ).val := fun x =>
        h0 ▸ hf ⟨0, hn⟩ x.succ (Nat.succ_pos _)
      let g : Fin n → Fin m := fun x =>
        ⟨(f x.succ).val - 1, by have := (f x.succ).isLt; have := pos x; omega⟩
      have hg : StrictMono g := fun x y h => by
        have := hf x.succ y.succ (Nat.succ_lt_succ h); have := pos x
        show (f x.succ).val - 1 < (f y.succ).val - 1; omega
      obtain ⟨ρ, hρ⟩ := exists_wk g hg
      refine ⟨.lift ρ, funext fun x => Fin.ext ?_⟩
      match x with
      | ⟨0, _⟩ => exact h0.symm
      | ⟨x + 1, hx⟩ =>
        let y : Fin n := ⟨x, Nat.lt_of_succ_lt_succ hx⟩
        have := pos y
        show (ρ.var y).val + 1 = (f y.succ).val
        rw [hρ]
        show (f y.succ).val - 1 + 1 = _
        omega
    · have pos : ∀ x, 0 < (f x).val := fun x => by
        have := x.isLt
        have : ¬(f ⟨0, by omega⟩).val = 0 := fun h => h0 ⟨by omega, h⟩
        rcases Nat.eq_zero_or_pos x.val with hx | hx
        · rw [show x = ⟨0, by omega⟩ from Fin.ext hx]; omega
        · have := hf ⟨0, by omega⟩ x hx; omega
      let g : Fin n → Fin m := fun x =>
        ⟨(f x).val - 1, by have := (f x).isLt; have := pos x; omega⟩
      have hg : StrictMono g := fun x y h => by
        have := hf x y h; have := pos x
        show (f x).val - 1 < (f y).val - 1; omega
      obtain ⟨ρ, hρ⟩ := exists_wk g hg
      refine ⟨.step ρ, funext fun x => Fin.ext ?_⟩
      show (ρ.var x).val + 1 = _
      rw [hρ]; have := pos x
      show (f x).val - 1 + 1 = _; omega

/-- The weakenings denote exactly the strictly increasing maps between indices. -/
theorem strictMono_iff_wk (f : Fin n → Fin m) : StrictMono f ↔ ∃ ρ : Wk m n, ρ.var = f :=
  ⟨exists_wk f, fun ⟨ρ, h⟩ => h ▸ var_strictMono ρ⟩

end Sic.Core.Substitution.Validation
