module

public import Sic.Core.Nesting
public import Sic.Core.Positivity
import Sic.Core.Substitution.Nesting

/-!
# Strict Positivity and Nesting

The strict positivity of annex 14 of RFC 36 relates the occurrences of a variable to the nesting of
a type: a variable whose nesting has a position does not occur in a type that is strictly positive
in it and whose nesting has no position, since the variable itself has its nesting, and an instance
of a declared type the nesting of its arguments, whatever the parameters in which the type is
declared strictly positive.

The strict positivity reads one variable, and the nesting the nestings of all the variables of the
scope: the property holds for each variable whose nesting has a position.

ADE have no declared types, and neither strict positivity nor nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α : Type}

/-! ## Variables That Do Not Occur in the Arguments of an Instance -/

/-- The variable `x` does not occur in the arguments `ā` of an instance, which are arguments of the
scope without `x`. -/
def InstanceArgs.Avoids {Γ Δ : Scope} {e : Scope.Entry} (as : InstanceArgs k Γ Δ) (x : Var Γ e) :
    Prop :=
  ∃ as' : InstanceArgs k (Scope.remove Γ x) Δ, as = as'.rename x.skip

/-- A term under new variables in which a variable of the scope does not occur is a term of the
scope without it, under the new variables. -/
theorem Term.Avoids.liftN :
    (n : Nat) → {Γ : Scope} → {e : Scope.Entry} → {x : Var Γ e} → {B : Term k (Γ.extend n)} →
      B.Avoids (x.weakenN n) →
      ∃ B' : Term k ((Scope.remove Γ x).extend n), B = B'.rename (Ren.liftN n x.skip)
  | 0, _, _, _, _, h => h
  | n + 1, Γ, _, x, _, h => Term.Avoids.liftN n (Γ := .var :: Γ) (x := .succ x) h

/-- A variable does not occur in the arguments of an instance when it occurs neither in the
arguments before the last one nor in the last one, under the variables of its abstraction. -/
theorem InstanceArgs.Avoids.snoc {Γ Δ : Scope} {e e' : Scope.Entry} {x : Var Γ e}
    {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend e'.params.length)} (has : as.Avoids x)
    (hB : B.Avoids (x.weakenN e'.params.length)) : (InstanceArgs.snoc as B).Avoids x := by
  obtain ⟨as', rfl⟩ := has
  obtain ⟨B', rfl⟩ := Term.Avoids.liftN _ hB
  exact ⟨.snoc as' B', by rw [InstanceArgs.rename]⟩

/-! ## Types Without Position -/

/-- A nesting that is no position is `⊥`. -/
theorem Nest.eq_plain_of_isPlain {n : Nest α} (h : n.isPlain = true) : n = .plain := by
  cases n <;> first | rfl | exact nomatch h

/-- The arguments of an instance whose nesting has no position have none. -/
theorem Nest.all_isPlain_of_ofArgs {ns : List (Nest α)} (h : Nest.ofArgs ns = .plain) :
    ns.all Nest.isPlain = true := by
  unfold Nest.ofArgs at h
  split at h
  · assumption
  · exact nomatch h

mutual

/-- A variable whose nesting has a position does not occur in a type that is strictly positive in
it and whose nesting has no position. -/
theorem Term.Positive.avoids {marks : Name → Nat → Prop} {mark : Name → Option α} {Γ : Scope}
    {e : Scope.Entry} {x : Var Γ e} {ν : Nesting α Γ} (hν : ν x ≠ .plain) {A : Term k Γ} :
    Term.Positive marks x A → A.nest mark @ν = .plain → A.Avoids x
  | .absent h, _ => h
  | .var _, hA => by
    rw [Term.nest] at hA
    exact absurd hA hν
  | .inst (D := D) (qs := qs) (ls := ls) (ps := ps) h, hA => by
    rw [Term.nest] at hA
    split at hA
    · exact nomatch hA
    · obtain ⟨as', rfl⟩ := InstanceArgs.Positive.avoids hν h (Nest.all_isPlain_of_ofArgs hA)
      exact ⟨.inst D qs ls ps as', by rw [Term.rename]⟩
termination_by structural h _ => h

/-- A variable whose nesting has a position does not occur in the arguments of an instance that are
strictly positive in it and none of whose nestings has a position. -/
theorem InstanceArgs.Positive.avoids {marks : Name → Nat → Prop} {mark : Name → Option α}
    {D : Name} {Γ Δ : Scope} {e : Scope.Entry} {x : Var Γ e} {ν : Nesting α Γ}
    (hν : ν x ≠ .plain) {as : InstanceArgs k Γ Δ} :
    InstanceArgs.Positive marks D x as → (as.nest mark @ν).all Nest.isPlain = true → as.Avoids x
  | .nil, _ => ⟨.nil, by rw [InstanceArgs.rename]⟩
  | .positive _ has hB, h => by
    rw [InstanceArgs.nest, List.all_cons, Bool.and_eq_true] at h
    exact (InstanceArgs.Positive.avoids hν has h.2).snoc
      (Term.Positive.avoids (ν := Nesting.liftN _ @ν) (by rwa [Nesting.liftN_weakenN]) hB
        (Nest.eq_plain_of_isPlain h.1))
  | .absent has hB, h => by
    rw [InstanceArgs.nest, List.all_cons, Bool.and_eq_true] at h
    exact (InstanceArgs.Positive.avoids hν has h.2).snoc hB
termination_by structural h _ => h

end

end Sic.Core
