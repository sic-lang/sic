module

public import Sic.Core.Nesting
public import Sic.Core.Positivity
import Sic.Core.Positivity.Substitution
import Sic.Core.Substitution.Nesting

/-!
# Strict Positivity and Nesting

The strict positivity of annex 15 of RFC 36 relates the occurrences of a variable to the nesting of
a type: a variable whose nesting has a position does not occur in a type that is strictly positive
in it and whose nesting has no position, since the variable itself has its nesting, and an instance
of a declared type the nesting of its arguments, whatever the parameters in which the type is
declared strictly positive.
Conversely, a type whose nesting has a position, where no declared type holds one, has a variable
that occurs in it and whose nesting has a position, so that a declared type is strictly positive in
each of its parameters whose argument has a nesting with a position, in an instance that is
strictly positive in the variables whose nestings have one.

The strict positivity reads one variable, and the nesting the nestings of all the variables of the
scope: the properties hold for each variable whose nesting has a position.

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

/-- A term under new variables that is a term of the scope without a variable, under the new
variables, is a term in which this variable does not occur. -/
theorem Term.Avoids.of_liftN :
    (n : Nat) → {Γ : Scope} → {e : Scope.Entry} → {x : Var Γ e} → {B : Term k (Γ.extend n)} →
      (∃ B' : Term k ((Scope.remove Γ x).extend n), B = B'.rename (Ren.liftN n x.skip)) →
      B.Avoids (x.weakenN n)
  | 0, _, _, _, _, h => h
  | n + 1, Γ, _, x, _, h => Term.Avoids.of_liftN n (Γ := .var :: Γ) (x := .succ x) h

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

/-- The arguments of an instance in which a variable does not occur are strictly positive in
it. -/
theorem InstanceArgs.Positive.of_avoids {marks : Name → Nat → Prop} {D : Name} {Γ : Scope}
    {e : Scope.Entry} {x : Var Γ e} :
    {Δ : Scope} → {as : InstanceArgs k Γ Δ} → as.Avoids x → InstanceArgs.Positive marks D x as
  | _, _, ⟨.nil, h⟩ => by
    rw [h, InstanceArgs.rename]
    exact .nil
  | _, _, ⟨.snoc as' B', h⟩ => by
    rw [h, InstanceArgs.rename]
    exact .absent (InstanceArgs.Positive.of_avoids ⟨as', rfl⟩) (Term.Avoids.of_liftN _ ⟨B', rfl⟩)

/-- A type that is strictly positive in a variable, and that is the application of a variable to
arguments, has arguments in which the variable does not occur. -/
theorem Term.Positive.var_args {marks : Name → Nat → Prop} {Γ : Scope} {e e' : Scope.Entry}
    {y : Var Γ e'} {x : Var Γ e} {ts : Args k Γ e.params} :
    Term.Positive marks y (.var x ts) → ts.Avoids y
  | .absent h => h.var_args
  | .var h => h

/-- A type that is strictly positive in a variable, and that is an instance of a declared type, has
arguments that are strictly positive in the variable. -/
theorem Term.Positive.inst_args {marks : Name → Nat → Prop} {Γ Δ : Scope} {e : Scope.Entry}
    {x : Var Γ e} {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grading.Grade}
    {as : InstanceArgs k Γ Δ} :
    Term.Positive marks x (.inst D qs ls ps as) → InstanceArgs.Positive marks D x as
  | .inst h => h
  | .absent ⟨A', hA'⟩ => by
    cases A' with
    | inst D' qs' ls' ps' as' =>
      rw [Term.rename] at hA'
      obtain ⟨hΔ, -, -, -, -, has⟩ := Term.inst.inj hA'
      subst hΔ
      cases has
      exact .of_avoids ⟨as', rfl⟩
    | _ => simp [Term.rename] at hA'

/-! ## Types With a Position -/

/-- A variable with a position under new variables is a variable of the scope with a position. -/
theorem Nesting.exists_of_liftN :
    (n : Nat) → {Γ : Scope} → {ν : Nesting α Γ} → {e : Scope.Entry} → (z : Var (Γ.extend n) e) →
      Nesting.liftN n @ν z ≠ .plain → ∃ x : Var Γ e, z = x.weakenN n ∧ ν x ≠ .plain
  | 0, _, _, _, z, h => ⟨z, rfl, h⟩
  | n + 1, Γ, ν, _, z, h => by
    obtain ⟨y, rfl, hy⟩ :=
      Nesting.exists_of_liftN n (Γ := .var :: Γ) (ν := Nesting.lift (e := .var) @ν) z h
    cases y with
    | zero => exact absurd rfl hy
    | succ x => exact ⟨x, rfl, hy⟩

mutual

/-- A type whose nesting has a position, where no declared type holds one, has a variable that
occurs in it and whose nesting has a position. -/
theorem Term.exists_of_nest :
    {Γ : Scope} → {ν : Nesting α Γ} → (A : Term k Γ) → A.nest (fun _ => none) @ν ≠ .plain →
      ∃ (e : Scope.Entry) (x : Var Γ e), ν x ≠ .plain ∧ ¬ A.Avoids x
  | _, _, .var x ts, h => ⟨_, x, h, Term.not_avoids_var x ts⟩
  | _, ν, .inst D qs ls ps as, h => by
    have h' : (as.nest (fun _ => none) @ν).all Nest.isPlain = false := by
      cases hall : (as.nest (fun _ => none) @ν).all Nest.isPlain with
      | false => rfl
      | true =>
        refine absurd (Nest.eq_plain_of_isPlain ?_) h
        rw [Term.nest, Nest.isPlain_ofArgs]
        exact hall
    obtain ⟨e, x, hx, hfree⟩ := InstanceArgs.exists_of_nest as h'
    refine ⟨e, x, hx, fun ⟨A', hA'⟩ => hfree ?_⟩
    cases A' with
    | inst D' qs' ls' ps' as' =>
      rw [Term.rename] at hA'
      obtain ⟨hΔ, -, -, -, -, has⟩ := Term.inst.inj hA'
      subst hΔ
      cases has
      exact ⟨as', rfl⟩
    | _ => simp [Term.rename] at hA'
  | _, _, .sort _, h => absurd rfl h
  | _, _, .const _ _ _ _, h => absurd rfl h
  | _, _, .ctor _ _ _ _ _ _ _, h => absurd rfl h
  | _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _, h => absurd rfl h
  | _, _, .obs _ _ _ _ _ _ _ _, h => absurd rfl h
  | _, _, .corec _ _ _ _ _ _ _ _ _, h => absurd rfl h

/-- The arguments of an instance one of whose nestings has a position, where no declared type holds
one, have a variable that occurs in them and whose nesting has a position. -/
theorem InstanceArgs.exists_of_nest :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → (as : InstanceArgs k Γ Δ) →
      (as.nest (fun _ => none) @ν).all Nest.isPlain = false →
      ∃ (e : Scope.Entry) (x : Var Γ e), ν x ≠ .plain ∧ ¬ as.Avoids x
  | _, _, _, .nil, h => nomatch h
  | _, _, ν, .snoc as B, h => by
    rw [InstanceArgs.nest, List.all_cons] at h
    cases hB : (B.nest (fun _ => none) (Nesting.liftN _ @ν)).isPlain with
    | false =>
      obtain ⟨e, z, hz, hfree⟩ := Term.exists_of_nest B fun hp => by
        rw [hp] at hB
        exact nomatch hB
      obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z hz
      refine ⟨e, x, hx, fun ⟨as', has'⟩ => hfree ?_⟩
      cases as' with
      | snoc as'' B' =>
        rw [InstanceArgs.rename] at has'
        injection has' with _ _ _ _ hB'
        exact Term.Avoids.of_liftN _ ⟨B', hB'⟩
    | true =>
      rw [hB, Bool.true_and] at h
      obtain ⟨e, x, hx, hfree⟩ := InstanceArgs.exists_of_nest as h
      refine ⟨e, x, hx, fun ⟨as', has'⟩ => hfree ?_⟩
      cases as' with
      | snoc as'' B' =>
        rw [InstanceArgs.rename] at has'
        injection has' with _ _ _ has'' _
        exact ⟨as'', has''⟩

end

/-- A declared type is strictly positive in each of its parameters whose argument has a nesting
with a position, in an instance whose arguments are strictly positive in the variables whose
nestings have a position. -/
theorem InstanceArgs.marks_of_nest {marks : Name → Nat → Prop} {D : Name} {Γ : Scope}
    {ν : Nesting α Γ} :
    {Δ : Scope} → {as : InstanceArgs k Γ Δ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), ν x ≠ .plain → InstanceArgs.Positive marks D x as) →
      ∀ {e' : Scope.Entry} (y : Var Δ e'),
        Nesting.ofArgs (as.nest (fun _ => none) @ν) y ≠ .plain → marks D y.level
  | _, .snoc as B, h, _, .zero, hy => by
    obtain ⟨e, z, hz, hfree⟩ := Term.exists_of_nest B hy
    obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN _ z hz
    cases h e x hx with
    | positive hm _ _ => exact hm
    | absent _ hB => exact absurd hB hfree
  | _, .snoc as B, h, _, .succ y, hy =>
    InstanceArgs.marks_of_nest (as := as)
      (fun e x hx => by
        cases h e x hx with
        | positive _ has _ => exact has
        | absent has _ => exact has) y hy

end Sic.Core
