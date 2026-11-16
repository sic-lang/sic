module

public import Sic.Core.Lifting
public import Sic.Core.Positivity.Nesting
import Sic.Core.Positivity.Substitution
import Sic.Core.Syntax.Signature

/-!
# Functionality of the Liftings

In a signature whose names are distinct, a type has one lifting at most, at a term and at its
nesting, of one level: each rule reads the form of the type and its nesting, the signature has one
declaration for a name, and an argument is either lifted or kept.

An argument that is lifted at no position holds a variable lifted, so that it is not kept: the
proof shows it first, by recursion on the relation, a variable lifted being in its own application,
and an instance without position having an argument lifted, without position either.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Variables Lifted -/

/-- A variable lifted by a lifting in a scope extended by an entry is lifted by the lifting. -/
theorem Lifting.isSome_of_weaken {Γ' Γ : Scope} {e a : Scope.Entry} (ρ : Lifting k Γ' Γ)
    (x : Var Γ a) (h : ((ρ.weaken (e := e)).motive x).isSome) : (ρ.motive x).isSome := by
  rwa [show (ρ.weaken (e := e)).motive x = (ρ.motive x).map (Prod.map .succ id) from rfl,
    Option.isSome_map] at h

/-- A variable lifted by a lifting under new variables is a variable lifted by the lifting. -/
theorem Lifting.isSome_of_liftN {Γ' Γ : Scope} :
    (n : Nat) → (ρ : Lifting k Γ' Γ) → {a : Scope.Entry} → (y : Var (Γ.extend n) a) →
      ((ρ.liftN n).motive y).isSome → ∃ x : Var Γ a, y = x.weakenN n ∧ (ρ.motive x).isSome
  | 0, _, _, y, h => ⟨y, rfl, h⟩
  | n + 1, ρ, _, y, h => by
    obtain ⟨x, rfl, hx⟩ := Lifting.isSome_of_liftN n ρ.lift y h
    cases x with
    | zero => exact nomatch hx
    | succ x =>
      refine ⟨x, rfl, ?_⟩
      rwa [show (ρ.lift (e := .var)).motive (.succ x) = (ρ.motive x).map (Prod.map .succ id)
        from rfl, Option.isSome_map] at hx

/-! ## Variables That Occur in an Instance -/

/-- A variable that does not occur in an instance does not occur in its arguments. -/
theorem Term.Avoids.inst_args {Γ Δ : Scope} {e : Scope.Entry} {x : Var Γ e} {D : Name}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} :
    (Term.inst D qs ls ps as).Avoids x → as.Avoids x := by
  intro ⟨A', hA'⟩
  cases A' with
  | inst D' qs' ls' ps' as' =>
    rw [Term.rename] at hA'
    injection hA' with _ hΔ _ _ _ _ has
    subst hΔ
    exact ⟨as', eq_of_heq has⟩
  | _ => simp [Term.rename] at hA'

/-- A variable that does not occur in the arguments of an instance occurs neither in the arguments
before the last one nor in the last one, under the variables of its abstraction. -/
theorem InstanceArgs.Avoids.of_snoc {Γ Δ : Scope} {e e' : Scope.Entry} {x : Var Γ e}
    {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend e'.params.length)} :
    (InstanceArgs.snoc as B).Avoids x → as.Avoids x ∧ B.Avoids (x.weakenN e'.params.length) := by
  intro ⟨as', has'⟩
  cases as' with
  | snoc as'' B'' =>
    rw [InstanceArgs.rename] at has'
    injection has' with _ _ _ has hB
    exact ⟨⟨as'', has⟩, Term.Avoids.of_liftN _ ⟨B'', hB⟩⟩

/-! ## Arguments Lifted and Arguments Kept -/

mutual

/-- A type lifted at no position holds a variable lifted. -/
theorem Term.Lifts.not_avoidsLifted :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {l : Level k} → Term.Lifts sig v ρ n e A A' l → n = .plain →
        ¬ A.AvoidsLifted ρ
  | _, _, _, _, _, _, _, _, .var (x := x) (ts := ts) hx _, _ => fun h =>
    Term.not_avoids_var x ts (h x (hx ▸ rfl))
  | _, _, _, _, _, _, _, _, .block _ _, hn => nomatch hn
  | _, _, _, _, _, _, _, _, .inst _ _ _ _ _ _ has hS _, hn => fun h => by
    subst hn
    exact has.not_avoidsLifted rfl hS fun x hx => (h x hx).inst_args

/-- Arguments of which one at least is lifted, at no position, hold a variable lifted. -/
theorem InstanceArgs.Lifts.not_avoidsLifted :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ls : List (Level k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ls as' → ns = [] →
        S ≠ [] → ¬ ∀ {a : Scope.Entry} (x : Var Γ a), (ρ.motive x).isSome → as.Avoids x
  | _, _, _, _, _, _, _, _, _, _, .nil, _, hS => absurd rfl hS
  | _, _, ρ, _, _, _, _, _, _, _, .lifted (a := a) _ hB, hn, _ => fun h => by
    subst hn
    refine hB.not_avoidsLifted rfl fun y hy => ?_
    obtain ⟨x, rfl, hx⟩ := Lifting.isSome_of_liftN a.params.length ρ y
      (Lifting.isSome_of_weaken _ y hy)
    exact (InstanceArgs.Avoids.of_snoc (h x hx)).2
  | _, _, _, _, _, _, _, _, _, _, .absent has _ _, hn, hS => fun h => by
    subst hn
    exact has.not_avoidsLifted rfl hS fun x hx => (InstanceArgs.Avoids.of_snoc (h x hx)).1

end

/-! ## Functionality -/

mutual

-- ADE: none.
/-- A type has one lifting at most at a term and at its nesting, of one level, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\uparrow}` -/
theorem Term.Lifts.unique (hd : sig.Distinct) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A₁ A₂ : Term k Γ'} → {l₁ l₂ : Level k} → Term.Lifts sig v ρ n e A A₁ l₁ →
        Term.Lifts sig v ρ n e A A₂ l₂ → A₁ = A₂ ∧ l₁ = l₂
  | _, _, _, _, _, _, _, _, _, _, .var hx₁ _, h₂ => by
    cases h₂ with
    | var hx₂ _ =>
      cases hx₁.symm.trans hx₂
      exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, _, _, .block hD₁ _, h₂ => by
    cases h₂ with
    | block hD₂ _ =>
      cases hD₁.symm.trans hD₂
      exact ⟨rfl, rfl⟩
    | inst _ _ hn => exact absurd rfl (hn _)
  | _, _, _, _, _, _, _, _, _, _,
      .inst (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h₁ hD₁ hn₁ hq₁ hl₁ hp₁ has₁ _ _,
      h₂ => by
    generalize hA : Term.inst D qs ls ps as = A at h₂
    cases h₂ with
    | var => cases hA
    | block =>
      injection hA with _ _ hD
      subst hD
      exact absurd rfl (hn₁ _)
    | inst h₂ hD₂ _ hq₂ hl₂ hp₂ has₂ _ _ =>
      injection hA with _ _ hD hqs hls hps has
      subst hD hqs hls hps
      obtain rfl := Entry.typeDeclaration.inj (hd.entry_unique h₁ h₂ hD₁ hD₂)
      cases eq_of_heq has
      obtain ⟨rfl, rfl, has⟩ := InstanceArgs.Lifts.unique hd has₁ has₂
      cases has
      exact ⟨rfl, rfl⟩

-- ADE: none.
/-- The arguments of an instance are lifted in one way at most at their nestings: the parameters
whose arguments are lifted, the levels of these and the arguments lifted are unique, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\uparrow\bar a}` -/
theorem InstanceArgs.Lifts.unique (hd : sig.Distinct) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S₁ S₂ : List Nat} → {ls₁ ls₂ : List (Level k)} →
      {Δ₁ Δ₂ : Scope} → {as₁ : InstanceArgs k Γ' Δ₁} → {as₂ : InstanceArgs k Γ' Δ₂} →
      InstanceArgs.Lifts sig v ρ ns as S₁ ls₁ as₁ → InstanceArgs.Lifts sig v ρ ns as S₂ ls₂ as₂ →
        S₁ = S₂ ∧ ls₁ = ls₂ ∧
          (⟨Δ₁, as₁⟩ : (Δ' : Scope) × InstanceArgs k Γ' Δ') = ⟨Δ₂, as₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil, h₂ => by
    cases h₂
    exact ⟨rfl, rfl, rfl⟩
  | _, _, ρ, _, _, _, _, _, _, _, _, _, _, _, .lifted has₁ hB₁, h₂ => by
    cases h₂ with
    | lifted has₂ hB₂ =>
      obtain ⟨rfl, rfl, has⟩ := InstanceArgs.Lifts.unique hd has₁ has₂
      cases has
      obtain ⟨rfl, rfl⟩ := Term.Lifts.unique hd hB₁ hB₂
      exact ⟨rfl, rfl, rfl⟩
    | absent _ hB₂ hn =>
      exact absurd (fun y hy => hB₂ y (Lifting.isSome_of_weaken _ y hy) : Term.AvoidsLifted _ _)
        (hB₁.not_avoidsLifted hn)
  | _, _, ρ, _, _, _, _, _, _, _, _, _, _, _, .absent has₁ hB₁ hn, h₂ => by
    cases h₂ with
    | lifted _ hB₂ =>
      exact absurd (fun y hy => hB₁ y (Lifting.isSome_of_weaken _ y hy) : Term.AvoidsLifted _ _)
        (hB₂.not_avoidsLifted hn)
    | absent has₂ _ _ =>
      obtain ⟨rfl, rfl, has⟩ := InstanceArgs.Lifts.unique hd has₁ has₂
      cases has
      exact ⟨rfl, rfl, rfl⟩

end

/-! ## Declarations of Liftings -/

/-- The destructors of the lifting of a type at parameters are those of its declaration. -/
theorem TypeDeclaration.lifting_destructors {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns₁ ns₂ : List Name}
    {body₁ : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns₁}
    {body₂ : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns₂}
    (h : decl.lifting F S ns₁ body₁ = decl.lifting F S ns₂ body₂) : ns₁ = ns₂ := by
  have h' : [ns₁] = [ns₂] :=
    congrArg (fun d : TypeDeclaration => d.codataTypes.map CodataType.destructors) h
  exact (List.cons.inj h').1

/-- The destructors of the lifting of a type at parameters, at each instance, are those of its
declaration. -/
theorem TypeDeclaration.lifting_body {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns : List Name}
    {body₁ body₂ : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (h : decl.lifting F S ns body₁ = decl.lifting F S ns body₂) : body₁ = body₂ := by
  unfold TypeDeclaration.lifting at h
  injection h with _ _ _ _ _ _ _ hb
  injection hb with hb
  injection hb with hb
  injection hb with _ _ _ _ hb

end Sic.Core
