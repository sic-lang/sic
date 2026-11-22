module

public import Sic.Core.Lifting
public import Sic.Core.Positivity.Nesting
import Sic.Core.Lifting.Substitution
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

The factors are functions of the result of a destructor of a lifting too, in such a signature: an
instance of a lifting reads one list of destructors, whose factors are unique by induction.
Without block, the factor that the lifting of a type gives is the factor of this type lifted: the
motive of a variable lifted reads its factor from the lifting of the scope, and the lifting of an
instance takes its factor as a premise.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables}

/-! ## Declarations of Liftings -/

/-- The destructors of the lifting of a type at parameters are those of its declaration. -/
theorem TypeDeclaration.lifting_destructors {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns₁ ns₂ : List Name}
    {body₁ : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns₁}
    {body₂ : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns₂}
    (h : decl.lifting F S ns₁ body₁ = decl.lifting F S ns₂ body₂) : ns₁ = ns₂ := by
  have h' : [ns₁] = [ns₂] :=
    congrArg (fun d : TypeDeclaration => d.codataTypes.map CodataType.destructors) h
  exact (List.cons.inj h').1

/-- The destructors of the lifting of a type at parameters, at each instance, are those of its
declaration. -/
theorem TypeDeclaration.lifting_body {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns : List Name}
    {body₁ body₂ : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (h : decl.lifting F S ns body₁ = decl.lifting F S ns body₂) : body₁ = body₂ := by
  unfold TypeDeclaration.lifting at h
  injection h with _ _ _ _ _ _ _ hb
  injection hb with hb
  injection hb with hb
  injection hb with _ _ _ _ hb

/-! ## Factors -/

/-- Two variables of a scope that are the same variable have the same level, whatever proof of the
equality of their entries is given. -/
theorem Var.level_heq {Γ : Scope} {e e' : Scope.Entry} {x : Var Γ e} {y : Var Γ e'} (h : e = e')
    (hxy : HEq x y) : x.level = y.level := by
  subst h
  cases hxy
  rfl

/-- The lifting `ρ` gives distinct variables lifted distinct motives, or the same result: two
variables lifted whose motives have the same level have the same result.
The RFC names the motive of each parameter, so that distinct parameters have distinct motives; with
de Bruijn indices, the factor of a motive, which reads the variable of the motive, needs it. -/
def Lifting.DistinctMotives {Γ' Γ : Scope} (ρ : Lifting k Γ' Γ) : Prop :=
  ∀ ⦃a b : Scope.Entry⦄ ⦃x : Var Γ a⦄ ⦃x' : Var Γ b⦄ ⦃y : Var Γ' a.motive⦄
    ⦃y' : Var Γ' b.motive⦄ ⦃m m' : Lifting.Result k⦄,
    ρ.motive x = some (y, m) → ρ.motive x' = some (y', m') → y.level = y'.level → m = m'

/-- The lifting `ρ` under a new entry of both scopes gives distinct variables distinct motives when
`ρ` does. -/
theorem Lifting.DistinctMotives.lift {Γ' Γ : Scope} {e : Scope.Entry} {ρ : Lifting k Γ' Γ}
    (h : ρ.DistinctMotives) : (ρ.lift (e := e)).DistinctMotives := by
  intro a b x x' y y' m m' hx hx' hl
  cases x with
  | zero => cases hx
  | succ x =>
    cases x' with
    | zero => cases hx'
    | succ x' =>
      obtain ⟨⟨z, n⟩, hz, he⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨⟨z', n'⟩, hz', he'⟩ := Option.map_eq_some_iff.1 hx'
      cases he
      cases he'
      exact h hz hz' hl

/-- The lifting `ρ` in a scope extended by a new entry gives distinct variables distinct motives
when `ρ` does. -/
theorem Lifting.DistinctMotives.weaken {Γ' Γ : Scope} {e : Scope.Entry} {ρ : Lifting k Γ' Γ}
    (h : ρ.DistinctMotives) : (ρ.weaken (e := e)).DistinctMotives := by
  intro a b x x' y y' m m' hx hx' hl
  obtain ⟨⟨z, n⟩, hz, he⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨⟨z', n'⟩, hz', he'⟩ := Option.map_eq_some_iff.1 hx'
  cases he
  cases he'
  exact h hz hz' hl

/-- The lifting `ρ` under new variables of both scopes gives distinct variables distinct motives
when `ρ` does. -/
theorem Lifting.DistinctMotives.liftN {Γ' Γ : Scope} :
    (n : Nat) → {ρ : Lifting k Γ' Γ} → ρ.DistinctMotives → (ρ.liftN n).DistinctMotives
  | 0, _, h => h
  | n + 1, _, h => Lifting.DistinctMotives.liftN n h.lift

/-- The lifting `ρ` extended by a parameter, lifted or not, gives distinct variables distinct
motives when `ρ` does. -/
theorem Lifting.DistinctMotives.cons {Δ' Δ : Scope} {e : Scope.Entry} {ρ : Lifting k Δ' Δ}
    (m : Lifting.Result k) (h : ρ.DistinctMotives) :
    (b : Bool) → (Lifting.cons (e := e) m b ρ).DistinctMotives
  | false => h.lift
  | true => by
    intro a b x x' y y' n n' hx hx' hl
    cases x with
    | zero =>
      cases x' with
      | zero =>
        cases hx
        cases hx'
        rfl
      | succ x' =>
        obtain ⟨⟨z', _⟩, -, he'⟩ := Option.map_eq_some_iff.1 hx'
        cases hx
        cases he'
        exact absurd hl (Nat.ne_of_gt (Nat.lt_of_lt_of_le z'.level_lt (Nat.le_succ _)))
    | succ x =>
      cases x' with
      | zero =>
        obtain ⟨⟨z, _⟩, -, he⟩ := Option.map_eq_some_iff.1 hx
        cases hx'
        cases he
        exact absurd hl (Nat.ne_of_lt (Nat.lt_of_lt_of_le z.level_lt (Nat.le_succ _)))
      | succ x' =>
        obtain ⟨⟨z, _⟩, hz, he⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨⟨z', _⟩, hz', he'⟩ := Option.map_eq_some_iff.1 hx'
        cases he
        cases he'
        exact h hz hz' hl

/-- The lifting of the parameters of a type declaration in their scope lifted gives distinct
parameters distinct motives. -/
theorem Lifting.base_distinctMotives (S : List Nat) (mv : Nat → Lifting.Result k) :
    (Δ : Scope) → (Lifting.base S mv Δ).DistinctMotives
  | [] => fun _ _ x => nomatch x
  | _ :: Δ => (Lifting.base_distinctMotives S mv Δ).cons _ _

/-- The lifting of the scope of a type declaration in the scope of the parameters of its lifting
gives distinct parameters distinct motives. -/
theorem TypeDeclaration.liftingScope_distinctMotives (decl : TypeDeclaration) (S : List Nat)
    (I : Instance (decl.sorts + 1) (decl.liftingGrades S)) :
    (decl.liftingScope S I).DistinctMotives :=
  (Lifting.base_distinctMotives S _ decl.scope).lift

/-- The name of the lifting of a type at parameters is a name of its declaration. -/
theorem TypeDeclaration.name_mem_lifting_names {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns} :
    Lifting.name F S ∈ Entry.names (.typeDeclaration (decl.lifting F S ns body)) := by
  simp [Entry.names, TypeDeclaration.lifting, TypeDeclaration.names]

mutual

/-- The result of a destructor of a lifting has one factor at most, in a signature whose names are
distinct, where `ρ` gives distinct variables distinct motives.
RFC: `\mathsf{unique}_{\mathsf{factor}}` -/
theorem Term.Factor.unique (hd : sig.Distinct) :
    {k : Nat} → {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → ρ.DistinctMotives → {B : Term k Γ'} →
      {π₁ π₂ : Grade} → Term.Factor sig ρ B π₁ → Term.Factor sig ρ B π₂ → π₁ = π₂
  | _, _, _, _, hρ, _, _, _, .var hx₁ ts₁, h₂ => by
    generalize hB : Term.var _ ts₁ = B at h₂
    cases h₂ with
    | var hx₂ _ =>
      injection hB with _ he hy
      exact congrArg Lifting.Result.factor (hρ hx₁ hx₂ (Var.level_heq he hy))
    | inst => cases hB
  | _, _, _, _, _, _, _, _, .inst hdecl₁ hD₁ h₁ hq hp hds₁, .inst hdecl₂ hD₂ h₂ _ _ hds₂ => by
    obtain rfl := Entry.typeDeclaration.inj (hd.entry_unique hdecl₁ hdecl₂ hD₁ hD₂)
    have he := Entry.typeDeclaration.inj
      (hd.entry_unique h₁ h₂ TypeDeclaration.name_mem_lifting_names
        TypeDeclaration.name_mem_lifting_names)
    obtain rfl := TypeDeclaration.lifting_destructors he
    obtain rfl := TypeDeclaration.lifting_body he
    rw [Destructors.Factor.unique hd (TypeDeclaration.liftingScope_distinctMotives _ _ _) hds₁ hds₂]

/-- Destructors have one meet at most, in a signature whose names are distinct, where `ρ` gives
distinct variables distinct motives. -/
theorem Destructors.Factor.unique (hd : sig.Distinct) :
    {k : Nat} → {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → ρ.DistinctMotives → {ns : List Name} →
      {ds : Destructors k Γ' ns} → {π₁ π₂ : Option Grade} → Destructors.Factor sig ρ ds π₁ →
        Destructors.Factor sig ρ ds π₂ → π₁ = π₂
  | _, _, _, _, _, _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, hρ, _, _, _, _, .cons hB₁ hds₁, .cons hB₂ hds₂ => by
    rw [Term.Factor.unique hd (hρ.liftN _) hB₁ hB₂, Destructors.Factor.unique hd hρ.weaken hds₁ hds₂]

end

/-- An instance of a lifting has one factor at most, in a signature whose names are distinct,
whatever the liftings of the scope. -/
theorem Term.Factor.unique_inst (hd : sig.Distinct) {Γ₁ Γ₂ Γ' Δ : Scope}
    {ρ₁ : Lifting k Γ' Γ₁} {ρ₂ : Lifting k Γ' Γ₂} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ' Δ} {π₁ π₂ : Grade}
    (h₁ : Term.Factor sig ρ₁ (.inst D qs ls ps as) π₁)
    (h₂ : Term.Factor sig ρ₂ (.inst D qs ls ps as) π₂) : π₁ = π₂ :=
  Term.Factor.unique hd (ρ := { ρ₁ with motive := fun _ => none }) (fun _ _ _ _ _ _ _ _ hx => nomatch hx)
    (h₁.inst_congr _ ls as) (h₂.inst_congr _ ls as)

/-- In a lifting without block, the factor of the recursive result that a type lifted is the type
of is the factor of this type lifted, so that the lifting of a destructor reads it from the lifting
of its result. -/
theorem Term.Lifts.factor {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} (hρ : ∀ D, ρ.block D = none)
    {n : Nest Name} {e : Term k Γ'} {A : Term k Γ} {A' : Term k Γ'} {m : Lifting.Result k}
    (h : Term.Lifts sig v ρ n e A A' m) : Term.Factor sig ρ A' m.factor := by
  cases h with
  | var hx _ => exact .var hx _
  | block hD => cases (hρ _).symm.trans hD
  | inst _ _ _ _ _ _ _ _ _ hπ => exact hπ

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

/-- A variable lifted by a lifting is lifted by the lifting under new variables. -/
theorem Lifting.isSome_liftN_weakenN {Γ' Γ : Scope} :
    (n : Nat) → (ρ : Lifting k Γ' Γ) → {a : Scope.Entry} → (x : Var Γ a) →
      (ρ.motive x).isSome → ((ρ.liftN n).motive (x.weakenN n)).isSome
  | 0, _, _, _, h => h
  | n + 1, ρ, _, x, h =>
    Lifting.isSome_liftN_weakenN n ρ.lift x.succ (by
      rwa [show (ρ.lift (e := .var)).motive (.succ x) = (ρ.motive x).map (Prod.map .succ id)
        from rfl, Option.isSome_map])

/-- A lifting that lifts no variable lifts none under new variables. -/
theorem Lifting.liftN_motive_eq_none {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (n : Nat) :
    ∀ {a} (y : Var (Γ.extend n) a), (ρ.liftN n).motive y = none := fun y => by
  cases h : (ρ.liftN n).motive y with
  | none => rfl
  | some p =>
    obtain ⟨x, -, hx⟩ := Lifting.isSome_of_liftN n ρ y (by rw [h]; rfl)
    rw [hρ x] at hx
    exact nomatch hx

/-- A lifting that lifts no variable lifts none in a scope extended by a new entry. -/
theorem Lifting.weaken_motive_eq_none {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry} :
    ∀ {a} (x : Var Γ a), (ρ.weaken (e := e)).motive x = none := fun x => by
  show (ρ.motive x).map _ = none
  rw [hρ x]
  rfl

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
      {A' : Term k Γ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m → n = .plain →
        ¬ A.AvoidsLifted ρ
  | _, _, _, _, _, _, _, _, .var (x := x) (ts := ts) hx _, _ => fun h =>
    Term.not_avoids_var x ts (h x (hx ▸ rfl))
  | _, _, _, _, _, _, _, _, .block _, hn => nomatch hn
  | _, _, _, _, _, _, _, _, .inst _ _ _ _ _ _ has hS _ _, hn => fun h => by
    subst hn
    exact has.not_avoidsLifted rfl hS fun x hx => (h x hx).inst_args

/-- Arguments of which one at least is lifted, at no position, hold a variable lifted. -/
theorem InstanceArgs.Lifts.not_avoidsLifted :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' → ns = [] →
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

/-! ## Liftings That Lift No Variable -/

/-- No variable of a type is lifted by a lifting that lifts none, under new variables and in a scope
extended by an entry. -/
theorem Term.avoidsLifted_of_none {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (n : Nat) {e : Scope.Entry}
    (B : Term k (Γ.extend n)) : B.AvoidsLifted ((ρ.liftN n).weaken (e := e)) := fun y hy => by
  obtain ⟨x, -, hx⟩ := Lifting.isSome_of_liftN n ρ y (Lifting.isSome_of_weaken _ y hy)
  rw [hρ x] at hx
  exact nomatch hx

/-- Liftings that lift no variable lift the same arguments of two instances of a declared type, at
the same nestings: those whose nesting has a position. -/
theorem InstanceArgs.Lifts.positions_eq {Γ₁' Γ₁ Γ₂' Γ₂ : Scope} {ρ₁ : Lifting k Γ₁' Γ₁}
    {ρ₂ : Lifting k Γ₂' Γ₂} (hρ₁ : ∀ {a} (x : Var Γ₁ a), ρ₁.motive x = none)
    (hρ₂ : ∀ {a} (x : Var Γ₂ a), ρ₂.motive x = none) :
    {ns : List (Nest Name)} → {Δ : Scope} → {as₁ : InstanceArgs k Γ₁ Δ} →
      {as₂ : InstanceArgs k Γ₂ Δ} → {S₁ S₂ : List Nat} → {ms₁ ms₂ : List (Lifting.Result k)} →
      {Δ₁' Δ₂' : Scope} → {as₁' : InstanceArgs k Γ₁' Δ₁'} → {as₂' : InstanceArgs k Γ₂' Δ₂'} →
      InstanceArgs.Lifts sig v ρ₁ ns as₁ S₁ ms₁ as₁' →
        InstanceArgs.Lifts sig v ρ₂ ns as₂ S₂ ms₂ as₂' → S₁ = S₂
  | _, _, _, _, _, _, _, _, _, _, _, _, .nil, h₂ => by
    cases h₂
    rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, .lifted has₁ hB₁, h₂ => by
    cases h₂ with
    | lifted has₂ _ => rw [InstanceArgs.Lifts.positions_eq hρ₁ hρ₂ has₁ has₂]
    | absent _ _ hn =>
      exact (hB₁.not_avoidsLifted hn (Term.avoidsLifted_of_none hρ₁ _ _)).elim
  | _, _, _, _, _, _, _, _, _, _, _, _, .absent has₁ _ hn, h₂ => by
    cases h₂ with
    | lifted _ hB₂ =>
      exact (hB₂.not_avoidsLifted hn (Term.avoidsLifted_of_none hρ₂ _ _)).elim
    | absent has₂ _ _ => exact InstanceArgs.Lifts.positions_eq hρ₁ hρ₂ has₁ has₂

/-! ## Functionality -/

mutual

/-- A type has one lifting at most at a term and at its nesting, of one result, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\uparrow}` -/
theorem Term.Lifts.unique (hd : sig.Distinct) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A₁ A₂ : Term k Γ'} → {m₁ m₂ : Lifting.Result k} → Term.Lifts sig v ρ n e A A₁ m₁ →
        Term.Lifts sig v ρ n e A A₂ m₂ → A₁ = A₂ ∧ m₁ = m₂
  | _, _, _, _, _, _, _, _, _, _, .var hx₁ _, h₂ => by
    cases h₂ with
    | var hx₂ _ =>
      cases hx₁.symm.trans hx₂
      exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, _, _, _, .block hD₁, h₂ => by
    cases h₂ with
    | block hD₂ =>
      cases hD₁.symm.trans hD₂
      exact ⟨rfl, rfl⟩
    | inst _ _ hn => exact absurd rfl (hn _)
  | _, _, _, _, _, _, _, _, _, _,
      .inst (D := D) (qs := qs) (ls := ls) (ps := ps) (as := as) h₁ hD₁ hn₁ hq₁ hl₁ hp₁ has₁ _ _ hπ₁,
      h₂ => by
    generalize hA : Term.inst D qs ls ps as = A at h₂
    cases h₂ with
    | var => cases hA
    | block =>
      injection hA with _ _ hD
      subst hD
      exact absurd rfl (hn₁ _)
    | inst h₂ hD₂ _ hq₂ hl₂ hp₂ has₂ _ _ hπ₂ =>
      injection hA with _ _ hD hqs hls hps has
      subst hD hqs hls hps
      obtain rfl := Entry.typeDeclaration.inj (hd.entry_unique h₁ h₂ hD₁ hD₂)
      cases eq_of_heq has
      obtain ⟨rfl, rfl, has⟩ := InstanceArgs.Lifts.unique hd has₁ has₂
      cases has
      obtain rfl := Term.Factor.unique_inst hd hπ₁ hπ₂
      exact ⟨rfl, rfl⟩

/-- The arguments of an instance are lifted in one way at most at their nestings: the parameters
whose arguments are lifted, the results of these and the arguments lifted are unique, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\uparrow\bar a}` -/
theorem InstanceArgs.Lifts.unique (hd : sig.Distinct) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S₁ S₂ : List Nat} → {ms₁ ms₂ : List (Lifting.Result k)} →
      {Δ₁ Δ₂ : Scope} → {as₁ : InstanceArgs k Γ' Δ₁} → {as₂ : InstanceArgs k Γ' Δ₂} →
      InstanceArgs.Lifts sig v ρ ns as S₁ ms₁ as₁ → InstanceArgs.Lifts sig v ρ ns as S₂ ms₂ as₂ →
        S₁ = S₂ ∧ ms₁ = ms₂ ∧
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

end Sic.Core
