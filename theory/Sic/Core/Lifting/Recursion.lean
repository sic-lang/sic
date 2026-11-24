module

public import Sic.Core.Lifting
import Sic.Core.Substitution.Composition
import Sic.Core.Syntax.Signature

/-!
# Recursion of the Liftings

The lifting of a codata type without recursive destructor has no recursive destructor: the result
of a destructor of the lifting is a motive, or an instance of the lifting of the type that the
result lifted is an instance of, which is the lifting itself only if this type is the type lifted.

The result lifted is the result of a destructor substituted by the parameters themselves and by the
observations of the destructors before it, so the proof shows that this substitution makes no
instance of a declared type: what it gives a variable is neutral, an observation or a variable of
the scope at arguments, which no instantiation makes an instance.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Neutral Abstractions -/

/-- An abstraction over `n` variables is neutral: an observation, or a variable of the scope at
arguments, which no instantiation of the `n` variables makes an instance of a declared type. -/
inductive Term.Neutral {Γ : Scope} : (n : Nat) → Term k (Γ.extend n) → Prop where
  /-- An observation. -/
  | obs {n : Nat} {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k (Γ.extend n) Δ) (t : Term k (Γ.extend n)) (d : Name)
      (bs : Terms k (Γ.extend n)) : Term.Neutral n (.obs D qs ls ps as t d bs)
  /-- A variable of the scope, at arguments. -/
  | var {n : Nat} {e : Scope.Entry} (y : Var Γ e) (us : Args k (Γ.extend n) e.params) :
      Term.Neutral n (.var (y.weakenN n) us)

/-- A neutral abstraction, instantiated, is not an instance of a declared type. -/
theorem Term.Neutral.blockName_instantiate {Γ : Scope} {ps : List Parameter}
    {u : Term k (Γ.extend ps.length)} (h : Term.Neutral ps.length u) (ts : Args k Γ ps)
    (names : List Name) : (u.instantiate ts).blockName names = none := by
  rw [Term.instantiate_eq_subst₀]
  cases h with
  | obs => rw [Term.subst₀]; rfl
  | var y us => rw [Term.subst₀_var, Args.toSubst₀_weakenN]; rfl

/-- A neutral abstraction, renamed under its variables, is neutral. -/
theorem Term.Neutral.rename {Γ Δ : Scope} {n : Nat} {u : Term k (Δ.extend n)}
    (h : Term.Neutral n u) (α : Ren Γ Δ) : Term.Neutral n (u.rename (Ren.liftN n α)) := by
  cases h with
  | obs => rw [Term.rename]; exact .obs ..
  | var y us => rw [Term.rename, Ren.liftN_weakenN]; exact .var ..

/-- A substitution of the second order is neutral: it gives each variable a neutral abstraction. -/
def Subst.Neutral {Γ Δ : Scope} (θ : Subst k Γ Δ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Δ e), Term.Neutral e.params.length (θ x)

/-- A neutral substitution under a new entry is neutral. -/
theorem Subst.Neutral.lift {Γ Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ} (h : Subst.Neutral θ) :
    Subst.Neutral (Subst.lift (e := e) θ) := fun x =>
  match x with
  | .zero => .var ..
  | .succ x => (h x).rename Ren.weaken

/-- A neutral substitution under new variables is neutral. -/
theorem Subst.Neutral.liftN {Γ Δ : Scope} :
    (n : Nat) → {θ : Subst k Γ Δ} → Subst.Neutral θ → Subst.Neutral (Subst.liftN n θ)
  | 0, _, h => h
  | n + 1, _, h => Subst.Neutral.liftN n h.lift

/-- A neutral substitution followed by a neutral abstraction is neutral. -/
theorem Subst.Neutral.snoc {Γ Δ : Scope} {e : Scope.Entry} {θ : Subst k Γ Δ} (h : Subst.Neutral θ)
    {B : Term k (Γ.extend e.params.length)} (hB : Term.Neutral e.params.length B) :
    Subst.Neutral (θ.snoc (e := e) B) := fun x =>
  match x with
  | .zero => hB
  | .succ x => h x

/-- The parameters themselves, renamed, are a neutral substitution. -/
theorem InstanceArgs.identity_rename_neutral {Γ : Scope} :
    {Δ : Scope} → (α : Ren Γ Δ) →
      Subst.Neutral ((InstanceArgs.identity (k := k) Δ).rename α).toSubst
  | _ :: _, α, _, .zero => by
    show Term.Neutral _ ((Var.eta .zero).rename (Ren.liftN _ α))
    rw [Var.eta_rename]
    exact .var ..
  | _ :: Δ, α, _, .succ x => by
    show Term.Neutral _ ((((InstanceArgs.identity Δ).rename Ren.weaken).rename α).toSubst x)
    rw [InstanceArgs.rename_rename_of (α₁ := α) (α₂ := Ren.weaken) (α₃ := fun y => α y.succ)
      (fun _ => rfl)]
    exact InstanceArgs.identity_rename_neutral (fun y => α y.succ) x

/-- A neutral substitution makes no instance of a declared type. -/
theorem Term.blockName_subst_neutral {Γ Δ : Scope} {θ : Subst k Γ Δ} (h : Subst.Neutral θ)
    (names : List Name) :
    (A : Term k Δ) → A.blockName names = none → (A.subst θ).blockName names = none
  | .var x ts, _ => by
    rw [Term.subst]
    exact (h x).blockName_instantiate _ names
  | .inst .., hA => by rw [Term.subst]; exact hA
  | .sort _, _ | .const .., _ | .ctor .., _ | .recursor .., _ | .obs .., _ | .corec .., _
  | .equality .., _ | .refl .., _ | .transp .., _ | .propExt .., _ | .coind .., _ => by
    rw [Term.subst]; rfl

/-- A term in which levels replace the level variables is an instance of the same type of the
block. -/
theorem Term.blockName_substLevels {k' : Nat} {Γ : Scope} (names : List Name)
    (ls' : Fin k → Level k') :
    (A : Term k Γ) → (A.substLevels ls').blockName names = A.blockName names
  | .var .. | .sort _ | .const .. | .inst .. | .ctor .. | .recursor .. | .obs .. | .corec ..
  | .equality .. | .refl .. | .transp .. | .propExt .. | .coind .. => by
    rw [Term.substLevels]; rfl

/-- Destructors in which levels replace the level variables have their recursive destructors at the
same positions. -/
theorem Destructors.recursion_substLevels {k' : Nat} (names : List Name)
    (ls' : Fin k → Level k') :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) →
      (ds.substLevels ls').recursion names = ds.recursion names
  | _, _, .nil => rfl
  | _, _, .cons _ _ _ _ B _ ds => by
    rw [Destructors.substLevels, Destructors.recursion, Destructors.recursion,
      Term.blockName_substLevels, Destructors.recursion_substLevels names ls' ds]

/-! ## Recursion of a Lifting -/

/-- A term of a scope with as many new variables is an instance of the same type of the block. -/
theorem Term.blockName_cast {Γ : Scope} (names : List Name) {n m : Nat} (h : n = m)
    (B : Term k (Γ.extend n)) : (h ▸ B).blockName names = B.blockName names := by
  subst h
  rfl

/-- The lifting of a type without position that is not an instance of a type of the block of `F`
is not an instance of a lifting of `F`. -/
theorem Term.Lifts.blockName {sig : Signature} {v : Lifting.Variables} {Γ' Γ : Scope}
    {ρ : Lifting k Γ' Γ} {e : Term k Γ'} {A : Term k Γ} {A' : Term k Γ'} {m : Lifting.Result k}
    (h : Term.Lifts sig v ρ .plain e A A' m) {names : List Name} {F : Name}
    (hF : F ∈ names) (hA : A.blockName names = none) (S : List Nat) :
    A'.blockName [Lifting.name F S] = none := by
  cases h with
  | var => rfl
  | @inst _ _ _ _ _ _ _ D _ _ _ _ _ S' =>
    show (if Lifting.name D S' ∈ [Lifting.name F S] then _ else _) = none
    split
    · next hm =>
      cases (Lifting.name_inj (List.mem_singleton.1 hm)).1
      simp [Term.blockName, hF] at hA
    · rfl

/-- Destructors lifted, none of which is recursive, at observations and at a substitution that are
neutral, have no destructor whose result is an instance
of a lifting of a type `F` of their block. -/
theorem Destructors.Lifts.recursion {Γ₀ : Scope} {sig : Signature} {v : Lifting.Variables}
    {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)}
    (ho : ∀ d ps, Term.Neutral ps.length (o d ps)) {names : List Name} {F : Name} (hF : F ∈ names)
    (S : List Nat) :
    {Γ' : Scope} → {ρ : Lifting k Γ' Γ₀} → {Ξ : Scope} → {θ : Subst k Γ₀ Ξ} → {ns : List Name} →
      {ds : Destructors k Ξ ns} → {ns' : List Name} → {ds' : Destructors k Γ' ns'} →
      Destructors.Lifts sig v κ o ρ @θ ds ds' → Subst.Neutral θ →
      (∀ r ∈ ds.recursion names, r = none) → ∀ r ∈ ds'.recursion [Lifting.name F S], r = none
  | _, _, _, _, _, _, _, _, .nil, _, _ => fun _ hr => nomatch hr
  | _, _, _, _, _, _, _, _, .lifted hB _ h, hθ, hds => fun r hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [Term.blockName_cast]
      exact hB.blockName hF
        (Term.blockName_subst_neutral (hθ.liftN _) names _ (hds _ List.mem_cons_self)) S
    · exact Destructors.Lifts.recursion ho hF S h (hθ.snoc (ho _ _))
        (fun r hr => hds r (List.mem_cons_of_mem _ hr)) r hr
  | _, _, _, _, _, _, _, _, .absent _ h, hθ, hds =>
    Destructors.Lifts.recursion ho hF S h (hθ.snoc (ho _ _))
      (fun r hr => hds r (List.mem_cons_of_mem _ hr))

/-- The lifting of a codata type without recursive destructor at an instance has no recursive
destructor at the instances that hold it. -/
theorem TypeDeclaration.Lifts.recursion {sig : Signature} {decl : TypeDeclaration} {F : Name}
    {S : List Nat} {ns : List Name}
    {body : decl.LiftingBody S ns}
    (h : decl.Lifts sig F S body) (I : Instance (decl.sorts + 1) (decl.liftingGrades S))
    (hF : ∀ T ∈ decl.codataTypes, T.name = F →
      ∀ r ∈ (T.body I.lifted).recursion decl.names, r = none) :
    ∀ r ∈ (body I).recursion [Lifting.name F S], r = none := by
  obtain ⟨T, hT, hn, hb⟩ := h
  refine Destructors.Lifts.recursion (fun _ _ => .obs ..)
    (hn ▸ TypeDeclaration.codata_name_mem_names hT : F ∈ decl.names) S (hb I)
    (InstanceArgs.identity_rename_neutral _) ?_
  rw [Destructors.recursion_substLevels]
  exact hF T hT hn

/-- The result of a destructor of the lifting of a codata type without recursive destructor at an
instance is no instance of this lifting, at the instances that hold it. -/
theorem TypeDeclaration.Lifts.blockName_pos {sig : Signature} {decl : TypeDeclaration} {F : Name}
    {S : List Nat} {ns : List Name}
    {body : decl.LiftingBody S ns}
    (h : decl.Lifts sig F S body) (I : Instance (decl.sorts + 1) (decl.liftingGrades S))
    (hF : ∀ T ∈ decl.codataTypes, T.name = F →
      ∀ r ∈ (T.body I.lifted).recursion decl.names, r = none)
    {d : Name} {p q ς : Grade} {ps : List Parameter} {Ξ : Scope}
    {Θ : Telescope (decl.levels + S.length) Ξ ps}
    {B : Term (decl.levels + S.length) (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
    (hpos : (body I).Pos d p q ς Ξ Θ B ψ) : B.blockName [Lifting.name F S] = none := by
  have hr : ((body I).recursion [Lifting.name F S])[hpos.index]?.join =
      B.blockName [Lifting.name F S] := hpos.recursionAt_index [Lifting.name F S]
  cases hi : ((body I).recursion [Lifting.name F S])[hpos.index]? with
  | none => rw [← hr, hi]; rfl
  | some r =>
    cases h.recursion I hF r (List.mem_of_getElem? hi)
    rw [← hr, hi]
    rfl

end Sic.Core
