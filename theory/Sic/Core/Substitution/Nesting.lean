module

public import Sic.Core.Nesting
public import Sic.Core.Substitution.Composition
public import Sic.Core.Substitution.Rules

/-!
# Nesting of the Renamed Types

A renaming keeps the nesting of a type of annex 08 of RFC 36, at the nestings of the variables that
it renames, and so the nestings of the fields of a block, whose variables have no position: the
fields after a recursive field, which do not depend on it, are renamed under it.
A variable of a scope keeps its nesting under new variables, which have no position.
A type keeps its nesting when levels replace its level variables, since the nesting does not read
the levels, and so do the variables of the scope of a destructor.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α : Type}

/-- The nestings of the variables that a renaming renames stay theirs under a new entry. -/
theorem Nesting.lift_rename {Γ Δ : Scope} {e₀ : Scope.Entry} {ρ : Ren Γ Δ} {ν : Nesting α Δ}
    {ν' : Nesting α Γ} (h : ∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Δ) e), Nesting.lift @ν' (Ren.lift @ρ x) = Nesting.lift @ν x :=
  fun _ x =>
    match x with
    | .zero => rfl
    | .succ x => h _ x

/-- The nestings of the variables that a renaming renames stay theirs under new variables. -/
theorem Nesting.liftN_rename :
    {Γ Δ : Scope} → (n : Nat) → {ρ : Ren Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) →
      ∀ (e : Scope.Entry) (x : Var (Δ.extend n) e),
        Nesting.liftN n @ν' (Ren.liftN n @ρ x) = Nesting.liftN n @ν x
  | _, _, 0, _, _, _, h => h
  | _, _, n + 1, _, _, _, h => Nesting.liftN_rename n (Nesting.lift_rename h)

/-- A variable of a scope keeps its nesting under new variables. -/
theorem Nesting.liftN_weakenN :
    {Γ : Scope} → (n : Nat) → (ν : Nesting α Γ) → {e : Scope.Entry} → (x : Var Γ e) →
      Nesting.liftN n @ν (x.weakenN n) = ν x
  | _, 0, _, _, _ => rfl
  | _, n + 1, ν, _, x => Nesting.liftN_weakenN n (Nesting.lift @ν) x.succ

mutual

/-- A renamed type has the nesting of the type, at the nestings of the variables renamed. -/
theorem Term.nest_rename (mark : Name → Option α) :
    {Γ Δ : Scope} → (ρ : Ren Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) → (A : Term k Δ) →
      (A.rename ρ).nest mark @ν' = A.nest mark @ν
  | _, _, _, _, _, h, .var x _ => h _ x
  | _, _, ρ, _, _, h, .inst _ _ _ _ as => by
    rw [Term.rename, Term.nest, Term.nest, InstanceArgs.nest_rename mark ρ h as]
  | _, _, _, _, _, _, .sort _ => rfl
  | _, _, _, _, _, _, .const _ _ _ _ => rfl
  | _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, _, _, .equality .. | _, _, _, _, _, _, .refl ..
  | _, _, _, _, _, _, .transp .. | _, _, _, _, _, _, .propExt .. => rfl

/-- Renamed arguments of an instance have the nestings of the arguments, at the nestings of the
variables renamed. -/
theorem InstanceArgs.nest_rename (mark : Name → Option α) :
    {Γ Δ Ξ : Scope} → (ρ : Ren Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) → (as : InstanceArgs k Δ Ξ) →
      (as.rename ρ).nest mark @ν' = as.nest mark @ν
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, ρ, _, _, h, .snoc as B => by
    rw [InstanceArgs.rename, InstanceArgs.nest, InstanceArgs.nest,
      Term.nest_rename mark (Ren.liftN _ ρ) (Nesting.liftN_rename _ h) B,
      InstanceArgs.nest_rename mark ρ h as]

end

/-- A renamed type of a field has the nesting of the type. -/
theorem Term.blockNest_rename {Γ Δ : Scope} (names : List Name) (ρ : Ren Γ Δ) (A : Term k Δ) :
    (A.rename ρ).blockNest names = A.blockNest names :=
  Term.nest_rename _ ρ (fun _ _ => rfl) A

/-- A renamed telescope has the nestings of the telescope. -/
theorem Telescope.nest_rename {Γ Δ : Scope} (names : List Name) :
    {ps : List Parameter} → (ρ : Ren Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.rename ρ).nest names = Θ.nest names
  | [], _, .nil => rfl
  | _ :: _, ρ, .cons _ _ A Θ => by
    rw [Telescope.rename, Telescope.nest, Telescope.nest, Term.blockNest_rename,
      Telescope.nest_rename names (Ren.lift ρ) Θ]

/-- Renamed destructors have their results with a position at the same positions, at the nestings
of the variables renamed. -/
theorem Destructors.nested_rename :
    {Γ Δ : Scope} → {ns : List Name} → (ρ : Ren Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) → (ds : Destructors k Δ ns) →
      (ds.rename ρ).nested @ν' = ds.nested @ν
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, ρ, _, _, h, .cons (ps := ps) _ _ _ _ B _ ds => by
    rw [Destructors.rename, Destructors.nested, Destructors.nested,
      Term.nest_rename _ (Ren.liftN ps.length ρ) (Nesting.liftN_rename ps.length h) B,
      Destructors.nested_rename (Ren.lift ρ) (Nesting.lift_rename h) ds]

mutual

/-- A type keeps its nesting when levels replace its level variables. -/
theorem Term.nest_substLevels {k' : Nat} (mark : Name → Option α) (ls' : Fin k → Level k') :
    {Γ : Scope} → {ν : Nesting α Γ} → (A : Term k Γ) →
      (A.substLevels ls').nest mark @ν = A.nest mark @ν
  | _, _, .var _ _ => by rw [Term.substLevels, Term.nest, Term.nest]
  | _, _, .inst _ _ _ _ as => by
    rw [Term.substLevels, Term.nest, Term.nest, InstanceArgs.nest_substLevels mark ls' as]
  | _, _, .sort _ => by rw [Term.substLevels]; rfl
  | _, _, .const _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, .equality .. | _, _, .refl ..
  | _, _, .transp .. | _, _, .propExt .. => by rw [Term.substLevels]; rfl

/-- The arguments of an instance keep their nestings when levels replace their level variables. -/
theorem InstanceArgs.nest_substLevels {k' : Nat} (mark : Name → Option α)
    (ls' : Fin k → Level k') :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → (as : InstanceArgs k Γ Δ) →
      (as.substLevels ls').nest mark @ν = as.nest mark @ν
  | _, _, _, .nil => rfl
  | _, _, _, .snoc as B => by
    rw [InstanceArgs.substLevels, InstanceArgs.nest, InstanceArgs.nest,
      Term.nest_substLevels mark ls' B, InstanceArgs.nest_substLevels mark ls' as]

end

/-- The nestings of the variables of the scope of a position are the same at instantiated levels,
since they read only the scopes. -/
theorem Destructors.Pos.nesting_substLevels {k' : Nat} (L : Fin k → Level k') {d : Name}
    {p q ς : Grading.Grade} {ps : List Parameter} :
    {Γ : Scope} → {nms : List Name} → {ds : Destructors k Γ nms} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grading.Grade ps.length} → (hpos : ds.Pos d p q ς Ξ Θ B ψ) →
      (ν : Nesting α Γ) → @Eq (Nesting α Ξ) ((hpos.substLevels L).nesting @ν) (hpos.nesting @ν)
  | _, _, _, _, _, _, _, .here, _ => rfl
  | _, _, _, _, _, _, _, .there h, ν => h.nesting_substLevels L (Nesting.lift @ν)

/-! ## Substituted Types -/

/-- The nesting of what a substitution of the first order gives a variable: that of the variable
it gives, or that of the term. -/
def Val.nest {Γ : Scope} {e : Scope.Entry} (mark : Name → Option α) (ν : Nesting α Γ) :
    Val k Γ e → Nest α
  | .var y => ν y
  | .term t => t.nest mark @ν

/-- A renamed value has the nesting of the value, at the nestings of the variables it renames. -/
theorem Val.nest_rename (mark : Name → Option α) {Γ Δ : Scope} (ρ : Ren Γ Δ) {ν : Nesting α Δ}
    {ν' : Nesting α Γ} (h : ∀ (e : Scope.Entry) (x : Var Δ e), ν' (ρ x) = ν x) {e : Scope.Entry} :
    (v : Val k Δ e) → (v.rename ρ).nest mark @ν' = v.nest mark @ν
  | .var y => h _ y
  | .term t => Term.nest_rename mark ρ h t

/-- A value applied to arguments has the nesting of the value. -/
theorem Val.nest_apply (mark : Name → Option α) {Γ : Scope} {ν : Nesting α Γ} {e : Scope.Entry} :
    (v : Val k Γ e) → (us : Args k Γ e.params) → (v.apply us).nest mark @ν = v.nest mark @ν
  | .var _, _ => rfl
  | .term _, _ => rfl

/-- A substitution that gives each variable its nesting still does under a new entry. -/
theorem Subst₀.lift_nest (mark : Name → Option α) {Γ Δ : Scope} {e₀ : Scope.Entry}
    {σ : Subst₀ k Γ Δ} {ν : Nesting α Δ} {ν' : Nesting α Γ}
    (h : ∀ (e : Scope.Entry) (x : Var Δ e), (σ x).nest mark @ν' = ν x) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Δ) e),
      (Subst₀.lift σ x).nest mark (Nesting.lift @ν') = Nesting.lift @ν x :=
  fun _ x =>
    match x with
    | .zero => rfl
    | .succ x => (Val.nest_rename mark Ren.weaken (fun _ _ => rfl) (σ x)).trans (h _ x)

/-- A substitution that gives each variable its nesting still does under new variables. -/
theorem Subst₀.liftN_nest (mark : Name → Option α) :
    {Γ Δ : Scope} → (n : Nat) → {σ : Subst₀ k Γ Δ} → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), (σ x).nest mark @ν' = ν x) →
      ∀ (e : Scope.Entry) (x : Var (Δ.extend n) e),
        (Subst₀.liftN n σ x).nest mark (Nesting.liftN n @ν') = Nesting.liftN n @ν x
  | _, _, 0, _, _, _, h => h
  | _, _, n + 1, _, _, _, h => Subst₀.liftN_nest mark n (Subst₀.lift_nest mark h)

mutual

/-- A substituted type has the nesting of the type, at the nestings of what the substitution gives
the variables. -/
theorem Term.nest_subst₀ (mark : Name → Option α) :
    {Γ Δ : Scope} → (σ : Subst₀ k Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), (σ x).nest mark @ν' = ν x) → (A : Term k Δ) →
      (A.subst₀ σ).nest mark @ν' = A.nest mark @ν
  | _, _, σ, _, _, h, .var x ts => by
    rw [Term.subst₀_var, Val.nest_apply]
    exact h _ x
  | _, _, σ, _, _, h, .inst _ _ _ _ as => by
    rw [Term.subst₀, Term.nest, Term.nest, InstanceArgs.nest_subst₀ mark σ h as]
  | _, _, _, _, _, _, .sort _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .const _ _ _ _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.subst₀]; rfl
  | _, _, _, _, _, _, .equality .. | _, _, _, _, _, _, .refl ..
  | _, _, _, _, _, _, .transp .. | _, _, _, _, _, _, .propExt .. => by rw [Term.subst₀]; rfl

/-- Substituted arguments of an instance have the nestings of the arguments. -/
theorem InstanceArgs.nest_subst₀ (mark : Name → Option α) :
    {Γ Δ Ξ : Scope} → (σ : Subst₀ k Γ Δ) → {ν : Nesting α Δ} → {ν' : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), (σ x).nest mark @ν' = ν x) →
      (as : InstanceArgs k Δ Ξ) → (as.subst₀ σ).nest mark @ν' = as.nest mark @ν
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, σ, _, _, h, .snoc as B => by
    rw [InstanceArgs.subst₀, InstanceArgs.nest, InstanceArgs.nest,
      Term.nest_subst₀ mark _ (Subst₀.liftN_nest mark _ h) B, InstanceArgs.nest_subst₀ mark σ h as]

end

/-- `nest(B[t̄ / Θ])`: a type in which arguments replace the variables of a telescope has the
nesting of the type, at the nestings of the arguments for these variables. -/
theorem Term.nest_instantiate (mark : Name → Option α) {Γ : Scope} {ps : List Parameter}
    {ν : Nesting α Γ} (B : Term k (Γ.extend ps.length)) (ts : Args k Γ ps) :
    (B.instantiate ts).nest mark @ν = B.nest mark (fun x => (ts.toSubst₀ x).nest mark @ν) := by
  rw [Term.instantiate_eq_subst₀]
  exact Term.nest_subst₀ mark _ (fun _ _ => rfl) B

/-- The nesting of an instance, mapped by `f`, is that of the nestings of its arguments, each
mapped by `f`. -/
theorem Nest.ofArgs_map {β : Type} (f : α → β) (ns : List (Nest α)) :
    (Nest.ofArgs ns).map f = Nest.ofArgs (Nest.mapList f ns) := by
  have hall : ∀ ns : List (Nest α), (Nest.mapList f ns).all Nest.isPlain = ns.all Nest.isPlain := by
    intro ns
    induction ns with
    | nil => rfl
    | cons n ns ih =>
      rw [Nest.mapList, List.all_cons, List.all_cons, ih]
      cases n <;> rfl
  unfold Nest.ofArgs
  rw [hall]
  split <;> rfl

/-- Nestings mapped by `f` still are under a new entry. -/
theorem Nesting.lift_map {β : Type} (f : α → β) {Γ : Scope} {e₀ : Scope.Entry} {ν : Nesting α Γ}
    {ν' : Nesting β Γ} (h : ∀ (e : Scope.Entry) (x : Var Γ e), (ν x).map f = ν' x) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Γ) e),
      (Nesting.lift @ν x).map f = Nesting.lift @ν' x :=
  fun _ x =>
    match x with
    | .zero => rfl
    | .succ x => h _ x

/-- Nestings mapped by `f` still are under new variables. -/
theorem Nesting.liftN_map {β : Type} (f : α → β) :
    {Γ : Scope} → (n : Nat) → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν x).map f = ν' x) →
      ∀ (e : Scope.Entry) (x : Var (Γ.extend n) e),
        (Nesting.liftN n @ν x).map f = Nesting.liftN n @ν' x
  | _, 0, _, _, h => h
  | _, n + 1, _, _, h => Nesting.liftN_map f n (Nesting.lift_map f h)

mutual

/-- `nest_Λ(A) ↦ f`: the nesting of a type, mapped by `f`, is its nesting where the types of the
block and the variables hold what `f` gives. -/
theorem Term.nest_map {β : Type} (f : α → β) (mark : Name → Option α) :
    {Γ : Scope} → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν x).map f = ν' x) → (A : Term k Γ) →
      (A.nest mark @ν).map f = A.nest (fun D => (mark D).map f) @ν'
  | _, _, _, h, .var x _ => h _ x
  | _, _, _, h, .inst D _ _ _ as => by
    rw [Term.nest, Term.nest]
    cases mark D with
    | some a => rfl
    | none =>
      show (Nest.ofArgs _).map f = Nest.ofArgs _
      rw [Nest.ofArgs_map, InstanceArgs.nest_map f mark h as]
  | _, _, _, _, .sort _ => rfl
  | _, _, _, _, .const _ _ _ _ => rfl
  | _, _, _, _, .ctor _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .obs _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .equality .. | _, _, _, _, .refl ..
  | _, _, _, _, .transp .. | _, _, _, _, .propExt .. => rfl

/-- The nestings of the arguments of an instance, each mapped by `f`. -/
theorem InstanceArgs.nest_map {β : Type} (f : α → β) (mark : Name → Option α) :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν x).map f = ν' x) → (as : InstanceArgs k Γ Δ) →
      Nest.mapList f (as.nest mark @ν) = as.nest (fun D => (mark D).map f) @ν'
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, h, .snoc as B => by
    rw [InstanceArgs.nest, InstanceArgs.nest, Nest.mapList,
      Term.nest_map f mark (Nesting.liftN_map f _ h) B, InstanceArgs.nest_map f mark h as]

end

end Sic.Core
