module

public import Sic.Core.Positivity

/-!
# Liftings

The liftings of annex 20 of RFC 36: the lifting of a codata type at a set of its parameters is a
codata type declared from it, over a motive for each of these parameters and a term `y` of the
type, whose terms hold, for each observation of `y`, a term of the motive at each position of the
parameters in the result.
The recursive result of a field nested below the codata type has this type.

The lifting has the destructors of the codata type whose results mention a parameter lifted, each
at the arguments of its own, used as many times as the recursor that computes its result uses them,
and its result is the result lifted at the observation of `y`: a parameter becomes its motive at
this observation, and an instance of a declared type the instance of its lifting.
The lifting is a relation, as the strict positivity is, whose cases it follows: its definition reads
which parameters occur in a term, and a term in which a variable does not occur is a term of the
scope without it.

The RFC names the variables, so that the motive of a parameter is found by its name, and a type of
the declaration is a type of its lifting as it is; with de Bruijn indices, a lifting of scopes gives
each variable of a scope its variable in the scope of the lifting, and each variable lifted its
motive.
The motive of a parameter follows it in the parameters of the lifting, so that this scope is
defined entry by entry.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Motives -/

-- ADE: none.
/-- The ownership of a result that is the constant `χ`, without factor, whatever the `n` arguments
are. -/
def Lifting.resultOwnership (χ : Grade) (n : Nat) : ResultOwnership Grade n :=
  ⟨some χ, fun _ => none⟩

/-- The grade and the requirement of the last entry of the telescope of a motive, the term at which
the motive is a type, which a type may use as it wants and of which it requires nothing. -/
def Lifting.termParam : Parameter := ⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩

-- ADE: none.
/-- The entry of the motive `C_Y : (Θ_Y, z : Y[Θ_Y] ⊢ κ_C)` of a parameter `Y : (Θ_Y ⊢ κ)`, whose
entry is `e`: a second-order variable over the telescope of `Y` followed by a term of `Y`, whose
result, a type, has the least ownership. -/
@[reducible] def Scope.Entry.motive (e : Scope.Entry) : Scope.Entry :=
  .secondOrder (e.params ++ [Lifting.termParam])
    (Lifting.resultOwnership .unrestrictedUnrestricted _)

/-- `(t̄, t)`: the arguments `t̄` followed by the argument `t` of one more entry. -/
def Args.snoc {Γ : Scope} {p : Parameter} :
    {ps : List Parameter} → Args k Γ ps → Term k Γ → Args k Γ (ps ++ [p])
  | [], .nil, t => .cons t .nil
  | _ :: _, .cons u us, t => .cons u (us.snoc t)

/-- `(Θ, x : A ▶ p; q ◀ r)`: the telescope `Θ` followed by one more entry, whose type `A` is in the
scope of the entries of `Θ`. -/
def Telescope.snoc {p : Parameter} (q : Grade) : {Γ : Scope} → {ps : List Parameter} →
    Telescope k Γ ps → Term k (Γ.extend ps.length) → Telescope k Γ (ps ++ [p])
  | _, [], .nil, A => .cons q p A .nil
  | _, _ :: _, .cons q' p' A' Θ, A => .cons q' p' A' (Θ.snoc q A)

/-- The scope `Γ` extended by the variables of a telescope and then by one more variable is `Γ`
extended by the variables of the telescope followed by one more entry. -/
theorem Scope.extend_snoc : (Γ : Scope) → (ps : List Parameter) → (p : Parameter) →
    .var :: Γ.extend ps.length = Γ.extend (ps ++ [p]).length
  | _, [], _ => rfl
  | Γ, _ :: ps, p => Scope.extend_snoc (.var :: Γ) ps p

/-! ## Liftings of Scopes -/

/-- A lifting of the scope `Γ` in the scope `Γ'`: each variable of `Γ` is a variable of `Γ'`, and
each variable lifted has a motive in `Γ'`.
The RFC finds both by the names of the variables. -/
structure Lifting (Γ' Γ : Scope) where
  /-- The variable of `Γ'` that a variable of `Γ` is. -/
  ren : Ren Γ' Γ
  /-- The motive of a variable lifted, none for the others. -/
  motive : ∀ {e : Scope.Entry}, Var Γ e → Option (Var Γ' e.motive)

namespace Lifting

/-- The lifting `ρ` under a new entry of both scopes, which is not lifted. -/
def lift {Γ' Γ : Scope} {e : Scope.Entry} (ρ : Lifting Γ' Γ) : Lifting (e :: Γ') (e :: Γ) where
  ren := Ren.lift ρ.ren
  motive := fun x =>
    match x with
    | .zero => none
    | .succ x => (ρ.motive x).map .succ

/-- The lifting `ρ` under `n` new variables of both scopes. -/
def liftN {Γ' Γ : Scope} : (n : Nat) → Lifting Γ' Γ → Lifting (Γ'.extend n) (Γ.extend n)
  | 0, ρ => ρ
  | n + 1, ρ => liftN n (lift ρ)

/-- The lifting `ρ` in the scope `Γ'` extended by a new entry. -/
def weaken {Γ' Γ : Scope} {e : Scope.Entry} (ρ : Lifting Γ' Γ) : Lifting (e :: Γ') Γ where
  ren := fun x => .succ (ρ.ren x)
  motive := fun x => (ρ.motive x).map .succ

end Lifting

-- ADE: none.
/-- No variable lifted occurs in the term `t`. -/
def Term.AvoidsLifted {Γ' Γ : Scope} (ρ : Lifting Γ' Γ) (t : Term k Γ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Γ e), (ρ.motive x).isSome → t.Avoids x

-- ADE: none.
/-- No variable lifted occurs in the arguments `t̄`. -/
def Args.AvoidsLifted {Γ' Γ : Scope} {ps : List Parameter} (ρ : Lifting Γ' Γ) (ts : Args k Γ ps) :
    Prop :=
  ∀ {e : Scope.Entry} (x : Var Γ e), (ρ.motive x).isSome → ts.Avoids x

/-! ## Liftings of Types -/

/-- The variables that a lifting adds to those of its type declaration, at an instance: the quality
`s_C` and the level `l_C` of the sort of the motives, the grade `r` of the recursor that computes
the terms of the lifting, the requirement `ς` of its destructors on the term that they observe, and
the ownership `χ` of their results. -/
structure Lifting.Variables (k : Nat) where
  /-- The quality `s_C` of the sort of the motives. -/
  quality : Quality
  /-- The level `l_C` of the sort of the motives. -/
  level : Level k
  /-- The grade `r` of the recursor. -/
  recursion : Grade
  /-- The requirement `ς` of the destructors on the term that they observe. -/
  requirement : Grade
  /-- The ownership `χ` of the results of the destructors. -/
  ownership : Grade

-- ADE: none.
/-- `F^S`: the name of the lifting of the type `F` at its parameters at the positions `S`, in
order, a name of the
signature that `F` and `S` determine. -/
def Lifting.name (F : Name) (S : List Nat) : Name := F ++ "^" ++ toString S

mutual

-- ADE: none.
/--
`A ↑ u = A'`: the type `A'` is the type `A` lifted at the term `e` of `A`, where `ρ` gives the
variables lifted and their motives, and `v` the variables of the lifting.
-/
inductive Term.Lifts (v : Lifting.Variables k) :
    {Γ' Γ : Scope} → Lifting Γ' Γ → Term k Γ' → Term k Γ → Term k Γ' → Prop where
  /-- A variable lifted, applied to arguments in which no variable lifted occurs: its motive, at
  these arguments and at the term.
  RFC: `\uparrow_X` -/
  | var {Γ' Γ : Scope} {ρ : Lifting Γ' Γ} {e : Term k Γ'} {a : Scope.Entry} {x : Var Γ a}
      {y : Var Γ' a.motive} {ts : Args k Γ a.params} (hx : ρ.motive x = some y)
      (hts : ts.AvoidsLifted ρ) :
      Term.Lifts v ρ e (.var x ts) (.var y ((ts.rename ρ.ren).snoc e))
  /-- An instance of a declared type, of which an argument at least is lifted: the instance of the
  lifting of this type at the parameters of these arguments, at the variables of the lifting, at
  the arguments lifted and at the term.
  RFC: `\uparrow_D` -/
  | inst {Γ' Γ : Scope} {ρ : Lifting Γ' Γ} {e : Term k Γ'} {Δ Δ' : Scope} {D : Name}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
      {S : List Nat} {as' : InstanceArgs k Γ' Δ'} (has : InstanceArgs.Lifts v ρ as S as')
      (hS : S ≠ []) :
      Term.Lifts v ρ e (.inst D qs ls ps as)
        (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ [v.level])
          (ps ++ [v.recursion, v.requirement, v.ownership]) (.snoc (e := .var) as' e))

-- ADE: none.
/--
`ā ↑ = (S; ā')`: the arguments `ā'` are the arguments `ā` of an instance lifted, and `S` the
positions of the parameters whose arguments are lifted, in order: the argument of such a parameter is
followed by its motive, the argument lifted at a term of its own, and the others are kept.
-/
inductive InstanceArgs.Lifts (v : Lifting.Variables k) :
    {Γ' Γ : Scope} → Lifting Γ' Γ → {Δ : Scope} → InstanceArgs k Γ Δ → List Nat → {Δ' : Scope} →
      InstanceArgs k Γ' Δ' → Prop where
  /-- No argument.
  RFC: `\uparrow_{\bar a\varepsilon}` -/
  | nil {Γ' Γ : Scope} {ρ : Lifting Γ' Γ} : InstanceArgs.Lifts v ρ .nil [] .nil
  /-- An argument in which a variable lifted occurs, followed by its motive.
  RFC: `\uparrow_{\bar a,}` -/
  | lifted {Γ' Γ : Scope} {ρ : Lifting Γ' Γ} {Δ Δ' : Scope} {a : Scope.Entry}
      {as : InstanceArgs k Γ Δ} {S : List Nat} {as' : InstanceArgs k Γ' Δ'}
      {B : Term k (Γ.extend a.params.length)} {B' : Term k (.var :: Γ'.extend a.params.length)}
      (has : InstanceArgs.Lifts v ρ as S as')
      (hB : Term.Lifts v (ρ.liftN a.params.length).weaken (.var₀ .zero) B B') :
      InstanceArgs.Lifts v ρ (.snoc as B) (S ++ [Δ.length])
        (.snoc (e := a.motive) (.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren)))
          (Scope.extend_snoc Γ' a.params Lifting.termParam ▸ B'))
  /-- An argument in which no variable lifted occurs.
  RFC: `\uparrow_{\bar a\notin}` -/
  | absent {Γ' Γ : Scope} {ρ : Lifting Γ' Γ} {Δ Δ' : Scope} {a : Scope.Entry}
      {as : InstanceArgs k Γ Δ} {S : List Nat} {as' : InstanceArgs k Γ' Δ'}
      {B : Term k (Γ.extend a.params.length)} (has : InstanceArgs.Lifts v ρ as S as')
      (hB : B.AvoidsLifted (ρ.liftN a.params.length)) :
      InstanceArgs.Lifts v ρ (.snoc as B) S
        (.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren)))

end

/-! ## Liftings of Destructors -/

/-- The parameter `p` of an argument of a destructor, in the lifting: the argument is used `r` times
more, by the recursor of the grade `r`, and its requirement is kept. -/
def Parameter.scale (r : Grade) (p : Parameter) : Parameter := ⟨r * p.usage, p.requirement⟩

-- ADE: none.
/-- `r · Θ`: the telescope `Θ` whose entries are used `r` times more.
RFC: `\mathsf{scale}_\Theta` -/
def Telescope.scale (r : Grade) : {Γ : Scope} → {ps : List Parameter} → Telescope k Γ ps →
    Telescope k Γ (ps.map (Parameter.scale r))
  | _, _, .nil => .nil
  | _, _, .cons q p A Θ => .cons q (p.scale r) A (Θ.scale r)

-- ADE: none.
/-- `p'`: the grade of the result of a destructor of a lifting whose motives have the quality `s`,
from the grade `p` of the destructor lifted: the grade of the mode of `p`, since an observation
reads the grade of its destructor by its mode only, without use at run time when the motives are
propositions.
RFC: `\mathsf{grade}_{\uparrow}` -/
def Lifting.resultGrade (s : Quality) (p : Grade) : Grade :=
  match s with
  | .type => p.mode.grade
  | .prop => (p.mode.mul .zeroOne).grade

-- ADE: none.
/--
`d̄ ↑ y = d̄'`: the destructors `d̄'` are the destructors `d̄` of a codata type lifted at the term
`y` of this type, where `o` gives the observation of `y` by each destructor, `θ` these observations
for the destructors before `d̄`, on which `d̄` depend, and `ρ` the variables lifted and their
motives.
-/
inductive Destructors.Lifts {Γ₀ : Scope} (v : Lifting.Variables k)
    (o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)) :
    {Γ' : Scope} → Lifting Γ' Γ₀ → {Ξ : Scope} → Subst k Γ₀ Ξ → {ns : List Name} →
      Destructors k Ξ ns → {ns' : List Name} → Destructors k Γ' ns' → Prop where
  /-- No destructor.
  RFC: `\uparrow_{\bar d\varepsilon}` -/
  | nil {Γ' : Scope} {ρ : Lifting Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} :
      Destructors.Lifts v o ρ θ .nil .nil
  /-- A destructor whose result is lifted at the observation of `y` by it: the lifting has it, at
  its arguments, used `r` times more, with this result, of the ownership `χ`, and the requirement
  `ς`, and no destructor after it depends on it.
  RFC: `\uparrow_{\bar d|}` -/
  | lifted {Γ' : Scope} {ρ : Lifting Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} {d : Name}
      {ns ns' : List Name} {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Ξ) ns} {B' : Term k (Γ'.extend ps.length)}
      {ds' : Destructors k
        (.secondOrder (ps.map (Parameter.scale v.recursion))
          (Lifting.resultOwnership v.ownership _) :: Γ') ns'}
      (hB : Term.Lifts v (ρ.liftN ps.length) ((o d ps).rename (Ren.liftN ps.length ρ.ren))
        (B.subst (Subst.liftN ps.length θ)) B')
      (hds : Destructors.Lifts v o ρ.weaken (θ.snoc (e := .secondOrder ps ψ) (o d ps)) ds ds') :
      Destructors.Lifts v o ρ θ (.cons (d := d) p q ς Θ B ψ ds)
        (.cons (d := d) (Lifting.resultGrade v.quality p) .zero v.requirement
          (((Θ.subst θ).rename ρ.ren).scale v.recursion)
          ((List.length_map (Parameter.scale v.recursion)).symm ▸ B')
          (Lifting.resultOwnership v.ownership _) ds')
  /-- A destructor in whose result no variable lifted occurs, which the lifting does not have.
  RFC: `\uparrow_{\bar d\notin}` -/
  | absent {Γ' : Scope} {ρ : Lifting Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} {d : Name}
      {ns ns' : List Name} {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Ξ) ns} {ds' : Destructors k Γ' ns'}
      (hB : (B.subst (Subst.liftN ps.length θ)).AvoidsLifted (ρ.liftN ps.length))
      (hds : Destructors.Lifts v o ρ (θ.snoc (e := .secondOrder ps ψ) (o d ps)) ds ds') :
      Destructors.Lifts v o ρ θ (.cons (d := d) p q ς Θ B ψ ds) ds'

/-! ## Parameters of a Lifting -/

/-- The scope `Δ'` extended by the entry `e` of a parameter, followed by the entry of its motive if
the parameter is lifted. -/
def Scope.liftedCons (b : Bool) (e : Scope.Entry) (Δ' : Scope) : Scope :=
  match b with
  | true => e.motive :: e :: Δ'
  | false => e :: Δ'

/-- The scope of the parameters `Δ` in which each parameter at a position of `S`, the first
parameter at `0`, is followed by its motive. -/
def Scope.lifted (S : List Nat) : Scope → Scope
  | [] => []
  | e :: Δ => Scope.liftedCons (decide (Δ.length ∈ S)) e (Scope.lifted S Δ)

/-- The lifting `ρ` extended by a parameter, lifted or not. -/
def Lifting.cons {Δ' Δ : Scope} {e : Scope.Entry} :
    (b : Bool) → Lifting Δ' Δ → Lifting (Scope.liftedCons b e Δ') (e :: Δ)
  | true, ρ =>
    { ren := fun x =>
        match x with
        | .zero => .succ .zero
        | .succ x => .succ (.succ (ρ.ren x))
      motive := fun x =>
        match x with
        | .zero => some .zero
        | .succ x => (ρ.motive x).map fun y => .succ (.succ y) }
  | false, ρ => ρ.lift

/-- The lifting of the parameters `Δ` in their scope lifted at the positions `S`, which lifts the
parameters at these positions. -/
def Lifting.base (S : List Nat) : (Δ : Scope) → Lifting (Δ.lifted S) Δ
  | [] => { ren := (fun x => nomatch x), motive := (fun x => nomatch x) }
  | _ :: Δ => Lifting.cons _ (Lifting.base S Δ)

/-- The context `Γ, x : A`, followed by the motive `C : (z : x ⊢ κ)` of `x` if it is lifted. -/
def Context.liftedVar {Δ' : Scope} (κ : Universe k) :
    (b : Bool) → Context k Δ' → Term k Δ' → Context k (Scope.liftedCons b .var Δ')
  | true, ctx, A =>
    .secondOrder (ps := [Lifting.termParam]) (.var ctx A)
      (.cons .unrestrictedUnrestricted Lifting.termParam (.var₀ .zero) .nil) (.sort κ)
      (Lifting.resultOwnership .unrestrictedUnrestricted _)
  | false, ctx, A => .var ctx A

/-- The context `Γ, X : (Θ ⊢ A ◀ ψ)`, followed by the motive `C : (Θ, z : X[Θ] ⊢ κ)` of `X` if it
is lifted. -/
def Context.liftedSecondOrder {Δ' : Scope} {ps : List Parameter} (κ : Universe k) :
    (b : Bool) → Context k Δ' → Telescope k Δ' ps → Term k (Δ'.extend ps.length) →
      (ψ : ResultOwnership Grade ps.length) →
        Context k (Scope.liftedCons b (.secondOrder ps ψ) Δ')
  | true, ctx, Θ, A, ψ =>
    .secondOrder (.secondOrder ctx Θ A ψ)
      ((Θ.rename Ren.weaken).snoc .unrestrictedUnrestricted (Var.eta .zero)) (.sort κ)
      (Lifting.resultOwnership .unrestrictedUnrestricted _)
  | false, ctx, Θ, A, ψ => .secondOrder ctx Θ A ψ

-- ADE: none.
/-- The parameters `Δ` in which each parameter at a position of `S` is followed by its motive, a
type of the sort `κ` over the telescope of the parameter and a term of it.
RFC: `\mathsf{params}_{\uparrow}` -/
def Context.lifted (S : List Nat) (κ : Universe k) :
    {Δ : Scope} → Context k Δ → Context k (Δ.lifted S)
  | _, .empty => .empty
  | _, .var (Γ := Δ) ctx A =>
    Context.liftedVar κ _ (ctx.lifted S κ) (A.rename (Lifting.base S Δ).ren)
  | _, .secondOrder (Γ := Δ) (ps := ps) ctx Θ A ψ =>
    Context.liftedSecondOrder κ _ (ctx.lifted S κ) (Θ.rename (Lifting.base S Δ).ren)
      (A.rename (Ren.liftN ps.length (Lifting.base S Δ).ren)) ψ

/-! ## Lifting of a Codata Type -/

/-- The instance of the variables of a type declaration that an instance of the variables of its
lifting holds. -/
def Instance.lifted {j g : Nat} (I : Instance (j + 1) (g + 3)) : Instance j g :=
  ⟨fun i => I.sorts i.castSucc, fun i => I.grades (i.castAdd 3)⟩

/-- The variables that a lifting adds, at an instance of its variables: its last sort variable, its
last level variable and its last three grade variables. -/
def Instance.liftingVariables {j g : Nat} (k : Nat) (I : Instance (j + 1) (g + 3)) :
    Lifting.Variables (k + 1) :=
  ⟨I.sorts (Fin.last j), .var (Fin.last k), I.grades (Fin.natAdd g 0), I.grades (Fin.natAdd g 1),
    I.grades (Fin.natAdd g 2)⟩

/-- The level variables of a type declaration, as level variables of its lifting. -/
def Level.lifted (i : Fin k) : Level (k + 1) := .var i.castSucc

/-- The instance `F.{s̄; l̄; p̄} ā` of the type `F` of the type declaration at its variables, among
those of its lifting, of which the parameter `y` is a term. -/
def TypeDeclaration.liftedInstance {Γ : Scope} (decl : TypeDeclaration) (F : Name)
    (I : Instance decl.sorts decl.grades) (as : InstanceArgs (decl.levels + 1) Γ decl.scope) :
    Term (decl.levels + 1) Γ :=
  .inst F (List.ofFn I.sorts) (List.ofFn Level.lifted) (List.ofFn I.grades) as

/-- `x̄. y.(T.d)(x̄)`: the observation of the parameter `y` of a lifting by the destructor `d` of
the type `F` that it lifts, in the scope of the parameters of `F` extended by `y`. -/
def TypeDeclaration.liftedObservation (decl : TypeDeclaration) (F : Name)
    (I : Instance decl.sorts decl.grades) (d : Name) (ps : List Parameter) :
    Term (decl.levels + 1) (Scope.extend (.var :: decl.scope) ps.length) :=
  Term.observation F (List.ofFn I.sorts) (List.ofFn Level.lifted) (List.ofFn I.grades)
    ((InstanceArgs.identity decl.scope).rename Ren.weaken) (.var₀ .zero) d ps

-- ADE: none.
/--
`F^S`: the lifting of the type `F` of the type declaration `decl` at its parameters at the positions
`S`, with the destructors `d̄'`, whose names are `ns`: a block of one codata type, over the
variables of `decl`, the quality `s_C` and the level `l_C` of the sort of the motives, and the
grades `r`, `ς` and `χ`, with the constraint of `decl`; its parameters are those of `decl`, each
parameter of `S` followed by its motive, and a term `y` of `F` at these parameters, and its sort has
the quality `s_C` and the level of `decl` joined to `l_C`.
It uses its parameters with the least grades, which state nothing, and declares no parameter in
which it is strictly positive.
RFC: `\mathsf{lifting}_{\mathcal{D}}`
-/
def TypeDeclaration.lifting (decl : TypeDeclaration) (F : Name) (S : List Nat) (ns : List Name)
    (body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + 1) (.var :: decl.scope.lifted S) ns) : TypeDeclaration where
  sorts := decl.sorts + 1
  levels := decl.levels + 1
  grades := decl.grades + 3
  constraint := fun I => decl.constraint I.lifted
  scope := .var :: decl.scope.lifted S
  params := fun I =>
    .var
      (((decl.params I.lifted).substLevels Level.lifted).lifted S
        ⟨I.sorts (Fin.last decl.sorts), .var (Fin.last decl.levels)⟩)
      (decl.liftedInstance F I.lifted
        ((InstanceArgs.identity decl.scope).rename (Lifting.base S decl.scope).ren))
  sort := fun I =>
    ⟨I.sorts (Fin.last decl.sorts),
      .max ((decl.sort I.lifted).level.subst Level.lifted) (.var (Fin.last decl.levels))⟩
  body := .codata [{
    name := Lifting.name F S
    usage := fun _ _ => .unrestrictedUnrestricted
    positive := fun _ => False
    destructors := ns
    body := body
  }]

-- ADE: none.
/-- The destructors `d̄'` are those of the lifting of the type `F` of the type declaration `decl` at
its parameters at the positions `S`: at each instance, they are the destructors of `F` lifted at the
parameter `y`.
RFC: `\uparrow_{\mathcal{D}}` -/
def TypeDeclaration.Lifts (decl : TypeDeclaration) (F : Name) (S : List Nat) {ns : List Name}
    (body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + 1) (.var :: decl.scope.lifted S) ns) : Prop :=
  ∃ T ∈ decl.codataTypes, T.name = F ∧
    ∀ I : Instance (decl.sorts + 1) (decl.grades + 3),
      Destructors.Lifts (I.liftingVariables decl.levels) (decl.liftedObservation F I.lifted)
        (Lifting.base S decl.scope).lift
        ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst
        ((T.body I.lifted).substLevels Level.lifted) (body I)

-- ADE: none.
/-- `F^S ∈ Σ`: the signature holds the lifting of its codata type `F` at its parameters at the
positions `S`.
RFC: `\in_{\uparrow}` -/
def Signature.HasLifting (sig : Signature) (F : Name) (S : List Nat) : Prop :=
  ∃ (decl : TypeDeclaration) (ns : List Name)
    (body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + 1) (.var :: decl.scope.lifted S) ns),
    .typeDeclaration decl ∈ sig ∧ decl.Lifts F S body ∧
      .typeDeclaration (decl.lifting F S ns body) ∈ sig

end Sic.Core
