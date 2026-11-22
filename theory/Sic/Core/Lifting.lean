module

public import Sic.Core.Nesting
public import Sic.Core.Positivity

/-!
# Liftings

The liftings of annex 13 of RFC 36: the lifting of a codata type at a set of its parameters is a
codata type declared from it, over a motive for each of these parameters and a term `y` of the
type, whose terms hold, for each observation of `y`, a term of the motive at each position of the
parameters in the result.
The recursive result of a field nested below the codata type has this type.

The lifting has the destructors of the codata type whose results mention a parameter lifted, each
at the arguments of its own, used as many times as the recursor that computes its result uses them,
the grade of the recursor times the factor of the result lifted, and its result is the result lifted
at the observation of `y`: a parameter becomes its motive at this observation, and an instance of a
declared type the instance of its lifting, a new value, owned alone.
The factor and the ownership of a result that is a motive are variables of the lifting, one each
for the motive of each parameter, which an instance gives: the recursive result of a motive may be
the result of the recursor, of the factor `11ᵖ` and of the ownership of the results of the
recursor, or, when an instance gives the motive the lifting of another type, a corecursor of this
lifting, of its own factor and owned alone.
The lifting is a relation, as the strict positivity is, whose cases it follows: its definition reads
which parameters occur in a term, and a term in which a variable does not occur is a term of the
scope without it.
It reads the signature for the level of the sort of a declared type and for the lifting that an
instance lifted names, which the signature declares: the motive of each parameter has a level of its
own, and a type lifted lives at the level of its instance joined to the levels of its motives.
The declaration of a lifting, which reads the syntax only, is thus before the relation.

The factor of the result of a destructor of a lifting is the grade that multiplies the uses of the
scope by the recursive result that this destructor observes.
The result of a destructor of a lifting is a motive, at the observation of the term lifted, of the
factor that the lifting gives this motive, or an instance of another lifting, whose recursive result
is a corecursor: an observation of it runs one branch, at the grade of its destructor, so that it
uses the scope as the meet of the grades of its destructors times their factors allows, as the
usage of a corecursor bounds its uses by those of each branch.
A lifting without destructor is never observed, and uses nothing, of the factor `00ᵖ`.
The factor reads the syntax, the liftings that the signature declares and the motives of the
lifting of the scope, and no judgment, and is a relation, as the lifting is: an instance of a
lifting that the signature does not declare has no factor.
The lifting of an instance reads the factor of the instance of the lifting that it gives, so that
the factor is before the relation.

The type of the recursive result of a field nested below a codata type is the type of the field
lifted at the types of its block, each of which has the motive of the recursor: an instance of a
type of the block is lifted to this motive, as a parameter lifted is.
The lifting follows the nesting of the field, which its declaration gives: the type of the field at
an instance may hold the types of the block elsewhere, where the declaration has a parameter, and
these are not positions of the block.

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

/-- The ownership of a result that is the constant `χ`, without factor, whatever the `n` arguments
are. -/
def Lifting.resultOwnership (χ : Grade) (n : Nat) : ResultOwnership Grade n :=
  ⟨some χ, fun _ => none⟩

/-- The grade and the requirement of the last entry of the telescope of a motive, the term at which
the motive is a type, which a type may use as it wants and of which it requires nothing. -/
def Lifting.termParam : Parameter := ⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩

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

/-- What a type lifted gives the result of a destructor of a lifting that has this type: the level
of its sort, its factor, the grade that multiplies the uses of the scope by the recursive result
that the destructor observes, and the ownership of this recursive result. -/
structure Lifting.Result (k : Nat) where
  /-- The level of the sort of the type lifted. -/
  level : Level k
  /-- The factor of the recursive result. -/
  factor : Grade
  /-- The ownership of the recursive result. -/
  ownership : Grade

/-- The grades of the results `m̄`, in order: the factor and the ownership of each. -/
def Lifting.Result.grades (ms : List (Lifting.Result k)) : List Grade :=
  ms.flatMap fun m => [m.factor, m.ownership]

/-- The motive of a type of a block, in a lifting of the scope `Γ` in the scope `Γ'`: the instance
`T` of this type, a type of `Γ`, the motive `z. C`, a type of `Γ'` over a term `z` of `T`, the
level of the sort of this motive, and the ownership `χ` of the results of the recursor, which this
motive is the type of. -/
structure Lifting.BlockMotive (k : Nat) (Γ' Γ : Scope) where
  /-- The instance `T` of the type of the block. -/
  type : Term k Γ
  /-- The motive `z. C`, over a term of the instance. -/
  motive : Term k (.var :: Γ')
  /-- The level of the sort of the motive. -/
  level : Level k
  /-- The ownership `χ` of the results of the recursor. -/
  ownership : Grade

/-- The motive `b` of a type of a block in the scope `Γ'` extended by a new entry. -/
def Lifting.BlockMotive.weaken {Γ' Γ : Scope} {e : Scope.Entry} (b : Lifting.BlockMotive k Γ' Γ) :
    Lifting.BlockMotive k (e :: Γ') Γ :=
  ⟨b.type, b.motive.rename (Ren.lift Ren.weaken), b.level, b.ownership⟩

/-- The motive `b` of a type of a block under a new entry of both scopes. -/
def Lifting.BlockMotive.lift {Γ' Γ : Scope} {e : Scope.Entry} (b : Lifting.BlockMotive k Γ' Γ) :
    Lifting.BlockMotive k (e :: Γ') (e :: Γ) :=
  ⟨b.type.rename Ren.weaken, b.motive.rename (Ren.lift Ren.weaken), b.level, b.ownership⟩

/-- A lifting of the scope `Γ` in the scope `Γ'`: each variable of `Γ` is a variable of `Γ'`, each
variable lifted has a motive in `Γ'`, with the level of the sort of this motive and the factor and
the ownership of the results that are this motive, and each type of a block lifted has its instance
and its motive.
The RFC finds them by the names of the variables and of the types. -/
structure Lifting (k : Nat) (Γ' Γ : Scope) where
  /-- The variable of `Γ'` that a variable of `Γ` is. -/
  ren : Ren Γ' Γ
  /-- The motive of a variable lifted, with the level of its sort and the factor and the ownership
  of the results that are this motive, none for the others. -/
  motive : ∀ {e : Scope.Entry}, Var Γ e → Option (Var Γ' e.motive × Lifting.Result k)
  /-- The motive of a type of the block, by its name, none for the other declared types. -/
  block : Name → Option (Lifting.BlockMotive k Γ' Γ)

namespace Lifting

/-- The lifting `ρ` under a new entry of both scopes, which is not lifted. -/
def lift {Γ' Γ : Scope} {e : Scope.Entry} (ρ : Lifting k Γ' Γ) :
    Lifting k (e :: Γ') (e :: Γ) where
  ren := Ren.lift ρ.ren
  motive := fun x =>
    match x with
    | .zero => none
    | .succ x => (ρ.motive x).map (Prod.map .succ id)
  block := fun D => (ρ.block D).map BlockMotive.lift

/-- The lifting `ρ` under `n` new variables of both scopes. -/
def liftN {Γ' Γ : Scope} : (n : Nat) → Lifting k Γ' Γ → Lifting k (Γ'.extend n) (Γ.extend n)
  | 0, ρ => ρ
  | n + 1, ρ => liftN n (lift ρ)

/-- The lifting `ρ` in the scope `Γ'` extended by a new entry. -/
def weaken {Γ' Γ : Scope} {e : Scope.Entry} (ρ : Lifting k Γ' Γ) : Lifting k (e :: Γ') Γ where
  ren := fun x => .succ (ρ.ren x)
  motive := fun x => (ρ.motive x).map (Prod.map .succ id)
  block := fun D => (ρ.block D).map BlockMotive.weaken

end Lifting

/-- No variable lifted occurs in the term `t`. -/
def Term.AvoidsLifted {Γ' Γ : Scope} (ρ : Lifting k Γ' Γ) (t : Term k Γ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Γ e), (ρ.motive x).isSome → t.Avoids x

/-- No variable lifted occurs in the arguments `t̄`. -/
def Args.AvoidsLifted {Γ' Γ : Scope} {ps : List Parameter} (ρ : Lifting k Γ' Γ) (ts : Args k Γ ps) :
    Prop :=
  ∀ {e : Scope.Entry} (x : Var Γ e), (ρ.motive x).isSome → ts.Avoids x

/-- The nestings `λ̄` of the arguments of an instance whose nesting is `(λ̄)`, the last one first,
and none for the other nestings, whose arguments have no position. -/
def Nest.args {α : Type} : Nest α → List (Nest α)
  | .inst ns => ns
  | _ => []

/-! ## Variables of a Lifting -/

/-- The sort and grade variables that a lifting adds to those of its type declaration, at an
instance, but those of its motives: the quality `s_C` of the sorts of the motives, the grade `r` of
the recursor that computes the terms of the lifting, and the requirement `ς` of its destructors on
the term that they observe.
The level of the sort of each motive, a level variable of the lifting, and the factor and the
ownership of the results that are this motive, two grade variables of the lifting, are with the
motive. -/
structure Lifting.Variables where
  /-- The quality `s_C` of the sorts of the motives. -/
  quality : Quality
  /-- The grade `r` of the recursor. -/
  recursion : Grade
  /-- The requirement `ς` of the destructors on the term that they observe. -/
  requirement : Grade

/-- The grades of an instance of a lifting: the grades `p̄` of the instance lifted, followed by the
grade `r` of the recursor, the requirement `ς`, and the factor and the ownership of the results that
are the motive of each parameter lifted, which the results `m̄` give, in order. -/
abbrev Lifting.Variables.grades (v : Lifting.Variables) (ps : List Grade)
    (ms : List (Lifting.Result k)) : List Grade :=
  ps ++ v.recursion :: v.requirement :: Lifting.Result.grades ms

/-- `F^Π`: the name of the lifting of the type `F` at the set `Π` of its parameters at the positions
`S`, in order, a name of the signature that `F` and `S` determine. -/
def Lifting.name (F : Name) (S : List Nat) : Name := .lifting F S

/-- The name of a lifting determines the type that it lifts and the positions of the parameters at
which it lifts it. -/
theorem Lifting.name_inj {D F : Name} {S' S : List Nat}
    (h : Lifting.name D S' = Lifting.name F S) : D = F ∧ S' = S := by
  cases h
  exact ⟨rfl, rfl⟩

/-- `l ⊔ ⨆ l̄`: the level `l` joined to each of the levels `l̄`.
RFC: `\textstyle\bigsqcup_l` -/
def Level.joins (l : Level k) (ls : List (Level k)) : Level k := ls.foldl .max l

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

/-- The lifting `ρ` extended by a parameter, lifted or not, whose motive has the level, the factor
and the ownership `m` if it is. -/
def Lifting.cons {Δ' Δ : Scope} {e : Scope.Entry} (m : Lifting.Result k) :
    (b : Bool) → Lifting k Δ' Δ → Lifting k (Scope.liftedCons b e Δ') (e :: Δ)
  | true, ρ =>
    { ren := fun x =>
        match x with
        | .zero => .succ .zero
        | .succ x => .succ (.succ (ρ.ren x))
      motive := fun x =>
        match x with
        | .zero => some (.zero, m)
        | .succ x => (ρ.motive x).map (Prod.map (fun y => .succ (.succ y)) id)
      block := (ρ.lift (e := e)).weaken.block }
  | false, ρ => ρ.lift

/-- The lifting of the parameters `Δ` in their scope lifted at the positions `S`, which lifts the
parameters at these positions, where `mv` gives the level, the factor and the ownership of the
motive of the parameter at each position, and no type of a block. -/
def Lifting.base (S : List Nat) (mv : Nat → Lifting.Result k) : (Δ : Scope) → Lifting k (Δ.lifted S) Δ
  | [] => { ren := (fun x => nomatch x), motive := (fun x => nomatch x), block := fun _ => none }
  | _ :: Δ => Lifting.cons (mv Δ.length) _ (Lifting.base S mv Δ)

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

/-- The parameters `Δ` in which each parameter at a position of `S` is followed by its motive, a
type over the telescope of the parameter and a term of it, of the sort of the quality `s` and of
the level that `mv` gives the position.
RFC: `\mathsf{params}_{\uparrow}` -/
def Context.lifted (S : List Nat) (s : Quality) (mv : Nat → Lifting.Result k) :
    {Δ : Scope} → Context k Δ → Context k (Δ.lifted S)
  | _, .empty => .empty
  | _, .var (Γ := Δ) ctx A =>
    Context.liftedVar ⟨s, (mv Δ.length).level⟩ _ (ctx.lifted S s mv)
      (A.rename (Lifting.base S mv Δ).ren)
  | _, .secondOrder (Γ := Δ) (ps := ps) ctx Θ A ψ =>
    Context.liftedSecondOrder ⟨s, (mv Δ.length).level⟩ _ (ctx.lifted S s mv)
      (Θ.rename (Lifting.base S mv Δ).ren)
      (A.rename (Ren.liftN ps.length (Lifting.base S mv Δ).ren)) ψ

/-! ## Declaration of a Lifting -/

/-- The number of the grade variables of the lifting of a type of the type declaration `decl` at
its parameters at the positions `S`: those of `decl`, the grade `r` of the recursor, the requirement
`ς`, and the factor `φ_Y` and the ownership `χ_Y` of the results that are the motive of each
parameter `Y` of `S`. -/
abbrev TypeDeclaration.liftingGrades (decl : TypeDeclaration) (S : List Nat) : Nat :=
  decl.grades + (2 + 2 * S.length)

/-- The instance of the variables of a type declaration that an instance of the variables of its
lifting at `n` parameters holds. -/
def Instance.lifted {j g n : Nat} (I : Instance (j + 1) (g + (2 + 2 * n))) : Instance j g :=
  ⟨fun i => I.sorts i.castSucc, fun i => I.grades (i.castAdd (2 + 2 * n))⟩

/-- The sort and grade variables that a lifting adds, at an instance of its variables, but those of
its motives: its last sort variable and the two grade variables after those of its type
declaration. -/
def Instance.liftingVariables {j g n : Nat} (I : Instance (j + 1) (g + (2 + 2 * n))) :
    Lifting.Variables :=
  ⟨I.sorts (Fin.last j), I.grades (Fin.natAdd g ⟨0, by omega⟩),
    I.grades (Fin.natAdd g ⟨1, by omega⟩)⟩

/-- The level variables of a type declaration, as level variables of its lifting, which has `n`
more. -/
def Level.lifted (n : Nat) (i : Fin k) : Level (k + n) := .var (i.castAdd n)

/-- `l_Y`: the level of the motive of the parameter at a position of `S`, the level variable of the
lifting, after the `k` of its type declaration, at the position of the parameter in `S`. -/
def Lifting.motiveLevel (k : Nat) (S : List Nat) (i : Nat) : Level (k + S.length) :=
  if h : S.idxOf i < S.length then .var (Fin.natAdd k ⟨S.idxOf i, h⟩) else .zero

/-- `φ_Y` (`o = 0`) or `χ_Y` (`o = 1`): the factor or the ownership of the results that are the
motive of the parameter at a position of `S`, the grade variable of the lifting, at an instance `I`
of its variables, after the `g` of its type declaration, `r` and `ς`, at twice the position of the
parameter in `S`, plus `o`. -/
def Lifting.motiveGrade {j g : Nat} (S : List Nat) (I : Instance j (g + (2 + 2 * S.length)))
    (o : Fin 2) (i : Nat) : Grade :=
  if h : S.idxOf i < S.length then I.grades (Fin.natAdd g ⟨2 + 2 * S.idxOf i + o, by omega⟩)
  else .unrestrictedUnrestricted

/-- The level, the factor and the ownership of the motive of the parameter at a position of `S`, in
the lifting of a type of the type declaration `decl` at the parameters at the positions `S`, at an
instance `I` of its variables. -/
def TypeDeclaration.liftingMotive (decl : TypeDeclaration) (S : List Nat)
    (I : Instance (decl.sorts + 1) (decl.liftingGrades S)) (i : Nat) :
    Lifting.Result (decl.levels + S.length) :=
  ⟨Lifting.motiveLevel decl.levels S i, Lifting.motiveGrade S I 0 i, Lifting.motiveGrade S I 1 i⟩

/-- The lifting of the scope of the type declaration `decl`, extended by the term `y`, in the scope
of the parameters of the lifting of a type of `decl` at its parameters at the positions `S`, at an
instance `I` of its variables: it lifts the parameters at these positions, each to its motive, and
not `y`. -/
def TypeDeclaration.liftingScope (decl : TypeDeclaration) (S : List Nat)
    (I : Instance (decl.sorts + 1) (decl.liftingGrades S)) :
    Lifting (decl.levels + S.length) (.var :: decl.scope.lifted S) (.var :: decl.scope) :=
  (Lifting.base S (decl.liftingMotive S I) decl.scope).lift

/-- The instance `F.{s̄; l̄; p̄} ā` of the type `F` of the type declaration at its variables, among
those of its lifting, of which the parameter `y` is a term. -/
def TypeDeclaration.liftedInstance {Γ : Scope} (decl : TypeDeclaration) (F : Name) (n : Nat)
    (I : Instance decl.sorts decl.grades) (as : InstanceArgs (decl.levels + n) Γ decl.scope) :
    Term (decl.levels + n) Γ :=
  .inst F (List.ofFn I.sorts) (List.ofFn (Level.lifted n)) (List.ofFn I.grades) as

/-- `x̄. y.(T.d)(x̄)`: the observation of the parameter `y` of a lifting by the destructor `d` of
the type `F` that it lifts, in the scope of the parameters of `F` extended by `y`. -/
def TypeDeclaration.liftedObservation (decl : TypeDeclaration) (F : Name) (n : Nat)
    (I : Instance decl.sorts decl.grades) (d : Name) (ps : List Parameter) :
    Term (decl.levels + n) (Scope.extend (.var :: decl.scope) ps.length) :=
  Term.observation F (List.ofFn I.sorts) (List.ofFn (Level.lifted n)) (List.ofFn I.grades)
    ((InstanceArgs.identity decl.scope).rename Ren.weaken) (.var₀ .zero) d ps

/-- The sort of the lifting of a type of the type declaration `decl` at its parameters at the
positions `S`, at an instance of its variables: the quality `s_C` of the sorts of the motives, and
the level of `decl` joined to the levels of the motives. -/
def TypeDeclaration.liftingSort (decl : TypeDeclaration) (S : List Nat)
    (I : Instance (decl.sorts + 1) (decl.liftingGrades S)) : Universe (decl.levels + S.length) :=
  ⟨I.sorts (Fin.last decl.sorts),
    ((decl.sort I.lifted).level.subst (Level.lifted S.length)).joins
      (List.ofFn fun i : Fin S.length => .var (Fin.natAdd decl.levels i))⟩

/--
`F^Π`: the lifting of the type `F` of the type declaration `decl` at its parameters at the positions
`S`, with the destructors `d̄'`, whose names are `ns`: a block of one codata type, over the
variables of `decl`, the quality `s_C` of the sorts of the motives, the level `l_Y` of the sort of
the motive of each parameter `Y` of `S`, the grades `r` and `ς`, and the factor `φ_Y` and the
ownership `χ_Y` of the results that are the motive of each parameter `Y` of `S`, with the
constraint of `decl`; its parameters are those of `decl`, each parameter of `S` followed by its motive, and a term
`y` of `F` at these parameters, and its sort has the quality `s_C` and the level of `decl` joined to
the levels of the motives.
It uses its parameters with the least grades, which state nothing, and declares no parameter in
which it is strictly positive.
RFC: `\mathsf{lifting}_{\mathcal{D}}`
-/
def TypeDeclaration.lifting (decl : TypeDeclaration) (F : Name) (S : List Nat) (ns : List Name)
    (body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns) : TypeDeclaration where
  sorts := decl.sorts + 1
  levels := decl.levels + S.length
  grades := decl.liftingGrades S
  constraint := fun I => decl.constraint I.lifted
  scope := .var :: decl.scope.lifted S
  params := fun I =>
    .var
      (((decl.params I.lifted).substLevels (Level.lifted S.length)).lifted S
        (I.sorts (Fin.last decl.sorts)) (decl.liftingMotive S I))
      (decl.liftedInstance F S.length I.lifted
        ((InstanceArgs.identity decl.scope).rename
          (Lifting.base S (decl.liftingMotive S I) decl.scope).ren))
  sort := decl.liftingSort S
  body := .codata [{
    name := Lifting.name F S
    usage := fun _ _ => .unrestrictedUnrestricted
    positive := fun _ => false
    destructors := ns
    body := body
  }]

/-! ## Factors -/

/-- The meet of a grade and of the meet of a list of grades, the latter absent when the list is
empty: the meet of the grades of a list of destructors, of which there may be none. -/
def _root_.Sic.Grading.Grade.meetWith (p : Grade) : Option Grade → Grade
  | none => p
  | some q => p ⊓ q

/-- A meet of a grade with the meet of a list of grades has no use at run time only when the grade
has none. -/
theorem _root_.Sic.Grading.Grade.run_meetWith_eq_zero (p : Grade) :
    (q : Option Grade) → (p.meetWith q).run = .zero → p.run = .zero
  | none, h => h
  | some _, h => (Multiplicity.modality.zero.meet_eq_zero _ _ h).1

mutual

/-- `Σ ⊢ factor(B) = π`: the result `B` of a destructor of a lifting has the factor `π`, where `ρ`
gives the variables lifted and their motives: the motive of a variable lifted, at its arguments, has
the factor that `ρ` gives it, and an instance of a lifting that the signature declares the meet of
the grades of its destructors times the factors of their results, or `00ᵖ` without destructor. -/
inductive Term.Factor (sig : Signature) :
    {k : Nat} → {Γ' Γ : Scope} → Lifting k Γ' Γ → Term k Γ' → Grade → Prop where
  /-- The motive of a variable lifted, at its arguments.
  RFC: `\mathsf{factor}_X` -/
  | var {k : Nat} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {a : Scope.Entry} {x : Var Γ a}
      {y : Var Γ' a.motive} {m : Lifting.Result k} (hx : ρ.motive x = some (y, m))
      (ts : Args k Γ' a.motive.params) :
      Term.Factor sig ρ (.var y ts) m.factor
  /-- An instance of the lifting of the type `D` of the type declaration `decl`, which the signature
  declares, whose destructors at this instance have the meet `π`, if any, where the lifting of the
  scope of `decl` gives the variables lifted and their motives.
  RFC: `\mathsf{factor}_D` -/
  | inst {k : Nat} {Γ' Γ Δ : Scope} {ρ : Lifting k Γ' Γ} {decl : TypeDeclaration} {D : Name}
      {S : List Nat} {ns : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ' Δ}
      {π : Option Grade} (hdecl : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names)
      (h : .typeDeclaration (decl.lifting D S ns body) ∈ sig)
      (hqp : Instance.AsMany (decl.sorts + 1) (decl.liftingGrades S) qs ps)
      (hds : Destructors.Factor sig (decl.liftingScope S hqp.inst)
        (body hqp.inst) π) :
      Term.Factor sig ρ (.inst (Lifting.name D S) qs ls ps as) (π.getD .noneNone)

/-- `Σ ⊢ factor(d̄) = π`: the destructors `d̄` have the meet `π` of their grades times the factors
of their results, absent when there is no destructor, where `ρ` gives the variables lifted and their
motives. -/
inductive Destructors.Factor (sig : Signature) :
    {k : Nat} → {Γ' Γ : Scope} → Lifting k Γ' Γ → {ns : List Name} → Destructors k Γ' ns →
      Option Grade → Prop where
  /-- No destructor.
  RFC: `\mathsf{factor}_{\bar d\varepsilon}` -/
  | nil {k : Nat} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} :
      Destructors.Factor sig ρ (.nil : Destructors k Γ' []) none
  /-- A destructor, of the grade `p`, whose result has the factor `π`, followed by destructors of the
  meet `π'`.
  RFC: `\mathsf{factor}_{\bar d,}` -/
  | cons {k : Nat} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {d : Name} {ns : List Name}
      {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Γ' ps}
      {B : Term k (Γ'.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Γ') ns} {π : Grade} {π' : Option Grade}
      (hB : Term.Factor sig (ρ.liftN ps.length) B π) (hds : Destructors.Factor sig ρ.weaken ds π') :
      Destructors.Factor sig ρ (.cons (d := d) p q ς Θ B ψ ds) (some ((p * π).meetWith π'))

end

/-! ## Liftings of Types -/

mutual

/--
`Σ ⊢ A ↑_λ u = A' : (s_C)_l ▷ π; χ'`: the type `A'`, of the level `l`, is the type `A`, whose
nesting is `n`, lifted at the term `e` of `A`, and the recursive result that it is the type of has
the factor `π` and the ownership `χ'`, which `m` gathers, where `ρ` gives the variables and the
types of the block lifted, their motives and what these give the results, and `v` the variables of
the lifting.
-/
inductive Term.Lifts (sig : Signature) (v : Lifting.Variables) :
    {Γ' Γ : Scope} → Lifting k Γ' Γ → Nest Name → Term k Γ' → Term k Γ → Term k Γ' →
      Lifting.Result k → Prop where
  /-- A variable lifted, applied to arguments in which no variable lifted occurs, without position:
  its motive, at these arguments and at the term, of the level, the factor and the ownership that
  `ρ` gives the motive.
  RFC: `\uparrow_X` -/
  | var {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {e : Term k Γ'} {a : Scope.Entry} {x : Var Γ a}
      {y : Var Γ' a.motive} {m : Lifting.Result k} {ts : Args k Γ a.params}
      (hx : ρ.motive x = some (y, m)) (hts : ts.AvoidsLifted ρ) :
      Term.Lifts sig v ρ .plain e (.var x ts) (.var y ((ts.rename ρ.ren).snoc e)) m
  /-- An instance of a type of the block lifted, at a position that holds this type: the motive of
  this type at the term, of the level of the motive, the factor `11ᵖ`, since its recursive result
  runs the recursor once, and the ownership `χ` of the results of the recursor.
  The position tells that the instance is the one that the motive is over, which a well-formed
  declaration ensures, so the rule does not compare them.
  RFC: `\uparrow_T` -/
  | block {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {e : Term k Γ'} {Δ : Scope} {D : Name}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
      {b : Lifting.BlockMotive k Γ' Γ} (hD : ρ.block D = some b) :
      Term.Lifts sig v ρ (.direct D) e (.inst D qs ls ps as) (b.motive.subst₀ (Subst₀.single e))
        ⟨b.level, .linearLinear, b.ownership⟩
  /-- An instance of a declared type whose nesting is not a position, of which an argument at least
  is lifted: the instance of the lifting of this type at the parameters of these arguments, which
  the signature declares, with some destructors, at the variables of the lifting, at the levels, the
  factors and the ownerships of the arguments lifted, at these arguments and at the term, of the
  level of the instance joined to these levels, of its factor `π`, and of the ownership `11ᵖ`, since
  its recursive result is a new value, a corecursor.
  RFC: `\uparrow_D` -/
  | inst {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n : Nest Name} {e : Term k Γ'}
      {decl : TypeDeclaration} {Δ' : Scope}
      {D : Name} {qs : List Quality} {ls : List (Level k)} {ms : List (Lifting.Result k)}
      {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} {S : List Nat} {as' : InstanceArgs k Γ' Δ'}
      {ns : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
      (h : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names) (hn : ∀ E, n ≠ .direct E)
      (hqp : Instance.AsMany decl.sorts decl.grades qs ps) (hl : ls.length = decl.levels)
      {π : Grade}
      (has : InstanceArgs.Lifts sig v ρ n.args as S ms as') (hS : S ≠ [])
      (hL : .typeDeclaration (decl.lifting D S ns body) ∈ sig)
      (hπ : Term.Factor sig ρ
        (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms.map (·.level)) (v.grades ps ms)
          (.snoc (e := .var) as' e)) π) :
      Term.Lifts sig v ρ n e (.inst D qs ls ps as)
        (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms.map (·.level)) (v.grades ps ms)
          (.snoc (e := .var) as' e))
        ⟨((decl.sort hqp.inst).level.subst (ls.getFin hl)).joins (ms.map (·.level)),
          π, .linearLinear⟩

/--
`Σ ⊢ ā ↑_λ̄ = (Π'; l̄; ḡ; ā')`: the arguments `ā'` are the arguments `ā` of an instance lifted,
whose nestings are `ns`, the last one first, and none for the arguments after those of `ns`, `S` the
positions of the parameters `Π'` whose arguments are lifted, in order, and `m̄` the levels `l̄` of
these arguments lifted and the factors and the ownerships `ḡ` of the recursive results that they
are the types of: the argument of such a parameter is followed by its motive, the argument lifted
at a term of its own, and the others, in which nothing is lifted, are kept.
-/
inductive InstanceArgs.Lifts (sig : Signature) (v : Lifting.Variables) :
    {Γ' Γ : Scope} → Lifting k Γ' Γ → List (Nest Name) → {Δ : Scope} → InstanceArgs k Γ Δ →
      List Nat → List (Lifting.Result k) → {Δ' : Scope} → InstanceArgs k Γ' Δ' → Prop where
  /-- No argument.
  RFC: `\uparrow_{\bar a\varepsilon}` -/
  | nil {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {ns : List (Nest Name)} :
      InstanceArgs.Lifts sig v ρ ns .nil [] [] .nil
  /-- An argument that is lifted, followed by its motive.
  RFC: `\uparrow_{\bar a,}` -/
  | lifted {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {ns : List (Nest Name)} {Δ Δ' : Scope}
      {a : Scope.Entry}
      {as : InstanceArgs k Γ Δ} {S : List Nat} {ms : List (Lifting.Result k)} {m : Lifting.Result k}
      {as' : InstanceArgs k Γ' Δ'} {B : Term k (Γ.extend a.params.length)}
      {B' : Term k (.var :: Γ'.extend a.params.length)}
      (has : InstanceArgs.Lifts sig v ρ ns.tail as S ms as')
      (hB : Term.Lifts sig v (ρ.liftN a.params.length).weaken (ns.headD .plain) (.var₀ .zero) B B'
        m) :
      InstanceArgs.Lifts sig v ρ ns (.snoc as B) (S ++ [Δ.length]) (ms ++ [m])
        (.snoc (e := a.motive) (.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren)))
          (Scope.extend_snoc Γ' a.params Lifting.termParam ▸ B'))
  /-- An argument in which no variable lifted occurs, and whose nesting has no position.
  RFC: `\uparrow_{\bar a\notin}` -/
  | absent {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {ns : List (Nest Name)} {Δ Δ' : Scope}
      {a : Scope.Entry}
      {as : InstanceArgs k Γ Δ} {S : List Nat} {ms : List (Lifting.Result k)} {as' : InstanceArgs k Γ' Δ'}
      {B : Term k (Γ.extend a.params.length)} (has : InstanceArgs.Lifts sig v ρ ns.tail as S ms as')
      (hB : B.AvoidsLifted (ρ.liftN a.params.length))
      (hn : ns.headD .plain = .plain) :
      InstanceArgs.Lifts sig v ρ ns (.snoc as B) S ms
        (.snoc as' (B.rename (Ren.liftN a.params.length ρ.ren)))

end

/-! ## Liftings of Destructors -/

/-- The parameter `p` of an argument of a destructor, in the lifting: the argument is used `r` times
more, by the recursor of the grade `r` times the factor of the result lifted, and its requirement is
kept. -/
def Parameter.scale (r : Grade) (p : Parameter) : Parameter := ⟨r * p.usage, p.requirement⟩

/-- `r · Θ`: the telescope `Θ` whose entries are used `r` times more, and whose variables the types
after them use with the least grade, which states nothing: the result of a destructor of a lifting
uses its arguments more than the result that it lifts.
RFC: `\mathsf{scale}_\Theta` -/
def Telescope.scale (r : Grade) : {Γ : Scope} → {ps : List Parameter} → Telescope k Γ ps →
    Telescope k Γ (ps.map (Parameter.scale r))
  | _, _, .nil => .nil
  | _, _, .cons _ p A Θ => .cons .unrestrictedUnrestricted (p.scale r) A (Θ.scale r)

/-- `p'`: the grade of the result of a destructor of a lifting whose motives have the quality `s`,
from the grade `p` of the destructor lifted: the grade of the mode of `p`, since an observation
reads the grade of its destructor by its mode only, without use at run time when the motives are
propositions.
RFC: `\mathsf{grade}_{\uparrow}` -/
def Lifting.resultGrade (s : Quality) (p : Grade) : Grade :=
  match s with
  | .type => p.mode.grade
  | .prop => (p.mode.mul .zeroOne).grade

/-- The grade of the result of a destructor of a lifting has no use at run time when the grade of
the destructor lifted has none. -/
theorem Lifting.resultGrade_run_eq_zero :
    ∀ (s : Quality) (p : Grade), p.run = .zero → (Lifting.resultGrade s p).run = .zero := by
  decide

/--
`Σ ⊢ d̄ ↑ y = d̄'`: the destructors `d̄'` are the destructors `d̄` of a codata type lifted at the term
`y` of this type, where `κ` is the sort of the lifting, `o` gives the observation of `y` by each
destructor, `θ` these observations for the destructors before `d̄`, on which `d̄` depend, and `ρ` the
variables lifted and their motives.
-/
inductive Destructors.Lifts {Γ₀ : Scope} (sig : Signature) (v : Lifting.Variables) (κ : Universe k)
    (o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)) :
    {Γ' : Scope} → Lifting k Γ' Γ₀ → {Ξ : Scope} → Subst k Γ₀ Ξ → {ns : List Name} →
      Destructors k Ξ ns → {ns' : List Name} → Destructors k Γ' ns' → Prop where
  /-- No destructor.
  RFC: `\uparrow_{\bar d\varepsilon}` -/
  | nil {Γ' : Scope} {ρ : Lifting k Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} :
      Destructors.Lifts sig v κ o ρ @θ .nil .nil
  /-- A destructor whose result is lifted at the observation of `y` by it, in a sort that the sort
  of the lifting bounds: the lifting has it, at its arguments, used `r` times the factor `π` of the
  result lifted more, with this result, of the ownership `χ'` that the lifting gives it, and the
  requirement `ς`, and no destructor after it depends on it.
  RFC: `\uparrow_{\bar d|}` -/
  | lifted {Γ' : Scope} {ρ : Lifting k Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} {d : Name}
      {ns ns' : List Name} {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Ξ) ns} {B' : Term k (Γ'.extend ps.length)}
      {m : Lifting.Result k}
      {ds' : Destructors k
        (.secondOrder (ps.map (Parameter.scale (v.recursion * m.factor)))
          (Lifting.resultOwnership m.ownership _) :: Γ') ns'}
      (hB : Term.Lifts sig v (ρ.liftN ps.length) .plain
        ((o d ps).rename (Ren.liftN ps.length ρ.ren))
        (B.subst (Subst.liftN ps.length θ)) B' m)
      (hκ : (⟨v.quality, m.level⟩ : Universe k) ≼ κ)
      (hds : Destructors.Lifts sig v κ o ρ.weaken (θ.snoc (e := .secondOrder ps ψ) (o d ps)) ds ds') :
      Destructors.Lifts sig v κ o ρ @θ (.cons (d := d) p q ς Θ B ψ ds)
        (.cons (d := d) (Lifting.resultGrade v.quality p) .zero v.requirement
          (((Θ.subst θ).rename ρ.ren).scale (v.recursion * m.factor))
          ((List.length_map (Parameter.scale (v.recursion * m.factor))).symm ▸ B')
          (Lifting.resultOwnership m.ownership _) ds')
  /-- A destructor in whose result no variable lifted occurs, which the lifting does not have.
  RFC: `\uparrow_{\bar d\notin}` -/
  | absent {Γ' : Scope} {ρ : Lifting k Γ' Γ₀} {Ξ : Scope} {θ : Subst k Γ₀ Ξ} {d : Name}
      {ns ns' : List Name} {ps : List Parameter} {p q ς : Grade} {Θ : Telescope k Ξ ps}
      {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Ξ) ns} {ds' : Destructors k Γ' ns'}
      (hB : (B.subst (Subst.liftN ps.length θ)).AvoidsLifted (ρ.liftN ps.length))
      (hds : Destructors.Lifts sig v κ o ρ (θ.snoc (e := .secondOrder ps ψ) (o d ps)) ds ds') :
      Destructors.Lifts sig v κ o ρ @θ (.cons (d := d) p q ς Θ B ψ ds) ds'

/-! ## Signatures That Hold a Lifting -/

/-- `Σ; 𝒟 ⊢ D ↑_Π d̄'`: the destructors `d̄'` are those of the lifting of the type `F` of the type
declaration `decl` at its parameters at the positions `S`: at each instance, they are the
destructors of `F` lifted at the parameter `y`, in the sort of the lifting.
RFC: `\uparrow_{\mathcal{D}}` -/
def TypeDeclaration.Lifts (sig : Signature) (decl : TypeDeclaration) (F : Name) (S : List Nat)
    {ns : List Name}
    (body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns) : Prop :=
  ∃ T ∈ decl.codataTypes, T.name = F ∧
    ∀ I : Instance (decl.sorts + 1) (decl.liftingGrades S),
      Destructors.Lifts sig I.liftingVariables (decl.liftingSort S I)
        (decl.liftedObservation F S.length I.lifted) (decl.liftingScope S I)
        ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst
        ((T.body I.lifted).substLevels (Level.lifted S.length)) (body I)

/-- `F^Π ∈ Σ`: the signature holds the lifting of its codata type `F` at its parameters at the
positions `S`.
RFC: `\in_{\uparrow}` -/
def Signature.HasLifting (sig : Signature) (F : Name) (S : List Nat) : Prop :=
  ∃ (decl : TypeDeclaration) (ns : List Name)
    (body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns),
    .typeDeclaration decl ∈ sig ∧ decl.Lifts sig F S body ∧
      .typeDeclaration (decl.lifting F S ns body) ∈ sig

end Sic.Core
