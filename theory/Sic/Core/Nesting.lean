module

public import Sic.Core.Syntax
import Sic.Core.Syntax.Terms

/-!
# Nesting

The nesting of annex 08 of RFC 36: the positions at which the types of a block occur in the type of
a field, as a tree, which is no position when none of them occurs, the type of the block when the
type is an instance of it, and, when the type is an instance of another declared type, the nesting
of each of its arguments.
A field is recursive when its nesting is a type of the block, and nested when its nesting is that
of an instance: the nestings of the fields of a constructor hold the names of the types of the
block.

The nesting reads the syntax alone, once, on the declaration: a substitution keeps the instances
of a type, and so its nesting, while it may bring a type of the block where the declaration has a
parameter, which is no position of the block.
It reads the instances only, and neither the terms nor the parameters in which a declared type is
strictly positive: the formation of a declaration checks them.

The RFC names the variables, so that one `Λ` gives their nestings to the variables it names, no
position to the others, and their objects to the types of the block; with de Bruijn indices, the
nestings of the variables of a scope are a function of its variables, extended by no position under
each variable that an abstraction binds, and the objects of the types of the block a function of
the names.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α : Type}

/-! ## Nestings -/

/-- `⊥`, `h` or `(λ̄)`: the nesting of a type, the positions at which it holds what `α` gives for
the types of a block.
RFC: `\mathsf{syntax}_\lambda` -/
inductive Nest (α : Type) where
  /-- `⊥`: no position. -/
  | plain : Nest α
  /-- `h`: a position, which holds `a`. -/
  | direct (a : α) : Nest α
  /-- `(λ̄)`: an instance of a declared type, with the nesting of each of its arguments, the last
  one first, as the arguments are. -/
  | inst (ns : List (Nest α)) : Nest α

/-- The nesting has no position. -/
def Nest.isPlain : Nest α → Bool
  | .plain => true
  | _ => false

/-- `nest(λ̄)`: the nesting of an instance whose arguments have the nestings `λ̄`: no position when
none of them has one.
RFC: `\mathsf{nest}_{\bar\lambda}` -/
def Nest.ofArgs (ns : List (Nest α)) : Nest α :=
  if ns.all Nest.isPlain then .plain else .inst ns

mutual

/-- `λ ↦ h`: the nesting `λ` whose positions hold what `f` gives for the objects that those of
`λ` hold.
RFC: `\mathsf{map}_\lambda` -/
def Nest.map {β : Type} (f : α → β) : Nest α → Nest β
  | .plain => .plain
  | .direct a => .direct (f a)
  | .inst ns => .inst (Nest.mapList f ns)

/-- The nestings `λ̄` of the arguments of an instance, each mapped by `f`. -/
def Nest.mapList {β : Type} (f : α → β) : List (Nest α) → List (Nest β)
  | [] => []
  | n :: ns => n.map f :: Nest.mapList f ns

end

/-- The nestings of the variables of the scope `Γ`. -/
abbrev Nesting (α : Type) (Γ : Scope) : Type := ∀ {e : Scope.Entry}, Var Γ e → Nest α

namespace Nesting

/-- The nestings of the variables of a scope none of which has a position. -/
def plain {Γ : Scope} : Nesting α Γ := fun _ => .plain

/-- The nestings `ν` under a new entry, which has no position. -/
def lift {Γ : Scope} {e : Scope.Entry} (ν : Nesting α Γ) : Nesting α (e :: Γ) := fun x =>
  match x with
  | .zero => .plain
  | .succ x => ν x

/-- The nestings `ν` under `n` new variables. -/
def liftN {Γ : Scope} : (n : Nat) → Nesting α Γ → Nesting α (Γ.extend n)
  | 0, ν => ν
  | n + 1, ν => liftN n (lift ν)

/-- `Δ ↦ λ̄`: the nestings of the parameters of a declared type at an instance whose arguments have
the nestings `λ̄`, the last one first.
RFC: `\mathsf{nest}_\Delta` -/
def ofArgs : {Δ : Scope} → List (Nest α) → Nesting α Δ
  | _ :: _, n :: _, _, .zero => n
  | _ :: _, _ :: ns, _, .succ x => ofArgs ns x
  | _, _, _, _ => .plain

end Nesting

/-! ## Nesting of a Type -/

mutual

/-- `nest_Λ(A)`: the nesting of the type `A`, where `mark` gives the types of the block what their
positions hold and `ν` the nestings of the variables: that of a variable applied to arguments is the nesting of the variable,
that of an instance of a type of the block is this type, and that of an instance of another
declared type is the nesting of its arguments.
RFC: `\mathsf{nest}_A` -/
def Term.nest {Γ : Scope} (mark : Name → Option α) (ν : Nesting α Γ) : Term k Γ → Nest α
  | .var x _ => ν x
  | .inst D _ _ _ as =>
    match mark D with
    | some a => .direct a
    | none => Nest.ofArgs (as.nest mark ν)
  | _ => .plain

/-- `nest_Λ(ā)`: the nesting of each of the arguments `ā` of an instance, the last one first,
under the variables that its abstraction binds.
RFC: `\mathsf{nest}_{\bar a}` -/
def InstanceArgs.nest {Γ Δ : Scope} (mark : Name → Option α) (ν : Nesting α Γ) :
    InstanceArgs k Γ Δ → List (Nest α)
  | .nil => []
  | .snoc as B => B.nest mark (ν.liftN _) :: as.nest mark ν

end

/-- A nesting with a position is not plain. -/
theorem Nest.isPlain_eq_false {n : Nest α} (h : n ≠ .plain) : n.isPlain = false := by
  cases n with
  | plain => exact absurd rfl h
  | direct _ => rfl
  | inst _ => rfl

/-- Nestings without position stay so under a new entry. -/
theorem Nesting.lift_plain {Γ : Scope} {e₀ : Scope.Entry} {ν : Nesting α Γ}
    (h : ∀ (e : Scope.Entry) (x : Var Γ e), ν x = .plain) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Γ) e), Nesting.lift @ν x = .plain :=
  fun _ x =>
    match x with
    | .zero => rfl
    | .succ x => h _ x

/-- Nestings without position stay so under new variables. -/
theorem Nesting.liftN_plain :
    {Γ : Scope} → (n : Nat) → {ν : Nesting α Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), ν x = .plain) →
      ∀ (e : Scope.Entry) (x : Var (Γ.extend n) e), Nesting.liftN n @ν x = .plain
  | _, 0, _, h => h
  | _, n + 1, _, h => Nesting.liftN_plain n (Nesting.lift_plain h)

mutual

/-- A type has no position when no variable has one and no declared type holds one. -/
theorem Term.nest_plain :
    {Γ : Scope} → {ν : Nesting α Γ} → (∀ (e : Scope.Entry) (x : Var Γ e), ν x = .plain) →
      (A : Term k Γ) → A.nest (fun _ => none) @ν = .plain
  | _, _, h, .var x _ => h _ x
  | _, _, h, .inst _ _ _ _ as => by
    show Nest.ofArgs (as.nest (fun _ => none) _) = .plain
    rw [Nest.ofArgs, InstanceArgs.nest_plain h as]
    rfl
  | _, _, _, .sort _ => rfl
  | _, _, _, .const _ _ _ _ => rfl
  | _, _, _, .ctor _ _ _ _ _ _ _ => rfl
  | _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .obs _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .corec _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .equality .. | _, _, _, .refl .. | _, _, _, .transp .. | _, _, _, .propExt .. => rfl
  | _, _, _, .coind .. => rfl

/-- The arguments of an instance have no position when no variable has one and no declared type
holds one. -/
theorem InstanceArgs.nest_plain :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → (∀ (e : Scope.Entry) (x : Var Γ e), ν x = .plain) →
      (as : InstanceArgs k Γ Δ) → (as.nest (fun _ => none) @ν).all Nest.isPlain = true
  | _, _, _, _, .nil => rfl
  | _, _, _, h, .snoc as B => by
    rw [InstanceArgs.nest, List.all_cons, Term.nest_plain (Nesting.liftN_plain _ h) B,
      InstanceArgs.nest_plain h as]
    rfl

end

/-- The nesting of an instance has no position when none of its arguments has one. -/
theorem Nest.isPlain_ofArgs (ns : List (Nest α)) :
    (Nest.ofArgs ns).isPlain = ns.all Nest.isPlain := by
  unfold Nest.ofArgs
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i h
    rw [Bool.not_eq_true] at h
    rw [h]
    rfl

/-- Nestings that give a position to less variables than others still do under a new entry. -/
theorem Nesting.lift_isPlain_mono {β : Type} {Γ : Scope} {e₀ : Scope.Entry} {ν : Nesting α Γ}
    {ν' : Nesting β Γ}
    (h : ∀ (e : Scope.Entry) (x : Var Γ e), (ν' x).isPlain = true → (ν x).isPlain = true) :
    ∀ (e : Scope.Entry) (x : Var (e₀ :: Γ) e),
      (Nesting.lift @ν' x).isPlain = true → (Nesting.lift @ν x).isPlain = true :=
  fun _ x =>
    match x with
    | .zero => fun _ => rfl
    | .succ x => h _ x

/-- Nestings that give a position to less variables than others still do under new variables. -/
theorem Nesting.liftN_isPlain_mono {β : Type} :
    {Γ : Scope} → (n : Nat) → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν' x).isPlain = true → (ν x).isPlain = true) →
      ∀ (e : Scope.Entry) (x : Var (Γ.extend n) e),
        (Nesting.liftN n @ν' x).isPlain = true → (Nesting.liftN n @ν x).isPlain = true
  | _, 0, _, _, h => h
  | _, n + 1, _, _, h => Nesting.liftN_isPlain_mono n (Nesting.lift_isPlain_mono h)

/-- Nestings that give a position to the same variables still do under new variables. -/
theorem Nesting.liftN_isPlain_congr {β : Type} {Γ : Scope} (n : Nat) {ν : Nesting α Γ}
    {ν' : Nesting β Γ}
    (h : ∀ (e : Scope.Entry) (x : Var Γ e), (ν x).isPlain = (ν' x).isPlain) :
    ∀ (e : Scope.Entry) (x : Var (Γ.extend n) e),
      (Nesting.liftN n @ν x).isPlain = (Nesting.liftN n @ν' x).isPlain :=
  fun e x => Bool.eq_iff_iff.2
    ⟨Nesting.liftN_isPlain_mono n (fun e x hx => h e x ▸ hx) e x,
      Nesting.liftN_isPlain_mono n (fun e x hx => (h e x).symm ▸ hx) e x⟩

mutual

/-- A type without position, where no declared type holds one, has none at nestings that give a
position to less variables. -/
theorem Term.nest_isPlain_mono {β : Type} :
    {Γ : Scope} → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν' x).isPlain = true → (ν x).isPlain = true) →
      (A : Term k Γ) → (A.nest (fun _ => none) @ν').isPlain = true →
        (A.nest (fun _ => none) @ν).isPlain = true
  | _, _, _, h, .var x _ => h _ x
  | _, _, _, h, .inst _ _ _ _ as => fun hA => by
    rw [Term.nest, Nest.isPlain_ofArgs] at hA ⊢
    exact InstanceArgs.nest_isPlain_mono h as hA
  | _, _, _, _, .sort _ => fun _ => rfl
  | _, _, _, _, .const _ _ _ _ => fun _ => rfl
  | _, _, _, _, .ctor _ _ _ _ _ _ _ => fun _ => rfl
  | _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => fun _ => rfl
  | _, _, _, _, .obs _ _ _ _ _ _ _ _ => fun _ => rfl
  | _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => fun _ => rfl
  | _, _, _, _, .equality .. | _, _, _, _, .refl .. | _, _, _, _, .transp ..
  | _, _, _, _, .propExt .. | _, _, _, _, .coind .. => fun _ => rfl

/-- The arguments of an instance without position, where no declared type holds one, have none at
nestings that give a position to less variables. -/
theorem InstanceArgs.nest_isPlain_mono {β : Type} :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → {ν' : Nesting β Γ} →
      (∀ (e : Scope.Entry) (x : Var Γ e), (ν' x).isPlain = true → (ν x).isPlain = true) →
      (as : InstanceArgs k Γ Δ) → (as.nest (fun _ => none) @ν').all Nest.isPlain = true →
        (as.nest (fun _ => none) @ν).all Nest.isPlain = true
  | _, _, _, _, _, .nil => fun _ => rfl
  | _, _, _, _, h, .snoc as B => fun has => by
    rw [InstanceArgs.nest, List.all_cons, Bool.and_eq_true] at has ⊢
    exact ⟨Term.nest_isPlain_mono (Nesting.liftN_isPlain_mono _ h) B has.1,
      InstanceArgs.nest_isPlain_mono h as has.2⟩

end

/-- A type has a position at nestings of its variables when it has one at nestings that give a
position to the same variables, and no declared type holds one. -/
theorem Term.nest_isPlain_congr {β : Type} {Γ : Scope} {ν : Nesting α Γ} {ν' : Nesting β Γ}
    (h : ∀ (e : Scope.Entry) (x : Var Γ e), (ν x).isPlain = (ν' x).isPlain) (A : Term k Γ) :
    (A.nest (fun _ => none) @ν).isPlain = (A.nest (fun _ => none) @ν').isPlain :=
  Bool.eq_iff_iff.2 ⟨Term.nest_isPlain_mono (fun e x hx => (h e x).symm ▸ hx) A,
    Term.nest_isPlain_mono (fun e x hx => h e x ▸ hx) A⟩

/-- One of the arguments of an instance has a nesting with a position when not all of them have
none. -/
theorem InstanceArgs.exists_ofArgs (mark : Name → Option α) {Γ : Scope} {ν : Nesting α Γ} :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → (as.nest mark @ν).all Nest.isPlain = false →
      ∃ (e : Scope.Entry) (y : Var Δ e), (Nesting.ofArgs (as.nest mark @ν) y).isPlain = false
  | _, .nil, h => nomatch h
  | _, .snoc as B, h => by
    rw [InstanceArgs.nest, List.all_cons] at h
    cases hB : (B.nest mark (Nesting.liftN _ @ν)).isPlain with
    | false => exact ⟨_, .zero, hB⟩
    | true =>
      rw [hB, Bool.true_and] at h
      obtain ⟨e, y, hy⟩ := InstanceArgs.exists_ofArgs mark as h
      exact ⟨e, .succ y, hy⟩

/-! ## Nesting of the Fields of a Block -/

/-- `nest_𝒟(A)`: the nesting of the type `A` of a field of a block whose types are named `names`,
whose positions hold the names of these types, and whose variables have no position.
RFC: `\mathsf{nest}_{\mathcal{D}}` -/
def Term.blockNest {Γ : Scope} (names : List Name) (A : Term k Γ) : Nest Name :=
  A.nest (fun D => if D ∈ names then some D else none) Nesting.plain

/-- `nest_𝒟(Θ)`: the nesting of the type of each entry of a telescope, in order.
RFC: `\mathsf{nest}_\Theta` -/
def Telescope.nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → Telescope k Γ ps → List (Nest Name)
  | [], .nil => []
  | _ :: _, .cons _ _ A Θ => A.blockNest names :: Θ.nest names

/-- The nesting of the type of the entry at each position of the telescope `Θ`, the first one at
`0`, and no position after its entries. -/
def Telescope.nestAt {Γ : Scope} {ps : List Parameter} (names : List Name)
    (Θ : Telescope k Γ ps) : Nat → Nest Name :=
  fun i => ((Θ.nest names)[i]?).getD .plain

/-- The nestings of the entries of a telescope are as many as its entries. -/
theorem Telescope.length_nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (Θ.nest names).length = ps.length
  | [], .nil => rfl
  | _ :: _, .cons _ _ _ Θ => congrArg (· + 1) (Telescope.length_nest names Θ)

/-- The parameters of the recursive results of the fields whose entries have the parameters `ps`,
those of the recursive and of the nested fields, whose nestings `ns` have a position, in order:
each result has the parameter of its field, which no judgment reads. -/
def Telescope.nestResultParams : List (Nest Name) → List Parameter → List Parameter
  | .plain :: ns, _ :: ps => Telescope.nestResultParams ns ps
  | _ :: ns, p :: ps => p :: Telescope.nestResultParams ns ps
  | [], _ | _ :: _, [] => []

/-- The positions of the fields whose nestings `ns` have a position, from the position `o`, in
order: the positions of the fields that have a recursive result, whose parameters
`Telescope.nestResultParams` gives. -/
def Telescope.nestPositions (ns : List (Nest Name)) (o : Nat) : List Nat :=
  (ns.zipIdx o).filterMap fun y => if y.1.isPlain then none else some y.2

/-- A field whose nesting has no position has no recursive result. -/
theorem Telescope.nestPositions_plain (ns : List (Nest Name)) (o : Nat) :
    Telescope.nestPositions (.plain :: ns) o = Telescope.nestPositions ns (o + 1) :=
  rfl

/-- A field whose nesting has a position has a recursive result, before those of the others. -/
theorem Telescope.nestPositions_cons {n : Nest Name} (h : n.isPlain = false)
    (ns : List (Nest Name)) (o : Nat) :
    Telescope.nestPositions (n :: ns) o = o :: Telescope.nestPositions ns (o + 1) := by
  cases n with
  | plain => cases h
  | direct _ | inst _ => rfl

/-- The positions of the fields that have a recursive result are those, from `o`, of the fields
whose nesting has a position. -/
theorem Telescope.mem_nestPositions {ns : List (Nest Name)} {o l : Nat} :
    o + l ∈ Telescope.nestPositions ns o ↔ ∃ n, ns[l]? = some n ∧ n.isPlain = false := by
  unfold Telescope.nestPositions
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨n, l'⟩, hy, hf⟩
    obtain ⟨-, hn⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.1 hy
    split at hf
    · cases hf
    · rename_i hp
      cases hf
      refine ⟨n, ?_, Bool.not_eq_true _ ▸ hp⟩
      simpa using hn
  · rintro ⟨n, hn, hp⟩
    refine ⟨(n, o + l), List.mem_zipIdx_iff_le_and_getElem?_sub.2
      ⟨by simp, by simpa using hn⟩, by simp [hp]⟩

/-- The positions of the fields that have a recursive result, from the position `o`, are at `o`
or after it. -/
theorem Telescope.le_of_mem_nestPositions {y : Nat} {ns : List (Nest Name)} {o : Nat}
    (h : y ∈ Telescope.nestPositions ns o) : o ≤ y := by
  obtain ⟨⟨n, l⟩, hy, hf⟩ := List.mem_filterMap.1 h
  have hl := (List.mem_zipIdx hy).1
  split at hf
  · cases hf
  · cases hf
    exact hl

/-- The fields that have a recursive result are as many as the recursive results that the typing
binds for fields of the parameters `ps`. -/
theorem Telescope.length_nestPositions : (ns : List (Nest Name)) → (ps : List Parameter) →
    ns.length = ps.length → (o : Nat) →
      (Telescope.nestPositions ns o).length = (Telescope.nestResultParams ns ps).length
  | [], [], _, _ => rfl
  | .plain :: ns, _ :: ps, h, o => Telescope.length_nestPositions ns ps (Nat.succ.inj h) (o + 1)
  | .direct _ :: ns, _ :: ps, h, o | .inst _ :: ns, _ :: ps, h, o =>
    congrArg (· + 1) (Telescope.length_nestPositions ns ps (Nat.succ.inj h) (o + 1))

/-- A list built from the fields whose nesting has a position, by a function of their positions, is
the image of their positions. -/
theorem Telescope.filterMap_eq_map_nestPositions {β : Type} (f : Nat → β)
    (ns : List (Nest Name)) (o : Nat) :
    (ns.zipIdx o).filterMap (fun y => if y.1.isPlain then none else some (f y.2)) =
      (Telescope.nestPositions ns o).map f := by
  rw [Telescope.nestPositions, List.map_filterMap]
  congr 1
  funext y
  split <;> rfl

/-- The parameters of the recursive results of the constructor `c` at the instance `I`, in a block
whose types have the names `names`. -/
abbrev Constructor.nestResultParams {j g k' : Nat} {Δ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) (names : List Name) : List Parameter :=
  Telescope.nestResultParams ((c.fields I).nest names) (c.params I)

/-! ## Nesting of the Destructors of a Block -/

/-- `nest_Π`: the nestings of the variables of the scope of a type that is strictly positive in the
parameters `positive`, by their positions: each of these parameters has a position that holds it,
and the other variables have none.
RFC: `\mathsf{nest}_\Pi` -/
def Nesting.ofPositive {Γ : Scope} (positive : Nat → Bool) : Nesting Nat Γ := fun x =>
  if positive x.level then .direct x.level else .plain

/-- `nest_{𝒟; Π}(d̄)`: whether the result of each destructor has a position, in order, where `ν`
gives the nestings of the variables of the scope of the destructors, those of the parameters in
which their type is strictly positive; a destructor has no position, as the variables that the
arguments of a destructor bind.
The RFC gives in one list the type of the block of a recursive destructor and the nesting of the
result of each other destructor; the Lean reads the first from `Destructors.recursion`, and keeps
of the second whether it has a position, which is all that the rules read of it.
RFC: `\mathsf{nest}_B`
RFC: `\mathsf{nest}_{\bar d}` -/
def Destructors.nested : {Γ : Scope} → Nesting α Γ → {ns : List Name} → Destructors k Γ ns →
    List Bool
  | _, _, _, .nil => []
  | _, ν, _, .cons (ps := ps) _ _ _ _ B _ ds =>
    (!(B.nest (fun _ => none) (Nesting.liftN ps.length @ν)).isPlain) ::
      ds.nested (Nesting.lift @ν)

/-- Whether the result of the destructor at each position of the destructors `d̄` has a position,
the first destructor at `0`, and none after its destructors. -/
def Destructors.nestedAt {Γ : Scope} {ns : List Name} (ν : Nesting α Γ)
    (ds : Destructors k Γ ns) : Nat → Bool :=
  fun i => ((ds.nested @ν)[i]?).getD false

/-- The nestings of the variables of the scope `Ξ` of a destructor, at its position in destructors
of the scope `Γ`, whose variables have the nestings `ν`: the destructors before it have no
position. -/
def Destructors.Pos.nesting {α : Type} {k' : Nat} {d : Name} {p q ς : Grading.Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grading.Grade ps.length} → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        Nesting α Γ → Nesting α Ξ
  | _, _, _, _, _, _, _, .here, ν => ν
  | _, _, _, _, _, _, _, .there h, ν => h.nesting (Nesting.lift @ν)

/-- The nesting of an instance is not a position. -/
theorem Nest.ofArgs_ne_direct (ns : List (Nest α)) (a : α) : Nest.ofArgs ns ≠ .direct a := by
  unfold Nest.ofArgs
  split <;> exact fun h => nomatch h

/-- The nesting of the type of a field is a position that holds a type of the block when the field
is recursive, of this type, and only then. -/
theorem Term.blockNest_eq_direct {Γ : Scope} {names : List Name} {D : Name} :
    (A : Term k Γ) → (A.blockNest names = .direct D ↔ A.blockName names = some D)
  | .inst D' _ _ _ as => by
    unfold Term.blockNest Term.blockName
    rw [Term.nest]
    by_cases hD : D' ∈ names
    · simp only [hD, ite_true, Nest.direct.injEq, Option.some.injEq]
    · simp only [hD, ite_false, reduceCtorEq, iff_false]
      exact Nest.ofArgs_ne_direct _ _
  | .var .. | .sort _ | .const .. | .ctor .. | .recursor .. | .obs .. | .corec .. | .equality ..
  | .refl .. | .transp .. | .propExt .. | .coind .. =>
    ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- The nesting of the entry at a position of a telescope is a position that holds a type of the
block when the entry is a recursive field of this type, and only then. -/
theorem Telescope.nestAt_eq_direct {Γ : Scope} {names : List Name} {D : Name} :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (i : Nat) →
      (Θ.nestAt names i = .direct D ↔ Θ.recursionAt names i = some D)
  | [], .nil, _ => ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | _ :: _, .cons _ _ A _, 0 => Term.blockNest_eq_direct A
  | _ :: _, .cons _ _ _ Θ, i + 1 => Telescope.nestAt_eq_direct Θ i

/-- The type of the block that a field whose type has the nesting `ν` is a recursive field of: the
type that its position holds, and none for the other nestings. -/
def Nest.blockName : Nest Name → Option Name
  | .direct D => some D
  | _ => none

/-- The recursive fields of a telescope are its fields whose nestings are positions. -/
theorem Telescope.recursion_eq_map_nest {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      Θ.recursion names = (Θ.nest names).map Nest.blockName
  | [], .nil => rfl
  | _ :: _, .cons _ _ A Θ => by
    show A.blockName names :: Θ.recursion names =
      Nest.blockName (A.blockNest names) :: (Θ.nest names).map Nest.blockName
    rw [Telescope.recursion_eq_map_nest names Θ]
    congr 1
    cases hN : A.blockNest names with
    | direct D => exact (Term.blockNest_eq_direct A).1 hN
    | plain | inst _ =>
      cases hA : A.blockName names with
      | none => rfl
      | some D => rw [(Term.blockNest_eq_direct A).2 hA] at hN; cases hN

/-- A position among the nestings of the entries of a telescope holds a type of the block. -/
theorem Telescope.mem_names_of_direct_mem {Γ : Scope} {names : List Name} {D : Name}
    {ps : List Parameter} {Θ : Telescope k Γ ps} (h : .direct D ∈ Θ.nest names) : D ∈ names :=
  Telescope.mem_recursion
    ((Telescope.recursion_eq_map_nest names Θ) ▸ List.mem_map_of_mem (f := Nest.blockName) h)

end Sic.Core
