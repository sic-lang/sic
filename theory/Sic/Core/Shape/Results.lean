module

public import Sic.Core.Shape
public import Sic.Core.Lifting

/-!
# Shapes of the Recursive Results

The shape of annex 14 of RFC 36 that the erasure of a recursor of annex 19 gives the recursive
result of a field of a constructor: the shape `Υ` of the corecursor of the lifting of the type of a
nested field, or the recursor itself for a recursive field, read from the signature.
The shape is computed in a mode, on an axis of the grades: the erasure reads it in the mode `11ᵐ`,
on the axis of the uses at run time, and the ownership of annex 18 reads it in the mode of the
recursor, on each axis, for the requirements of the recursions on the observations of a nested
field.

The shape follows the lifting of annex 13: the shape of a type lifted is that of the motive of a
variable lifted, `⋆_Z` for an instance of a type of the block, and, for an instance of another
declared type, of which an argument at least is lifted, the shape of the lifting of this type, at
the shapes of these arguments.
The shape of a lifting has an element for each destructor of the type whose result is lifted, in
order, as the lifting keeps it: the case of the destructor, its multiplicity on the axis, the
parameters of its arguments in the observation and in the lifting, the ownerships of the results and
the requirements on the value observed, and the shape of its result, the result lifted where the
parameters of the type have the shapes of the arguments.
Each element also reads the factor and the ownership of the result lifted, which a variable lifted
has from the argument of the instance: the shape of a type lifted carries them, as grades, beside
the shape `Υ`, as the lifting carries them in its output.
The multiplicity and the parameters of a destructor of the lifting are those that the lifting gives
it, read from the destructor that it lifts: the mode of the grade of the destructor, its arguments
used the grade of the recursor times the factor of the result more, the ownership of the result,
and the requirement of the recursor.

The result of a destructor of a lifting is an instance of a lifting declared before it, as the
signature declares its liftings in order, so that the shape of a lifting reads only the shapes of
the liftings before it in the signature: the shape follows the signature, entry by entry, without
fuel, and it reads the declarations of the types lifted and their cases in the entries before the
lifting too, which a well-formed signature declares before it, so that the shape of a lifting does
not depend on the entries after it, which an extension of the signature adds.
The shape is a function, which the erasure computes on the syntax, and it is the shape of an
instance of a lifting that the signature declares only: an instance of a lifting that the signature
does not declare has none.

The shapes of the nested fields of a constructor are those of their types, in the block of the
recursor, whose types have the shape of the recursor itself on the terms of their skeletons, and the
ownership of the source and the erasure read them alike.

The RFC names the variables, so that the shape of a variable lifted is found by its name; with de
Bruijn indices, the shapes of the variables of a scope are a nesting of its variables, whose
positions hold the shapes of the variables lifted, while the types of the block, which a name finds,
have their shapes apart, where the RFC gives both by one nesting `Λ`; the shapes of the arguments of
an instance, which the RFC gives as a nesting per parameter, are the positions of the parameters
lifted with their shapes.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Shapes of the Types Lifted -/

/-- What a type lifted gives the recursive result that it is the type of: the shape `Υ` of this
result, its factor `π` and its ownership `χ'`, as grades, as the lifting gives them. -/
structure Shape.Motive where
  /-- The shape `Υ` of the recursive result. -/
  next : Shape.Next
  /-- The factor `π` of the recursive result. -/
  factor : Grade
  /-- The ownership `χ'` of the recursive result. -/
  ownership : Grade

/-- The shape and the factor of the lifting of the type `D` at the instance of the qualities `qs`
and of the grades `ps`, whose parameters at the positions of `ms` are lifted, each with the shape,
the factor and the ownership of its motive, when the signature declares this lifting. -/
abbrev Shape.Lookup : Type :=
  Name → List Quality → List Grade → List (Nat × Shape.Motive) → Option (Shape × Grade)

/-- The shape of a variable whose nesting is `n`: the shape of a position, none for the others. -/
def Nest.motive : Nest Shape.Motive → Option Shape.Motive
  | .direct m => some m
  | _ => none

mutual

/-- The shape of the recursive result of a term of the type `A`, whose nesting is `n`, where `lookup`
gives the shapes of the liftings, `block` the shapes of the types of the block and `ν` those of the
variables lifted, as `Term.Lifts` lifts it: a variable lifted, applied to arguments, has its shape,
an instance of a type of the block at a position that holds it has the shape of this type, and an
instance of another declared type, of which an argument at least is lifted and each argument whose
nesting has a position has a shape, the shape of the lifting of this type at the positions and the
shapes of these arguments, of the ownership `11ᵖ`.
RFC: `\mathsf{shape}_A` -/
def Term.shape (v : Lifting.Variables) (lookup : Shape.Lookup) (block : Name → Option Shape.Motive)
    {Γ : Scope} (ν : Nesting Shape.Motive Γ) (n : Nest Name) : Term k Γ → Option Shape.Motive
  | .var x _ => (ν x).motive
  | .inst D qs _ ps as =>
    match n with
    | .direct _ => block D
    | _ =>
      match as.shapes v lookup block ν n.args with
      | some (m :: ms) => (lookup D qs ps (m :: ms)).map fun σ => ⟨.lifting σ.1, σ.2, .linearLinear⟩
      | _ => none
  | _ => none
termination_by structural A => A

/-- The positions and the shapes of the arguments `ā` of an instance that are lifted, whose nestings
are `ns`, the last one first, the first argument first, as `InstanceArgs.Lifts` lifts them: the
position of an argument is the number of the arguments before it; an argument without shape is
not lifted when its nesting has no position, and the arguments have no shapes when its nesting has
one, since the lifting lifts it.
RFC: `\mathsf{shape}_{\bar a}` -/
def InstanceArgs.shapes (v : Lifting.Variables) (lookup : Shape.Lookup)
    (block : Name → Option Shape.Motive) {Γ : Scope} (ν : Nesting Shape.Motive Γ) :
    List (Nest Name) → {Δ : Scope} → InstanceArgs k Γ Δ → Option (List (Nat × Shape.Motive))
  | _, _, .nil => some []
  | ns, _, .snoc (Δ := Δ) as B =>
    match as.shapes v lookup block ν ns.tail,
      B.shape v lookup block (Nesting.liftN _ ν) (ns.headD .plain) with
    | some l, some m => some (l ++ [(Δ.length, m)])
    | some l, none => if (ns.headD .plain).isPlain then some l else none
    | none, _ => none
termination_by structural _ _ as => as

end

/-! ## Shapes of the Liftings -/

/-- The shape of the lifting of the type `D` whose destructors are `d̄`, checked in the mode `m`,
on the axis `ax` of the grades, where `ν` gives the shapes of the variables lifted, and the meet of
the grades of its destructors times the factors of their results, absent without destructor, as
`Destructors.Lifts` and `Destructors.Factor` give them: a destructor whose result has a shape is
kept, at the case that the signature gives it, and the others are not; the multiplicities of the
shape are those of the grades on the axis, the uses at run time or all the uses, and the arguments
of the lifted destructor are used as the mode `m` gives its grade.
The axis `β` of the grades is the function `ax : Grade → Multiplicity`, `Grade.run` or
`Grade.total`: an axis reads each grade on one of its multiplicities, which is what a projection of
a grade does, so the walk applies the projection itself, with no name of the axis to decode.
RFC: `\mathsf{shape}_{\bar d}` -/
def Destructors.shape (sig : Signature) (v : Lifting.Variables) (m : Mode)
    (ax : Grade → Multiplicity) (lookup : Shape.Lookup) (D : Name) :
    {Γ : Scope} → Nesting Shape.Motive Γ → {ns : List Name} → Destructors k Γ ns →
      Shape × Option Grade
  | _, _, [], .nil => (.nil, none)
  | _, ν, d :: _, .cons (ps := ps) p _ ς₀ _ B ψ₀ ds =>
    let rest := ds.shape sig v m ax lookup D (Nesting.lift ν)
    match B.shape v lookup (fun _ => none) (Nesting.liftN ps.length ν) .plain with
    | none => rest
    | some μ =>
      let p' := Lifting.resultGrade v.quality p
      ⟨.cons ((sig.destructorCase D d).getD 0) ps.length (ax p')
        (fun j => ax ps[j].usage) (fun j => ax ps[j].requirement)
        (fun j => ax ((m ⊙ p').grade * (ps[j].scale (v.recursion * μ.factor)).usage))
        (fun j => ax ps[j].requirement)
        ((Lifting.resultOwnership μ.ownership _).map ax) (ax v.requirement)
        (ψ₀.map ax) (ax ς₀) μ.next rest.1,
        some ((p' * μ.factor).meetWith rest.2)⟩
termination_by structural _ _ ds => ds

/-- The shapes of the parameters of a type declaration, the parameter at each position of `ms`
lifted with its shape, and the others not. -/
def Shape.motives {Δ : Scope} (ms : List (Nat × Shape.Motive)) : Nesting Shape.Motive Δ :=
  fun x =>
    match ms.lookup x.level with
    | some m => .direct m
    | none => .plain

/-- The shapes of the liftings that the entries of a signature declare, checked in the mode `m`, on
the axis `ax` of the grades: the shape of the lifting of the type `D` at the positions of `ms`, at
the instance of the qualities `qs` and of the grades `ps`, is that of the destructors of `D` at this
instance, where the parameters at these positions have the shapes of `ms`, which reads the
declaration of `D`, its cases and the shapes of the liftings in the entries before the lifting, so
that the shape does not depend on the entries after it.
RFC: `\mathsf{shape}_\Sigma` -/
def Signature.shapes (v : Lifting.Variables) (m : Mode) (ax : Grade → Multiplicity) :
    Signature → Shape.Lookup
  | [] => fun _ _ _ _ => none
  | .typeDeclaration L :: sig' => fun D qs ps ms =>
    if L.names = [Lifting.name D (ms.map (·.1))] then
      sig'.findSome? fun
        | .typeDeclaration decl =>
          if hq : qs.length = decl.sorts then
            if hp : ps.length = decl.grades then
              (decl.codataTypes.find? (·.name == D)).map fun T =>
                let σ := (T.body (.ofLists qs ps hq hp)).shape sig' v m ax
                  (Signature.shapes v m ax sig') D (Shape.motives ms)
                (σ.1, σ.2.getD .noneNone)
            else none
          else none
        | _ => none
    else Signature.shapes v m ax sig' D qs ps ms
  | _ :: sig' => Signature.shapes v m ax sig'
termination_by structural sig => sig

/-! ## Shapes of the Nested Fields -/

/-- The shapes of the types of the block whose names are `names`, for a recursor whose results that
are motives have the ownership `χ`, at the instance of the qualities `qs` and of the grades `ps`: the
recursor itself, on the term of the skeleton of the type when its multiplicity is `0`, of the factor
`11ᵖ` and of the ownership `χ`, as the lifting of the block gives them, and none for the other
names.
RFC: `\mathsf{shape}_{\mathcal{D}}` -/
def Signature.blockShapes (sig : Signature) (names : List Name) (qs : List Quality)
    (ps : List Grade) (χ : Grade) : Name → Option Shape.Motive :=
  fun D => if D ∈ names then some ⟨.recursor (sig.skeleton D qs ps), .linearLinear, χ⟩ else none

/-- The shape of the nested result of a field, from the shape of its type: the shape of the lifting
when the result is the corecursor of a lifting, and none for the others. -/
def Shape.Motive.nested : Option Shape.Motive → Option Shape
  | some ⟨.lifting σ, _, _⟩ => some σ
  | _ => none

/-- The shapes of the nested results of the fields of a telescope, the first one first: the shape
of the lifting of the type of each nested field, at the nesting of its type in the block whose names
are `names`, where `lookup` gives the shapes of the liftings and `block` those of the types of the
block, and none for the other fields; the variables of the fields have no shape, since the lifting
of a block lifts no variable.
RFC: `\mathsf{shapes}_\Theta` -/
def Telescope.nestedShapes (v : Lifting.Variables) (lookup : Shape.Lookup)
    (block : Name → Option Shape.Motive) (names : List Name) :
    {Γ : Scope} → {ps : List Parameter} → Telescope k Γ ps → List (Option Shape)
  | _, [], .nil => []
  | _, _ :: _, .cons _ _ A Θ =>
    Shape.Motive.nested (A.shape v lookup block Nesting.plain (A.blockNest names)) ::
      Θ.nestedShapes v lookup block names

/-- The shapes of the nested results of the fields of the constructor `con` at the instance `I`, in
a block whose types are named `names`, of a recursor of the variables `v` whose results that are
motives have the ownership `χ`, at the instance of the qualities `qs` and of the grades `ps`,
computed in the mode `m` on the axis `ax` of the grades, in the signature `sig`: the shape of each
nested field, and none for the other fields, in order.
RFC: `\mathsf{shapes}_c` -/
def Constructor.nestedShapes {j g k' : Nat} {Δ : Scope} (sig : Signature) (v : Lifting.Variables)
    (m : Mode) (ax : Grade → Multiplicity) (names : List Name) (qs : List Quality)
    (ps : List Grade) (χ : Grade) (con : Constructor j g k' Δ) (I : Instance j g) :
    List (Option Shape) :=
  (con.fields I).nestedShapes v (sig.shapes v m ax) (sig.blockShapes names qs ps χ) names

/-- Each nested field of the constructor `con` at the instance `I` has a shape, computed as
`Constructor.nestedShapes` computes it: the field whose type is at the nesting of an instance, in
the block whose types are named `names`, has the shape of a lifting that the signature declares. -/
def Constructor.NestedHaveShapes {j g k' : Nat} {Δ : Scope} (sig : Signature)
    (v : Lifting.Variables) (m : Mode) (ax : Grade → Multiplicity) (names : List Name)
    (qs : List Quality) (ps : List Grade) (χ : Grade) (con : Constructor j g k' Δ)
    (I : Instance j g) : Prop :=
  ∀ (l : Nat) (ns : List (Nest Name)), ((con.fields I).nest names)[l]? = some (.inst ns) →
    ∃ σ, (con.nestedShapes sig v m ax names qs ps χ I)[l]? = some (some σ)

end Sic.Core
