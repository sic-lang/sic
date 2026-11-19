module

public import Sic.Core.Shape
public import Sic.Core.Lifting

/-!
# Shapes of the Recursive Results

The shape that the erasure of a recursor of annex 16 of RFC 36 gives the recursive result of a field
of a constructor: the shape `Υ` of the corecursor of the lifting of the type of a nested field, or the
recursor itself for a recursive field, read from the signature.
The shape is computed in a mode, on an axis of the grades: the erasure reads it in the mode `11ᵐ`,
on the axis of the uses at run time, and the ownership of annex 13 reads it in the mode of the
recursor, on each axis, for the requirements of the recursions on the observations of a nested
field.

The shape follows the lifting of annex 20: the shape of a type lifted is that of the motive of a
variable lifted, `⋆_M` for an instance of a type of the block, and, for an instance of another
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
fuel, while it reads the declarations of the types lifted and their cases in the whole signature.
The shape is a function, which the erasure computes on the syntax, and it is the shape of an
instance of a lifting that the signature declares only: an instance of a lifting that the signature
does not declare has none.

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

-- ADE: none.
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

-- ADE: none.
/-- The shape of the recursive result of a term of the type `A`, whose nesting is `n`, where `lookup`
gives the shapes of the liftings, `block` the shapes of the types of the block and `ν` those of the
variables lifted, as `Term.Lifts` lifts it: a variable lifted, applied to arguments, has its shape,
an instance of a type of the block at a position that holds it has the shape of this type, and an
instance of another declared type, of which an argument at least is lifted, the shape of the
lifting of this type at the positions and the shapes of these arguments, of the ownership `11ᵖ`.
RFC: `\mathsf{shape}_A` -/
def Term.shape (v : Lifting.Variables) (lookup : Shape.Lookup) (block : Name → Option Shape.Motive)
    {Γ : Scope} (ν : Nesting Shape.Motive Γ) (n : Nest Name) : Term k Γ → Option Shape.Motive
  | .var x _ => (ν x).motive
  | .inst D qs _ ps as =>
    match n with
    | .direct _ => block D
    | _ =>
      match as.shapes v lookup block ν n.args with
      | [] => none
      | ms => (lookup D qs ps ms).map fun σ => ⟨.lifting σ.1, σ.2, .linearLinear⟩
  | _ => none
termination_by structural A => A

-- ADE: none.
/-- The positions and the shapes of the arguments `ā` of an instance that are lifted, whose nestings
are `ns`, the last one first, the first argument first, as `InstanceArgs.Lifts` lifts them: the
position of an argument is the number of the arguments before it.
RFC: `\mathsf{shape}_{\bar a}` -/
def InstanceArgs.shapes (v : Lifting.Variables) (lookup : Shape.Lookup)
    (block : Name → Option Shape.Motive) {Γ : Scope} (ν : Nesting Shape.Motive Γ) :
    List (Nest Name) → {Δ : Scope} → InstanceArgs k Γ Δ → List (Nat × Shape.Motive)
  | _, _, .nil => []
  | ns, _, .snoc (Δ := Δ) as B =>
    as.shapes v lookup block ν ns.tail ++
      ((B.shape v lookup block (Nesting.liftN _ ν) (ns.headD .plain)).map
        fun m => (Δ.length, m)).toList
termination_by structural _ _ as => as

end

/-! ## Shapes of the Liftings -/

-- ADE: none.
/-- The shape of the lifting of the type `D` whose destructors are `d̄`, checked in the mode `m`,
on the axis `ax` of the grades, where `ν` gives the shapes of the variables lifted, and the meet of
the grades of its destructors times the factors of their results, absent without destructor, as
`Destructors.Lifts` and `Destructors.Factor` give them: a destructor whose result has a shape is
kept, at the case that the signature gives it, and the others are not; the multiplicities of the
shape are those of the grades on the axis, the uses at run time or all the uses, and the arguments
of the lifted destructor are used as the mode `m` gives its grade.
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

-- ADE: none.
/-- The shapes of the liftings that the entries `sig'` of the signature `sig` declare, checked in the
mode `m`, on the axis `ax` of the grades: the shape of the lifting of the type `D` at the positions
of `ms`, at the instance of the qualities `qs` and of the grades `ps`, is that of the destructors of
`D` at this instance, where the parameters at these positions have the shapes of `ms`, which reads
the shapes of the liftings declared before it, and the declarations of the types in the whole
signature.
RFC: `\mathsf{shape}_\Sigma` -/
def Signature.shapes (sig : Signature) (v : Lifting.Variables) (m : Mode)
    (ax : Grade → Multiplicity) : Signature → Shape.Lookup
  | [] => fun _ _ _ _ => none
  | .typeDeclaration L :: sig' => fun D qs ps ms =>
    if L.names = [Lifting.name D (ms.map (·.1))] then
      sig.findSome? fun
        | .typeDeclaration decl =>
          if hq : qs.length = decl.sorts then
            if hp : ps.length = decl.grades then
              (decl.codataTypes.find? (·.name == D)).map fun T =>
                let σ := (T.body (.ofLists qs ps hq hp)).shape sig v m ax (sig.shapes v m ax sig') D
                  (Shape.motives ms)
                (σ.1, σ.2.getD .noneNone)
            else none
          else none
        | _ => none
    else sig.shapes v m ax sig' D qs ps ms
  | _ :: sig' => sig.shapes v m ax sig'
termination_by structural sig' => sig'

end Sic.Core
