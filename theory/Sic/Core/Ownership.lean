module

public import Sic.Core.Shape.Recursion

/-!
# Ownership

The judgment of ownership `Σ; φ ⊢ t ◀ p; m` of annex 13 of RFC 36: checked in the mode `m`, the
value of the term `t` has the ownership `p`, given the ownership `φ` of each variable of its scope
whose telescope is empty.

Ownership is defined on the term and the signature alone, without a context, as usage is: the scope
gives each second-order variable its telescope and the ownership of its result, and the signature
gives each constant its ownership.
Unlike the vector of the usage, which each premise computes and the conclusion adds, `φ` is the same
in every premise, as the context of the typing is.
The declared types give the ownership of their instances, the data types that of their
constructors and of their recursors, and the codata types that of their observations and of their
corecursors.

A recursor on a block with nested fields reads the shapes of these fields, in its mode and on each
axis of the grades: the requirement of its recursion reads the paths of the shapes, the destructors
that they observe require ownerships within the term at this requirement, and its branches are
checked a second time, as the corecursors of the nested results run them; the variable of a nested
result has the ownership of a new value.
Until the erasure gives the nested results, a premise of the recursor excludes the nested fields, as
the usage does.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `φ, x̄ ◀ o · r̄ · (g · q̄)`: the ownerships `φ` of the variables of the scope `Γ`, extended by the
ownership `o · rᵢ · (g · qᵢ)` of the new variable of each entry of a telescope whose parameters are
`ps`, the first one first, `rᵢ` being the requirement of the entry and `qᵢ` its grade: the value
that the entry requires `o · rᵢ` is used `g · qᵢ` times through its variable, as its usage allows. -/
def Ownership.extendFields {Γ : Scope} (φ : Var Γ .var → Grade) (o g : Grade) :
    (ps : List Parameter) → Var (Γ.extend ps.length) .var → Grade
  | [] => φ
  | p :: ps => Ownership.extendFields (Γ := .var :: Γ)
      (fun | .zero => (o * p.requirement) * (g * p.usage) | .succ x => φ x) o g ps

-- ADE: none.
/-- `φ, ȳ ◀ ō · ē`: the ownerships `φ` of the variables of the scope `Γ`, extended by the ownership
`oᵢ · eᵢ` of `n` new variables, `oᵢ` and `eᵢ` being the ownership and the grade that `os` and `es`
give the `i`-th one, the first one first, and `ωωᵖ · eᵢ` for a variable without `oᵢ`: the value of
ownership `oᵢ` is used `eᵢ` times through the variable, as its usage allows. -/
def Ownership.extendResults {Γ : Scope} (φ : Var Γ .var → Grade) :
    List Grade → List Grade → (n : Nat) → Var (Γ.extend n) .var → Grade
  | _, _, 0 => φ
  | os, es, n + 1 => Ownership.extendResults (Γ := .var :: Γ)
      (fun | .zero => os.headD .unrestrictedUnrestricted * es.headD Grade.zero | .succ x => φ x)
      os.tail es.tail n

-- ADE: none.
/-- `own_p(λ)`: the ownership of the value of the recursive result of a field whose type has the
nesting `ν`, in a branch of a recursor of the ownership `p`: `11ᵖ` for a nested result, the
corecursor of a lifting, a new value, and `p` for the result of a recursive field, a result of the
recursor.
RFC: `\mathsf{own}_\lambda` -/
def Nest.resultOwnership (p : Grade) : Nest Name → Grade
  | .inst _ => .linearLinear
  | _ => p

-- ADE: none.
/-- `own_p(λ̄)`: the ownerships of the values of the recursive results of the fields whose types
have the nestings `ns`, those of the recursive and of the nested fields, in order, in a branch of a
recursor of the ownership `p`.
RFC: `\mathsf{own}_{\bar\lambda}` -/
def Telescope.resultOwnerships (p : Grade) (ns : List (Nest Name)) : List Grade :=
  ns.filterMap fun n => if n.isPlain then none else some (n.resultOwnership p)

-- ADE: none.
/-- A constructor of the block of the type declaration `decl` has, at the instance `I`, a nested
field, a field whose type is at the nesting of an instance. -/
def TypeDeclaration.HasNestedField (decl : TypeDeclaration) (I : Instance decl.sorts decl.grades) :
    Prop :=
  ∃ (i j : Nat) (T : DataType decl.sorts decl.grades decl.levels decl.scope)
    (con : Constructor decl.sorts decl.grades decl.levels decl.scope),
    decl.cases[i]? = some (j, T, con) ∧ ∃ ms, Nest.inst ms ∈ (con.fields I).nest decl.names

-- ADE: none.
/-- A block whose fields are at the nesting of no instance has no nested field, so that the
temporary premise of the recursor that excludes the nested fields excludes the second check of its
branches. -/
theorem TypeDeclaration.not_hasNestedField {decl : TypeDeclaration}
    {I : Instance decl.sorts decl.grades}
    (hn : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∀ ν ∈ (con.fields I).nest decl.names, ∀ ms, ν ≠ Nest.inst ms) :
    ¬ decl.HasNestedField I :=
  fun ⟨i, j, T, con, hi, ms, hm⟩ => hn i j T con hi _ hm ms rfl

-- ADE: none.
/-- `φ, x̄ ◀ ō · (g · q̄)`: the ownerships `φ` of the variables of the scope `Γ`, extended by the
ownership `oᵢ · (g · qᵢ)` of the new variable of each entry of a telescope whose parameters are `ps`,
the first one first, `qᵢ` being the grade of the entry, and `ωωᵖ · (g · qᵢ)` for a variable without
`oᵢ`: the value of ownership `oᵢ` is used `g · qᵢ` times through its variable, as its usage allows. -/
def Ownership.extendArgs {Γ : Scope} (φ : Var Γ .var → Grade) (g : Grade) :
    (ps : List Parameter) → List Grade → Var (Γ.extend ps.length) .var → Grade
  | [], _ => φ
  | p :: ps, os => Ownership.extendArgs (Γ := .var :: Γ)
      (fun | .zero => os.headD .unrestrictedUnrestricted * (g * p.usage) | .succ x => φ x) g ps
        os.tail

-- ADE: none.
/-- The ownerships `ō` of arguments of a telescope whose entries have the parameters `ps`, checked in
the mode `m`, satisfy the requirements of their entries, as those of `Σ; φ ⊢ t̄ ◀ ō; Θ; m` do: one
ownership for each entry, which satisfies its requirement unless the argument is checked in the
mode `00ᵐ`. -/
def Parameter.Allow (m : Mode) : List Parameter → List Grade → Prop
  | [], [] => True
  | p :: ps, o :: os => (m ⊙ p.usage ≠ .zeroZero → p.requirement ≤ o) ∧ Parameter.Allow m ps os
  | _, _ => False

mutual

-- ADE: none.
/-- `Σ; φ ⊢ t ◀ p; m`: checked in the mode `m`, the value of the term `t` has the ownership `p`,
given the ownership `φ` of each variable of its scope whose telescope is empty. -/
inductive Ownership (sig : Signature) : {k : Nat} → {Γ : Scope} → (Var Γ .var → Grade) → Mode →
    Grade → Term k Γ → Prop where
  /-- A variable whose telescope is empty has the ownership that `φ` gives it.
  RFC: `\mathsf{var}_{◀}` -/
  | var {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {x : Var Γ .var} :
      Ownership sig φ m (φ x) (.var₀ x : Term k Γ)
  /-- The application `X[t̄]` of a second-order variable has the value of the ownership of its
  result, when it is defined, given the ownerships `os` of its arguments; each argument on whose
  variable `ψ` has a factor is checked in the mode `m` of the application, so that the value of `ψ`
  reads only ownerships that the mode counts, as for an observation.
  RFC: `\mathsf{var}_{X◀}` -/
  | secondOrder {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {ps : List Parameter}
      {ψ : ResultOwnership Grade ps.length} {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps} {os : List Grade}
      {p : Grade} (hts : OwnershipArgs sig φ m ts os) (hp : ψ.value os = some p)
      (hf : ∀ i : Fin ps.length, (ψ.coefficient i).isSome → m ⊙ ps[i].usage = m) :
      Ownership sig φ m p (.var X ts)
  /-- A constant, defined or declared, has the ownership `p` of its entry, in every mode.
  RFC: `f_{◀}` -/
  | const {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m₁ m₂ : Mode} {f : Name} {j k' g : Nat}
      {p : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (h : sig.HasConstant f j k' g m₂ p A) :
      Ownership sig φ m₁ p (.const f qs ls ps : Term k Γ)
  /-- A sort has the least ownership, `ωωᵖ`, which states nothing.
  RFC: `\kappa_{◀}` -/
  | sort {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {κ : Universe k} :
      Ownership sig φ m .unrestrictedUnrestricted (.sort κ : Term k Γ)
  /-- An instance of a declared type, a type, has the least ownership, `ωωᵖ`, which states nothing.
  RFC: `D_{◀}` -/
  | inst {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {D : Name} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {Δ : Scope} {as : InstanceArgs k Γ Δ} :
      Ownership sig φ m .unrestrictedUnrestricted (.inst D qs ls ps as)
  /-- A constructor builds a new value, which has the ownership `11ᵖ`, whatever its fields; the
  arguments of its fields satisfy the requirements of their entries, as the arguments of a telescope
  do.
  RFC: `c_{◀}` -/
  | ctor {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {os : List Grade}
      (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))} (hts : OwnershipArgs sig φ m ts os) :
      Ownership sig φ m .linearLinear (.ctor D qs ls ps as con.name ts.terms)
  /-- A recursor has the ownership of its branches, each checked with the ownership `o` of the term
  times the requirement `r̂` of its recursion, times the requirement of the entry of each field,
  times the grade `⌜m⌝ · r · q` with which the branch uses the field of grade `q`, for the variable
  of the field, and with the ownership `own_p(λ)` of each recursive result times the grade `e` that
  the branch gives it, for its variable, `p` for the result of a recursive field, a result of the
  recursor, and `11ᵖ` for a nested result, the corecursor of a lifting, a new value: a field of a
  unique value has the ownership its entry requires, a field of a shared value is shared, and a
  variable used more than once is shared; the branches run at each level of the recursion, on a
  recursive field or on an observation of a nested field, and a recursion is a use of its field,
  whose ownership is that of its value times the coefficient of the variable of the field, the
  requirement of its entry times the grade `⌜m⌝ · r · q`, or times the ownerships along the path of
  the observation, which `r̂` reads from the shape of the field, so that they see the term at the
  ownership `o · r̂`, which every level has.
  Each nested field of the block has a shape, which reads the liftings that the signature declares;
  on each axis of the grades, each destructor that its shape observes requires of the value that it
  observes an ownership within `o · r̂`, and the arguments of its observation meet their requirements
  and give its result an ownership, `Shape.Meets`.
  When the block has a nested field, each branch is checked a second time, with the ownership `χ`,
  the scope at `ς · φ` and the results at `own_χ(λ̄) · ē`: the corecursor of a nested result
  captures the scope, which its observations see at the requirement `ς` of its destructors, and runs
  the recursor on the observations of the field, whose results have the ownership `χ`; any branch,
  since a recursion from a nested result may reach any constructor.
  The premise `hn` excludes the nested fields until the erasure of their results is plugged.
  RFC: `\mathsf{rec}_{◀}` -/
  | recursor {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r ς χ : Grade}
      {κ : Universe k} {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {o p : Grade}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (ht : Ownership sig φ (m ⊙ r) o t)
      (hns : decl.NestedHaveShapes sig ⟨κ.quality, r, ς⟩ m χ qs ps (.ofLists qs ps hq hp))
      (hn : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ∀ ms, ν ≠ Nest.inst ms)
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hu : ∀ i j T' con u, decl.cases[i]? = some (j, T', con) →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        Ownership sig (Ownership.extendResults (Ownership.extendFields φ
          (o * decl.recursionRequirement sig ⟨κ.quality, r, ς⟩ m χ qs ps (.ofLists qs ps hq hp))
          (m.grade * r) (con.params (.ofLists qs ps hq hp)))
          (Telescope.resultOwnerships p ((con.fields (.ofLists qs ps hq hp)).nest decl.names))
          (us.grades i) (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) m p u)
      (hu' : decl.HasNestedField (.ofLists qs ps hq hp) → ∀ i j T' con u,
        decl.cases[i]? = some (j, T', con) →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        Ownership sig (Ownership.extendResults (Ownership.extendFields (fun x => ς * φ x)
          (o * decl.recursionRequirement sig ⟨κ.quality, r, ς⟩ m χ qs ps (.ofLists qs ps hq hp))
          (m.grade * r) (con.params (.ofLists qs ps hq hp)))
          (Telescope.resultOwnerships χ ((con.fields (.ofLists qs ps hq hp)).nest decl.names))
          (us.grades i) (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) m χ u)
      (hmeets : ∀ (i j : Nat) (T' : DataType decl.sorts decl.grades decl.levels decl.scope)
        (con : Constructor decl.sorts decl.grades decl.levels decl.scope),
        decl.cases[i]? = some (j, T', con) →
        ∀ ax ∈ [Grade.run, Grade.total], ∀ (l : Nat) (σ : Shape),
          (con.nestedShapes sig ⟨κ.quality, r, ς⟩ m ax decl.names qs ps χ
            (.ofLists qs ps hq hp))[l]? = some (some σ) →
          σ.Meets (ax (o * decl.recursionRequirement sig ⟨κ.quality, r, ς⟩ m χ qs ps
            (.ofLists qs ps hq hp))) (ax ς)) :
      Ownership sig φ m p (.recursor r ς χ D qs ls ps as t κ Cs us)
  /-- An observation has the ownership `o` of its term times the value `v` of the ownership `ψ` of
  the result of its destructor, given the ownerships of its arguments, which satisfy the requirements
  of the entries of the telescope of the destructor, as the arguments of a telescope do: the result
  of a value owned alone has the ownership that its destructor gives it, and the result of a shared
  value is shared, since an other owner of the value may observe it; each argument on whose variable
  `ψ` has a factor is checked in the mode `m` of the observation, so that the value of `ψ` reads only
  ownerships that the mode counts, as the usage counts only the uses of these arguments; the
  ownership of the term satisfies the requirement `ς` of the destructor on the value that it
  observes, in every mode, since the branch of the destructor gives the entries of the state and the
  variables of its scope the ownerships that a value of the ownership `ς` holds.
  RFC: `d_{◀}` -/
  | obs {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
      {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership Grade ps'.length} {o v : Grade} {os : List Grade}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ)
      (ht : Ownership sig φ m o t) {bs : Args k Γ ps'} (hbs : OwnershipArgs sig φ m bs os)
      (hv : ψ.value os = some v)
      (hf : ∀ i : Fin ps'.length, (ψ.coefficient i).isSome → m ⊙ ps'[i].usage = m)
      (hς : ς ≤ o) : Ownership sig φ m (o * v) (.obs D qs ls ps as t d bs.terms)
  /-- A corecursor builds a new value, which has the ownership `11ᵖ`, whatever its state, whose terms
  satisfy the requirements of the entries of the state of its type, as the arguments of a telescope
  do, checked in the mode `m ⊙ r`; the branch of each destructor, checked in the mode `m ⊙ p` of its
  grade `p`, with the requirement `ς` of the destructor on the value that it observes times the
  requirement of its entry for the variable of each entry of the state, which a value of the
  ownership `ς` holds, `ς` times its ownership for each variable of the scope, which such a value
  captures, since the evaluation shares a value among the uses of its position, and the ownership
  `oᵢ` of each argument, each times the grade with which the branch uses the variable, so that a
  variable used more than once is shared, has the ownership `ψ[ō / x̄]` of the result of the
  destructor for every ownerships `ō` of its arguments that satisfy the requirements of their
  entries, since an observation reads `ψ` at the ownerships of its arguments; the branch of a
  recursive destructor has the ownership `11ᵖ` of a new value instead, since its position is
  resumed by a recursor, which gives the term already built of a position the ownership `χ` that
  the position requires of it only when the position is owned alone.
  RFC: `\mathsf{corec}_{◀}` -/
  | corec {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Ss : States k Γ} {gs : CorecBranches k Γ} {h' : Nat} {ps' : List Parameter}
      {S : Telescope k Γ ps'} {ss : Args k Γ ps'} {os : List Grade}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (hh : decl.codataTypes[h']? = some T)
      (hS : Ss.get h' = some ⟨0, ps', S⟩) (hss : OwnershipArgs sig φ (m ⊙ r) ss os)
      (hSl : Ss.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S' : Telescope k Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgo : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → B.blockName decl.names = none →
        ∀ os' v, Parameter.Allow (m ⊙ p) ps₁ os' → ψ.value os' = some v →
        Ownership sig (Ownership.extendArgs (Ownership.extendFields (fun x => ς * φ x) ς
          ((m ⊙ p).grade * r) ps'') (m ⊙ p).grade ps₁ os') (m ⊙ p) v g)
      (hgr : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)) (D' : Name),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → B.blockName decl.names = some D' →
        ∀ os', Parameter.Allow (m ⊙ p) ps₁ os' →
        Ownership sig (Ownership.extendArgs (Ownership.extendFields (fun x => ς * φ x) ς
          ((m ⊙ p).grade * r) ps'') (m ⊙ p).grade ps₁ os') (m ⊙ p) .linearLinear g) :
      Ownership sig φ m .linearLinear (.corec r D qs ls ps as ss.terms Ss gs)
  /-- A term may be given an ownership lower than its own, which states less.
  RFC: `\mathsf{sub}_{◀}` -/
  | sub {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p q : Grade} {t : Term k Γ}
      (h : Ownership sig φ m p t) (hle : q ≤ p) : Ownership sig φ m q t

-- ADE: none.
/-- `Σ; φ ⊢ t̄ ◀ ō; Θ; m`: checked in the mode `m`, the arguments `t̄` of a telescope whose entries
have the parameters `ps` have the ownerships `os`, each satisfying the requirement of its entry. -/
inductive OwnershipArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    (Var Γ .var → Grade) → Mode → Args k Γ ps → List Grade → Prop where
  /-- No argument has no ownership.
  RFC: `\mathsf{tel}_{\varepsilon◀}` -/
  | nil {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} :
      OwnershipArgs sig φ m (.nil : Args k Γ []) []
  /-- The first argument, of the parameter `p`, checked in the mode `m ⊙ p.usage`, with an ownership
  `o` that satisfies the requirement of `p` unless this mode is `00ᵐ`, and the others.
  RFC: `\mathsf{tel}_{,◀}` -/
  | cons {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {p : Parameter}
      {ps : List Parameter} {t : Term k Γ} {ts : Args k Γ ps} {o : Grade} {os : List Grade}
      (ht : Ownership sig φ (m ⊙ p.usage) o t)
      (hr : m ⊙ p.usage ≠ .zeroZero → p.requirement ≤ o) (hts : OwnershipArgs sig φ m ts os) :
      OwnershipArgs sig φ m (.cons t ts : Args k Γ (p :: ps)) (o :: os)

end

-- ADE: none.
/--
`⊢ Σ ◀`: the values of the entries of the signature have their ownerships: at each instance of its
sort and grade variables, the value of the body of a constant definition has the ownership of the
definition, in its mode, without variable; the ownership `ψ` of the result of each recursive
destructor of a block of codata types is a constant `χ`, which the ownerships of its arguments do not
change, at each instance, and below the ownership `11ᵖ` of a new value, which an observation that
resumes the corecursor gives, at each instance that the constraint of the block admits.
-/
inductive OwnershipSig : Signature → Prop where
  /-- The empty signature.
  RFC: `\mathsf{sig}_{\varnothing◀}` -/
  | empty : OwnershipSig []
  /-- A constant definition, whose body has the ownership of the definition.
  RFC: `\mathsf{sig}_{\mathsf{def}◀}` -/
  | constantDefinition {sig : Signature} {d : ConstantDefinition} (h : OwnershipSig sig)
      (ho : ∀ ι, Ownership sig (fun x : Var [] .var => nomatch x) d.mode d.ownership (d.body ι)) :
      OwnershipSig (.constantDefinition d :: sig)
  /-- A constant declaration, which has no body.
  RFC: `\mathsf{sig}_{\mathsf{decl}◀}` -/
  | constantDeclaration {sig : Signature} {c : ConstantDeclaration} (h : OwnershipSig sig) :
      OwnershipSig (.constantDeclaration c :: sig)
  /-- A block of data types, whose constructors give the ownerships of their values.
  RFC: `\mathsf{sig}_{\mathsf{data}◀}` -/
  | data {sig : Signature} {decl : TypeDeclaration}
      {Ts : List (DataType decl.sorts decl.grades decl.levels decl.scope)} (h : OwnershipSig sig)
      (hb : decl.body = .data Ts) : OwnershipSig (.typeDeclaration decl :: sig)
  /-- A block of codata types, the ownership of the result of each recursive destructor a constant
  `χ` at each instance, and `χ ≤ 11ᵖ` at each instance that its constraint admits.
  RFC: `\mathsf{sig}_{\mathsf{codata}◀}` -/
  | codata {sig : Signature} {decl : TypeDeclaration}
      {Ts : List (CodataType decl.sorts decl.grades decl.levels decl.scope)} (h : OwnershipSig sig)
      (hb : decl.body = .codata Ts)
      (hψ : ∀ ι, ∀ T ∈ decl.codataTypes, ∀ d p q ς ps Ξ
        (Θ : Telescope decl.levels Ξ ps) (B : Term decl.levels (Ξ.extend ps.length))
        (ψ : ResultOwnership Grade ps.length), (T.body ι).Pos d p q ς Ξ Θ B ψ →
        B.blockName decl.names ≠ none →
          ∃ χ, ψ = ⟨some χ, fun _ => none⟩ ∧ (decl.constraint ι → χ ≤ Grade.one)) :
      OwnershipSig (.typeDeclaration decl :: sig)

end Sic.Core
