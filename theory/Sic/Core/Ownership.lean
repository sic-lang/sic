module

public import Sic.Core.Syntax

/-!
# Ownership

The judgment of ownership `Σ; φ ⊢ t ◀ p; m` of annex 12 of RFC 36: checked in the mode `m`, the
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
-/

@[expose] public section

namespace Sic.Core

-- ADE: none.
/-- `ψ'`: the ownership `ψ` of the result of a second-order variable without the factor of the first
variable of its telescope, over the variables after it. -/
def ResultOwnership.tail {n : Nat} (ψ : ResultOwnership (n + 1)) : ResultOwnership n :=
  ⟨ψ.constant, fun i => ψ.coefficient i.succ⟩

-- ADE: none.
/-- `ψ[ō / x̄]`: the value of the ownership `ψ` of the result of a second-order variable, given the
ownerships `os` of its arguments: the meet of its constant `ψ` and of the ownership `oⱼ` of each
argument scaled by the coefficient `χⱼ` of its variable, over the factors present, and none if no
factor is.
RFC: `\mathsf{value}_\psi` -/
def ResultOwnership.value : {n : Nat} → ResultOwnership n → List Grade → Option Grade
  | _ + 1, ψ, o :: os => Option.merge (· ⊓ ·) ((ψ.coefficient 0).map (o * ·)) (ψ.tail.value os)
  | _, ψ, _ => ψ.constant

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
/-- `φ, ȳ ◀ p · ē`: the ownerships `φ` of the variables of the scope `Γ`, extended by the ownership
`p · eᵢ` of `n` new variables, `eᵢ` being the grade `es` gives the `i`-th one, the first one first:
the value of ownership `p` is used `eᵢ` times through the variable, as its usage allows. -/
def Ownership.extendResults {Γ : Scope} (φ : Var Γ .var → Grade) (p : Grade) :
    List Grade → (n : Nat) → Var (Γ.extend n) .var → Grade
  | _, 0 => φ
  | es, n + 1 => Ownership.extendResults (Γ := .var :: Γ)
      (fun | .zero => p * es.headD Grade.zero | .succ x => φ x) p es.tail n

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
  result, when it is defined, given the ownerships `os` of its arguments.
  RFC: `\mathsf{var}_{X◀}` -/
  | secondOrder {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {ps : List Parameter}
      {ψ : ResultOwnership ps.length} {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps} {os : List Grade}
      {p : Grade} (hts : OwnershipArgs sig φ m ts os) (hp : ψ.value os = some p) :
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
  times the requirement of the entry of each field, times the grade `⌜m⌝ · r · q` with which the
  branch uses the field of grade `q`, for the variable of the field, and with the ownership `p` of
  the recursor times the grade `e` that the branch gives each recursive result, for its variable: a
  field of a unique value has the ownership its entry requires, a field of a shared value is
  shared, a recursive result is a result of the recursor, and a variable used more than once is
  shared.
  RFC: `\mathsf{rec}_{◀}` -/
  | recursor {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {o p : Grade}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (ht : Ownership sig φ (m ⊙ r) o t)
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hu : ∀ i j T' con u, decl.cases[i]? = some (j, T', con) →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        Ownership sig (Ownership.extendResults (Ownership.extendFields φ o (m.grade * r)
          (con.params (.ofLists qs ps hq hp))) p (us.grades i)
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length) m p u) :
      Ownership sig φ m p (.recursor r D qs ls ps as t Cs us)
  /-- An observation has the ownership `o` of its term times the value `v` of the ownership `ψ` of
  the result of its destructor, given the ownerships of its arguments, which satisfy the requirements
  of the entries of the telescope of the destructor, as the arguments of a telescope do: the result
  of a value owned alone has the ownership that its destructor gives it, and the result of a shared
  value is shared, since an other owner of the value may observe it.
  RFC: `d_{◀}` -/
  | obs {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
      {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership ps'.length} {o v : Grade} {os : List Grade}
      (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (ht : Ownership sig φ m o t) {bs : Args k Γ ps'} (hbs : OwnershipArgs sig φ m bs os)
      (hv : ψ.value os = some v) :
      Ownership sig φ m (o * v) (.obs D qs ls ps as t d bs.terms)
  /-- A corecursor builds a new value, which has the ownership `11ᵖ`, whatever its state, whose terms
  satisfy the requirements of the entries of the state of its type, as the arguments of a telescope
  do, checked in the mode `m ⊙ r`; the branch of each destructor, checked in the mode `m ⊙ p` of its
  grade `p`, with the requirement of its entry for the variable of each entry of the state, which
  the value owned alone holds, and the ownership `oᵢ` of each argument, each times the grade with
  which the branch uses the variable, so that a variable used more than once is shared, has the
  ownership `ψ[ō / x̄]` of the result of the destructor for every ownerships `ō` of its arguments
  that satisfy the requirements of their entries, since an observation reads `ψ` at the ownerships
  of its arguments; the branch of a recursive destructor has the ownership `11ᵖ` of a new value
  instead, since its position is resumed by a recursor, which gives the term already built of a
  position the ownership `χ` that the position requires of it only when the position is owned alone.
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
        ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgo : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → B.blockName decl.names = none →
        ∀ os' v, Parameter.Allow (m ⊙ p) ps₁ os' → ψ.value os' = some v →
        Ownership sig (Ownership.extendArgs (Ownership.extendFields φ .linearLinear
          ((m ⊙ p).grade * r) ps'') (m ⊙ p).grade ps₁ os') (m ⊙ p) v g)
      (hgr : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)) (D' : Name),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → B.blockName decl.names = some D' →
        ∀ os', Parameter.Allow (m ⊙ p) ps₁ os' →
        Ownership sig (Ownership.extendArgs (Ownership.extendFields φ .linearLinear
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
definition, in its mode, without variable; at each instance that the constraint of a block of codata
types admits, the ownership `ψ` of the result of each recursive destructor is a constant `χ`, which
the ownerships of its arguments do not change, below the ownership `11ᵖ` of a new value, which an
observation that resumes the corecursor gives.
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
  `χ ≤ 11ᵖ` at each instance.
  RFC: `\mathsf{sig}_{\mathsf{codata}◀}` -/
  | codata {sig : Signature} {decl : TypeDeclaration}
      {Ts : List (CodataType decl.sorts decl.grades decl.levels decl.scope)} (h : OwnershipSig sig)
      (hb : decl.body = .codata Ts)
      (hψ : ∀ ι, decl.constraint ι → ∀ T ∈ decl.codataTypes, ∀ d p q ps Ξ
        (Θ : Telescope decl.levels Ξ ps) (B : Term decl.levels (Ξ.extend ps.length))
        (ψ : ResultOwnership ps.length), (T.body ι).Pos d p q Ξ Θ B ψ →
        B.blockName decl.names ≠ none → ∃ χ, χ ≤ Grade.one ∧ ψ = ⟨some χ, fun _ => none⟩) :
      OwnershipSig (.typeDeclaration decl :: sig)

end Sic.Core
