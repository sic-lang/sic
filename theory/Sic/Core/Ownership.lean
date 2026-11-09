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
/-- `φ, x̄ ◀ o · r̄`: the ownerships `φ` of the variables of the scope `Γ`, extended by the ownership
`o · rᵢ` of the new variable of each entry of a telescope whose parameters are `ps`, the first one
first, `rᵢ` being the requirement of the entry. -/
def Ownership.extendFields {Γ : Scope} (φ : Var Γ .var → Grade) (o : Grade) :
    (ps : List Parameter) → Var (Γ.extend ps.length) .var → Grade
  | [] => φ
  | p :: ps => Ownership.extendFields (Γ := .var :: Γ)
      (fun | .zero => o * p.requirement | .succ x => φ x) o ps

-- ADE: none.
/-- `φ, x̄ ◀ ō`: the ownerships `φ` of the variables of the scope `Γ`, extended by the ownership `oᵢ`
of the new variable of each entry of a telescope whose parameters are `ps`, the first one first, and
`ωωᵖ`, which states nothing, for a variable without one. -/
def Ownership.extendArgs {Γ : Scope} (φ : Var Γ .var → Grade) :
    (ps : List Parameter) → List Grade → Var (Γ.extend ps.length) .var → Grade
  | [], _ => φ
  | _ :: ps, os => Ownership.extendArgs (Γ := .var :: Γ)
      (fun | .zero => os.headD .unrestrictedUnrestricted | .succ x => φ x) ps os.tail

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
  times the requirement of the entry of each field, for the variable of the field: a field of a
  unique value has the ownership its entry requires, and a field of a shared value is shared.
  RFC: `\mathsf{rec}_{◀}` -/
  | recursor {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade} {m : Mode} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {o p : Grade}
      (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (ht : Ownership sig φ (m ⊙ r) o t)
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0, u⟩)
      (hu : ∀ i j T' con u, decl.cases[i]? = some (j, T', con) →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0, u⟩ →
        Ownership sig (Ownership.extendFields φ o (con.params (.ofLists qs ps hq hp))) m p u) :
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
  the value owned alone holds, has the ownership `ψ[ō / x̄]` of the result of the destructor for
  every ownerships `ō` of its arguments that satisfy the requirements of their entries, since an
  observation reads `ψ` at the ownerships of its arguments.
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
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ → ∀ os' v,
        Parameter.Allow (m ⊙ p) ps₁ os' → ψ.value os' = some v →
        Ownership sig (Ownership.extendArgs (Ownership.extendFields φ .linearLinear ps'') ps₁ os')
          (m ⊙ p) v g) :
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

end Sic.Core
