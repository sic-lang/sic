module

public import Sic.Core.GradeVector
public import Sic.Core.Syntax

/-!
# Usage

The judgment of usage of annex 11 of RFC 36, `Σ; γ ⊢ t ▶ m`: checked in the mode `m`, the term `t`
uses each variable of its scope as the grade that `γ` gives it allows.
Usage is defined on the term and the signature alone, whose binders and entries carry the grades:
a second-order variable uses its arguments with the grades of the parameters of its telescope, which
its scope gives.

The usage of an instance of a declared type reads the grades `ζ` with which its type uses its
of its constructors or of its destructors, defined here.
of its constructors, defined here.
ADE have no second-order variables, no constants, no sorts of propositions and no declared types.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • (r · p₁) • … • (r · pₐ)`: the vector `γ` extended by a grade for each variable of a telescope
whose parameters are `ps`, the grade `pᵢ` of its entry multiplied by `r`, the first variable first. -/
def GradeVector.extendParams {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    (ps : List Parameter) → GradeVector (Γ.extend ps.length).length
  | [] => γ
  | p :: ps => GradeVector.extendParams (Γ := .var :: Γ) (γ ∙ (r * p.usage)) r ps

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • (r · q₁) • … • (r · qₐ)`: the vector `γ` extended by a grade for each variable of the
telescope `Θ`, the grade `qᵢ` with which the types after its entry use it multiplied by `r`, the
first variable first. -/
def GradeVector.extendTelescope {k : Nat} {Γ : Scope} (γ : GradeVector Γ.length) (r : Grade) :
    {ps : List Parameter} → Telescope k Γ ps → GradeVector (Γ.extend ps.length).length
  | [], .nil => γ
  | _ :: _, .cons q _ _ Θ => GradeVector.extendTelescope (Γ := .var :: Γ) (γ ∙ (r * q)) r Θ

mutual

-- ADE: `_▸[_]_`, in `Graded/Usage.agda`.
/-- `Σ; γ ⊢ t ▶ m`: checked in the mode `m`, the term `t` uses its variables as `γ` allows. -/
inductive Usage (sig : Signature) : {k : Nat} → {Γ : Scope} → GradeVector Γ.length → Mode →
    Term k Γ → Prop where
  -- ADE: `var` and `_∘ₘ_`, in `Graded/Usage.agda`, for a variable and for an application.
  /--
  The application `x[t̄]` uses `x` with the grade of the mode, and each argument `tⱼ` with the
  grade `pⱼ` of its entry, checked in the mode `m ⊙ pⱼ`; a variable with an empty telescope uses
  itself only.
  RFC: `\mathsf{var}_{X▶}`
  -/
  | var {k : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {ts : Args k Γ e.params} {m : Mode}
      {δ : GradeVector Γ.length} (hts : UsageArgs sig δ m ts) :
      Usage sig ((GradeVector.update 𝟘ᶜ x.toFin m.grade) +ᶜ δ) m (.var x ts)
  -- ADE: `defn`, in `Graded/Usage.agda`, for the definitions.
  /-- A constant, defined or declared, uses no variable, in a mode `m₁` that the mode `m₂` of its
  entry allows.
  RFC: `f_{▶}` -/
  | const {k : Nat} {Γ : Scope} {f : Name} {j k' g : Nat} {m₁ m₂ : Mode} {p : Grade}
      {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : sig.HasConstant f j k' g m₂ p A) (hm : m₁ ·ᵐ m₂ = m₁) :
      Usage sig 𝟘ᶜ m₁ (.const f qs ls ps : Term k Γ)
  -- ADE: `Uₘ`, in `Graded/Usage.agda`.
  /-- A sort uses no variable.
  RFC: `\kappa_{▶}` -/
  | sort {k : Nat} {Γ : Scope} {κ : Universe k} {m : Mode} : Usage sig 𝟘ᶜ m (.sort κ : Term k Γ)
  -- ADE: none.
  /-- An instance of a declared type uses the variables of its arguments as many times as the type
  uses its parameters, as the grades `ζ` of the type at the instance say.
  RFC: `D_{▶}` -/
  | inst {k : Nat} {Γ : Scope} {decl : TypeDeclaration} {D : Name}
      {ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {m : Mode}
      {δ : GradeVector Γ.length} (h : sig.HasDeclaredType D decl ζ) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades) (has : UsageInstanceArgs sig δ m (ζ (.ofLists qs ps hq hp)) as) :
      Usage sig δ m (.inst D qs ls ps as)
  -- ADE: none.
  /-- A constructor uses the variables of the terms of its fields, each checked in the mode of the
  grade of its field and counted with this grade, as the arguments of its telescope do; the
  instance it carries uses none.
  RFC: `c_{▶}` -/
  | ctor {k : Nat} {Γ : Scope} {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {m : Mode}
      {γ : GradeVector Γ.length} (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))} (hts : UsageArgs sig γ m ts) :
      Usage sig γ m (.ctor D qs ls ps as con.name ts.terms)
  -- ADE: `natrecₘ`, `prodrecₘ`, `unitrecₘ` and `emptyrecₘ`, in `Graded/Usage.agda`.
  /-- A recursor uses the variables of its term `r` times, the term checked in the mode `m ⊙ r`, and
  those of its branches, which share the same uses `δ` of the variables of the scope, since one of
  them runs, each using the variable of a field as `⌜m⌝ · r` times the grade of the field at the
  instance allows; its motives, which are types, use no variable, checked in the mode `00ᵐ`; in the
  mode `11ᵐ`, a recursor on a block of which a type has two constructors or more uses its term at
  run time, whose constructor chooses the branch.
  RFC: `\mathsf{rec}_{▶}` -/
  | recursor {k : Nat} {Γ : Scope} {decl : TypeDeclaration} {D : Name}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {m : Mode}
      {γ δ : GradeVector Γ.length} (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts)
      (hp : ps.length = decl.grades)
      (hC : ∀ j n (C : Term k (Γ.extend (n + 1))), Cs.get j = some ⟨n, C⟩ →
        Usage sig 𝟘ᶜ .zeroZero C)
      (ht : Usage sig γ (m ⊙ r) t) (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0, u⟩)
      (hu : ∀ i j T' con u, decl.cases[i]? = some (j, T', con) →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0, u⟩ →
        Usage sig (δ.extendParams (m.grade * r) (con.params (.ofLists qs ps hq hp))) m u)
      (hr : m = .oneOne → (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) → r.mode = .oneOne) :
      Usage sig ((r ·ᶜ γ) +ᶜ δ) m (.recursor r D qs ls ps as t Cs us)
  -- ADE: `sub`, in `Graded/Usage.agda`.
  /-- A term may be given grades lower than its uses.
  RFC: `\mathsf{sub}_{▶}` -/
  | sub {k : Nat} {Γ : Scope} {γ δ : GradeVector Γ.length} {m : Mode} {t : Term k Γ}
      (h : Usage sig γ m t) (hle : δ ≤ᶜ γ) : Usage sig δ m t

-- ADE: none.
/-- `Σ; γ ⊢ t̄ ▶ p̄; m`: checked in the mode `m`, the arguments `t̄` of a telescope whose parameters have
the grades `p̄` use the variables of their scope as `γ` allows. -/
inductive UsageArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    GradeVector Γ.length → Mode → Args k Γ ps → Prop where
  /-- No argument uses no variable.
  RFC: `\mathsf{tel}_{\varepsilon▶}` -/
  | nil {k : Nat} {Γ : Scope} {m : Mode} : UsageArgs sig 𝟘ᶜ m (.nil : Args k Γ [])
  /-- The first argument, of grade `p.usage`, checked in the mode `m ⊙ p.usage`, and the others.
  RFC: `\mathsf{tel}_{,▶}` -/
  | cons {k : Nat} {Γ : Scope} {p : Parameter} {ps : List Parameter} {t : Term k Γ}
      {ts : Args k Γ ps} {m : Mode} {γ δ : GradeVector Γ.length} (ht : Usage sig γ (m ⊙ p.usage) t)
      (hts : UsageArgs sig δ m ts) :
      UsageArgs sig ((p.usage ·ᶜ γ) +ᶜ δ) m (.cons t ts : Args k Γ (p :: ps))

-- ADE: none.
/-- `Σ; γ ⊢ ā ▶ ζ; m`: checked in the mode `m`, the arguments `ā` of an instance whose type uses its
parameters with the grades `ζ` use the variables of their scope as `γ` allows. -/
inductive UsageInstanceArgs (sig : Signature) : {k : Nat} → {Γ Δ : Scope} → GradeVector Γ.length →
    Mode → GradeVector Δ.length → InstanceArgs k Γ Δ → Prop where
  /-- No argument uses no variable.
  RFC: `\mathsf{arg}_{\varepsilon▶}` -/
  | nil {k : Nat} {Γ : Scope} {m : Mode} {ζ : GradeVector ([] : Scope).length} :
      UsageInstanceArgs sig 𝟘ᶜ m ζ (.nil : InstanceArgs k Γ [])
  /-- The arguments of the parameters before a variable, and its argument, of the grade `p` of the
  variable, checked in the mode `m ⊙ p`.
  RFC: `\mathsf{arg}_{x▶}` -/
  | var {k : Nat} {Γ Δ : Scope} {as : InstanceArgs k Γ Δ} {a : Term k Γ} {m : Mode}
      {ζ : GradeVector Δ.length} {p : Grade} {γ δ : GradeVector Γ.length}
      (has : UsageInstanceArgs sig γ m ζ as) (ha : Usage sig δ (m ⊙ p) a) :
      UsageInstanceArgs sig (Δ := Scope.Entry.var :: Δ) (γ +ᶜ (p ·ᶜ δ)) m (ζ ∙ p)
        (.snoc (e := .var) as a)
  /-- The arguments of the parameters before a second-order variable, and the abstraction for it,
  of the grade `p` of the variable, whose term, checked in the mode `m' = m ⊙ p`, uses each
  variable of the telescope as its grade `pᵢ` allows, as `⌜m'⌝ · pᵢ`.
  RFC: `\mathsf{arg}_{X▶}` -/
  | secondOrder {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend ps.length)} {m : Mode}
      {ζ : GradeVector Δ.length} {p : Grade} {γ δ : GradeVector Γ.length}
      (has : UsageInstanceArgs sig γ m ζ as)
      (hB : Usage sig (δ.extendParams (m ⊙ p).grade ps) (m ⊙ p) B) :
      UsageInstanceArgs sig (Δ := Scope.Entry.secondOrder ps ψ :: Δ) (γ +ᶜ (p ·ᶜ δ)) m (ζ ∙ p)
        (.snoc (e := .secondOrder ps ψ) as B)

end

-- ADE: `ΠΣₘ`, in `Graded/Usage.agda`, once for each entry.
/-- `Σ; γ ⊢ Θ ▶ m`: checked in the mode `m`, the types of the telescope `Θ` use the variables of its
scope as `γ` allows, each entry `x : A ▶ p; q ◀ r` counting the uses of its type `p` times, and the
types after it using `x` as `q` allows. -/
inductive UsageTelescope (sig : Signature) {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    GradeVector Γ.length → Mode → Telescope k Γ ps → Prop where
  /-- The empty telescope uses no variable.
  RFC: `\Theta_{\varepsilon▶}` -/
  | nil {Γ : Scope} {m : Mode} : UsageTelescope sig 𝟘ᶜ m (.nil : Telescope k Γ [])
  /-- The type of the first entry, checked in the mode `m ⊙ p`, and the types after it, which use
  its variable as `⌜m⌝ · q` allows.
  RFC: `\Theta_{,▶}` -/
  | cons {Γ : Scope} {ps : List Parameter} {q : Grade} {p : Parameter} {A : Term k Γ}
      {Θ : Telescope k (.var :: Γ) ps} {m : Mode} {γ δ : GradeVector Γ.length}
      (hA : Usage sig γ (m ⊙ p.usage) A) (hΘ : UsageTelescope sig (Γ := .var :: Γ) (δ ∙ (m.grade * q)) m Θ) :
      UsageTelescope sig ((p.usage ·ᶜ γ) +ᶜ δ) m (.cons q p A Θ)
  /-- A telescope may be given grades lower than its uses.
  RFC: `\mathsf{sub}_{\Theta▶}` -/
  | sub {Γ : Scope} {ps : List Parameter} {Θ : Telescope k Γ ps} {m : Mode}
      {γ δ : GradeVector Γ.length} (h : UsageTelescope sig γ m Θ) (hle : δ ≤ᶜ γ) :
      UsageTelescope sig δ m Θ

-- ADE: none.
/-- `Σ; γ ⊢ c̄ ▶ m`: checked in the mode `m`, the telescopes of the constructors `c̄` of a data type,
at the instance `ι`, use the variables of their scope as `γ` allows, the uses of all the
constructors added, since the type mentions all of them. -/
inductive UsageConstructors (sig : Signature) {j g k : Nat} {Δ : Scope} (ι : Instance j g) :
    GradeVector Δ.length → Mode → List (Constructor j g k Δ) → Prop where
  /-- No constructor uses no variable.
  RFC: `\bar c_{\varepsilon▶}` -/
  | nil {m : Mode} : UsageConstructors sig ι 𝟘ᶜ m []
  /-- The telescope of the first constructor, and those of the others.
  RFC: `\bar c_{|▶}` -/
  | cons {c : Constructor j g k Δ} {cs : List (Constructor j g k Δ)} {m : Mode}
      {γ δ : GradeVector Δ.length} (hΘ : UsageTelescope sig γ m (c.fields ι))
      (hcs : UsageConstructors sig ι δ m cs) : UsageConstructors sig ι (γ +ᶜ δ) m (c :: cs)

-- ADE: `ΠΣₘ`, in `Graded/Usage.agda`, once for each destructor.
/-- `Σ; γ ⊢ d̄ ▶ m`: checked in the mode `m`, the destructors `d̄` of a codata type use the
variables of their scope as `γ` allows, each destructor `d : (Θ ⊢ B ◀ ψ) ▶ p; q` counting the uses
of its arguments and of its result `p` times, its result using each argument as the types after the
argument do, and the destructors after it using `d` as `q` allows. -/
inductive UsageDestructors (sig : Signature) {k : Nat} : {Γ : Scope} → {ns : List Name} →
    GradeVector Γ.length → Mode → Destructors k Γ ns → Prop where
  /-- No destructor uses no variable.
  RFC: `\bar d_{\varepsilon▶}` -/
  | nil {Γ : Scope} {m : Mode} : UsageDestructors sig 𝟘ᶜ m (.nil : Destructors k Γ [])
  /-- The arguments and the result of the first destructor, checked in the mode `m' = m ⊙ p`, the
  result using each argument `xᵢ` as `⌜m'⌝ · qᵢ` allows, and the destructors after it, which use it
  as `⌜m⌝ · q` allows.
  RFC: `\bar d_{|▶}` -/
  | cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
      {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
      {ds : Destructors k (.secondOrder ps ψ :: Γ) ns} {m : Mode} {γ δ η : GradeVector Γ.length}
      (hΘ : UsageTelescope sig γ (m ⊙ p) Θ)
      (hB : Usage sig (δ.extendTelescope (m ⊙ p).grade Θ) (m ⊙ p) B)
      (hds : UsageDestructors sig (Γ := .secondOrder ps ψ :: Γ) (η ∙ (m.grade * q)) m ds) :
      UsageDestructors sig ((p ·ᶜ (γ +ᶜ δ)) +ᶜ η) m (.cons (d := d) p q Θ B ψ ds)
  /-- Destructors may be given grades lower than their uses.
  RFC: `\mathsf{sub}_{\bar d▶}` -/
  | sub {Γ : Scope} {ns : List Name} {ds : Destructors k Γ ns} {m : Mode}
      {γ δ : GradeVector Γ.length} (h : UsageDestructors sig γ m ds) (hle : δ ≤ᶜ γ) :
      UsageDestructors sig δ m ds

end Sic.Core
