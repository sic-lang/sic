module

public import Sic.Core.Ownership
public import Sic.Core.Substitution
public import Sic.Core.Usage

/-!
# Typing

The judgments of typing and of equality of annex 13 of RFC 36, with the judgments for signatures
and contexts, for the arguments of telescopes and of instances, and for the telescopes in a sort:

* `⊢ Σ`, `Σ ⊢ Γ`, `Σ; Γ ⊢ A`, `Σ; Γ ⊢ A ≡ B`, `Σ; Γ ⊢ t : A` and `Σ; Γ ⊢ t ≡ u : A`;
* `Σ; Γ ⊢ t̄ : Θ` and `Σ; Γ ⊢ t̄ ≡ ū : Θ`, the arguments of a telescope;
* `Σ; Γ ⊢ ā : Δ` and `Σ; Γ ⊢ ā ≡ b̄ : Δ`, the arguments of an instance;
* `Σ; Γ ⊢ Θ : κ` and `Σ; Γ ⊢ Θ₁ ≡ Θ₂ : κ`, telescopes in a sort, and `Σ; Γ ⊢ d̄ : κ`, destructors
  in a sort;
* `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`, `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p`,
  `Σ ⊢ data.{s̄; l̄; p̄ | C} Δ : κ where …` and `Σ ⊢ codata.{s̄; l̄; p̄ | C} Δ : κ where …`, the
  entries of the signature.

Typing and equality carry no grade; the definitions are checked for their usage.
An entry of the signature is checked for each instance of its sort and grade variables, once with
its level variables, so that its rules quantify over the instances; a type declaration only at the
instances that its constraint admits.
A variable `x` is fresh in its context by construction, being a de Bruijn index, so that the
conditions `x ∉ Γ` disappear; the condition that the names of a signature are fresh remains.

ADE have no second-order variables, no constants, no sorts of propositions and no declarations,
and their typing has a context of definitions instead of a signature.
-/

@[expose] public section

namespace Sic.Core

/-! ## Entries of Contexts -/

/-- `x : A ∈ Γ`: the variable `x` is declared with the type `A` in the context, by the cases of the
last entry; the empty context, which has no variable, has no constructor, and the type is weakened
to the scope of the context. -/
inductive Context.VarIn {k : Nat} : {Γ : Scope} → Context k Γ → Var Γ .var → Term k Γ → Prop where
  /-- The last entry.
  RFC: `\in_\Gamma.x` -/
  | zero {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      VarIn (ctx.var A) .zero (A.rename Ren.weaken)
  /-- An entry before a variable.
  RFC: `\in_\Gamma.x,y` -/
  | succVar {Γ : Scope} {ctx : Context k Γ} {x : Var Γ .var} {A B : Term k Γ} (h : VarIn ctx x A) :
      VarIn (ctx.var B) x.succ (A.rename Ren.weaken)
  /-- An entry before a second-order variable.
  RFC: `\in_\Gamma.x,Y` -/
  | succSecondOrder {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ}
      {x : Var Γ .var} {A : Term k Γ} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)}
      (h : VarIn ctx x A) : VarIn (ctx.secondOrder Θ B ψ) x.succ (A.rename Ren.weaken)

/-- `X : (Θ ⊢ A) ∈ Γ`: the second-order variable `X` is declared with the telescope `Θ` and the
type `A` in the context, by the cases of the last entry; the empty context, which has no
second-order variable, has no constructor, and the telescope and the type are weakened to the scope
of the context. -/
inductive Context.SecondOrderIn {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    {ψ : ResultOwnership ps.length} → Context k Γ → Var Γ (.secondOrder ps ψ) → Telescope k Γ ps →
    Term k (Γ.extend ps.length) → Prop where
  /-- The last entry.
  RFC: `\in_\Gamma.X` -/
  | zero {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
      SecondOrderIn (ctx.secondOrder Θ A ψ) .zero (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a variable.
  RFC: `\in_\Gamma.X,y` -/
  | succVar {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ}
      {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {B : Term k Γ} (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.var B) X.succ (Θ.rename Ren.weaken) (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a second-order variable.
  RFC: `\in_\Gamma.X,Y` -/
  | succSecondOrder {Γ : Scope} {ps qs : List Parameter} {ψ : ResultOwnership ps.length} {ψ' : ResultOwnership qs.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps}
      {A : Term k (Γ.extend ps.length)} {Θ' : Telescope k Γ qs} {B : Term k (Γ.extend qs.length)}
      (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.secondOrder Θ' B ψ') X.succ (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))

/-- `A[s̄' / s̄, l̄' / l̄, p̄' / p̄]`: the type or the body `A` of an entry of the signature at the
instance `ι` of its sort and grade variables, then at the levels `l̄'`, weakened from the empty scope
to the scope `Γ`.
RFC: `\mathsf{inst}_e` -/
def Signature.instanceType {k k' j g : Nat} {Γ : Scope} (A : Instance j g → Term k' [])
    (ι : Instance j g) (ls : Fin k' → Level k) : Term k Γ :=
  ((A ι).substLevels ls).weakenClosed

/-! ## Instantiation of the Level Variables -/

/-- A variable declared in a context is declared, with its type instantiated, in the context
instantiated. -/
theorem Context.VarIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ctx : Context k Γ} {x : Var Γ .var} {A : Term k Γ} :
    ctx.VarIn x A → (ctx.substLevels ls').VarIn x (A.substLevels ls')
  | .zero => by rw [Term.substLevels_rename]; exact .zero
  | .succVar h => by rw [Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by rw [Term.substLevels_rename]; exact .succSecondOrder (h.substLevels ls')

/-- A second-order variable declared in a context is declared, with its telescope and its type
instantiated, in the context instantiated. -/
theorem Context.SecondOrderIn.substLevels {k k' : Nat} (ls' : Fin k → Level k') {Γ : Scope}
    {ps : List Parameter} {ψ : ResultOwnership ps.length} {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)}
    {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
    ctx.SecondOrderIn X Θ A →
      (ctx.substLevels ls').SecondOrderIn X (Θ.substLevels ls') (A.substLevels ls')
  | .zero => by rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .zero
  | .succVar h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]; exact .succVar (h.substLevels ls')
  | .succSecondOrder h => by
    rw [Telescope.substLevels_rename, Term.substLevels_rename]
    exact .succSecondOrder (h.substLevels ls')

/-- An entry of the signature at the levels `ls`, then instantiated by `ls'`, is the entry at the
levels `ls` instantiated by `ls'`. -/
theorem Signature.instanceType_substLevels {k k' k'' j g : Nat} {Γ : Scope}
    (A : Instance j g → Term k' []) (ι : Instance j g) (ls : Fin k' → Level k)
    (ls' : Fin k → Level k'') :
    (Signature.instanceType A ι ls : Term k Γ).substLevels ls'
      = Signature.instanceType A ι fun i => (ls i).subst ls' := by
  rw [Signature.instanceType, Signature.instanceType, Term.weakenClosed, Term.weakenClosed,
    Term.substLevels_rename, Term.substLevels_substLevels]

mutual

-- ADE: `»_`, in `Definition/Typed.agda`, for contexts of definitions.
/-- `⊢ Σ`: the signature is well formed. -/
inductive WfSig : Signature → Prop where
  /-- The empty signature.
  RFC: `\mathsf{sig}_\varnothing` -/
  | empty : WfSig []
  /-- A constant definition, whose name is fresh.
  RFC: `\mathsf{sig}_{\mathsf{def}}` -/
  | constantDefinition {sig : Signature} {d : ConstantDefinition}
      (h : WfConstantDefinition sig d)
      (fresh : ∀ e ∈ sig, d.name ∉ e.names) : WfSig (.constantDefinition d :: sig)
  /-- A constant declaration, whose name is fresh.
  RFC: `\mathsf{sig}_{\mathsf{decl}}` -/
  | constantDeclaration {sig : Signature} {c : ConstantDeclaration}
      (h : WfConstantDeclaration sig c)
      (fresh : ∀ e ∈ sig, c.name ∉ e.names) : WfSig (.constantDeclaration c :: sig)
  /-- A type declaration, whose names of types are distinct and fresh.
  RFC: `\mathsf{sig}_{\mathsf{data}}`
  RFC: `\mathsf{sig}_{\mathsf{codata}}` -/
  | typeDeclaration {sig : Signature} {decl : TypeDeclaration}
      (h : WfTypeDeclaration sig decl) (hn : decl.names.Nodup)
      (fresh : ∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names) : WfSig (.typeDeclaration decl :: sig)

/--
`Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`: for each instance of the sort and grade variables, the type `A` is a
type of some sort and the body `t` a term of it, both in the empty context, and the body uses no
variable in the mode `m`, where its value has the ownership `p` of the definition.
-/
inductive WfConstantDefinition : Signature → ConstantDefinition → Prop where
  /-- The rule, with a sort `κ ι` of the type at each instance `ι`.
  RFC: `\mathsf{def}` -/
  | intro {sig : Signature} {d : ConstantDefinition}
      (κ : Instance d.sorts d.grades → Universe d.levels)
      (hA : ∀ ι, HasType sig .empty (d.type ι) (.sort (κ ι)))
      (ht : ∀ ι, HasType sig .empty (d.body ι) (d.type ι))
      (hu : ∀ ι, Usage sig 𝟘ᶜ d.mode (d.body ι))
      (ho : ∀ ι, Ownership sig (fun x : Var [] .var => nomatch x) d.mode d.ownership (d.body ι)) :
      WfConstantDefinition sig d

/-- `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p`: for each instance of the sort and grade variables, the type `A` is a
type of some sort in the empty context. -/
inductive WfConstantDeclaration : Signature → ConstantDeclaration → Prop where
  /-- The rule, with a sort `κ ι` of the type at each instance `ι`.
  RFC: `\mathsf{decl}` -/
  | intro {sig : Signature} {c : ConstantDeclaration}
      (κ : Instance c.sorts c.grades → Universe c.levels)
      (hA : ∀ ι, HasType sig .empty (c.type ι) (.sort (κ ι))) :
      WfConstantDeclaration sig c

-- ADE: `_»⊢_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ Γ`: the context is well formed. -/
inductive WfCtx : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Prop where
  /-- The empty context, in a well-formed signature.
  RFC: `\mathsf{ctx}_\varepsilon` -/
  | empty {sig : Signature} {k : Nat} (h : WfSig sig) : WfCtx sig (.empty : Context k [])
  /-- A variable, whose type is a type in the context.
  RFC: `\mathsf{ctx}_x` -/
  | var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : WfCtx sig (ctx.var A)
  /-- A second-order variable, whose type is a type in the context extended by its telescope, and
  the ownership `ψ` of whose result has a constant or a factor.
  RFC: `\mathsf{ctx}_X` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      (h : WfType sig (ctx.append Θ) A) (hc : ψ.constant.isSome ∨ ∃ i, (ψ.coefficient i).isSome) :
      WfCtx sig (ctx.secondOrder Θ A ψ)

-- ADE: `_⊢_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A`: `A` is a type. -/
inductive WfType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Prop where
  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- A term of a universe is a type.
  RFC: `U_{\mathsf{type}}` -/
  | univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.type, l⟩)) : WfType sig ctx A
  /-- A proposition is a type.
  RFC: `\Omega_{\mathsf{type}}` -/
  | propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.prop, l⟩)) : WfType sig ctx A

-- ADE: `_⊢_≡_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A ≡ B`: `A` and `B` are equal types. -/
inductive EqType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Prop where
  /-- The equality of types is reflexive.
  RFC: `\mathsf{refl}_{\mathsf{type}}` -/
  | refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : EqType sig ctx A A
  /-- The equality of types is symmetric.
  RFC: `\mathsf{sym}_{\mathsf{type}}` -/
  | symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      (h : EqType sig ctx A B) : EqType sig ctx B A
  /-- The equality of types is transitive.
  RFC: `\mathsf{trans}_{\mathsf{type}}` -/
  | trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A₁ A₂ A₃ : Term k Γ}
      (h₁ : EqType sig ctx A₁ A₂) (h₂ : EqType sig ctx A₂ A₃) : EqType sig ctx A₁ A₃
  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- Equal terms of a universe are equal types.
  RFC: `U_{\mathsf{type}\equiv}` -/
  | univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.type, l⟩)) : EqType sig ctx A B
  /-- Equal propositions are equal types.
  RFC: `\Omega_{\mathsf{type}\equiv}` -/
  | propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.prop, l⟩)) : EqType sig ctx A B

-- ADE: `_⊢_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t : A`: `t` is a term of type `A`. -/
inductive HasType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Prop where
  -- ADE: `var`, in `Definition/Typed.agda`.
  /-- A variable has the type of its declaration.
  RFC: `\mathsf{var}` -/
  | var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {x : Var Γ .var} {A : Term k Γ}
      (hctx : WfCtx sig ctx) (hx : ctx.VarIn x A) : HasType sig ctx (.var₀ x) A
  /-- An application of a second-order variable to arguments of its telescope has its type, in
  which the arguments are substituted for the variables of the telescope.
  RFC: `\mathsf{var}_X` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {ts : Args k Γ ps}
      (hX : ctx.SecondOrderIn X Θ A) (hts : HasArgs sig ctx ts Θ) :
      HasType sig ctx (.var X ts) (A.instantiate ts)
  -- ADE: `defn`, in `Definition/Typed.agda`, for the definitions.
  /-- A constant, defined or declared, at an instance of its variables, has its type at this
  instance.
  RFC: `f` -/
  | const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {f : Name} {j k' g : Nat}
      {m : Mode} {p : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m p A)
      (hq : qs.length = j) (hl : ls.length = k') (hp : ps.length = g) :
      HasType sig ctx (.const f qs ls ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls.getFin hl))
  -- ADE: `Uⱼ`, in `Definition/Typed.agda`.
  /-- A universe is in the universe above its level.
  RFC: `U` -/
  | univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.type, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- A universe of propositions is in the universe above its level.
  RFC: `\Omega` -/
  | prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.prop, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- An instance of a declared type that its constraint admits, whose arguments are arguments of its
  parameters, is in the sort of its type declaration.
  RFC: `D` -/
  | inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl ζ)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) :
      HasType sig ctx (.inst D qs ls ps as)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
  -- ADE: none.
  /-- A constructor of a data type, applied to arguments of its fields at the instance it carries,
  which the constraint admits and whose arguments are arguments of the parameters, is a term of this
  instance.
  RFC: `c` -/
  | ctor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope}
      (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))}
      (hts : HasArgs sig ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) :
      HasType sig ctx (.ctor D qs ls ps as con.name ts.terms) (.inst D qs ls ps as)
  -- ADE: `natrecⱼ`, `prodrecⱼ`, `unitrecⱼ` and `emptyrecⱼ`, in `Definition/Typed.agda`.
  /-- A recursor on a term of the instance it carries, which the constraint admits and whose
  arguments are arguments of the parameters, with a motive for each type of the block, a type of the
  sort `κ` over a term of the instance of this type, and a branch for each case of the block, a term
  of the motive of its type at its constructor applied to the variables of its fields, in the
  context extended by its fields and by its recursive results, has the motive of the type of the
  term at the term; the motives on a block of propositions that has a constructor are propositions.
  The positions `h'` of the type of the term in the block, `j` of a type and `i` of a case give the
  motives and the branches, as the order of the declaration does.
  RFC: `\mathsf{rec}` -/
  | recursor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k} {h' : Nat}
      {C : Term k (.var :: Γ)} (h : sig.HasDataType D decl T) (hq : qs.length = decl.sorts)
      (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (ht : HasType sig ctx t (.inst D qs ls ps as)) (hh : decl.dataTypes[h']? = some T)
      (hC : Cs.get h' = some ⟨0, C⟩) (hCl : Cs.length = decl.dataTypes.length)
      (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
      (hCt : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
        HasType sig (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hut : ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      HasType sig ctx (.recursor r D qs ls ps as t Cs us) (C.subst₀ (Subst₀.single t))
  -- ADE: `_∘ⱼ_`, `fstⱼ` and `sndⱼ`, in `Definition/Typed.agda`.
  /-- An observation of a term of the instance it carries, which the constraint admits and whose
  arguments are arguments of the parameters, by one of the destructors of its codata type, at the
  position `hd` in the destructors `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q | d̄₂)` of the type at the
  instance, applied to arguments of its telescope, has its result, the destructors `d̄₁` before it
  being the observations of the term by them, and the arguments substituted for the variables of the
  telescope.
  RFC: `d` -/
  | obs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
      {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership ps'.length} {bs : Args k Γ ps'} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (ht : HasType sig ctx t (.inst D qs ls ps as))
      (hbs : HasArgs sig ctx bs ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
      HasType sig ctx (.obs D qs ls ps as t d bs.terms)
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))).instantiate bs)
  -- ADE: none.
  /-- A corecursor of the instance it carries, which the constraint admits and whose arguments are
  arguments of the parameters, from a state, arguments of the state of its type, with a state for
  each type of the block, a telescope of a sort `κs j`, and a branch for each case of the block, is a
  term of the instance: the branch of a destructor `d`, at the position `hd` in the destructors
  `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q | d̄₂)` of its type `T'` at the instance, is a term of its result
  over the variables `ȳ` of the state of `T'` and those of the telescope of `d`, the destructors `d̄₁`
  before it being the observations of the corecursor of `T'` from `ȳ`.
  The positions `h'` of the type of the corecursor in the block, `j` of a type and `i` of a case
  give the states and the branches, as the order of the declaration does.
  RFC: `\mathsf{corec}` -/
  | corec {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Ss : States k Γ} {gs : CorecBranches k Γ} {κs : Nat → Universe k} {h' : Nat}
      {ps' : List Parameter} {S : Telescope k Γ ps'} {ss : Args k Γ ps'}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
      (hss : HasArgs sig ctx ss S) (hSl : Ss.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S' : Telescope k Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
      (hSt : ∀ j T' (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss.get j = some ⟨0, ps'', S'⟩ →
        WfTelescope sig ctx S' (κs j))
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
        HasType sig ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))) g
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
              ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))) :
      HasType sig ctx (.corec r D qs ls ps as ss.terms Ss gs) (.inst D qs ls ps as)
  -- ADE: `conv`, in `Definition/Typed.agda`.
  /-- A term has every type equal to its own.
  RFC: `\mathsf{conv}` -/
  | conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A B : Term k Γ}
      (ht : HasType sig ctx t A) (h : EqType sig ctx A B) : HasType sig ctx t B

-- ADE: `_⊢_≡_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t ≡ u : A`: `t` and `u` are equal terms of type `A`. -/
inductive EqTerm : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Term k Γ → Prop where
  /-- The equality of terms is reflexive.
  RFC: `\mathsf{refl}` -/
  | refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
      (h : HasType sig ctx t A) : EqTerm sig ctx t t A
  /-- The equality of terms is symmetric.
  RFC: `\mathsf{sym}` -/
  | symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      (h : EqTerm sig ctx t u A) : EqTerm sig ctx u t A
  /-- The equality of terms is transitive.
  RFC: `\mathsf{trans}` -/
  | trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t₁ t₂ t₃ A : Term k Γ}
      (h₁ : EqTerm sig ctx t₁ t₂ A) (h₂ : EqTerm sig ctx t₂ t₃ A) : EqTerm sig ctx t₁ t₃ A
  /-- An equality holds at every type equal to its own.
  RFC: `\mathsf{conv}_\equiv` -/
  | conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A B : Term k Γ}
      (h : EqTerm sig ctx t u A) (hA : EqType sig ctx A B) : EqTerm sig ctx t u B
  /-- Two proofs of a proposition are equal.
  RFC: `\mathsf{irr}` -/
  | irr {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      {l : Level k} (ht : HasType sig ctx t A) (hu : HasType sig ctx u A)
      (hA : HasType sig ctx A (.sort ⟨.prop, l⟩)) : EqTerm sig ctx t u A
  /-- Equal arguments give equal applications of a second-order variable.
  RFC: `\mathsf{var}_{X\equiv}` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {ts us : Args k Γ ps} (hX : ctx.SecondOrderIn X Θ A) (hts : EqArgs sig ctx ts us Θ) :
      EqTerm sig ctx (.var X ts) (.var X us) (A.instantiate ts)
  -- ADE: `δ-red`, in `Definition/Typed.agda`.
  /-- A constant definition, at an instance of its variables, unfolds to its body at this instance.
  RFC: `\delta` -/
  | delta {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {d : ConstantDefinition}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} (hctx : WfCtx sig ctx)
      (h : .constantDefinition d ∈ sig) (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
      (hp : ps.length = d.grades) :
      EqTerm sig ctx (.const d.name qs ls ps)
        (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))
        (Signature.instanceType d.type (.ofLists qs ps hq hp) (ls.getFin hl))
  /-- Two instances of a constant at equal levels are equal.
  RFC: `f_\equiv` -/
  | const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {f : Name} {j k' g : Nat}
      {m : Mode} {A : Instance j g → Term k' []} {qs : List Quality} {ls₁ ls₂ : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m p A)
      (hq : qs.length = j) (hl₁ : ls₁.length = k') (hl₂ : ls₂.length = k') (hp : ps.length = g)
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.const f qs ls₁ ps) (.const f qs ls₂ ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls₁.getFin hl₁))
  -- ADE: `U-cong`, in `Definition/Typed.agda`.
  /-- Universes at equal levels are equal.
  RFC: `U_\equiv` -/
  | univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.type, l₁⟩) (.sort ⟨.type, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- Universes of propositions at equal levels are equal.
  RFC: `\Omega_\equiv` -/
  | prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.prop, l₁⟩) (.sort ⟨.prop, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- Two instances of a declared type with equal arguments at equal levels are equal.
  RFC: `D_\equiv` -/
  | inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length}
      {qs : List Quality} {ls₁ ls₂ : List (Level k)} {ps : List Grade}
      {as₁ as₂ : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl ζ)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
  -- ADE: none.
  /-- Two applications of the same constructor, at equal arguments of the instance, at equal levels
  and at equal arguments of its fields, are equal.
  RFC: `c_\equiv` -/
  | ctor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
      {ts us : Args k Γ (con.params (.ofLists qs ps hq hp))}
      (hts : EqArgs sig ctx ts us (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)) :
      EqTerm sig ctx (.ctor D qs ls₁ ps as₁ con.name ts.terms)
        (.ctor D qs ls₂ ps as₂ con.name us.terms) (.inst D qs ls₁ ps as₁)
  -- ADE: `natrec-cong`, `prodrec-cong`, `unitrec-cong` and `emptyrec-cong`, in
  -- `Definition/Typed.agda`.
  /-- Two recursors at equal arguments of the instance, at equal levels, on equal terms, with equal
  motives and equal branches, are equal.
  RFC: `\mathsf{rec}_\equiv` -/
  | recursor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {r : Grade} {t₁ t₂ : Term k Γ} {Cs₁ Cs₂ : Motives k Γ} {us₁ us₂ : Branches k Γ}
      {κ : Universe k} {h' : Nat} {C₁ : Term k (.var :: Γ)} (h : sig.HasDataType D decl T)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
      (ht : EqTerm sig ctx t₁ t₂ (.inst D qs ls₁ ps as₁)) (hh : decl.dataTypes[h']? = some T)
      (hC : Cs₁.get h' = some ⟨0, C₁⟩) (hCl₁ : Cs₁.length = decl.dataTypes.length)
      (hCl₂ : Cs₂.length = decl.dataTypes.length)
      (hCs₁ : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs₁.get j = some ⟨0, C'⟩)
      (hCs₂ : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs₂.get j = some ⟨0, C'⟩)
      (hCt : ∀ j T' C₁' C₂', decl.dataTypes[j]? = some T' → Cs₁.get j = some ⟨0, C₁'⟩ →
        Cs₂.get j = some ⟨0, C₂'⟩ →
        EqTerm sig (ctx.var (.inst T'.name qs ls₁ ps as₁)) C₁' C₂' (.sort κ))
      (hul₁ : us₁.length = decl.cases.length) (hul₂ : us₂.length = decl.cases.length)
      (hus₁ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hus₂ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hut : ∀ i j T' con C' R u₁ u₂, decl.cases[i]? = some (j, T', con) →
        Cs₁.get j = some ⟨0, C'⟩ → con.results (.ofLists qs ps hq hp) decl.names Cs₁ = some R →
        us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
        us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
        EqTerm sig
          ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)).append R) u₁ u₂
          ((C'.atCtor T'.name qs ls₁ ps as₁ con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (.recursor r D qs ls₁ ps as₁ t₁ Cs₁ us₁)
        (.recursor r D qs ls₂ ps as₂ t₂ Cs₂ us₂) (C₁.subst₀ (Subst₀.single t₁))
  -- ADE: `app-cong`, `fst-cong` and `snd-cong`, in `Definition/Typed.agda`.
  /-- Two observations by the same destructor, at equal arguments of the instance, at equal levels,
  of equal terms, at equal arguments of its telescope, are equal.
  RFC: `d_\equiv` -/
  | obs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {t₁ t₂ : Term k Γ} {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership ps'.length} {bs₁ bs₂ : Args k Γ ps'} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
      (ht : EqTerm sig ctx t₁ t₂ (.inst D qs ls₁ ps as₁))
      (hbs : EqArgs sig ctx bs₁ bs₂ ((Θ.substLevels (ls₁.getFin hl₁)).subst
        (hd.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))) :
      EqTerm sig ctx (.obs D qs ls₁ ps as₁ t₁ d bs₁.terms) (.obs D qs ls₂ ps as₂ t₂ d bs₂.terms)
        (((B.substLevels (ls₁.getFin hl₁)).subst
          (Subst.liftN _ (hd.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))).instantiate
            bs₁)
  -- ADE: `prod-cong`, in `Definition/Typed.agda`.
  /-- Two corecursors of the same type, at equal arguments of the instance, at equal levels, from
  equal states, with equal states and equal branches, are equal: the branch of a destructor `d` of a
  type `T'` of the block is over the variables of the state of `T'` and those of the telescope of
  `d`, the destructors before it being the observations of the first corecursor of `T'` from the
  variables of its state, as `(corec)` types it.
  RFC: `\mathsf{corec}_\equiv` -/
  | corec {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {r : Grade} {Ss₁ Ss₂ : States k Γ} {gs₁ gs₂ : CorecBranches k Γ} {κs : Nat → Universe k}
      {h' : Nat} {ps' : List Parameter} {S₁ S₂ : Telescope k Γ ps'} {ss₁ ss₂ : Args k Γ ps'}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
      (hh : decl.codataTypes[h']? = some T) (hS₁ : Ss₁.get h' = some ⟨0, ps', S₁⟩)
      (hS₂ : Ss₂.get h' = some ⟨0, ps', S₂⟩) (hss : EqArgs sig ctx ss₁ ss₂ S₁)
      (hSl₁ : Ss₁.length = decl.codataTypes.length) (hSl₂ : Ss₂.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S₁' S₂' : Telescope k Γ ps''),
          Ss₁.get j = some ⟨0, ps'', S₁'⟩ ∧ Ss₂.get j = some ⟨0, ps'', S₂'⟩)
      (hSt : ∀ j T' (ps'' : List Parameter) (S₁' S₂' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        Ss₂.get j = some ⟨0, ps'', S₂'⟩ → EqTelescope sig ctx S₁' S₂' (κs j))
      (hgl₁ : gs₁.length = decl.codataCases.length) (hgl₂ : gs₂.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S₁' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
          gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S₁' : Telescope k Γ ps'') (p q : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
        (g₁ g₂ : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
        gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
        gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
        EqTerm sig ((ctx.append S₁').append ((Θ.substLevels (ls₁.getFin hl₁)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls₁ ps as₁ Ss₁ gs₁ ps'').observation T'.name
            qs ls₁ ps (as₁.rename (Ren.weakenN ps''.length)))
            (as₁.rename (Ren.weakenN ps''.length)).toSubst))) g₁ g₂
          ((B.substLevels (ls₁.getFin hl₁)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls₁ ps as₁ Ss₁ gs₁ ps'').observation T'.name
              qs ls₁ ps (as₁.rename (Ren.weakenN ps''.length)))
              (as₁.rename (Ren.weakenN ps''.length)).toSubst)))) :
      EqTerm sig ctx (.corec r D qs ls₁ ps as₁ ss₁.terms Ss₁ gs₁)
        (.corec r D qs ls₂ ps as₂ ss₂.terms Ss₂ gs₂) (.inst D qs ls₁ ps as₁)
  -- ADE: `natrec-zero`, `natrec-suc`, `prodrec-β` and `unitrec-β`, in `Definition/Typed.agda`.
  /-- A recursor on a constructor applied to arguments of its fields, with the premises of `(rec)`,
  is equal to the branch of the constructor, the case `i` of the block, with the arguments
  substituted for the variables of the fields and, for those of the recursive results, the
  recursors on the arguments of the recursive fields, at the same instance, with the same motives
  and the same branches.
  RFC: `\iota` -/
  | iota {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k} {i j : Nat}
      {C : Term k (.var :: Γ)} (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      {u : Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend
        (con.resultParams (.ofLists qs ps hq hp) decl.names).length)}
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))}
      (hts : HasArgs sig ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      (hi : decl.cases[i]? = some (j, T, con)) (hC : Cs.get j = some ⟨0, C⟩)
      (hu : us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hCl : Cs.length = decl.dataTypes.length)
      (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
      (hCt : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
        HasType sig (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hut : ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (.recursor r D qs ls ps as (.ctor D qs ls ps as con.name ts.terms) Cs us)
        ((u.instantiate ((ts.results (fun D' t => .recursor r D' qs ls ps as t Cs us)
          ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)).rename
            (Ren.weakenN _))).instantiate ts)
        (C.subst₀ (Subst₀.single (.ctor D qs ls ps as con.name ts.terms)))
  -- ADE: `unitrec-β-η`, in `Definition/Typed.agda`, for the unit type with `η`.
  /-- A term `e` over a term `t` of a data type with a single constructor without recursive field, the
  case `i` of the block, is equal to the recursor on `t`, with the premises of `(rec)`, whose motive of
  the type is that of `e` and whose branch of the constructor is `e` at the constructor applied to its
  fields.
  RFC: `\eta_c` -/
  | etaCtor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k} {i j : Nat}
      {C e : Term k (.var :: Γ)} (h : sig.HasDataType D decl T) (hc : T.constructors = [con])
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hr : ∀ R ∈ (con.fields (.ofLists qs ps hq hp)).recursion decl.names, R = none)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (ht : HasType sig ctx t (.inst D qs ls ps as))
      (he : HasType sig (ctx.var (.inst D qs ls ps as)) e C)
      (hi : decl.cases[i]? = some (j, T, con)) (hC : Cs.get j = some ⟨0, C⟩)
      (hu : us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0,
        e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))⟩)
      (hCl : Cs.length = decl.dataTypes.length)
      (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
      (hCt : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
        HasType sig (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hut : ∀ i j T' con C' R u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        con.results (.ofLists qs ps hq hp) decl.names Cs = some R →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append R)
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (e.subst₀ (Subst₀.single t)) (.recursor r D qs ls ps as t Cs us)
        (C.subst₀ (Subst₀.single t))
  -- ADE: `β-red`, `Σ-β₁` and `Σ-β₂`, in `Definition/Typed.agda`.
  /-- An observation of a corecursor by the destructor of the case `i` of the block, a destructor of
  the type of the corecursor, applied to arguments of its telescope, with the premises of `(corec)`,
  is equal to the branch of the destructor, with the terms of the state substituted for the
  variables of the state and the arguments for those of the telescope.
  RFC: `\beta` -/
  | beta {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Ss : States k Γ} {gs : CorecBranches k Γ} {κs : Nat → Universe k} {h' i : Nat}
      {ps' : List Parameter}
      {S : Telescope k Γ ps'} {ss : Args k Γ ps'} {d : Name} {p q : Grade} {ps₀ : List Parameter}
      {Ξ₀ : Scope} {Θ₀ : Telescope decl.levels Ξ₀ ps₀} {B₀ : Term decl.levels (Ξ₀.extend ps₀.length)}
      {ψ₀ : ResultOwnership ps₀.length} {g : Term k ((Γ.extend ps'.length).extend ps₀.length)}
      {bs : Args k Γ ps₀} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
      (hss : HasArgs sig ctx ss S) (hi : decl.codataCases[i]? = some (h', T, d))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ₀ Θ₀ B₀ ψ₀)
      (hg : gs.get i = some ⟨0, ps'.length, ps₀.length, g⟩)
      (hbs : HasArgs sig ctx bs ((Θ₀.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
          as.toSubst)))
      (hSl : Ss.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S' : Telescope k Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
      (hSt : ∀ j T' (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss.get j = some ⟨0, ps'', S'⟩ →
        WfTelescope sig ctx S' (κs j))
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
        HasType sig ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))) g
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
              ps (as.rename (Ren.weakenN ps''.length)))
              (as.rename (Ren.weakenN ps''.length)).toSubst)))) :
      EqTerm sig ctx (.obs D qs ls ps as (.corec r D qs ls ps as ss.terms Ss gs) d bs.terms)
        ((g.instantiate (bs.rename (Ren.weakenN ps'.length))).instantiate ss)
        (((B₀.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hd.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D
            qs ls ps as) as.toSubst))).instantiate bs)
  -- ADE: `η-eq`, `Σ-η` and `η-unit`, in `Definition/Typed.agda`.
  /-- Two terms of the instance of a codata type, whose arguments are arguments of the parameters,
  whose observations by each destructor, at the position `hd` in the destructors
  `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q | d̄₂)` of the type at the instance, are equal over the variables
  of its telescope, the destructors `d̄₁` before it being the observations of the first term by
  them, are equal.
  RFC: `\eta_d` -/
  | etaObs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t u : Term k Γ}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (ht : HasType sig ctx t (.inst D qs ls ps as)) (hu : HasType sig ctx u (.inst D qs ls ps as))
      (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
        (ψ : ResultOwnership ps'.length) (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ),
        EqTerm sig (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
          (t.observation D qs ls ps as d ps') (u.observation D qs ls ps as d ps')
          ((B.substLevels (ls.getFin hl)).subst
            (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))) :
      EqTerm sig ctx t u (.inst D qs ls ps as)

/-- `Σ; Γ ⊢ t̄ : Θ`: the arguments are typed by the telescope, each argument instantiating the types
after it, whose grades typing ignores. -/
inductive HasArgs : Signature → {k : Nat} → {Γ : Scope} → {ps : List Parameter} → Context k Γ →
    Args k Γ ps → Telescope k Γ ps → Prop where
  /-- No argument for the empty telescope.
  RFC: `\mathsf{tel}_\varepsilon` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasArgs sig ctx .nil .nil
  /-- The first argument, of the type of the first entry, and the others, of the telescope that
  it instantiates.
  RFC: `\mathsf{tel}_{,}` -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade} {p : Parameter}
      {t A : Term k Γ} {ts : Args k Γ ps} {Θ : Telescope k (.var :: Γ) ps}
      (ht : HasType sig ctx t A) (hts : HasArgs sig ctx ts (Θ.subst₀ (Subst₀.single t))) :
      HasArgs sig ctx (.cons t ts) (.cons q p A Θ)

/-- `Σ; Γ ⊢ t̄ ≡ ū : Θ`: the arguments are equal, typed by the telescope. -/
inductive EqArgs : Signature → {k : Nat} → {Γ : Scope} → {ps : List Parameter} → Context k Γ →
    Args k Γ ps → Args k Γ ps → Telescope k Γ ps → Prop where
  /-- No argument for the empty telescope.
  RFC: `\mathsf{tel}_{\varepsilon\equiv}` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqArgs sig ctx .nil .nil .nil
  /-- The first arguments, equal at the type of the first entry, and the others, equal in the
  telescope that the first argument instantiates.
  RFC: `\mathsf{tel}_{,\equiv}` -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade} {p : Parameter}
      {t u A : Term k Γ} {ts us : Args k Γ ps} {Θ : Telescope k (.var :: Γ) ps}
      (ht : EqTerm sig ctx t u A) (hts : EqArgs sig ctx ts us (Θ.subst₀ (Subst₀.single t))) :
      EqArgs sig ctx (.cons t ts) (.cons u us) (.cons q p A Θ)

/-- `Σ; Γ ⊢ ā : Δ`: the arguments of an instance are typed by its parameters, each argument
instantiating the types after it. -/
inductive HasInstanceArgs : Signature → {k : Nat} → {Γ Δ : Scope} → Context k Γ →
    InstanceArgs k Γ Δ → Context k Δ → Prop where
  /-- No argument for the empty parameters.
  RFC: `\mathsf{arg}_\varepsilon` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasInstanceArgs sig ctx .nil .empty
  /-- The arguments of the parameters before a variable, and the argument of its type, which they
  instantiate.
  RFC: `\mathsf{arg}_x` -/
  | var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
      {params : Context k Δ} {a : Term k Γ} {A : Term k Δ}
      (has : HasInstanceArgs sig ctx as params) (ha : HasType sig ctx a (A.subst as.toSubst)) :
      HasInstanceArgs sig ctx (.snoc (e := .var) as a) (params.var A)
  /-- The arguments of the parameters before a second-order variable, and the abstraction for it, a
  term of its type under the variables of its telescope, which they instantiate.
  RFC: `\mathsf{arg}_X` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
      (has : HasInstanceArgs sig ctx as params)
      (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B
        (A.subst (Subst.liftN _ as.toSubst))) :
      HasInstanceArgs sig ctx (.snoc (e := .secondOrder ps ψ) as B)
        (params.secondOrder Θ A ψ)

/-- `Σ; Γ ⊢ ā₁ ≡ ā₂ : Δ`: the arguments of two instances are equal, typed by the parameters. -/
inductive EqInstanceArgs : Signature → {k : Nat} → {Γ Δ : Scope} → Context k Γ →
    InstanceArgs k Γ Δ → InstanceArgs k Γ Δ → Context k Δ → Prop where
  /-- No argument for the empty parameters.
  RFC: `\mathsf{arg}_{\varepsilon\equiv}` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqInstanceArgs sig ctx .nil .nil .empty
  /-- Equal arguments of the parameters before a variable, and equal arguments of its type, which
  the first ones instantiate.
  RFC: `\mathsf{arg}_{x\equiv}` -/
  | var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} {a₁ a₂ : Term k Γ} {A : Term k Δ}
      (has : EqInstanceArgs sig ctx as₁ as₂ params)
      (ha : EqTerm sig ctx a₁ a₂ (A.subst as₁.toSubst)) :
      EqInstanceArgs sig ctx (.snoc (e := .var) as₁ a₁) (.snoc (e := .var) as₂ a₂) (params.var A)
  /-- Equal arguments of the parameters before a second-order variable, and equal abstractions for
  it, under the variables of its telescope, which the first ones instantiate.
  RFC: `\mathsf{arg}_{X\equiv}` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership ps.length}
      {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (has : EqInstanceArgs sig ctx as₁ as₂ params)
      (hB : EqTerm sig (ctx.append (Θ.subst as₁.toSubst)) B₁ B₂
        (A.subst (Subst.liftN _ as₁.toSubst))) :
      EqInstanceArgs sig ctx (.snoc (e := .secondOrder ps ψ) as₁ B₁)
        (.snoc (e := .secondOrder ps ψ) as₂ B₂) (params.secondOrder Θ A ψ)

/--
`Σ; Γ ⊢ Θ : κ`: the telescope lives in the sort `κ`, each of its types living in a sort that `κ`
bounds, and an entry whose type is a proposition has a grade without use at run time.
-/
inductive WfTelescope : Signature → {k : Nat} → {Γ : Scope} → {ps : List Parameter} → Context k Γ →
    Telescope k Γ ps → Universe k → Prop where
  /-- The empty telescope lives in every sort.
  RFC: `\mathsf{tel}_{\kappa\varepsilon}` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {κ : Universe k}
      (hctx : WfCtx sig ctx) : WfTelescope sig ctx .nil κ
  /-- The first entry, whose type lives in a sort that `κ₂` bounds, with a grade without use at
  run time if it is a proposition, and the others.
  RFC: `\mathsf{tel}_{\kappa,}` -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade}
      {p : Parameter} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps} {κ₁ κ₂ : Universe k}
      (hA : HasType sig ctx A (.sort κ₁)) (hκ : κ₁ ≼ κ₂) (hΘ : WfTelescope sig (ctx.var A) Θ κ₂)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfTelescope sig ctx (.cons q p A Θ) κ₂

-- ADE: none.
/--
`Σ; Γ ⊢ Θ₁ ≡ Θ₂ : κ`: the telescopes are equal in the sort `κ`, entry by entry, with the same grades,
their types being equal types of a sort that `κ` bounds, and an entry whose type is a proposition has
a grade without use at run time.
-/
inductive EqTelescope : Signature → {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    Context k Γ → Telescope k Γ ps → Telescope k Γ ps → Universe k → Prop where
  /-- The empty telescope is equal to itself in every sort.
  RFC: `\mathsf{tel}_{\kappa\varepsilon\equiv}` -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {κ : Universe k}
      (hctx : WfCtx sig ctx) : EqTelescope sig ctx .nil .nil κ
  /-- The first entries, with the same grades, whose types are equal types of a sort that `κ₂`
  bounds, with a grade without use at run time if they are propositions, and the others, equal in
  the context extended by the first entry of the first telescope.
  RFC: `\mathsf{tel}_{\kappa,\equiv}` -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {q : Grade} {p : Parameter} {A₁ A₂ : Term k Γ} {Θ₁ Θ₂ : Telescope k (.var :: Γ) ps}
      {κ₁ κ₂ : Universe k} (hA : EqTerm sig ctx A₁ A₂ (.sort κ₁)) (hκ : κ₁ ≼ κ₂)
      (hΘ : EqTelescope sig (ctx.var A₁) Θ₁ Θ₂ κ₂)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      EqTelescope sig ctx (.cons q p A₁ Θ₁) (.cons q p A₂ Θ₂) κ₂

-- ADE: none.
/--
`Σ; Γ ⊢_𝒟 Θ : κ`: the fields `Θ` of a constructor of the block of data types `decl`, at the instance
`ι` of its sort and grade variables, live in the sort `κ`, in the context `Γ` of the parameters
extended by the fields before them that are not recursive, where `ā` are the parameters
themselves.
A field whose type is an instance of a type of the block is recursive: its type is this type at the
instance of the block, at its level variables and at the parameters themselves, and no field after
it depends on it, so that it does not extend the context.
The type of a field that is not recursive lives in a sort that `κ` bounds, with a grade without use
at run time if it is a proposition, in the signature `Σ`, which the block does not extend, so that no
type of the block occurs in it.
The RFC writes the parameters themselves as the variables `x̄_Δ`, the same under every field; the
Lean carries them as the arguments `ā` of the parameters in the scope of the fields, the identity
renamed under the fields before, since de Bruijn indices shift under each field.
-/
inductive WfFields : Signature → (decl : TypeDeclaration) → Instance decl.sorts decl.grades →
    {Γ : Scope} → InstanceArgs decl.levels Γ decl.scope → Context decl.levels Γ →
    {ps : List Parameter} →
    Telescope decl.levels Γ ps → Universe decl.levels → Prop where
  /-- No field.
  RFC: `\mathsf{fields}_\varepsilon` -/
  | nil {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {κ : Universe decl.levels}
      (hctx : WfCtx sig ctx) : WfFields sig decl ι as ctx .nil κ
  /-- A first field that is not recursive, whose type lives in a sort that `κ` bounds, and the
  others, in the context extended by it.
  RFC: `\mathsf{fields}_{,}` -/
  | cons {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {q : Grade} {p : Parameter} {A : Term decl.levels Γ}
      {Θ : Telescope decl.levels (.var :: Γ) ps} {κ₁ κ : Universe decl.levels}
      (hn : A.blockName decl.names = none) (hA : HasType sig ctx A (.sort κ₁)) (hκ : κ₁ ≼ κ)
      (hΘ : WfFields sig decl ι (as.rename Ren.weaken) (ctx.var A) Θ κ)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfFields sig decl ι as ctx (.cons q p A Θ) κ
  /-- A first field that is recursive, a type `D` of the block at the instance of the block and at
  the parameters, with a grade without use at run time if the block is a block of propositions, and
  the others, which do not depend on it, in the same context.
  RFC: `\mathsf{fields}_{\mathsf{rec}}` -/
  | recursive {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {q : Grade} {p : Parameter} {D : Name} {Θ : Telescope decl.levels Γ ps}
      {κ : Universe decl.levels} (hD : D ∈ decl.names) (hΘ : WfFields sig decl ι as ctx Θ κ)
      (hp : κ.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfFields sig decl ι as ctx (.cons q p (decl.blockInstance ι D as) (Θ.rename Ren.weaken)) κ

-- ADE: none.
/--
`Σ; Γ ⊢_𝒟 d̄ : κ`: the destructors `d̄` of a codata type of the block `decl`, at the instance `ι` of
its sort and grade variables, live in the sort `κ = s_l`, in the context `Γ` of the parameters
extended by the destructors before them that are not recursive, where `ā` are the parameters
themselves: the arguments of each destructor live in the universe `U_l`, and each destructor that is
not recursive is a second-order variable of the context of the destructors after it.
A destructor whose result is an instance of a type of the block is recursive: its result is this
type at the instance of the block, at its level variables and at the parameters themselves, with a
grade without use at run time if the block is a block of propositions, and no destructor after it
depends on it, so that it does not extend the context.
The result of a destructor that is not recursive lives in a sort that `κ` bounds, with a grade
without use at run time if it is a proposition.
The arguments and the results are checked in the signature `Σ`, which the block does not extend, so
that the types of the block occur only as the results of the recursive destructors.
The RFC writes the parameters themselves as the variables `x̄_Δ`; the Lean carries them as the
arguments `ā` of the parameters, renamed under the destructors before and under the arguments, as for
the fields.
-/
inductive WfDestructors : Signature → (decl : TypeDeclaration) → Instance decl.sorts decl.grades →
    {Γ : Scope} → {ns : List Name} → InstanceArgs decl.levels Γ decl.scope →
    Context decl.levels Γ → Destructors decl.levels Γ ns → Universe decl.levels → Prop where
  /-- No destructor lives in every sort.
  RFC: `\bar d_{\kappa\varepsilon}` -/
  | nil {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ}
      {κ : Universe decl.levels} (hctx : WfCtx sig ctx) : WfDestructors sig decl ι as ctx .nil κ
  /-- A first destructor that is not recursive, whose arguments live in the universe of the level of
  `κ` and whose result lives in a sort that `κ` bounds, with a grade without use at run time if it is
  a proposition, and the others, in the context extended by it.
  RFC: `\bar d_{\kappa|}` -/
  | cons {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {ctx : Context decl.levels Γ} {p q : Grade}
      {Θ : Telescope decl.levels Γ ps} {B : Term decl.levels (Γ.extend ps.length)}
      {ψ : ResultOwnership ps.length} {ds : Destructors decl.levels (.secondOrder ps ψ :: Γ) ns}
      {κ₁ κ : Universe decl.levels} (hn : B.blockName decl.names = none)
      (hΘ : WfTelescope sig ctx Θ ⟨.type, κ.level⟩)
      (hB : HasType sig (ctx.append Θ) B (.sort κ₁)) (hκ : κ₁ ≼ κ)
      (hp : κ₁.quality = .prop → p.mode ≠ .oneOne)
      (hds : WfDestructors sig decl ι (as.rename Ren.weaken) (ctx.secondOrder Θ B ψ) ds κ) :
      WfDestructors sig decl ι as ctx (.cons (d := d) p q Θ B ψ ds) κ
  /-- A first destructor that is recursive, whose arguments live in the universe of the level of `κ`
  and whose result is a type `D` of the block at the instance of the block and at the parameters,
  with a grade without use at run time if the block is a block of propositions, and the others,
  which do not depend on it, in the same context.
  RFC: `\bar d_{\kappa\mathsf{rec}}` -/
  | recursive {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {d : Name} {ns : List Name}
      {ps : List Parameter} {ctx : Context decl.levels Γ} {p q : Grade}
      {Θ : Telescope decl.levels Γ ps} {ψ : ResultOwnership ps.length} {D : Name}
      {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} (hD : D ∈ decl.names)
      (hΘ : WfTelescope sig ctx Θ ⟨.type, κ.level⟩)
      (hp : κ.quality = .prop → p.mode ≠ .oneOne)
      (hds : WfDestructors sig decl ι as ctx ds κ) :
      WfDestructors sig decl ι as ctx
        (.cons (d := d) p q Θ (decl.blockInstance ι D (as.rename (Ren.weakenN ps.length))) ψ
          (ds.rename Ren.weaken)) κ

-- ADE: none.
/--
`Σ ⊢ 𝒟`: the type declaration is well formed.
A block of data types is well formed when its constraint `C` admits an instance of the sort and grade
variables and, for each instance it admits, the parameters `Δ` form a context, the fields of each constructor live in the sort `κ`, and the
constructors of each type `Dⱼ` use the parameters as its grades `ζⱼ` allow, in the signature
extended by the block; the constructors of each type have distinct names.
The fields may be recursive, as the judgment of the fields allows.
A block of codata types likewise, with the destructors of each type in place of its constructors,
which may be recursive, as the judgment of the destructors allows.
-/
inductive WfTypeDeclaration : Signature → TypeDeclaration → Prop where
  /-- A block of data types, with the uses `γ` of the constructors of each type at each instance.
  RFC: `\mathsf{data}` -/
  | data {sig : Signature} {decl : TypeDeclaration} {Ts : List (DataType decl.sorts decl.grades
      decl.levels decl.scope)} (hb : decl.body = .data Ts)
      (hadm : ∃ ι, decl.constraint ι) (hΔ : ∀ ι, decl.constraint ι → WfCtx sig (decl.params ι))
      (hΘ : ∀ ι, decl.constraint ι → ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        WfFields sig decl ι (.identity decl.scope) (decl.params ι) (c.fields ι) (decl.sort ι))
      (hu : ∀ ι, decl.constraint ι → ∀ T ∈ decl.dataTypes, ∃ γ,
        UsageConstructors (.typeDeclaration decl :: sig) ι γ .oneOne T.constructors ∧
        T.usage ι ≤ᶜ γ)
      (hc : ∀ T ∈ decl.dataTypes, (T.constructors.map (·.name)).Nodup) :
      WfTypeDeclaration sig decl
  /-- A block of codata types, with the uses `γ` of the destructors of each type at each instance.
  RFC: `\mathsf{codata}` -/
  | codata {sig : Signature} {decl : TypeDeclaration} {Ts : List (CodataType decl.sorts
      decl.grades decl.levels decl.scope)} (hb : decl.body = .codata Ts)
      (hadm : ∃ ι, decl.constraint ι) (hΔ : ∀ ι, decl.constraint ι → WfCtx sig (decl.params ι))
      (hd : ∀ ι, decl.constraint ι → ∀ T ∈ decl.codataTypes,
        WfDestructors sig decl ι (.identity decl.scope) (decl.params ι) (T.body ι) (decl.sort ι))
      (hu : ∀ ι, decl.constraint ι → ∀ T ∈ decl.codataTypes, ∃ γ,
        UsageDestructors (.typeDeclaration decl :: sig) γ .oneOne (T.body ι) ∧ T.usage ι ≤ᶜ γ)
      (hc : ∀ T ∈ decl.codataTypes, T.destructors.Nodup) :
      WfTypeDeclaration sig decl

end

/-! ## Presuppositions

Every judgment holds in a well-formed signature, and the signature that a well-formed signature
extends is well formed: each rule has a premise that is a judgment in the same signature, down to the
rule `(ctx_ε)`, whose premise is `⊢ Σ`.
The proof is by mutual structural recursion on the derivations, through such a premise, in the
clause `where` of the theorem, whose auxiliary theorems give the fields of the record.
-/

-- ADE: none.
/-- An instance of `j` sort variables and `g` grade variables, which exists whatever `j` and `g`. -/
def Instance.default (j g : Nat) : Instance j g := ⟨fun _ => .type, fun _ => Grade.zero⟩

-- ADE: `wf` and `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`, for the contexts and
-- the judgments in a context of definitions.
/-- Every judgment holds in a well-formed signature, and the signature that a well-formed signature
extends is well formed. -/
structure Presuppositions : Prop where
  /-- A well-formed constant definition is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{def}` -/
  wfConstantDefinition : ∀ {sig : Signature} {d : ConstantDefinition},
    WfConstantDefinition sig d → WfSig sig
  /-- A well-formed constant declaration is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{decl}` -/
  wfConstantDeclaration : ∀ {sig : Signature} {c : ConstantDeclaration},
    WfConstantDeclaration sig c → WfSig sig
  /-- A well-formed context is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Gamma` -/
  wfCtx : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ},
    WfCtx sig ctx → WfSig sig
  /-- A type is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ},
    WfType sig ctx A → WfSig sig
  /-- An equality of types is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ},
    EqType sig ctx A B → WfSig sig
  /-- A typing is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    HasType sig ctx t A → WfSig sig
  /-- An equality of terms is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ},
    EqTerm sig ctx t u A → WfSig sig
  /-- Arguments of a telescope are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, HasArgs sig ctx ts Θ → WfSig sig
  /-- Equal arguments of a telescope are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, EqArgs sig ctx ts us Θ → WfSig sig
  /-- Arguments of an instance are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    HasInstanceArgs sig ctx as params → WfSig sig
  /-- Equal arguments of instances are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    EqInstanceArgs sig ctx as₁ as₂ params → WfSig sig
  /-- A telescope in a sort is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {Θ : Telescope k Γ ps} {κ : Universe k}, WfTelescope sig ctx Θ κ → WfSig sig
  /-- An equality of telescopes in a sort is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → WfSig sig
  /-- The fields of a constructor in a sort are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{fields}` -/
  wfFields : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
    {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
    {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels},
    WfFields sig decl ι as ctx Θ κ → WfSig sig
  /-- The destructors of a codata type in a sort are in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\bar d` -/
  wfDestructors : ∀ {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
    {Γ : Scope} {ns : List Name} {as : InstanceArgs decl.levels Γ decl.scope}
    {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels},
    WfDestructors sig decl ι as ctx ds κ → WfSig sig
  /-- A well-formed type declaration is in a well-formed signature.
  RFC: `\mathsf{presup}_\Sigma.\mathsf{data}`
  RFC: `\mathsf{presup}_\Sigma.\mathsf{codata}` -/
  wfTypeDeclaration : ∀ {sig : Signature} {decl : TypeDeclaration},
    WfTypeDeclaration sig decl → WfSig sig
  /-- The signature that a well-formed signature extends is well formed.
  RFC: `\mathsf{presup}_\Sigma.e` -/
  tail : ∀ {e : Entry} {sig : Signature}, WfSig (e :: sig) → WfSig sig

-- ADE: `wf` and `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`, for the contexts and
-- the judgments in a context of definitions.
/-- The judgments hold in well-formed signatures.
RFC: `\mathsf{presup}_\Sigma.\mathsf{def}`
RFC: `\mathsf{presup}_\Sigma.\mathsf{decl}`
RFC: `\mathsf{presup}_\Sigma.\Gamma`
RFC: `\mathsf{presup}_\Sigma.A`
RFC: `\mathsf{presup}_\Sigma.A_\equiv`
RFC: `\mathsf{presup}_\Sigma.t`
RFC: `\mathsf{presup}_\Sigma.t_\equiv`
RFC: `\mathsf{presup}_\Sigma.\bar t`
RFC: `\mathsf{presup}_\Sigma.\bar t_\equiv`
RFC: `\mathsf{presup}_\Sigma.\bar a`
RFC: `\mathsf{presup}_\Sigma.\bar a_\equiv`
RFC: `\mathsf{presup}_\Sigma.\Theta`
RFC: `\mathsf{presup}_\Sigma.\Theta_\equiv`
RFC: `\mathsf{presup}_\Sigma.\mathsf{fields}`
RFC: `\mathsf{presup}_\Sigma.\bar d`
RFC: `\mathsf{presup}_\Sigma.\mathsf{data}`
RFC: `\mathsf{presup}_\Sigma.\mathsf{codata}`
RFC: `\mathsf{presup}_\Sigma.e` -/
theorem presuppositions : Presuppositions :=
  ⟨wfConstantDefinition, wfConstantDeclaration, wfCtx, wfType, eqType, hasType, eqTerm, hasArgs,
    eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope, eqTelescope, wfFields, wfDestructors,
    wfTypeDeclaration, tail⟩
where
  wfConstantDefinition {sig : Signature} {d : ConstantDefinition} :
      WfConstantDefinition sig d → WfSig sig
    | .intro _ hA _ _ _ => hasType (hA (.default _ _))
  wfConstantDeclaration {sig : Signature} {c : ConstantDeclaration} :
      WfConstantDeclaration sig c → WfSig sig
    | .intro _ hA => hasType (hA (.default _ _))
  wfCtx {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} : WfCtx sig ctx → WfSig sig
    | .empty h => h
    | .var h => wfType h
    | .secondOrder h _ => wfType h
  wfType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      WfType sig ctx A → WfSig sig
    | .univType h => hasType h
    | .propType h => hasType h
  eqType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ} :
      EqType sig ctx A B → WfSig sig
    | .refl h => wfType h
    | .symm h => eqType h
    | .trans h _ => eqType h
    | .univType h => eqTerm h
    | .propType h => eqTerm h
  hasType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ} :
      HasType sig ctx t A → WfSig sig
    | .var hctx _ => wfCtx hctx
    | .secondOrder _ hts => hasArgs hts
    | .const hctx _ _ _ _ => wfCtx hctx
    | .univ hctx => wfCtx hctx
    | .prop hctx => wfCtx hctx
    | .inst _ _ _ _ _ has => hasInstanceArgs has
    | .ctor _ _ _ _ _ _ has _ => hasInstanceArgs has
    | .recursor _ _ _ _ _ has .. => hasInstanceArgs has
    | .obs _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ has .. => hasInstanceArgs has
    | .conv ht _ => hasType ht
  eqTerm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ} :
      EqTerm sig ctx t u A → WfSig sig
    | .refl h => hasType h
    | .symm h => eqTerm h
    | .trans h _ => eqTerm h
    | .conv h _ => eqTerm h
    | .irr ht _ _ => hasType ht
    | .secondOrder _ hts => eqArgs hts
    | .delta hctx _ _ _ _ => wfCtx hctx
    | .const hctx .. => wfCtx hctx
    | .univ hctx _ => wfCtx hctx
    | .prop hctx _ => wfCtx hctx
    | .inst _ _ _ _ _ _ has _ => eqInstanceArgs has
    | .ctor _ _ _ _ _ _ _ has _ _ => eqInstanceArgs has
    | .recursor _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .obs _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .iota _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaCtor _ _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .beta _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaObs _ _ _ _ _ has .. => hasInstanceArgs has
  hasArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} : HasArgs sig ctx ts Θ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons ht _ => hasType ht
  eqArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} : EqArgs sig ctx ts us Θ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons ht _ => eqTerm ht
  hasInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
      HasInstanceArgs sig ctx as params → WfSig sig
    | .nil hctx => wfCtx hctx
    | .var has _ => hasInstanceArgs has
    | .secondOrder has _ => hasInstanceArgs has
  eqInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} :
      EqInstanceArgs sig ctx as₁ as₂ params → WfSig sig
    | .nil hctx => wfCtx hctx
    | .var has _ => eqInstanceArgs has
    | .secondOrder has _ => eqInstanceArgs has
  wfTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {κ : Universe k} : WfTelescope sig ctx Θ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons hA _ _ _ => hasType hA
  eqTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} : EqTelescope sig ctx Θ₁ Θ₂ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons hA _ _ _ => eqTerm hA
  wfFields {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {Θ : Telescope decl.levels Γ ps} {κ : Universe decl.levels} :
      WfFields sig decl ι as ctx Θ κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons _ hA _ _ _ => hasType hA
    | .recursive _ hΘ _ => wfFields hΘ
  wfDestructors {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ns : List Name} {as : InstanceArgs decl.levels Γ decl.scope}
      {ctx : Context decl.levels Γ} {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} :
      WfDestructors sig decl ι as ctx ds κ → WfSig sig
    | .nil hctx => wfCtx hctx
    | .cons _ hΘ .. => wfTelescope hΘ
    | .recursive _ hΘ .. => wfTelescope hΘ
  wfTypeDeclaration {sig : Signature} {decl : TypeDeclaration} :
      WfTypeDeclaration sig decl → WfSig sig
    | .data _ ⟨_, hadm⟩ hΔ _ _ _ => wfCtx (hΔ _ hadm)
    | .codata _ ⟨_, hadm⟩ hΔ _ _ _ => wfCtx (hΔ _ hadm)
  tail {e : Entry} {sig : Signature} : WfSig (e :: sig) → WfSig sig
    | .constantDefinition h _ => wfConstantDefinition h
    | .constantDeclaration h _ => wfConstantDeclaration h
    | .typeDeclaration h _ _ => wfTypeDeclaration h

-- ADE: `wfTerm`, `wfEqTerm` and their kin, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Every judgment in a context holds in a well-formed context. -/
structure ContextPresuppositions : Prop where
  /-- A type is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.A` -/
  wfType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ},
    WfType sig ctx A → WfCtx sig ctx
  /-- An equality of types is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.A_\equiv` -/
  eqType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ},
    EqType sig ctx A B → WfCtx sig ctx
  /-- A typing is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.t` -/
  hasType : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ},
    HasType sig ctx t A → WfCtx sig ctx
  /-- An equality of terms is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.t_\equiv` -/
  eqTerm : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ},
    EqTerm sig ctx t u A → WfCtx sig ctx
  /-- Arguments of a telescope are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar t` -/
  hasArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts : Args k Γ ps} {Θ : Telescope k Γ ps}, HasArgs sig ctx ts Θ → WfCtx sig ctx
  /-- Equal arguments of a telescope are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar t_\equiv` -/
  eqArgs : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {ts us : Args k Γ ps} {Θ : Telescope k Γ ps}, EqArgs sig ctx ts us Θ → WfCtx sig ctx
  /-- Arguments of an instance are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar a` -/
  hasInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ},
    HasInstanceArgs sig ctx as params → WfCtx sig ctx
  /-- Equal arguments of instances are in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\bar a_\equiv` -/
  eqInstanceArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ},
    EqInstanceArgs sig ctx as₁ as₂ params → WfCtx sig ctx
  /-- A telescope in a sort is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\Theta` -/
  wfTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
    {Θ : Telescope k Γ ps} {κ : Universe k}, WfTelescope sig ctx Θ κ → WfCtx sig ctx
  /-- An equality of telescopes in a sort is in a well-formed context.
  RFC: `\mathsf{presup}_\Gamma.\Theta_\equiv` -/
  eqTelescope : ∀ {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → WfCtx sig ctx

-- ADE: `wfTerm`, `wfEqTerm` and their kin, in `Definition/Typed/Properties/Well-formed.agda`.
/-- The judgments in a context hold in a well-formed context.
RFC: `\mathsf{presup}_\Gamma.A`
RFC: `\mathsf{presup}_\Gamma.A_\equiv`
RFC: `\mathsf{presup}_\Gamma.t`
RFC: `\mathsf{presup}_\Gamma.t_\equiv`
RFC: `\mathsf{presup}_\Gamma.\bar t`
RFC: `\mathsf{presup}_\Gamma.\bar t_\equiv`
RFC: `\mathsf{presup}_\Gamma.\bar a`
RFC: `\mathsf{presup}_\Gamma.\bar a_\equiv`
RFC: `\mathsf{presup}_\Gamma.\Theta`
RFC: `\mathsf{presup}_\Gamma.\Theta_\equiv` -/
theorem contextPresuppositions : ContextPresuppositions :=
  ⟨wfType, eqType, hasType, eqTerm, hasArgs, eqArgs, hasInstanceArgs, eqInstanceArgs, wfTelescope,
    eqTelescope⟩
where
  wfType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      WfType sig ctx A → WfCtx sig ctx
    | .univType h => hasType h
    | .propType h => hasType h
  eqType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ} :
      EqType sig ctx A B → WfCtx sig ctx
    | .refl h => wfType h
    | .symm h => eqType h
    | .trans h _ => eqType h
    | .univType h => eqTerm h
    | .propType h => eqTerm h
  hasType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ} :
      HasType sig ctx t A → WfCtx sig ctx
    | .var hctx _ => hctx
    | .secondOrder _ hts => hasArgs hts
    | .const hctx _ _ _ _ => hctx
    | .univ hctx => hctx
    | .prop hctx => hctx
    | .inst _ _ _ _ _ has => hasInstanceArgs has
    | .ctor _ _ _ _ _ _ has _ => hasInstanceArgs has
    | .recursor _ _ _ _ _ has .. => hasInstanceArgs has
    | .obs _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ has .. => hasInstanceArgs has
    | .conv ht _ => hasType ht
  eqTerm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ} :
      EqTerm sig ctx t u A → WfCtx sig ctx
    | .refl h => hasType h
    | .symm h => eqTerm h
    | .trans h _ => eqTerm h
    | .conv h _ => eqTerm h
    | .irr ht _ _ => hasType ht
    | .secondOrder _ hts => eqArgs hts
    | .delta hctx _ _ _ _ => hctx
    | .const hctx .. => hctx
    | .univ hctx _ => hctx
    | .prop hctx _ => hctx
    | .inst _ _ _ _ _ _ has _ => eqInstanceArgs has
    | .ctor _ _ _ _ _ _ _ has _ _ => eqInstanceArgs has
    | .recursor _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .obs _ _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .iota _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaCtor _ _ _ _ _ _ _ has .. => hasInstanceArgs has
    | .corec _ _ _ _ _ _ has .. => eqInstanceArgs has
    | .beta _ _ _ _ _ has .. => hasInstanceArgs has
    | .etaObs _ _ _ _ _ has .. => hasInstanceArgs has
  hasArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts : Args k Γ ps} {Θ : Telescope k Γ ps} : HasArgs sig ctx ts Θ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons ht _ => hasType ht
  eqArgs {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} : EqArgs sig ctx ts us Θ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons ht _ => eqTerm ht
  hasInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
      HasInstanceArgs sig ctx as params → WfCtx sig ctx
    | .nil hctx => hctx
    | .var has _ => hasInstanceArgs has
    | .secondOrder has _ => hasInstanceArgs has
  eqInstanceArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} :
      EqInstanceArgs sig ctx as₁ as₂ params → WfCtx sig ctx
    | .nil hctx => hctx
    | .var has _ => eqInstanceArgs has
    | .secondOrder has _ => eqInstanceArgs has
  wfTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {κ : Universe k} : WfTelescope sig ctx Θ κ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons hA _ _ _ => hasType hA
  eqTelescope {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {κ : Universe k} : EqTelescope sig ctx Θ₁ Θ₂ κ → WfCtx sig ctx
    | .nil hctx => hctx
    | .cons hA _ _ _ => eqTerm hA

-- ADE: none.
/-- The last entry of a well-formed signature introduces names that no entry before it does. -/
theorem WfSig.fresh {e : Entry} {sig : Signature} :
    WfSig (e :: sig) → ∀ e' ∈ sig, ∀ n ∈ e.names, n ∉ e'.names
  | .constantDefinition _ h, e', he', n, hn => by
    simp only [Entry.names, List.mem_singleton] at hn
    exact hn ▸ h e' he'
  | .constantDeclaration _ h, e', he', n, hn => by
    simp only [Entry.names, List.mem_singleton] at hn
    exact hn ▸ h e' he'
  | .typeDeclaration _ _ h, e', he', n, hn => h e' he' n hn

-- ADE: none.
/-- The names of a well-formed signature are distinct.
RFC: `\mathsf{distinct}_\Sigma` -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨(Presuppositions.tail presuppositions h).distinct,
      by cases h with
        | typeDeclaration _ hn _ => exact hn
        | _ => exact List.pairwise_singleton _ _, h.fresh,
      by cases h with
        | typeDeclaration hdecl _ _ => cases hdecl with
          | data hb _ _ _ _ hc =>
            refine ⟨hc, fun T hT => ?_⟩
            simp only [TypeDeclaration.codataTypes, hb] at hT
            nomatch hT
          | codata hb _ _ _ _ hc =>
            refine ⟨fun T hT => ?_, hc⟩
            simp only [TypeDeclaration.dataTypes, hb] at hT
            nomatch hT
        | _ => trivial⟩

-- ADE: none.
/-- Arguments of an instance are equal to themselves. -/
theorem EqInstanceArgs.refl {Γ Δ : Scope} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
    {params : Context k Δ} : HasInstanceArgs sig ctx as params → EqInstanceArgs sig ctx as as params
  | .nil hctx => .nil hctx
  | .var has ha => .var (EqInstanceArgs.refl has) (.refl ha)
  | .secondOrder has hB => .secondOrder (EqInstanceArgs.refl has) (.refl hB)

end Sic.Core
