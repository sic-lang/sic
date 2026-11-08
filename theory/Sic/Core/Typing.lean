module

public import Sic.Core.Substitution
public import Sic.Core.Usage

/-!
# Typing

The judgments of typing and of equality of annex 11 of RFC 36, with the judgments for signatures
and contexts, for the arguments of telescopes and of instances, and for the telescopes in a sort:

* `⊢ Σ`, `Σ ⊢ Γ`, `Σ; Γ ⊢ A`, `Σ; Γ ⊢ A ≡ B`, `Σ; Γ ⊢ t : A` and `Σ; Γ ⊢ t ≡ u : A`;
* `Σ; Γ ⊢ t̄ : Θ` and `Σ; Γ ⊢ t̄ ≡ ū : Θ`, the arguments of a telescope;
* `Σ; Γ ⊢ ā : Δ` and `Σ; Γ ⊢ ā ≡ b̄ : Δ`, the arguments of an instance;
* `Σ; Γ ⊢ Θ : κ`, a telescope in a sort;
* `Σ ⊢ f.{s̄; l̄; p̄} :_m A ≔ t` and `Σ ⊢ f.{s̄; l̄; p̄} :_m A`, the entries of the signature.

Typing and equality carry no grade; the definitions are checked for their usage.
An entry of the signature is checked for each instance of its sort and grade variables, once with
its level variables, so that its rules quantify over the instances.
A variable `x` is fresh in its context by construction, being a de Bruijn index, so that the
conditions `x ∉ Γ` disappear; the condition that the names of a signature are fresh remains.

The core names no type: the type declarations enter a signature by the rules of their kinds, which
come with their annexes.

ADE have no second-order variables, no constants, no sorts of propositions and no declarations,
and their typing has a context of definitions instead of a signature.
-/

@[expose] public section

namespace Sic.Core

/-! ## Entries of Contexts -/

/-- `x : A ∈ Γ`: the variable `x` is declared with the type `A` in the context, by the cases of the
last entry; the empty context, which has no variable, has no constructor, and the type is weakened
to the scope of the context.
RFC: `\in_\Gamma` -/
inductive Context.VarIn {k : Nat} : {Γ : Scope} → Context k Γ → Var Γ .var → Term k Γ → Prop where
  /-- The last entry. -/
  | zero {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      VarIn (ctx.var A) .zero (A.rename Ren.weaken)
  /-- An entry before a variable. -/
  | succVar {Γ : Scope} {ctx : Context k Γ} {x : Var Γ .var} {A B : Term k Γ} (h : VarIn ctx x A) :
      VarIn (ctx.var B) x.succ (A.rename Ren.weaken)
  /-- An entry before a second-order variable. -/
  | succSecondOrder {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade} {ctx : Context k Γ}
      {x : Var Γ .var} {A : Term k Γ} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)}
      (h : VarIn ctx x A) : VarIn (ctx.secondOrder Θ B c₀) x.succ (A.rename Ren.weaken)

/-- `X : (Θ ⊢ A) ∈ Γ`: the second-order variable `X` is declared with the telescope `Θ` and the
type `A` in the context, by the cases of the last entry; the empty context, which has no
second-order variable, has no constructor, and the telescope and the type are weakened to the scope
of the context.
RFC: `\in_\Gamma` -/
inductive Context.SecondOrderIn {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    {c₀ : Option Grade} → Context k Γ → Var Γ (.secondOrder ps c₀) → Telescope k Γ ps →
    Term k (Γ.extend ps.length) → Prop where
  /-- The last entry. -/
  | zero {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} :
      SecondOrderIn (ctx.secondOrder Θ A c₀) .zero (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a variable. -/
  | succVar {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade} {ctx : Context k Γ}
      {X : Var Γ (.secondOrder ps c₀)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {B : Term k Γ} (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.var B) X.succ (Θ.rename Ren.weaken) (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a second-order variable. -/
  | succSecondOrder {Γ : Scope} {ps qs : List Parameter} {c₀ c₀' : Option Grade}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps c₀)} {Θ : Telescope k Γ ps}
      {A : Term k (Γ.extend ps.length)} {Θ' : Telescope k Γ qs} {B : Term k (Γ.extend qs.length)}
      (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.secondOrder Θ' B c₀') X.succ (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))

/-- `A[s̄' / s̄, l̄' / l̄, p̄' / p̄]`: the type or the body `A` of an entry of the signature at the
instance `ι` of its sort and grade variables, then at the levels `l̄'`, weakened from the empty scope
to the scope `Γ`.
RFC: `\mathsf{inst}_e` -/
def Signature.instanceType {k k' j g : Nat} {Γ : Scope} (A : Instance j g → Term k' [])
    (ι : Instance j g) (ls : Fin k' → Level k) : Term k Γ :=
  ((A ι).substLevels ls).weakenClosed

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

/--
`Σ ⊢ f.{s̄; l̄; p̄} :_m A ≔ t`: for each instance of the sort and grade variables, the type `A` is a
type of some sort and the body `t` a term of it, both in the empty context, and the body uses no
variable in the mode `m`.
-/
inductive WfConstantDefinition : Signature → ConstantDefinition → Prop where
  /-- The rule, with a sort `κ ι` of the type at each instance `ι`.
  RFC: `\mathsf{def}` -/
  | intro {sig : Signature} {d : ConstantDefinition}
      (κ : Instance d.sorts d.grades → Universe d.levels)
      (hA : ∀ ι, HasType sig .empty (d.type ι) (.sort (κ ι)))
      (ht : ∀ ι, HasType sig .empty (d.body ι) (d.type ι))
      (hu : ∀ ι, Usage sig 𝟘ᶜ d.mode (d.body ι)) :
      WfConstantDefinition sig d

/-- `Σ ⊢ f.{s̄; l̄; p̄} :_m A`: for each instance of the sort and grade variables, the type `A` is a
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
  the ownership of whose result has a term: the constant `c₀` or the coefficient of a parameter.
  RFC: `\mathsf{ctx}_X` -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      (h : WfType sig (ctx.append Θ) A) (hc : c₀.isSome ∨ ∃ p ∈ ps, p.coefficient.isSome) :
      WfCtx sig (ctx.secondOrder Θ A c₀)

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
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps c₀)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {ts : Args k Γ ps}
      (hX : ctx.SecondOrderIn X Θ A) (hts : HasArgs sig ctx ts Θ) :
      HasType sig ctx (.var X ts) (A.instantiate ts)
  -- ADE: `defn`, in `Definition/Typed.agda`, for the definitions.
  /-- A constant, defined or declared, at an instance of its variables, has its type at this
  instance.
  RFC: `f` -/
  | const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {f : Name} {j k' g : Nat}
      {m : Mode} {c₀ : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m c₀ A)
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
  /-- An instance of a declared type, whose arguments are arguments of its parameters, is in the
  sort of its type declaration.
  RFC: `D` -/
  | inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) :
      HasType sig ctx (.inst D qs ls ps as)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
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
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {c₀ : Option Grade}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps c₀)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
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
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m c₀ A)
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
      {D : Name} {qs : List Quality} {ls₁ ls₂ : List (Level k)} {ps : List Grade}
      {as₁ as₂ : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))

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
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {c₀ : Option Grade}
      {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
      (has : HasInstanceArgs sig ctx as params)
      (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B
        (A.subst (Subst.liftN _ as.toSubst))) :
      HasInstanceArgs sig ctx (.snoc (e := .secondOrder ps c₀) as B)
        (params.secondOrder Θ A c₀)

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
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {c₀ : Option Grade}
      {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (has : EqInstanceArgs sig ctx as₁ as₂ params)
      (hB : EqTerm sig (ctx.append (Θ.subst as₁.toSubst)) B₁ B₂
        (A.subst (Subst.liftN _ as₁.toSubst))) :
      EqInstanceArgs sig ctx (.snoc (e := .secondOrder ps c₀) as₁ B₁)
        (.snoc (e := .secondOrder ps c₀) as₂ B₂) (params.secondOrder Θ A c₀)

end

/--
`Σ; Γ ⊢ Θ : κ`: the telescope lives in the sort `κ`, each of its types living in a sort that `κ`
bounds, and an entry whose type is a proposition has a grade without use at run time.
-/
inductive WfTelescope (sig : Signature) {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → Context k Γ → Telescope k Γ ps → Universe k → Prop where
  /-- The empty telescope lives in every sort.
  RFC: `\mathsf{tel}_{\kappa\varepsilon}` -/
  | nil {Γ : Scope} {ctx : Context k Γ} {κ : Universe k} (hctx : WfCtx sig ctx) :
      WfTelescope sig ctx .nil κ
  /-- The first entry, whose type lives in a sort that `κ₂` bounds, with a grade without use at
  run time if it is a proposition, and the others.
  RFC: `\mathsf{tel}_{\kappa,}` -/
  | cons {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade} {p : Parameter} {A : Term k Γ}
      {Θ : Telescope k (.var :: Γ) ps} {κ₁ κ₂ : Universe k} (hA : HasType sig ctx A (.sort κ₁))
      (hκ : κ₁ ≼ κ₂) (hΘ : WfTelescope sig (ctx.var A) Θ κ₂)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfTelescope sig ctx (.cons q p A Θ) κ₂


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
  /-- The signature that a well-formed signature extends is well formed.
  RFC: `\mathsf{presup}_\Sigma.e` -/
  tail : ∀ {e : Entry} {sig : Signature}, WfSig (e :: sig) → WfSig sig

-- ADE: `wf` and `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`, for the contexts and
-- the judgments in a context of definitions.
/-- The judgments hold in well-formed signatures.
RFC: `\mathsf{presup}_\Sigma.\mathsf{def}`, `\mathsf{presup}_\Sigma.\mathsf{decl}`
RFC: `\mathsf{presup}_\Sigma.\Gamma`, `\mathsf{presup}_\Sigma.A`
RFC: `\mathsf{presup}_\Sigma.A_\equiv`, `\mathsf{presup}_\Sigma.t`
RFC: `\mathsf{presup}_\Sigma.t_\equiv`, `\mathsf{presup}_\Sigma.\bar t`
RFC: `\mathsf{presup}_\Sigma.\bar t_\equiv`, `\mathsf{presup}_\Sigma.\bar a`
RFC: `\mathsf{presup}_\Sigma.\bar a_\equiv`, `\mathsf{presup}_\Sigma.e` -/
theorem presuppositions : Presuppositions :=
  ⟨wfConstantDefinition, wfConstantDeclaration, wfCtx, wfType, eqType, hasType, eqTerm, hasArgs,
    eqArgs, hasInstanceArgs, eqInstanceArgs, tail⟩
where
  wfConstantDefinition {sig : Signature} {d : ConstantDefinition} :
      WfConstantDefinition sig d → WfSig sig
    | .intro _ hA _ _ => hasType (hA (.default _ _))
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
    | .inst _ _ _ _ has => hasInstanceArgs has
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
    | .inst _ _ _ _ _ has _ => eqInstanceArgs has
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
  tail {e : Entry} {sig : Signature} : WfSig (e :: sig) → WfSig sig
    | .constantDefinition h _ => wfConstantDefinition h
    | .constantDeclaration h _ => wfConstantDeclaration h

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

-- ADE: none.
/-- The names of a well-formed signature are distinct.
RFC: `\mathsf{distinct}_\Sigma` -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨(Presuppositions.tail presuppositions h).distinct, h.fresh⟩

end Sic.Core
