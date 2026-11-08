module

public import Sic.Core.Substitution
public import Sic.Core.Usage

/-!
# Typing

The judgments of typing and of equality of RFC 24, with the judgments for signatures and contexts,
for the arguments of telescopes and of instances, and for the telescopes in a sort:

* `⊢ Σ`, `Σ ⊢ Γ`, `Σ; Γ ⊢ A`, `Σ; Γ ⊢ A ≡ B`, `Σ; Γ ⊢ t : A` and `Σ; Γ ⊢ t ≡ u : A`;
* `Σ; Γ ⊢ t̄ : Θ` and `Σ; Γ ⊢ t̄ ≡ ū : Θ`, the arguments of a telescope;
* `Σ; Γ ⊢ ā : Δ` and `Σ; Γ ⊢ ā ≡ b̄ : Δ`, the arguments of an instance;
* `Σ; Γ ⊢ Θ : κ`, a telescope in a sort;
* `Σ ⊢ c.{s̄; l̄; p̄} :_m A ≔ t` and `Σ ⊢ c.{s̄; l̄; p̄} :_m A`, the entries of the signature.

Typing and equality carry no grade; the definitions are checked for their usage.
An entry of the signature is checked for each instance of its sort and grade variables, once with
its level variables, so that its rules quantify over the instances.
A variable `x` is fresh in its context by construction, being a de Bruijn index, so that the
conditions `x ∉ Γ` disappear; the condition that the names of a signature are fresh remains.

The core names no type: the rules of the kinds of declarations, which give the declarations of the
signature, and the rule `(sig_𝒟)` with them, come with their RFCs.

ADE have no second-order variables, no constants, no sorts of propositions and no declarations,
and their typing has a context of definitions instead of a signature.
-/

@[expose] public section

namespace Sic.Core

/-! ## Entries of Contexts -/

/-- `x : A ∈ Γ`: the variable `x` is declared with the type `A` in the context. -/
inductive Context.VarIn {k : Nat} : {Γ : Scope} → Context k Γ → Var Γ [] → Term k Γ → Prop where
  /-- The last entry. -/
  | zero {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
      VarIn (ctx.var A) .zero (A.rename Ren.weaken)
  /-- An entry before a variable. -/
  | succVar {Γ : Scope} {ctx : Context k Γ} {x : Var Γ []} {A B : Term k Γ} (h : VarIn ctx x A) :
      VarIn (ctx.var B) x.succ (A.rename Ren.weaken)
  /-- An entry before a second-order variable. -/
  | succSecondOrder {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {x : Var Γ []}
      {A : Term k Γ} {Θ : Telescope k Γ ps} {B : Term k (Γ.extend ps.length)} (h : VarIn ctx x A) :
      VarIn (ctx.secondOrder Θ B) x.succ (A.rename Ren.weaken)

/-- `X : (Θ ⊢ A) ∈ Γ`: the second-order variable `X` is declared with the telescope `Θ` and the
type `A` in the context. -/
inductive Context.SecondOrderIn {k : Nat} : {Γ : Scope} → {ps : List Grade} → Context k Γ →
    Var Γ ps → Telescope k Γ ps → Term k (Γ.extend ps.length) → Prop where
  /-- The last entry. -/
  | zero {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {Θ : Telescope k Γ ps}
      {A : Term k (Γ.extend ps.length)} :
      SecondOrderIn (ctx.secondOrder Θ A) .zero (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a variable. -/
  | succVar {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {X : Var Γ ps}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {B : Term k Γ}
      (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.var B) X.succ (Θ.rename Ren.weaken) (A.rename (Ren.liftN _ Ren.weaken))
  /-- An entry before a second-order variable. -/
  | succSecondOrder {Γ : Scope} {ps qs : List Grade} {ctx : Context k Γ} {X : Var Γ ps}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {Θ' : Telescope k Γ qs}
      {B : Term k (Γ.extend qs.length)} (h : SecondOrderIn ctx X Θ A) :
      SecondOrderIn (ctx.secondOrder Θ' B) X.succ (Θ.rename Ren.weaken)
        (A.rename (Ren.liftN _ Ren.weaken))

/-- The type of an entry of the signature at an instance `c.{s̄; l̄; p̄}` of its variables, in the
scope `Γ`. -/
def Signature.instanceType {k k' j g : Nat} {Γ : Scope} (A : Instance j g → Term k' [])
    (ι : Instance j g) (ls : Fin k' → Level k) : Term k Γ :=
  ((A ι).substLevels ls).weakenClosed

mutual

-- ADE: `»_`, in `Definition/Typed.agda`, for contexts of definitions.
/-- `⊢ Σ`: the signature is well formed. -/
inductive WfSig : Signature → Prop where
  /-- `(sig_∅)`. -/
  | empty : WfSig []
  /-- `(sig_≔)`: a definition, whose name is fresh. -/
  | constantDefinition {sig : Signature} {d : ConstantDefinition} (h : WfDefinition sig d)
      (fresh : ∀ e ∈ sig, d.name ∉ e.names) : WfSig (.constantDefinition d :: sig)
  /-- `(sig_c)`: a constant, whose name is fresh. -/
  | constantDeclaration {sig : Signature} {c : ConstantDeclaration} (h : WfConstant sig c)
      (fresh : ∀ e ∈ sig, c.name ∉ e.names) : WfSig (.constantDeclaration c :: sig)

/--
`(def)`: `Σ ⊢ c.{s̄; l̄; p̄} :_m A ≔ t`, for each instance of the sort and grade variables, the type
`A` is a type of some sort and the body `t` a term of it, both in the empty context, and the body
uses no variable in the mode `m`.
-/
inductive WfDefinition : Signature → ConstantDefinition → Prop where
  /-- The rule, with a sort `κ ι` of the type at each instance `ι`. -/
  | intro {sig : Signature} {d : ConstantDefinition}
      (κ : Instance d.sorts d.grades → Universe d.levels)
      (hA : ∀ ι, HasType sig .empty (d.type ι) (.sort (κ ι)))
      (ht : ∀ ι, HasType sig .empty (d.body ι) (d.type ι))
      (hu : ∀ ι, Usage sig 𝟘ᶜ d.mode (d.body ι)) :
      WfDefinition sig d

/-- `(const)`: `Σ ⊢ c.{s̄; l̄; p̄} :_m A`, for each instance of the sort and grade variables, the type
`A` is a type of some sort in the empty context. -/
inductive WfConstant : Signature → ConstantDeclaration → Prop where
  /-- The rule, with a sort `κ ι` of the type at each instance `ι`. -/
  | intro {sig : Signature} {c : ConstantDeclaration}
      (κ : Instance c.sorts c.grades → Universe c.levels)
      (hA : ∀ ι, HasType sig .empty (c.type ι) (.sort (κ ι))) :
      WfConstant sig c

-- ADE: `_»⊢_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ Γ`: the context is well formed. -/
inductive WfCtx : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Prop where
  /-- `(ctx_ε)`. -/
  | empty {sig : Signature} {k : Nat} (h : WfSig sig) : WfCtx sig (.empty : Context k [])
  /-- `(ctx_x)`. -/
  | var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : WfCtx sig (ctx.var A)
  /-- `(ctx_X)`. -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade} {ctx : Context k Γ}
      {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} (h : WfType sig (ctx.append Θ) A) :
      WfCtx sig (ctx.secondOrder Θ A)

-- ADE: `_⊢_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A`: `A` is a type. -/
inductive WfType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Prop where
  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- `(U_type)`: a term of a universe is a type. -/
  | univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.type, l⟩)) : WfType sig ctx A
  /-- `(Ω_type)`: a proposition is a type. -/
  | propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.prop, l⟩)) : WfType sig ctx A

-- ADE: `_⊢_≡_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A ≡ B`: `A` and `B` are equal types. -/
inductive EqType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Prop where
  /-- `(refl_type)`. -/
  | refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : EqType sig ctx A A
  /-- `(sym_type)`. -/
  | symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      (h : EqType sig ctx A B) : EqType sig ctx B A
  /-- `(trans_type)`. -/
  | trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A₁ A₂ A₃ : Term k Γ}
      (h₁ : EqType sig ctx A₁ A₂) (h₂ : EqType sig ctx A₂ A₃) : EqType sig ctx A₁ A₃
  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- `(U_type≡)`: equal terms of a universe are equal types. -/
  | univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.type, l⟩)) : EqType sig ctx A B
  /-- `(Ω_type≡)`: equal propositions are equal types. -/
  | propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.prop, l⟩)) : EqType sig ctx A B

-- ADE: `_⊢_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t : A`: `t` is a term of type `A`. -/
inductive HasType : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Prop where
  -- ADE: `var`, in `Definition/Typed.agda`.
  /-- `(var)`: a variable has the type of its declaration. -/
  | var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {x : Var Γ []} {A : Term k Γ}
      (hctx : WfCtx sig ctx) (hx : ctx.VarIn x A) : HasType sig ctx (.var₀ x) A
  /-- `(var_X)`: an application of a second-order variable to arguments of its telescope. -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade} {ctx : Context k Γ}
      {X : Var Γ ps} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {ts : Args k Γ ps}
      (hX : ctx.SecondOrderIn X Θ A) (hts : HasArgs sig ctx ts Θ) :
      HasType sig ctx (.var X ts) (A.instantiate ts)
  -- ADE: `defn`, in `Definition/Typed.agda`, for the definitions.
  /-- `(c)`: a definition or a constant, at an instance of its variables, has its type at this
  instance. -/
  | const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {c : Name} {j k' g : Nat}
      {m : Mode} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant c j k' g m A)
      (hq : qs.length = j) (hl : ls.length = k') (hp : ps.length = g) :
      HasType sig ctx (.const c qs ls ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls.getFin hl))
  -- ADE: `Uⱼ`, in `Definition/Typed.agda`.
  /-- `(U)`: a universe is in the universe above it. -/
  | univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.type, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- `(Ω)`: a universe of propositions is in the universe above it. -/
  | prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.prop, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- `(D)`: an instance of a declared type is a type in the sort of its declaration. -/
  | inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) :
      HasType sig ctx (.inst D qs ls ps as)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
  -- ADE: `conv`, in `Definition/Typed.agda`.
  /-- `(conv)`: a term has every type equal to its own. -/
  | conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A B : Term k Γ}
      (ht : HasType sig ctx t A) (h : EqType sig ctx A B) : HasType sig ctx t B

-- ADE: `_⊢_≡_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t ≡ u : A`: `t` and `u` are equal terms of type `A`. -/
inductive EqTerm : Signature → {k : Nat} → {Γ : Scope} → Context k Γ → Term k Γ → Term k Γ →
    Term k Γ → Prop where
  /-- `(refl)`. -/
  | refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
      (h : HasType sig ctx t A) : EqTerm sig ctx t t A
  /-- `(sym)`. -/
  | symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      (h : EqTerm sig ctx t u A) : EqTerm sig ctx u t A
  /-- `(trans)`. -/
  | trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t₁ t₂ t₃ A : Term k Γ}
      (h₁ : EqTerm sig ctx t₁ t₂ A) (h₂ : EqTerm sig ctx t₂ t₃ A) : EqTerm sig ctx t₁ t₃ A
  /-- `(conv_≡)`: an equality holds at every type equal to its own. -/
  | conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A B : Term k Γ}
      (h : EqTerm sig ctx t u A) (hA : EqType sig ctx A B) : EqTerm sig ctx t u B
  /-- `(irr)`: two proofs of a proposition are equal. -/
  | irr {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      {l : Level k} (ht : HasType sig ctx t A) (hu : HasType sig ctx u A)
      (hA : HasType sig ctx A (.sort ⟨.prop, l⟩)) : EqTerm sig ctx t u A
  /-- `(var_X≡)`: equal arguments give equal applications. -/
  | secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade} {ctx : Context k Γ}
      {X : Var Γ ps} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {ts us : Args k Γ ps} (hX : ctx.SecondOrderIn X Θ A) (hts : EqArgs sig ctx ts us Θ) :
      EqTerm sig ctx (.var X ts) (.var X us) (A.instantiate ts)
  -- ADE: `δ-red`, in `Definition/Typed.agda`.
  /-- `(δ)`: a definition unfolds to its body, at an instance of its variables. -/
  | delta {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {d : ConstantDefinition}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} (hctx : WfCtx sig ctx)
      (h : .constantDefinition d ∈ sig) (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
      (hp : ps.length = d.grades) :
      EqTerm sig ctx (.const d.name qs ls ps)
        (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))
        (Signature.instanceType d.type (.ofLists qs ps hq hp) (ls.getFin hl))
  /-- `(c_≡)`: two instances of an entry at equal levels are equal. -/
  | const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {c : Name} {j k' g : Nat}
      {m : Mode} {A : Instance j g → Term k' []} {qs : List Quality} {ls₁ ls₂ : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant c j k' g m A)
      (hq : qs.length = j) (hl₁ : ls₁.length = k') (hl₂ : ls₂.length = k') (hp : ps.length = g)
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.const c qs ls₁ ps) (.const c qs ls₂ ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls₁.getFin hl₁))
  -- ADE: `U-cong`, in `Definition/Typed.agda`.
  /-- `(U_≡)`: universes at equal levels are equal. -/
  | univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.type, l₁⟩) (.sort ⟨.type, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- `(Ω_≡)`: universes of propositions at equal levels are equal. -/
  | prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.prop, l₁⟩) (.sort ⟨.prop, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- `(D_≡)`: instances with equal arguments at equal levels are equal. -/
  | inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {qs : List Quality} {ls₁ ls₂ : List (Level k)} {ps : List Grade}
      {as bs : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (has : EqInstanceArgs sig ctx as bs
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.inst D qs ls₁ ps as) (.inst D qs ls₂ ps bs)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))

/-- `Σ; Γ ⊢ t̄ : Θ`: the arguments are typed by the telescope, each argument instantiating the types
after it, whose grades typing ignores. -/
inductive HasArgs : Signature → {k : Nat} → {Γ : Scope} → {ps : List Grade} → Context k Γ →
    Args k Γ ps → Telescope k Γ ps → Prop where
  /-- `(tel_ε)`. -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasArgs sig ctx .nil .nil
  /-- `(tel_,)`. -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {q p : Grade}
      {t A : Term k Γ} {ts : Args k Γ ps} {Θ : Telescope k ([] :: Γ) ps}
      (ht : HasType sig ctx t A) (hts : HasArgs sig ctx ts (Θ.subst₀ (Subst₀.single t))) :
      HasArgs sig ctx (.cons t ts) (.cons q p A Θ)

/-- `Σ; Γ ⊢ t̄ ≡ ū : Θ`: the arguments are equal, typed by the telescope. -/
inductive EqArgs : Signature → {k : Nat} → {Γ : Scope} → {ps : List Grade} → Context k Γ →
    Args k Γ ps → Args k Γ ps → Telescope k Γ ps → Prop where
  /-- `(tel_≡ε)`. -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqArgs sig ctx .nil .nil .nil
  /-- `(tel_≡,)`. -/
  | cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {q p : Grade}
      {t u A : Term k Γ} {ts us : Args k Γ ps} {Θ : Telescope k ([] :: Γ) ps}
      (ht : EqTerm sig ctx t u A) (hts : EqArgs sig ctx ts us (Θ.subst₀ (Subst₀.single t))) :
      EqArgs sig ctx (.cons t ts) (.cons u us) (.cons q p A Θ)

/-- `Σ; Γ ⊢ ā : Δ`: the arguments of an instance are typed by its parameters, each argument
instantiating the types after it. -/
inductive HasInstanceArgs : Signature → {k : Nat} → {Γ Δ : Scope} → Context k Γ →
    InstanceArgs k Γ Δ → Context k Δ → Prop where
  /-- `(arg_ε)`. -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasInstanceArgs sig ctx .nil .empty
  /-- `(arg_x)`. -/
  | var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
      {params : Context k Δ} {a : Term k Γ} {A : Term k Δ}
      (has : HasInstanceArgs sig ctx as params) (ha : HasType sig ctx a (A.subst as.toSubst)) :
      HasInstanceArgs sig ctx (.snoc (ps := []) as a) (params.var A)
  /-- `(arg_X)`. -/
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Grade} {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
      (has : HasInstanceArgs sig ctx as params)
      (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B
        (A.subst (Subst.liftN _ as.toSubst))) :
      HasInstanceArgs sig ctx (.snoc as B) (params.secondOrder Θ A)

/-- `Σ; Γ ⊢ ā ≡ b̄ : Δ`: the arguments of two instances are equal, typed by the parameters. -/
inductive EqInstanceArgs : Signature → {k : Nat} → {Γ Δ : Scope} → Context k Γ →
    InstanceArgs k Γ Δ → InstanceArgs k Γ Δ → Context k Δ → Prop where
  /-- `(arg_≡ε)`. -/
  | nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqInstanceArgs sig ctx .nil .nil .empty
  /-- `(arg_≡x)`. -/
  | var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as bs : InstanceArgs k Γ Δ} {params : Context k Δ} {a b : Term k Γ} {A : Term k Δ}
      (has : EqInstanceArgs sig ctx as bs params) (ha : EqTerm sig ctx a b (A.subst as.toSubst)) :
      EqInstanceArgs sig ctx (.snoc (ps := []) as a) (.snoc (ps := []) bs b) (params.var A)
  /-- `(arg_≡X)`. -/
  | secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Grade} {ctx : Context k Γ}
      {as bs : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (has : EqInstanceArgs sig ctx as bs params)
      (hB : EqTerm sig (ctx.append (Θ.subst as.toSubst)) B₁ B₂
        (A.subst (Subst.liftN _ as.toSubst))) :
      EqInstanceArgs sig ctx (.snoc as B₁) (.snoc bs B₂) (params.secondOrder Θ A)

end

/--
`Σ; Γ ⊢ Θ : κ`: the telescope lives in the sort `κ`, each of its types living in a sort that `κ`
bounds, and an entry whose type is a proposition has a grade without use at run time.
-/
inductive WfTelescope (sig : Signature) {k : Nat} :
    {Γ : Scope} → {ps : List Grade} → Context k Γ → Telescope k Γ ps → Universe k → Prop where
  /-- `(tel_κε)`. -/
  | nil {Γ : Scope} {ctx : Context k Γ} {κ : Universe k} (hctx : WfCtx sig ctx) :
      WfTelescope sig ctx .nil κ
  /-- `(tel_κ,)`. -/
  | cons {Γ : Scope} {ps : List Grade} {ctx : Context k Γ} {q p : Grade} {A : Term k Γ}
      {Θ : Telescope k ([] :: Γ) ps} {κ₁ κ₂ : Universe k} (hA : HasType sig ctx A (.sort κ₁))
      (hκ : κ₁ ≼ κ₂) (hΘ : WfTelescope sig (ctx.var A) Θ κ₂)
      (hp : κ₁.quality = .prop → p.mode ≠ .oneOne) :
      WfTelescope sig ctx (.cons q p A Θ) κ₂

/-! ## Presuppositions

Every judgment implies that its signature is well formed, the first of the presuppositions of the
admissible properties of RFC 24: each rule has a premise that is a judgment in the same signature,
down to the rule `(ctx_ε)`, whose premise is `⊢ Σ`.
The proofs are by structural recursion on the derivations, through such a premise.
-/

-- ADE: none.
/-- An instance of `j` sort variables and `g` grade variables, which exists whatever `j` and `g`. -/
def Instance.default (j g : Nat) : Instance j g := ⟨fun _ => .type, fun _ => Grade.zero⟩

mutual

-- ADE: `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- A well-formed context is in a well-formed signature. -/
theorem WfCtx.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} :
    WfCtx sig ctx → WfSig sig
  | .empty h => h
  | .var h => h.wfSig
  | .secondOrder h => h.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- A type is in a well-formed signature. -/
theorem WfType.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
    WfType sig ctx A → WfSig sig
  | .univType h => h.wfSig
  | .propType h => h.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- An equality of types is in a well-formed signature. -/
theorem EqType.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {A B : Term k Γ} : EqType sig ctx A B → WfSig sig
  | .refl h => h.wfSig
  | .symm h => h.wfSig
  | .trans h _ => h.wfSig
  | .univType h => h.wfSig
  | .propType h => h.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- A typing is in a well-formed signature. -/
theorem HasType.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t A : Term k Γ} : HasType sig ctx t A → WfSig sig
  | .var hctx _ => hctx.wfSig
  | .secondOrder _ hts => hts.wfSig
  | .const hctx _ _ _ _ => hctx.wfSig
  | .univ hctx => hctx.wfSig
  | .prop hctx => hctx.wfSig
  | .inst _ _ _ _ has => has.wfSig
  | .conv ht _ => ht.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- An equality of terms is in a well-formed signature. -/
theorem EqTerm.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    {t u A : Term k Γ} : EqTerm sig ctx t u A → WfSig sig
  | .refl h => h.wfSig
  | .symm h => h.wfSig
  | .trans h _ => h.wfSig
  | .conv h _ => h.wfSig
  | .irr ht _ _ => ht.wfSig
  | .secondOrder _ hts => hts.wfSig
  | .delta hctx _ _ _ _ => hctx.wfSig
  | .const hctx .. => hctx.wfSig
  | .univ hctx _ => hctx.wfSig
  | .prop hctx _ => hctx.wfSig
  | .inst _ _ _ _ _ has _ => has.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Arguments of a telescope are in a well-formed signature. -/
theorem HasArgs.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade}
    {ctx : Context k Γ} {ts : Args k Γ ps} {Θ : Telescope k Γ ps} :
    HasArgs sig ctx ts Θ → WfSig sig
  | .nil hctx => hctx.wfSig
  | .cons ht _ => ht.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Equal arguments of a telescope are in a well-formed signature. -/
theorem EqArgs.wfSig {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Grade}
    {ctx : Context k Γ} {ts us : Args k Γ ps} {Θ : Telescope k Γ ps} :
    EqArgs sig ctx ts us Θ → WfSig sig
  | .nil hctx => hctx.wfSig
  | .cons ht _ => ht.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Arguments of an instance are in a well-formed signature. -/
theorem HasInstanceArgs.wfSig {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ Δ} {params : Context k Δ} :
    HasInstanceArgs sig ctx as params → WfSig sig
  | .nil hctx => hctx.wfSig
  | .var has _ => has.wfSig
  | .secondOrder has _ => has.wfSig

-- ADE: `wf`, then `defn-wf`, in `Definition/Typed/Properties/Well-formed.agda`.
/-- Equal arguments of instances are in a well-formed signature. -/
theorem EqInstanceArgs.wfSig {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
    {as bs : InstanceArgs k Γ Δ} {params : Context k Δ} :
    EqInstanceArgs sig ctx as bs params → WfSig sig
  | .nil hctx => hctx.wfSig
  | .var has _ => has.wfSig
  | .secondOrder has _ => has.wfSig

end

-- ADE: none.
/-- A well-formed definition is in a well-formed signature. -/
theorem WfDefinition.wfSig {sig : Signature} {d : ConstantDefinition} :
    WfDefinition sig d → WfSig sig
  | .intro _ hA _ _ => (hA (.default _ _)).wfSig

-- ADE: none.
/-- A well-formed constant is in a well-formed signature. -/
theorem WfConstant.wfSig {sig : Signature} {c : ConstantDeclaration} : WfConstant sig c → WfSig sig
  | .intro _ hA => (hA (.default _ _)).wfSig

-- ADE: none.
/-- The signature before the last entry of a well-formed signature is well formed. -/
theorem WfSig.tail {e : Entry} {sig : Signature} : WfSig (e :: sig) → WfSig sig
  | .constantDefinition h _ => h.wfSig
  | .constantDeclaration h _ => h.wfSig

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
/-- The names of a well-formed signature are distinct. -/
theorem WfSig.distinct : {sig : Signature} → WfSig sig → sig.Distinct
  | [], _ => trivial
  | _ :: _, h => ⟨h.tail.distinct, h.fresh⟩

end Sic.Core
