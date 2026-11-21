module

public import Sic.Core.Results
public import Sic.Core.Prelude
public import Sic.Core.Substitution.Closed
public import Sic.Core.Substitution.Levels

/-!
# Typing

The judgments of typing and of equality of annex 15 of RFC 36, with the judgments for signatures
and contexts, for the arguments of telescopes and of instances, and for the telescopes in a sort:

* `⊢ Σ`, `Σ ⊢ Γ`, `Σ; Γ ⊢ A`, `Σ; Γ ⊢ A ≡ B`, `Σ; Γ ⊢ t : A` and `Σ; Γ ⊢ t ≡ u : A`;
* `Σ; Γ ⊢ t̄ : Θ` and `Σ; Γ ⊢ t̄ ≡ ū : Θ`, the arguments of a telescope;
* `Σ; Γ ⊢ ā : Δ` and `Σ; Γ ⊢ ā ≡ b̄ : Δ`, the arguments of an instance;
* `Σ; Γ ⊢ Θ : κ` and `Σ; Γ ⊢ Θ₁ ≡ Θ₂ : κ`, telescopes in a sort, and `Σ; Γ ⊢ d̄ : κ`, destructors
  in a sort;
* `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`, `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p`,
  `Σ ⊢ data.{s̄; l̄; p̄ | C} Δ : κ where …` and `Σ ⊢ codata.{s̄; l̄; p̄ | C} Δ : κ where …`, the
  entries of the signature.

Typing and equality carry no grade, and no rule has a premise of the usage or of the ownership:
the usage and the ownership of the entries of the signature are their own judgments, `⊢ Σ ▶` and
`⊢ Σ ◀`, which `Sic/Core/Usage.lean` and `Sic/Core/Ownership.lean` define.
An entry of the signature is checked for each instance of its sort and grade variables, once with
its level variables, so that its rules quantify over the instances; a type declaration only at the
instances that its constraint admits.
A variable `x` is fresh in its context by construction, being a de Bruijn index, so that the
conditions `x ∉ Γ` disappear; the condition that the names of a signature are fresh remains.

The judgments are one inductive `Derivable`, indexed by the form of the judgment, `Judgment`, rather
than a family of mutual inductives, one for each judgment: `induction` works on one inductive, not on
a family of mutual ones, and a structural recursion on mutual inductives of propositions costs, to
compile, much more than an induction, more with each rule.
Each judgment is an abbreviation of `Derivable` at its form, such as `HasType sig ctx t A` for
`Derivable (.hasType sig ctx t A)`, and its rules are the constructors `HasType.var`, … of
`Derivable`, which the namespace of the judgment exports.
A property of the derivations of several judgments is one theorem on `Derivable`, by induction,
whose statement is a property of each form, defined by cases on the form.

ADE have no second-order variables, no constants, no sorts of propositions and no declarations,
and their typing has a context of definitions instead of a signature.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Judgments -/

/-- The forms of the judgments, one for each judgment, with what it is about. -/
inductive Judgment : Type where
  /-- The form of `⊢ Σ`. -/
  | wfSig (sig : Signature)
  /-- The form of `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`. -/
  | wfConstantDefinition (sig : Signature) (d : ConstantDefinition)
  /-- The form of `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p`. -/
  | wfConstantDeclaration (sig : Signature) (c : ConstantDeclaration)
  /-- The form of `Σ ⊢ Γ`. -/
  | wfCtx (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
  /-- The form of `Σ; Γ ⊢ A`. -/
  | wfType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ)
  /-- The form of `Σ; Γ ⊢ A ≡ B`. -/
  | eqType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A B : Term k Γ)
  /-- The form of `Σ; Γ ⊢ t : A`. -/
  | hasType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (t A : Term k Γ)
  /-- The form of `Σ; Γ ⊢ t ≡ u : A`. -/
  | eqTerm (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (t u A : Term k Γ)
  /-- The form of `Σ; Γ ⊢ t̄ : Θ`. -/
  | hasArgs (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
      (ts : Args k Γ ps) (Θ : Telescope k Γ ps)
  /-- The form of `Σ; Γ ⊢ t̄ ≡ ū : Θ`. -/
  | eqArgs (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
      (ts us : Args k Γ ps) (Θ : Telescope k Γ ps)
  /-- The form of `Σ; Γ ⊢ ā : Δ`. -/
  | hasInstanceArgs (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ)
      (as : InstanceArgs k Γ Δ) (params : Context k Δ)
  /-- The form of `Σ; Γ ⊢ ā₁ ≡ ā₂ : Δ`. -/
  | eqInstanceArgs (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ)
      (as₁ as₂ : InstanceArgs k Γ Δ) (params : Context k Δ)
  /-- The form of `Σ; Γ ⊢ Θ : κ`. -/
  | wfTelescope (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
      (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κ : Universe k)
  /-- The form of `Σ; Γ ⊢ Θ : κ̄ ≤ l`. -/
  | wfTelescopeSorts (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
      (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κs : List (Universe k)) (l : Level k)
  /-- The form of `Σ; Γ ⊢ Θ₁ ≡ Θ₂ : κ`. -/
  | eqTelescope (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
      (ctx : Context k Γ) (Θ₁ Θ₂ : Telescope k Γ ps) (κ : Universe k)
  /-- The form of `Σ; Γ ⊢_𝒟 Θ : κ`. -/
  | wfFields (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
      {Γ : Scope} (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
      {ps : List Parameter} (Θ : Telescope decl.levels Γ ps) (κ : Universe decl.levels)
  /-- The form of `Σ; Γ ⊢_{𝒟; Π} d̄ : κ`. -/
  | wfDestructors (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
      {Γ : Scope} {ns : List Name} (ν : Nesting Nat Γ)
      (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
      (ds : Destructors decl.levels Γ ns) (κ : Universe decl.levels)
  /-- The form of `Σ ⊢ 𝒟`. -/
  | wfTypeDeclaration (sig : Signature) (decl : TypeDeclaration)

section

-- The rules write their premises and their conclusions as the judgments that the abbreviations
-- below name, which only exist once `Derivable` does: these notations stand for them in the rules,
-- without hygiene, so that `Derivable` in them is the inductive that the rules define, which does
-- not exist yet where the notations are declared.
set_option hygiene false
local notation "WfSig " sig:max =>
    Derivable (Judgment.wfSig sig)
local notation "WfConstantDefinition " sig:max d:max =>
    Derivable (Judgment.wfConstantDefinition sig d)
local notation "WfConstantDeclaration " sig:max c:max =>
    Derivable (Judgment.wfConstantDeclaration sig c)
local notation "WfCtx " sig:max ctx:max =>
    Derivable (Judgment.wfCtx sig ctx)
local notation "WfType " sig:max ctx:max A:max =>
    Derivable (Judgment.wfType sig ctx A)
local notation "EqType " sig:max ctx:max A:max B:max =>
    Derivable (Judgment.eqType sig ctx A B)
local notation "HasType " sig:max ctx:max t:max A:max =>
    Derivable (Judgment.hasType sig ctx t A)
local notation "EqTerm " sig:max ctx:max t:max u:max A:max =>
    Derivable (Judgment.eqTerm sig ctx t u A)
local notation "HasArgs " sig:max ctx:max ts:max Θ:max =>
    Derivable (Judgment.hasArgs sig ctx ts Θ)
local notation "EqArgs " sig:max ctx:max ts:max us:max Θ:max =>
    Derivable (Judgment.eqArgs sig ctx ts us Θ)
local notation "HasInstanceArgs " sig:max ctx:max as:max params:max =>
    Derivable (Judgment.hasInstanceArgs sig ctx as params)
local notation "EqInstanceArgs " sig:max ctx:max as₁:max as₂:max params:max =>
    Derivable (Judgment.eqInstanceArgs sig ctx as₁ as₂ params)
local notation "WfTelescope " sig:max ctx:max Θ:max κ:max =>
    Derivable (Judgment.wfTelescope sig ctx Θ κ)
local notation "WfTelescopeSorts " sig:max ctx:max Θ:max κs:max l:max =>
    Derivable (Judgment.wfTelescopeSorts sig ctx Θ κs l)
local notation "EqTelescope " sig:max ctx:max Θ₁:max Θ₂:max κ:max =>
    Derivable (Judgment.eqTelescope sig ctx Θ₁ Θ₂ κ)
local notation "WfFields " sig:max decl:max ι:max as:max ctx:max Θ:max κ:max =>
    Derivable (Judgment.wfFields sig decl ι as ctx Θ κ)
local notation "WfDestructors " sig:max decl:max ι:max ν:max as:max ctx:max ds:max κ:max =>
    Derivable (Judgment.wfDestructors sig decl ι ν as ctx ds κ)
local notation "WfTypeDeclaration " sig:max decl:max =>
    Derivable (Judgment.wfTypeDeclaration sig decl)

/-- The derivations of the judgments: one inductive, indexed by the form of the judgment, so that
the proofs on the derivations of all the judgments are one `induction`, which a family of mutual
inductives does not allow; the rule `R` of a judgment `J` is the constructor `J.R`. -/
inductive Derivable : Judgment → Prop where
  /-- The empty signature.
  RFC: `\mathsf{sig}_\varnothing` -/
  | WfSig.empty : WfSig []
  /-- A constant definition, whose name is fresh.
  RFC: `\mathsf{sig}_{\mathsf{def}}` -/
  | WfSig.constantDefinition {sig : Signature} {d : ConstantDefinition}
      (h : WfConstantDefinition sig d)
      (fresh : ∀ e ∈ sig, d.name ∉ e.names) : WfSig (.constantDefinition d :: sig)
  /-- A constant declaration, whose name is fresh.
  RFC: `\mathsf{sig}_{\mathsf{decl}}` -/
  | WfSig.constantDeclaration {sig : Signature} {c : ConstantDeclaration}
      (h : WfConstantDeclaration sig c)
      (fresh : ∀ e ∈ sig, c.name ∉ e.names) : WfSig (.constantDeclaration c :: sig)
  /-- A type declaration, whose names of types are distinct, and none of them the name of a
  lifting.
  RFC: `\mathsf{sig}_{\mathsf{data}}`
  RFC: `\mathsf{sig}_{\mathsf{codata}}` -/
  | WfSig.typeDeclaration {sig : Signature} {decl : TypeDeclaration}
      (h : WfTypeDeclaration sig decl) (hn : decl.names.Nodup)
      (hL : ∀ F S, Lifting.name F S ∉ decl.names) :
      WfSig (.typeDeclaration decl :: sig)
  /-- The lifting of a codata type of a block of the signature, with the destructors of this type
  lifted.
  RFC: `\mathsf{sig}_{\mathsf{lift}}` -/
  | WfSig.lifting {sig : Signature} {decl : TypeDeclaration} {F : Name} {S : List Nat} {ns : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
      (h : WfTypeDeclaration sig (decl.lifting F S ns body)) (hd : .typeDeclaration decl ∈ sig)
      (hl : decl.Lifts sig F S body) :
      WfSig (.typeDeclaration (decl.lifting F S ns body) :: sig)

  /-- The rule, with a sort `κ ι` of the type at each instance `ι`.
  RFC: `\mathsf{def}` -/
  | WfConstantDefinition.intro {sig : Signature} {d : ConstantDefinition}
      (κ : Instance d.sorts d.grades → Universe d.levels)
      (hA : ∀ ι, HasType sig .empty (d.type ι) (.sort (κ ι)))
      (ht : ∀ ι, HasType sig .empty (d.body ι) (d.type ι)) :
      WfConstantDefinition sig d

  /-- The rule, with a sort `κ ι` of the type at each instance `ι`.
  RFC: `\mathsf{decl}` -/
  | WfConstantDeclaration.intro {sig : Signature} {c : ConstantDeclaration}
      (κ : Instance c.sorts c.grades → Universe c.levels)
      (hA : ∀ ι, HasType sig .empty (c.type ι) (.sort (κ ι))) :
      WfConstantDeclaration sig c

  /-- The empty context, in a well-formed signature.
  RFC: `\mathsf{ctx}_\varepsilon` -/
  | WfCtx.empty {sig : Signature} {k : Nat} (h : WfSig sig) : WfCtx sig (.empty : Context k [])
  /-- A variable, whose type is a type in the context.
  RFC: `\mathsf{ctx}_x` -/
  | WfCtx.var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : WfCtx sig (ctx.var A)
  /-- A second-order variable, whose type is a type in the context extended by its telescope.
  RFC: `\mathsf{ctx}_X` -/
  | WfCtx.secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {ctx : Context k Γ} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      (h : WfType sig (ctx.append Θ) A) : WfCtx sig (ctx.secondOrder Θ A ψ)

  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- A term of a universe is a type.
  RFC: `U_{\mathsf{type}}` -/
  | WfType.univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.type, l⟩)) : WfType sig ctx A
  /-- A proposition is a type.
  RFC: `\Omega_{\mathsf{type}}` -/
  | WfType.propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      {l : Level k} (h : HasType sig ctx A (.sort ⟨.prop, l⟩)) : WfType sig ctx A

  /-- The equality of types is reflexive.
  RFC: `\mathsf{refl}_{\mathsf{type}}` -/
  | EqType.refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
      (h : WfType sig ctx A) : EqType sig ctx A A
  /-- The equality of types is symmetric.
  RFC: `\mathsf{sym}_{\mathsf{type}}` -/
  | EqType.symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      (h : EqType sig ctx A B) : EqType sig ctx B A
  /-- The equality of types is transitive.
  RFC: `\mathsf{trans}_{\mathsf{type}}` -/
  | EqType.trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A₁ A₂ A₃ : Term k Γ}
      (h₁ : EqType sig ctx A₁ A₂) (h₂ : EqType sig ctx A₂ A₃) : EqType sig ctx A₁ A₃
  -- ADE: `univ`, in `Definition/Typed.agda`.
  /-- Equal terms of a universe are equal types.
  RFC: `U_{\mathsf{type}\equiv}` -/
  | EqType.univType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.type, l⟩)) : EqType sig ctx A B
  /-- Equal propositions are equal types.
  RFC: `\Omega_{\mathsf{type}\equiv}` -/
  | EqType.propType {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A B : Term k Γ}
      {l : Level k} (h : EqTerm sig ctx A B (.sort ⟨.prop, l⟩)) : EqType sig ctx A B

  -- ADE: `var`, in `Definition/Typed.agda`.
  /-- A variable has the type of its declaration.
  RFC: `\mathsf{var}` -/
  | HasType.var {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {x : Var Γ .var} {A : Term k Γ}
      (hctx : WfCtx sig ctx) (hx : ctx.VarIn x A) : HasType sig ctx (.var₀ x) A
  /-- An application of a second-order variable to arguments of its telescope has its type, in
  which the arguments are substituted for the variables of the telescope.
  RFC: `\mathsf{var}_X` -/
  | HasType.secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)} {ts : Args k Γ ps}
      (hX : ctx.SecondOrderIn X Θ A) (hts : HasArgs sig ctx ts Θ) :
      HasType sig ctx (.var X ts) (A.instantiate ts)
  -- ADE: `defn`, in `Definition/Typed.agda`, for the definitions.
  /-- A constant, defined or declared, at an instance of its variables, has its type at this
  instance.
  RFC: `f` -/
  | HasType.const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {f : Name} {j k' g : Nat}
      {m : Mode} {p : Grade} {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m p A)
      (hq : qs.length = j) (hl : ls.length = k') (hp : ps.length = g) :
      HasType sig ctx (.const f qs ls ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls.getFin hl))
  -- ADE: `Uⱼ`, in `Definition/Typed.agda`.
  /-- A universe is in the universe above its level.
  RFC: `U` -/
  | HasType.univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.type, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- A universe of propositions is in the universe above its level.
  RFC: `\Omega` -/
  | HasType.prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : HasType sig ctx (.sort ⟨.prop, l⟩) (.sort ⟨.type, .succ l⟩)
  /-- An instance of a declared type that its constraint admits, whose arguments are arguments of its
  parameters, is in the sort of its type declaration.
  RFC: `D` -/
  | HasType.inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} (h : sig.HasDeclaredType D decl ζ)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) :
      HasType sig ctx (.inst D qs ls ps as)
        (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
  -- ADE: `Idⱼ`, in `Definition/Typed.agda`.
  /-- The equality of two terms of a type is a proposition at the level of the sort of this type.
  RFC: `\sim` -/
  | HasType.equality {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l : Level k} {A t u : Term k Γ} (hA : HasType sig ctx A (.sort ⟨s, l⟩))
      (ht : HasType sig ctx t A) (hu : HasType sig ctx u A) :
      HasType sig ctx (.equality s l A t u) (.sort ⟨.prop, l⟩)
  -- ADE: `rflⱼ`, in `Definition/Typed.agda`.
  /-- The proof by reflexivity of the equality of a term of a type with itself.
  RFC: `\mathsf{refl}_\sim` -/
  | HasType.reflProof {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l : Level k} {A t : Term k Γ} (hA : HasType sig ctx A (.sort ⟨s, l⟩))
      (ht : HasType sig ctx t A) : HasType sig ctx (.refl s l A t) (.equality s l A t t)
  -- ADE: `Jⱼ`, in `Definition/Typed.agda`, whose motive also binds the proof.
  /-- The transport of a term of the motive at the first of two terms of a type of a sort, along a
  proof of their equality, is a term of the motive at the second; the motive is a type of a sort `κ`
  over a term of the type.
  RFC: `\mathsf{transp}` -/
  | HasType.transp {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l : Level k} {κ : Universe k} {A t₁ t₂ t u : Term k Γ} {C : Term k (.var :: Γ)}
      (hA : HasType sig ctx A (.sort ⟨s, l⟩)) (ht₁ : HasType sig ctx t₁ A)
      (ht₂ : HasType sig ctx t₂ A) (hC : HasType sig (ctx.var A) C (.sort κ))
      (ht : HasType sig ctx t (.equality s l A t₁ t₂))
      (hu : HasType sig ctx u (C.subst₀ (Subst₀.single t₁))) :
      HasType sig ctx (.transp A t₁ t₂ C t u) (C.subst₀ (Subst₀.single t₂))
  -- ADE: none.
  /-- The proof by extensionality of the equality of two propositions of `Ω_l` that imply each
  other, by a proof `t` of `B` from a proof `x` of `A` and a proof `u` of `A` from a proof `y` of
  `B`, as terms of `Ω_l`.
  RFC: `\mathsf{propext}` -/
  | HasType.propExt {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      {A B : Term k Γ} {t u : Term k (.var :: Γ)} (hA : HasType sig ctx A (.sort ⟨.prop, l⟩))
      (hB : HasType sig ctx B (.sort ⟨.prop, l⟩))
      (ht : HasType sig (ctx.var A) t (B.rename Ren.weaken))
      (hu : HasType sig (ctx.var B) u (A.rename Ren.weaken)) :
      HasType sig ctx (.propExt l A B t u) (.equality .type (.succ l) (.sort ⟨.prop, l⟩) A B)
  -- ADE: none.
  /-- The proof by coinduction of the equality of two terms `t₁` and `t₂` of the instance
  `T_h = D_h.{s̄'; l̄'; p̄'} ā` it carries, which the constraint admits and whose arguments are
  arguments of the parameters, at the sort `s_l` of the block at the instance, with a relation
  `A_j` for each instance `T_j = D_j.{s̄'; l̄'; p̄'} ā` of a type of the block, a proposition of
  `Ω_l'` over two terms `x₁` and `x₂` of `T_j`, a proof `t` that `A_h` relates `t₁` and `t₂`, and a
  branch `g_ji` for each case of the block: the branch of a destructor `d_ji`, at the position
  `hd` in the destructors `(d̄_ji,1 | d_ji : (Θ_ji ⊢ B_ji ◀ ψ_ji) ▶ p_ji; q_ji ◀ ς_ji | d̄_ji,2)`
  of `T_j` at the instance, is a term over `x₁`, `x₂`, a proof `y` of `A_j` and the variables
  `z̄_ji` of the telescope of `d_ji`, of the equality
  `x₁.d_ji(z̄_ji) ∼.{s_ji; l_ji}_B_ji x₂.d_ji(z̄_ji)`, at the sort `κs i = (s_ji)_l_ji` of the
  result, if `d_ji` is not recursive, and of `A_j'` at `x₁.d_ji(z̄_ji)` and `x₂.d_ji(z̄_ji)` if the
  result of `d_ji` is the type `D_j'` of the block.
  The telescope and the result of each destructor are the same at the observations of `x₁` by the
  destructors `d̄_ji,1` before it and at those of `x₂`, so that no destructor depends on an earlier
  one.
  There are as many relations as types and as many branches as cases.
  The positions `h'` of the type of the terms in the block, `j` of a type and `i` of a case give the
  relations and the branches, as the order of the declaration does.
  RFC: `\mathsf{coind}` -/
  | HasType.coind {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {l' : Level k}
      {t₁ t₂ t : Term k Γ} {As : Terms k (Γ.extend 2)} {gs : DestructorBranches k Γ} {h' : Nat}
      {A : Term k (Γ.extend 2)} {κs : Nat → Universe k}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (hh : decl.codataTypes[h']? = some T) (hA : As.get h' = some A)
      (hAl : As.length = decl.codataTypes.length)
      (hAt : ∀ j T' A', decl.codataTypes[j]? = some T' → As.get j = some A' →
        HasType sig ((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken)) A' (.sort ⟨.prop, l'⟩))
      (ht₁ : HasType sig ctx t₁ (.inst D qs ls ps as))
      (ht₂ : HasType sig ctx t₂ (.inst D qs ls ps as))
      (ht : HasType sig ctx t ((A.subst₀ (Subst₀.liftN 1 (Subst₀.single t₁))).subst₀
        (Subst₀.single t₂)))
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length),
        decl.codataCases[i]? = some (j, T', d) →
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, 3, ps₁.length, g⟩)
      (hΘ : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length),
        decl.codataCases[i]? = some (j, T', d) →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        (Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst) =
          (Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst))
      (hB : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length),
        decl.codataCases[i]? = some (j, T', d) →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        (B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)) =
          (B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
      (hBt : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length) (A' : Term k (Γ.extend 2)),
        decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        B.blockName decl.names = none →
        HasType sig ((((ctx.var (.inst T'.name qs ls ps as)).var
            ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
            ((Θ.substLevels (ls.getFin hl)).subst
              (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
          (.sort (κs i)))
      (hgt : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length) (A' : Term k (Γ.extend 2))
          (g : Term k ((Γ.extend 3).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        B.blockName decl.names = none →
        gs.get i = some ⟨0, 3, ps₁.length, g⟩ →
        HasType sig ((((ctx.var (.inst T'.name qs ls ps as)).var
            ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
            ((Θ.substLevels (ls.getFin hl)).subst
              (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
          g
          (.equality (κs i).quality (κs i).level
            ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
              (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
            ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) d ps₁)
            ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation T'.name qs ls ps
              (as.rename (Ren.weakenN 3)) d ps₁)))
      (hgr : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
          (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length) (A' : Term k (Γ.extend 2)) (D' : Name) (j' : Nat)
          (A'' : Term k (Γ.extend 2)) (g : Term k ((Γ.extend 3).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        B.blockName decl.names = some D' → decl.names.idxOf? D' = some j' →
        As.get j' = some A'' →
        gs.get i = some ⟨0, 3, ps₁.length, g⟩ →
        HasType sig ((((ctx.var (.inst T'.name qs ls ps as)).var
            ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
            ((Θ.substLevels (ls.getFin hl)).subst
              (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
          g
          ((((A''.rename (Ren.liftN 2 (Ren.weakenN 3))).rename
              (Ren.liftN 2 (Ren.weakenN ps₁.length))).subst₀
            (Subst₀.liftN 1 (Subst₀.single
              ((Term.var₀ (.succ (.succ .zero)) : Term k (Γ.extend 3)).observation T'.name qs ls
                ps (as.rename (Ren.weakenN 3)) d ps₁)))).subst₀
            (Subst₀.single ((Term.var₀ (.succ .zero) : Term k (Γ.extend 3)).observation T'.name
              qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)))) :
      HasType sig ctx (.coind D qs ls ps as t₁ t₂ As t gs)
        (.equality ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).quality
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).level
          (.inst D qs ls ps as) t₁ t₂)
  -- ADE: none.
  /-- A constructor of a data type, applied to arguments of its fields at the instance it carries,
  which the constraint admits and whose arguments are arguments of the parameters, is a term of this
  instance.
  RFC: `c` -/
  | HasType.ctor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
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
  sort `κ` that the recursor carries, over a term of the instance of this type, and a branch for each case of the block, a term
  of the motive of its type at its constructor applied to the variables of its fields, in the
  context extended by its fields and by its recursive results, has the motive of the type of the
  term at the term; the motives on a block of propositions that has a constructor are propositions.
  The positions `h'` of the type of the term in the block, `j` of a type and `i` of a case give the
  motives and the branches, as the order of the declaration does.
  RFC: `\mathsf{rec}` -/
  | HasType.recursor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r ς χ : Grade}
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
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
        Telescope k (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
      (hRs : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs) (Rs con) πs)
      (hut : ∀ i j T' con C' u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con))
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      HasType sig ctx (.recursor r ς χ D qs ls ps as t κ Cs us) (C.subst₀ (Subst₀.single t))
  -- ADE: `_∘ⱼ_`, `fstⱼ` and `sndⱼ`, in `Definition/Typed.agda`.
  /-- An observation of a term of the instance it carries, which the constraint admits and whose
  arguments are arguments of the parameters, by one of the destructors of its codata type, at the
  position `hd` in the destructors `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)` of the type at
  the instance, applied to arguments of its telescope, has its result, the destructors `d̄₁` before
  it being the observations of the term by them, and the arguments substituted for the variables of
  the telescope.
  RFC: `d` -/
  | HasType.obs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
      {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership Grade ps'.length} {bs : Args k Γ ps'} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ)
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
  `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)` of its type `T'` at the instance, is a term of its
  result over the variables `ȳ` of the state of `T'` and those of the telescope of `d`, the
  destructors `d̄₁` before it being the observations of the corecursor of `T'` from `ȳ`.
  The positions `h'` of the type of the corecursor in the block, `j` of a type and `i` of a case
  give the states and the branches, as the order of the declaration does.
  RFC: `\mathsf{corec}` -/
  | HasType.corec {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Ss : States k Γ} {gs : DestructorBranches k Γ} {h' : Nat}
      {ps' : List Parameter} {S : Telescope k Γ ps'} {ss : Args k Γ ps'}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (i : Nat) (D' : Name),
        decl.codataTypes[j]? = some T' ∧
        (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
      (hss : HasArgs sig ctx ss S) (hSl : Ss.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S' : Telescope k Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
      (hSt : ∀ j T' (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss.get j = some ⟨0, ps'', S'⟩ →
        WfTelescopeSorts sig ctx S' (Ss.sorts j) (Telescope.packLevel (Ss.sorts j) .zero))
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
        HasType sig ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))) g
          (Term.branchResult decl.names B
            ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
            (ψ.constant.getD .unrestrictedUnrestricted)
            ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
            ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
              (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
                ls ps (as.rename (Ren.weakenN ps''.length)))
                (as.rename (Ren.weakenN ps''.length)).toSubst))))) :
      HasType sig ctx (.corec r D qs ls ps as ss.terms Ss gs) (.inst D qs ls ps as)
  -- ADE: `conv`, in `Definition/Typed.agda`.
  /-- A term has every type equal to its own.
  RFC: `\mathsf{conv}` -/
  | HasType.conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A B : Term k Γ}
      (ht : HasType sig ctx t A) (h : EqType sig ctx A B) : HasType sig ctx t B

  /-- The equality of terms is reflexive.
  RFC: `\mathsf{refl}` -/
  | EqTerm.refl {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t A : Term k Γ}
      (h : HasType sig ctx t A) : EqTerm sig ctx t t A
  /-- The equality of terms is symmetric.
  RFC: `\mathsf{sym}` -/
  | EqTerm.symm {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      (h : EqTerm sig ctx t u A) : EqTerm sig ctx u t A
  /-- The equality of terms is transitive.
  RFC: `\mathsf{trans}` -/
  | EqTerm.trans {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t₁ t₂ t₃ A : Term k Γ}
      (h₁ : EqTerm sig ctx t₁ t₂ A) (h₂ : EqTerm sig ctx t₂ t₃ A) : EqTerm sig ctx t₁ t₃ A
  /-- An equality holds at every type equal to its own.
  RFC: `\mathsf{conv}_\equiv` -/
  | EqTerm.conv {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A B : Term k Γ}
      (h : EqTerm sig ctx t u A) (hA : EqType sig ctx A B) : EqTerm sig ctx t u B
  /-- Two proofs of a proposition are equal.
  RFC: `\mathsf{irr}` -/
  | EqTerm.irr {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {t u A : Term k Γ}
      {l : Level k} (ht : HasType sig ctx t A) (hu : HasType sig ctx u A)
      (hA : HasType sig ctx A (.sort ⟨.prop, l⟩)) : EqTerm sig ctx t u A
  /-- Equal arguments give equal applications of a second-order variable.
  RFC: `\mathsf{var}_{X\equiv}` -/
  | EqTerm.secondOrder {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {ctx : Context k Γ} {X : Var Γ (.secondOrder ps ψ)} {Θ : Telescope k Γ ps} {A : Term k (Γ.extend ps.length)}
      {ts us : Args k Γ ps} (hX : ctx.SecondOrderIn X Θ A) (hts : EqArgs sig ctx ts us Θ) :
      EqTerm sig ctx (.var X ts) (.var X us) (A.instantiate ts)
  -- ADE: `δ-red`, in `Definition/Typed.agda`.
  /-- A constant definition, at an instance of its variables, unfolds to its body at this instance.
  RFC: `\delta` -/
  | EqTerm.delta {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {d : ConstantDefinition}
      {qs : List Quality} {ls : List (Level k)} {ps : List Grade} (hctx : WfCtx sig ctx)
      (h : .constantDefinition d ∈ sig) (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
      (hp : ps.length = d.grades) :
      EqTerm sig ctx (.const d.name qs ls ps)
        (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))
        (Signature.instanceType d.type (.ofLists qs ps hq hp) (ls.getFin hl))
  /-- Two instances of a constant at equal levels are equal.
  RFC: `f_\equiv` -/
  | EqTerm.const {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {f : Name} {j k' g : Nat}
      {m : Mode} {p : Grade} {A : Instance j g → Term k' []} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} (hctx : WfCtx sig ctx) (h : sig.HasConstant f j k' g m p A)
      (hq : qs.length = j) (hl₁ : ls₁.length = k') (hl₂ : ls₂.length = k') (hp : ps.length = g)
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) :
      EqTerm sig ctx (.const f qs ls₁ ps) (.const f qs ls₂ ps)
        (Signature.instanceType A (.ofLists qs ps hq hp) (ls₁.getFin hl₁))
  -- ADE: `U-cong`, in `Definition/Typed.agda`.
  /-- Universes at equal levels are equal.
  RFC: `U_\equiv` -/
  | EqTerm.univ {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.type, l₁⟩) (.sort ⟨.type, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- Universes of propositions at equal levels are equal.
  RFC: `\Omega_\equiv` -/
  | EqTerm.prop {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l₁ l₂ : Level k}
      (hctx : WfCtx sig ctx) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.sort ⟨.prop, l₁⟩) (.sort ⟨.prop, l₂⟩) (.sort ⟨.type, .succ l₁⟩)
  /-- Two instances of a declared type with equal arguments at equal levels are equal.
  RFC: `D_\equiv` -/
  | EqTerm.inst {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
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
  -- ADE: `Id-cong`, in `Definition/Typed.agda`.
  /-- Two equalities of equal terms of equal types, at equal levels, are equal.
  RFC: `\sim_\equiv` -/
  | EqTerm.equality {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l₁ l₂ : Level k} {A₁ A₂ t₁ t₂ u₁ u₂ : Term k Γ}
      (hA : EqTerm sig ctx A₁ A₂ (.sort ⟨s, l₁⟩)) (ht : EqTerm sig ctx t₁ t₂ A₁)
      (hu : EqTerm sig ctx u₁ u₂ A₁) (hl : l₁ ≈ l₂) :
      EqTerm sig ctx (.equality s l₁ A₁ t₁ u₁) (.equality s l₂ A₂ t₂ u₂) (.sort ⟨.prop, l₁⟩)
  -- ADE: `J-cong`, in `Definition/Typed.agda`, whose motive also binds the proof.
  /-- Two transports of equal terms, along equal proofs of the equality of equal terms of equal
  types, with equal motives of a sort `κ`, are equal.
  RFC: `\mathsf{transp}_\equiv` -/
  | EqTerm.transp {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l : Level k} {κ : Universe k} {A A' t₁ t₁' t₂ t₂' t t' u u' : Term k Γ}
      {C C' : Term k (.var :: Γ)} (hA : EqTerm sig ctx A A' (.sort ⟨s, l⟩))
      (ht₁ : EqTerm sig ctx t₁ t₁' A) (ht₂ : EqTerm sig ctx t₂ t₂' A)
      (hC : EqTerm sig (ctx.var A) C C' (.sort κ))
      (ht : EqTerm sig ctx t t' (.equality s l A t₁ t₂))
      (hu : EqTerm sig ctx u u' (C.subst₀ (Subst₀.single t₁))) :
      EqTerm sig ctx (.transp A t₁ t₂ C t u) (.transp A' t₁' t₂' C' t' u')
        (C.subst₀ (Subst₀.single t₂))
  -- ADE: none.
  /-- A transport between two equal instances of its motive, those at the two terms of the
  equality, is its term.
  RFC: `\mathsf{transp}_\mathsf{same}` -/
  | EqTerm.transpSame {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {s : Quality}
      {l : Level k} {κ : Universe k} {A t₁ t₂ t u : Term k Γ} {C : Term k (.var :: Γ)}
      (hA : HasType sig ctx A (.sort ⟨s, l⟩)) (ht₁ : HasType sig ctx t₁ A)
      (ht₂ : HasType sig ctx t₂ A) (hC : HasType sig (ctx.var A) C (.sort κ))
      (ht : HasType sig ctx t (.equality s l A t₁ t₂))
      (hu : HasType sig ctx u (C.subst₀ (Subst₀.single t₁)))
      (hCC : EqTerm sig ctx (C.subst₀ (Subst₀.single t₁)) (C.subst₀ (Subst₀.single t₂)) (.sort κ)) :
      EqTerm sig ctx (.transp A t₁ t₂ C t u) u (C.subst₀ (Subst₀.single t₂))
  -- ADE: none.
  /-- Two applications of the same constructor, at equal arguments of the instance, at equal levels
  and at equal arguments of its fields, are equal.
  RFC: `c_\equiv` -/
  | EqTerm.ctor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
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
  motives of the same sort and equal branches, with the same ownerships of the results of their
  nested fields, are equal, when the fields have the recursive results of both; the branches are
  equal in the context of the results of the first.
  RFC: `\mathsf{rec}_\equiv` -/
  | EqTerm.recursor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {r ς χ : Grade} {t₁ t₂ : Term k Γ} {Cs₁ Cs₂ : Motives k Γ} {us₁ us₂ : Branches k Γ}
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
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hus₂ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      (hes : us₁.grades = us₂.grades)
      {Rs₁ Rs₂ : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
        Telescope k (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
      (hRs₁ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls₁.getFin hl₁) as₁ (Lifting.ofMotives decl.names qs ls₁ ps as₁ κ.level χ Cs₁)
          (Rs₁ con) πs)
      (hRs₂ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls₂.getFin hl₂) as₂ (Lifting.ofMotives decl.names qs ls₂ ps as₂ κ.level χ Cs₂)
          (Rs₂ con) πs)
      (hut : ∀ i j T' con C' u₁ u₂, decl.cases[i]? = some (j, T', con) → Cs₁.get j = some ⟨0, C'⟩ →
        us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
        us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
        EqTerm sig
          ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)).append (Rs₁ con)) u₁
          u₂
          ((C'.atCtor T'.name qs ls₁ ps as₁ con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (.recursor r ς χ D qs ls₁ ps as₁ t₁ κ Cs₁ us₁)
        (.recursor r ς χ D qs ls₂ ps as₂ t₂ κ Cs₂ us₂) (C₁.subst₀ (Subst₀.single t₁))
  -- ADE: `app-cong`, `fst-cong` and `snd-cong`, in `Definition/Typed.agda`.
  /-- Two observations by the same destructor, at equal arguments of the instance, at equal levels,
  of equal terms, at equal arguments of its telescope, are equal.
  RFC: `d_\equiv` -/
  | EqTerm.obs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {t₁ t₂ : Term k Γ} {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
      {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
      {ψ : ResultOwnership Grade ps'.length} {bs₁ bs₂ : Args k Γ ps'} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ)
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
  | EqTerm.corec {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ decl.scope}
      {r : Grade} {Ss₁ Ss₂ : States k Γ} {gs₁ gs₂ : DestructorBranches k Γ}
      {h' : Nat} {ps' : List Parameter} {S₁ S₂ : Telescope k Γ ps'} {ss₁ ss₂ : Args k Γ ps'}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
      (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (i : Nat) (D' : Name),
        decl.codataTypes[j]? = some T' ∧
        (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude)
      (has : EqInstanceArgs sig ctx as₁ as₂
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
      (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
      (hh : decl.codataTypes[h']? = some T) (hS₁ : Ss₁.get h' = some ⟨0, ps', S₁⟩)
      (hS₂ : Ss₂.get h' = some ⟨0, ps', S₂⟩) (hss : EqArgs sig ctx ss₁ ss₂ S₁)
      (hSl₁ : Ss₁.length = decl.codataTypes.length) (hSl₂ : Ss₂.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S₁' S₂' : Telescope k Γ ps''),
          Ss₁.get j = some ⟨0, ps'', S₁'⟩ ∧ Ss₂.get j = some ⟨0, ps'', S₂'⟩)
      (hSk : ∀ j, Ss₁.sorts j = Ss₂.sorts j)
      (hSt : ∀ j T' (ps'' : List Parameter) (S₁' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        WfTelescopeSorts sig ctx S₁' (Ss₁.sorts j) (Telescope.packLevel (Ss₁.sorts j) .zero))
      (hSe : ∀ j T' (ps'' : List Parameter) (S₁' S₂' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        Ss₂.get j = some ⟨0, ps'', S₂'⟩ →
        EqTelescope sig ctx S₁' S₂' ⟨.type, Telescope.packLevel (Ss₁.sorts j) .zero⟩)
      (hgl₁ : gs₁.length = decl.codataCases.length) (hgl₂ : gs₂.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S₁' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
          gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S₁' : Telescope k Γ ps'') (p q ς : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
        (g₁ g₂ : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss₁.get j = some ⟨0, ps'', S₁'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
        gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
        EqTerm sig ((ctx.append S₁').append ((Θ.substLevels (ls₁.getFin hl₁)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls₁ ps as₁ Ss₁ gs₁ ps'').observation T'.name
            qs ls₁ ps (as₁.rename (Ren.weakenN ps''.length)))
            (as₁.rename (Ren.weakenN ps''.length)).toSubst))) g₁ g₂
          (Term.branchResult decl.names B
            ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)) r
            (ψ.constant.getD .unrestrictedUnrestricted)
            ((Ss₁.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
            ((B.substLevels (ls₁.getFin hl₁)).subst (Subst.liftN _
              (hd.obsSubst ((Term.corecAt r T'.name qs ls₁ ps as₁ Ss₁ gs₁ ps'').observation
                T'.name qs ls₁ ps (as₁.rename (Ren.weakenN ps''.length)))
                (as₁.rename (Ren.weakenN ps''.length)).toSubst))))) :
      EqTerm sig ctx (.corec r D qs ls₁ ps as₁ ss₁.terms Ss₁ gs₁)
        (.corec r D qs ls₂ ps as₂ ss₂.terms Ss₂ gs₂) (.inst D qs ls₁ ps as₁)
  -- ADE: `natrec-zero`, `natrec-suc`, `prodrec-β` and `unitrec-β`, in `Definition/Typed.agda`.
  /-- A recursor on a constructor applied to arguments of its fields, with the premises of `(rec)`,
  is equal to the branch of the constructor, the case `i` of the block, with the arguments
  substituted for the variables of the fields and, for those of the recursive results, the
  recursive results of these arguments, where the result of a term of a type of the block is the
  recursor on it, at the same instance, with the same motives and the same branches.
  RFC: `\iota` -/
  | EqTerm.iota {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r ς χ : Grade}
      {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k} {i j : Nat}
      {C : Term k (.var :: Γ)} (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      {u : Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length)}
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      {ts : Args k Γ (con.params (.ofLists qs ps hq hp))}
      (hts : HasArgs sig ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      (hi : decl.cases[i]? = some (j, T, con)) (hC : Cs.get j = some ⟨0, C⟩)
      (hu : us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      {rs : Args k Γ (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
      (hrs : Constructor.ResultTerms sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs)
        (Term.recursorAt r ς χ qs ls ps as κ Cs us) ts rs)
      (hCl : Cs.length = decl.dataTypes.length)
      (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
      (hCt : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
        HasType sig (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
      (hul : us.length = decl.cases.length)
      (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
        Telescope k (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
      (hRs : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs) (Rs con) πs)
      (hut : ∀ i j T' con C' u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con))
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (.recursor r ς χ D qs ls ps as (.ctor D qs ls ps as con.name ts.terms) κ Cs us)
        ((u.instantiate (rs.rename (Ren.weakenN _))).instantiate ts)
        (C.subst₀ (Subst₀.single (.ctor D qs ls ps as con.name ts.terms)))
  -- ADE: `unitrec-β-η`, in `Definition/Typed.agda`, for the unit type with `η`.
  /-- A term `e` over a term `t` of a data type with a single constructor whose fields have no
  recursive result, the case `i` of the block, is equal to the recursor on `t`, with the premises of `(rec)`, whose motive of
  the type is that of `e` and whose branch of the constructor is `e` at the constructor applied to its
  fields.
  RFC: `\eta_c` -/
  | EqTerm.etaCtor {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r ς χ : Grade}
      {t : Term k Γ} {Cs : Motives k Γ} {us : Branches k Γ} {κ : Universe k} {i j : Nat}
      {C e : Term k (.var :: Γ)} (h : sig.HasDataType D decl T) (hc : T.constructors = [con])
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hr : ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ν = .plain)
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
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
      {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
        Telescope k (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
          (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
      (hRs : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
        ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
          (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs) (Rs con) πs)
      (hut : ∀ i j T' con C' u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
        us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
        HasType sig ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con))
          u ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
            (Ren.weakenN _)))
      (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
        κ.quality = .prop) :
      EqTerm sig ctx (e.subst₀ (Subst₀.single t)) (.recursor r ς χ D qs ls ps as t κ Cs us)
        (C.subst₀ (Subst₀.single t))
  -- ADE: `β-red`, `Σ-β₁` and `Σ-β₂`, in `Definition/Typed.agda`.
  /-- An observation of a corecursor by the destructor of the case `i` of the block, a destructor of
  the type of the corecursor, applied to arguments of its telescope, with the premises of `(corec)`,
  is equal to the branch of the destructor, with the terms of the state substituted for the
  variables of the state and the arguments for those of the telescope.
  RFC: `\beta` -/
  | EqTerm.beta {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {r : Grade}
      {Ss : States k Γ} {gs : DestructorBranches k Γ} {h' i : Nat}
      {ps' : List Parameter}
      {S : Telescope k Γ ps'} {ss : Args k Γ ps'} {d : Name} {p q ς : Grade} {ps₀ : List Parameter}
      {Ξ₀ : Scope} {Θ₀ : Telescope decl.levels Ξ₀ ps₀} {B₀ : Term decl.levels (Ξ₀.extend ps₀.length)}
      {ψ₀ : ResultOwnership Grade ps₀.length} {g : Term k ((Γ.extend ps'.length).extend ps₀.length)}
      {bs : Args k Γ ps₀} (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (i : Nat) (D' : Name),
        decl.codataTypes[j]? = some T' ∧
        (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
      (hss : HasArgs sig ctx ss S) (hi : decl.codataCases[i]? = some (h', T, d))
      (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ₀ Θ₀ B₀ ψ₀)
      (hg : gs.get i = some ⟨0, ps'.length, ps₀.length, g⟩)
      (hbs : HasArgs sig ctx bs ((Θ₀.substLevels (ls.getFin hl)).subst
        (hd.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
          as.toSubst)))
      (hSl : Ss.length = decl.codataTypes.length)
      (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
        ∃ (ps'' : List Parameter) (S' : Telescope k Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
      (hSt : ∀ j T' (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataTypes[j]? = some T' → Ss.get j = some ⟨0, ps'', S'⟩ →
        WfTelescopeSorts sig ctx S' (Ss.sorts j) (Telescope.packLevel (Ss.sorts j) .zero))
      (hgl : gs.length = decl.codataCases.length)
      (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
        (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
        ∃ g, gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
      (hgt : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade)
        (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
        (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
        decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
        HasType sig ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs ls
            ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))) g
          (Term.branchResult decl.names B
            ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
            (ψ.constant.getD .unrestrictedUnrestricted)
            ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
            ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
              (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs ps'').observation T'.name qs
                ls ps (as.rename (Ren.weakenN ps''.length)))
                (as.rename (Ren.weakenN ps''.length)).toSubst))))) :
      EqTerm sig ctx (.obs D qs ls ps as (.corec r D qs ls ps as ss.terms Ss gs) d bs.terms)
        (Term.observed decl.names (B₀.blockName decl.names) r qs ls ps as Ss gs
          ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
          (ψ₀.constant.getD .unrestrictedUnrestricted)
          ((g.instantiate (bs.rename (Ren.weakenN ps'.length))).instantiate ss))
        (((B₀.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hd.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D
            qs ls ps as) as.toSubst))).instantiate bs)
  -- ADE: `η-eq`, `Σ-η` and `η-unit`, in `Definition/Typed.agda`.
  /-- Two terms of the instance of a codata type without recursive destructor, whose arguments are
  arguments of the parameters, whose observations by each destructor, at the position `hd` in the
  destructors `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)` of the type at the instance, are
  equal over the variables of its telescope, the destructors `d̄₁` before it being the observations
  of the first term by them, are equal. The premise `hr` is not needed by the soundness: comparing two
  terms by their observations ends only when no observation gives a term of the block again.
  RFC: `\eta_d` -/
  | EqTerm.etaObs {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration}
      {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
      {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {t u : Term k Γ}
      (h : sig.HasCodataType D decl T)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (hadm : decl.constraint (.ofLists qs ps hq hp))
      (hr : ∀ R ∈ (T.body (.ofLists qs ps hq hp)).recursion decl.names, R = none)
      (has : HasInstanceArgs sig ctx as
        ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
      (ht : HasType sig ctx t (.inst D qs ls ps as)) (hu : HasType sig ctx u (.inst D qs ls ps as))
      (hobs : ∀ (d : Name) (p q ς : Grade) (ps' : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
        (ψ : ResultOwnership Grade ps'.length) (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ),
        EqTerm sig (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
          (t.observation D qs ls ps as d ps') (u.observation D qs ls ps as d ps')
          ((B.substLevels (ls.getFin hl)).subst
            (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))) :
      EqTerm sig ctx t u (.inst D qs ls ps as)

  /-- No argument for the empty telescope.
  RFC: `\mathsf{tel}_\varepsilon` -/
  | HasArgs.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasArgs sig ctx .nil .nil
  /-- The first argument, of the type of the first entry, and the others, of the telescope that
  it instantiates.
  RFC: `\mathsf{tel}_{,}` -/
  | HasArgs.cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade} {p : Parameter}
      {t A : Term k Γ} {ts : Args k Γ ps} {Θ : Telescope k (.var :: Γ) ps}
      (ht : HasType sig ctx t A) (hts : HasArgs sig ctx ts (Θ.subst₀ (Subst₀.single t))) :
      HasArgs sig ctx (.cons t ts) (.cons q p A Θ)

  /-- No argument for the empty telescope.
  RFC: `\mathsf{tel}_{\varepsilon\equiv}` -/
  | EqArgs.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqArgs sig ctx .nil .nil .nil
  /-- The first arguments, equal at the type of the first entry, and the others, equal in the
  telescope that the first argument instantiates.
  RFC: `\mathsf{tel}_{,\equiv}` -/
  | EqArgs.cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade} {p : Parameter}
      {t u A : Term k Γ} {ts us : Args k Γ ps} {Θ : Telescope k (.var :: Γ) ps}
      (ht : EqTerm sig ctx t u A) (hts : EqArgs sig ctx ts us (Θ.subst₀ (Subst₀.single t))) :
      EqArgs sig ctx (.cons t ts) (.cons u us) (.cons q p A Θ)

  /-- No argument for the empty parameters.
  RFC: `\mathsf{arg}_\varepsilon` -/
  | HasInstanceArgs.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      HasInstanceArgs sig ctx .nil .empty
  /-- The arguments of the parameters before a variable, and the argument of its type, which they
  instantiate.
  RFC: `\mathsf{arg}_x` -/
  | HasInstanceArgs.var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ} {as : InstanceArgs k Γ Δ}
      {params : Context k Δ} {a : Term k Γ} {A : Term k Δ}
      (has : HasInstanceArgs sig ctx as params) (ha : HasType sig ctx a (A.subst as.toSubst)) :
      HasInstanceArgs sig ctx (.snoc (e := .var) as a) (params.var A)
  /-- The arguments of the parameters before a second-order variable, and the abstraction for it, a
  term of its type under the variables of its telescope, which they instantiate.
  RFC: `\mathsf{arg}_X` -/
  | HasInstanceArgs.secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {ctx : Context k Γ}
      {as : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B : Term k (Γ.extend ps.length)}
      (has : HasInstanceArgs sig ctx as params)
      (hB : HasType sig (ctx.append (Θ.subst as.toSubst)) B
        (A.subst (Subst.liftN _ as.toSubst))) :
      HasInstanceArgs sig ctx (.snoc (e := .secondOrder ps ψ) as B)
        (params.secondOrder Θ A ψ)

  /-- No argument for the empty parameters.
  RFC: `\mathsf{arg}_{\varepsilon\equiv}` -/
  | EqInstanceArgs.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} (hctx : WfCtx sig ctx) :
      EqInstanceArgs sig ctx .nil .nil .empty
  /-- Equal arguments of the parameters before a variable, and equal arguments of its type, which
  the first ones instantiate.
  RFC: `\mathsf{arg}_{x\equiv}` -/
  | EqInstanceArgs.var {sig : Signature} {k : Nat} {Γ Δ : Scope} {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} {a₁ a₂ : Term k Γ} {A : Term k Δ}
      (has : EqInstanceArgs sig ctx as₁ as₂ params)
      (ha : EqTerm sig ctx a₁ a₂ (A.subst as₁.toSubst)) :
      EqInstanceArgs sig ctx (.snoc (e := .var) as₁ a₁) (.snoc (e := .var) as₂ a₂) (params.var A)
  /-- Equal arguments of the parameters before a second-order variable, and equal abstractions for
  it, under the variables of its telescope, which the first ones instantiate.
  RFC: `\mathsf{arg}_{X\equiv}` -/
  | EqInstanceArgs.secondOrder {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {ctx : Context k Γ}
      {as₁ as₂ : InstanceArgs k Γ Δ} {params : Context k Δ} {Θ : Telescope k Δ ps}
      {A : Term k (Δ.extend ps.length)} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (has : EqInstanceArgs sig ctx as₁ as₂ params)
      (hB : EqTerm sig (ctx.append (Θ.subst as₁.toSubst)) B₁ B₂
        (A.subst (Subst.liftN _ as₁.toSubst))) :
      EqInstanceArgs sig ctx (.snoc (e := .secondOrder ps ψ) as₁ B₁)
        (.snoc (e := .secondOrder ps ψ) as₂ B₂) (params.secondOrder Θ A ψ)

  /-- The empty telescope lives in every sort.
  RFC: `\mathsf{tel}_{\kappa\varepsilon}` -/
  | WfTelescope.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {κ : Universe k}
      (hctx : WfCtx sig ctx) : WfTelescope sig ctx .nil κ
  /-- The first entry, whose type lives in a sort that `κ₂` bounds, with a grade without use at
  run time if it is a proposition, and the others.
  RFC: `\mathsf{tel}_{\kappa,}` -/
  | WfTelescope.cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade}
      {p : Parameter} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps} {κ₁ κ₂ : Universe k}
      (hA : HasType sig ctx A (.sort κ₁)) (hκ : κ₁ ≼ κ₂) (hΘ : WfTelescope sig (ctx.var A) Θ κ₂)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfTelescope sig ctx (.cons q p A Θ) κ₂

  /-- The empty telescope, of no sort, below every level.
  RFC: `\mathsf{tel}_{\bar\kappa\varepsilon}` -/
  | WfTelescopeSorts.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {l : Level k}
      (hctx : WfCtx sig ctx) : WfTelescopeSorts sig ctx .nil [] l
  /-- The first entry, whose type lives in the sort `κ` of a level below `l`, with a grade without
  use at run time if it is a proposition, and the others.
  RFC: `\mathsf{tel}_{\bar\kappa,}` -/
  | WfTelescopeSorts.cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {q : Grade} {p : Parameter} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps} {κ : Universe k}
      {κs : List (Universe k)} {l : Level k} (hA : HasType sig ctx A (.sort κ))
      (hl : κ.level ≤ l) (hΘ : WfTelescopeSorts sig (ctx.var A) Θ κs l)
      (hp : κ.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfTelescopeSorts sig ctx (.cons q p A Θ) (κ :: κs) l

  /-- The empty telescope is equal to itself in every sort.
  RFC: `\mathsf{tel}_{\kappa\varepsilon\equiv}` -/
  | EqTelescope.nil {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {κ : Universe k}
      (hctx : WfCtx sig ctx) : EqTelescope sig ctx .nil .nil κ
  /-- The first entries, with the same grades, whose types are equal types of a sort that `κ₂`
  bounds, with a grade without use at run time if they are propositions, and the others, equal in
  the context extended by the first entry of the first telescope.
  RFC: `\mathsf{tel}_{\kappa,\equiv}` -/
  | EqTelescope.cons {sig : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ}
      {q : Grade} {p : Parameter} {A₁ A₂ : Term k Γ} {Θ₁ Θ₂ : Telescope k (.var :: Γ) ps}
      {κ₁ κ₂ : Universe k} (hA : EqTerm sig ctx A₁ A₂ (.sort κ₁)) (hκ : κ₁ ≼ κ₂)
      (hΘ : EqTelescope sig (ctx.var A₁) Θ₁ Θ₂ κ₂)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      EqTelescope sig ctx (.cons q p A₁ Θ₁) (.cons q p A₂ Θ₂) κ₂

  /-- No field.
  RFC: `\mathsf{fields}_\varepsilon` -/
  | WfFields.nil {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {κ : Universe decl.levels}
      (hctx : WfCtx sig ctx) : WfFields sig decl ι as ctx .nil κ
  /-- A first field whose type has no position and lives in a sort that `κ` bounds, and the
  others, in the context extended by it.
  RFC: `\mathsf{fields}_{,}` -/
  | WfFields.cons {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {q : Grade} {p : Parameter} {A : Term decl.levels Γ}
      {Θ : Telescope decl.levels (.var :: Γ) ps} {κ₁ κ : Universe decl.levels}
      (hn : A.blockNest decl.names = .plain) (hA : HasType sig ctx A (.sort κ₁)) (hκ : κ₁ ≼ κ)
      (hΘ : WfFields sig decl ι (as.rename Ren.weaken) (ctx.var A) Θ κ)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfFields sig decl ι as ctx (.cons q p A Θ) κ
  /-- A first field that is recursive, a type `D` of the block at the instance of the block and at
  the parameters, with a grade without use at run time if the block is a block of propositions, and
  the others, which do not depend on it, in the same context.
  RFC: `\mathsf{fields}_{\mathsf{rec}}` -/
  | WfFields.recursive {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {q : Grade} {p : Parameter} {D : Name} {Θ : Telescope decl.levels Γ ps}
      {κ : Universe decl.levels} (hD : D ∈ decl.names) (hΘ : WfFields sig decl ι as ctx Θ κ)
      (hp : κ.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfFields sig decl ι as ctx (.cons q p (decl.blockInstance ι D as) (Θ.rename Ren.weaken)) κ
  /-- A first field that is nested, the type `A₀` at the types of the block, at the instance of the
  block and at the parameters, in place of its type variables `X̄`, one of the universe `κ` for each
  type of the block: its nesting is that of an instance, `A₀` lives in a sort that `κ` bounds, in
  the context extended by `X̄`, and is strictly positive in each of them, in a signature that holds
  the prelude, with a grade without use at run time if it is a proposition, and the others, which do
  not depend on it, in the same context.
  RFC: `\mathsf{fields}_\lambda` -/
  | WfFields.nested {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {as : InstanceArgs decl.levels Γ decl.scope} {ctx : Context decl.levels Γ} {ps : List Parameter}
      {q : Grade} {p : Parameter}
      {A₀ : Term decl.levels
        (Γ.extend (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length)}
      {Θ : Telescope decl.levels Γ ps} {κ₁ κ : Universe decl.levels} {νs : List (Nest Name)}
      (hn : (A₀.instantiate (decl.blockArgs ι as)).blockNest decl.names = .inst νs)
      (hA₀ : HasType sig (ctx.append (Telescope.sorts κ decl.names.length)) A₀ (.sort κ₁))
      (hκ : κ₁ ≼ κ) (hq : κ.quality = .type)
      (hpos : ∀ z : Var (Scope.extend []
          (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) .var,
        Term.Positive (sig.PositiveIn decl) (Ren.liftN _ Ren.empty z) A₀)
      (hpre : sig.HasPrelude) (hΘ : WfFields sig decl ι as ctx Θ κ)
      (hp : κ₁.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfFields sig decl ι as ctx
        (.cons q p (A₀.instantiate (decl.blockArgs ι as)) (Θ.rename Ren.weaken)) κ

  /-- No destructor lives in every sort.
  RFC: `\bar d_{\kappa\varepsilon}` -/
  | WfDestructors.nil {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope}
      {ctx : Context decl.levels Γ} {κ : Universe decl.levels} (hctx : WfCtx sig ctx) :
      WfDestructors sig decl ι @ν as ctx .nil κ
  /-- A first destructor that is not recursive and whose result has no position, whose arguments
  live in the universe of the level of `κ` and whose result lives in a sort that `κ` bounds, with a
  grade without use at run time if it is a proposition, and the others, in the context extended by
  it.
  RFC: `\bar d_{\kappa|}` -/
  | WfDestructors.cons {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope} {d : Name}
      {ns : List Name} {ps : List Parameter} {ctx : Context decl.levels Γ} {p q ς : Grade}
      {Θ : Telescope decl.levels Γ ps} {B : Term decl.levels (Γ.extend ps.length)}
      {ψ : ResultOwnership Grade ps.length} {ds : Destructors decl.levels (.secondOrder ps ψ :: Γ) ns}
      {κ₁ κ : Universe decl.levels} (hn : B.blockName decl.names = none)
      (hν : B.nest (fun _ => none) (Nesting.liftN ps.length @ν) = .plain)
      (hΘ : WfTelescope sig ctx Θ ⟨.type, κ.level⟩)
      (hB : HasType sig (ctx.append Θ) B (.sort κ₁)) (hκ : κ₁ ≼ κ)
      (hp : κ₁.quality = .prop → p.mode ≠ .oneOne)
      (hds : WfDestructors sig decl ι (Nesting.lift @ν) (as.rename Ren.weaken)
        (ctx.secondOrder Θ B ψ) ds κ) :
      WfDestructors sig decl ι @ν as ctx (.cons (d := d) p q ς Θ B ψ ds) κ
  /-- A first destructor that is not recursive and whose result has a position, whose arguments
  live in the universe of the level of `κ` and whose result lives in a sort that `κ` bounds, with a
  grade without use at run time if it is a proposition, and the others, which do not depend on it,
  in the same context.
  RFC: `\bar d_{\kappa\lambda}` -/
  | WfDestructors.nested {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope} {d : Name}
      {ns : List Name} {ps : List Parameter} {ctx : Context decl.levels Γ} {p q ς : Grade}
      {Θ : Telescope decl.levels Γ ps} {B : Term decl.levels (Γ.extend ps.length)}
      {ψ : ResultOwnership Grade ps.length} {ds : Destructors decl.levels Γ ns}
      {κ₁ κ : Universe decl.levels} (hn : B.blockName decl.names = none)
      (hν : B.nest (fun _ => none) (Nesting.liftN ps.length @ν) ≠ .plain)
      (hΘ : WfTelescope sig ctx Θ ⟨.type, κ.level⟩)
      (hB : HasType sig (ctx.append Θ) B (.sort κ₁)) (hκ : κ₁ ≼ κ)
      (hp : κ₁.quality = .prop → p.mode ≠ .oneOne)
      (hds : WfDestructors sig decl ι @ν as ctx ds κ) :
      WfDestructors sig decl ι @ν as ctx (.cons (d := d) p q ς Θ B ψ (ds.rename Ren.weaken)) κ
  /-- A first destructor that is recursive, whose arguments live in the universe of the level of `κ`
  and whose result is a type `D` of the block at the instance of the block and at the parameters,
  with a grade without use at run time if the block is a block of propositions, and the others, which
  do not depend on it, in the same context.
  RFC: `\bar d_{\kappa\mathsf{rec}}` -/
  | WfDestructors.recursive {sig : Signature} {decl : TypeDeclaration} {ι : Instance decl.sorts decl.grades}
      {Γ : Scope} {ν : Nesting Nat Γ} {as : InstanceArgs decl.levels Γ decl.scope} {d : Name}
      {ns : List Name} {ps : List Parameter} {ctx : Context decl.levels Γ} {p q ς : Grade}
      {Θ : Telescope decl.levels Γ ps} {ψ : ResultOwnership Grade ps.length} {D : Name}
      {ds : Destructors decl.levels Γ ns} {κ : Universe decl.levels} (hD : D ∈ decl.names)
      (hΘ : WfTelescope sig ctx Θ ⟨.type, κ.level⟩)
      (hp : κ.quality = .prop → p.mode ≠ .oneOne)
      (hds : WfDestructors sig decl ι @ν as ctx ds κ) :
      WfDestructors sig decl ι @ν as ctx
        (.cons (d := d) p q ς Θ (decl.blockInstance ι D (as.rename (Ren.weakenN ps.length))) ψ
          (ds.rename Ren.weaken)) κ

  /-- A block of data types.
  RFC: `\mathsf{data}` -/
  | WfTypeDeclaration.data {sig : Signature} {decl : TypeDeclaration} {Ts : List (DataType decl.sorts decl.grades
      decl.levels decl.scope)} (hb : decl.body = .data Ts)
      (hadm : ∃ ι, decl.constraint ι) (hΔ : ∀ ι, decl.constraint ι → WfCtx sig (decl.params ι))
      (hΘ : ∀ ι, decl.constraint ι → ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        WfFields sig decl ι (.identity decl.scope) (decl.params ι) (c.fields ι) (decl.sort ι))
      (hp : ∀ ι, decl.constraint ι → ∀ T ∈ decl.dataTypes, ∀ {e : Scope.Entry}
        (x : Var decl.scope e), T.positive x.level → ∀ c ∈ T.constructors,
          (c.fields ι).Positive (sig.PositiveIn decl) x)
      (hc : ∀ T ∈ decl.dataTypes, (T.constructors.map (·.name)).Nodup)
      (fresh : ∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names) :
      WfTypeDeclaration sig decl
  /-- A block of codata types.
  RFC: `\mathsf{codata}` -/
  | WfTypeDeclaration.codata {sig : Signature} {decl : TypeDeclaration} {Ts : List (CodataType decl.sorts
      decl.grades decl.levels decl.scope)} (hb : decl.body = .codata Ts)
      (hadm : ∃ ι, decl.constraint ι) (hΔ : ∀ ι, decl.constraint ι → WfCtx sig (decl.params ι))
      (hd : ∀ ι, decl.constraint ι → ∀ T ∈ decl.codataTypes,
        WfDestructors sig decl ι (Nesting.ofPositive T.positive) (.identity decl.scope)
          (decl.params ι) (T.body ι) (decl.sort ι))
      (hp : ∀ ι, decl.constraint ι → ∀ T ∈ decl.codataTypes, ∀ {e : Scope.Entry}
        (x : Var decl.scope e), T.positive x.level →
          (T.body ι).Positive (sig.PositiveIn decl) x)
      (hc : ∀ T ∈ decl.codataTypes, T.destructors.Nodup)
      (fresh : ∀ e ∈ sig, ∀ D ∈ decl.names, D ∉ e.names) :
      WfTypeDeclaration sig decl

end

-- ADE: `»_`, in `Definition/Typed.agda`, for contexts of definitions.
/-- `⊢ Σ`: the signature is well formed. -/
abbrev WfSig (sig : Signature) : Prop :=
  Derivable (.wfSig sig)

/--
`Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p ≔ t`: for each instance of the sort and grade variables, the type `A` is a
type of some sort and the body `t` a term of it, both in the empty context.
-/
abbrev WfConstantDefinition (sig : Signature) (d : ConstantDefinition) : Prop :=
  Derivable (.wfConstantDefinition sig d)

/-- `Σ ⊢ f.{s̄; l̄; p̄} : A ▶ m ◀ p`: for each instance of the sort and grade variables, the type `A` is a
type of some sort in the empty context. -/
abbrev WfConstantDeclaration (sig : Signature) (c : ConstantDeclaration) : Prop :=
  Derivable (.wfConstantDeclaration sig c)

-- ADE: `_»⊢_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ Γ`: the context is well formed. -/
abbrev WfCtx (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) : Prop :=
  Derivable (.wfCtx sig ctx)

-- ADE: `_⊢_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A`: `A` is a type. -/
abbrev WfType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A : Term k Γ) : Prop :=
  Derivable (.wfType sig ctx A)

-- ADE: `_⊢_≡_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ A ≡ B`: `A` and `B` are equal types. -/
abbrev EqType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ) (A B : Term k Γ) : Prop :=
  Derivable (.eqType sig ctx A B)

-- ADE: `_⊢_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t : A`: `t` is a term of type `A`. -/
abbrev HasType (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t A : Term k Γ) : Prop :=
  Derivable (.hasType sig ctx t A)

-- ADE: `_⊢_≡_∷_`, in `Definition/Typed.agda`.
/-- `Σ; Γ ⊢ t ≡ u : A`: `t` and `u` are equal terms of type `A`. -/
abbrev EqTerm (sig : Signature) {k : Nat} {Γ : Scope} (ctx : Context k Γ)
    (t u A : Term k Γ) : Prop :=
  Derivable (.eqTerm sig ctx t u A)

/-- `Σ; Γ ⊢ t̄ : Θ`: the arguments are typed by the telescope, each argument instantiating the types
after it, whose grades typing ignores. -/
abbrev HasArgs (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
    (ts : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  Derivable (.hasArgs sig ctx ts Θ)

/-- `Σ; Γ ⊢ t̄ ≡ ū : Θ`: the arguments are equal, typed by the telescope. -/
abbrev EqArgs (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
    (ts us : Args k Γ ps) (Θ : Telescope k Γ ps) : Prop :=
  Derivable (.eqArgs sig ctx ts us Θ)

/-- `Σ; Γ ⊢ ā : Δ`: the arguments of an instance are typed by its parameters, each argument
instantiating the types after it. -/
abbrev HasInstanceArgs (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ)
    (as : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  Derivable (.hasInstanceArgs sig ctx as params)

/-- `Σ; Γ ⊢ ā₁ ≡ ā₂ : Δ`: the arguments of two instances are equal, typed by the parameters. -/
abbrev EqInstanceArgs (sig : Signature) {k : Nat} {Γ Δ : Scope} (ctx : Context k Γ)
    (as₁ as₂ : InstanceArgs k Γ Δ) (params : Context k Δ) : Prop :=
  Derivable (.eqInstanceArgs sig ctx as₁ as₂ params)

/--
`Σ; Γ ⊢ Θ : κ`: the telescope lives in the sort `κ`, each of its types living in a sort that `κ`
bounds, and an entry whose type is a proposition has a grade without use at run time.
-/
abbrev WfTelescope (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  Derivable (.wfTelescope sig ctx Θ κ)

-- ADE: none.
/-- `Σ; Γ ⊢ Θ : κ̄ ≤ l`: the types of the telescope `Θ` live in the sorts `κ̄`, one for each entry,
whose levels are below `l`, and an entry whose type is a proposition has a grade without use at run
time, as in a telescope in a sort; the packing of `Θ` needs the sort of each entry, which the
telescope does not give. -/
abbrev WfTelescopeSorts (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (Θ : Telescope k Γ ps) (κs : List (Universe k)) (l : Level k) : Prop :=
  Derivable (.wfTelescopeSorts sig ctx Θ κs l)

-- ADE: none.
/--
`Σ; Γ ⊢ Θ₁ ≡ Θ₂ : κ`: the telescopes are equal in the sort `κ`, entry by entry, with the same grades,
their types being equal types of a sort that `κ` bounds, and an entry whose type is a proposition has
a grade without use at run time.
-/
abbrev EqTelescope (sig : Signature) {k : Nat} {Γ : Scope} {ps : List Parameter}
    (ctx : Context k Γ) (Θ₁ Θ₂ : Telescope k Γ ps) (κ : Universe k) : Prop :=
  Derivable (.eqTelescope sig ctx Θ₁ Θ₂ κ)

-- ADE: none.
/--
`Σ; Γ ⊢_𝒟 Θ : κ`: the fields `Θ` of a constructor of the block of data types `decl`, at the instance
`ι` of its sort and grade variables, live in the sort `κ`, in the context `Γ` of the parameters
extended by the fields before them that are not recursive, where `ā` are the parameters
themselves.
A field whose type is an instance of a type of the block is recursive: its type is this type at the
instance of the block, at its level variables and at the parameters themselves, and no field after
it depends on it, so that it does not extend the context.
A field whose nesting is that of an instance is nested: its type is a type `A₀` at the types of the
block, at the instance of the block, at its level variables and at the parameters themselves, in
place of type variables `X̄ : κ`, one for each type of the block, in which `A₀` is strictly positive;
`κ` is a universe, and no field after it depends on it.
The type of a field that is neither recursive nor nested has a nesting without position, and lives in a sort that
`κ` bounds, with a grade without use at run time if it is a proposition, in the signature `Σ`, which
the block does not extend, so that no type of the block occurs in it.
The RFC writes the parameters themselves as the variables `x̄_Δ`, the same under every field; the
Lean carries them as the arguments `ā` of the parameters in the scope of the fields, the identity
renamed under the fields before, since de Bruijn indices shift under each field.
-/
abbrev WfFields (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
    {Γ : Scope} (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
    {ps : List Parameter} (Θ : Telescope decl.levels Γ ps) (κ : Universe decl.levels) : Prop :=
  Derivable (.wfFields sig decl ι as ctx Θ κ)

-- ADE: none.
/--
`Σ; Γ ⊢_{𝒟; Π} d̄ : κ`: the destructors `d̄` of a codata type of the block `decl`, at the instance
`ι` of its sort and grade variables, live in the sort `κ = s_l`, in the context `Γ` of the
parameters extended by the destructors before them that are not recursive and whose results have no
position, where `ā` are the parameters themselves and `ν` gives the nestings of the variables,
those of the parameters `Π` in which the type is strictly positive: the arguments of each
destructor live in the universe `U_l`, and each destructor that is not recursive and whose result
has no position is a second-order variable of the context of the destructors after it.
The result of a destructor has a position when a parameter of `Π` occurs in it, below instances of
declared types: no destructor after it depends on it, so that it does not extend the context.
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
abbrev WfDestructors (sig : Signature) (decl : TypeDeclaration) (ι : Instance decl.sorts decl.grades)
    {Γ : Scope} {ns : List Name} (ν : Nesting Nat Γ)
    (as : InstanceArgs decl.levels Γ decl.scope) (ctx : Context decl.levels Γ)
    (ds : Destructors decl.levels Γ ns) (κ : Universe decl.levels) : Prop :=
  Derivable (.wfDestructors sig decl ι ν as ctx ds κ)

-- ADE: none.
/--
`Σ ⊢ 𝒟`: the type declaration is well formed.
No entry of the signature introduces the name of one of its types, so that an instance of a type of
this name is an instance of the block.
A block of data types is well formed when its constraint `C` admits an instance of the sort and grade
variables and, for each instance it admits, the parameters `Δ` form a context and the fields of each
constructor live in the sort `κ` and are strictly positive in each parameter in which their type
declares that it is; the constructors of each type have distinct names.
The fields may be recursive, as the judgment of the fields allows.
A block of codata types likewise, with the destructors of each type in place of its constructors,
which may be recursive, as the judgment of the destructors allows.
The strict positivity reads the parameters that the types of the block itself declare, for its
recursive fields and destructors, and those that the codata types of the signature without recursive
destructor declare.
-/
abbrev WfTypeDeclaration (sig : Signature) (decl : TypeDeclaration) : Prop :=
  Derivable (.wfTypeDeclaration sig decl)

-- The rules of each judgment are in the namespace of the judgment too, so that `HasType.conv` and
-- `h.conv`, for `h : HasType sig ctx t A`, name the rule.
namespace WfSig
export Derivable.WfSig (empty constantDefinition constantDeclaration typeDeclaration lifting)
end WfSig

namespace WfConstantDefinition
export Derivable.WfConstantDefinition (intro)
end WfConstantDefinition

namespace WfConstantDeclaration
export Derivable.WfConstantDeclaration (intro)
end WfConstantDeclaration

namespace WfCtx
export Derivable.WfCtx (empty var secondOrder)
end WfCtx

namespace WfType
export Derivable.WfType (univType propType)
end WfType

namespace EqType
export Derivable.EqType (refl symm trans univType propType)
end EqType

namespace HasType
export Derivable.HasType (var secondOrder const univ prop inst equality reflProof transp propExt
    coind ctor recursor obs corec conv)
end HasType

namespace EqTerm
export Derivable.EqTerm (refl symm trans conv irr secondOrder delta const univ prop inst equality
    transp transpSame ctor recursor obs corec iota etaCtor beta etaObs)
end EqTerm

namespace HasArgs
export Derivable.HasArgs (nil cons)
end HasArgs

namespace EqArgs
export Derivable.EqArgs (nil cons)
end EqArgs

namespace HasInstanceArgs
export Derivable.HasInstanceArgs (nil var secondOrder)
end HasInstanceArgs

namespace EqInstanceArgs
export Derivable.EqInstanceArgs (nil var secondOrder)
end EqInstanceArgs

namespace WfTelescope
export Derivable.WfTelescope (nil cons)
end WfTelescope

namespace WfTelescopeSorts
export Derivable.WfTelescopeSorts (nil cons)
end WfTelescopeSorts

namespace EqTelescope
export Derivable.EqTelescope (nil cons)
end EqTelescope

namespace WfFields
export Derivable.WfFields (nil cons recursive nested)
end WfFields

namespace WfDestructors
export Derivable.WfDestructors (nil cons nested recursive)
end WfDestructors

namespace WfTypeDeclaration
export Derivable.WfTypeDeclaration (data codata)
end WfTypeDeclaration

-- The rules are in the namespace `Derivable` under their short names too, so that `.conv` names the
-- rule where the expected type is a judgment unfolded to `Derivable`.
namespace Derivable
export Derivable.WfSig (empty constantDefinition constantDeclaration typeDeclaration lifting)
export Derivable.WfConstantDefinition (intro)
export Derivable.WfConstantDeclaration (intro)
export Derivable.WfCtx (empty var secondOrder)
export Derivable.WfType (univType propType)
export Derivable.EqType (refl symm trans univType propType)
export Derivable.HasType (var secondOrder const univ prop inst equality reflProof transp propExt
    coind ctor recursor obs corec conv)
export Derivable.EqTerm (refl symm trans conv irr secondOrder delta const univ prop inst equality
    transp transpSame ctor recursor obs corec iota etaCtor beta etaObs)
export Derivable.HasArgs (nil cons)
export Derivable.EqArgs (nil cons)
export Derivable.HasInstanceArgs (nil var secondOrder)
export Derivable.EqInstanceArgs (nil var secondOrder)
export Derivable.WfTelescope (nil cons)
export Derivable.WfTelescopeSorts (nil cons)
export Derivable.EqTelescope (nil cons)
export Derivable.WfFields (nil cons recursive nested)
export Derivable.WfDestructors (nil cons nested recursive)
export Derivable.WfTypeDeclaration (data codata)
end Derivable

-- The goals, the hovers and the documentation show a derivation of a form as its judgment,
-- `HasType sig ctx t A` rather than `Derivable (Judgment.hasType sig ctx t A)`: the proofs unfold the
-- abbreviations wherever they read the rules, so that only this unexpander keeps the judgments in
-- what is shown. It names the abbreviation of each form by a table rather than by capitalizing the
-- name of the form, whose functions on strings depend on `Classical.choice`.
/-- Shows the derivation of a form of judgment as the judgment. -/
@[app_unexpander Derivable] meta def Derivable.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $j) => do
    let `($f:ident $xs*) := j | throw ()
    let .str p c := f.getId | throw ()
    let g : String ← match c with
      | "wfSig" => pure "WfSig"
      | "wfConstantDefinition" => pure "WfConstantDefinition"
      | "wfConstantDeclaration" => pure "WfConstantDeclaration"
      | "wfCtx" => pure "WfCtx"
      | "wfType" => pure "WfType"
      | "eqType" => pure "EqType"
      | "hasType" => pure "HasType"
      | "eqTerm" => pure "EqTerm"
      | "hasArgs" => pure "HasArgs"
      | "eqArgs" => pure "EqArgs"
      | "hasInstanceArgs" => pure "HasInstanceArgs"
      | "eqInstanceArgs" => pure "EqInstanceArgs"
      | "wfTelescope" => pure "WfTelescope"
      | "wfTelescopeSorts" => pure "WfTelescopeSorts"
      | "eqTelescope" => pure "EqTelescope"
      | "wfFields" => pure "WfFields"
      | "wfDestructors" => pure "WfDestructors"
      | "wfTypeDeclaration" => pure "WfTypeDeclaration"
      | _ => throw ()
    let n ← match p with
      | .anonymous => pure (Lean.Name.mkSimple g)
      | .str q "Judgment" => pure (Lean.Name.str q g)
      | _ => throw ()
    `($(Lean.mkIdent n) $xs*)
  | _ => throw ()

end Sic.Core
