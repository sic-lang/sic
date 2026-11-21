module

public import Sic.Core.Typing
import Sic.Core.Results.Substitution

/-!
# Lifted Substitutions of the Typing

The judgments of typing and of equality of annex 15 of RFC 36 are stable under the substitutions of
the second order that a family of typed substitutions gives and that the rules lift under their
binders: a judgment in a context, substituted, holds in the context of the substitution.
The renamings and the substitutions of the first order are two such families, whose stability
follows from this one, so that the proof by cases on the rules is written once.

A family gives the context of each of its substitutions well formed, the image of each second-order
variable, at arguments of its telescope, substituted, a term of its type, substituted, at these
arguments, equal at equal arguments, and the image of each variable a term of its type, substituted,
in the context lifted when it is well formed.
A family whose substitutions give each second-order variable a variable declared with its telescope
and its type, substituted, is one, by the rules `(var_X)` and `(var_X≡)`.
The proof is by induction on the derivations of all the judgments, `Derivable.substStable`.
Under the binders of a rule, the substitution is lifted, and the context extended by the type
substituted is well formed: the relation `Subst.Lifted` lifts a substitution under variables without
this condition, and the clause of the judgment `Σ ⊢ Γ` builds the context extended at the leaves of
the derivation, from the derivation of the context extended, which the rule `(ctx_x)` gives with a
derivation of its type, a subderivation substituted by the substitution before the lift.

ADE prove the weakening and the substitution apart, each by cases on the rules, and build the
context extended from the derivation of the type, which the rules of a binder do not always have, by
a well-founded recursion on the sizes of the derivations; here the induction is structural.
-/

@[expose] public section

namespace Sic.Core

variable {sig : Signature} {k : Nat}

-- ADE: `_∷_⊇_`, in `Definition/Typed/Weakening.agda`, whose constructor `lift` it has.
/-- A substitution `θ` of the family `Base`, lifted under variables, whose contexts are extended by
a type and by the type substituted, without the condition that the context extended be well formed,
which the leaves of a derivation in the context extended give.
The substitution is lifted as the substitutions of the rules are, so that the judgments under the
binders of a rule hold at the substitution of the rule without conversion. -/
inductive Subst.Lifted (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) :
    {Γ Δ : Scope} → Context k Γ → Subst k Γ Δ → Context k Δ → Prop where
  /-- A substitution of the family. -/
  | base {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      (h : Base ctx' @θ ctx) : Lifted @Base ctx' @θ ctx
  /-- A lifted substitution, lifted under a variable. -/
  | var {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      (A : Term k Δ) (h : Lifted @Base ctx' @θ ctx) :
      Lifted @Base (ctx'.var (A.subst θ)) (Subst.lift θ) (ctx.var A)

-- ADE: none.
/-- What a family `Base` of substitutions gives for the typing to be stable under them. -/
structure Subst.Liftable (sig : Signature)
    (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) : Prop where
  /-- The context of a substitution of the family is well formed. -/
  wfCtx : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ},
    Base ctx' @θ ctx → WfCtx sig ctx'
  /-- The image of a second-order variable by a lifted substitution, at arguments of its telescope,
  substituted, is a term of its type, substituted, at these arguments. -/
  secondOrder : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {ps : List Parameter} {ψ : ResultOwnership Grading.Grade ps.length} {X : Var Δ (.secondOrder ps ψ)}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} {ts : Args k Γ ps},
    Subst.Lifted @Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A → HasArgs sig ctx' ts (Θ.subst θ) →
      HasType sig ctx' ((θ X).instantiate ts) ((A.subst (Subst.liftN _ θ)).instantiate ts)
  /-- The images of a second-order variable by a lifted substitution, at equal arguments of its
  telescope, substituted, are equal at its type, substituted, at the first arguments. -/
  eqSecondOrder : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {ps : List Parameter} {ψ : ResultOwnership Grading.Grade ps.length} {X : Var Δ (.secondOrder ps ψ)}
    {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} {ts us : Args k Γ ps},
    Subst.Lifted @Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A → EqArgs sig ctx' ts us (Θ.subst θ) →
      EqTerm sig ctx' ((θ X).instantiate ts) ((θ X).instantiate us)
        ((A.subst (Subst.liftN _ θ)).instantiate ts)
  /-- The image of a variable by a lifted substitution is a term of its type, substituted, when the
  context of the substitution is well formed. -/
  varIn : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {x : Var Δ .var} {A : Term k Δ},
    Subst.Lifted @Base ctx' @θ ctx → ctx.VarIn x A → WfCtx sig ctx' →
      HasType sig ctx' ((Term.var₀ x).subst θ) (A.subst θ)

variable {Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop}

/-- A lifted substitution, lifted under the variables of a telescope. -/
theorem Subst.Lifted.append {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} :
    {ps : List Parameter} → (Θ : Telescope k Δ ps) → Lifted @Base ctx' @θ ctx →
      Lifted @Base (ctx'.append (Θ.subst θ)) (Subst.liftN ps.length θ) (ctx.append Θ)
  | [], .nil, h => h
  | _ :: _, .cons _ _ A Θ, h => Subst.Lifted.append Θ (h.var A)

-- ADE: none.
/-- The image of a second-order variable by a lifted substitution is the abstraction of a variable
declared with its telescope and its type, substituted, when the substitutions of the family give
such images. -/
theorem Subst.Lifted.secondOrderIn
    (hB : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      {ps : List Parameter} {ψ : ResultOwnership Grading.Grade ps.length}
      {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)},
      Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A →
        ∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ)))
    {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ps : List Parameter} {ψ : ResultOwnership Grading.Grade ps.length}
    {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)} :
    Lifted @Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A →
      ∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ))
  | .base h, hX => hB h hX
  | .var B h, .succVar hX => by
    obtain ⟨Y, hY, hYin⟩ := Subst.Lifted.secondOrderIn hB h hX
    refine ⟨Y.succ, ?_, ?_⟩
    · show Term.rename _ _ = _
      dsimp only
      rw [hY]
      exact Var.eta_rename Ren.weaken Y
    · rw [Telescope.subst_lift_rename_weaken, Term.subst_liftN_lift_rename_weaken]
      exact .succVar hYin

-- ADE: none.
/-- A family gives what the stability of the typing asks when the image of each second-order
variable by its substitutions is the abstraction of a variable declared with its telescope and its
type, substituted: the rules `(var_X)` and `(var_X≡)` type the image at arguments. -/
theorem Subst.Liftable.ofSecondOrderIn
    (wfCtx : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ},
      Base ctx' @θ ctx → WfCtx sig ctx')
    (secondOrderIn : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      {ps : List Parameter} {ψ : ResultOwnership Grading.Grade ps.length}
      {X : Var Δ (.secondOrder ps ψ)} {Θ : Telescope k Δ ps} {A : Term k (Δ.extend ps.length)},
      Base ctx' @θ ctx → ctx.SecondOrderIn X Θ A →
        ∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ)))
    (varIn : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
      {x : Var Δ .var} {A : Term k Δ},
      Subst.Lifted @Base ctx' @θ ctx → ctx.VarIn x A → WfCtx sig ctx' →
        HasType sig ctx' ((Term.var₀ x).subst θ) (A.subst θ)) :
    Subst.Liftable sig @Base where
  wfCtx := wfCtx
  secondOrder := fun hθ hX hts => by
    obtain ⟨Y, hY, hYin⟩ := hθ.secondOrderIn secondOrderIn hX
    rw [hY, Var.eta_instantiate]
    exact .secondOrder hYin hts
  eqSecondOrder := fun hθ hX hts => by
    obtain ⟨Y, hY, hYin⟩ := hθ.secondOrderIn secondOrderIn hX
    rw [hY, Var.eta_instantiate, Var.eta_instantiate]
    exact .secondOrder hYin hts
  varIn := varIn

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`, and `subst-⊢`,
-- `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the lifted substitutions of a family. -/
structure Subst.Stable (sig : Signature)
    (Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop) : Prop where
  /-- A type, substituted, is a type. -/
  wfType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {A : Term k Δ},
    WfType sig ctx A → Lifted @Base ctx' @θ ctx → WfType sig ctx' (A.subst θ)
  /-- Equal types, substituted, are equal. -/
  eqType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {A B : Term k Δ},
    EqType sig ctx A B → Lifted @Base ctx' @θ ctx → EqType sig ctx' (A.subst θ) (B.subst θ)
  /-- A term of a type, substituted, is a term of the type, substituted. -/
  hasType : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {t A : Term k Δ},
    HasType sig ctx t A → Lifted @Base ctx' @θ ctx → HasType sig ctx' (t.subst θ) (A.subst θ)
  /-- Equal terms of a type, substituted, are equal at the type, substituted. -/
  eqTerm : ∀ {Γ Δ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {t u A : Term k Δ},
    EqTerm sig ctx t u A → Lifted @Base ctx' @θ ctx →
      EqTerm sig ctx' (t.subst θ) (u.subst θ) (A.subst θ)
  /-- Arguments of a telescope, substituted, are arguments of the telescope, substituted. -/
  hasArgs : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ts : Args k Δ ps} {Θ : Telescope k Δ ps},
    HasArgs sig ctx ts Θ → Lifted @Base ctx' @θ ctx → HasArgs sig ctx' (ts.subst θ) (Θ.subst θ)
  /-- Equal arguments of a telescope, substituted, are equal arguments of the telescope,
  substituted. -/
  eqArgs : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {ts us : Args k Δ ps} {Θ : Telescope k Δ ps},
    EqArgs sig ctx ts us Θ → Lifted @Base ctx' @θ ctx →
      EqArgs sig ctx' (ts.subst θ) (us.subst θ) (Θ.subst θ)
  /-- Arguments of an instance, substituted, are arguments of its parameters. -/
  hasInstanceArgs : ∀ {Γ Δ Ψ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {as : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    HasInstanceArgs sig ctx as params → Lifted @Base ctx' @θ ctx →
      HasInstanceArgs sig ctx' (as.subst θ) params
  /-- Equal arguments of instances, substituted, are equal arguments of the parameters. -/
  eqInstanceArgs : ∀ {Γ Δ Ψ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ}
    {as₁ as₂ : InstanceArgs k Δ Ψ} {params : Context k Ψ},
    EqInstanceArgs sig ctx as₁ as₂ params → Lifted @Base ctx' @θ ctx →
      EqInstanceArgs sig ctx' (as₁.subst θ) (as₂.subst θ) params
  /-- A telescope in a sort, substituted, is in the sort. -/
  wfTelescope : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κ : Universe k},
    WfTelescope sig ctx Θ κ → Lifted @Base ctx' @θ ctx → WfTelescope sig ctx' (Θ.subst θ) κ
  /-- A telescope in sorts, substituted, is in the sorts. -/
  wfTelescopeSorts : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
    {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κs : List (Universe k)}
    {l : Level k}, WfTelescopeSorts sig ctx Θ κs l → Lifted @Base ctx' @θ ctx →
      WfTelescopeSorts sig ctx' (Θ.subst θ) κs l
  /-- Equal telescopes in a sort, substituted, are equal in the sort. -/
  eqTelescope : ∀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ} {θ : Subst k Γ Δ}
    {ctx : Context k Δ} {Θ₁ Θ₂ : Telescope k Δ ps} {κ : Universe k},
    EqTelescope sig ctx Θ₁ Θ₂ κ → Lifted @Base ctx' @θ ctx →
      EqTelescope sig ctx' (Θ₁.subst θ) (Θ₂.subst θ) κ

-- ADE: none.
/-- A family of substitutions of a level context, as `Subst.Lifted` takes it. -/
abbrev Subst.Family (k : Nat) : Type :=
  ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop

-- ADE: none.
/-- What the stability of a judgment under the lifted substitutions of a family says. -/
def Judgment.SubstStable : Judgment → Prop
  | @Judgment.wfCtx sig k Δ ctx => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        WfCtx sig ctx'
  | @Judgment.wfType sig k Δ ctx A => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        WfType sig ctx' (A.subst θ)
  | @Judgment.eqType sig k Δ ctx A B => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        EqType sig ctx' (A.subst θ) (B.subst θ)
  | @Judgment.hasType sig k Δ ctx t A => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        HasType sig ctx' (t.subst θ) (A.subst θ)
  | @Judgment.eqTerm sig k Δ ctx t u A => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        EqTerm sig ctx' (t.subst θ) (u.subst θ) (A.subst θ)
  | @Judgment.hasArgs sig k Δ _ ctx ts Θ => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        HasArgs sig ctx' (ts.subst θ) (Θ.subst θ)
  | @Judgment.eqArgs sig k Δ _ ctx ts us Θ => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        EqArgs sig ctx' (ts.subst θ) (us.subst θ) (Θ.subst θ)
  | @Judgment.hasInstanceArgs sig k Δ _ ctx as params => ∀ (Base : Subst.Family k),
      Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        HasInstanceArgs sig ctx' (as.subst θ) params
  | @Judgment.eqInstanceArgs sig k Δ _ ctx as₁ as₂ params => ∀ (Base : Subst.Family k),
      Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        EqInstanceArgs sig ctx' (as₁.subst θ) (as₂.subst θ) params
  | @Judgment.wfTelescope sig k Δ _ ctx Θ κ => ∀ (Base : Subst.Family k), Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        WfTelescope sig ctx' (Θ.subst θ) κ
  | @Judgment.wfTelescopeSorts sig k Δ _ ctx Θ κs l => ∀ (Base : Subst.Family k),
      Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        WfTelescopeSorts sig ctx' (Θ.subst θ) κs l
  | @Judgment.eqTelescope sig k Δ _ ctx Θ₁ Θ₂ κ => ∀ (Base : Subst.Family k),
      Subst.Liftable sig @Base →
      ∀ {Γ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Δ}, Subst.Lifted @Base ctx' @θ ctx →
        EqTelescope sig ctx' (Θ₁.subst θ) (Θ₂.subst θ) κ
  | _ => True

-- ADE: none.
/-- The judgments in a context are stable under the lifted substitutions of a family that gives what
`Subst.Liftable` says, by induction on their derivations. -/
theorem Derivable.substStable {J : Judgment} (h : Derivable J) : J.SubstStable := by
  induction h with
  | WfCtx.empty h _ =>
    intro Base hL Γ ctx' θ hθ
    cases hθ with
    | base hθ => exact hL.wfCtx hθ
  | WfCtx.var h h_ih =>
    intro Base hL Γ ctx' θ hθ
    cases hθ with
    | base hθ => exact hL.wfCtx hθ
    | var _ hθ => exact .var (h_ih Base hL hθ)
  | WfCtx.secondOrder h _ =>
    intro Base hL Γ ctx' θ hθ
    cases hθ with
    | base hθ => exact hL.wfCtx hθ
  | WfType.univType h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .univType (h_ih Base hL hθ)
  | WfType.propType h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .propType (h_ih Base hL hθ)
  | EqType.refl h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .refl (h_ih Base hL hθ)
  | EqType.symm h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .symm (h_ih Base hL hθ)
  | EqType.trans h₁ h₂ h₁_ih h₂_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .trans (h₁_ih Base hL hθ) (h₂_ih Base hL hθ)
  | EqType.univType h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .univType (h_ih Base hL hθ)
  | EqType.propType h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .propType (h_ih Base hL hθ)
  | HasType.var hctx hx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact hL.varIn hθ hx (hctx_ih Base hL hθ)
  | HasType.secondOrder hX hts hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Term.subst, Term.instantiate_subst]
    exact hL.secondOrder hθ hX (hts_ih Base hL hθ)
  | HasType.const hctx h hq hl hp hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Signature.instanceType, Term.weakenClosed_subst]
    exact .const (hctx_ih Base hL hθ) h hq hl hp
  | HasType.univ hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .univ (hctx_ih Base hL hθ)
  | HasType.prop hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .prop (hctx_ih Base hL hθ)
  | HasType.inst h hq hl hp hadm has has_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .inst h hq hl hp hadm (has_ih Base hL hθ)
  | HasType.equality hA ht hu hA_ih ht_ih hu_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .equality (hA_ih Base hL hθ) (ht_ih Base hL hθ) (hu_ih Base hL hθ)
  | HasType.reflProof hA ht hA_ih ht_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .reflProof (hA_ih Base hL hθ) (ht_ih Base hL hθ)
  | HasType.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t₁ t₂ _ _ _
    have hu' := hu_ih Base hL hθ
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₁ θ)] at hu'
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₂ θ)]
    exact .transp (hA_ih Base hL hθ) (ht₁_ih Base hL hθ) (ht₂_ih Base hL hθ) (hC_ih Base hL (hθ.var _))
      (ht_ih Base hL hθ) hu'
  | HasType.propExt hA hB ht hu hA_ih hB_ih ht_ih hu_ih =>
    intro Base hL Γ ctx' θ hθ
    have ht' := ht_ih Base hL (hθ.var _)
    have hu' := hu_ih Base hL (hθ.var _)
    rw [Term.subst_lift_rename_weaken] at ht' hu'
    exact .propExt (hA_ih Base hL hθ) (hB_ih Base hL hθ) ht' hu'
  | HasType.coind h hq hl hp hadm has hh hA hAl hAt ht₁ ht₂ ht hgl hgs hΘ hB hBt hgt hgr has_ih
      hAt_ih ht₁_ih ht₂_ih ht_ih hBt_ih hgt_ih hgr_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i sig k Δ _ decl _ _ qs ls ps as l' t₁ t₂ _ As gs _ A κs
    let p₀ : Parameter := ⟨Grading.Grade.one, Grading.Grade.one⟩
    -- The observations of the variables of a branch, substituted under them.
    have hc : ∀ (X : Var (Δ.extend 3) .var) (Y : Var (Γ.extend 3) .var),
        (Term.var₀ X).subst (Subst.liftN 3 θ) = Term.var₀ Y →
        ∀ {T' : CodataType decl.sorts decl.grades decl.levels
        decl.scope} {d : Name} {p q ς : Grading.Grade} {ps₁ : List Parameter} {Ξ : Scope}
        {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
        {ψ : ResultOwnership Grading.Grade ps₁.length}
        (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) {a'} (v : Var Ξ a'),
        ((hd.obsSubst ((Term.var₀ X).observation T'.name qs ls ps (as.rename (Ren.weakenN 3)))
          (as.rename (Ren.weakenN 3)).toSubst) v).subst (Subst.liftN a'.params.length
            (Subst.liftN 3 θ)) =
        hd.obsSubst ((Term.var₀ Y).observation T'.name qs ls ps
          ((as.subst θ).rename (Ren.weakenN 3)))
          ((as.subst θ).rename (Ren.weakenN 3)).toSubst v :=
      fun X Y hX {T' _ _ _ _ _ _ _ _ _} hd {_} v =>
      hd.obsSubst_subst _
        (o := (Term.var₀ X).observation T'.name qs ls ps (as.rename (Ren.weakenN 3)))
        (o' := (Term.var₀ Y).observation T'.name qs ls ps
          ((as.subst θ).rename (Ren.weakenN 3)))
        (fun d ps' => by
          rw [Term.observation_subst, InstanceArgs.subst_liftN_rename_weakenN, hX])
        (θ' := ((as.subst θ).rename (Ren.weakenN 3)).toSubst)
        (fun v => by rw [InstanceArgs.toSubst_subst, InstanceArgs.subst_liftN_rename_weakenN]) v
    -- A term over two variables renamed under them commutes with a substitution lifted.
    have hcomm : ∀ (m : Nat) {Δ Ψ : Scope} (σ' : Subst k Δ Ψ) (t' : Term k (Ψ.extend 2)),
        (t'.rename (Ren.liftN 2 (Ren.weakenN m))).subst (Subst.liftN 2 (Subst.liftN m σ')) =
          (t'.subst (Subst.liftN 2 σ')).rename (Ren.liftN 2 (Ren.weakenN m)) := fun m _ _ σ' t' =>
      (Term.subst_rename_of (Subst.liftN_rename_comm_of 2 (θ₂ := σ')
        (fun x => Subst.liftN_weakenN m σ' x)) t').trans
        (Term.rename_subst_of (fun _ => rfl) t').symm
    rw [Term.subst]
    refine .coind (l' := l') (κs := κs) h hq hl hp hadm (has_ih Base hL hθ) hh
      (Terms.get_subst _ hA)
      ((Terms.length_subst _ As).trans hAl) ?_ (ht₁_ih Base hL hθ) (ht₂_ih Base hL hθ) ?_
      ((DestructorBranches.length_subst _ gs).trans hgl) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j T' A' hj hA'
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_subst_inv _ hA'
      have ih := (hAt_ih j T' A₀ hj hA₀ Base hL)  ((hθ.var _).var _)
      rw [Term.subst_lift_rename_weaken] at ih
      exact ih
    · have ih := ht_ih Base hL hθ
      rw [show ((A.subst₀ (Subst₀.liftN 1 (Subst₀.single t₁))).subst₀ (Subst₀.single t₂)) =
          A.instantiate (Args.cons (p := p₀) t₁ (Args.cons (p := p₀) t₂ .nil)) from rfl,
        Term.instantiate_subst] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      obtain ⟨g, hg⟩ := hgs i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      exact ⟨_, DestructorBranches.get_subst _ hg⟩
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      have e := congrArg (Telescope.subst (Subst.liftN 3 θ))
        (hΘ i j T' d p q ς ps₁ Ξ Θ B ψ hi hd)
      rw [Telescope.subst_subst_of (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd),
        Telescope.subst_subst_of (hc (.succ .zero) (.succ .zero) rfl hd)] at e
      exact e
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ hi hd
      have e := congrArg (Term.subst (Subst.liftN ps₁.length (Subst.liftN 3 θ)))
        (hB i j T' d p q ς ps₁ Ξ Θ B ψ hi hd)
      rw [Term.subst_subst_of (Subst.liftN_subst_of _ (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd)),
        Term.subst_subst_of (Subst.liftN_subst_of _ (hc (.succ .zero) (.succ .zero) rfl hd))] at e
      exact e
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hd hn
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_subst_inv _ hA'
      have ih := (hBt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ hi hA₀ hd hn Base hL)
        ((((hθ.var _).var _).var _).append _)
      erw [Term.subst_lift_rename_weaken, Telescope.subst_subst_of (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd),
        Term.subst_subst_of (Subst.liftN_subst_of _ (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd))] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hd hn hg
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_subst_inv _ hA'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_subst_inv _ hg
      have ih := (hgt_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ g₀ hi hA₀ hd hn hg₀ Base hL)
        ((((hθ.var _).var _).var _).append _)
      erw [Term.subst_lift_rename_weaken, Telescope.subst_subst_of (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd)] at ih
      simp only [Term.subst] at ih
      erw [Term.subst_subst_of (Subst.liftN_subst_of _ (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd)),
        Term.observation_subst, Term.observation_subst,
        InstanceArgs.subst_liftN_rename_weakenN 3 θ as] at ih
      exact ih
    · intro i j T' d p q ς ps₁ Ξ Θ B ψ A' D' j' A'' g hi hA' hd hn hj' hA'' hg
      obtain ⟨A₀, hA₀, rfl⟩ := Terms.get_subst_inv _ hA'
      obtain ⟨A₀', hA₀', rfl⟩ := Terms.get_subst_inv _ hA''
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_subst_inv _ hg
      have ih := (hgr_ih i j T' d p q ς ps₁ Ξ Θ B ψ A₀ D' j' A₀' g₀ hi hA₀ hd hn hj' hA₀'
        hg₀ Base hL)  ((((hθ.var _).var _).var _).append _)
      replace ih : HasType sig _ _ ((((A₀'.rename (Ren.liftN 2 (Ren.weakenN 3))).rename
          (Ren.liftN 2 (Ren.weakenN ps₁.length))).instantiate
            (Args.cons (p := p₀) ((Term.var₀ (.succ (.succ .zero)) : Term k (Δ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)
            (Args.cons (p := p₀) ((Term.var₀ (.succ .zero) : Term k (Δ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3)) d ps₁) .nil))).subst
            (Subst.liftN ps₁.length (Subst.liftN 3 θ))) := ih
      erw [Term.instantiate_subst, hcomm, hcomm, Term.subst_lift_rename_weaken,
        Telescope.subst_subst_of (hc (.succ (.succ .zero)) (.succ (.succ .zero)) rfl hd)] at ih
      simp only [Args.subst] at ih
      erw [Term.observation_subst, Term.observation_subst,
        InstanceArgs.subst_liftN_rename_weakenN] at ih
      exact ih
  | HasType.ctor h hc hq hl hp hadm has hts has_ih hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Term.ctor_subst]
    refine .ctor h hc hq hl hp hadm (has_ih Base hL hθ) ?_
    rw [← Constructor.fieldsAt_subst]
    exact hts_ih Base hL hθ
  | HasType.recursor h hq hl hp hadm has ht hh hC hCl hCs hCt hul hus hRs hut hκ has_ih ht_ih hCt_ih
      hut_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t Cs us _ _ _ Rs
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t _)]
    refine .recursor (Rs := fun con => (Rs con).subst (Subst.liftN _ θ)) h hq hl hp hadm
      (has_ih Base hL hθ) (ht_ih Base hL hθ) hh
      (Motives.get_subst _ hC) ((Motives.length_subst _ Cs).trans hCl) ?_ ?_
      ((Branches.length_subst _ us).trans hul) ?_ ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_subst _ hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
      have ih := (hCt_ih j T' C₀ hj hC₀ Base hL)  (hθ.var _)
      exact ih
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_subst _ hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ h => Constructor.ResultTypes.subst h
        (Lifting.ofMotives_substitutes θ _ _ _ _ _ _ _ _)
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv _ hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv _ hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ Base hL)  ((hθ.append _).append _)
      rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst _ C₀] at ih
      exact ih
  | HasType.obs h hq hl hp hadm hd has ht hbs has_ih ht_ih hbs_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i D _ qs ls ps as t _ _ _ _ _ _ _ _ _ _
    rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
      (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst]
    refine .obs h hq hl hp hadm hd (has_ih Base hL hθ) (ht_ih Base hL hθ) ?_
    rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
    exact hbs_ih Base hL hθ
  | HasType.corec h hq hl hp hadm hpre has hh hS hss hSl hSs hSt hgl hgs hgt has_ih hss_ih hSt_ih
      hgt_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i qs ls ps as r Ss gs _ _ _ _
    rw [Term.corec_subst]
    refine .corec h hq hl hp hadm hpre (has_ih Base hL hθ) hh (States.get_subst _ hS)
      (hss_ih Base hL hθ) ((States.length_subst _ Ss).trans hSl) ?_ ?_
      ((DestructorBranches.length_subst _ gs).trans hgl) ?_ ?_
    · intro j T' hj
      obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
      exact ⟨ps'', _, States.get_subst _ hS'⟩
    · intro j T' ps'' S' hj hS'
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
      rw [States.sorts_subst]
      exact (hSt_ih j T' ps'' S₀ hj hS₀ Base hL)  hθ
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, DestructorBranches.get_subst _ hg⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_subst_inv _ hg
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ Base hL)
        ((hθ.append S₀).append _)
      dsimp only [Scope.extend] at ih
      rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
        States.subst_liftN_rename_weakenN] at ih
      rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
        Term.subst_subst_of (Subst.liftN_subst_of _
          (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
      exact ih
  | HasType.conv ht h ht_ih h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .conv (ht_ih Base hL hθ) (h_ih Base hL hθ)
  | EqTerm.refl h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .refl (h_ih Base hL hθ)
  | EqTerm.symm h h_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .symm (h_ih Base hL hθ)
  | EqTerm.trans h₁ h₂ h₁_ih h₂_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .trans (h₁_ih Base hL hθ) (h₂_ih Base hL hθ)
  | EqTerm.conv h hA h_ih hA_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .conv (h_ih Base hL hθ) (hA_ih Base hL hθ)
  | EqTerm.irr ht hu hA ht_ih hu_ih hA_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .irr (ht_ih Base hL hθ) (hu_ih Base hL hθ) (hA_ih Base hL hθ)
  | EqTerm.secondOrder hX hts hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Term.subst, Term.subst, Term.instantiate_subst]
    exact hL.eqSecondOrder hθ hX (hts_ih Base hL hθ)
  | EqTerm.delta hctx h hq hl hp hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Signature.instanceType, Signature.instanceType, Term.weakenClosed_subst,
      Term.weakenClosed_subst]
    exact .delta (hctx_ih Base hL hθ) h hq hl hp
  | EqTerm.const hctx h hq hl₁ hl₂ hp hls hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Signature.instanceType, Term.weakenClosed_subst]
    exact .const (hctx_ih Base hL hθ) h hq hl₁ hl₂ hp hls
  | EqTerm.univ hctx hl hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .univ (hctx_ih Base hL hθ) hl
  | EqTerm.prop hctx hl hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .prop (hctx_ih Base hL hθ) hl
  | EqTerm.inst h hq hl₁ hl₂ hp hadm has hls has_ih =>
    intro Base hL Γ ctx' θ hθ
    exact
    .inst h hq hl₁ hl₂ hp hadm (has_ih Base hL hθ) hls
  | EqTerm.equality hA ht hu hl hA_ih ht_ih hu_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .equality (hA_ih Base hL hθ) (ht_ih Base hL hθ) (hu_ih Base hL hθ) hl
  | EqTerm.transp hA ht₁ ht₂ hC ht hu hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t₁ _ t₂ _ _ _ _ _ _ _
    have hu' := hu_ih Base hL hθ
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₁ θ)] at hu'
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₂ θ)]
    exact .transp (hA_ih Base hL hθ) (ht₁_ih Base hL hθ) (ht₂_ih Base hL hθ) (hC_ih Base hL (hθ.var _))
      (ht_ih Base hL hθ) hu'
  | EqTerm.transpSame hA ht₁ ht₂ hC ht hu hCC hA_ih ht₁_ih ht₂_ih hC_ih ht_ih hu_ih hCC_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t₁ t₂ _ _ _
    have hu' := hu_ih Base hL hθ
    have hCC' := hCC_ih Base hL hθ
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₁ θ)] at hu' hCC'
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t₂ θ)] at hCC' ⊢
    exact .transpSame (hA_ih Base hL hθ) (ht₁_ih Base hL hθ) (ht₂_ih Base hL hθ) (hC_ih Base hL (hθ.var _))
      (ht_ih Base hL hθ) hu' hCC'
  | EqTerm.ctor h hc hq hl₁ hl₂ hp hadm has hls hts has_ih hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rw [Term.ctor_subst, Term.ctor_subst]
    refine .ctor h hc hq hl₁ hl₂ hp hadm (has_ih Base hL hθ) hls ?_
    rw [← Constructor.fieldsAt_subst]
    exact hts_ih Base hL hθ
  | EqTerm.recursor h hq hl₁ hl₂ hp hadm has hls ht hh hC hCl₁ hCl₂ hCs₁ hCs₂ hCt hul₁ hul₂ hus₁
      hus₂ hes hRs₁ hRs₂ hut hκ has_ih ht_ih hCt_ih hut_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t _ Cs₁ Cs₂ us₁ us₂ _ _ _ Rs₁ Rs₂
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
    refine .recursor (Rs₁ := fun con => (Rs₁ con).subst (Subst.liftN _ θ))
      (Rs₂ := fun con => (Rs₂ con).subst (Subst.liftN _ θ)) h hq hl₁ hl₂ hp hadm (has_ih Base hL hθ) hls (ht_ih Base hL hθ) hh
      (Motives.get_subst θ hC) ((Motives.length_subst θ Cs₁).trans hCl₁)
      ((Motives.length_subst θ Cs₂).trans hCl₂) ?_ ?_ ?_ ((Branches.length_subst θ us₁).trans hul₁)
      ((Branches.length_subst θ us₂).trans hul₂) ?_ ?_
      (by funext i; rw [Branches.grades_subst, Branches.grades_subst, hes]) ?_ ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs₁ j T' hj
      exact ⟨_, Motives.get_subst θ hC'⟩
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs₂ j T' hj
      exact ⟨_, Motives.get_subst θ hC'⟩
    · intro j T' C₁' C₂' hj h₁ h₂
      obtain ⟨C₁₀, hC₁₀, rfl⟩ := Motives.get_subst_inv θ h₁
      obtain ⟨C₂₀, hC₂₀, rfl⟩ := Motives.get_subst_inv θ h₂
      have ih := (hCt_ih j T' C₁₀ C₂₀ hj hC₁₀ hC₂₀ Base hL)  (hθ.var _)
      exact ih
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus₁ i j T' con hi
      exact ⟨_, Branches.get_subst θ hu⟩
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus₂ i j T' con hi
      exact ⟨_, Branches.get_subst θ hu⟩
    · intro i j T' con hi
      exact (hRs₁ i j T' con hi).imp fun _ h => Constructor.ResultTypes.subst h
        (Lifting.ofMotives_substitutes θ _ _ _ _ _ _ _ _)
    · intro i j T' con hi
      exact (hRs₂ i j T' con hi).imp fun _ h => Constructor.ResultTypes.subst h
        (Lifting.ofMotives_substitutes θ _ _ _ _ _ _ _ _)
    · intro i j T' con C' u₁ u₂ hi hC' hu₁ hu₂
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
      obtain ⟨u₁₀, hu₁₀, rfl⟩ := Branches.get_subst_inv θ hu₁
      obtain ⟨u₂₀, hu₂₀, rfl⟩ := Branches.get_subst_inv θ hu₂
      have ih := (hut_ih i j T' con C₀ u₁₀ u₂₀ hi hC₀ hu₁₀ hu₂₀ Base hL)
        ((hθ.append _).append _)
      rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
      exact ih
  | EqTerm.obs h hq hl₁ hl₂ hp hadm hd has hls ht hbs has_ih ht_ih hbs_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i D _ qs ls _ ps as _ t _ _ _ _ _ _ _ _ _ _ _ _
    rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _
      (hd.obsSubst_observation_subst θ D qs ls ps as t)), Term.obs_subst, Term.obs_subst]
    refine .obs h hq hl₁ hl₂ hp hadm hd (has_ih Base hL hθ) hls (ht_ih Base hL hθ) ?_
    rw [← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t)]
    exact hbs_ih Base hL hθ
  | EqTerm.corec h hq hl₁ hl₂ hp hadm hpre has hls hh hS₁ hS₂ hss hSl₁ hSl₂ hSs hSk hSt hSe hgl₁
      hgl₂ hgs hgt has_ih hss_ih hSt_ih hSe_ih hgt_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i qs ls _ ps as _ r Ss₁ Ss₂ gs₁ gs₂ _ _ _ _ _ _
    rw [Term.corec_subst, Term.corec_subst]
    refine .corec h hq hl₁ hl₂ hp hadm hpre (has_ih Base hL hθ) hls hh
      (States.get_subst θ hS₁) (States.get_subst θ hS₂) (hss_ih Base hL hθ)
      ((States.length_subst θ Ss₁).trans hSl₁) ((States.length_subst θ Ss₂).trans hSl₂) ?_
      (fun j => by rw [States.sorts_subst, States.sorts_subst]; exact hSk j) ?_ ?_
      ((DestructorBranches.length_subst θ gs₁).trans hgl₁) ((DestructorBranches.length_subst θ gs₂).trans hgl₂)
      ?_ ?_
    · intro j T' hj
      obtain ⟨ps'', S₁', S₂', h₁, h₂⟩ := hSs j T' hj
      exact ⟨ps'', _, _, States.get_subst θ h₁, States.get_subst θ h₂⟩
    · intro j T' ps'' S₁' hj h₁
      obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_subst_inv θ h₁
      rw [States.sorts_subst]
      exact (hSt_ih j T' ps'' S₁₀ hj hS₁₀ Base hL)  hθ
    · intro j T' ps'' S₁' S₂' hj h₁ h₂
      obtain ⟨S₁₀, hS₁₀, rfl⟩ := States.get_subst_inv θ h₁
      obtain ⟨S₂₀, hS₂₀, rfl⟩ := States.get_subst_inv θ h₂
      rw [States.sorts_subst]
      exact (hSe_ih j T' ps'' S₁₀ S₂₀ hj hS₁₀ hS₂₀ Base hL)  hθ
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
      obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, _, DestructorBranches.get_subst θ hg₁, DestructorBranches.get_subst θ hg₂⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g₁ g₂ hi hS' hd hg₁ hg₂
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
      obtain ⟨g₁₀, hg₁₀, rfl⟩ := DestructorBranches.get_subst_inv θ hg₁
      obtain ⟨g₂₀, hg₂₀, rfl⟩ := DestructorBranches.get_subst_inv θ hg₂
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₁₀ g₂₀ hi hS₀ hd hg₁₀ hg₂₀ Base hL)
        ((hθ.append S₀).append _)
      dsimp only [Scope.extend] at ih
      rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
        States.subst_liftN_rename_weakenN] at ih
      rw [Telescope.subst_subst_of
          (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''),
        Term.subst_subst_of (Subst.liftN_subst_of _
          (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss₁ gs₁ ps''))] at ih
      exact ih
  | EqTerm.iota h hc hq hl hp hadm has hts hi hC hu hrs hCl hCs hCt hul hus hRs hut hκ has_ih hts_ih
      hCt_ih hut_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i sig _ _ _ _ _ _ con _ _ _ _ _ _ _ Cs us _ i j _ u _ _ Rs
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ θ), Term.instantiate_subst,
      Term.instantiate_subst, Args.subst_liftN_rename_weakenN]
    show EqTerm sig ctx' (.recursor _ _ _ _ _ _ _ _ (Term.subst θ (.ctor _ _ _ _ _ _ _)) _ _ _) _ _
    rw [Term.ctor_subst]
    refine .iota (Rs := fun con => (Rs con).subst (Subst.liftN _ θ)) h hc hq hl hp hadm
      (has_ih Base hL hθ) ?_ hi (Motives.get_subst θ hC) (Branches.get_subst θ hu)
      (Constructor.ResultTerms.subst_recursorAt θ hrs) ((Motives.length_subst θ Cs).trans hCl)
      ?_ ?_ ((Branches.length_subst θ us).trans hul) ?_ ?_ ?_ hκ
    · rw [← Constructor.fieldsAt_subst]
      exact hts_ih Base hL hθ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_subst θ hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
      have ih := (hCt_ih j T' C₀ hj hC₀ Base hL)  (hθ.var _)
      exact ih
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_subst θ hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ h => Constructor.ResultTypes.subst h
        (Lifting.ofMotives_substitutes θ _ _ _ _ _ _ _ _)
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ Base hL)  ((hθ.append _).append _)
      rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
      exact ih
  | EqTerm.etaCtor h hc hq hl hp hadm hr has ht he hi hC hu hCl hCs hCt hul hus hRs hut hκ has_ih
      ht_ih he_ih hCt_ih hut_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i k _ _ _ D T con qs ls ps as _ _ _ t Cs us _ i j _ e Rs
    rw [Term.subst_subst₀_of (Subst₀.Swaps.single t θ),
      Term.subst_subst₀_of (Subst₀.Swaps.single t θ)]
    have hu' := Branches.get_subst θ hu
    rw [show ((e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).subst
          (Subst.liftN 0 (Subst.liftN _ θ)) :
            Term k ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)) =
        (e.subst (Subst.lift θ)).atCtor T.name qs ls ps (as.subst θ) con.name
          (con.params (.ofLists qs ps hq hp)) from Term.atCtor_subst θ e _ _ _ _ _ _ _] at hu'
    have he' := he_ih Base hL (hθ.var (.inst D qs ls ps as))
    refine .etaCtor (Rs := fun con => (Rs con).subst (Subst.liftN _ θ)) h hc hq hl hp hadm hr
      (has_ih Base hL hθ) (ht_ih Base hL hθ) he' hi (Motives.get_subst θ hC) hu'
      ((Motives.length_subst θ Cs).trans hCl) ?_ ?_ ((Branches.length_subst θ us).trans hul) ?_
      ?_ ?_ hκ
    · intro j T' hj
      obtain ⟨C', hC'⟩ := hCs j T' hj
      exact ⟨_, Motives.get_subst θ hC'⟩
    · intro j T' C' hj hC'
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
      have ih := (hCt_ih j T' C₀ hj hC₀ Base hL)  (hθ.var _)
      exact ih
    · intro i j T' con hi
      obtain ⟨u, hu⟩ := hus i j T' con hi
      exact ⟨_, Branches.get_subst θ hu⟩
    · intro i j T' con hi
      exact (hRs i j T' con hi).imp fun _ h => Constructor.ResultTypes.subst h
        (Lifting.ofMotives_substitutes θ _ _ _ _ _ _ _ _)
    · intro i j T' con C' u hi hC' hu
      obtain ⟨C₀, hC₀, rfl⟩ := Motives.get_subst_inv θ hC'
      obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv θ hu
      have ih := (hut_ih i j T' con C₀ u₀ hi hC₀ hu₀ Base hL)  ((hθ.append _).append _)
      rw [Constructor.fieldsAt_subst, Term.subst_liftN_rename_weakenN, Term.atCtor_subst θ C₀] at ih
      exact ih
  | EqTerm.beta h hq hl hp hadm hpre has hh hS hss hi hd hg hbs hSl hSs hSt hgl hgs hgt has_ih
      hss_ih hbs_ih hSt_ih hgt_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i D _ qs ls ps as r Ss gs _ i _ _ _ d p q ς _ _ _ _ _ g _
    rw [Term.obs_subst, Term.corec_subst, Term.observed_subst, Term.instantiate_subst, Term.instantiate_subst,
      Args.subst_liftN_rename_weakenN, Term.instantiate_subst, Term.subst_subst_of
        (Subst.liftN_subst_of _ (hd.obsSubst_observation_subst θ D qs ls ps as _)),
      Term.corec_subst]
    refine .beta h hq hl hp hadm hpre (has_ih Base hL hθ) hh (States.get_subst θ hS)
      (hss_ih Base hL hθ) hi hd (DestructorBranches.get_subst θ hg) ?_
      ((States.length_subst θ Ss).trans hSl) ?_ ?_
      ((DestructorBranches.length_subst θ gs).trans hgl)
      ?_ ?_
    · dsimp only [Subst.liftN, Scope.extend]
      rw [← Term.corec_subst,
        ← Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as _)]
      exact hbs_ih Base hL hθ
    · intro j T' hj
      obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
      exact ⟨ps'', _, States.get_subst θ hS'⟩
    · intro j T' ps'' S' hj hS'
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
      rw [States.sorts_subst]
      exact (hSt_ih j T' ps'' S₀ hj hS₀ Base hL)  hθ
    · intro i j T' d ps'' S' hi hS' p q ς ps₁ Ξ Θ B ψ hd
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
      obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ς ps₁ Ξ Θ B ψ hd
      exact ⟨_, DestructorBranches.get_subst θ hg⟩
    · intro i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hi hS' hd hg
      obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv θ hS'
      obtain ⟨g₀, hg₀, rfl⟩ := DestructorBranches.get_subst_inv θ hg
      have ih := (hgt_ih i j T' d ps'' S₀ p q ς ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ Base hL)
        ((hθ.append S₀).append _)
      dsimp only [Scope.extend] at ih
      rw [Term.branchResult_subst, States.subst_liftN_rename_weakenN,
        States.subst_liftN_rename_weakenN] at ih
      rw [Telescope.subst_subst_of (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''),
        Term.subst_subst_of (Subst.liftN_subst_of _
          (hd.obsSubst_corecAt_subst θ r T'.name qs ls ps as Ss gs ps''))] at ih
      exact ih
  | EqTerm.etaObs h hq hl hp hadm hr has ht hu hobs has_ih ht_ih hu_ih hobs_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i D _ qs ls ps as t u
    refine .etaObs h hq hl hp hadm hr (has_ih Base hL hθ) (ht_ih Base hL hθ) (hu_ih Base hL hθ) ?_
    intro d p q ς ps' Ξ Θ B ψ hd
    have ih := (hobs_ih d p q ς ps' Ξ Θ B ψ hd Base hL)  (hθ.append _)
    rw [Telescope.subst_subst_of (hd.obsSubst_observation_subst θ D qs ls ps as t),
      Term.observation_subst θ D qs ls ps as t, Term.observation_subst θ D qs ls ps as u,
      Term.subst_subst_of (Subst.liftN_subst_of _
        (hd.obsSubst_observation_subst θ D qs ls ps as t))] at ih
    exact ih
  | HasArgs.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | HasArgs.cons ht hts ht_ih hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t _ _ _
    refine .cons (ht_ih Base hL hθ) ?_
    rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
    exact hts_ih Base hL hθ
  | EqArgs.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | EqArgs.cons ht hts ht_ih hts_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i t _ _ _ _ _
    refine .cons (ht_ih Base hL hθ) ?_
    rw [← Telescope.subst_subst₀_of (Subst₀.Swaps.single t _)]
    exact hts_ih Base hL hθ
  | HasInstanceArgs.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | HasInstanceArgs.var has ha has_ih ha_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i as _ _ A
    refine .var (has_ih Base hL hθ) ?_
    rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
    exact ha_ih Base hL hθ
  | HasInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i as _ _ _ _
    refine .secondOrder (has_ih Base hL hθ) ?_
    have ih := hB_ih Base hL (hθ.append _)
    rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
      Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
    exact ih
  | EqInstanceArgs.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | EqInstanceArgs.var has ha has_ih ha_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i as _ _ _ _ A
    refine .var (has_ih Base hL hθ) ?_
    rw [← Term.subst_subst_of (InstanceArgs.toSubst_subst θ as) A]
    exact ha_ih Base hL hθ
  | EqInstanceArgs.secondOrder has hB has_ih hB_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i as _ _ _ _ _ _
    refine .secondOrder (has_ih Base hL hθ) ?_
    have ih := hB_ih Base hL (hθ.append _)
    rw [Telescope.subst_subst_of (InstanceArgs.toSubst_subst θ as),
      Term.subst_subst_of (Subst.liftN_subst_of _ (InstanceArgs.toSubst_subst θ as))] at ih
    exact ih
  | WfTelescope.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | WfTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i A _ _ _
    refine .cons (hA_ih Base hL hθ) hκ ?_ hp
    exact hΘ_ih Base hL (hθ.var A)
  | WfTelescopeSorts.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | WfTelescopeSorts.cons hA hl hΘ hp hA_ih hΘ_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i A _ _ _ _
    refine .cons (hA_ih Base hL hθ) hl ?_ hp
    exact hΘ_ih Base hL (hθ.var A)
  | EqTelescope.nil hctx hctx_ih =>
    intro Base hL Γ ctx' θ hθ
    exact .nil (hctx_ih Base hL hθ)
  | EqTelescope.cons hA hκ hΘ hp hA_ih hΘ_ih =>
    intro Base hL Γ ctx' θ hθ
    rename_i A _ _ _ _ _
    refine .cons (hA_ih Base hL hθ) hκ ?_ hp
    exact hΘ_ih Base hL (hθ.var A)
  | _ => trivial

-- ADE: `wk`, `wkEq`, `wkTerm` and `wkEqTerm`, in `Definition/Typed/Weakening.agda`, and `subst-⊢`,
-- `subst-⊢≡`, `subst-⊢∷` and `subst-⊢≡∷`, in `Definition/Typed/Substitution/Primitive/Primitive.agda`.
/-- The judgments in a context are stable under the lifted substitutions of a family that gives what
`Subst.Liftable` says. -/
theorem Subst.Liftable.stable (hB : Subst.Liftable sig @Base) : Subst.Stable sig @Base :=
  ⟨fun h hθ => h.substStable _ hB hθ, fun h hθ => h.substStable _ hB hθ,
    fun h hθ => h.substStable _ hB hθ, fun h hθ => h.substStable _ hB hθ,
    fun h hθ => h.substStable _ hB hθ, fun h hθ => h.substStable _ hB hθ,
    fun h hθ => h.substStable _ hB hθ, fun h hθ => h.substStable _ hB hθ,
    fun h hθ => h.substStable _ hB hθ, fun h hθ => h.substStable _ hB hθ,
    fun h hθ => h.substStable _ hB hθ⟩

end Sic.Core
