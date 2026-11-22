module

public import Sic.Core.Typing
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Induction
import Sic.Core.Typing.Presuppositions

/-!
# Inversion

The inversion of the rules `(var_X)` and `(D)` of annex 15 of RFC 36: a typing of an application of
a second-order variable, or of an instance of a declared type, has the premises of its rule, since
the rule of its term and the rule `(conv)`, which keeps the term and its premises, are the only ones
that conclude it.
The proof is by the induction on the derivations, `Derivations.induction`, through the premise of
`(conv)`.

The type of the typing is left out: it is the type that the rule gives or a type equal to it, which
nothing reads so far.

The type declaration of the premises of `(D)` is the one of the signature that declares the name of
the instance, since the names of a well-formed signature are distinct.

ADE prove the inversion of each of their rules, with the equality of the type to the one that the
rule gives.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

-- ADE: `inversion-app`, in `Definition/Typed/Consequences/Inversion.agda`, for the applications,
-- with the equality of the types.
/-- An application of a second-order variable that has a type is typed by `(var_X)`: the variable is
in the context with a telescope, and the arguments are arguments of this telescope. -/
theorem HasType.secondOrder_inv {Γ : Scope} {ctx : Context k Γ} {ps : List Parameter}
    {ψ : ResultOwnership Grade ps.length} {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps}
    {B : Term k Γ} (h : HasType sig ctx (.var X ts) B) :
    ∃ (Θ : Telescope k Γ ps) (A : Term k (Γ.extend ps.length)),
      ctx.SecondOrderIn X Θ A ∧ HasArgs sig ctx ts Θ :=
  go h rfl
where
  /-- The inversion, by induction on the derivation of a term equal to the application. -/
  go {Γ : Scope} {ctx : Context k Γ} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps} : {t B : Term k Γ} →
      HasType sig ctx t B → t = .var X ts →
      ∃ (Θ : Telescope k Γ ps) (A : Term k (Γ.extend ps.length)),
        ctx.SecondOrderIn X Θ A ∧ HasArgs sig ctx ts Θ := by
    suffices H : Derivations.Conclusion
        (hasType := fun sig {k Γ} ctx t _ _ => ∀ {ps : List Parameter}
          {ψ : ResultOwnership Grade ps.length} {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps},
          t = .var X ts → ∃ (Θ : Telescope k Γ ps) (A : Term k (Γ.extend ps.length)),
            ctx.SecondOrderIn X Θ A ∧ HasArgs sig ctx ts Θ) from
      fun {_ _} h e => H.hasType h e
    apply Derivations.induction
    case hasType_secondOrder =>
      refine fun hX hts hts_ih => fun e => ?_
      cases e; exact ⟨_, _, hX, hts⟩
    case hasType_conv => exact fun ht _ ht_ih _ => fun e => ht_ih e
    case hasType_var | hasType_const | hasType_univ | hasType_prop | hasType_inst |
        hasType_equality | hasType_reflProof | hasType_transp | hasType_propExt | hasType_coind |
        hasType_ctor | hasType_recursor | hasType_obs | hasType_corec =>
      intros; cases ‹_ = _›
    all_goals intros; trivial

-- ADE: `inversion-ΠΣ-U`, in `Definition/Typed/Consequences/Inversion.agda`, for the types of
-- functions and of pairs, with the equality of the sorts.
/-- An instance of a declared type that has a type is typed by `(D)`: the signature has the declared
type, whose constraint admits the instance, and the arguments are arguments of its parameters. -/
theorem HasType.inst_inv {Γ Δ : Scope} {ctx : Context k Γ} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {B : Term k Γ}
    (h : HasType sig ctx (.inst D qs ls ps as) B) :
    ∃ (decl : TypeDeclaration) (ζ : Instance decl.sorts decl.grades →
        GradeVector decl.scope.length) (hΔ : Δ = decl.scope) (hqp : decl.AsMany qs ps)
        (hl : ls.length = decl.levels),
      sig.HasDeclaredType D decl ζ ∧ decl.constraint hqp.inst ∧
        HasInstanceArgs sig ctx (hΔ ▸ as)
          ((decl.params hqp.inst).substLevels (ls.getFin hl)) :=
  go h rfl
where
  /-- The inversion, by induction on the derivation of a term equal to the instance. -/
  go {Γ Δ : Scope} {ctx : Context k Γ} {D : Name} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} {as : InstanceArgs k Γ Δ} : {t B : Term k Γ} →
      HasType sig ctx t B → t = .inst D qs ls ps as →
      ∃ (decl : TypeDeclaration) (ζ : Instance decl.sorts decl.grades →
          GradeVector decl.scope.length) (hΔ : Δ = decl.scope) (hqp : decl.AsMany qs ps)
          (hl : ls.length = decl.levels),
        sig.HasDeclaredType D decl ζ ∧ decl.constraint hqp.inst ∧
          HasInstanceArgs sig ctx (hΔ ▸ as)
            ((decl.params hqp.inst).substLevels (ls.getFin hl)) := by
    suffices H : Derivations.Conclusion
        (hasType := fun sig {k Γ} ctx t _ _ => ∀ {Δ : Scope} {D : Name} {qs : List Quality}
          {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}, t = .inst D qs ls ps as →
          ∃ (decl : TypeDeclaration) (ζ : Instance decl.sorts decl.grades →
              GradeVector decl.scope.length) (hΔ : Δ = decl.scope) (hqp : decl.AsMany qs ps)
              (hl : ls.length = decl.levels),
            sig.HasDeclaredType D decl ζ ∧ decl.constraint hqp.inst ∧
              HasInstanceArgs sig ctx (hΔ ▸ as)
                ((decl.params hqp.inst).substLevels (ls.getFin hl))) from
      fun {_ _} h e => H.hasType h e
    apply Derivations.induction
    case hasType_inst =>
      refine fun h hqp hl hadm has has_ih => fun e => ?_
      cases e; exact ⟨_, _, rfl, hqp, hl, h, hadm, has⟩
    case hasType_conv => exact fun ht _ ht_ih _ => fun e => ht_ih e
    case hasType_var | hasType_secondOrder | hasType_const | hasType_univ | hasType_prop |
        hasType_equality | hasType_reflProof | hasType_transp | hasType_propExt | hasType_coind |
        hasType_ctor | hasType_recursor | hasType_obs | hasType_corec =>
      intros; cases ‹_ = _›
    all_goals intros; trivial

/-- An instance of a type of a type declaration of the signature, which has a type, has the
premises of the rule `(D)` at this type declaration, the only one that declares its name. -/
theorem HasType.inst_inv_of_mem {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {D : Name}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope}
    {B : Term k Γ} (h : HasType sig ctx (.inst D qs ls ps as) B)
    (hd : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names) :
    ∃ (ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length)
        (hqp : decl.AsMany qs ps) (hl : ls.length = decl.levels),
      sig.HasDeclaredType D decl ζ ∧ decl.constraint hqp.inst ∧
        HasInstanceArgs sig ctx as
          ((decl.params hqp.inst).substLevels (ls.getFin hl)) := by
  obtain ⟨decl', ζ, hΔ, hqp, hl, hD', hadm, has⟩ := h.inst_inv
  have hm : D ∈ decl'.names := by
    rcases hD'.2 with ⟨T, hT, rfl, -⟩ | ⟨T, hT, rfl, -⟩
    · exact TypeDeclaration.name_mem_names hT
    · exact TypeDeclaration.codata_name_mem_names hT
  have he := (presuppositions.wfCtx (contextPresuppositions.hasType h)).distinct.entry_unique
    hD'.1 hd (n := D) hm hD
  injection he with he
  subst he
  exact ⟨ζ, hqp, hl, hD', hadm, has⟩

end Sic.Core
