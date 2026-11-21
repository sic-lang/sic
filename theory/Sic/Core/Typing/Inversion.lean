module

public import Sic.Core.Typing
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Presuppositions

/-!
# Inversion

The inversion of the rules `(var_X)` and `(D)` of annex 15 of RFC 36: a typing of an application of
a second-order variable, or of an instance of a declared type, has the premises of its rule, since
the rule of its term and the rule `(conv)`, which keeps the term and its premises, are the only ones
that conclude it.
The proof is by structural recursion on the derivation, through the premise of `(conv)`.

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

-- The compilation of the structural recursion over the mutual judgments, which grows with the
-- premises under binders of their rules, the rule `(coind)` above all, takes more than the default
-- number of heartbeats; the tactics take little, and no rewrite of the recursion or of the rules
-- lowers it.
set_option maxHeartbeats 400000 in
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
  /-- The inversion, by recursion on the derivation of a term equal to the application. -/
  go {Γ : Scope} {ctx : Context k Γ} {ps : List Parameter} {ψ : ResultOwnership Grade ps.length}
      {X : Var Γ (.secondOrder ps ψ)} {ts : Args k Γ ps} : {t B : Term k Γ} →
      HasType sig ctx t B → t = .var X ts →
      ∃ (Θ : Telescope k Γ ps) (A : Term k (Γ.extend ps.length)),
        ctx.SecondOrderIn X Θ A ∧ HasArgs sig ctx ts Θ
    | _, _, .secondOrder hX hts, e => by cases e; exact ⟨_, _, hX, hts⟩
    | _, _, .conv ht _, e => go ht e
    | _, _, .var .., e => by cases e
    | _, _, .const .., e => by cases e
    | _, _, .univ .., e => by cases e
    | _, _, .prop .., e => by cases e
    | _, _, .inst .., e => by cases e
    | _, _, .ctor .., e => by cases e
    | _, _, .recursor .., e => by cases e
    | _, _, .obs .., e => by cases e
    | _, _, .corec .., e => by cases e
    | _, _, .transp .., e => by cases e

-- The compilation of the structural recursion over the mutual judgments, which grows with the
-- premises under binders of their rules, the rule `(coind)` above all, takes more than the default
-- number of heartbeats; the tactics take little, and no rewrite of the recursion or of the rules
-- lowers it.
set_option maxHeartbeats 400000 in
-- ADE: `inversion-ΠΣ-U`, in `Definition/Typed/Consequences/Inversion.agda`, for the types of
-- functions and of pairs, with the equality of the sorts.
/-- An instance of a declared type that has a type is typed by `(D)`: the signature has the declared
type, whose constraint admits the instance, and the arguments are arguments of its parameters. -/
theorem HasType.inst_inv {Γ Δ : Scope} {ctx : Context k Γ} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {B : Term k Γ}
    (h : HasType sig ctx (.inst D qs ls ps as) B) :
    ∃ (decl : TypeDeclaration) (ζ : Instance decl.sorts decl.grades →
        GradeVector decl.scope.length) (hΔ : Δ = decl.scope) (hq : qs.length = decl.sorts)
        (hl : ls.length = decl.levels) (hp : ps.length = decl.grades),
      sig.HasDeclaredType D decl ζ ∧ decl.constraint (.ofLists qs ps hq hp) ∧
        HasInstanceArgs sig ctx (hΔ ▸ as)
          ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) :=
  go h rfl
where
  /-- The inversion, by recursion on the derivation of a term equal to the instance. -/
  go {Γ Δ : Scope} {ctx : Context k Γ} {D : Name} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} {as : InstanceArgs k Γ Δ} : {t B : Term k Γ} →
      HasType sig ctx t B → t = .inst D qs ls ps as →
      ∃ (decl : TypeDeclaration) (ζ : Instance decl.sorts decl.grades →
          GradeVector decl.scope.length) (hΔ : Δ = decl.scope) (hq : qs.length = decl.sorts)
          (hl : ls.length = decl.levels) (hp : ps.length = decl.grades),
        sig.HasDeclaredType D decl ζ ∧ decl.constraint (.ofLists qs ps hq hp) ∧
          HasInstanceArgs sig ctx (hΔ ▸ as)
            ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
    | _, _, .inst h hq hl hp hadm has, e => by
      cases e; exact ⟨_, _, rfl, hq, hl, hp, h, hadm, has⟩
    | _, _, .conv ht _, e => by exact go ht e
    | _, _, .var .., e => by cases e
    | _, _, .secondOrder .., e => by cases e
    | _, _, .const .., e => by cases e
    | _, _, .univ .., e => by cases e
    | _, _, .prop .., e => by cases e
    | _, _, .ctor .., e => by cases e
    | _, _, .recursor .., e => by cases e
    | _, _, .obs .., e => by cases e
    | _, _, .corec .., e => by cases e
    | _, _, .transp .., e => by cases e

-- ADE: none.
/-- An instance of a type of a type declaration of the signature, which has a type, has the
premises of the rule `(D)` at this type declaration, the only one that declares its name. -/
theorem HasType.inst_inv_of_mem {Γ : Scope} {ctx : Context k Γ} {decl : TypeDeclaration} {D : Name}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope}
    {B : Term k Γ} (h : HasType sig ctx (.inst D qs ls ps as) B)
    (hd : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names) :
    ∃ (ζ : Instance decl.sorts decl.grades → GradeVector decl.scope.length)
        (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades),
      sig.HasDeclaredType D decl ζ ∧ decl.constraint (.ofLists qs ps hq hp) ∧
        HasInstanceArgs sig ctx as
          ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) := by
  obtain ⟨decl', ζ, hΔ, hq, hl, hp, hD', hadm, has⟩ := h.inst_inv
  have hm : D ∈ decl'.names := by
    rcases hD'.2 with ⟨T, hT, rfl, -⟩ | ⟨T, hT, rfl, -⟩
    · exact TypeDeclaration.name_mem_names hT
    · exact TypeDeclaration.codata_name_mem_names hT
  have he := (presuppositions.wfCtx (contextPresuppositions.hasType h)).distinct.entry_unique
    hD'.1 hd (n := D) hm hD
  injection he with he
  subst he
  exact ⟨ζ, hq, hl, hp, hD', hadm, has⟩

end Sic.Core
