module

public import Sic.Core.Typing

/-!
# Inversion

The inversion of the rules `(var_X)` and `(D)` of annex 14 of RFC 36: a typing of an application of
a second-order variable, or of an instance of a declared type, has the premises of its rule, since
the rule of its term and the rule `(conv)`, which keeps the term and its premises, are the only ones
that conclude it.
The proof is by structural recursion on the derivation, through the premise of `(conv)`.

The type of the typing is left out: it is the type that the rule gives or a type equal to it, which
nothing reads so far.

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

end Sic.Core
