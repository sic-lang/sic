module

public import Sic.Core.Meaning

/-!
# Relation of Run Time

The relation of run time of annex 20 of RFC 36, `t ®_H a : A`, between a closed term `t` of the
source of a closed type `A` and the address `a` of a value of the target language in the heap `H`,
which states that the value at `a` is what the erasure by `S^{11ᵐ}` of `t` computes at run time: the
type computes to a proposition, whose proofs are related to every address, or to a canonical type,
whose relation of run time, which the meaning gives, relates the term to the address.

A term with grades `γ` is valid at run time, `Σ; γ; Γ ⊨® t : A`, when its erasure computes, from the
addresses of the variables that `γ` counts at run time, a value related to the term substituted by
the closed terms that these addresses stand for: the statement of the fundamental lemma.

ADE relate a term to the term of the target language that it extracts to, `t ® v ∷ A / [A]`, by
recursion on the proof that `A` is reducible, in `Graded/Erasure/LogicalRelation.agda`.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: `_®_∷_/_`, in `Graded/Erasure/LogicalRelation.agda`.
/-- `t ®_H a : A`: the closed type `A` computes to a proposition, whose closed terms are related to
every address, as `(rt_⇓)` relates the terms of a field, since a proof has no use at run time and the
meaning does not compute it, or to a type whose relation of run time relates what the closed term `t`
computes to the address `a` in the heap `H`.
RFC: `\circledR_A` -/
def RunsAs (sig : Signature) (ι : Interpretation) (P : Program) (H : Heap) (t : Term 0 [])
    (a : Nat) (A : Term 0 []) : Prop :=
  ∃ v, Computesι sig ι A v ∧
    (IsProp sig ι v ∨ ∃ R, HasRun sig ι P v R ∧ R.computed sig ι H t a)

-- ADE: `_®_∷[_]_◂_`, for the substitutions, in `Graded/Erasure/LogicalRelation.agda`.
/-- `(σ, E) ∈ ®_H(Γ, γ)`: the closed substitution `σ` of the context `Γ`, whose variables are all
first-order, and the addresses `E` of the variables in the heap `H`, the last one first: each variable
whose grade in `γ` is not in `S^{11ᵐ}`, so that the erasure keeps its uses, is related to its address
at its type; a second-order variable has no address, since the erasure keeps no abstraction.
RFC: `\circledR_\varepsilon`
RFC: `\circledR_x` -/
def RunsAsSubst (sig : Signature) (ι : Interpretation) (P : Program) (H : Heap) :
    {Γ : Scope} → Context 0 Γ → GradeVector Γ.length → Subst 0 [] Γ → List Nat → Prop
  /- `(®_ε)`. -/
  | _, .empty, _, _, E => E = []
  /- `(®_x)`. -/
  | _, .var ctx A, γ, σ, E => ∃ a E', E = a :: E' ∧
      RunsAsSubst sig ι P H ctx (fun x => γ x.succ) (Subst.tail σ) E' ∧
      (γ 0 ∉ Mode.oneOne.erased → RunsAs sig ι P H (σ .zero) a (A.subst (Subst.tail σ)))
  | _, .secondOrder .., _, _, _ => False

-- ADE: `_▸_⊩ʳ_∷[_]_`, in `Graded/Erasure/LogicalRelation/Hidden.agda`.
/-- `Σ; γ; Γ ⊨® t : A`, at levels without variables: for each closed substitution `σ` of the
first-order context `Γ` that the meaning relates to itself, and each heap `H` in which the addresses
`E` stand for `σ` as `γ` requires, the erasure of `t` by `S^{11ᵐ}` evaluates, in `E` and `H`, to an
address `a` in a heap `H'` that extends `H`, to which `t[σ]` is related at `A[σ]`.
RFC: `{\vDash}^{\circledR}` -/
def RunValid (sig : Signature) (ι : Interpretation) (P : Program) {Γ : Scope} (hΓ : Γ.FirstOrder)
    (ctx : Context 0 Γ) (γ : GradeVector Γ.length) (t A : Term 0 Γ) : Prop :=
  ∀ σ H E, EqSubst sig ι ctx σ σ → RunsAsSubst sig ι P H ctx γ σ E →
    ∃ a H', Eval P H E (t.erase sig Mode.oneOne.erased hΓ) a H' ∧ H.Extends H' ∧
      RunsAs sig ι P H' (t.subst σ) a (A.subst σ)

end Sic.Core
