module

public import Sic.Core.Meaning
public import Sic.Core.Syntax.Grades

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
The arguments of a telescope are related to addresses, `t̄ ®_H b̄ : Θ`, and valid at run time,
`Σ; γ; Γ ⊨® t̄ : Θ`, in the same way, each at the type of its entry, when its grade is used at run
time.

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

-- ADE: none.
/-- `t̄ ®_H^{p̄} b̄ : Θ`: the closed arguments `t̄` of the closed telescope `Θ` and the addresses `b̄`
of their values in the heap `H`, one for each entry, the first one first, at the grades `p̄`, the
grade `p l` of the argument at each position `l`: each argument whose grade is not in `S^{11ᵐ}`, so
that the erasure keeps it, is related to its address at the type of its entry, in which the
arguments before it are substituted. The grades are those of the entries for the fields of a
constructor, and those of the variables of a branch for its fields and its recursive results. -/
def RunsAsArgs (sig : Signature) (ι : Interpretation) (P : Program) (H : Heap) :
    {ps : List Parameter} → (Nat → Grade) → Args 0 [] ps → List Nat → Telescope 0 [] ps → Prop
  | [], _, .nil, [], .nil => True
  | _ :: _, g, .cons t ts, b :: bs, .cons _ _ A Θ =>
    (g 0 ∉ Mode.oneOne.erased → RunsAs sig ι P H t b A) ∧
      RunsAsArgs sig ι P H (fun l => g (l + 1)) ts bs (Θ.subst₀ (Subst₀.single t))
  | _, _, _, _, _ => False

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

-- ADE: none.
/-- `Σ; γ; Γ ⊨® t̄ : Θ`, at levels without variables: for each closed substitution `σ` of the
first-order context `Γ` that the meaning relates to itself, and each heap `H` in which the addresses
`E` stand for `σ` as `γ` requires, the erasure of the arguments `t̄` at the grades of the entries of
`Θ` evaluates, in `E` and `H`, to addresses `b̄` in a heap `H'` that extends `H`, to which `t̄[σ]`
are related at `Θ[σ]`. -/
def RunValidArgs (sig : Signature) (ι : Interpretation) (P : Program) {Γ : Scope}
    (hΓ : Γ.FirstOrder) (ctx : Context 0 Γ) (γ : GradeVector Γ.length) {ps : List Parameter}
    (ts : Args 0 Γ ps) (Θ : Telescope 0 Γ ps) : Prop :=
  ∀ σ H E, EqSubst sig ι ctx σ σ → RunsAsSubst sig ι P H ctx γ σ E →
    ∃ bs H', EvalAll P H E (ts.terms.erase sig Mode.oneOne.erased hΓ (ps.map (·.usage))) bs H' ∧
      H.Extends H' ∧ RunsAsArgs sig ι P H' (Parameter.grades ps) (ts.subst σ) bs (Θ.subst σ)

end Sic.Core
