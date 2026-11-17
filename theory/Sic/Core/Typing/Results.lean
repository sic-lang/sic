module

public import Sic.Core.Typing
import Sic.Core.Results.Existence
import Sic.Core.Typing.Lifting
import Sic.Core.Typing.Presuppositions

/-!
# Recursive Results in a Well-Formed Signature

The existence of the recursive results of annex 21 of RFC 36: in a well-formed signature, the
terms of the fields of a telescope whose recursive results have types have recursive results.

A well-formed signature has distinct names and declares each of its liftings after the destructors
that it lifts, which is what the existence of the results asks of a signature.

The RFC names the variables, so that the lifting of a recursor keeps each of them; with de Bruijn
indices, it is a lifting of a scope in itself that renames no variable, taken under the fields for
the types of their results.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- In a well-formed signature, the terms of the fields of a telescope whose recursive results
have types have recursive results, where the lifting of the block lifts no variable, whatever the
results of the terms of the types of the block are.
RFC: `\mathsf{exists}_{\mathsf{res}\Theta}` -/
theorem WfSig.exists_resultTerms {sig : Signature} (h : WfSig sig) {k : Nat}
    {v : Lifting.Variables} {Γ : Scope} {ρ : Lifting k Γ Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (hid : ∀ {a} (x : Var Γ a), ρ.ren x = x)
    {ns : List (Nest Name)} {ps ps' : List Parameter} {Θ : Telescope k Γ ps}
    {R : Telescope k (Γ.extend ps.length) ps'}
    (hR : Terms.ResultTypes sig v (ρ.liftN ps.length) ns ps Θ.types
      (Args.bound (Γ := Γ) ps).terms R)
    (φ : Name → Term k (.var :: Γ)) (ts : Args k Γ ps) :
    ∃ rs : Args k Γ ps', Terms.ResultTerms sig v ρ φ ns ps (Θ.typesAt ts) ts.terms rs :=
  Telescope.exists_resultTerms h.distinct h.liftsInOrder hρ hid hR φ ts

end Sic.Core
