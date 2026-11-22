module

public import Sic.Core.Meaning

/-!
# Meaning of the Premises of a Recursor

The premises of `(rec)` on the motives and on the branches, `hCs`, `hCt` and `hus` of
`HasType.recursor`, in the meaning at closed levels, which the soundness of `(rec)`, `(rec_≡)` and
`(ι)` and the run-time relation of the recursors use together.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The premises `hCs`, `hCt` and `hus` of `(rec)`, `HasType.recursor`, in the meaning at levels
without variables: a motive for each type of the block, a type of the sort `κ` over a term of the
instance of this type, and a branch for each case of the block, over its fields and its recursive
results.
The premises `hCl` and `hul` on the numbers of motives and of branches are absent, since the
meaning does not use them.
The premises `hRs` and `hut` are kept apart: `hRs` gives the types of the recursive results at
grades of the fields, which the soundness takes at some grades, as `(rec)` states them, and the
run-time relation at the grades `π̄` of `(rec▶)`; `hut` is stated at these types. -/
structure ValidRecursorPremises (sig : Signature) (ι : Interpretation) {Γ : Scope}
    (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) (hqp : decl.AsMany qs ps)
    (as : InstanceArgs 0 Γ decl.scope) (Cs : Motives 0 Γ) (us : Branches 0 Γ) (κ : Universe 0) :
    Prop where
  /-- `hCs`: a motive for each type of the block. -/
  motives : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩
  /-- `hCt`: the motive of a type of the block is a type of the sort `κ` over a term of the
  instance of this type. -/
  motives_valid : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
    ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ)
  /-- `hus`: a branch for each case of the block, over the fields and the recursive results of its
  constructor. -/
  branches : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
    ∃ u, us.get i = some ⟨(con.params hqp.inst).length,
      (con.nestResultParams hqp.inst decl.names).length, u⟩

end Sic.Core
