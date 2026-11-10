module

public import Sic.Core.Prelude.Unpacking

/-!
# Unpacking a Telescope

The unpacking of annex 17 of RFC 36: on a telescope of one entry, a recursor on the pair whose
branch is a recursor on the unit, over the variable of the rest; and, in the prelude, the unpacking
of the packing of no argument computes to the term unpacked into.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- The unpacking of a term `u` of the packing of `(x : A ▶ p; q ◀ r)` into `b`: the recursor on the
pair, with the motive that does not depend on `u`, whose branch unpacks the second field `y`, the
packing of the empty rest, into `b` under `y`. -/
example (ρ q : Grade) (p : Parameter) (κ : Universe 0) (A u C : Term 0 []) (b : Term 0 [.var]) :
    Term.unpack ρ u (.cons q p A .nil) [κ] .zero C b =
      .recursor ρ "Pair" [κ.quality] [κ.level, .zero] [p.usage, p.requirement]
        (Prelude.pairArgs A (.inst "Unit" [] [.zero] [] .nil)) u (.cons 0 (C.rename Ren.weaken) .nil)
        (.cons 2 0 (.recursor ρ "Unit" [] [.zero] [] .nil (.var₀ .zero)
          (.cons 0 ((C.rename (Ren.weakenN 2)).rename Ren.weaken) .nil)
          (.cons 0 0 (b.rename (Ren.liftN 0 Ren.weaken)) .nil)) .nil) := rfl

/-- In the prelude, the unpacking of the packing of no argument, the constructor of the unit, into
the unit type of `U_0`, is this type. -/
example (ρ : Grade) :
    EqTerm Signature.prelude Context.empty
      (Term.unpack ρ ((Args.nil (k := 0) (Γ := [])).pack .nil [] .zero) .nil [] .zero
        (.sort ⟨.type, .zero⟩) (Telescope.nil.pack [] .zero))
      (Telescope.nil.pack [] .zero) (.sort ⟨.type, .zero⟩) :=
  have hctx : WfCtx Signature.prelude (Context.empty (k := 0)) := .empty WfSig.prelude
  EqTerm.unpackBeta Signature.hasPrelude_prelude ρ (.nil hctx) (.nil hctx) (.univ hctx)
    (HasType.packLevel Signature.hasPrelude_prelude (.nil hctx))

end SicExample.Core
