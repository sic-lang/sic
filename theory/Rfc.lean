module

public import Lean.Attributes

/-!
# Correspondence with the RFCs

The attribute `rfc` relates a declaration to the definitions, formulas and rules of the RFCs that it
formalizes, by their names, written exactly as the RFCs write them in LaTeX.
It is a library apart from `Sic`, since the attributes of Lean depend on `Classical.choice`, which
the declarations of `Sic` may not.
-/

public section

namespace Rfc

open Lean

/-- `rfc "name"…`: the declaration formalizes the definitions, formulas or rules of these names. -/
syntax (name := rfc) "rfc" (ppSpace str)+ : attr

/-- The names of the RFCs that each declaration formalizes. -/
initialize rfcAttr : ParametricAttribute (Array String) ←
  registerParametricAttribute {
    name := `rfc
    descr := "the names of the definitions, formulas and rules of the RFCs that it formalizes"
    getParam := fun _ stx => match stx with
      | `(attr| rfc $names:str*) => pure (names.map (·.getString))
      | _ => throwError "expected the names of the RFCs, as strings"
  }

end Rfc
