module

public import Sic.Grading.Grade
public import Sic.Math.Vector

/-!
# Vectors of Grades

The vectors of grades of annex 10 of RFC 36, one grade for each entry of a context: the vectors of
`Sic/Math/Vector.lean` whose elements are grades, whose operations, order and laws are those of the
vectors at the modality of the grades, `Grade.modality`.
The entries are numbered by de Bruijn indices, the last entry of the context being `0`.
-/

@[expose] public section

namespace Sic.Grading

-- ADE: `Conₘ`, in `Graded/Context.agda`, at their modality of grades.
/-- A vector of grades over `n` entries, which gives each entry its grade.
RFC: `\mathsf{vector}_\gamma` -/
abbrev GradeVector (n : Nat) : Type := Sic.Math.Vector Grade n

-- ADE: `𝟘ᶜ`, in `Graded/Context.agda`.
/-- `𝟘ᶜ`, the zero vector of grades, whose components are all the grade `𝟘`.
RFC: `\mathsf{zero}_\gamma` -/
notation "𝟘ᶜ" => Sic.Math.Vector.zero Grade.zero

/-! The operations and the laws of the vectors that the core names, under the name of the vectors
of grades, so that only this module names the vectors. -/
namespace GradeVector

export Sic.Math.Vector (add add_le_add extend module smul update zero)

end GradeVector

end Sic.Grading
