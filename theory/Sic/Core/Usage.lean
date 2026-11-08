module

public import Sic.Core.GradeVector
public import Sic.Core.Syntax

/-!
# Usage

The judgment of usage of RFC 24, `Σ; γ ▶_m t`: checked in the mode `m`, the term `t` uses each
variable of its scope as the grade that `γ` gives it allows.
Usage is defined on the term and the signature alone, whose binders and entries carry the grades:
a second-order variable uses its arguments with the grades of its telescope, which its scope gives.

The core gives the usage of its variables, of its constants and of its sorts, and the rule `(sub)`;
the kinds of declarations give the usage of their instances and of their terms.
ADE have no second-order variables, no constants and no sorts of propositions.
-/

@[expose] public section

namespace Sic.Core

mutual

-- ADE: `_▸[_]_`, in `Graded/Usage.agda`.
/-- `Σ; γ ▶_m t`: checked in the mode `m`, the term `t` uses its variables as `γ` allows. -/
inductive Usage (sig : Signature) : {k : Nat} → {Γ : Scope} → GradeVector Γ.length → Mode →
    Term k Γ → Prop where
  /--
  `(var_Xm)`: the application `X[t̄]` uses `X` with the grade of the mode, and each argument `tⱼ`
  with the grade `pⱼ` of its entry, checked in the mode of this grade; a variable `x` is the case
  without arguments, the rule `(var_m)`.
  -/
  | var {k : Nat} {Γ : Scope} {ps : List Grade} {x : Var Γ ps} {ts : Args k Γ ps} {m : Mode}
      {δ : GradeVector Γ.length} (hts : UsageArgs sig δ m ts) :
      Usage sig ((GradeVector.update 𝟘ᶜ x.toFin m.grade) +ᶜ δ) m (.var x ts)
  -- ADE: `defn`, in `Graded/Usage.agda`, for the definitions.
  /-- `(c_m)`: a definition or a constant uses no variable, in a mode that its mode allows. -/
  | const {k : Nat} {Γ : Scope} {c : Name} {j k' g : Nat} {m m' : Mode}
      {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : sig.HasConstant c j k' g m' A) (hm : m ·ᵐ m' = m) :
      Usage sig 𝟘ᶜ m (.const c qs ls ps : Term k Γ)
  /-- `(U_m)` and `(Ω_m)`: a sort uses no variable. -/
  | sort {k : Nat} {Γ : Scope} {κ : Universe k} {m : Mode} : Usage sig 𝟘ᶜ m (.sort κ : Term k Γ)
  /-- `(sub)`: a term may be given grades lower than its uses. -/
  | sub {k : Nat} {Γ : Scope} {γ δ : GradeVector Γ.length} {m : Mode} {t : Term k Γ}
      (h : Usage sig γ m t) (hle : δ ≤ᶜ γ) : Usage sig δ m t

/-- The usage `p₁ ·ᶜ δ₁ +ᶜ … +ᶜ pₐ ·ᶜ δₐ` of the arguments `t̄` of a telescope whose entries have the
grades `p₁, …, pₐ`, each argument `tⱼ` being checked in the mode `m ⊙ pⱼ`. -/
inductive UsageArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Grade} →
    GradeVector Γ.length → Mode → Args k Γ ps → Prop where
  /-- No argument uses no variable. -/
  | nil {k : Nat} {Γ : Scope} {m : Mode} : UsageArgs sig 𝟘ᶜ m (.nil : Args k Γ [])
  /-- The first argument, of grade `p`, and the others. -/
  | cons {k : Nat} {Γ : Scope} {p : Grade} {ps : List Grade} {t : Term k Γ} {ts : Args k Γ ps}
      {m : Mode} {γ δ : GradeVector Γ.length} (ht : Usage sig γ (m ⊙ p) t)
      (hts : UsageArgs sig δ m ts) :
      UsageArgs sig ((p ·ᶜ γ) +ᶜ δ) m (.cons t ts : Args k Γ (p :: ps))

end

end Sic.Core
