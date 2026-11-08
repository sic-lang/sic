module

public import Sic.Core.GradeVector
public import Sic.Core.Syntax

/-!
# Usage

The judgment of usage of annex 10 of RFC 36, `Σ; γ ⊢ t ▶ m`: checked in the mode `m`, the term `t`
uses each variable of its scope as the grade that `γ` gives it allows.
Usage is defined on the term and the signature alone, whose binders and entries carry the grades:
a second-order variable uses its arguments with the grades of the parameters of its telescope, which
its scope gives.

The core gives the usage of its variables, of its constants and of its sorts, and the rule `(sub)`;
the kinds of declarations give the usage of their instances and of their terms.
ADE have no second-order variables, no constants and no sorts of propositions.
-/

@[expose] public section

namespace Sic.Core

mutual

-- ADE: `_▸[_]_`, in `Graded/Usage.agda`.
/-- `Σ; γ ⊢ t ▶ m`: checked in the mode `m`, the term `t` uses its variables as `γ` allows. -/
inductive Usage (sig : Signature) : {k : Nat} → {Γ : Scope} → GradeVector Γ.length → Mode →
    Term k Γ → Prop where
  -- ADE: `var` and `_∘ₘ_`, in `Graded/Usage.agda`, for a variable and for an application.
  /--
  The application `x[t̄]` uses `x` with the grade of the mode, and each argument `tⱼ` with the
  grade `pⱼ` of its entry, checked in the mode `m ⊙ pⱼ`; a variable with an empty telescope uses
  itself only.
  RFC: `\mathsf{var}_{X\mathsf{m}}`
  -/
  | var {k : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e} {ts : Args k Γ e.params} {m : Mode}
      {δ : GradeVector Γ.length} (hts : UsageArgs sig δ m ts) :
      Usage sig ((GradeVector.update 𝟘ᶜ x.toFin m.grade) +ᶜ δ) m (.var x ts)
  -- ADE: `defn`, in `Graded/Usage.agda`, for the definitions.
  /-- A constant, defined or declared, uses no variable, in a mode `m₁` that the mode `m₂` of its
  entry allows.
  RFC: `f_{\mathsf{m}}` -/
  | const {k : Nat} {Γ : Scope} {f : Name} {j k' g : Nat} {m₁ m₂ : Mode} {c₀ : Grade}
      {A : Instance j g → Term k' []} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : sig.HasConstant f j k' g m₂ c₀ A) (hm : m₁ ·ᵐ m₂ = m₁) :
      Usage sig 𝟘ᶜ m₁ (.const f qs ls ps : Term k Γ)
  -- ADE: `Uₘ`, in `Graded/Usage.agda`.
  /-- A sort uses no variable.
  RFC: `\kappa_{\mathsf{m}}` -/
  | sort {k : Nat} {Γ : Scope} {κ : Universe k} {m : Mode} : Usage sig 𝟘ᶜ m (.sort κ : Term k Γ)
  -- ADE: `sub`, in `Graded/Usage.agda`.
  /-- A term may be given grades lower than its uses.
  RFC: `\mathsf{sub}` -/
  | sub {k : Nat} {Γ : Scope} {γ δ : GradeVector Γ.length} {m : Mode} {t : Term k Γ}
      (h : Usage sig γ m t) (hle : δ ≤ᶜ γ) : Usage sig δ m t

-- ADE: none.
/-- `Σ; γ ⊢ t̄ ▶ p̄; m`: checked in the mode `m`, the arguments `t̄` of a telescope whose parameters have
the grades `p̄` use the variables of their scope as `γ` allows. -/
inductive UsageArgs (sig : Signature) : {k : Nat} → {Γ : Scope} → {ps : List Parameter} →
    GradeVector Γ.length → Mode → Args k Γ ps → Prop where
  /-- No argument uses no variable.
  RFC: `\mathsf{tel}_{\varepsilon\mathsf{m}}` -/
  | nil {k : Nat} {Γ : Scope} {m : Mode} : UsageArgs sig 𝟘ᶜ m (.nil : Args k Γ [])
  /-- The first argument, of grade `p.usage`, checked in the mode `m ⊙ p.usage`, and the others.
  RFC: `\mathsf{tel}_{,\mathsf{m}}` -/
  | cons {k : Nat} {Γ : Scope} {p : Parameter} {ps : List Parameter} {t : Term k Γ}
      {ts : Args k Γ ps} {m : Mode} {γ δ : GradeVector Γ.length} (ht : Usage sig γ (m ⊙ p.usage) t)
      (hts : UsageArgs sig δ m ts) :
      UsageArgs sig ((p.usage ·ᶜ γ) +ᶜ δ) m (.cons t ts : Args k Γ (p :: ps))

end

end Sic.Core
