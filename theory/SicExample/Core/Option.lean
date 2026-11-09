module

public import Sic.Core.Typing

/-!
# Option

The type of the optional values of a type `X`,
`data.{} (X : U₀) : U₀ where Option ▶ (1) ≔ none : () | some : (x : X ▶ 1; 0 ◀ ωω)`, is a well-formed
type declaration in the empty signature, whose type uses its parameter once: its constructor `none`
uses `X` no time and `some` once, and the uses of the constructors are added, `0 + 1 = 1`, since the
type mentions both.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- The parameters `(X : U₀)`. -/
def Option.params : Context 0 [.var] := .var .empty (.sort ⟨.type, .zero⟩)

/-- `none : ()`, without field. -/
def Option.none : Constructor 0 0 0 [.var] where
  name := "none"
  params := fun _ => []
  fields := fun _ => .nil

/-- `some : (x : X ▶ 1; 0 ◀ ωω)`, a field of type `X`, used once, which requires nothing of its
argument. -/
def Option.some : Constructor 0 0 0 [.var] where
  name := "some"
  params := fun _ => [⟨Grade.one, Grade.unrestrictedUnrestricted, .none⟩]
  fields := fun _ => .cons Grade.zero _ (.var₀ .zero) .nil

/-- `data.{} (X : U₀) : U₀ where Option ▶ (1) ≔ none : () | some : (x : X ▶ 1; 0 ◀ ωω)`. -/
def Option.decl : TypeDeclaration where
  sorts := 0
  levels := 0
  grades := 0
  scope := [.var]
  params := fun _ => Option.params
  sort := fun _ => ⟨.type, .zero⟩
  types := [⟨"Option", fun _ _ => Grade.one, [Option.none, Option.some]⟩]

/-- The parameters form a context: `U₀` is a type. -/
theorem Option.wfParams : WfCtx [] Option.params :=
  .var (.univType (.univ (.empty .empty)))

/-- The uses of `X` by the type of the field of `some`, once, in the mode `11ᵐ ⊙ 1`. -/
def Option.usesX : GradeVector 1 :=
  GradeVector.update 𝟘ᶜ (Var.zero : Var [.var] .var).toFin (Mode.oneOne ⊙ Grade.one).grade +ᶜ 𝟘ᶜ

/-- The type of the field of `some`, `X`, uses `X` once. -/
theorem Option.usageX :
    Usage [] (Γ := [.var]) Option.usesX (.oneOne ⊙ Grade.one) (.var₀ .zero : Term 0 [.var]) :=
  .var .nil

/-- The field of `some` uses `X` once, and no type after it uses its variable `x`. -/
theorem Option.usageSome :
    UsageTelescope [] (Γ := [.var]) ((Grade.one ·ᶜ Option.usesX) +ᶜ 𝟘ᶜ) .oneOne
      (.cons Grade.zero ⟨Grade.one, Grade.unrestrictedUnrestricted, .none⟩ (.var₀ .zero) .nil :
        Telescope 0 [.var] _) :=
  .cons (p := ⟨Grade.one, Grade.unrestrictedUnrestricted, .none⟩) Option.usageX
    (show UsageTelescope [] (k := 0) (Γ := [.var, .var]) ((𝟘ᶜ : GradeVector 1) ∙ (Mode.oneOne.grade * Grade.zero))
      .oneOne .nil from .sub .nil (by decide))

/-- The type uses `X` once, as the uses of its constructors added allow: `0 + 1 = 1`. -/
theorem Option.usage_le :
    (fun _ => Grade.one : GradeVector 1) ≤ᶜ 𝟘ᶜ +ᶜ (((Grade.one ·ᶜ Option.usesX) +ᶜ 𝟘ᶜ) +ᶜ 𝟘ᶜ) := by
  decide

/-- The declaration is well formed: the field of `some` lives in `U₀`, and the constructors use `X`
once in all, `0` for `none` and `1` for `some`. -/
theorem Option.wf : WfTypeDeclaration [] Option.decl := by
  refine .intro (fun _ => Option.wfParams) ?_ ?_ ?_
  · intro _ T hT c hc
    obtain rfl := List.mem_singleton.1 hT
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .nil Option.wfParams
    · obtain rfl := List.mem_singleton.1 hc
      have hX : HasType [] Option.params (.var₀ .zero) (.sort ⟨.type, .zero⟩) :=
        .var Option.wfParams .zero
      exact .cons hX (by decide : (⟨.type, .zero⟩ : Universe 0) ≼ ⟨.type, .zero⟩)
        (.nil (.var (.univType hX))) (by simp)
  · intro _ T hT
    obtain rfl := List.mem_singleton.1 hT
    exact ⟨_, .cons .nil (.cons Option.usageSome .nil), Option.usage_le⟩
  · intro T hT
    obtain rfl := List.mem_singleton.1 hT
    decide

end SicExample.Core
