module

public import Sic.Core.Prelude
public import Sic.Core.Typing

/-!
# Formation of the Prelude

The formation of the prelude of annex 17 of RFC 36: each of its declarations is well formed in the
declarations before it, at every instance that its constraint admits.
-/

@[expose] public section

namespace Sic.Core

/-- A sort is a term of the universe above its level, in a well-formed context. -/
theorem HasType.sort {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    (hctx : WfCtx sig ctx) : (κ : Universe k) →
      HasType sig ctx (.sort κ) (.sort ⟨.type, .succ κ.level⟩)
  | ⟨.type, _⟩ => .univ hctx
  | ⟨.prop, _⟩ => .prop hctx

/-- A term of a sort is a type. -/
theorem WfType.ofSort {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
    {κ : Universe k} → HasType sig ctx A (.sort κ) → WfType sig ctx A
  | ⟨.type, _⟩, h => .univType h
  | ⟨.prop, _⟩, h => .propType h

/-- The unit is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.unit {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.unit :=
  .data (Ts := _) rfl ⟨⟨Fin.elim0, Fin.elim0⟩, trivial⟩ (fun _ _ => .empty h)
    (fun _ _ T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      obtain _ | ⟨_, ⟨⟩⟩ := hc
      exact .nil (.empty h))
    (fun ι _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      exact ⟨_, .cons .nil .nil, fun x => x.elim0⟩)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The parameters of the pair form a context, whatever the sort of `A`. -/
theorem WfCtx.pairParams {sig : Signature} (h : WfSig sig) (ι : Instance 1 2) :
    WfCtx sig (Prelude.pair.params ι) := by
  have hA : WfCtx sig (Context.empty.var (.sort ⟨ι.sorts 0, .var 0⟩) : Context 2 [.var]) :=
    .var (WfType.ofSort (HasType.sort (.empty h) _))
  have hx := WfCtx.var (WfType.ofSort (HasType.var hA .zero))
  exact .secondOrder (WfType.ofSort (HasType.sort hx ⟨.type, .var 1⟩)) (.inl rfl)

/-- The pair is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.pair {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.pair :=
  .data (Ts := _) rfl ⟨⟨fun _ => .type, fun _ => Grade.zero⟩, fun h => nomatch h⟩
    (fun ι _ => WfCtx.pairParams h ι)
    (fun ι hι T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      obtain _ | ⟨_, ⟨⟩⟩ := hc
      have hctx := WfCtx.pairParams h ι
      have hA : HasType sig (Prelude.pair.params ι) (.var₀ (.succ .zero))
          (.sort ⟨ι.sorts (0 : Fin 1), .var (0 : Fin 2)⟩) :=
        .var hctx (.succSecondOrder .zero)
      have hx := WfCtx.var (WfType.ofSort hA)
      have hB : HasType sig ((Prelude.pair.params ι).var (.var₀ (.succ .zero)))
          (.var (.succ .zero) (.cons (.var₀ .zero) .nil)) (.sort ⟨.type, .var (1 : Fin 2)⟩) :=
        .secondOrder (.succVar .zero) (.cons (.var hx .zero) (.nil hx))
      exact .cons rfl hA ⟨fun h => (by cases h), fun _ => (by simp [Prelude.pair, Level.value]; omega)⟩
        (.cons rfl hB ⟨fun h => (by cases h), fun _ => (by simp [Prelude.pair, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hB))) nofun)
        hι)
    (fun (ι : Instance 1 2) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.pairMk) (.cons (δ := (𝟘ᶜ ∙ Grade.zero) ∙ Grade.one)
        (Usage.var .nil) (.sub (.cons (δ := 𝟘ᶜ) (Usage.var (.cons (Usage.var .nil) .nil))
          (.sub .nil ?_)) ?_)) .nil, ?_⟩
      all_goals
        intro x
        try simp only [Prelude.pairType]
        generalize ι.grades 0 = p
        generalize ι.grades 1 = ρ
        revert x p ρ
        decide)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The parameters of the type of positions form a context, whatever the sort of `B`. -/
theorem WfCtx.stepParams {sig : Signature} (h : WfSig sig) (ι : Instance 1 3) :
    WfCtx sig (Prelude.step.params ι) := by
  have hS : WfCtx sig (Context.empty.var (.sort ⟨.type, .var 0⟩) : Context 2 [.var]) :=
    .var (WfType.ofSort (HasType.sort (.empty h) _))
  exact .var (WfType.ofSort (HasType.sort hS ⟨ι.sorts 0, .var 1⟩))

/-- The type of positions is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.step {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.step :=
  .data (Ts := _) rfl ⟨⟨fun _ => .type, fun _ => Grade.zero⟩, fun h => nomatch h⟩
    (fun ι _ => WfCtx.stepParams h ι)
    (fun ι hι T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      have hctx := WfCtx.stepParams h ι
      obtain _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩ := hc
      · have hS : HasType sig (Prelude.step.params ι) (.var₀ (.succ .zero))
            (.sort ⟨.type, .var (0 : Fin 2)⟩) :=
          .var hctx (.succVar .zero)
        exact .cons rfl hS ⟨fun h => (by cases h), fun _ => (by simp [Prelude.step, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hS))) nofun
      · have hT : HasType sig (Prelude.step.params ι) (.var₀ .zero)
            (.sort ⟨ι.sorts (0 : Fin 1), .var (1 : Fin 2)⟩) :=
          .var hctx .zero
        exact .cons rfl hT ⟨fun h => (by cases h), fun _ => (by simp [Prelude.step, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hT))) hι)
    (fun (ι : Instance 1 3) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.stepNext) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_))
        (.cons (c := Prelude.stepDone) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_)) .nil), ?_⟩
      all_goals
        intro x
        try simp only [Prelude.stepType]
        generalize ι.grades 0 = r
        generalize ι.grades 1 = p
        revert x r p
        decide)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The prelude is a well-formed signature.
RFC: `\mathsf{prelude}_{\vdash}` -/
theorem WfSig.prelude : WfSig Signature.prelude :=
  have hu : WfSig [.typeDeclaration Prelude.unit] :=
    .typeDeclaration (.unit .empty) (by decide) nofun
  have hp : WfSig [.typeDeclaration Prelude.pair, .typeDeclaration Prelude.unit] :=
    .typeDeclaration (.pair hu) (by decide) (by decide)
  .typeDeclaration (.step hp) (by decide) (by decide)
end Sic.Core
