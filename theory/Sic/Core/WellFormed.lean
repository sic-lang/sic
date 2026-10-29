module

public import Sic.Core.TypedSubstitution

/-!
# Well-Formedness

The syntactic validity of the judgments of `Sic.Core.Typing`, as in the formalization of ADE: the
type of a typed term is a type, a term of a universe, and two equal terms are typed, at a type.
-/

@[expose] public section

namespace Sic.Core

open Term

/-- The type of each variable of a well-formed context is a type. -/
theorem WfCon.get {Γ : Con k n} (h : ⊢ Γ) (x : Fin n) : ∃ l, Γ ⊢ Γ.get x : Term.univ l :=
  match n, Γ, h, x with
  | _, _, .snoc hA, ⟨0, _⟩ => ⟨_, hA.wk (.step .id) (.snoc hA)⟩
  | _, _, .snoc hA, ⟨x + 1, hx⟩ =>
    have ⟨l, h'⟩ := hA.wfCon.get ⟨x, Nat.lt_of_succ_lt_succ hx⟩
    ⟨l, h'.wk (.step .id) (.snoc hA)⟩

/-!
The validity of both judgments, by induction on their derivations, which need each other: the type
of an application is valid since the type of its function is, a function type, and two equal
terms are typed since their types are valid, to convert the type of the right one.
-/

mutual

/-- The type of a typed term is a type. -/
theorem HasType.wfType : Γ ⊢ t : A → ∃ l, Γ ⊢ A : Term.univ l
  | .var h => h.get _
  | .conv _ hA => ⟨_, hA.wf.2.1⟩
  | .univ h => ⟨_, .univ h⟩
  | .pi hA _ => ⟨_, .univ hA.wfCon⟩
  | .lam hPi _ => ⟨_, hPi⟩
  | .app ht ha =>
    have ⟨_, hPi⟩ := ht.wfType
    have ⟨_, _, hB⟩ := hPi.inv_pi
    ⟨_, hB.instantiate ha⟩

/-- Two equal terms are terms of their type, which is a type. -/
theorem TermEq.wf : Γ ⊢ t ≡ u : A → (Γ ⊢ t : A) ∧ (Γ ⊢ u : A) ∧ ∃ l, Γ ⊢ A : Term.univ l
  | .refl h => ⟨h, h, h.wfType⟩
  | .symm h => ⟨h.wf.2.1, h.wf.1, h.wf.2.2⟩
  | .trans h₁ h₂ => ⟨h₁.wf.1, h₂.wf.2.1, h₁.wf.2.2⟩
  | .conv h hA => ⟨.conv h.wf.1 hA, .conv h.wf.2.1 hA, _, hA.wf.2.1⟩
  | .univ h hl => ⟨.univ h, .conv (.univ h) (.univ h hl.succ.symm), _, .univ h⟩
  | .pi hA hB =>
    have ⟨hA₁, hA₂, _⟩ := hA.wf
    have ⟨hB₁, hB₂, _⟩ := hB.wf
    ⟨.pi hA₁ hB₁, .pi hA₂ (hB₂.conv_last hA hA₂), _, .univ hA₁.wfCon⟩
  | .lam hPi hA ht =>
    have ⟨_, hA₂, _⟩ := hA.wf
    have ⟨ht₁, ht₂, _⟩ := ht.wf
    have ⟨_, _, hB⟩ := hPi.inv_pi
    have hB₂ := hB.conv_last hA hA₂
    ⟨.lam hPi ht₁,
      .conv (.lam (.pi hA₂ hB₂) (ht₂.conv_last hA hA₂)) (.pi hA.symm (.refl hB₂)), _, hPi⟩
  | .app ht ha =>
    have ⟨ht₁, ht₂, _, hPi⟩ := ht.wf
    have ⟨ha₁, ha₂, _⟩ := ha.wf
    have ⟨_, _, hB⟩ := hPi.inv_pi
    ⟨.app ht₁ ha₁, .conv (.app ht₂ ha₂) (hB.instantiateEq ha₁ ha).symm, _, hB.instantiate ha₁⟩
  | .beta hPi ht ha =>
    have ⟨_, _, hB⟩ := hPi.inv_pi
    ⟨.app (.lam hPi ht) ha, ht.instantiate ha, _, hB.instantiate ha⟩
  | .eta h =>
    have ⟨_, hPi⟩ := h.wfType
    have ⟨⟨_, hA⟩, _⟩ := hPi.inv_pi
    have hΓ := WfCon.snoc hA
    have happ := HasType.app (h.wk (.step .id) hΓ) (.var (x := 0) hΓ)
    ⟨h, .lam hPi (by rwa [instantiate_wk_lift_step] at happ), _, hPi⟩

end

end Sic.Core
