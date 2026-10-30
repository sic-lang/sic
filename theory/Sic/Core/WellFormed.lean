module

public import Sic.Core.TypedSubstitution

/-!
# Well-Formedness

The syntactic validity of the judgments of `Sic.Core.Typing`, as in the formalization of ADE: the
type of a typed term is a type, two equal types are types, and two equal terms are typed, at a type.
Every type is a term of a universe, since `(U_type)` is the only rule that makes a term a type.

## Correspondence with the Formalization of ADE

| Theorem | Theorem of ADE, in `Definition/Typed/Well-formed.agda` |
| --- | --- |
| `HasType.wfType` | `wf-⊢∷` |
| `TypeEq.wf` | `wf-⊢≡` |
| `TermEq.wf` | `wf-⊢≡∷` |

ADE have no counterpart of `IsType.sort`, since their type of levels may lie in no universe.
-/

@[expose] public section

namespace Sic.Core

open Term

/-- Every type is a term of a universe. -/
theorem IsType.sort : Γ ⊢ A → ∃ l, Γ ⊢ A : Term.univ l
  | .univ h => ⟨_, h⟩

/-- The type of each variable of a well-formed context is a type. -/
theorem WfCon.get {Γ : Con k n} (h : ⊢ Γ) (x : Fin n) : Γ ⊢ Γ.get x :=
  match n, Γ, h, x with
  | _, _, .snoc hA, ⟨0, _⟩ => hA.wk (.step .id) (.snoc hA)
  | _, _, .snoc hA, ⟨x + 1, hx⟩ =>
    (hA.wfCon.get ⟨x, Nat.lt_of_succ_lt_succ hx⟩).wk (.step .id) (.snoc hA)

/-!
The validity of the judgments, by induction on their derivations, which need each other: the type
of an application is valid since the type of its function is, a function type, and two equal
terms are typed since their types are valid, to convert the type of the right one.
-/

mutual

/-- Two equal types are types. -/
theorem TypeEq.wf : Γ ⊢ A ≡ B → (Γ ⊢ A) ∧ (Γ ⊢ B)
  | .univ h => ⟨.univ h.wf.1, .univ h.wf.2.1⟩
  | .refl h => ⟨h, h⟩
  | .symm h => ⟨h.wf.2, h.wf.1⟩
  | .trans h₁ h₂ => ⟨h₁.wf.1, h₂.wf.2⟩

/-- The type of a typed term is a type. -/
theorem HasType.wfType : Γ ⊢ t : A → Γ ⊢ A
  | .var h => h.get _
  | .conv _ hA => hA.wf.2
  | .univ h => .univ (.univ h)
  | .pi hA _ => .univ (.univ hA.wfCon)
  | .lam hPi _ => hPi
  | .app ht ha =>
    have ⟨_, _, hB⟩ := ht.wfType.inv_pi
    .univ (hB.instantiate ha)

/-- Two equal terms are terms of their type, which is a type. -/
theorem TermEq.wf : Γ ⊢ t ≡ u : A → (Γ ⊢ t : A) ∧ (Γ ⊢ u : A) ∧ (Γ ⊢ A)
  | .refl h => ⟨h, h, h.wfType⟩
  | .symm h => ⟨h.wf.2.1, h.wf.1, h.wf.2.2⟩
  | .trans h₁ h₂ => ⟨h₁.wf.1, h₂.wf.2.1, h₁.wf.2.2⟩
  | .conv h hA => ⟨.conv h.wf.1 hA, .conv h.wf.2.1 hA, hA.wf.2⟩
  | .univ h hl =>
    ⟨.univ h, .conv (.univ h) (.univ (.univ h hl.succ.symm)), .univ (.univ h)⟩
  | .pi hA hB =>
    have ⟨hA₁, hA₂, _⟩ := hA.wf
    have ⟨hB₁, hB₂, _⟩ := hB.wf
    ⟨.pi hA₁ hB₁, .pi hA₂ (hB₂.conv_last (.univ hA) (.univ hA₂)), .univ (.univ hA₁.wfCon)⟩
  | .lam hPi hA ht =>
    have ⟨_, hA₂, _⟩ := hA.wf
    have ⟨ht₁, ht₂, _⟩ := ht.wf
    have ⟨_, _, hB⟩ := hPi.inv_pi
    have hB₂ := hB.conv_last (.univ hA) (.univ hA₂)
    ⟨.lam hPi ht₁,
      .conv (.lam (.univ (.pi hA₂ hB₂)) (ht₂.conv_last (.univ hA) (.univ hA₂)))
        (.univ (.pi hA.symm (.refl hB₂))), hPi⟩
  | .app ht ha =>
    have ⟨ht₁, ht₂, hPi⟩ := ht.wf
    have ⟨ha₁, ha₂, _⟩ := ha.wf
    have ⟨_, _, hB⟩ := hPi.inv_pi
    ⟨.app ht₁ ha₁, .conv (.app ht₂ ha₂) (.univ (hB.instantiateEq ha₁ ha).symm),
      .univ (hB.instantiate ha₁)⟩
  | .beta hPi ht ha =>
    have ⟨_, _, hB⟩ := hPi.inv_pi
    ⟨.app (.lam hPi ht) ha, ht.instantiate ha, .univ (hB.instantiate ha)⟩
  | .eta h =>
    have hPi := h.wfType
    have ⟨⟨_, hA⟩, _⟩ := hPi.inv_pi
    have hΓ := WfCon.snoc (.univ hA)
    have happ := HasType.app (h.wk (.step .id) hΓ) (.var (x := 0) hΓ)
    ⟨h, .lam hPi (by rwa [instantiate_wk_lift_step] at happ), hPi⟩

end

end Sic.Core
