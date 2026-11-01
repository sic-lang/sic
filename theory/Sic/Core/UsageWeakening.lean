module

public import Sic.Core.Substitution
public import Sic.Core.Usage

/-!
# Usage Weakening

The usage of a weakened term: moved by a weakening, a term uses the variables that the weakening
adds with the grade `𝟘`, and its other variables as before, as the vector moved by the weakening
says.

## Correspondence with the Formalization of ADE

ADE prove the same lemma, `wkUsage`, with the same weakening of the vectors, `wkConₘ`, defined by
recursion on the weakening.
-/

@[expose] public section

namespace Sic

open Grade Core

namespace GradeVector

-- ADE: `wkConₘ`, in `Graded/Context/Weakening.agda`.
/-- The vector `γ` moved by the weakening `ρ`: the variables that `ρ` adds have the grade `𝟘`. -/
def wk : Wk m n → GradeVector n → GradeVector m
  | .id, γ => γ
  | .step ρ, γ => wk ρ γ ∙ 𝟘
  | .lift ρ, γ => wk ρ (tail γ) ∙ head γ

/-!
The weakening of the vectors commutes with the operations of the rules of the usage, which the
weakening of the usage follows rule by rule.
-/

-- ADE: `wk-𝟘ᶜ`, in `Graded/Context/Weakening.agda`.
theorem wk_zero : ∀ ρ : Wk m n, (𝟘ᶜ : GradeVector n).wk ρ = 𝟘ᶜ
  | .id => rfl
  | .step ρ => by
    rw [wk, wk_zero ρ]
    funext x; match x with | ⟨0, _⟩ | ⟨_ + 1, _⟩ => rfl
  | .lift ρ => by
    rw [wk, show tail (𝟘ᶜ : GradeVector (_ + 1)) = 𝟘ᶜ from rfl, wk_zero ρ]
    funext x; match x with | ⟨0, _⟩ | ⟨_ + 1, _⟩ => rfl

-- ADE: `wk-+ᶜ`, in `Graded/Context/Weakening.agda`.
theorem wk_add : ∀ (ρ : Wk m n) (γ δ : GradeVector n), (γ + δ).wk ρ = γ.wk ρ + δ.wk ρ
  | .id, _, _ => rfl
  | .step ρ, γ, δ => by
    rw [wk, wk, wk, wk_add ρ]
    funext x; match x with | ⟨0, _⟩ => exact (Grade.add_zero _).symm | ⟨_ + 1, _⟩ => rfl
  | .lift ρ, γ, δ => by
    rw [wk, wk, wk, show tail (γ + δ) = tail γ + tail δ from rfl, wk_add ρ]
    funext x; match x with | ⟨0, _⟩ | ⟨_ + 1, _⟩ => rfl

-- ADE: `wk-·ᶜ`, in `Graded/Context/Weakening.agda`.
theorem wk_smul : ∀ (ρ : Wk m n) (p : Grade) (γ : GradeVector n), (p • γ).wk ρ = p • γ.wk ρ
  | .id, _, _ => rfl
  | .step ρ, p, γ => by
    rw [wk, wk, wk_smul ρ]
    funext x; match x with | ⟨0, _⟩ => exact (Grade.mul_zero ..).symm | ⟨_ + 1, _⟩ => rfl
  | .lift ρ, p, γ => by
    rw [wk, wk, show tail (p • γ) = p • tail γ from rfl, wk_smul ρ]
    funext x; match x with | ⟨0, _⟩ | ⟨_ + 1, _⟩ => rfl

-- ADE: `wk-≤ᶜ`, in `Graded/Context/Weakening.agda`.
theorem wk_mono : ∀ (ρ : Wk m n) {γ δ : GradeVector n}, γ ≤ δ → γ.wk ρ ≤ δ.wk ρ
  | .id, _, _, h => h
  | .step ρ, _, _, h => fun
    | ⟨0, _⟩ => Grade.le_refl _
    | ⟨x + 1, hx⟩ => wk_mono ρ h ⟨x, Nat.lt_of_succ_lt_succ hx⟩
  | .lift ρ, _, _, h => fun
    | ⟨0, _⟩ => h 0
    | ⟨x + 1, hx⟩ => wk_mono ρ (tail_mono h) ⟨x, Nat.lt_of_succ_lt_succ hx⟩

-- ADE: `wkUsageVar`, in `Graded/Usage/Weakening.agda`.
theorem wk_update_zero :
    ∀ (ρ : Wk m n) (x : Fin n) (p : Grade), (𝟘ᶜ, x ≔ p).wk ρ = (𝟘ᶜ, ρ.var x ≔ p)
  | .id, _, _ => rfl
  | .step ρ, x, p => by
    show wk ρ (𝟘ᶜ, x ≔ p) ∙ 𝟘 = (𝟘ᶜ, (ρ.var x).succ ≔ p)
    rw [wk_update_zero ρ, update_succ_zero]
  | .lift ρ, ⟨0, _⟩, p => by
    show wk ρ (tail (𝟘ᶜ, 0 ≔ p)) ∙ head (𝟘ᶜ, 0 ≔ p) = (𝟘ᶜ, 0 ≔ p)
    rw [update_zero_zero, update_zero_zero]
    show wk ρ 𝟘ᶜ ∙ p = 𝟘ᶜ ∙ p
    rw [wk_zero]
  | .lift ρ, ⟨x + 1, hx⟩, p => by
    show wk ρ (tail (𝟘ᶜ, Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩ ≔ p)) ∙
        head (𝟘ᶜ, Fin.succ ⟨x, Nat.lt_of_succ_lt_succ hx⟩ ≔ p) =
      (𝟘ᶜ, (ρ.var ⟨x, Nat.lt_of_succ_lt_succ hx⟩).succ ≔ p)
    rw [update_succ_zero, update_succ_zero]
    show wk ρ (𝟘ᶜ, _ ≔ p) ∙ 𝟘 = _
    rw [wk_update_zero ρ]

end GradeVector

namespace Core

open GradeVector

-- ADE: `wkUsage`, in `Graded/Usage/Weakening.agda`.
/--
A term moved by a weakening is well used with the vector moved by the weakening: the variables that
the weakening adds are not used.
-/
theorem Usage.wk (ρ : Wk m n) {γ : GradeVector n} {t : Term k n} : γ ▶[md] t → γ.wk ρ ▶[md] t.wk ρ
  | .sub h hγ => .sub (h.wk ρ) (wk_mono ρ hγ)
  | .var => wk_update_zero .. ▸ .var
  | .univ => wk_zero ρ ▸ .univ
  | .pi hA hB => by
    rw [wk_add, wk_smul]
    exact .pi (hA.wk ρ) (hB.wk ρ.lift)
  | .lam ht => .lam (ht.wk ρ.lift)
  | .app ht ha => by
    rw [wk_add, wk_smul]
    exact .app (ht.wk ρ) (ha.wk ρ)

end Core

end Sic
