module

public import Sic.Core.Evaluation.Claims

/-!
# Environments

The reach and the claims of an environment under another usage, for the proof of the invariant of
the uniqueness at run time: the environment of a term whose usage is above the one that its reach
reads, and the environment of the term of a position.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The reach of an environment for a vector above another keeps the addresses that the frame and
the environment refer to once at most, and the addresses that the environment does not refer to. -/
theorem Heap.EnvReach.sub {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {φ ν ν' : MultiplicityVector n} {U_E F : Demand} (hE : Heap.EnvReach H g E ν U_E)
    (hle : ν ≤ᶜ ν') (hc : ∀ b, Heap.EnvClaims H g E φ ν b → F b + U_E b ≠ .omega) :
    ∃ U', Heap.EnvReach H g E ν' U' ∧
      (∀ b, Heap.EnvClaims H g E φ ν' b → F b + U' b ≠ .omega) ∧
      ∀ b, U_E b = .zero → U' b = .zero := by
  obtain ⟨U', hU', hE'⟩ := hE.toEnvSum.le hle
  refine ⟨U', hE'.toEnvReach, fun b hb => ?_, fun b hb => ?_⟩
  · have h := hc b (hb.imp fun x hx =>
      (by decide : ∀ x y : Multiplicity, x ≤ y → y ≠ .zero → x ≠ .zero) _ _ (hle x) hx)
    exact (by decide : ∀ f x y : Multiplicity, x ≤ y → f + x ≠ .omega → f + y ≠ .omega) _ _ _
      (hU' b) h
  · exact (by decide : ∀ x y : Multiplicity, x ≤ y → x = .zero → y = .zero) _ _ (hU' b) hb

/-- The term of a position of the multiplicity `π`, in an environment whose reach is that of the
position and of the rest: its usage, `0` for a skeleton at the multiplicity `0`, the reach of the
environment for it, which refers to no address that the position does not refer to, and to the
addresses that the term claims once at most with the frame and the rest. -/
theorem Target.Usage.atPosition {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {φ ν₁ ν₂ : MultiplicityVector n} {π : Multiplicity} {M : Target n} {U₁ U₂ F : Demand}
    (hν₁ : Target.Usage ν₁ M) (hz : π = .zero → M.IsSkeleton)
    (hE₁ : Heap.EnvSum H (Heap.ValueReach H g) E ν₁ U₁)
    (hc : ∀ b, Heap.EnvClaims H g E φ ((π ·ᶜ ν₁) +ᶜ ν₂) b →
      F b + (π * U₁ b + U₂ b) ≠ .omega) :
    ∃ (ν₁' : MultiplicityVector n) (U₁' : Demand), Target.Usage ν₁' M ∧
      Heap.EnvReach H g E ν₁' U₁' ∧ (∀ b, π * U₁ b = .zero → U₁' b = .zero) ∧
      ∀ b, Heap.EnvClaims H g E φ ν₁' b → (F b + U₂ b) + U₁' b ≠ .omega := by
  by_cases hπ : π = .zero
  · exact ⟨𝟘ᵛ, 𝟘ᵛ, (hz hπ).usage, hE₁.zero.toEnvReach, fun _ _ => rfl,
      fun b ⟨x, _, _, _, hx, _⟩ => absurd rfl hx⟩
  · refine ⟨ν₁, U₁, hν₁, hE₁.toEnvReach, fun b hb =>
      (by decide : ∀ π u : Multiplicity, π ≠ .zero → π * u = .zero → u = .zero) _ _ hπ hb,
      fun b hb => ?_⟩
    have h := hc b (hb.imp fun x hx => (by decide : ∀ π u v : Multiplicity, π ≠ .zero →
      u ≠ .zero → π * u + v ≠ .zero) _ _ _ hπ hx)
    exact (by decide : ∀ f π u v : Multiplicity, π ≠ .zero → f + (π * u + v) ≠ .omega →
      f + v + u ≠ .omega) _ _ _ _ hπ h

end Sic.Core
