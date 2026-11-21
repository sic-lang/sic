module

public import Sic.Core.Erasure.Usage
public import Sic.Core.Evaluation

/-!
# Inversions of the Usage

The inversions of the usage of the target language, for the proof of the invariant of the
conservation of the bindings: what the usage of a term of each form gives, and the usage of a
branch of a recursor and of a branch of a corecursor.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

namespace Target.Usage

variable {n : Nat}

-- ADE: none.
/-- A variable reads itself once, at most. -/
theorem var_inv {x : Fin n} :
    {ν : MultiplicityVector n} → {M : Target n} → Target.Usage ν M → M = .var x →
    ν ≤ᶜ MultiplicityVector.update 𝟘ᵛ x .one
  | _, _, .var _, h => by
    cases h
    exact MultiplicityVector.le_refl _
  | _, _, .sub h hle, hM => MultiplicityVector.le_trans hle (var_inv h hM)
  | _, _, .const .., h | _, _, .erased, h | _, _, .ctor _, h | _, _, .recursor .., h
  | _, _, .obs .., h | _, _, .corec .., h => nomatch h

-- ADE: none.
/-- A term that reads no variable, a constant or `↯`, reads none. -/
theorem zero_inv : {ν : MultiplicityVector n} → {M : Target n} → Target.Usage ν M →
    (M = .erased ∨ ∃ f qs ps, M = .const f qs ps) → ν ≤ᶜ 𝟘ᵛ
  | _, _, .const .., _ | _, _, .erased, _ => MultiplicityVector.le_refl _
  | _, _, .sub h hle, hM => MultiplicityVector.le_trans hle (zero_inv h hM)
  | _, _, .var _, h | _, _, .ctor _, h | _, _, .recursor .., h | _, _, .obs .., h
  | _, _, .corec .., h => by
    rcases h with h | ⟨_, _, _, h⟩ <;> exact nomatch h

-- ADE: none.
/-- A constructor reads the variables of its fields. -/
theorem ctor_inv {i : Nat} {Ms : Targets n} :
    {ν : MultiplicityVector n} → {M : Target n} → Target.Usage ν M →
    M = .ctor i Ms → ∃ ν', ν ≤ᶜ ν' ∧ Targets.Usage ν' Ms
  | _, _, .ctor h, hM => by
    cases hM
    exact ⟨_, MultiplicityVector.le_refl _, h⟩
  | _, _, .sub h hle, hM =>
    have ⟨ν', hle', h'⟩ := ctor_inv h hM
    ⟨ν', MultiplicityVector.le_trans hle hle', h'⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased, h | _, _, .recursor .., h
  | _, _, .obs .., h | _, _, .corec .., h => nomatch h

-- ADE: none.
/-- A recursor reads the variables of its term as its multiplicity allows, and those of its
branches. -/
theorem recursor_inv {ρ ϱ : Multiplicity} {M : Target n} {Ns : TargetBranches n} :
    {ν : MultiplicityVector n} → {M' : Target n} → Target.Usage ν M' → M' = .recursor ρ ϱ M Ns →
      ∃ ν₁ χ, ν ≤ᶜ (ρ ·ᶜ ν₁) +ᶜ χ ∧ Target.Usage ν₁ M ∧ (ρ = .zero → M.IsData) ∧
        TargetBranches.Usage ρ χ Ns
  | _, _, .recursor hM hz hNs, h => by
    cases h
    exact ⟨_, _, MultiplicityVector.le_refl _, hM, hz, hNs⟩
  | _, _, .sub h hle, hM =>
    have ⟨ν₁, χ, hle', h₁, hz, h₂⟩ := recursor_inv h hM
    ⟨ν₁, χ, MultiplicityVector.le_trans hle hle', h₁, hz, h₂⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased, h | _, _, .ctor _, h | _, _, .obs .., h
  | _, _, .corec .., h => nomatch h

-- ADE: none.
/-- An observation reads the variables of its term and of its arguments. -/
theorem obs_inv {M : Target n} {i c : Nat} {ψ : ResultOwnership Multiplicity c}
    {ς : Multiplicity} {Ms : Targets n} :
    {ν : MultiplicityVector n} → {M' : Target n} → Target.Usage ν M' → M' = .obs M i ψ ς Ms →
      ∃ ν₁ ν₂, ν ≤ᶜ ν₁ +ᶜ ν₂ ∧ Target.Usage ν₁ M ∧ Targets.Usage ν₂ Ms
  | _, _, .obs hM hMs, h => by
    cases h
    exact ⟨_, _, MultiplicityVector.le_refl _, hM, hMs⟩
  | _, _, .sub h hle, hM =>
    have ⟨ν₁, ν₂, hle', h₁, h₂⟩ := obs_inv h hM
    ⟨ν₁, ν₂, MultiplicityVector.le_trans hle hle', h₁, h₂⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased, h | _, _, .ctor _, h
  | _, _, .recursor .., h
  | _, _, .corec .., h => nomatch h

-- ADE: none.
/-- A corecursor reads the variables of its state, and those of its branches. -/
theorem corec_inv {Ms : Targets n} {Ps : TargetCorecBranches n} :
    {ν : MultiplicityVector n} → {M' : Target n} → Target.Usage ν M' → M' = .corec Ms Ps →
      ∃ ν₁ δ, ν ≤ᶜ ν₁ +ᶜ δ ∧ Targets.Usage ν₁ Ms ∧ TargetCorecBranches.Usage δ Ps
  | _, _, .corec hMs hPs, h => by
    cases h
    exact ⟨_, _, MultiplicityVector.le_refl _, hMs, hPs⟩
  | _, _, .sub h hle, hM =>
    have ⟨ν₁, δ, hle', h₁, h₂⟩ := corec_inv h hM
    ⟨ν₁, δ, MultiplicityVector.le_trans hle hle', h₁, h₂⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased, h | _, _, .ctor _, h
  | _, _, .recursor .., h
  | _, _, .obs .., h => nomatch h

end Target.Usage

/-- The usage of the branches of a recursor gives that of each branch. -/
theorem TargetBranches.Usage.get {n : Nat} {ρ : Multiplicity} {χ : MultiplicityVector n} :
    {Ns : TargetBranches n} → TargetBranches.Usage ρ χ Ns → (i : Nat) → {a b : Nat} →
      {πs κs : Fin a → Multiplicity} → {πs' : Fin b → Multiplicity} →
      {ks : Fin b → RecursiveResult} →
      {N : Target (n + (a + b))} → Ns.get i = some ⟨a, b, πs, κs, πs', ks, N⟩ →
      ∃ δ : MultiplicityVector n, Target.Usage (δ.extendBinders πs πs') N ∧
        χ ≤ᶜ δ +ᶜ (Multiplicity.sum (fun j => πs' j * (ks j).factor) ·ᶜ χ) ∧
        (∀ j, ks j ≠ .erased → πs' j ≠ .zero) ∧
        ∀ (j : Fin b) (l : Nat) (σ : Shape), ks j = .nested l σ → σ.Fits ρ
  | _, .nil, _, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hN hχ hk hσ _, 0, _, _, _, _, _, _, _, h => by
    cases h
    exact ⟨_, hN, hχ, hk, hσ⟩
  | _, .cons _ _ _ _ hNs, i + 1, _, _, _, _, _, _, _, h => TargetBranches.Usage.get hNs i h

/-- The usage of the branches of a corecursor gives that of each branch. -/
theorem TargetCorecBranches.Usage.get {n : Nat} {δ : MultiplicityVector n} :
    {Ps : TargetCorecBranches n} → TargetCorecBranches.Usage δ Ps → (i : Nat) →
      {o : Resumption} → {b c : Nat} → {πs ϱs : Fin b → Multiplicity} →
      {πs' ϱs' : Fin c → Multiplicity} → {ψ : ResultOwnership Multiplicity c} →
      {ς : Multiplicity} → {P : Target (n + (b + c))} →
      Ps.get i = some (o, ⟨b, c, πs, ϱs, πs', ϱs', ψ, ς, P⟩) →
      ∃ δᵢ : MultiplicityVector n, Target.Usage (δᵢ.extendBinders πs πs') P ∧ δ ≤ᶜ δᵢ ∧
        (o ≠ .none → δ ≤ᶜ δᵢ +ᶜ δ)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hP hδ hr _, 0, _, _, _, _, _, _, _, _, _, _, h => by
    cases h
    exact ⟨_, hP, hδ, hr⟩
  | _, .cons _ _ _ hPs, i + 1, _, _, _, _, _, _, _, _, _, _, h =>
    TargetCorecBranches.Usage.get hPs i h

end Sic.Core
