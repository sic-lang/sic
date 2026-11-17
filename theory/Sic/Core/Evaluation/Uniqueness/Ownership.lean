module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Evaluation

/-!
# Inversions of the Ownership

The inversions of the ownership of the target language, for the proof of the invariant of the
uniqueness at run time: what the ownership of a term of each form gives, and the ownership of the
term of a position, of a branch of a recursor and of a branch of a corecursor.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

namespace Target.Ownership

variable {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n}

/-- A variable has an ownership below the one that `φ` gives it. -/
theorem var_inv {x : Fin n} : {o : Multiplicity} → {M : Target n} →
    Target.Ownership Ω φ o M → M = .var x → o ≤ φ x
  | _, _, .var _, h => by
    cases h
    exact Multiplicity.le_refl' _
  | _, _, .sub h hle, hM => Multiplicity.le_trans' _ _ _ hle (var_inv h hM)
  | _, _, .const .., h | _, _, .erased _, h | _, _, .ctor _, h
  | _, _, .recursor .., h | _, _, .obs .., h | _, _, .corec .., h => nomatch h

/-- A constant has an ownership below the one that `Ω` gives it. -/
theorem const_inv {f : Name} {qs : List Quality} {ps : List Grade} :
    {o : Multiplicity} → {M : Target n} →
      Target.Ownership Ω φ o M → M = .const f qs ps → o ≤ Ω f
  | _, _, .const .., h => by
    cases h
    exact Multiplicity.le_refl' _
  | _, _, .sub h hle, hM => Multiplicity.le_trans' _ _ _ hle (const_inv h hM)
  | _, _, .var _, h | _, _, .erased _, h | _, _, .ctor _, h
  | _, _, .recursor .., h | _, _, .obs .., h | _, _, .corec .., h => nomatch h

/-- The fields of a constructor satisfy the requirements of their positions. -/
theorem ctor_inv {i : Nat} {Ms : Targets n} : {o : Multiplicity} → {M : Target n} → Target.Ownership Ω φ o M → M = .ctor i Ms →
      ∃ os, Targets.Ownership Ω φ os Ms
  | _, _, .ctor h, hM => by
    cases hM
    exact ⟨_, h⟩
  | _, _, .sub h _, hM => ctor_inv h hM
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased _, h
  | _, _, .recursor .., h | _, _, .obs .., h | _, _, .corec .., h => nomatch h

/-- A recursor has an ownership below that of its branches, checked with the ownership of its term
times the requirement of its recursion. -/
theorem recursor_inv {ρ ϱ : Multiplicity} {M : Target n} {Ns : TargetBranches n} :
    {o : Multiplicity} → {M' : Target n} →
      Target.Ownership Ω φ o M' → M' = .recursor ρ ϱ M Ns →
      ∃ o₁ o' ς χ, Target.Ownership Ω φ o₁ M ∧ TargetBranches.Ownership Ω φ (o₁ * ϱ) o' ς χ Ns ∧
        o ≤ o'
  | _, _, .recursor hM hNs, h => by
    cases h
    exact ⟨_, _, _, _, hM, hNs, Multiplicity.le_refl' _⟩
  | _, _, .sub h hle, hM =>
    have ⟨o₁, o', ς, χ, h₁, h₂, hle'⟩ := recursor_inv h hM
    ⟨o₁, o', ς, χ, h₁, h₂, Multiplicity.le_trans' _ _ _ hle hle'⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased _, h | _, _, .ctor _, h
  | _, _, .obs .., h | _, _, .corec .., h => nomatch h

/-- An observation has an ownership below that of its term times the value of the ownership of the
result of its destructor. -/
theorem obs_inv {M : Target n} {i c : Nat} {ψ : ResultOwnership Multiplicity c}
    {ς : Multiplicity} {Ms : Targets n} : {o : Multiplicity} → {M' : Target n} → Target.Ownership Ω φ o M' → M' = .obs M i ψ ς Ms →
      ∃ o₁ v os, Target.Ownership Ω φ o₁ M ∧ Targets.Ownership Ω φ os Ms ∧
        ψ.value os = some v ∧ ς ≤ o₁ ∧ o ≤ o₁ * v
  | _, _, .obs hM hMs hv hς, h => by
    cases h
    exact ⟨_, _, _, hM, hMs, hv, hς, Multiplicity.le_refl' _⟩
  | _, _, .sub h hle, hM =>
    have ⟨o₁, v, os, h₁, h₂, hv, hς, hle'⟩ := obs_inv h hM
    ⟨o₁, v, os, h₁, h₂, hv, hς, Multiplicity.le_trans' _ _ _ hle hle'⟩
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased _, h | _, _, .ctor _, h
  | _, _, .recursor .., h | _, _, .corec .., h => nomatch h

/-- The state of a corecursor satisfies the requirements of its positions, and its branches have
their ownerships. -/
theorem corec_inv {Ms : Targets n} {Ps : TargetCorecBranches n} : {o : Multiplicity} → {M' : Target n} → Target.Ownership Ω φ o M' → M' = .corec Ms Ps →
      ∃ os, Targets.Ownership Ω φ os Ms ∧ TargetCorecBranches.Ownership Ω φ Ps
  | _, _, .corec hMs hPs, h => by
    cases h
    exact ⟨_, hMs, hPs⟩
  | _, _, .sub h _, hM => corec_inv h hM
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased _, h | _, _, .ctor _, h
  | _, _, .recursor .., h | _, _, .obs .., h => nomatch h

end Target.Ownership

namespace Target.Ownership

/-- A constructor builds a new value, whose ownership is at most `1`. -/
theorem ctor_le {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} {i : Nat}
    {Ms : Targets n} : {o : Multiplicity} → {M : Target n} → Target.Ownership Ω φ o M →
      M = .ctor i Ms → o ≤ .one
  | _, _, .ctor _, _ => Multiplicity.le_refl' _
  | _, _, .sub h hle, hM => Multiplicity.le_trans' _ _ _ hle (ctor_le h hM)
  | _, _, .var _, h | _, _, .const .., h | _, _, .erased _, h
  | _, _, .recursor .., h | _, _, .obs .., h | _, _, .corec .., h => nomatch h

end Target.Ownership

/-- The ownership of each term of a list satisfies the requirement of its position. -/
theorem Targets.Ownership.get {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} :
    {os : List Multiplicity} → {Ms : Targets n} → Targets.Ownership Ω φ os Ms → {k : Nat} →
      {ϱ : Multiplicity} → Ms.requirements[k]? = some ϱ → ∃ o, os[k]? = some o ∧ ϱ ≤ o
  | _, _, .nil, _, _, h => by simp [Targets.requirements] at h
  | _, _, .cons _ hϱ _, 0, _, h => by
    cases h
    exact ⟨_, rfl, hϱ⟩
  | _, _, .cons _ _ hMs, k + 1, _, h => hMs.get (k := k) (by simpa [Targets.requirements] using h)

/-- Terms that have ownerships have as many ownerships. -/
theorem Targets.Ownership.length {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} :
    {os : List Multiplicity} → {Ms : Targets n} → Targets.Ownership Ω φ os Ms →
      os.length = Ms.multiplicities.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ hMs => congrArg (· + 1) hMs.length

/-- The ownership of the branches of a recursor gives that of each branch, with the ownership of the
variable of each recursive result, and the ownerships and the requirements of the shape of each
nested result. -/
theorem TargetBranches.Ownership.get {Ω : Name → Multiplicity} {n : Nat}
    {φ : MultiplicityVector n} {o o' ς χ : Multiplicity} : {Ns : TargetBranches n} →
    TargetBranches.Ownership Ω φ o o' ς χ Ns → (i : Nat) → {a b : Nat} →
      {πs κs : Fin a → Multiplicity} → {πs' : Fin b → Multiplicity} →
      {ks : Fin b → RecursiveResult} → {N : Target (n + (a + b))} →
      Ns.get i = some ⟨a, b, πs, κs, πs', ks, N⟩ →
      Target.Ownership Ω
        (φ.extendBinders (fun l => o * κs l) (fun j => (ks j).ownership o' * πs' j)) o' N ∧
      ∀ (j : Fin b) (l : Fin a) (σ : Shape), ks j = .nested l σ →
        σ.Uniform ς χ ∧ σ.Requires o ς ∧ o ≤ ς * (o * κs l)
  | _, .nil, _, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hN _ hks _, 0, _, _, _, _, _, _, _, h => by
    cases h
    exact ⟨hN, hks⟩
  | _, .cons _ _ _ hNs, i + 1, _, _, _, _, _, _, _, h => TargetBranches.Ownership.get hNs i h

/-- The ownership of the branches of a corecursor gives that of each branch. -/
theorem TargetCorecBranches.Ownership.get {Ω : Name → Multiplicity} {n : Nat}
    {φ : MultiplicityVector n} : {Ps : TargetCorecBranches n} →
    TargetCorecBranches.Ownership Ω φ Ps → (i : Nat) → {k : Resumption} → {b c : Nat} →
      {πs ϱs : Fin b → Multiplicity} → {πs' ϱs' : Fin c → Multiplicity} →
      {ψ : ResultOwnership Multiplicity c} → {ς : Multiplicity} → {P : Target (n + (b + c))} →
      Ps.get i = some (k, ⟨b, c, πs, ϱs, πs', ϱs', ψ, ς, P⟩) →
      (∀ (os : Fin c → Multiplicity) (v : Multiplicity), (∀ l, ϱs' l ≤ os l) →
        (k = .none ∧ ψ.value (List.ofFn os) = some v ∨ k ≠ .none ∧ v = .one) →
        Target.Ownership Ω (MultiplicityVector.extendBinders (ς ·ᶜ φ)
          (fun l => ς * ϱs l * πs l) (fun l => os l * πs' l)) v P) ∧
      (k ≠ .none → ∃ χ, ψ = ⟨some χ, fun _ => none⟩)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hP hψ _, 0, _, _, _, _, _, _, _, _, _, _, h => by
    cases h
    exact ⟨hP, hψ⟩
  | _, .cons _ _ hPs, i + 1, _, _, _, _, _, _, _, _, _, _, h =>
    TargetCorecBranches.Ownership.get hPs i h

end Sic.Core
