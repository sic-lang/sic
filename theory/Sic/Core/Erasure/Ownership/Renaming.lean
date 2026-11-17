module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Erasure.Renaming

/-!
# Ownership of the Renamed Terms of the Target Language

The ownership of the target language of `Sic/Core/Erasure/Ownership.lean` is kept by the renamings
of its variables: a term renamed by `α` has the ownership of the term, given ownerships of its new
variables that give each variable that `α` renames the ownership of the variable, which the
representation of the variables by de Bruijn indices needs, since the RFC names its variables.

ADE have no ownership.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- The ownerships of a branch at a variable renamed by `α` lifted are those of the branch before
the renaming, when the ownerships of the scope agree along `α`. -/
theorem _root_.Sic.Grading.MultiplicityVector.extendBinders_lift {n m a b : Nat}
    (α : TargetRen n m) {φ' : MultiplicityVector n} {φ : MultiplicityVector m}
    (hφ : ∀ x, φ' (α x) = φ x) (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity)
    (i : Fin (m + (a + b))) :
    φ'.extendBinders πs πs' (α.lift (a + b) i) = φ.extendBinders πs πs' i := by
  have hv := TargetRen.lift_val α (a + b) i
  by_cases hab : (i : Nat) < a + b
  · have he : α.lift (a + b) i = ⟨i, by omega⟩ := by
      apply Fin.ext
      rw [hv]
      simp [hab]
    rw [he]
    simp only [MultiplicityVector.extendBinders, hab, ↓reduceDIte]
  · have he : α.lift (a + b) i = ⟨(α ⟨i - (a + b), by omega⟩ : Nat) + (a + b),
        by have := (α ⟨i - (a + b), by omega⟩).isLt; omega⟩ := by
      apply Fin.ext
      rw [hv]
      simp [hab]
    rw [he]
    simp only [MultiplicityVector.extendBinders, show ¬ (i : Nat) < b by omega, hab,
      show ¬ ((α ⟨i - (a + b), by omega⟩ : Nat) + (a + b) < b) by omega,
      show ¬ ((α ⟨i - (a + b), by omega⟩ : Nat) + (a + b) < a + b) by omega, ↓reduceDIte,
      Nat.add_sub_cancel, Fin.eta]
    exact hφ _

/-! ## Renaming -/

mutual

-- ADE: none.
/-- A term renamed by `α` has the ownership of the term, given ownerships `φ'` of its variables that
agree with `φ` along `α`. -/
theorem Target.Ownership.rename {Ω : Name → Multiplicity} {n m : Nat} (α : TargetRen n m)
    {φ' : MultiplicityVector n} {φ : MultiplicityVector m} (hφ : ∀ x, φ' (α x) = φ x) :
    {o : Multiplicity} → {M : Target m} → Target.Ownership Ω φ o M →
      Target.Ownership Ω φ' o (M.rename α)
  | _, _, .var x => by
    rw [← hφ x]
    exact .var _
  | _, _, .const .. => .const ..
  | _, _, .erased o => .erased o
  | _, _, .ctor hMs => .ctor (hMs.rename α hφ)
  | _, _, .recursor hM hNs => .recursor (hM.rename α hφ) (hNs.rename α hφ)
  | _, _, .obs hM hMs hv hς => .obs (hM.rename α hφ) (hMs.rename α hφ) hv hς
  | _, _, .corec hMs hPs => .corec (hMs.rename α hφ) (hPs.rename α hφ)
  | _, _, .sub h hle => .sub (h.rename α hφ) hle

-- ADE: none.
/-- Terms renamed by `α` have the ownerships of the terms, given ownerships `φ'` of their variables
that agree with `φ` along `α`. -/
theorem Targets.Ownership.rename {Ω : Name → Multiplicity} {n m : Nat} (α : TargetRen n m)
    {φ' : MultiplicityVector n} {φ : MultiplicityVector m} (hφ : ∀ x, φ' (α x) = φ x) :
    {os : List Multiplicity} → {Ms : Targets m} → Targets.Ownership Ω φ os Ms →
      Targets.Ownership Ω φ' os (Ms.rename α)
  | _, _, .nil => .nil
  | _, _, .cons hM hϱ hMs => .cons (hM.rename α hφ) hϱ (hMs.rename α hφ)

-- ADE: none.
/-- The branches of a recursor renamed by `α` have the ownerships of the branches, given ownerships
`φ'` of the variables of the scope that agree with `φ` along `α`. -/
theorem TargetBranches.Ownership.rename {Ω : Name → Multiplicity} {n m : Nat} (α : TargetRen n m)
    {φ' : MultiplicityVector n} {φ : MultiplicityVector m} (hφ : ∀ x, φ' (α x) = φ x) :
    {o o' ς χ : Multiplicity} → {Ns : TargetBranches m} → TargetBranches.Ownership Ω φ o o' ς χ Ns →
      TargetBranches.Ownership Ω φ' o o' ς χ (Ns.rename α)
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons hN hN' hks hNs =>
    .cons (hN.rename _ (MultiplicityVector.extendBinders_lift α hφ _ _))
      (hN'.rename _ (MultiplicityVector.extendBinders_lift α
        (fun x => congrArg (_ * ·) (hφ x)) _ _))
      hks (hNs.rename α hφ)

-- ADE: none.
/-- The branches of a corecursor renamed by `α` have the ownerships of the branches, given
ownerships `φ'` of the variables of the scope that agree with `φ` along `α`. -/
theorem TargetCorecBranches.Ownership.rename {Ω : Name → Multiplicity} {n m : Nat}
    (α : TargetRen n m) {φ' : MultiplicityVector n} {φ : MultiplicityVector m}
    (hφ : ∀ x, φ' (α x) = φ x) :
    {Ps : TargetCorecBranches m} → TargetCorecBranches.Ownership Ω φ Ps →
      TargetCorecBranches.Ownership Ω φ' (Ps.rename α)
  | _, .nil => .nil
  | _, .cons hP hψ hPs =>
    .cons (fun os v hos hv => (hP os v hos hv).rename _
        (MultiplicityVector.extendBinders_lift α (fun x => congrArg (_ * ·) (hφ x)) _ _))
      hψ (hPs.rename α hφ)

end

end Sic.Core
