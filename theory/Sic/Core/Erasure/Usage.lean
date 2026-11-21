module

public import Sic.Core.Erasure
public import Sic.Grading.MultiplicityVector

/-!
# Usage of the Target Language

The usage of the target language of annex 19 of RFC 36, `ν ⊢ M ▶`: the term `M` reads each of its
variables at most as the multiplicity that `ν` gives it allows, as the evaluation of annex 20 runs
it, so that the conservation of the bindings of the multiplicity `1` is stated on it.
Each binder and each position carries its multiplicity, so that the rules read them; a position
is evaluated once, and its value is then read as its multiplicity allows, so that the position
counts the reads of its term that many times, and a position of the multiplicity `0`, whose value
is never read, holds data, which reads no variable and binds none: a closure that it holds
would never release a linear variable, read by its term or bound inside it, and the multiplicity
`0` would hide the reads of the others; the term of a recursor of the multiplicity `0` likewise.
A recursor evaluates its term once and runs a branch, whose recursive results each run the
recursor again, and a corecursor evaluates its state once and captures its scope in a closure, each
observation of which runs a branch, and a resumption captures it again.
ADE have no such judgment: their erasure keeps no count of the uses.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- `ν • π̄ • π̄'`: the vector `ν` extended by the multiplicities `πs` of `a` new variables, then by
the multiplicities `πs'` of `b` new variables, the first one first, so that the last one has the
index `0`, as the binders of the branches number them.
RFC: `\bullet_\nu` -/
def _root_.Sic.Grading.MultiplicityVector.extendBinders {n a b : Nat} (ν : MultiplicityVector n)
    (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity) : MultiplicityVector (n + (a + b)) :=
  fun i =>
    if h₁ : (i : Nat) < b then πs' ⟨b - 1 - i, by omega⟩
    else if h₂ : (i : Nat) < a + b then πs ⟨a - 1 - (i - b), by omega⟩
    else ν ⟨i - (a + b), by omega⟩

mutual

-- ADE: none.
/-- `ν ⊢ M ▶`: the term `M` of the target language reads its variables as `ν` allows. -/
inductive Target.Usage : {n : Nat} → MultiplicityVector n → Target n → Prop where
  /-- A variable reads itself once.
  RFC: `\mathsf{usage}_M.x` -/
  | var {n : Nat} (x : Fin n) : Target.Usage (MultiplicityVector.update 𝟘ᵛ x .one) (.var x)
  /-- A constant reads no variable.
  RFC: `\mathsf{usage}_M.f` -/
  | const {n : Nat} (f : Name) (qs : List Quality) (ps : List Grade) :
      Target.Usage 𝟘ᵛ (.const f qs ps : Target n)
  /-- `↯` reads no variable.
  RFC: `\mathsf{usage}_M.\text{↯}` -/
  | erased {n : Nat} : Target.Usage 𝟘ᵛ (.erased : Target n)
  /-- A constructor reads the variables of its fields.
  RFC: `\mathsf{usage}_M.c` -/
  | ctor {n : Nat} {ν : MultiplicityVector n} {i : Nat} {Ms : Targets n}
      (hMs : Targets.Usage ν Ms) : Target.Usage ν (.ctor i Ms)
  /-- A recursor reads the variables of its term as its multiplicity `ρ` allows, and those of its
  branches as `χ` allows; a term of the multiplicity `0` is data.
  RFC: `\mathsf{usage}_M.\mathsf{rec}` -/
  | recursor {n : Nat} {ν χ : MultiplicityVector n} {ρ ϱ : Multiplicity} {M : Target n}
      {Ns : TargetBranches n} (hM : Target.Usage ν M) (hz : ρ = .zero → M.IsData)
      (hNs : TargetBranches.Usage ρ χ Ns) : Target.Usage ((ρ ·ᶜ ν) +ᶜ χ) (.recursor ρ ϱ M Ns)
  /-- An observation reads the variables of its term and of its arguments once.
  RFC: `\mathsf{usage}_M.d` -/
  | obs {n : Nat} {ν₁ ν₂ : MultiplicityVector n} {M : Target n} {i c : Nat}
      {ψ : ResultOwnership Multiplicity c}
      {ς : Multiplicity} {Ms : Targets n} (hM : Target.Usage ν₁ M)
      (hMs : Targets.Usage ν₂ Ms) : Target.Usage (ν₁ +ᶜ ν₂) (.obs M i ψ ς Ms)
  /-- A corecursor reads the variables of its state once, and those of its branches as `δ` allows.
  RFC: `\mathsf{usage}_M.\mathsf{corec}` -/
  | corec {n : Nat} {ν δ : MultiplicityVector n} {Ms : Targets n} {Ps : TargetDestructorBranches n}
      (hMs : Targets.Usage ν Ms) (hPs : TargetDestructorBranches.Usage δ Ps) :
      Target.Usage (ν +ᶜ δ) (.corec Ms Ps)
  /-- A term may be given multiplicities lower than its reads.
  RFC: `\mathsf{usage}_M.\mathsf{sub}` -/
  | sub {n : Nat} {ν μ : MultiplicityVector n} {M : Target n} (h : Target.Usage ν M)
      (hle : μ ≤ᶜ ν) : Target.Usage μ M

-- ADE: none.
/-- `ν ⊢ M̄ ▶`: the terms `M̄` read their variables as `ν` allows, the reads of each added. -/
inductive Targets.Usage : {n : Nat} → MultiplicityVector n → Targets n → Prop where
  /-- No term reads no variable.
  RFC: `\mathsf{usage}_{\bar M}.\varepsilon` -/
  | nil {n : Nat} : Targets.Usage 𝟘ᵛ (.nil : Targets n)
  /-- The first term, read as its multiplicity `π` allows, and the others; a term of the
  multiplicity `0` is data.
  RFC: `\mathsf{usage}_{\bar M}.{,}` -/
  | cons {n : Nat} {ν₁ ν₂ : MultiplicityVector n} {π ϱ : Multiplicity} {M : Target n}
      {Ms : Targets n} (hM : Target.Usage ν₁ M) (hz : π = .zero → M.IsData)
      (hMs : Targets.Usage ν₂ Ms) : Targets.Usage ((π ·ᶜ ν₁) +ᶜ ν₂) (.cons π ϱ M Ms)

-- ADE: `natrec-no-nrₘ`, in `Graded/Usage.agda`, for the bound of the uses of the branches.
/-- `ρ; χ ⊢ N̄ ▶`: the branches `N̄` of a recursor of the multiplicity `ρ` read the variables of the scope as `χ` allows: each
branch reads them as `δ` allows and its new variables as their binders allow, and each recursive
result that it computes runs the recursor again, which reads them as `χ` allows again, and is read
as its binder allows, so that `χ` bounds `δ` plus `χ` times the multiplicity of the binder of each
result that the branch computes times the factor of the result, an erased result running no
recursion and a nested result running the branches of its corecursor, which read the scope as often
as its shape allows; a result that the branch computes has a multiplicity other than `0`, since the
recursion that computes it reads the field, whose uses a result never read would not count.
The shape of each nested result fits the recursor of the multiplicity `ρ`, so that its corecursor
reads the arguments of its observations as the observations allow. -/
inductive TargetBranches.Usage :
    {n : Nat} → Multiplicity → MultiplicityVector n → TargetBranches n → Prop where
  /-- No branch.
  RFC: `\mathsf{usage}_{\bar N}.\varepsilon` -/
  | nil {n : Nat} {ρ : Multiplicity} {χ : MultiplicityVector n} : TargetBranches.Usage ρ χ .nil
  /-- The first branch and the others.
  RFC: `\mathsf{usage}_{\bar N}.{,}` -/
  | cons {n a b : Nat} {ρ : Multiplicity} {χ δ : MultiplicityVector n}
      {πs κs : Fin a → Multiplicity} {πs' : Fin b → Multiplicity} {ks : Fin b → RecursiveResult}
      {N : Target (n + (a + b))} {Ns : TargetBranches n}
      (hN : Target.Usage (δ.extendBinders πs πs') N)
      (hχ : χ ≤ᶜ δ +ᶜ (Multiplicity.sum (fun j => πs' j * (ks j).factor) ·ᶜ χ))
      (hk : ∀ j, ks j ≠ .erased → πs' j ≠ .zero)
      (hσ : ∀ (j : Fin b) (l : Nat) (σ : Shape), ks j = .nested l σ → σ.Fits ρ)
      (hNs : TargetBranches.Usage ρ χ Ns) :
      TargetBranches.Usage ρ χ (.cons a b πs κs πs' ks N Ns)

-- ADE: none.
/-- `δ ⊢ P̄ ▶`: the branches `P̄` of a corecursor, which its closure captures with the scope, read
the variables of the scope as `δ` allows: an observation runs one branch, which reads them as `δᵢ`
allows and its new variables as their binders allow, and a branch that resumes the corecursor
captures the scope again in a new closure, so that `δ` bounds `δᵢ`, and `δᵢ` plus `δ` for such a
branch. -/
inductive TargetDestructorBranches.Usage : {n : Nat} → MultiplicityVector n →
    TargetDestructorBranches n →
    Prop where
  /-- No branch.
  RFC: `\mathsf{usage}_{\bar P}.\varepsilon` -/
  | nil {n : Nat} {δ : MultiplicityVector n} : TargetDestructorBranches.Usage δ .nil
  /-- The first branch and the others.
  RFC: `\mathsf{usage}_{\bar P}.{,}` -/
  | cons {n b c : Nat} {δ δᵢ : MultiplicityVector n} {o : Resumption}
      {πs ϱs : Fin b → Multiplicity} {πs' ϱs' : Fin c → Multiplicity}
      {ψ : ResultOwnership Multiplicity c}
      {ς : Multiplicity} {P : Target (n + (b + c))} {Ps : TargetDestructorBranches n}
      (hP : Target.Usage (δᵢ.extendBinders πs πs') P) (hδ : δ ≤ᶜ δᵢ)
      (hr : o ≠ .none → δ ≤ᶜ δᵢ +ᶜ δ) (hPs : TargetDestructorBranches.Usage δ Ps) :
      TargetDestructorBranches.Usage δ (.cons o b c πs ϱs πs' ϱs' ψ ς P Ps)

end

/-! ## Properties -/

mutual

-- ADE: none.
/-- Data reads no variable. -/
theorem Target.IsData.usage {n : Nat} {M : Target n} : M.IsData → Target.Usage 𝟘ᵛ M
  | .erased => .erased
  | .ctor h => .ctor h.usage

-- ADE: none.
/-- Terms that are data read no variable. -/
theorem Targets.IsData.usage {n : Nat} {Ms : Targets n} : Ms.IsData → Targets.Usage 𝟘ᵛ Ms
  | .nil => .nil
  | .cons (π := π) (ϱ := ϱ) hM hMs => by
    have h := Targets.Usage.cons (π := π) (ϱ := ϱ) hM.usage (fun _ => hM) hMs.usage
    rwa [(MultiplicityVector.module Multiplicity.modality).smul_zero,
      (MultiplicityVector.module Multiplicity.modality).zero_add] at h

end

end Sic.Core
