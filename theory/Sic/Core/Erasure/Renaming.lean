module

public import Sic.Core.Erasure

/-!
# Renaming of the Target Language

The renamings of the variables of the terms of the target language of annex 19 of RFC 36, which the
representation of its variables by de Bruijn indices needs: the RFC names its variables, so that a
term placed under new binders keeps its variables, while here their indices are shifted.
A renaming `α : TargetRen n m` gives each of the `m` variables of a term a variable of the `n`
variables of the renamed term, and a binder of `k` new variables lifts it, `α.lift k`, the new
variables keeping their indices, below those of the scope.

ADE rename the terms of their target language by `wk`, in `Graded/Erasure/Target.agda`, along the
weakenings `Wk`, a data type of the identity, of a new variable and of a lift by one variable, while
a renaming here is any function on the indices, lifted by several variables at once, the number of
the new variables of a branch.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `Wk`, in `Definition/Untyped/NotParametrised.agda`.
/-- A renaming of the `m` variables of a term of the target language into `n` variables. -/
abbrev TargetRen (n m : Nat) : Type := Fin m → Fin n

-- ADE: `lift`, the constructor of `Wk`, in `Definition/Untyped/NotParametrised.agda`.
/-- The renaming `α` under `k` new variables, which keep their indices, below those that `α`
renames. -/
def TargetRen.lift {n m : Nat} (α : TargetRen n m) (k : Nat) : TargetRen (n + k) (m + k) :=
  fun i =>
    if h : (i : Nat) < k then ⟨i, by omega⟩
    else
      have hi := i.isLt
      let y := α ⟨i - k, by omega⟩
      ⟨y + k, by have := y.isLt; omega⟩

-- ADE: none.
/-- The index of a variable renamed by a lift: itself when it is new, and the index that the
renaming gives it, shifted by the new variables, otherwise. -/
theorem TargetRen.lift_val {n m : Nat} (α : TargetRen n m) (k : Nat) (i : Fin (m + k)) :
    (α.lift k i : Nat) =
      if h : (i : Nat) < k then (i : Nat) else (α ⟨i - k, by omega⟩ : Nat) + k := by
  simp only [TargetRen.lift]
  split <;> rfl

-- ADE: `step id`, a weakening of `Wk`, in `Definition/Untyped/NotParametrised.agda`, by one variable.
/-- The renaming of the `n` variables of a term placed under `k` new variables, which shifts their
indices above them. -/
def TargetRen.shift (n k : Nat) : TargetRen (n + k) n :=
  fun x => ⟨x + k, by omega⟩

mutual

-- ADE: `wk`, in `Graded/Erasure/Target.agda`.
/-- The term `M` with its variables renamed by `α`. -/
def Target.rename {n m : Nat} (α : TargetRen n m) : Target m → Target n
  | .var x => .var (α x)
  | .const f qs ps => .const f qs ps
  | .erased => .erased
  | .ctor i Ms => .ctor i (Ms.rename α)
  | .recursor ρ ϱ M Ns => .recursor ρ ϱ (M.rename α) (Ns.rename α)
  | .obs M i ψ ς Ms => .obs (M.rename α) i ψ ς (Ms.rename α)
  | .corec Ms Ps => .corec (Ms.rename α) (Ps.rename α)

-- ADE: none.
/-- The terms with their variables renamed by `α`. -/
def Targets.rename {n m : Nat} (α : TargetRen n m) : Targets m → Targets n
  | .nil => .nil
  | .cons π ϱ M Ms => .cons π ϱ (M.rename α) (Ms.rename α)

-- ADE: none.
/-- The branches of a recursor with the variables of the scope renamed by `α`, under the new
variables of each branch. -/
def TargetBranches.rename {n m : Nat} (α : TargetRen n m) : TargetBranches m → TargetBranches n
  | .nil => .nil
  | .cons a b πs κs πs' ks N Ns => .cons a b πs κs πs' ks (N.rename (α.lift (a + b))) (Ns.rename α)

-- ADE: none.
/-- The branches of a corecursor with the variables of the scope renamed by `α`, under the new
variables of each branch. -/
def TargetCorecBranches.rename {n m : Nat} (α : TargetRen n m) :
    TargetCorecBranches m → TargetCorecBranches n
  | .nil => .nil
  | .cons o b c πs ϱs πs' ϱs' ψ ς P Ps =>
    .cons o b c πs ϱs πs' ϱs' ψ ς (P.rename (α.lift (b + c))) (Ps.rename α)

end

/-! ## Validation -/

-- ADE: none.
/-- The identity lifted is the identity. -/
theorem TargetRen.lift_id {n : Nat} (k : Nat) : TargetRen.lift (n := n) (m := n) id k = id := by
  funext i
  simp only [TargetRen.lift, id]
  split <;> (apply Fin.ext; simp only)
  omega

-- ADE: none.
/-- The composition of two renamings lifted is the composition of their lifts. -/
theorem TargetRen.lift_comp {n m l : Nat} (α : TargetRen n m) (β : TargetRen m l) (k : Nat) :
    α.lift k ∘ β.lift k = TargetRen.lift (α ∘ β) k := by
  funext i
  simp only [TargetRen.lift, Function.comp]
  by_cases h : (i : Nat) < k
  · simp [h]
  · simp only [h, ↓reduceDIte, Nat.add_sub_cancel,
      show ¬ ((β ⟨i - k, by omega⟩ : Nat) + k < k) by omega]

mutual

-- ADE: `wk-id`, in `Graded/Erasure/Target/Properties/Weakening.agda`.
/-- The identity renaming leaves a term unchanged. -/
theorem Target.rename_id {n : Nat} : (M : Target n) → M.rename id = M
  | .var _ | .const .. | .erased => rfl
  | .ctor _ Ms => by rw [Target.rename, Targets.rename_id Ms]
  | .recursor _ _ M Ns => by rw [Target.rename, Target.rename_id M, TargetBranches.rename_id Ns]
  | .obs M _ _ _ Ms => by rw [Target.rename, Target.rename_id M, Targets.rename_id Ms]
  | .corec Ms Ps => by rw [Target.rename, Targets.rename_id Ms, TargetCorecBranches.rename_id Ps]

-- ADE: none.
/-- The identity renaming leaves terms unchanged. -/
theorem Targets.rename_id {n : Nat} : (Ms : Targets n) → Ms.rename id = Ms
  | .nil => rfl
  | .cons _ _ M Ms => by rw [Targets.rename, Target.rename_id M, Targets.rename_id Ms]

-- ADE: none.
/-- The identity renaming leaves the branches of a recursor unchanged. -/
theorem TargetBranches.rename_id {n : Nat} : (Ns : TargetBranches n) → Ns.rename id = Ns
  | .nil => rfl
  | .cons _ _ _ _ _ _ N Ns => by
    rw [TargetBranches.rename, TargetRen.lift_id, Target.rename_id N, TargetBranches.rename_id Ns]

-- ADE: none.
/-- The identity renaming leaves the branches of a corecursor unchanged. -/
theorem TargetCorecBranches.rename_id {n : Nat} : (Ps : TargetCorecBranches n) → Ps.rename id = Ps
  | .nil => rfl
  | .cons _ _ _ _ _ _ _ _ _ P Ps => by
    rw [TargetCorecBranches.rename, TargetRen.lift_id, Target.rename_id P,
      TargetCorecBranches.rename_id Ps]

end

mutual

-- ADE: `wk-comp`, in `Graded/Erasure/Target/Properties/Weakening.agda`.
/-- Two renamings, one after the other, are the renaming by their composition. -/
theorem Target.rename_rename {n m l : Nat} (α : TargetRen n m) (β : TargetRen m l) :
    (M : Target l) → (M.rename β).rename α = M.rename (α ∘ β)
  | .var _ | .const .. | .erased => rfl
  | .ctor _ Ms => by rw [Target.rename, Target.rename, Target.rename, Targets.rename_rename α β Ms]
  | .recursor _ _ M Ns => by
    rw [Target.rename, Target.rename, Target.rename, Target.rename_rename α β M,
      TargetBranches.rename_rename α β Ns]
  | .obs M _ _ _ Ms => by
    rw [Target.rename, Target.rename, Target.rename, Target.rename_rename α β M,
      Targets.rename_rename α β Ms]
  | .corec Ms Ps => by
    rw [Target.rename, Target.rename, Target.rename, Targets.rename_rename α β Ms,
      TargetCorecBranches.rename_rename α β Ps]

-- ADE: none.
/-- Two renamings of terms, one after the other, are the renaming by their composition. -/
theorem Targets.rename_rename {n m l : Nat} (α : TargetRen n m) (β : TargetRen m l) :
    (Ms : Targets l) → (Ms.rename β).rename α = Ms.rename (α ∘ β)
  | .nil => rfl
  | .cons _ _ M Ms => by
    rw [Targets.rename, Targets.rename, Targets.rename, Target.rename_rename α β M,
      Targets.rename_rename α β Ms]

-- ADE: none.
/-- Two renamings of the branches of a recursor, one after the other, are the renaming by their
composition. -/
theorem TargetBranches.rename_rename {n m l : Nat} (α : TargetRen n m) (β : TargetRen m l) :
    (Ns : TargetBranches l) → (Ns.rename β).rename α = Ns.rename (α ∘ β)
  | .nil => rfl
  | .cons _ _ _ _ _ _ N Ns => by
    rw [TargetBranches.rename, TargetBranches.rename, TargetBranches.rename,
      Target.rename_rename, TargetRen.lift_comp, TargetBranches.rename_rename α β Ns]

-- ADE: none.
/-- Two renamings of the branches of a corecursor, one after the other, are the renaming by their
composition. -/
theorem TargetCorecBranches.rename_rename {n m l : Nat} (α : TargetRen n m) (β : TargetRen m l) :
    (Ps : TargetCorecBranches l) → (Ps.rename β).rename α = Ps.rename (α ∘ β)
  | .nil => rfl
  | .cons _ _ _ _ _ _ _ _ _ P Ps => by
    rw [TargetCorecBranches.rename, TargetCorecBranches.rename, TargetCorecBranches.rename,
      Target.rename_rename, TargetRen.lift_comp, TargetCorecBranches.rename_rename α β Ps]

end

/-! ## Casts -/

-- ADE: none.
/-- A term whose scope is cast to an equal one, renamed, is the term renamed by the renaming that
reads each variable at its index in the cast scope: the indices are the same. -/
theorem Target.rename_cast {n m m' : Nat} (h : m = m') (α : TargetRen n m') (M : Target m) :
    (h ▸ M).rename α = M.rename fun x => α (Fin.cast h x) := by
  subst h
  rfl

/-! ## Multiplicities and Requirements -/

-- ADE: none.
/-- The multiplicities at which terms are stored do not depend on their variables. -/
theorem Targets.multiplicities_rename {n m : Nat} (α : TargetRen n m) :
    (Ms : Targets m) → (Ms.rename α).multiplicities = Ms.multiplicities
  | .nil => rfl
  | .cons _ _ _ Ms => by
    simp only [Targets.rename, Targets.multiplicities, Targets.multiplicities_rename α Ms]

-- ADE: none.
/-- The requirements of the positions at which terms are stored do not depend on their variables. -/
theorem Targets.requirements_rename {n m : Nat} (α : TargetRen n m) :
    (Ms : Targets m) → (Ms.rename α).requirements = Ms.requirements
  | .nil => rfl
  | .cons _ _ _ Ms => by
    simp only [Targets.rename, Targets.requirements, Targets.requirements_rename α Ms]

/-! ## Skeletons -/

mutual

-- ADE: none.
/-- The term of a skeleton mentions no variable: a renaming leaves it unchanged. -/
theorem Skeleton.target_rename {n m : Nat} (α : TargetRen n m) :
    (K : Skeleton) → (K.target : Target m).rename α = K.target
  | .empty => rfl
  | .ctor _ ks => by
    simp only [Skeleton.target, Target.rename, Skeleton.targets_rename α ks]

-- ADE: none.
/-- The terms of skeletons mention no variable: a renaming leaves them unchanged. -/
theorem Skeleton.targets_rename {n m : Nat} (α : TargetRen n m) :
    (ks : List Skeleton) → (Skeleton.targets ks : Targets m).rename α = Skeleton.targets ks
  | [] => rfl
  | k :: ks => by
    simp only [Skeleton.targets, Targets.rename, Skeleton.target_rename α k,
      Skeleton.targets_rename α ks]

end

/-! ## Data -/

mutual

-- ADE: none.
/-- Data renamed is data. -/
theorem Target.IsData.rename {n m : Nat} (α : TargetRen n m) :
    {M : Target m} → M.IsData → (M.rename α).IsData
  | _, .erased => .erased
  | _, .ctor h => .ctor (h.rename α)

-- ADE: none.
/-- Terms that are data, renamed, are data. -/
theorem Targets.IsData.rename {n m : Nat} (α : TargetRen n m) :
    {Ms : Targets m} → Ms.IsData → (Ms.rename α).IsData
  | _, .nil => .nil
  | _, .cons h hs => .cons (h.rename α) (hs.rename α)

end

end Sic.Core
