module

public import Sic.Core.Erasure.Nested
public import Sic.Core.Erasure.Usage.Renaming

/-!
# Usage of the Corecursors of the Nested Results

The branches that the evaluation builds for the corecursor of a nested result, in
`Sic/Core/Erasure/Nested.lean`, read the variables of the scope as the factor of the shape times the
vector `χ` of the branches of the recursor allows, when the shape fits the recursor: an observation
of the corecursor runs one built branch, which runs the recursor once on the observation of the
field, or captures the scope in the corecursor of the next lifting, whose observations read it as
its factor allows, and the multiplicity of the destructor scales these reads, so that the meet of
these factors, the factor of the shape, bounds them all.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

namespace MultiplicityVector

-- ADE: none.
/-- The vector of the scope shifted under `a + b` new variables is the vector extended by `0` for
each of them. -/
theorem rename_shift {n a b : Nat} (ν : MultiplicityVector n) :
    MultiplicityVector.rename (TargetRen.shift n (a + b)) ν =
      ν.extendBinders (fun _ : Fin a => .zero) (fun _ : Fin b => .zero) :=
  funext fun i => by
    have hs : ∀ x : Fin n, (TargetRen.shift n (a + b) x : Nat) = x + (a + b) := fun _ => rfl
    by_cases hi : (i : Nat) < a + b
    · have h0 : (fun x : Fin n => if TargetRen.shift n (a + b) x = i then ν x else .zero) =
          fun _ => .zero := funext fun x => by
        have : TargetRen.shift n (a + b) x ≠ i :=
          fun e => by have := congrArg Fin.val e; rw [hs] at this; omega
        simp only [this, ↓reduceIte]
      rw [MultiplicityVector.rename, h0, Multiplicity.sum_zero]
      simp only [MultiplicityVector.extendBinders, hi, ↓reduceDIte]
      split <;> rfl
    · rw [MultiplicityVector.rename, Multiplicity.sum_single _ ⟨(i : Nat) - (a + b), by omega⟩
        fun x hx => by
          have : TargetRen.shift n (a + b) x ≠ i :=
            fun e => hx (Fin.ext (by have := congrArg Fin.val e; rw [hs] at this; simp only; omega))
          simp only [this, ↓reduceIte]]
      have : TargetRen.shift n (a + b) ⟨(i : Nat) - (a + b), by omega⟩ = i :=
        Fin.ext (by rw [hs]; simp only; omega)
      simp only [this, ↓reduceIte, MultiplicityVector.extendBinders,
        show ¬ (i : Nat) < b by omega, hi, ↓reduceDIte]

/-- The vector of the corecursor of a nested result reads the field `factor(σ) · ρ` times. -/
theorem nested_zero {n : Nat} (f ρ : Multiplicity) (χ : MultiplicityVector n) :
    (f ·ᶜ ((ρ ·ᶜ MultiplicityVector.update 𝟘ᵛ 0 .one) +ᶜ
      MultiplicityVector.rename (TargetRen.shift n 1) χ)) 0 = f * ρ := by
  show f * (ρ * MultiplicityVector.update 𝟘ᵛ 0 .one 0 +
    MultiplicityVector.rename (TargetRen.shift n (0 + 1)) χ 0) = f * ρ
  rw [rename_shift (a := 0) (b := 1)]
  simp [MultiplicityVector.update, Sic.Math.Vector.update, MultiplicityVector.extendBinders]
  cases f <;> cases ρ <;> rfl

/-- The vector of the corecursor of a nested result reads the scope `factor(σ) · χ`. -/
theorem nested_succ {n : Nat} (f ρ : Multiplicity) (χ : MultiplicityVector n) (x : Fin n) :
    (f ·ᶜ ((ρ ·ᶜ MultiplicityVector.update 𝟘ᵛ 0 .one) +ᶜ
      MultiplicityVector.rename (TargetRen.shift n 1) χ)) x.succ = f * χ x := by
  show f * (ρ * MultiplicityVector.update 𝟘ᵛ 0 .one x.succ +
    MultiplicityVector.rename (TargetRen.shift n (0 + 1)) χ (TargetRen.shift n (0 + 1) x)) =
    f * χ x
  rw [rename_shift (a := 0) (b := 1), extendBinders_shift]
  simp [MultiplicityVector.update, Sic.Math.Vector.update, Fin.succ_ne_zero]
  cases f <;> cases ρ <;> rfl

end MultiplicityVector

-- ADE: none.
/-- The variables as terms read each variable as the sum of the multiplicities of the positions that
hold it. -/
theorem Targets.Usage.ofVars {n : Nat} : {c : Nat} → (πs ϱs : Fin c → Multiplicity) →
    (xs : Fin c → Fin n) →
      Targets.Usage (MultiplicityVector.rename xs πs) (Targets.ofVars πs ϱs xs)
  | 0, πs, _, xs => by
    have h : MultiplicityVector.rename xs πs = 𝟘ᵛ := funext fun _ => rfl
    rw [h]
    exact .nil
  | c + 1, πs, ϱs, xs => by
    have hs := Targets.Usage.ofVars (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ)
    have hM : Target.Usage (if πs 0 = .zero then 𝟘ᵛ else MultiplicityVector.update 𝟘ᵛ (xs 0) .one)
        (if πs 0 = .zero then .erased else .var (xs 0)) := by
      split
      · exact .erased
      · exact .var _
    have h := Targets.Usage.cons (π := πs 0) (ϱ := ϱs 0) hM
      (fun h0 => by simp only [h0, ↓reduceIte]; exact .erased) hs
    have he : (πs 0 ·ᶜ (if πs 0 = .zero then 𝟘ᵛ else MultiplicityVector.update 𝟘ᵛ (xs 0) .one)) +ᶜ
        MultiplicityVector.rename (fun k => xs k.succ) (fun k => πs k.succ) =
          MultiplicityVector.rename xs πs := funext fun y => by
      show πs 0 * (if πs 0 = .zero then 𝟘ᵛ else MultiplicityVector.update 𝟘ᵛ (xs 0) .one) y +
          Multiplicity.sum (fun k => if xs k.succ = y then πs k.succ else .zero) =
        (if xs 0 = y then πs 0 else .zero) +
          Multiplicity.sum (fun k => if xs k.succ = y then πs k.succ else .zero)
      congr 1
      by_cases h0 : πs 0 = .zero
      · simp only [h0, ↓reduceIte]
        split <;> rfl
      · simp only [h0, ↓reduceIte, Sic.Math.Vector.update]
        by_cases hy : xs 0 = y
        · simp only [hy, ↓reduceIte]
          cases πs 0 <;> rfl
        · simp only [Ne.symm hy, hy, ↓reduceIte]
          cases πs 0 <;> rfl
    exact he ▸ h

namespace MultiplicityVector

-- ADE: none.
/-- The arguments of a built branch, as variables, read each argument as its multiplicity and no
variable of the scope. -/
theorem rename_argVar {m c : Nat} (πs : Fin c → Multiplicity) :
    MultiplicityVector.rename (Shape.argVar m c) πs =
      MultiplicityVector.extendBinders (𝟘ᵛ : MultiplicityVector m) (fun _ : Fin 0 => .zero) πs :=
  funext fun i => by
    have hv : ∀ k : Fin c, (Shape.argVar m c k : Nat) = c - 1 - k := fun _ => rfl
    by_cases hi : (i : Nat) < c
    · rw [MultiplicityVector.rename, Multiplicity.sum_single _ ⟨c - 1 - i, by omega⟩
        fun k hk => by
          have : Shape.argVar m c k ≠ i :=
            fun e => hk (Fin.ext (by have := congrArg Fin.val e; rw [hv] at this; simp only; omega))
          simp only [this, ↓reduceIte]]
      have : Shape.argVar m c ⟨c - 1 - i, by omega⟩ = i := Fin.ext (by rw [hv]; simp only; omega)
      simp only [this, ↓reduceIte, MultiplicityVector.extendBinders, hi, ↓reduceDIte]
    · have h0 : (fun k : Fin c => if Shape.argVar m c k = i then πs k else .zero) =
          fun _ => .zero := funext fun k => by
        have : Shape.argVar m c k ≠ i :=
          fun e => by have := congrArg Fin.val e; rw [hv] at this; omega
        simp only [this, ↓reduceIte]
      rw [MultiplicityVector.rename, h0, Multiplicity.sum_zero]
      simp only [MultiplicityVector.extendBinders, hi, ↓reduceDIte]
      split <;> rfl

end MultiplicityVector

mutual

-- ADE: none.
/-- The branches built from a shape that fits the recursor of the multiplicity `ρ` read the variables
of the path `M` as `ρ` times its reads, and those of the scope of the branches of the recursor as
`χ`, at most as many times as the factor of the shape: the branch of each destructor observed at run
time runs the recursor once on the observation of the path, or on the term of the skeleton of the
motive when `ρ` is `0`, or captures it in the corecursor of the next lifting, whose factor bounds
its reads in turn, and the factor of the shape is the meet of these factors, each times the
multiplicity of its destructor. -/
theorem TargetCorecBranches.Usage.branches {ρ ϱ : Multiplicity} :
    {m : Nat} → {ν χ : MultiplicityVector m} → {M : Target m} → {Ns : TargetBranches m} →
      (σ : Shape) → {π : Multiplicity} → Target.Usage ν M → TargetBranches.Usage ρ χ Ns →
        σ.Fits ρ → (σ ≠ .nil → π ≤ σ.factor) →
          TargetCorecBranches.Usage (π ·ᶜ ((ρ ·ᶜ ν) +ᶜ χ)) (σ.branches ρ ϱ M Ns)
  | _, _, _, _, _, .nil, _, _, _, _, _ => .nil
  | m, ν, χ, M, Ns, .cons i c ρᵢ πs ϱs πs' ϱs' ψ ς ψ₀ ς₀ next rest, π, hM, hNs,
      ⟨hfit, hnext, hrest⟩, hπ => by
    have hπ := hπ Shape.noConfusion
    have hfactor : π ≤ ρᵢ * next.factor := by
      cases rest
      · exact hπ
      · exact Multiplicity.le_trans' _ _ _ hπ
          ((by decide : ∀ a b : Multiplicity, a ⊓ b ≤ a) _ _)
    have hrest' := TargetCorecBranches.Usage.branches (ϱ := ϱ) rest hM hNs hrest fun hn => by
      cases rest
      · exact absurd rfl hn
      · exact Multiplicity.le_trans' _ _ _ hπ ((by decide : ∀ a b : Multiplicity, a ⊓ b ≤ b) _ _)
    refine .cons (δᵢ := (ρᵢ * next.factor) ·ᶜ ((ρ ·ᶜ ν) +ᶜ χ)) ?_
      (fun x => Multiplicity.mul_le_mul_right' _ _ _ hfactor) (fun h => absurd rfl h) hrest'
    by_cases hz : ρᵢ = .zero
    · subst hz
      simp only [↓reduceIte]
      refine .sub .erased fun x => ?_
      simp only [MultiplicityVector.extendBinders, Sic.Math.Vector.smul, Sic.Math.Vector.add,
        Sic.Math.Vector.zero]
      split
      · exact (by decide : ∀ a r f p : Multiplicity, a ≤ r * (.zero * f) * p → a ≤ .zero) _ _ _ _
          (hfit _)
      · split
        · omega
        · exact (by decide : ∀ f y : Multiplicity, Multiplicity.zero * f * y ≤ .zero) _ _
    · simp only [hz, ↓reduceIte]
      have hO := Target.Usage.obs (i := i) (ψ := ψ₀) (ς := ς₀) (hM.rename (TargetRen.shift m (0 + c)))
        (Targets.Usage.ofVars πs ϱs (Shape.argVar m c))
      have hB := Target.Usage.body (ϱ := ϱ) next hO (hNs.rename (TargetRen.shift m (0 + c))) hnext
      rw [MultiplicityVector.rename_shift, MultiplicityVector.rename_shift,
        MultiplicityVector.rename_argVar] at hB
      refine .sub hB fun x => ?_
      simp only [MultiplicityVector.extendBinders, Sic.Math.Vector.smul, Sic.Math.Vector.add,
        Sic.Math.Vector.zero]
      split
      · exact (by decide : ∀ a r i f p : Multiplicity, i ≠ .zero → a ≤ r * (i * f) * p →
            a ≤ f * (r * (.zero + p) + .zero)) _ _ _ _ _ hz (hfit _)
      · split
        · omega
        · exact (by decide : ∀ r i f v y : Multiplicity, i ≠ .zero →
              i * f * (r * v + y) ≤ f * (r * (v + .zero) + y)) _ _ _ _ _ hz

-- ADE: none.
/-- The result of the observation `O` of a field, for the shape of a result that fits the recursor
of the multiplicity `ρ`, reads the variables of `O` as `ρ` times its reads, and those of the scope
of the branches of the recursor as `χ`, as many times as the factor of the shape. -/
theorem Target.Usage.body {ρ ϱ : Multiplicity} {m : Nat}
    {ν χ : MultiplicityVector m} {O : Target m} {Ns : TargetBranches m} :
    (next : Shape.Next) → Target.Usage ν O → TargetBranches.Usage ρ χ Ns → next.Fits ρ →
      Target.Usage (next.factor ·ᶜ ((ρ ·ᶜ ν) +ᶜ χ)) (next.body ρ ϱ O Ns)
  | .recursor K, hO, hNs, _ => by
    rw [show Shape.Next.factor (.recursor K) = .one from rfl,
      (MultiplicityVector.module Multiplicity.modality).one_smul]
    by_cases hρ : ρ = .zero
    · subst hρ
      have h := Target.Usage.recursor (ρ := .zero) (ϱ := ϱ) K.target_isData.usage
        (fun _ => K.target_isData) hNs
      simp only [↓reduceIte, Shape.Next.body]
      rwa [(MultiplicityVector.module Multiplicity.modality).zero_smul,
        ← (MultiplicityVector.module Multiplicity.modality).zero_smul ν] at h
    · simp only [hρ, ↓reduceIte, Shape.Next.body]
      exact .recursor hO (fun h => absurd h hρ) hNs
  | .lifting σ, hO, hNs, hσ => by
    have h := Target.Usage.corec .nil
      (TargetCorecBranches.Usage.branches (ϱ := ϱ) σ hO hNs hσ fun _ => Multiplicity.le_refl' _)
    rwa [MultiplicityVector.zero_add] at h

end

-- ADE: none.
/-- `n.Ξ` at run time, for a shape that fits the recursor of the multiplicity `ρ`, reads the field,
the variable `0`, `ρ` times, and the variables of the scope of the recursor as `χ`, each as many
times as the factor of the shape. -/
theorem Target.Usage.nested {ρ ϱ : Multiplicity} {n : Nat}
    {χ : MultiplicityVector n} {σ : Shape} {Ns : TargetBranches n}
    (hNs : TargetBranches.Usage ρ χ Ns)
    (hσ : σ.Fits ρ) :
    Target.Usage
      (σ.factor ·ᶜ ((ρ ·ᶜ MultiplicityVector.update 𝟘ᵛ 0 .one) +ᶜ
        MultiplicityVector.rename (TargetRen.shift n 1) χ))
      (Target.nested ρ ϱ σ Ns) := by
  have h := Target.Usage.corec .nil
    (TargetCorecBranches.Usage.branches (ϱ := ϱ) σ (.var 0)
      (hNs.rename (TargetRen.shift n 1)) hσ fun _ => Multiplicity.le_refl' _)
  rwa [MultiplicityVector.zero_add] at h

end Sic.Core
