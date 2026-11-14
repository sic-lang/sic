module

public import Sic.Core.Evaluation.Conservation.Positions
import Sic.Core.Evaluation.Conservation.Demands

/-!
# Recursions

The demands of the recursions of a branch of a recursor, for the proof of the invariant of the
conservation of the bindings: the demands of the fields that the recursive results use, each as
many times as the multiplicity of the binder of its result.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The uses of a field and of the others by a branch pay `ρ` times their multiplicities. -/
theorem Multiplicity.field_le : ∀ ρ π₀ π r p₀ p q d : Multiplicity, ρ * π₀ ≤ π + ρ * r →
    ρ * p₀ ≤ p + ρ * q → ρ * (π₀ * d + p₀) ≤ π * d + p + ρ * (r * d + q) := by decide

-- ADE: none.
/-- `Σ_{kⱼ ≠ ⊥} π'ⱼ`: the multiplicities of the binders of the results that a branch computes. -/
def Multiplicity.computed : List (Option Nat) → List Multiplicity → Multiplicity
  | some _ :: ks, π :: πs => π + Multiplicity.computed ks πs
  | none :: ks, _ :: πs => Multiplicity.computed ks πs
  | _, _ => .zero

-- ADE: none.
/-- The demands of the fields that the recursions of a branch use, each as many times as the
multiplicity of the binder of its result. -/
def Demand.recursions : List (Option Nat) → List Multiplicity → List Demand → Demand
  | some l :: ks, π :: πs, Ds => π ·ᶜ Ds.getD l 𝟘ᵛ +ᶜ Demand.recursions ks πs Ds
  | none :: ks, _ :: πs, Ds => Demand.recursions ks πs Ds
  | _, _, _ => 𝟘ᵛ

/-- The multiplicities of the computed results, as a list, are those that the usage of the branches
sums. -/
theorem Multiplicity.computed_ofFn : {b : Nat} → (ks : Fin b → Option Nat) →
    (πs : Fin b → Multiplicity) →
      Multiplicity.computed (List.ofFn ks) (List.ofFn πs) =
        Multiplicity.sum (fun j => if (ks j).isSome then πs j else .zero)
  | 0, _, _ => rfl
  | b + 1, ks, πs => by
    rw [List.ofFn_succ, List.ofFn_succ, Multiplicity.sum]
    have ih := Multiplicity.computed_ofFn (fun j => ks j.succ) (fun j => πs j.succ)
    cases h : ks 0 with
    | none =>
      simp only [Multiplicity.computed, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [ih, Multiplicity.modality.semiring.zero_add]
    | some l =>
      simp only [Multiplicity.computed, Option.isSome_some, ↓reduceIte]
      rw [ih]

/-- The sum of demands at the sum of two multiplicities, one by one, is the sum of the sums. -/
theorem Demand.positions_add : (πs₁ πs₂ : List Multiplicity) → (Ds : List Demand) →
    πs₁.length = Ds.length → πs₂.length = Ds.length →
      Demand.positions (List.zipWith (· + ·) πs₁ πs₂) Ds =
        Demand.positions πs₁ Ds +ᶜ Demand.positions πs₂ Ds
  | π₁ :: πs₁, π₂ :: πs₂, D :: Ds, h₁, h₂ => by
    rw [List.zipWith_cons_cons, Demand.positions, Demand.positions, Demand.positions,
      Demand.positions_add πs₁ πs₂ Ds (Nat.succ.inj h₁) (Nat.succ.inj h₂),
      (Sic.Math.Vector.module Multiplicity.modality).add_smul]
    ac_rfl
  | [], [], [], _, _ => (Demand.zero_add _).symm
  | [], _, _ :: _, h₁, _ | _ :: _, _, [], h₁, _ => nomatch h₁
  | [], _ :: _, [], _, h₂ | _ :: _, [], _ :: _, _, h₂ => nomatch h₂

/-- The sum of demands at the multiplicity `π` at the position `l` and `0` elsewhere is `π` times
the demand at `l`. -/
theorem Demand.positions_single (π : Multiplicity) : (l o : Nat) → (Ds : List Demand) →
    l < o + Ds.length → o ≤ l →
      Demand.positions ((List.range' o Ds.length).map fun l' => if l' = l then π else .zero) Ds =
        π ·ᶜ Ds.getD (l - o) 𝟘ᵛ
  | _, _, [], h₁, h₂ => (by rw [List.length_nil] at h₁; omega : False).elim
  | l, o, D :: Ds, h₁, h₂ => by
    rw [List.length_cons, List.range'_succ, List.map_cons, Demand.positions]
    by_cases hl : o = l
    · subst hl
      have hz : Demand.positions ((List.range' (o + 1) Ds.length).map
          fun l' => if l' = o then π else .zero) Ds = 𝟘ᵛ := by
        rw [show ((List.range' (o + 1) Ds.length).map fun l' => if l' = o then π else .zero) =
            List.replicate Ds.length .zero by
          apply List.ext_getElem
            (by rw [List.length_map, List.length_range', List.length_replicate])
          intro i h₁ h₂
          simp only [List.getElem_map, List.getElem_range', List.getElem_replicate,
            show ¬ (o + 1 + 1 * i = o) by omega, ↓reduceIte]]
        exact Demand.positions_replicate_zero _ _
      simp only [↓reduceIte]
      rw [hz, Demand.add_zero, Nat.sub_self]
      rfl
    · simp only [hl, ↓reduceIte]
      rw [Demand.zero_smul, Demand.zero_add,
        Demand.positions_single π l (o + 1) Ds (by rw [List.length_cons] at h₁; omega)
          (by omega)]
      rw [show l - o = (l - (o + 1)) + 1 by omega]
      rfl

/-- The recursions of a branch regroup by field: each field is used as many times as the
multiplicities of the binders of the results that its recursions compute. -/
theorem Demand.recursions_eq : (ks : List (Option Nat)) → (πs : List Multiplicity) →
    (Ds : List Demand) → ks.length = πs.length →
      (∀ (j : Nat) l, ks[j]? = some (some l) → l < Ds.length) →
      Demand.recursions ks πs Ds =
        Demand.positions ((List.range Ds.length).map (recursionsAt ks πs)) Ds
  | [], [], Ds, _, _ => by
    show 𝟘ᵛ = _
    rw [show (List.range Ds.length).map (recursionsAt [] []) =
        List.replicate Ds.length .zero by
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [recursionsAt]]
    exact (Demand.positions_replicate_zero _ _).symm
  | k :: ks, π :: πs, Ds, hl, hk => by
    have ih := Demand.recursions_eq ks πs Ds (Nat.succ.inj hl) (fun j l h => hk (j + 1) l h)
    have hsplit : (List.range Ds.length).map (recursionsAt (k :: ks) (π :: πs)) =
        List.zipWith (· + ·) ((List.range Ds.length).map fun l => if k = some l then π else .zero)
          ((List.range Ds.length).map (recursionsAt ks πs)) := by
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [recursionsAt]
    rw [hsplit, Demand.positions_add _ _ _ (by simp) (by simp), ← ih]
    cases k with
    | none =>
      rw [Demand.recursions, show ((List.range Ds.length).map fun l =>
          if (none : Option Nat) = some l then π else .zero) = List.replicate Ds.length .zero by
        apply List.ext_getElem (by simp)
        intro i _ _
        simp,
        Demand.positions_replicate_zero, Demand.zero_add]
    | some l =>
      have hlt := hk 0 l rfl
      rw [Demand.recursions, List.range_eq_range', show ((List.range' 0 Ds.length).map fun l' =>
          if some l = some l' then π else .zero) =
          (List.range' 0 Ds.length).map fun l' => if l' = l then π else .zero by
        apply List.map_congr_left
        intro x _
        simp [eq_comm],
        Demand.positions_single π l 0 Ds (by omega) (Nat.zero_le _), Nat.sub_zero]
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => nomatch hl

/-- The uses of the fields by a branch of the recursor of the multiplicity `ρ`: `ρ` times their
multiplicities in the constructor are within those of their binders plus `ρ` times those of the
recursions on them. -/
theorem Demand.positions_le_add (ρ : Multiplicity) : (πs₀ πs ρs : List Multiplicity) →
    (Ds : List Demand) → πs₀.length = Ds.length → πs.length = Ds.length →
      ρs.length = Ds.length →
      (∀ (l : Nat) π₀ π r, πs₀[l]? = some π₀ → πs[l]? = some π → ρs[l]? = some r →
        ρ * π₀ ≤ π + ρ * r) →
      ρ ·ᶜ Demand.positions πs₀ Ds ≤ᶜ Demand.positions πs Ds +ᶜ ρ ·ᶜ Demand.positions ρs Ds
  | π₀ :: πs₀, π :: πs, r :: ρs, D :: Ds, h₀, h₁, h₂, h => by
    have ih := Demand.positions_le_add ρ πs₀ πs ρs Ds (Nat.succ.inj h₀) (Nat.succ.inj h₁)
      (Nat.succ.inj h₂) (fun l => h (l + 1))
    have hl := h 0 π₀ π r rfl rfl rfl
    simp only [Demand.positions]
    intro x
    have ihx := ih x
    simp only [Sic.Math.Vector.add, Sic.Math.Vector.smul] at ihx ⊢
    exact Multiplicity.field_le ρ π₀ π r _ _ _ (D x) hl ihx
  | [], [], [], [], _, _, _, _ => fun _ => Multiplicity.le_refl' _
  | [], _, _, _ :: _, h₀, _, _, _ | _ :: _, _, _, [], h₀, _, _, _ => nomatch h₀
  | _, [], _, _ :: _, _, h₁, _, _ | _, _ :: _, _, [], _, h₁, _, _ => nomatch h₁
  | _, _, [], _ :: _, _, _, h₂, _ | _, _, _ :: _, [], _, _, h₂, _ => nomatch h₂

/-- The recursive results of a branch are on its fields. -/
theorem EvalResults.lt {P : Program} {ϖ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {ρ ϱ : Multiplicity} {Ns : TargetBranches n} {as : List Nat} :
    {ks : List (Option Nat)} → {πs : List Multiplicity} → {rs : List Nat} → {R : List Nat} →
      EvalResults P ϖ H E ρ ϱ Ns as ks πs rs H' R →
        ∀ (j : Nat) l, ks[j]? = some (some l) → l < as.length
  | _, _, _, _, .nil, _, _, h => nomatch h
  | _, _, _, _, .erased hs, j + 1, l, h => hs.lt j l h
  | _, _, _, _, .recursor hj _ _, 0, l, h => by
    cases h
    exact (List.getElem?_eq_some_iff.1 hj).1
  | _, _, _, _, .recursor _ _ hs, j + 1, l, h => hs.lt j l h

end Sic.Core
