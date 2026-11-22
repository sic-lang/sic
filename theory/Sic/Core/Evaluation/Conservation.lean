module

public import Sic.Core.Evaluation.Conservation.Binders
public import Sic.Core.Evaluation.Conservation.Data
public import Sic.Core.Evaluation.Conservation.Demands
public import Sic.Core.Evaluation.Conservation.Environments
public import Sic.Core.Evaluation.Conservation.Positions
public import Sic.Core.Evaluation.Conservation.Recursions
public import Sic.Core.Evaluation.Conservation.Usage
import Sic.Core.Erasure.Usage.Nested

/-!
# Conservation

The conservation of the bindings of annex 20 of RFC 36: a run of a term of the target language that
reads its variables as its usage allows reads each cell that it allocates, of the multiplicity `π`,
as `π` allows, once the reads that the value that it computes can still do are counted, its demand.
The invariant, `𝒫; ϖ; H; E ⊢ M ⇓ a; H'; R` with `ν ⊢ M ▶` and `H ⊢ E ▶_ν D_E`, bounds the demand
of the environment, at the weight `ϖ`, plus the multiplicities of the cells that the run allocates,
by the reads of the run plus the demand of its value, at the weight: `ϖ · D_E + new_H(H, H') ≤ #R +
ϖ · D`.
A closed term, run at the weight `1`, then reads each cell of the multiplicity `1` that it allocates
once, or leaves the read to its value, and never reads a cell of the multiplicity `0`; a value
without closure leaves no read, so that each such cell is read exactly once.

The modules of `Sic/Core/Evaluation/Conservation/` hold the lemmas that the proof of the invariant
reads, which the RFC does not state.

ADE prove the resource correctness of their machine by the usage of its states, in
`Graded/Heap/Usage/Reduction.agda`, whose heap holds the grades that remain: the demands here are
these grades, which the run does not store.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-! ## Invariant -/

mutual

-- ADE: `▸-⇾`, in `Graded/Heap/Usage/Reduction.agda`, for the usage of the states along a step.
/-- `cons_⇓`: a run of a term of the target language, at a weight other than `0`, whose usage
bounds its reads by `ν`, in an environment of the demand `D_E` for `ν`, reads the cells and
allocates cells as the demand of the environment allows, once the demand `D` of its value is
counted:
`ϖ · D_E + new_H(H, H') ≤ #R + ϖ · D`.
RFC: `\mathsf{cons}_\Downarrow` -/
theorem Eval.conserve {P : Program} (hP : P.Usage) {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {M : Target n} {a : Nat} {R : List Nat}
    (h : Eval P ϖ H E M a H' R) {ν : MultiplicityVector n} {D_E : Demand}
    (hM : Target.Usage ν M) (hE : H.EnvDemand E ν D_E) :
    ∃ D, H'.ValueDemand a D ∧ ϖ ·ᶜ D_E +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ D :=
  match h with
  | .var (x := x) hx hc => by
    obtain ⟨D', hD', hE'⟩ := hE.le (hM.var_inv rfl)
    obtain ⟨c', π', ℓ', Dx, hx', hc', hv, rfl⟩ := hE'.var_inv x
      (by simp [MultiplicityVector.update, Sic.Math.Vector.update])
      (fun y hy => by simp [MultiplicityVector.update, Sic.Math.Vector.update, hy]; rfl)
    rw [hx] at hx'
    cases hx'
    rw [hc] at hc'
    cases hc'
    refine ⟨Dx, hv, ?_⟩
    rw [Demand.allocated_self, Demand.uses_singleton]
    exact fun y => Multiplicity.var_le ϖ _ _ _ hϖ (hD' y)
  | .const hf hb => by
    obtain ⟨D', hD', hE'⟩ := hE.le (hM.zero_inv (.inr ⟨_, _, _, rfl⟩))
    rw [hE'.eq_zero fun _ => rfl] at hD'
    obtain ⟨D, hv, hD⟩ := Eval.conserve hP hϖ hb (hP _ _ _ _ hf) .nil
    refine ⟨D, hv, Demand.le_trans (Demand.add_le_add_right ?_ _) hD⟩
    rw [Demand.smul_zero]
    exact Demand.smul_le_zero hD'
  | .erased => by
    obtain ⟨D', hD', hE'⟩ := hE.le (hM.zero_inv (.inl rfl))
    rw [hE'.eq_zero fun _ => rfl] at hD'
    refine ⟨𝟘ᵛ, .erased List.getElem?_concat_length, ?_⟩
    rw [Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero,
      Demand.uses_nil, Demand.smul_zero, Demand.add_zero]
    exact Demand.smul_le_zero hD'
  | .ctor hs => by
    obtain ⟨ν', hle, hMs⟩ := hM.ctor_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D, hv, hD⟩ := EvalAll.conserve hP hϖ hs hMs hE'
    refine ⟨D, .ctor List.getElem?_concat_length (hv.mono (List.prefix_append _ _)), ?_⟩
    rw [Demand.allocated_trans hs.extends (List.prefix_append _ _),
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
    exact Demand.le_trans (Demand.add_le_add_right (Demand.smul_le_smul ϖ hD') _) hD
  | .recursor (ρ := ρ) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) hev hr => by
    obtain ⟨ν₁, χ, hle, hM₁, hz, hNs⟩ := hM.recursor_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁', Dχ, rfl, hE₁', hEχ⟩ := hE'.split
    obtain ⟨D₁, rfl, hE₁⟩ := hE₁'.unsmul
    have hH := hev.extends
    by_cases hρ : ρ = .zero
    · obtain ⟨rfl, hal, hva⟩ := (hz hρ).conserve hev
      obtain ⟨D, hv, hD⟩ := EvalRec.conserve hP hϖ hr hNs (hEχ.mono hH) hva
      refine ⟨D, hv, ?_⟩
      rw [Demand.allocated_trans hH hr.extends, hal, Demand.zero_add, List.nil_append]
      refine Demand.le_trans (Demand.add_le_add_right (Demand.smul_le_smul ϖ hD') _)
        (Demand.le_trans (Demand.le_of_eq ?_) hD)
      rw [hρ, Demand.zero_smul, Demand.zero_add, Demand.smul_zero, Demand.add_zero]
    · obtain ⟨Da, hva, hDa⟩ := Eval.conserve hP (Multiplicity.mul_ne_zero ϖ ρ hϖ hρ) hev hM₁ hE₁
      obtain ⟨D, hv, hD⟩ := EvalRec.conserve hP hϖ hr hNs (hEχ.mono hH) hva
      refine ⟨D, hv, ?_⟩
      rw [Demand.allocated_trans hH hr.extends, Demand.uses_append]
      rw [Demand.mul_smul, Demand.mul_smul] at hDa
      rw [Demand.smul_add] at hD
      generalize Demand.allocated H H₂ = A₁ at hDa ⊢
      generalize Demand.allocated H₂ H' = A₂ at hD ⊢
      generalize Demand.uses R₁ = U₁ at hDa ⊢
      generalize Demand.uses R₂ = U₂ at hD ⊢
      calc ϖ ·ᶜ D_E +ᶜ (A₁ +ᶜ A₂)
          ≤ᶜ ϖ ·ᶜ (ρ ·ᶜ D₁ +ᶜ Dχ) +ᶜ (A₁ +ᶜ A₂) :=
            Demand.add_le_add_right (Demand.smul_le_smul ϖ hD') _
        _ = (ϖ ·ᶜ ρ ·ᶜ D₁ +ᶜ A₁) +ᶜ (ϖ ·ᶜ Dχ +ᶜ A₂) := by
          rw [Demand.smul_add]
          ac_rfl
        _ ≤ᶜ (U₁ +ᶜ ϖ ·ᶜ ρ ·ᶜ Da) +ᶜ (ϖ ·ᶜ Dχ +ᶜ A₂) := Demand.add_le_add_right hDa _
        _ = U₁ +ᶜ (ϖ ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Da +ᶜ A₂) := by ac_rfl
        _ ≤ᶜ U₁ +ᶜ (U₂ +ᶜ ϖ ·ᶜ D) := Demand.add_le_add_left _ hD
        _ = U₁ +ᶜ U₂ +ᶜ ϖ ·ᶜ D := by ac_rfl
  | .obs (H₂ := H₂) (H₃ := H₃) (R₁ := R₁) (R₂ := R₂) (R₃ := R₃) hev hs ho => by
    obtain ⟨ν₁, ν₂, hle, hM₁, hMs⟩ := hM.obs_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁, D₂, rfl, hE₁, hE₂⟩ := hE'.split
    obtain ⟨Da, hva, hDa⟩ := Eval.conserve hP hϖ hev hM₁ hE₁
    obtain ⟨Db, hvb, hDb⟩ := EvalAll.conserve hP hϖ hs hMs (hE₂.mono hev.extends)
    obtain ⟨D, hv, hD⟩ := EvalObs.conserve hP hϖ ho (hva.mono hs.extends) hvb
    refine ⟨D, hv, ?_⟩
    rw [Demand.allocated_trans hev.extends (hs.extends.trans ho.extends),
      Demand.allocated_trans hs.extends ho.extends, Demand.uses_append, Demand.uses_append]
    rw [Demand.smul_add] at hD
    generalize Demand.allocated H H₂ = A₁ at hDa ⊢
    generalize Demand.allocated H₂ H₃ = A₂ at hDb ⊢
    generalize Demand.allocated H₃ H' = A₃ at hD ⊢
    generalize Demand.uses R₁ = U₁ at hDa ⊢
    generalize Demand.uses R₂ = U₂ at hDb ⊢
    generalize Demand.uses R₃ = U₃ at hD ⊢
    calc ϖ ·ᶜ D_E +ᶜ (A₁ +ᶜ (A₂ +ᶜ A₃))
        ≤ᶜ ϖ ·ᶜ (D₁ +ᶜ D₂) +ᶜ (A₁ +ᶜ (A₂ +ᶜ A₃)) :=
          Demand.add_le_add_right (Demand.smul_le_smul ϖ hD') _
      _ = (ϖ ·ᶜ D₁ +ᶜ A₁) +ᶜ (ϖ ·ᶜ D₂ +ᶜ A₂) +ᶜ A₃ := by
          rw [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ ϖ ·ᶜ Da) +ᶜ (U₂ +ᶜ ϖ ·ᶜ Db) +ᶜ A₃ :=
          Demand.add_le_add_right (Demand.add_le_add hDa hDb) _
      _ = U₁ +ᶜ U₂ +ᶜ (ϖ ·ᶜ Da +ᶜ ϖ ·ᶜ Db +ᶜ A₃) := by ac_rfl
      _ ≤ᶜ U₁ +ᶜ U₂ +ᶜ (U₃ +ᶜ ϖ ·ᶜ D) := Demand.add_le_add_left _ hD
      _ = U₁ +ᶜ (U₂ +ᶜ U₃) +ᶜ ϖ ·ᶜ D := by ac_rfl
  | .corec (Ps := Ps) (Ms := Ms) (as := as) (H' := H₁) (R := R₁) hs => by
    obtain ⟨ν₁, δ, hle, hMs, hPs⟩ := hM.corec_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁, Dδ, rfl, hE₁, hEδ⟩ := hE'.split
    obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hϖ hs hMs hE₁
    have hH : H₁.Extends (H₁ ++ [Value.corec _ E Ps Ms.multiplicities Ms.requirements as]) :=
      List.prefix_append _ _
    refine ⟨Dδ +ᶜ Ds, .corec List.getElem?_concat_length hPs ((hEδ.mono hs.extends).mono hH)
      (hvs.mono hH), ?_⟩
    rw [Demand.allocated_trans hs.extends hH,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
    generalize Demand.allocated H H₁ = A₁ at hDs ⊢
    generalize Demand.uses R₁ = U₁ at hDs ⊢
    calc ϖ ·ᶜ D_E +ᶜ A₁
        ≤ᶜ ϖ ·ᶜ (D₁ +ᶜ Dδ) +ᶜ A₁ := Demand.add_le_add_right (Demand.smul_le_smul ϖ hD') _
      _ = (ϖ ·ᶜ D₁ +ᶜ A₁) +ᶜ ϖ ·ᶜ Dδ := by
          rw [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ ϖ ·ᶜ Ds) +ᶜ ϖ ·ᶜ Dδ := Demand.add_le_add_right hDs _
      _ = U₁ +ᶜ ϖ ·ᶜ (Dδ +ᶜ Ds) := by
          rw [Demand.smul_add]
          ac_rfl
termination_by structural h

/-- The invariant of the terms evaluated one after the other, each at the weight times its
multiplicity, whose values have the demands of their positions. -/
theorem EvalAll.conserve {P : Program} (hP : P.Usage) {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n} {as : List Nat} {R : List Nat}
    (h : EvalAll P ϖ H E Ms as H' R) {ν : MultiplicityVector n} {D_E : Demand}
    (hMs : Targets.Usage ν Ms) (hE : H.EnvDemand E ν D_E) :
    ∃ D, H'.PositionsDemand Ms.multiplicities as D ∧
      ϖ ·ᶜ D_E +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ D :=
  match h with
  | .nil => by
    cases hMs
    rw [hE.eq_zero fun _ => rfl, Demand.allocated_self]
    refine ⟨𝟘ᵛ, .nil, ?_⟩
    rw [Demand.uses_nil, Demand.smul_zero, Demand.add_zero]
    exact Demand.le_refl _
  | .cons (π := π) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) hev hs => by
    cases hMs with
    | cons hM hz hMs =>
    obtain ⟨D₁', D₂, rfl, hE₁', hE₂⟩ := hE.split
    obtain ⟨D₁, rfl, hE₁⟩ := hE₁'.unsmul
    by_cases hπ : π = .zero
    · obtain ⟨rfl, hal, hva⟩ := (hz hπ).conserve hev
      obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hϖ hs hMs (hE₂.mono hev.extends)
      refine ⟨_, .cons (hva.mono hs.extends) hvs, ?_⟩
      rw [Demand.allocated_trans hev.extends hs.extends, hal, List.nil_append, hπ, Demand.zero_smul,
        Demand.zero_smul, Demand.zero_add, Demand.zero_add, Demand.zero_add]
      exact hDs
    · obtain ⟨Da, hva, hDa⟩ :=
        Eval.conserve hP (Multiplicity.mul_ne_zero ϖ π hϖ hπ) hev hM hE₁
      obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hϖ hs hMs (hE₂.mono hev.extends)
      refine ⟨_, .cons (hva.mono hs.extends) hvs, ?_⟩
      rw [Demand.allocated_trans hev.extends hs.extends, Demand.uses_append]
      rw [Demand.mul_smul, Demand.mul_smul] at hDa
      generalize Demand.allocated H H₂ = A₁ at hDa ⊢
      generalize Demand.allocated H₂ H' = A₂ at hDs ⊢
      generalize Demand.uses R₁ = U₁ at hDa ⊢
      generalize Demand.uses R₂ = U₂ at hDs ⊢
      calc ϖ ·ᶜ (π ·ᶜ D₁ +ᶜ D₂) +ᶜ (A₁ +ᶜ A₂)
          = (ϖ ·ᶜ π ·ᶜ D₁ +ᶜ A₁) +ᶜ (ϖ ·ᶜ D₂ +ᶜ A₂) := by
            rw [Demand.smul_add]
            ac_rfl
        _ ≤ᶜ (U₁ +ᶜ ϖ ·ᶜ π ·ᶜ Da) +ᶜ (U₂ +ᶜ ϖ ·ᶜ Ds) := Demand.add_le_add hDa hDs
        _ = U₁ +ᶜ U₂ +ᶜ ϖ ·ᶜ (π ·ᶜ Da +ᶜ Ds) := by
            rw [Demand.smul_add]
            ac_rfl
termination_by structural h

/-- The invariant of the elimination of a value by a recursor: the demand of the scope, for the
reads of the branches, and `ρ` times that of the value pay the reads of the run and the demand of
its value. -/
theorem EvalRec.conserve {P : Program} (hP : P.Usage) {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {ρ ϱ : Multiplicity} {Ns : TargetBranches n}
    {a v : Nat} {R : List Nat} (h : EvalRec P ϖ H E ρ ϱ Ns a v H' R)
    {χ : MultiplicityVector n} {Dχ Da : Demand} (hNs : TargetBranches.Usage ρ χ Ns)
    (hE : H.EnvDemand E χ Dχ) (ha : H.ValueDemand a Da) :
    ∃ D, H'.ValueDemand v D ∧
      ϖ ·ᶜ (Dχ +ᶜ ρ ·ᶜ Da) +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ D :=
  match h with
  | .iota (H₂ := H₂) (πs₀ := πs₀) (as := as) (a' := a') (b := b) (πs := πs) (πs' := πs')
      (ks := ks) (N := N) (rs := rs) (R₁ := R₁) (R₂ := R₂) hca hN hla hπ _ _ hres hv => by
    obtain ⟨Ds, hDs, rfl, hl₀⟩ := (ha.ctor_inv hca).inv
    obtain ⟨δ, hNu, hχ, hk, hσ⟩ := hNs.get _ hN
    obtain ⟨D', hD', hE'⟩ := hE.le hχ
    obtain ⟨Dδ, DS, rfl, hEδ, hES⟩ := hE'.split
    obtain ⟨Dχ₂, rfl, hEχ₂⟩ := hES.unsmul
    have hlr := hres.length
    -- The recursive results.
    obtain ⟨Drs, hDrs, hDres⟩ := EvalResults.conserve hP hϖ hres hNs hEχ₂ hDs
      (fun j k π hj hke hπj h0 => by
        rw [List.getElem?_ofFn] at hj hπj
        by_cases hjb : j < b
        · simp only [hjb, ↓reduceDIte, Option.some.injEq] at hj hπj
          exact hk ⟨j, hjb⟩ (by rw [hj]; exact hke) (hπj.trans h0)
        · simp only [hjb, ↓reduceDIte] at hj
          cases hj)
      (fun j l σ' hj => by
        rw [List.getElem?_ofFn] at hj
        by_cases hjb : j < b
        · simp only [hjb, ↓reduceDIte, Option.some.injEq] at hj
          exact hσ ⟨j, hjb⟩ l σ' hj
        · simp only [hjb, ↓reduceDIte] at hj
          cases hj)
    have hH₂ : H₂.Extends (H₂.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (as ++ rs)) :=
      List.prefix_append _ _
    -- The branch, with cells for the fields and the results.
    obtain ⟨C, hEbr, hal⟩ := Heap.EnvDemand.bindBranch ϖ πs πs'
      ((hEδ.mono hres.extends).mono hH₂) ((hDs.mono hres.extends).mono hH₂) (hDrs.mono hH₂) hla
      (by simp at hlr; omega)
    obtain ⟨Dv, hvv, hDv⟩ := Eval.conserve hP hϖ hv hNu hEbr
    refine ⟨Dv, hvv, ?_⟩
    -- The uses of the fields by the branch and by the recursions.
    have hfield := Demand.positions_le_add ρ πs₀ (List.ofFn πs)
      ((List.range Ds.length).map (recursionsAt (List.ofFn ks) (List.ofFn πs'))) Ds
      (hl₀.trans hDs.length) (by simp [← hDs.length, hla]) (by simp)
      (fun l π₀ π r h₀ h₁ h₂ => by
        rw [List.getElem?_ofFn] at h₁
        split at h₁
        · rename_i hl
          cases h₁
          obtain ⟨π₀', h₀', hle⟩ := hπ ⟨l, hl⟩
          rw [h₀] at h₀'
          cases h₀'
          simp only [List.getElem?_map, List.getElem?_range (show l < Ds.length by
            rw [← hDs.length, hla]; exact hl), Option.map_some, Option.some.injEq] at h₂
          rw [← h₂]
          exact hle
        · cases h₁)
    rw [← Demand.recursions_eq _ _ _ (by simp) (fun j k l h hk => hDs.length ▸ hres.lt j k l h hk)]
      at hfield
    rw [Multiplicity.computed_ofFn] at hDres
    rw [Demand.allocated_trans hres.extends (hH₂.trans hv.extends),
      Demand.allocated_trans hH₂ hv.extends, hal, Demand.uses_append]
    rw [Demand.smul_add, Demand.smul_add, Demand.smul_add] at hDv
    rw [Demand.smul_add] at hDres
    generalize Demand.allocated H H₂ = A₁ at hDres ⊢
    generalize Demand.allocated _ H' = A₂ at hDv ⊢
    generalize Demand.uses R₁ = U₁ at hDres ⊢
    generalize Demand.uses R₂ = U₂ at hDv ⊢
    generalize Demand.recursions (List.ofFn ks) (List.ofFn πs') Ds = Rc at hfield hDres ⊢
    generalize Demand.positions (List.ofFn πs) Ds = Q₁ at hfield hDv ⊢
    generalize Demand.positions (List.ofFn πs') Drs = Q₂ at hDres hDv ⊢
    generalize Demand.positions πs₀ Ds = P₀ at hfield ⊢
    generalize Multiplicity.sum _ = S at hD' hDres ⊢
    calc ϖ ·ᶜ (Dχ +ᶜ ρ ·ᶜ P₀) +ᶜ (A₁ +ᶜ (ϖ ·ᶜ C +ᶜ A₂))
        ≤ᶜ ϖ ·ᶜ (Dδ +ᶜ S ·ᶜ Dχ₂ +ᶜ (Q₁ +ᶜ ρ ·ᶜ Rc)) +ᶜ (A₁ +ᶜ (ϖ ·ᶜ C +ᶜ A₂)) :=
          Demand.add_le_add_right (Demand.smul_le_smul ϖ (Demand.add_le_add hD' hfield)) _
      _ = (ϖ ·ᶜ S ·ᶜ Dχ₂ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc +ᶜ A₁) +ᶜ (ϖ ·ᶜ Dδ +ᶜ ϖ ·ᶜ C +ᶜ ϖ ·ᶜ Q₁ +ᶜ A₂) := by
          simp only [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ ϖ ·ᶜ Q₂) +ᶜ (ϖ ·ᶜ Dδ +ᶜ ϖ ·ᶜ C +ᶜ ϖ ·ᶜ Q₁ +ᶜ A₂) :=
          Demand.add_le_add_right hDres _
      _ = U₁ +ᶜ (ϖ ·ᶜ Dδ +ᶜ ϖ ·ᶜ C +ᶜ (ϖ ·ᶜ Q₁ +ᶜ ϖ ·ᶜ Q₂) +ᶜ A₂) := by ac_rfl
      _ ≤ᶜ U₁ +ᶜ (U₂ +ᶜ ϖ ·ᶜ Dv) := Demand.add_le_add_left _ hDv
      _ = U₁ +ᶜ U₂ +ᶜ ϖ ·ᶜ Dv := by ac_rfl
termination_by structural h

/-- The invariant of the recursive results of a branch: the demand of the scope, as many times as
the multiplicities of the binders of the computed results, and `ρ` times the demands of the fields
that the recursions use, pay the reads of the runs and the demands of the results, each as many
times as the multiplicity of its binder. -/
theorem EvalResults.conserve {P : Program} (hP : P.Usage) {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {ρ ϱ : Multiplicity} {Ns : TargetBranches n}
    {as : List Nat} {ks : List RecursiveResult} {πs : List Multiplicity} {rs : List Nat}
    {R : List Nat} (h : EvalResults P ϖ H E ρ ϱ Ns as ks πs rs H' R) {χ : MultiplicityVector n}
    {Dχ : Demand} {Ds : List Demand} (hNs : TargetBranches.Usage ρ χ Ns)
    (hE : H.EnvDemand E χ Dχ) (hDs : H.ValueDemands as Ds)
    (hk : ∀ (j : Nat) (k : RecursiveResult) π, ks[j]? = some k → k ≠ .erased → πs[j]? = some π →
      π ≠ .zero)
    (hσ : ∀ (j l : Nat) (σ : Shape), ks[j]? = some (.nested l σ) → σ.Fits ρ) :
    ∃ Drs, H'.ValueDemands rs Drs ∧
      ϖ ·ᶜ (Multiplicity.computed ks πs ·ᶜ Dχ +ᶜ ρ ·ᶜ Demand.recursions ks πs Ds) +ᶜ
        Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ Demand.positions πs Drs :=
  match h with
  | .nil => by
    refine ⟨[], .nil, ?_⟩
    rw [Demand.allocated_self, Demand.uses_nil]
    intro x
    exact (by decide : ∀ ϖ ρ d : Multiplicity, ϖ * (.zero * d + ρ * .zero) + .zero ≤
      .zero + ϖ * .zero) ϖ ρ (Dχ x)
  | .erased (H₂ := H₂) hs => by
    have hH : H.Extends (H ++ [Value.erased]) := List.prefix_append _ _
    obtain ⟨Drs, hDrs, hD⟩ := EvalResults.conserve hP hϖ hs hNs (hE.mono hH) (hDs.mono hH)
      (fun j => hk (j + 1)) (fun j => hσ (j + 1))
    refine ⟨𝟘ᵛ :: Drs, .cons (Heap.ValueDemand.erased List.getElem?_concat_length |>.mono
      hs.extends) hDrs, ?_⟩
    rw [Demand.allocated_trans hH hs.extends,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.zero_add]
    show _ ≤ᶜ _ +ᶜ ϖ ·ᶜ (_ ·ᶜ 𝟘ᵛ +ᶜ _)
    rw [Demand.smul_zero, Demand.zero_add]
    rwa [Multiplicity.computed, RecursiveResult.factor, Multiplicity.modality.semiring.mul_zero,
      Multiplicity.modality.semiring.zero_add, Demand.recursions]
  | .recursor (π := π) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) (j := j) hj hev hs => by
    have hπ : π ≠ .zero := fun h0 => hk 0 _ π rfl (fun h => nomatch h) rfl h0
    have hD := hDs.getElem? j hj
    obtain ⟨Dr, hvr, hDr⟩ := EvalRec.conserve hP (Multiplicity.mul_ne_zero ϖ π hϖ hπ) hev hNs hE hD
    obtain ⟨Drs, hDrs, hDt⟩ := EvalResults.conserve hP hϖ hs hNs (hE.mono hev.extends)
      (hDs.mono hev.extends) (fun j => hk (j + 1)) (fun j => hσ (j + 1))
    refine ⟨Dr :: Drs, .cons (hvr.mono hs.extends) hDrs, ?_⟩
    rw [Demand.allocated_trans hev.extends hs.extends, Demand.uses_append, Multiplicity.computed,
      RecursiveResult.factor, Multiplicity.modality.semiring.mul_one]
    show ϖ ·ᶜ ((π + Multiplicity.computed _ _) ·ᶜ Dχ +ᶜ
        ρ ·ᶜ (π ·ᶜ Ds.getD j 𝟘ᵛ +ᶜ Demand.recursions _ _ Ds)) +ᶜ _ ≤ᶜ
      _ +ᶜ ϖ ·ᶜ (π ·ᶜ Dr +ᶜ Demand.positions _ Drs)
    rw [Demand.smul_add] at hDr
    rw [Demand.smul_add] at hDt
    generalize Demand.allocated H H₂ = A₁ at hDr ⊢
    generalize Demand.allocated H₂ H' = A₂ at hDt ⊢
    generalize Demand.uses R₁ = U₁ at hDr ⊢
    generalize Demand.uses R₂ = U₂ at hDt ⊢
    generalize Ds.getD j 𝟘ᵛ = Da at hDr ⊢
    generalize Demand.recursions _ _ Ds = Rc at hDt ⊢
    generalize Multiplicity.computed _ _ = c at hDt ⊢
    generalize Demand.positions _ Drs = Q at hDt ⊢
    have e₁ : ϖ ·ᶜ ((π + c) ·ᶜ Dχ +ᶜ ρ ·ᶜ (π ·ᶜ Da +ᶜ Rc)) =
        (ϖ * π) ·ᶜ Dχ +ᶜ (ϖ * π) ·ᶜ ρ ·ᶜ Da +ᶜ (ϖ ·ᶜ c ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc) := by
      funext x
      exact (by decide : ∀ ϖ π c ρ d a r : Multiplicity,
        ϖ * ((π + c) * d + ρ * (π * a + r)) =
          ϖ * π * d + ϖ * π * (ρ * a) + (ϖ * (c * d) + ϖ * (ρ * r))) ϖ π c ρ (Dχ x) (Da x) (Rc x)
    rw [e₁, Demand.smul_add, ← Demand.mul_smul ϖ π]
    calc (ϖ * π) ·ᶜ Dχ +ᶜ (ϖ * π) ·ᶜ ρ ·ᶜ Da +ᶜ (ϖ ·ᶜ c ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc) +ᶜ (A₁ +ᶜ A₂)
        = ((ϖ * π) ·ᶜ Dχ +ᶜ (ϖ * π) ·ᶜ ρ ·ᶜ Da +ᶜ A₁) +ᶜ
            (ϖ ·ᶜ c ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc +ᶜ A₂) := by ac_rfl
      _ ≤ᶜ (U₁ +ᶜ (ϖ * π) ·ᶜ Dr) +ᶜ (U₂ +ᶜ ϖ ·ᶜ Q) := Demand.add_le_add hDr hDt
      _ = U₁ +ᶜ U₂ +ᶜ ((ϖ * π) ·ᶜ Dr +ᶜ ϖ ·ᶜ Q) := by ac_rfl
  | .nested (π := π) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) (l := l) (a := a) (σ := σ) hl hev hs => by
    have hπ : π ≠ .zero := fun h0 => hk 0 _ π rfl (fun h => nomatch h) rfl h0
    have hD := hDs.getElem? l hl
    have hH : H.Extends (H ++ [.cell ((ϖ * π) * (σ.factor * ρ)) a]) := List.prefix_append _ _
    -- The corecursor reads its field `factor(σ) · ρ` times and the scope `factor(σ)` times.
    have hν := MultiplicityVector.nested_succ σ.factor ρ χ
    have hEn := Heap.EnvDemand.cons (ν := σ.factor ·ᶜ ((ρ ·ᶜ MultiplicityVector.update 𝟘ᵛ 0 .one)
        +ᶜ MultiplicityVector.rename (TargetRen.shift n 1) χ)) List.getElem?_concat_length
      (hD.mono hH) (by rw [funext hν]; exact (hE.mono hH).smul σ.factor)
    obtain ⟨Dr, hvr, hDr⟩ := Eval.conserve hP (Multiplicity.mul_ne_zero ϖ π hϖ hπ) hev
      (Target.Usage.nested hNs (hσ 0 l σ rfl)) hEn
    obtain ⟨Drs, hDrs, hDt⟩ := EvalResults.conserve hP hϖ hs hNs ((hE.mono hH).mono hev.extends)
      ((hDs.mono hH).mono hev.extends) (fun j => hk (j + 1)) (fun j => hσ (j + 1))
    refine ⟨Dr :: Drs, .cons (hvr.mono hs.extends) hDrs, ?_⟩
    rw [Demand.allocated_trans hH (hev.extends.trans hs.extends),
      Demand.allocated_trans hev.extends hs.extends, Demand.allocated_cell, Demand.uses_append,
      Multiplicity.computed, RecursiveResult.factor]
    show ϖ ·ᶜ ((π * σ.factor + Multiplicity.computed _ _) ·ᶜ Dχ +ᶜ
        ρ ·ᶜ ((π * σ.factor) ·ᶜ Ds.getD l 𝟘ᵛ +ᶜ Demand.recursions _ _ Ds)) +ᶜ _ ≤ᶜ
      _ +ᶜ ϖ ·ᶜ (π ·ᶜ Dr +ᶜ Demand.positions _ Drs)
    rw [MultiplicityVector.nested_zero] at hDr
    rw [Demand.smul_add] at hDt
    generalize Demand.allocated (H ++ _) H₂ = A₂ at hDr ⊢
    generalize Demand.allocated H₂ H' = A₃ at hDt ⊢
    generalize Demand.uses R₁ = U₁ at hDr ⊢
    generalize Demand.uses R₂ = U₂ at hDt ⊢
    generalize Ds.getD l 𝟘ᵛ = Da at hDr ⊢
    generalize Demand.recursions _ _ Ds = Rc at hDt ⊢
    generalize Multiplicity.computed _ _ = c at hDt ⊢
    generalize Demand.positions _ Drs = Q at hDt ⊢
    generalize Demand.unit H.length = Uc at hDr ⊢
    generalize σ.factor = f at hDr ⊢
    have e₁ : ϖ ·ᶜ ((π * f + c) ·ᶜ Dχ +ᶜ ρ ·ᶜ ((π * f) ·ᶜ Da +ᶜ Rc)) +ᶜ
        ((ϖ * π * (f * ρ)) ·ᶜ Uc +ᶜ (A₂ +ᶜ A₃)) =
        ((ϖ * π) ·ᶜ ((f * ρ) ·ᶜ (Uc +ᶜ Da) +ᶜ f ·ᶜ Dχ) +ᶜ A₂) +ᶜ
          (ϖ ·ᶜ c ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc +ᶜ A₃) := by
      funext x
      show ϖ * ((π * f + c) * Dχ x + ρ * (π * f * Da x + Rc x)) +
          (ϖ * π * (f * ρ) * Uc x + (A₂ x + A₃ x)) =
        (ϖ * π * (f * ρ * (Uc x + Da x) + f * Dχ x) + A₂ x) +
          (ϖ * (c * Dχ x) + ϖ * (ρ * Rc x) + A₃ x)
      rw [(by decide : ∀ ϖ π f c ρ d a r : Multiplicity,
          ϖ * ((π * f + c) * d + ρ * (π * f * a + r)) =
            ϖ * π * (f * ρ * a + f * d) + (ϖ * (c * d) + ϖ * (ρ * r))) ϖ π f c ρ (Dχ x) (Da x)
          (Rc x),
        (by decide : ∀ w f ρ u a d : Multiplicity,
          w * (f * ρ * (u + a) + f * d) = w * (f * ρ) * u + w * (f * ρ * a + f * d))
          (ϖ * π) f ρ (Uc x) (Da x) (Dχ x)]
      exact (by decide : ∀ X Y Z a b : Multiplicity,
        X + Y + (Z + (a + b)) = Z + X + a + (Y + b)) _ _ _ _ _
    rw [e₁, Demand.smul_add ϖ (π ·ᶜ Dr), ← Demand.mul_smul ϖ π]
    calc ((ϖ * π) ·ᶜ ((f * ρ) ·ᶜ (Uc +ᶜ Da) +ᶜ f ·ᶜ Dχ) +ᶜ A₂) +ᶜ
          (ϖ ·ᶜ c ·ᶜ Dχ +ᶜ ϖ ·ᶜ ρ ·ᶜ Rc +ᶜ A₃)
        ≤ᶜ (U₁ +ᶜ (ϖ * π) ·ᶜ Dr) +ᶜ (U₂ +ᶜ ϖ ·ᶜ Q) := Demand.add_le_add hDr hDt
      _ = U₁ +ᶜ U₂ +ᶜ ((ϖ * π) ·ᶜ Dr +ᶜ ϖ ·ᶜ Q) := by ac_rfl
termination_by structural h

/-- The invariant of an observation: the demand of the closure and of the arguments pay the reads
of the run and the demand of its value. -/
theorem EvalObs.conserve {P : Program} (hP : P.Usage) {ϖ : Multiplicity} (hϖ : ϖ ≠ .zero)
    {H H' : Heap} {a i c₀ : Nat} {ψ₀ : ResultOwnership Multiplicity c₀} {ς₀ : Multiplicity}
    {πb ϱb : List Multiplicity} {bs : List Nat} {v : Nat} {R : List Nat}
    (h : EvalObs P ϖ H a i ψ₀ ς₀ πb ϱb bs v H' R) {Da Db : Demand} (ha : H.ValueDemand a Da)
    (hb : H.PositionsDemand πb bs Db) :
    ∃ D, H'.ValueDemand v D ∧
      ϖ ·ᶜ (Da +ᶜ Db) +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ D :=
  match h with
  | .beta (H₂ := H₂) (w := w) (n := n) (E := E) (Ps := Ps) (πs₁ := πs₁) (ss := ss) (o := o)
      (b := b) (c := c) (πs := πs) (πs' := πs') (N := N) (R := R) hclo hget hlb hlc hπ₁ hπ₂ _ _ _
      _ hw hr => by
    obtain ⟨δ, Dδ, Dss, hPs, hEδ, hss, rfl⟩ := ha.corec_inv hclo
    obtain ⟨δᵢ, hN, hδ, hres⟩ := hPs.get i hget
    obtain ⟨Dsl, hDsl, rfl, hlss⟩ := hss.inv
    obtain ⟨Dbl, hDbl, rfl, hlbs⟩ := hb.inv
    have hH₁ : H.Extends (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (ss ++ bs)) :=
      List.prefix_append _ _
    -- The branch runs from a demand `Di` of the scope for its reads, the closure keeping `Drest`.
    have key : ∀ Di Drest, H.EnvDemand E δᵢ Di → Dδ ≤ᶜ Di +ᶜ Drest →
        ∃ Dw, H₂.ValueDemand w Dw ∧
          ϖ ·ᶜ (Dδ +ᶜ Demand.positions πs₁ Dsl +ᶜ Demand.positions πb Dbl) +ᶜ
            Demand.allocated H H₂ ≤ᶜ Demand.uses R +ᶜ ϖ ·ᶜ (Dw +ᶜ Drest) := by
      intro Di Drest hEi hDi
      obtain ⟨C, hEbr, hal⟩ := Heap.EnvDemand.bindBranch ϖ πs πs' (hEi.mono hH₁)
        (hDsl.mono hH₁) (hDbl.mono hH₁) hlb hlc
      obtain ⟨Dw, hvw, hDw⟩ := Eval.conserve hP hϖ hw hN hEbr
      refine ⟨Dw, hvw, ?_⟩
      have h₁ := Demand.positions_le_ofFn πs₁ πs (hlss.trans hlb) hπ₁ Dsl
      have h₂ := Demand.positions_le_ofFn πb πs' (hlbs.trans hlc) hπ₂ Dbl
      rw [Demand.allocated_trans hH₁ hw.extends, hal]
      rw [Demand.smul_add, Demand.smul_add, Demand.smul_add] at hDw
      generalize Demand.allocated _ H₂ = A at hDw ⊢
      generalize Demand.uses R = U at hDw ⊢
      generalize Demand.positions πs₁ Dsl = P₁ at h₁ ⊢
      generalize Demand.positions πb Dbl = P₂ at h₂ ⊢
      generalize Demand.positions (List.ofFn πs) Dsl = Q₁ at h₁ hDw ⊢
      generalize Demand.positions (List.ofFn πs') Dbl = Q₂ at h₂ hDw ⊢
      calc ϖ ·ᶜ (Dδ +ᶜ P₁ +ᶜ P₂) +ᶜ (ϖ ·ᶜ C +ᶜ A)
          ≤ᶜ ϖ ·ᶜ (Di +ᶜ Drest +ᶜ Q₁ +ᶜ Q₂) +ᶜ (ϖ ·ᶜ C +ᶜ A) :=
            Demand.add_le_add_right (Demand.smul_le_smul ϖ
              (Demand.add_le_add (Demand.add_le_add hDi h₁) h₂)) _
        _ = (ϖ ·ᶜ Di +ᶜ ϖ ·ᶜ C +ᶜ (ϖ ·ᶜ Q₁ +ᶜ ϖ ·ᶜ Q₂) +ᶜ A) +ᶜ ϖ ·ᶜ Drest := by
            rw [Demand.smul_add, Demand.smul_add, Demand.smul_add]
            ac_rfl
        _ ≤ᶜ (U +ᶜ ϖ ·ᶜ Dw) +ᶜ ϖ ·ᶜ Drest := Demand.add_le_add_right hDw _
        _ = U +ᶜ ϖ ·ᶜ (Dw +ᶜ Drest) := by
            rw [Demand.smul_add]
            ac_rfl
    cases hr with
    | none =>
      obtain ⟨Di, hDi, hEi⟩ := hEδ.le hδ
      obtain ⟨Dw, hvw, hDw⟩ := key Di 𝟘ᵛ hEi (by rwa [Demand.add_zero])
      rw [Demand.add_zero] at hDw
      exact ⟨Dw, hvw, by rw [Demand.add_assoc] at hDw; rwa [Demand.add_assoc]⟩
    | done _ hwv hπd _ =>
      obtain ⟨Di, hDi, hEi⟩ := hEδ.le hδ
      obtain ⟨Dw, hvw, hDw⟩ := key Di 𝟘ᵛ hEi (by rwa [Demand.add_zero])
      obtain ⟨Ds, hDs, rfl, -⟩ := (hvw.ctor_inv hwv).inv
      obtain _ | ⟨hx, hDs⟩ := hDs
      cases hDs
      refine ⟨_, hx, ?_⟩
      refine Demand.le_trans hDw (Demand.add_le_add_left _ fun y => ?_)
      exact Multiplicity.done_le ϖ _ _ hπd
    | next hwv hu =>
      obtain ⟨D', hD', hE'⟩ := hEδ.le (hres (by simp))
      obtain ⟨Di, Drest, rfl, hEi, hEr⟩ := hE'.split
      obtain ⟨Dw, hvw, hDw⟩ := key Di Drest hEi hD'
      obtain ⟨Ds, hDs, rfl, -⟩ := (hvw.ctor_inv hwv).inv
      obtain _ | ⟨hx, hDs⟩ := hDs
      cases hDs
      obtain ⟨Dss', hDss', rfl⟩ := Unpack.demand hu hx
      refine ⟨_, .corec List.getElem?_concat_length hPs
        ((hEr.mono (hH₁.trans hw.extends)).mono (List.prefix_append _ _))
          (Heap.PositionsDemand.of_forall₂ (hDss'.mono (List.prefix_append _ _))
            (by simp [hu.length])), ?_⟩
      rw [Demand.allocated_trans (hH₁.trans hw.extends) (List.prefix_append _ _),
        Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
      refine Demand.le_trans hDw (Demand.le_of_eq ?_)
      simp only [Demand.positions, Demand.positions_map_mul, Demand.add_zero]
      rw [Demand.add_comm Drest]
    | erased hwv =>
      obtain ⟨D', hD', hE'⟩ := hEδ.le (hres (by simp))
      obtain ⟨Di, Drest, rfl, hEi, hEr⟩ := hE'.split
      obtain ⟨Dw, hvw, hDw⟩ := key Di Drest hEi hD'
      obtain ⟨Ds, hDs, rfl, -⟩ := (hvw.ctor_inv hwv).inv
      obtain _ | ⟨hx, hDs⟩ := hDs
      cases hDs
      refine ⟨_, .corec List.getElem?_concat_length hPs
        ((hEr.mono (hH₁.trans hw.extends)).mono (List.prefix_append _ _))
          (Heap.PositionsDemand.of_forall₂
            (List.Pointwise.replicate (hx.mono (List.prefix_append _ _)) _) (by simp)), ?_⟩
      rw [Demand.allocated_trans (hH₁.trans hw.extends) (List.prefix_append _ _),
        Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
      refine Demand.le_trans hDw (Demand.le_of_eq ?_)
      simp only [Demand.positions, Demand.positions_replicate_zero, Demand.zero_smul,
        Demand.add_zero, Demand.zero_add]
termination_by structural h

end

/-! ## Conservation -/

/-- A value that holds no closure has only the demand `0`. -/
theorem Heap.IsData.demand {H : Heap} : {ℓ : Nat} → H.IsData ℓ → {D : Demand} →
    H.ValueDemand ℓ D → D = 𝟘ᵛ
  | _, .erased h, _, .erased _ => rfl
  | _, .erased h, _, .ctor h' _ | _, .erased h, _, .corec h' _ _ _ => by
    rw [h] at h'
    cases h'
  | _, .ctor (as := as₀) h hs, _, hD => by
    obtain ⟨Ds, hDs, rfl, -⟩ := (hD.ctor_inv h).inv
    -- The demands of the fields, each `0`, sum to `0`.
    have hz : ∀ (as : List Nat) (Ds : List Demand), (∀ a ∈ as, a ∈ as₀) → H.ValueDemands as Ds →
        ∀ πs : List Multiplicity, Demand.positions πs Ds = 𝟘ᵛ := by
      intro as Ds has hDs
      induction hDs with
      | nil => intro πs; cases πs <;> rfl
      | cons hv _ ih =>
        intro πs
        cases πs with
        | nil => rfl
        | cons π πs =>
          rw [Demand.positions, Heap.IsData.demand (hs _ (has _ List.mem_cons_self)) hv,
            ih (fun a ha => has a (List.mem_cons_of_mem _ ha)), Demand.smul_zero, Demand.add_zero]
    exact hz _ Ds (fun _ h => h) hDs _

-- ADE: `▸-⇾*`, in `Graded/Heap/Usage/Reduction.agda`, for the usage along the reduction of a
-- whole run.
/-- `cons`: a closed term of the target language, whose usage reads no variable, run at the weight
`1` in the empty heap, reads each cell of its heap as the multiplicity of the cell allows, once the
reads that its value can still do are counted: a cell of the multiplicity `1` is read once, or not
read and left to the value; a cell of the multiplicity `0` is never read.
RFC: `\mathsf{cons}` -/
theorem Eval.conservation {P : Program} (hP : P.Usage) {M : Target 0}
    (hM : Target.Usage 𝟘ᵛ M) {a : Nat} {H : Heap} {R : List Nat} (h : Eval P .one [] [] M a H R) :
    ∃ D, H.ValueDemand a D ∧ ∀ c π ℓ, H[c]? = some (.cell π ℓ) → π ≤ Demand.uses R c + D c := by
  obtain ⟨D, hv, hD⟩ := Eval.conserve hP (by decide) h hM .nil
  refine ⟨D, hv, fun c π ℓ hc => ?_⟩
  have hc' := hD c
  have ha : Demand.allocated [] H c = π := by
    simp only [Demand.allocated, List.length_nil, Nat.zero_le, ↓reduceIte, hc]
  simp only [Sic.Math.Vector.add, Sic.Math.Vector.smul, ha] at hc'
  exact (by decide : ∀ π u d : Multiplicity, .one * .zero + π ≤ u + .one * d → π ≤ u + d) _ _ _
    hc'

/-- `cons_data`: a closed term of the target language, whose usage reads no variable, run at the
weight `1` in the empty heap to a value that holds no closure, reads each cell of the multiplicity
`1` of its heap exactly once, and never a cell of the multiplicity `0`.
RFC: `\mathsf{cons}_{\mathsf{data}}` -/
theorem Eval.conservation_data {P : Program} (hP : P.Usage) {M : Target 0}
    (hM : Target.Usage 𝟘ᵛ M) {a : Nat} {H : Heap} {R : List Nat} (h : Eval P .one [] [] M a H R)
    (hd : H.IsData a) (c ℓ : Nat) :
    (H[c]? = some (.cell .one ℓ) → R.count c = 1) ∧
      (H[c]? = some (.cell .zero ℓ) → R.count c = 0) := by
  obtain ⟨D, hv, hD⟩ := Eval.conservation hP hM h
  rw [hd.demand hv] at hD
  refine ⟨fun hc => Demand.uses_eq_one.1 ?_, fun hc => Demand.uses_eq_zero.1 ?_⟩
  · exact (by decide : ∀ u : Multiplicity, .one ≤ u + .zero → u = .one) _ (hD c .one ℓ hc)
  · exact (by decide : ∀ u : Multiplicity, .zero ≤ u + .zero → u = .zero) _ (hD c .zero ℓ hc)

end Sic.Core
