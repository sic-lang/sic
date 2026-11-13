module

public import Sic.Core.Evaluation.Demand

/-!
# Conservation

The conservation of the bindings of annex 17 of RFC 36: a run of a term of the target language that
reads its variables as its usage allows reads each cell that it allocates, of the multiplicity `π`,
as `π` allows, once the reads that the value that it computes can still do are counted, its demand.
The invariant, `𝒫; κ; H; E ⊢ M ⇓ a; H'; R` with `ν ⊢ M ▶` and `H ⊢ E ▶_ν D_E`, bounds the demand
of the environment, at the weight `κ`, plus the multiplicities of the cells that the run allocates,
by the reads of the run plus the demand of its value, at the weight: `κ · D_E + new_H(H, H') ≤ #R +
κ · D`.
A closed term, run at the weight `1`, then reads each cell of the multiplicity `1` that it allocates
once, or leaves the read to its value, and never reads a cell of the multiplicity `0`; a value
without closure leaves no read, so that each such cell is read exactly once.

ADE prove the resource correctness of their machine by the usage of its states, in
`Graded/Heap/Usage/Reduction.agda`, whose heap holds the grades that remain: the demands here are
these grades, which the run does not store.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-! ## Definitions -/

-- ADE: none.
/-- `new_H(H, H')`: the multiplicities of the cells that a run from the heap `H` to the heap `H'`
allocates, `0` at every other address.
RFC: `\mathsf{new}_H` -/
def Demand.allocated (H H' : Heap) : Demand := fun c =>
  if H.length ≤ c then
    match H'[c]? with
    | some (.cell π _) => π
    | _ => .zero
  else .zero

-- ADE: none.
/-- `⊢ 𝒫 ▶`: each body of the program reads no variable, and its binders as their multiplicities
allow.
RFC: `\mathsf{usage}_{\mathcal{P}}` -/
def Program.Usage (P : Program) : Prop :=
  ∀ f qs ps M, P f qs ps = some M → Target.Usage (𝟘ᵛ : MultiplicityVector 0) M

-- ADE: none.
/-- `data_H(ℓ)`: the value at the address `ℓ` holds no closure, `↯` or a constructor whose fields
are such values. -/
inductive Heap.IsData (H : Heap) : Nat → Prop where
  /-- `↯`.
  RFC: `\mathsf{data}_\ell.\text{↯}` -/
  | erased {ℓ : Nat} (h : H[ℓ]? = some .erased) : Heap.IsData H ℓ
  /-- A constructor whose fields hold no closure.
  RFC: `\mathsf{data}_\ell.c` -/
  | ctor {ℓ i : Nat} {πs : List Multiplicity} {as : List Nat}
      (h : H[ℓ]? = some (.ctor i πs as)) (hs : ∀ a ∈ as, Heap.IsData H a) : Heap.IsData H ℓ

/-! ## Demands -/

namespace Demand

/-- The order of the demands is reflexive. -/
theorem le_refl (D : Demand) : D ≤ᶜ D := fun c => Multiplicity.le_refl' (D c)

/-- The order of the demands is transitive. -/
theorem le_trans {D₁ D₂ D₃ : Demand} (h₁ : D₁ ≤ᶜ D₂) (h₂ : D₂ ≤ᶜ D₃) : D₁ ≤ᶜ D₃ :=
  fun c => Multiplicity.le_trans' _ _ _ (h₁ c) (h₂ c)

/-- Two equal demands are in order. -/
theorem le_of_eq {D₁ D₂ : Demand} (h : D₁ = D₂) : D₁ ≤ᶜ D₂ := h ▸ le_refl D₁

/-- The addition of the demands is monotone. -/
theorem add_le_add {D₁ D₂ D₃ D₄ : Demand} (h₁ : D₁ ≤ᶜ D₂) (h₂ : D₃ ≤ᶜ D₄) :
    D₁ +ᶜ D₃ ≤ᶜ D₂ +ᶜ D₄ :=
  Sic.Math.Vector.add_le_add Multiplicity.modality h₁ h₂

/-- The multiplication of a demand by a multiplicity is monotone. -/
theorem smul_le_smul (π : Multiplicity) {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) : π ·ᶜ D₁ ≤ᶜ π ·ᶜ D₂ :=
  Sic.Math.Vector.smul_le_smul Multiplicity.modality π h

/-- The addition of the demands is associative. -/
theorem add_assoc (D₁ D₂ D₃ : Demand) : D₁ +ᶜ D₂ +ᶜ D₃ = D₁ +ᶜ (D₂ +ᶜ D₃) :=
  (Sic.Math.Vector.module Multiplicity.modality).add_assoc D₁ D₂ D₃

/-- The addition of the demands is commutative. -/
theorem add_comm (D₁ D₂ : Demand) : D₁ +ᶜ D₂ = D₂ +ᶜ D₁ :=
  (Sic.Math.Vector.module Multiplicity.modality).add_comm D₁ D₂

/-- `0` is a unit of the addition of the demands. -/
theorem zero_add (D : Demand) : 𝟘ᵛ +ᶜ D = D :=
  (Sic.Math.Vector.module Multiplicity.modality).zero_add D

/-- `0` is a unit of the addition of the demands, on the right. -/
theorem add_zero (D : Demand) : D +ᶜ 𝟘ᵛ = D := by
  rw [add_comm, zero_add]

/-- The multiplication of a demand distributes over their addition. -/
theorem smul_add (π : Multiplicity) (D₁ D₂ : Demand) : π ·ᶜ (D₁ +ᶜ D₂) = π ·ᶜ D₁ +ᶜ π ·ᶜ D₂ :=
  (Sic.Math.Vector.module Multiplicity.modality).smul_add π D₁ D₂

/-- The multiplication of a demand is associative. -/
theorem mul_smul (π₁ π₂ : Multiplicity) (D : Demand) : (π₁ * π₂) ·ᶜ D = π₁ ·ᶜ (π₂ ·ᶜ D) :=
  (Sic.Math.Vector.module Multiplicity.modality).mul_smul π₁ π₂ D

/-- `0` times a demand is `0`. -/
theorem zero_smul (D : Demand) : Multiplicity.zero ·ᶜ D = 𝟘ᵛ :=
  (Sic.Math.Vector.module Multiplicity.modality).zero_smul D

/-- A multiplicity times `0` is `0`. -/
theorem smul_zero (π : Multiplicity) : π ·ᶜ (𝟘ᵛ : Demand) = 𝟘ᵛ :=
  (Sic.Math.Vector.module Multiplicity.modality).smul_zero π

/-- The demand of one read is below itself at a weight other than `0`. -/
theorem smul_unit_le {κ : Multiplicity} (hκ : κ ≠ .zero) (c : Nat) : κ ·ᶜ unit c ≤ᶜ unit c :=
  fun _ => Multiplicity.mul_le_self κ _ hκ

end Demand

/-! ## Allocations -/

/-- A run that allocates nothing allocates no cell. -/
theorem Demand.allocated_self (H : Heap) : Demand.allocated H H = 𝟘ᵛ := by
  funext c
  simp only [Demand.allocated]
  split
  · rename_i h
    rw [List.getElem?_eq_none h]
    rfl
  · rfl

/-- The cells that two runs one after the other allocate are those of each. -/
theorem Demand.allocated_trans {H₁ H₂ H₃ : Heap} (h₁ : H₁.Extends H₂) (h₂ : H₂.Extends H₃) :
    Demand.allocated H₁ H₃ = Demand.allocated H₁ H₂ +ᶜ Demand.allocated H₂ H₃ := by
  funext c
  have hl₁ := h₁.length_le
  show _ = Demand.allocated H₁ H₂ c + Demand.allocated H₂ H₃ c
  simp only [Demand.allocated]
  by_cases hc₁ : H₁.length ≤ c
  · by_cases hc₂ : H₂.length ≤ c
    · rw [List.getElem?_eq_none hc₂]
      simp only [hc₁, hc₂, ↓reduceIte]
      exact (Multiplicity.modality.semiring.zero_add _).symm
    · have hc₂' : c < H₂.length := Nat.lt_of_not_le hc₂
      obtain ⟨v, hv⟩ : ∃ v, H₂[c]? = some v := ⟨_, List.getElem?_eq_getElem hc₂'⟩
      rw [h₂.getElem? hv, hv]
      simp only [hc₁, hc₂, ↓reduceIte]
      exact (Multiplicity.modality.semiring.add_comm _ _).trans
        (Multiplicity.modality.semiring.zero_add _) |>.symm
  · have hc₂ : ¬ H₂.length ≤ c := fun h => hc₁ (Nat.le_trans hl₁ h)
    simp only [hc₁, hc₂, ↓reduceIte]
    rfl

/-- A value other than a cell, allocated, allocates no cell. -/
theorem Demand.allocated_append {H : Heap} {v : Value} (hv : ∀ π a, v ≠ .cell π a) :
    Demand.allocated H (H ++ [v]) = 𝟘ᵛ := by
  funext c
  simp only [Demand.allocated]
  split
  · rename_i h
    rcases Nat.lt_or_ge c (H.length + 1) with hc | hc
    · have hc' : c = H.length := by omega
      subst hc'
      rw [List.getElem?_concat_length]
      split
      · rename_i π a h'
        cases h'
        exact (hv π a rfl).elim
      · rfl
    · rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  · rfl

/-! ## Skeletons -/

mutual

-- ADE: none.
/-- A skeleton reads no cell, allocates none, and its value has the demand `0`. -/
theorem Target.IsSkeleton.conserve {P : Program} {κ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {M : Target n} {a : Nat} {R : List Nat} :
    M.IsSkeleton → Eval P κ H E M a H' R →
      R = [] ∧ Demand.allocated H H' = 𝟘ᵛ ∧ Heap.ValueDemand H' a 𝟘ᵛ
  | .erased, h => by
    cases h
    exact ⟨rfl, Demand.allocated_append (fun _ _ h => Value.noConfusion h),
      .erased List.getElem?_concat_length⟩
  | .ctor hs, h => by
    cases h with
    | ctor hev =>
    obtain ⟨rfl, hal, hD⟩ := Targets.IsSkeleton.conserve hs hev
    refine ⟨rfl, ?_, .ctor List.getElem?_concat_length (hD.mono (List.prefix_append _ _))⟩
    rw [Demand.allocated_trans hev.extends (List.prefix_append _ _), hal,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.zero_add]

-- ADE: none.
/-- Skeletons read no cell, allocate none, and their values have the demand `0`. -/
theorem Targets.IsSkeleton.conserve {P : Program} {κ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {Ms : Targets n} {as : List Nat} {R : List Nat} :
    Ms.IsSkeleton → EvalAll P κ H E Ms as H' R →
      R = [] ∧ Demand.allocated H H' = 𝟘ᵛ ∧ Heap.PositionsDemand H' Ms.multiplicities as 𝟘ᵛ
  | .nil, h => by
    cases h
    exact ⟨rfl, Demand.allocated_self _, .nil⟩
  | .cons (π := π) hM hMs, h => by
    cases h with
    | cons hev hevs =>
    obtain ⟨rfl, hal₁, hD₁⟩ := Target.IsSkeleton.conserve hM hev
    obtain ⟨rfl, hal₂, hD₂⟩ := Targets.IsSkeleton.conserve hMs hevs
    refine ⟨rfl, ?_, ?_⟩
    · rw [Demand.allocated_trans hev.extends hevs.extends, hal₁, hal₂, Demand.zero_add]
    · have h := Heap.PositionsDemand.cons (π := π) (hD₁.mono hevs.extends) hD₂
      rwa [Demand.smul_zero, Demand.zero_add] at h

end

/-! ## Inversions of the Demands of the Environments -/

-- ADE: none.
/-- The demand of an environment for a vector of `0`s is `0`. -/
theorem Heap.EnvDemand.eq_zero {H : Heap} : {n : Nat} → {E : List Nat} →
    {ν : MultiplicityVector n} → {D : Demand} → Heap.EnvDemand H E ν D → (∀ x, ν x = .zero) →
      D = 𝟘ᵛ
  | _, _, _, _, .nil, _ => rfl
  | _, _, ν, _, .cons _ _ hE, hν => by
    rw [Heap.EnvDemand.eq_zero hE fun x => hν x.succ, hν 0, Demand.zero_smul, Demand.zero_add]

-- ADE: none.
/-- The demand of an environment for the vector of one read of the variable `x` is that of one read
of its cell, and of a use of its value. -/
theorem Heap.EnvDemand.var_inv {H : Heap} : {n : Nat} → {E : List Nat} →
    {ν : MultiplicityVector n} → {D : Demand} → Heap.EnvDemand H E ν D → (x : Fin n) →
      ν x = .one → (∀ y, y ≠ x → ν y = .zero) →
      ∃ c π ℓ Dx, E[(x : Nat)]? = some c ∧ H[c]? = some (.cell π ℓ) ∧
        Heap.ValueDemand H ℓ Dx ∧ D = Demand.unit c +ᶜ Dx
  | _, _, _, _, .nil, x, _, _ => x.elim0
  | _, c :: E, ν, _, .cons (D₁ := D₁) hc hv hE, x, hx, hy => by
    cases x using Fin.cases with
    | zero =>
      refine ⟨c, _, _, D₁, rfl, hc, hv, ?_⟩
      rw [Heap.EnvDemand.eq_zero hE fun y => hy y.succ (Fin.succ_ne_zero y), hx,
        Demand.add_zero]
      exact (Sic.Math.Vector.module Multiplicity.modality).one_smul _
    | succ x =>
      obtain ⟨c', π, ℓ, Dx, hx', hc', hv', rfl⟩ := Heap.EnvDemand.var_inv hE x hx
        fun y hyx => hy y.succ fun h => hyx (Fin.succ_inj.1 h)
      refine ⟨c', π, ℓ, Dx, hx', hc', hv', ?_⟩
      rw [hy 0 (Fin.succ_ne_zero x).symm, Demand.zero_smul, Demand.zero_add]

/-! ## Inversions of the Usage -/

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
theorem recursor_inv {ρ : Multiplicity} {M : Target n} {Ns : TargetBranches n} :
    {ν : MultiplicityVector n} → {M' : Target n} → Target.Usage ν M' → M' = .recursor ρ M Ns →
      ∃ ν₁ χ, ν ≤ᶜ (ρ ·ᶜ ν₁) +ᶜ χ ∧ Target.Usage ν₁ M ∧ (ρ = .zero → M.IsSkeleton) ∧
        TargetBranches.Usage χ Ns
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
theorem obs_inv {M : Target n} {i : Nat} {Ms : Targets n} :
    {ν : MultiplicityVector n} → {M' : Target n} → Target.Usage ν M' → M' = .obs M i Ms →
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

/-! ## Sums of Demands -/

-- ADE: none.
/-- `H ⊢ ℓ̄ ▶ D̄`: the values at the addresses `ℓ̄` have the demands `D̄`, one by one. -/
inductive Heap.ValueDemands (H : Heap) : List Nat → List Demand → Prop where
  /-- No value. -/
  | nil : Heap.ValueDemands H [] []
  /-- The first value and the others. -/
  | cons {ℓ : Nat} {as : List Nat} {D : Demand} {Ds : List Demand} (h : Heap.ValueDemand H ℓ D)
      (hs : Heap.ValueDemands H as Ds) : Heap.ValueDemands H (ℓ :: as) (D :: Ds)

-- ADE: none.
/-- `Σ π̄ · D̄`: the demands `Ds`, each times the multiplicity at its position in `πs`. -/
def Demand.positions : List Multiplicity → List Demand → Demand
  | π :: πs, D :: Ds => π ·ᶜ D +ᶜ Demand.positions πs Ds
  | _, _ => 𝟘ᵛ

-- ADE: none.
/-- The reads of the cells that a binder allocates from the address `c`, one for each binder, each
as many times as its multiplicity. -/
def Demand.cells (c : Nat) : List (Multiplicity × Nat × Demand) → Demand
  | b :: bs => b.1 ·ᶜ Demand.unit c +ᶜ Demand.cells (c + 1) bs
  | [] => 𝟘ᵛ

-- ADE: none.
/-- The uses of the values that a binder binds, each as many times as its multiplicity. -/
def Demand.values : List (Multiplicity × Nat × Demand) → Demand
  | b :: bs => b.1 ·ᶜ b.2.2 +ᶜ Demand.values bs
  | [] => 𝟘ᵛ

/-- The demand of positions is the sum of the demands of their values, each times its multiplicity.
-/
theorem Heap.PositionsDemand.inv {H : Heap} : {πs : List Multiplicity} → {as : List Nat} →
    {D : Demand} → Heap.PositionsDemand H πs as D →
      ∃ Ds, Heap.ValueDemands H as Ds ∧ D = Demand.positions πs Ds ∧
        πs.length = as.length
  | _, _, _, .nil => ⟨[], .nil, rfl, rfl⟩
  | _, _, _, .cons h hs => by
    obtain ⟨Ds, hDs, rfl, hl⟩ := Heap.PositionsDemand.inv hs
    exact ⟨_ :: Ds, .cons h hDs, rfl, congrArg (· + 1) hl⟩

/-- Positions whose values have demands have the sum of these demands, each times its multiplicity.
-/
theorem Heap.PositionsDemand.of_forall₂ {H : Heap} : {πs : List Multiplicity} → {as : List Nat} →
    {Ds : List Demand} → Heap.ValueDemands H as Ds → πs.length = as.length →
      Heap.PositionsDemand H πs as (Demand.positions πs Ds)
  | [], _, _, .nil, _ => .nil
  | _ :: _, _, _, .cons h hs, hl => .cons h (Heap.PositionsDemand.of_forall₂ hs (Nat.succ.inj hl))
  | [], _, _, .cons _ _, hl | _ :: _, _, _, .nil, hl => nomatch hl

/-- The sum of demands at multiplicities each times `π` is `π` times their sum. -/
theorem Demand.positions_map_mul (π : Multiplicity) :
    (πs : List Multiplicity) → (Ds : List Demand) →
      Demand.positions (πs.map (π * ·)) Ds = π ·ᶜ Demand.positions πs Ds
  | π' :: πs, D :: Ds => by
    rw [List.map_cons, Demand.positions, Demand.positions, Demand.positions_map_mul π πs Ds,
      Demand.smul_add, Demand.mul_smul]
  | [], _ => (Demand.smul_zero π).symm
  | _ :: _, [] => (Demand.smul_zero π).symm

/-- The demands at the multiplicity `0` sum to `0`. -/
theorem Demand.positions_replicate_zero : (k : Nat) → (Ds : List Demand) →
    Demand.positions (List.replicate k .zero) Ds = 𝟘ᵛ
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: Ds => by
    rw [List.replicate_succ, Demand.positions, Demand.positions_replicate_zero k Ds,
      Demand.zero_smul, Demand.zero_add]

/-- The uses of the values of two binders joined are those of each. -/
theorem Demand.values_append : (bs₁ bs₂ : List (Multiplicity × Nat × Demand)) →
    Demand.values (bs₁ ++ bs₂) = Demand.values bs₁ +ᶜ Demand.values bs₂
  | [], _ => (Demand.zero_add _).symm
  | b :: bs₁, bs₂ => by
    rw [List.cons_append, Demand.values, Demand.values, Demand.values_append bs₁ bs₂,
      Demand.add_assoc]

/-- The uses of the values of a binder are the sum of their demands at its multiplicities. -/
theorem Demand.values_zip : (πs : List Multiplicity) → (as : List Nat) → (Ds : List Demand) →
    πs.length = as.length → as.length = Ds.length →
      Demand.values (πs.zip (as.zip Ds)) = Demand.positions πs Ds
  | [], [], [], _, _ => rfl
  | π :: πs, a :: as, D :: Ds, h₁, h₂ => by
    rw [List.zip_cons_cons, List.zip_cons_cons, Demand.values, Demand.positions,
      Demand.values_zip πs as Ds (Nat.succ.inj h₁) (Nat.succ.inj h₂)]
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _, [], _ :: _, _, h | _, _ :: _, [], _, h =>
    nomatch h

/-- The reads of the cells of a binder with one more variable are those of the others, and of the
last cell. -/
theorem Demand.cells_concat : (c : Nat) → (bs : List (Multiplicity × Nat × Demand)) →
    (b : Multiplicity × Nat × Demand) →
      Demand.cells c (bs ++ [b]) = Demand.cells c bs +ᶜ b.1 ·ᶜ Demand.unit (c + bs.length)
  | c, [], b => by
    rw [List.nil_append, Demand.cells, Demand.cells, Demand.cells, Demand.add_zero,
      Demand.zero_add]
    rfl
  | c, b' :: bs, b => by
    rw [List.cons_append, Demand.cells, Demand.cells, Demand.cells_concat (c + 1) bs b,
      Demand.add_assoc, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- The uses of the values of a binder with one more variable are those of the others, and of the
last value. -/
theorem Demand.values_concat (bs : List (Multiplicity × Nat × Demand))
    (b : Multiplicity × Nat × Demand) :
    Demand.values (bs ++ [b]) = Demand.values bs +ᶜ b.1 ·ᶜ b.2.2 := by
  rw [Demand.values_append, Demand.values, Demand.values, Demand.add_zero]

/-! ## Inversions of the Demands of the Values -/

/-- The demand of a constructor is that of its fields. -/
theorem Heap.ValueDemand.ctor_inv {H : Heap} {ℓ i : Nat} {πs : List Multiplicity} {as : List Nat}
    {D : Demand} (hℓ : H[ℓ]? = some (.ctor i πs as)) :
    Heap.ValueDemand H ℓ D → Heap.PositionsDemand H πs as D
  | .erased h | .corec h _ _ _ => by
    rw [hℓ] at h
    cases h
  | .ctor h hs => by
    rw [hℓ] at h
    cases h
    exact hs

/-- The demand of a closure is that of its environment, for the reads of its branches, and that of
its state. -/
theorem Heap.ValueDemand.corec_inv {H : Heap} {ℓ n : Nat} {E : List Nat}
    {Ps : TargetCorecBranches n} {πs : List Multiplicity} {as : List Nat} {D : Demand}
    (hℓ : H[ℓ]? = some (.corec n E Ps πs as)) :
    Heap.ValueDemand H ℓ D → ∃ δ D₁ D₂, TargetCorecBranches.Usage δ Ps ∧
      Heap.EnvDemand H E δ D₁ ∧ Heap.PositionsDemand H πs as D₂ ∧ D = D₁ +ᶜ D₂
  | .erased h | .ctor h _ => by
    rw [hℓ] at h
    cases h
  | .corec h hPs hE hs => by
    rw [hℓ] at h
    cases h
    exact ⟨_, _, _, hPs, hE, hs, rfl⟩

/-- The demand of a value that the pairs of a state pack is the sum of the demands of the entries,
each at the multiplicity at which the pairs store it: the end of the pairs, without field, has none.
-/
theorem Unpack.demand {H : Heap} : {k x : Nat} → {πs : List Multiplicity} → {ss : List Nat} →
    Unpack H k x πs ss → {D : Demand} → Heap.ValueDemand H x D →
      ∃ Ds, Heap.ValueDemands H ss Ds ∧ D = Demand.positions πs Ds
  | _, _, _, _, .zero h, _, hD => by
    obtain ⟨Ds, hDs, rfl, -⟩ := (hD.ctor_inv h).inv
    cases hDs
    exact ⟨[], .nil, rfl⟩
  | _, _, _, _, .pair (π := π) (π' := π') (πs := πs) h hs, _, hD => by
    obtain ⟨Ds, hDs, rfl, -⟩ := (hD.ctor_inv h).inv
    obtain _ | ⟨hy, hDs⟩ := hDs
    obtain _ | ⟨hz, hDs⟩ := hDs
    cases hDs
    obtain ⟨Dss, hDss, rfl⟩ := Unpack.demand hs hz
    refine ⟨_ :: Dss, .cons hy hDss, ?_⟩
    simp only [Demand.positions, Demand.positions_map_mul, Demand.add_zero]

/-! ## Inversions of the Usage of the Branches -/

/-- The usage of the branches of a recursor gives that of each branch. -/
theorem TargetBranches.Usage.get {n : Nat} {χ : MultiplicityVector n} :
    {Ns : TargetBranches n} → TargetBranches.Usage χ Ns → (i : Nat) → {a b : Nat} →
      {πs : Fin a → Multiplicity} → {πs' : Fin b → Multiplicity} → {ks : Fin b → Option Nat} →
      {N : Target (n + (a + b))} → Ns.get i = some ⟨a, b, πs, πs', ks, N⟩ →
      ∃ δ : MultiplicityVector n, Target.Usage (δ.extendBinders πs πs') N ∧
        χ ≤ᶜ δ +ᶜ (Multiplicity.sum (fun j => if (ks j).isSome then πs' j else .zero) ·ᶜ χ) ∧
        ∀ j, (ks j).isSome → πs' j ≠ .zero
  | _, .nil, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hN hχ hk _, 0, _, _, _, _, _, _, h => by
    cases h
    exact ⟨_, hN, hχ, hk⟩
  | _, .cons _ _ _ hNs, i + 1, _, _, _, _, _, _, h => TargetBranches.Usage.get hNs i h

/-- The usage of the branches of a corecursor gives that of each branch. -/
theorem TargetCorecBranches.Usage.get {n : Nat} {δ : MultiplicityVector n} :
    {Ps : TargetCorecBranches n} → TargetCorecBranches.Usage δ Ps → (i : Nat) →
      {o : Resumption} → {b c : Nat} → {πs : Fin b → Multiplicity} →
      {πs' : Fin c → Multiplicity} → {P : Target (n + (b + c))} →
      Ps.get i = some (o, ⟨b, c, πs, πs', P⟩) →
      ∃ δᵢ : MultiplicityVector n, Target.Usage (δᵢ.extendBinders πs πs') P ∧ δ ≤ᶜ δᵢ ∧
        (o ≠ .none → δ ≤ᶜ δᵢ +ᶜ δ)
  | _, .nil, _, _, _, _, _, _, _, h => nomatch h
  | _, .cons hP hδ hr _, 0, _, _, _, _, _, _, h => by
    cases h
    exact ⟨_, hP, hδ, hr⟩
  | _, .cons _ _ _ hPs, i + 1, _, _, _, _, _, _, h => TargetCorecBranches.Usage.get hPs i h

/-! ## Binders -/

/-- A cell allocated at the end of a heap allocates its multiplicity at its address. -/
theorem Demand.allocated_cell (H : Heap) (π : Multiplicity) (a : Nat) :
    Demand.allocated H (H ++ [.cell π a]) = π ·ᶜ Demand.unit H.length := by
  funext c
  show _ = π * Demand.unit H.length c
  simp only [Demand.allocated, Demand.unit]
  by_cases hc : c = H.length
  · subst hc
    rw [List.getElem?_concat_length]
    simp only [Nat.le_refl, ↓reduceIte]
    exact (Multiplicity.modality.semiring.mul_one π).symm
  · simp only [hc, ↓reduceIte, Multiplicity.modality.semiring.mul_zero]
    split
    · rw [List.getElem?_eq_none (by simp; omega)]
    · rfl

/-- The cells that a binder allocates are its multiplicities, each times the weight. -/
theorem Demand.allocated_bind (κ : Multiplicity) :
    (H : Heap) → (bs : List (Multiplicity × Nat × Demand)) →
      Demand.allocated H (H.bind (bs.map fun b => κ * b.1) (bs.map (·.2.1))) =
        κ ·ᶜ Demand.cells H.length bs
  | H, [] => by
    show Demand.allocated H (H ++ []) = _
    rw [List.append_nil, Demand.allocated_self, Demand.cells, Demand.smul_zero]
  | H, b :: bs => by
    have e : H.bind ((b :: bs).map fun b => κ * b.1) ((b :: bs).map (·.2.1)) =
        (H ++ [Value.cell (κ * b.1) b.2.1]).bind (bs.map fun b => κ * b.1) (bs.map (·.2.1)) := by
      simp only [Heap.bind, List.map_cons, List.zipWith_cons_cons, List.append_assoc,
        List.singleton_append]
    have h₂ : (H ++ [Value.cell (κ * b.1) b.2.1]).Extends
        ((H ++ [Value.cell (κ * b.1) b.2.1]).bind (bs.map fun b => κ * b.1) (bs.map (·.2.1))) :=
      List.prefix_append _ _
    rw [e, Demand.allocated_trans (List.prefix_append _ _) h₂,
      Demand.allocated_cell, Demand.allocated_bind κ _ bs, Demand.cells, Demand.smul_add,
      Demand.mul_smul, List.length_append, List.length_singleton]

/-- The demand of an environment extended by the cells that a binder allocates from the address `c`,
for the vector extended by the multiplicities of the binder, the last variable first, adds their
reads and the uses of their values. -/
theorem Heap.EnvDemand.bindAll {H : Heap} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {D : Demand} (hE : Heap.EnvDemand H E ν D) (c : Nat) :
    (m : Nat) → (bs : List (Multiplicity × Nat × Demand)) → bs.length = m →
      (∀ l b, bs[l]? = some b → ∃ π, H[c + l]? = some (.cell π b.2.1)) →
      (∀ b ∈ bs, Heap.ValueDemand H b.2.1 b.2.2) →
      (μ : MultiplicityVector (n + m)) →
      (∀ i : Fin (n + m), (i : Nat) < m → some (μ i) = (bs[m - 1 - i]?).map (·.1)) →
      (∀ i : Fin n, μ ⟨i + m, by omega⟩ = ν i) →
      Heap.EnvDemand H ((List.range' c m).reverse ++ E) μ
        (D +ᶜ Demand.cells c bs +ᶜ Demand.values bs)
  | 0, [], _, _, _, μ, _, hμ => by
    have e : μ = ν := funext fun i => hμ i
    subst e
    rw [Demand.cells, Demand.values, Demand.add_zero, Demand.add_zero]
    exact hE
  | m + 1, bs, hl, hc, hv, μ, hμ₁, hμ₂ => by
    obtain ⟨bs', b, rfl⟩ : ∃ bs' b, bs = bs' ++ [b] :=
      match List.eq_nil_or_concat bs with
      | .inl h => by subst h; cases hl
      | .inr ⟨bs', b, h⟩ => ⟨bs', b, by rw [h, List.concat_eq_append]⟩
    have hl' : bs'.length = m := by simpa using hl
    have ih := Heap.EnvDemand.bindAll hE c m bs' hl'
      (fun l b' hb' => hc l b' (by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hb').1, hb']))
      (fun b' hb' => hv b' (List.mem_append_left _ hb'))
      (fun x => μ x.succ)
      (fun i h => by
        rw [hμ₁ i.succ (by simp only [Fin.val_succ]; omega)]
        simp only [Fin.val_succ]
        rw [show m + 1 - 1 - (↑i + 1) = m - 1 - ↑i by omega,
          List.getElem?_append_left (by omega)])
      (fun i => by
        rw [← hμ₂ i]
        congr 1)
    have hbm : (bs' ++ [b])[m]? = some b := by
      rw [List.getElem?_append_right (by omega), hl', Nat.sub_self]
      rfl
    obtain ⟨π, hπ⟩ := hc m b hbm
    have hcons := Heap.EnvDemand.cons hπ
      (hv b (List.mem_append_right _ (List.mem_singleton_self b))) ih
    have hμ0 : μ 0 = b.1 := by
      have h0 := hμ₁ 0 (by simp)
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel] at h0
      rw [hbm] at h0
      exact Option.some.inj h0
    rw [hμ0] at hcons
    have er : (List.range' c (m + 1)).reverse ++ E =
        (c + m) :: ((List.range' c m).reverse ++ E) := by
      rw [List.range'_concat, List.reverse_append, Nat.one_mul]
      rfl
    rw [er]
    have e : D +ᶜ Demand.cells c (bs' ++ [b]) +ᶜ Demand.values (bs' ++ [b]) =
        b.1 ·ᶜ (Demand.unit (c + m) +ᶜ b.2.2) +ᶜ
          (D +ᶜ Demand.cells c bs' +ᶜ Demand.values bs') := by
      rw [Demand.cells_concat, Demand.values_concat, hl']
      funext x
      show D x + (Demand.cells c bs' x + b.1 * Demand.unit (c + m) x) +
          (Demand.values bs' x + b.1 * b.2.2 x) =
        b.1 * (Demand.unit (c + m) x + b.2.2 x) + (D x + Demand.cells c bs' x + Demand.values bs' x)
      generalize D x = d
      generalize Demand.cells c bs' x = u
      generalize Demand.values bs' x = w
      generalize Demand.unit (c + m) x = e
      generalize b.2.2 x = f
      generalize b.1 = π
      revert d u w e f π
      decide
    rw [e]
    exact hcons

/-! ## Rearrangements -/

instance : Std.Associative (α := Demand) (· +ᶜ ·) := ⟨Demand.add_assoc⟩

instance : Std.Commutative (α := Demand) (· +ᶜ ·) := ⟨Demand.add_comm⟩

/-- A trace without read reads no cell. -/
theorem Demand.uses_nil : Demand.uses [] = 𝟘ᵛ := rfl

/-- The weight times a sum is the sum of the weighted demands. -/
theorem Demand.smul_add₃ (κ : Multiplicity) (D₁ D₂ D₃ : Demand) :
    κ ·ᶜ (D₁ +ᶜ D₂ +ᶜ D₃) = κ ·ᶜ D₁ +ᶜ κ ·ᶜ D₂ +ᶜ κ ·ᶜ D₃ := by
  rw [Demand.smul_add, Demand.smul_add]

/-- A demand below another stays below it with the same demand added. -/
theorem Demand.add_le_add_right {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) (D : Demand) :
    D₁ +ᶜ D ≤ᶜ D₂ +ᶜ D :=
  Demand.add_le_add h (Demand.le_refl D)

/-- A demand below another stays below it with the same demand added on the left. -/
theorem Demand.add_le_add_left (D : Demand) {D₁ D₂ : Demand} (h : D₁ ≤ᶜ D₂) :
    D +ᶜ D₁ ≤ᶜ D +ᶜ D₂ :=
  Demand.add_le_add (Demand.le_refl D) h

/-- A demand below `0` at a weight stays below `0`. -/
theorem Demand.smul_le_zero {κ : Multiplicity} {D : Demand} (h : D ≤ᶜ 𝟘ᵛ) : κ ·ᶜ D ≤ᶜ 𝟘ᵛ := by
  have h' := Demand.smul_le_smul κ h
  rwa [Demand.smul_zero] at h'

/-- Anything plus a demand below `0` is below the thing. -/
theorem Demand.add_le_of_le_zero {D₁ D₂ : Demand} (h : D₁ ≤ᶜ 𝟘ᵛ) : D₁ +ᶜ D₂ ≤ᶜ D₂ := by
  have h' := Demand.add_le_add_right h D₂
  rwa [Demand.zero_add] at h'

/-! ## Branches -/

/-- The demands of values hold in each heap that extends their heap. -/
theorem Heap.ValueDemands.mono {H H' : Heap} (hH : H.Extends H') :
    {as : List Nat} → {Ds : List Demand} → Heap.ValueDemands H as Ds → Heap.ValueDemands H' as Ds
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.mono hH) (hs.mono hH)

/-- Values with demands have as many demands. -/
theorem Heap.ValueDemands.length {H : Heap} :
    {as : List Nat} → {Ds : List Demand} → Heap.ValueDemands H as Ds → as.length = Ds.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg (· + 1) hs.length

/-- Values with demands joined have their demands joined. -/
theorem Heap.ValueDemands.append {H : Heap} :
    {as₁ : List Nat} → {Ds₁ : List Demand} → {as₂ : List Nat} → {Ds₂ : List Demand} →
      Heap.ValueDemands H as₁ Ds₁ → Heap.ValueDemands H as₂ Ds₂ →
        Heap.ValueDemands H (as₁ ++ as₂) (Ds₁ ++ Ds₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h hs, h₂ => .cons h (hs.append h₂)

/-- The same value, as many times as wanted, has its demand as many times. -/
theorem Heap.ValueDemands.replicate {H : Heap} {ℓ : Nat} {D : Demand} (h : Heap.ValueDemand H ℓ D) :
    (k : Nat) → Heap.ValueDemands H (List.replicate k ℓ) (List.replicate k D)
  | 0 => .nil
  | k + 1 => .cons h (Heap.ValueDemands.replicate h k)

/-- A value with demands has the demand at each of its positions. -/
theorem Heap.ValueDemands.mem {H : Heap} :
    {as : List Nat} → {Ds : List Demand} → Heap.ValueDemands H as Ds →
      ∀ b ∈ as.zip Ds, Heap.ValueDemand H b.1 b.2
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons h hs, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h
    · exact hs.mem b hb

/-- The unpacking of a state gives as many multiplicities as entries. -/
theorem Unpack.length {H : Heap} : {k x : Nat} → {πs : List Multiplicity} → {ss : List Nat} →
    Unpack H k x πs ss → πs.length = ss.length
  | _, _, _, _, .zero _ => rfl
  | _, _, _, _, .pair _ hs => by simp [hs.length]

/-- The cells that a binder allocates hold its addresses, at its multiplicities. -/
theorem Heap.bind_getElem? (H : Heap) : (πs : List Multiplicity) → (as : List Nat) →
    (l : Nat) → (π : Multiplicity) → (a : Nat) → πs[l]? = some π → as[l]? = some a →
      (H.bind πs as)[H.length + l]? = some (.cell π a) := by
  intro πs as l π a hπ ha
  simp only [Heap.bind]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_zipWith, hπ, ha]

/-- Demands at lower multiplicities, one by one, sum to a lower demand. -/
theorem Demand.positions_le : (πs₁ πs₂ : List Multiplicity) → πs₁.length = πs₂.length →
    (∀ (j : Nat) π₁ π₂, πs₁[j]? = some π₁ → πs₂[j]? = some π₂ → π₁ ≤ π₂) → (Ds : List Demand) →
      Demand.positions πs₁ Ds ≤ᶜ Demand.positions πs₂ Ds
  | π₁ :: πs₁, π₂ :: πs₂, hl, h, D :: Ds =>
    Demand.add_le_add (fun x => Multiplicity.mul_le_mul_right' π₁ π₂ (D x) (h 0 π₁ π₂ rfl rfl))
      (Demand.positions_le πs₁ πs₂ (Nat.succ.inj hl) (fun j => h (j + 1)) Ds)
  | [], [], _, _, _ | _ :: _, _ :: _, _, _, [] => Demand.le_refl _
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => nomatch hl

/-- The demands of positions joined are those of each, when the first are as many as their
multiplicities. -/
theorem Demand.positions_append : (πs₁ πs₂ : List Multiplicity) → (Ds₁ Ds₂ : List Demand) →
    πs₁.length = Ds₁.length →
      Demand.positions (πs₁ ++ πs₂) (Ds₁ ++ Ds₂) =
        Demand.positions πs₁ Ds₁ +ᶜ Demand.positions πs₂ Ds₂
  | [], _, [], _, _ => (Demand.zero_add _).symm
  | π :: πs₁, πs₂, D :: Ds₁, Ds₂, hl => by
    rw [List.cons_append, List.cons_append, Demand.positions, Demand.positions,
      Demand.positions_append πs₁ πs₂ Ds₁ Ds₂ (Nat.succ.inj hl), Demand.add_assoc]
  | [], _, _ :: _, _, hl | _ :: _, _, [], _, hl => nomatch hl

/-- The multiplicities of the binders of a branch, the last one first, extend the vector of the
scope. -/
theorem MultiplicityVector.extendBinders_spec {n a b : Nat} (ν : MultiplicityVector n)
    (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity) :
    (∀ i : Fin (n + (a + b)), (i : Nat) < a + b →
      some (ν.extendBinders πs πs' i) = (List.ofFn πs ++ List.ofFn πs')[a + b - 1 - i]?) ∧
    ∀ i : Fin n, ν.extendBinders πs πs' ⟨i + (a + b), by omega⟩ = ν i := by
  refine ⟨fun i hi => ?_, fun i => ?_⟩
  · simp only [MultiplicityVector.extendBinders]
    by_cases h₁ : (i : Nat) < b
    · simp only [h₁, ↓reduceDIte]
      rw [List.getElem?_append_right (by simp; omega), List.length_ofFn, List.getElem?_ofFn]
      simp only [show a + b - 1 - (i : Nat) - a < b by omega, ↓reduceDIte, Option.some.injEq]
      exact congrArg πs' (Fin.ext (by simp only; omega))
    · simp only [h₁, hi, ↓reduceDIte]
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
      simp only [show a + b - 1 - (i : Nat) < a by omega, ↓reduceDIte, Option.some.injEq]
      exact congrArg πs (Fin.ext (by simp only; omega))
  · simp only [MultiplicityVector.extendBinders, show ¬ ((i : Nat) + (a + b) < b) by omega,
      show ¬ ((i : Nat) + (a + b) < a + b) by omega, ↓reduceDIte]
    exact congrArg ν (Fin.ext (by simp only; omega))

/-- The cells that a branch allocates for its `a + b` variables, at the multiplicities of its
binders times the weight, give the environment of the branch a demand for the extended vector: that
of the scope, the reads of the new cells, and the uses of their values. -/
theorem Heap.EnvDemand.bindBranch {H : Heap} (κ : Multiplicity) {n a b : Nat} {E : List Nat}
    {δ : MultiplicityVector n} {D : Demand} (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity)
    {vs₁ vs₂ : List Nat} {Ds₁ Ds₂ : List Demand}
    (hE : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (vs₁ ++ vs₂)).EnvDemand E δ D)
    (h₁ : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (vs₁ ++ vs₂)).ValueDemands vs₁ Ds₁)
    (h₂ : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (vs₁ ++ vs₂)).ValueDemands vs₂ Ds₂)
    (hl₁ : vs₁.length = a) (hl₂ : vs₂.length = b) :
    ∃ C, (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (vs₁ ++ vs₂)).EnvDemand
        ((List.range' H.length (vs₁ ++ vs₂).length).reverse ++ E) (δ.extendBinders πs πs')
        (D +ᶜ C +ᶜ (Demand.positions (List.ofFn πs) Ds₁ +ᶜ Demand.positions (List.ofFn πs') Ds₂)) ∧
      Demand.allocated H (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (vs₁ ++ vs₂)) =
        κ ·ᶜ C := by
  have hd₁ := h₁.length
  have hd₂ := h₂.length
  let bs := (List.ofFn πs ++ List.ofFn πs').zip ((vs₁ ++ vs₂).zip (Ds₁ ++ Ds₂))
  have hlen : (List.ofFn πs ++ List.ofFn πs').length = (vs₁ ++ vs₂).length := by simp; omega
  have hlen' : (vs₁ ++ vs₂).length = (Ds₁ ++ Ds₂).length := by simp; omega
  have hfst : bs.map Prod.fst = List.ofFn πs ++ List.ofFn πs' :=
    List.map_fst_zip (by simp; omega)
  have hsnd : bs.map Prod.snd = (vs₁ ++ vs₂).zip (Ds₁ ++ Ds₂) :=
    List.map_snd_zip (by simp; omega)
  have hm₁ : bs.map (fun b => κ * b.1) = (List.ofFn πs ++ List.ofFn πs').map (κ * ·) := by
    rw [← hfst, List.map_map]
    rfl
  have hm₂ : bs.map (·.2.1) = vs₁ ++ vs₂ := by
    rw [show (fun x : Multiplicity × Nat × Demand => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← List.map_map, hsnd, List.map_fst_zip (by simp; omega)]
  have hbl : bs.length = a + b := by simp [bs]; omega
  refine ⟨Demand.cells H.length bs, ?_, ?_⟩
  · have hb := Heap.EnvDemand.bindAll hE H.length (a + b) bs hbl
      (fun l x hx => by
        obtain ⟨hx₁, hx₂⟩ := List.getElem?_zip_eq_some.1 hx
        obtain ⟨hx₂, -⟩ := List.getElem?_zip_eq_some.1 hx₂
        refine ⟨κ * x.1, Heap.bind_getElem? H _ _ l _ _ ?_ hx₂⟩
        rw [List.getElem?_map, hx₁]
        rfl)
      (fun x hx => by
        obtain ⟨-, hx⟩ := List.of_mem_zip hx
        exact (h₁.append h₂).mem x.2 hx)
      _ (fun i hi => by
        rw [(MultiplicityVector.extendBinders_spec δ πs πs').1 i hi, ← hfst, List.getElem?_map])
      (MultiplicityVector.extendBinders_spec δ πs πs').2
    rw [show (vs₁ ++ vs₂).length = a + b by simp; omega]
    rw [Demand.values_zip _ _ _ hlen hlen'] at hb
    rwa [show Demand.positions (List.ofFn πs ++ List.ofFn πs') (Ds₁ ++ Ds₂) =
      Demand.positions (List.ofFn πs) Ds₁ +ᶜ Demand.positions (List.ofFn πs') Ds₂ from
      Demand.positions_append _ _ _ _ (by simp; omega)] at hb
  · rw [← Demand.allocated_bind κ H bs, hm₁, hm₂]


/-- Demands at multiplicities below those of a binder sum to a demand below the sum at those of the
binder. -/
theorem Demand.positions_le_ofFn {b : Nat} (πs₁ : List Multiplicity) (πs : Fin b → Multiplicity)
    (hl : πs₁.length = b) (h : ∀ j : Fin b, ∃ π₁, πs₁[(j : Nat)]? = some π₁ ∧ π₁ ≤ πs j)
    (Ds : List Demand) : Demand.positions πs₁ Ds ≤ᶜ Demand.positions (List.ofFn πs) Ds :=
  Demand.positions_le _ _ (by simp [hl]) (fun j π₁ π₂ h₁ h₂ => by
    rw [List.getElem?_ofFn] at h₂
    split at h₂
    · rename_i hj
      cases h₂
      obtain ⟨π₁', h₁', hle⟩ := h ⟨j, hj⟩
      rw [h₁] at h₁'
      cases h₁'
      exact hle
    · cases h₂) Ds

/-- A term already built, of a multiplicity other than `0`, pays the demand of its value. -/
theorem Multiplicity.done_le : ∀ κ π d : Multiplicity, π ≠ .zero →
    κ * (π * d + .zero + .zero) ≤ κ * d := by decide

/-! ## Recursions -/

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

/-- The recursive results of a branch are as many as their fields and their binders. -/
theorem EvalResults.length {P : Program} {κ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {ρ : Multiplicity} {Ns : TargetBranches n} {as : List Nat} :
    {ks : List (Option Nat)} → {πs : List Multiplicity} → {rs : List Nat} → {R : List Nat} →
      EvalResults P κ H E ρ Ns as ks πs rs H' R → rs.length = ks.length ∧ πs.length = ks.length
  | _, _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, _, .erased hs | _, _, _, _, .recursor _ _ hs =>
    ⟨congrArg (· + 1) hs.length.1, congrArg (· + 1) hs.length.2⟩

/-- The recursive results of a branch are on its fields. -/
theorem EvalResults.lt {P : Program} {κ : Multiplicity} {n : Nat} {H H' : Heap}
    {E : List Nat} {ρ : Multiplicity} {Ns : TargetBranches n} {as : List Nat} :
    {ks : List (Option Nat)} → {πs : List Multiplicity} → {rs : List Nat} → {R : List Nat} →
      EvalResults P κ H E ρ Ns as ks πs rs H' R →
        ∀ (j : Nat) l, ks[j]? = some (some l) → l < as.length
  | _, _, _, _, .nil, _, _, h => nomatch h
  | _, _, _, _, .erased hs, j + 1, l, h => hs.lt j l h
  | _, _, _, _, .recursor hj _ _, 0, l, h => by
    cases h
    exact (List.getElem?_eq_some_iff.1 hj).1
  | _, _, _, _, .recursor _ _ hs, j + 1, l, h => hs.lt j l h

/-- The values with demands have a demand at each of their positions. -/
theorem Heap.ValueDemands.getElem? {H : Heap} :
    {as : List Nat} → {Ds : List Demand} → Heap.ValueDemands H as Ds → (j : Nat) → {a : Nat} →
      as[j]? = some a → Heap.ValueDemand H a (Ds.getD j 𝟘ᵛ)
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons hv _, 0, _, h => by
    cases h
    exact hv
  | _, _, .cons _ hs, j + 1, _, h => hs.getElem? j h

/-- The order of the demands chains in a calculation. -/
instance : Trans (α := Demand) (β := Demand) (γ := Demand) (· ≤ᶜ ·) (· ≤ᶜ ·) (· ≤ᶜ ·) :=
  ⟨Demand.le_trans⟩

/-- A variable read at a weight other than `0` pays its demand. -/
theorem Multiplicity.var_le : ∀ κ e u d : Multiplicity, κ ≠ .zero → e ≤ u + d →
    κ * e + .zero ≤ u + κ * d := by decide

/-! ## Invariant -/

mutual

-- ADE: `▸-⇾`, in `Graded/Heap/Usage/Reduction.agda`, for the usage of the states along a step.
/-- `cons_⇓`: a run of a term of the target language, at a weight other than `0`, whose usage
bounds its reads by `ν`, in an environment of the demand `D_E` for `ν`, reads the cells and
allocates cells as the demand of the environment allows, once the demand `D` of its value is
counted:
`κ · D_E + new_H(H, H') ≤ #R + κ · D`.
RFC: `\mathsf{cons}_\Downarrow` -/
theorem Eval.conserve {P : Program} (hP : P.Usage) {κ : Multiplicity} (hκ : κ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {M : Target n} {a : Nat} {R : List Nat}
    (h : Eval P κ H E M a H' R) {ν : MultiplicityVector n} {D_E : Demand}
    (hM : Target.Usage ν M) (hE : H.EnvDemand E ν D_E) :
    ∃ D, H'.ValueDemand a D ∧ κ ·ᶜ D_E +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ D :=
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
    exact fun y => Multiplicity.var_le κ _ _ _ hκ (hD' y)
  | .const hf hb => by
    obtain ⟨D', hD', hE'⟩ := hE.le (hM.zero_inv (.inr ⟨_, _, _, rfl⟩))
    rw [hE'.eq_zero fun _ => rfl] at hD'
    obtain ⟨D, hv, hD⟩ := Eval.conserve hP hκ hb (hP _ _ _ _ hf) .nil
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
    obtain ⟨D, hv, hD⟩ := EvalAll.conserve hP hκ hs hMs hE'
    refine ⟨D, .ctor List.getElem?_concat_length (hv.mono (List.prefix_append _ _)), ?_⟩
    rw [Demand.allocated_trans hs.extends (List.prefix_append _ _),
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
    exact Demand.le_trans (Demand.add_le_add_right (Demand.smul_le_smul κ hD') _) hD
  | .recursor (ρ := ρ) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) hev hr => by
    obtain ⟨ν₁, χ, hle, hM₁, hz, hNs⟩ := hM.recursor_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁', Dχ, rfl, hE₁', hEχ⟩ := hE'.split
    obtain ⟨D₁, rfl, hE₁⟩ := hE₁'.unsmul
    have hH := hev.extends
    by_cases hρ : ρ = .zero
    · obtain ⟨rfl, hal, hva⟩ := (hz hρ).conserve hev
      obtain ⟨D, hv, hD⟩ := EvalRec.conserve hP hκ hr hNs (hEχ.mono hH) hva
      refine ⟨D, hv, ?_⟩
      rw [Demand.allocated_trans hH hr.extends, hal, Demand.zero_add, List.nil_append]
      refine Demand.le_trans (Demand.add_le_add_right (Demand.smul_le_smul κ hD') _)
        (Demand.le_trans (Demand.le_of_eq ?_) hD)
      rw [hρ, Demand.zero_smul, Demand.zero_add, Demand.smul_zero, Demand.add_zero]
    · obtain ⟨Da, hva, hDa⟩ := Eval.conserve hP (Multiplicity.mul_ne_zero κ ρ hκ hρ) hev hM₁ hE₁
      obtain ⟨D, hv, hD⟩ := EvalRec.conserve hP hκ hr hNs (hEχ.mono hH) hva
      refine ⟨D, hv, ?_⟩
      rw [Demand.allocated_trans hH hr.extends, Demand.uses_append]
      rw [Demand.mul_smul, Demand.mul_smul] at hDa
      rw [Demand.smul_add] at hD
      generalize Demand.allocated H H₂ = A₁ at hDa ⊢
      generalize Demand.allocated H₂ H' = A₂ at hD ⊢
      generalize Demand.uses R₁ = U₁ at hDa ⊢
      generalize Demand.uses R₂ = U₂ at hD ⊢
      calc κ ·ᶜ D_E +ᶜ (A₁ +ᶜ A₂)
          ≤ᶜ κ ·ᶜ (ρ ·ᶜ D₁ +ᶜ Dχ) +ᶜ (A₁ +ᶜ A₂) :=
            Demand.add_le_add_right (Demand.smul_le_smul κ hD') _
        _ = (κ ·ᶜ ρ ·ᶜ D₁ +ᶜ A₁) +ᶜ (κ ·ᶜ Dχ +ᶜ A₂) := by
          rw [Demand.smul_add]
          ac_rfl
        _ ≤ᶜ (U₁ +ᶜ κ ·ᶜ ρ ·ᶜ Da) +ᶜ (κ ·ᶜ Dχ +ᶜ A₂) := Demand.add_le_add_right hDa _
        _ = U₁ +ᶜ (κ ·ᶜ Dχ +ᶜ κ ·ᶜ ρ ·ᶜ Da +ᶜ A₂) := by ac_rfl
        _ ≤ᶜ U₁ +ᶜ (U₂ +ᶜ κ ·ᶜ D) := Demand.add_le_add_left _ hD
        _ = U₁ +ᶜ U₂ +ᶜ κ ·ᶜ D := by ac_rfl
  | .obs (H₂ := H₂) (H₃ := H₃) (R₁ := R₁) (R₂ := R₂) (R₃ := R₃) hev hs ho => by
    obtain ⟨ν₁, ν₂, hle, hM₁, hMs⟩ := hM.obs_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁, D₂, rfl, hE₁, hE₂⟩ := hE'.split
    obtain ⟨Da, hva, hDa⟩ := Eval.conserve hP hκ hev hM₁ hE₁
    obtain ⟨Db, hvb, hDb⟩ := EvalAll.conserve hP hκ hs hMs (hE₂.mono hev.extends)
    obtain ⟨D, hv, hD⟩ := EvalObs.conserve hP hκ ho (hva.mono hs.extends) hvb
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
    calc κ ·ᶜ D_E +ᶜ (A₁ +ᶜ (A₂ +ᶜ A₃))
        ≤ᶜ κ ·ᶜ (D₁ +ᶜ D₂) +ᶜ (A₁ +ᶜ (A₂ +ᶜ A₃)) :=
          Demand.add_le_add_right (Demand.smul_le_smul κ hD') _
      _ = (κ ·ᶜ D₁ +ᶜ A₁) +ᶜ (κ ·ᶜ D₂ +ᶜ A₂) +ᶜ A₃ := by
          rw [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ κ ·ᶜ Da) +ᶜ (U₂ +ᶜ κ ·ᶜ Db) +ᶜ A₃ :=
          Demand.add_le_add_right (Demand.add_le_add hDa hDb) _
      _ = U₁ +ᶜ U₂ +ᶜ (κ ·ᶜ Da +ᶜ κ ·ᶜ Db +ᶜ A₃) := by ac_rfl
      _ ≤ᶜ U₁ +ᶜ U₂ +ᶜ (U₃ +ᶜ κ ·ᶜ D) := Demand.add_le_add_left _ hD
      _ = U₁ +ᶜ (U₂ +ᶜ U₃) +ᶜ κ ·ᶜ D := by ac_rfl
  | .corec (Ps := Ps) (Ms := Ms) (as := as) (H' := H₁) (R := R₁) hs => by
    obtain ⟨ν₁, δ, hle, hMs, hPs⟩ := hM.corec_inv rfl
    obtain ⟨D', hD', hE'⟩ := hE.le hle
    obtain ⟨D₁, Dδ, rfl, hE₁, hEδ⟩ := hE'.split
    obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hκ hs hMs hE₁
    have hH : H₁.Extends (H₁ ++ [Value.corec _ E Ps Ms.multiplicities as]) :=
      List.prefix_append _ _
    refine ⟨Dδ +ᶜ Ds, .corec List.getElem?_concat_length hPs ((hEδ.mono hs.extends).mono hH)
      (hvs.mono hH), ?_⟩
    rw [Demand.allocated_trans hs.extends hH,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.add_zero]
    generalize Demand.allocated H H₁ = A₁ at hDs ⊢
    generalize Demand.uses R₁ = U₁ at hDs ⊢
    calc κ ·ᶜ D_E +ᶜ A₁
        ≤ᶜ κ ·ᶜ (D₁ +ᶜ Dδ) +ᶜ A₁ := Demand.add_le_add_right (Demand.smul_le_smul κ hD') _
      _ = (κ ·ᶜ D₁ +ᶜ A₁) +ᶜ κ ·ᶜ Dδ := by
          rw [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ κ ·ᶜ Ds) +ᶜ κ ·ᶜ Dδ := Demand.add_le_add_right hDs _
      _ = U₁ +ᶜ κ ·ᶜ (Dδ +ᶜ Ds) := by
          rw [Demand.smul_add]
          ac_rfl
termination_by structural h

-- ADE: none.
/-- The invariant of the terms evaluated one after the other, each at the weight times its
multiplicity, whose values have the demands of their positions. -/
theorem EvalAll.conserve {P : Program} (hP : P.Usage) {κ : Multiplicity} (hκ : κ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n} {as : List Nat} {R : List Nat}
    (h : EvalAll P κ H E Ms as H' R) {ν : MultiplicityVector n} {D_E : Demand}
    (hMs : Targets.Usage ν Ms) (hE : H.EnvDemand E ν D_E) :
    ∃ D, H'.PositionsDemand Ms.multiplicities as D ∧
      κ ·ᶜ D_E +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ D :=
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
      obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hκ hs hMs (hE₂.mono hev.extends)
      refine ⟨_, .cons (hva.mono hs.extends) hvs, ?_⟩
      rw [Demand.allocated_trans hev.extends hs.extends, hal, List.nil_append, hπ, Demand.zero_smul,
        Demand.zero_smul, Demand.zero_add, Demand.zero_add, Demand.zero_add]
      exact hDs
    · obtain ⟨Da, hva, hDa⟩ :=
        Eval.conserve hP (Multiplicity.mul_ne_zero κ π hκ hπ) hev hM hE₁
      obtain ⟨Ds, hvs, hDs⟩ := EvalAll.conserve hP hκ hs hMs (hE₂.mono hev.extends)
      refine ⟨_, .cons (hva.mono hs.extends) hvs, ?_⟩
      rw [Demand.allocated_trans hev.extends hs.extends, Demand.uses_append]
      rw [Demand.mul_smul, Demand.mul_smul] at hDa
      generalize Demand.allocated H H₂ = A₁ at hDa ⊢
      generalize Demand.allocated H₂ H' = A₂ at hDs ⊢
      generalize Demand.uses R₁ = U₁ at hDa ⊢
      generalize Demand.uses R₂ = U₂ at hDs ⊢
      calc κ ·ᶜ (π ·ᶜ D₁ +ᶜ D₂) +ᶜ (A₁ +ᶜ A₂)
          = (κ ·ᶜ π ·ᶜ D₁ +ᶜ A₁) +ᶜ (κ ·ᶜ D₂ +ᶜ A₂) := by
            rw [Demand.smul_add]
            ac_rfl
        _ ≤ᶜ (U₁ +ᶜ κ ·ᶜ π ·ᶜ Da) +ᶜ (U₂ +ᶜ κ ·ᶜ Ds) := Demand.add_le_add hDa hDs
        _ = U₁ +ᶜ U₂ +ᶜ κ ·ᶜ (π ·ᶜ Da +ᶜ Ds) := by
            rw [Demand.smul_add]
            ac_rfl
termination_by structural h

-- ADE: none.
/-- The invariant of the elimination of a value by a recursor: the demand of the scope, for the
reads of the branches, and `ρ` times that of the value pay the reads of the run and the demand of
its value. -/
theorem EvalRec.conserve {P : Program} (hP : P.Usage) {κ : Multiplicity} (hκ : κ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {ρ : Multiplicity} {Ns : TargetBranches n}
    {a v : Nat} {R : List Nat} (h : EvalRec P κ H E ρ Ns a v H' R)
    {χ : MultiplicityVector n} {Dχ Da : Demand} (hNs : TargetBranches.Usage χ Ns)
    (hE : H.EnvDemand E χ Dχ) (ha : H.ValueDemand a Da) :
    ∃ D, H'.ValueDemand v D ∧
      κ ·ᶜ (Dχ +ᶜ ρ ·ᶜ Da) +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ D :=
  match h with
  | .iota (H₂ := H₂) (πs₀ := πs₀) (as := as) (a' := a') (b := b) (πs := πs) (πs' := πs')
      (ks := ks) (N := N) (rs := rs) (R₁ := R₁) (R₂ := R₂) hca hN hla hπ hres hv => by
    obtain ⟨Ds, hDs, rfl, hl₀⟩ := (ha.ctor_inv hca).inv
    obtain ⟨δ, hNu, hχ, hk⟩ := hNs.get _ hN
    obtain ⟨D', hD', hE'⟩ := hE.le hχ
    obtain ⟨Dδ, DS, rfl, hEδ, hES⟩ := hE'.split
    obtain ⟨Dχ₂, rfl, hEχ₂⟩ := hES.unsmul
    have hlr := hres.length
    -- The recursive results.
    obtain ⟨Drs, hDrs, hDres⟩ := EvalResults.conserve hP hκ hres hNs hEχ₂ hDs
      (fun j l π hj hπj h0 => by
        rw [List.getElem?_ofFn] at hj hπj
        by_cases hjb : j < b
        · simp only [hjb, ↓reduceDIte, Option.some.injEq] at hj hπj
          exact hk ⟨j, hjb⟩ (by rw [hj]; rfl) (hπj.trans h0)
        · simp only [hjb, ↓reduceDIte] at hj
          cases hj)
    have hH₂ : H₂.Extends (H₂.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (as ++ rs)) :=
      List.prefix_append _ _
    -- The branch, with cells for the fields and the results.
    obtain ⟨C, hEbr, hal⟩ := Heap.EnvDemand.bindBranch κ πs πs'
      ((hEδ.mono hres.extends).mono hH₂) ((hDs.mono hres.extends).mono hH₂) (hDrs.mono hH₂) hla
      (by simp at hlr; omega)
    obtain ⟨Dv, hvv, hDv⟩ := Eval.conserve hP hκ hv hNu hEbr
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
    rw [← Demand.recursions_eq _ _ _ (by simp) (fun j l h => hDs.length ▸ hres.lt j l h)]
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
    calc κ ·ᶜ (Dχ +ᶜ ρ ·ᶜ P₀) +ᶜ (A₁ +ᶜ (κ ·ᶜ C +ᶜ A₂))
        ≤ᶜ κ ·ᶜ (Dδ +ᶜ S ·ᶜ Dχ₂ +ᶜ (Q₁ +ᶜ ρ ·ᶜ Rc)) +ᶜ (A₁ +ᶜ (κ ·ᶜ C +ᶜ A₂)) :=
          Demand.add_le_add_right (Demand.smul_le_smul κ (Demand.add_le_add hD' hfield)) _
      _ = (κ ·ᶜ S ·ᶜ Dχ₂ +ᶜ κ ·ᶜ ρ ·ᶜ Rc +ᶜ A₁) +ᶜ (κ ·ᶜ Dδ +ᶜ κ ·ᶜ C +ᶜ κ ·ᶜ Q₁ +ᶜ A₂) := by
          simp only [Demand.smul_add]
          ac_rfl
      _ ≤ᶜ (U₁ +ᶜ κ ·ᶜ Q₂) +ᶜ (κ ·ᶜ Dδ +ᶜ κ ·ᶜ C +ᶜ κ ·ᶜ Q₁ +ᶜ A₂) :=
          Demand.add_le_add_right hDres _
      _ = U₁ +ᶜ (κ ·ᶜ Dδ +ᶜ κ ·ᶜ C +ᶜ (κ ·ᶜ Q₁ +ᶜ κ ·ᶜ Q₂) +ᶜ A₂) := by ac_rfl
      _ ≤ᶜ U₁ +ᶜ (U₂ +ᶜ κ ·ᶜ Dv) := Demand.add_le_add_left _ hDv
      _ = U₁ +ᶜ U₂ +ᶜ κ ·ᶜ Dv := by ac_rfl
termination_by structural h

-- ADE: none.
/-- The invariant of the recursive results of a branch: the demand of the scope, as many times as
the multiplicities of the binders of the computed results, and `ρ` times the demands of the fields
that the recursions use, pay the reads of the runs and the demands of the results, each as many
times as the multiplicity of its binder. -/
theorem EvalResults.conserve {P : Program} (hP : P.Usage) {κ : Multiplicity} (hκ : κ ≠ .zero)
    {n : Nat} {H H' : Heap} {E : List Nat} {ρ : Multiplicity} {Ns : TargetBranches n}
    {as : List Nat} {ks : List (Option Nat)} {πs : List Multiplicity} {rs : List Nat}
    {R : List Nat} (h : EvalResults P κ H E ρ Ns as ks πs rs H' R) {χ : MultiplicityVector n}
    {Dχ : Demand} {Ds : List Demand} (hNs : TargetBranches.Usage χ Ns)
    (hE : H.EnvDemand E χ Dχ) (hDs : H.ValueDemands as Ds)
    (hk : ∀ (j l : Nat) π, ks[j]? = some (some l) → πs[j]? = some π → π ≠ .zero) :
    ∃ Drs, H'.ValueDemands rs Drs ∧
      κ ·ᶜ (Multiplicity.computed ks πs ·ᶜ Dχ +ᶜ ρ ·ᶜ Demand.recursions ks πs Ds) +ᶜ
        Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ Demand.positions πs Drs :=
  match h with
  | .nil => by
    refine ⟨[], .nil, ?_⟩
    rw [Demand.allocated_self, Demand.uses_nil]
    intro x
    exact (by decide : ∀ κ ρ d : Multiplicity, κ * (.zero * d + ρ * .zero) + .zero ≤
      .zero + κ * .zero) κ ρ (Dχ x)
  | .erased (H₂ := H₂) hs => by
    have hH : H.Extends (H ++ [Value.erased]) := List.prefix_append _ _
    obtain ⟨Drs, hDrs, hD⟩ := EvalResults.conserve hP hκ hs hNs (hE.mono hH) (hDs.mono hH)
      (fun j l π h₁ h₂ => hk (j + 1) l π h₁ h₂)
    refine ⟨𝟘ᵛ :: Drs, .cons (Heap.ValueDemand.erased List.getElem?_concat_length |>.mono
      hs.extends) hDrs, ?_⟩
    rw [Demand.allocated_trans hH hs.extends,
      Demand.allocated_append (fun _ _ h => Value.noConfusion h), Demand.zero_add]
    show _ ≤ᶜ _ +ᶜ κ ·ᶜ (_ ·ᶜ 𝟘ᵛ +ᶜ _)
    rw [Demand.smul_zero, Demand.zero_add]
    exact hD
  | .recursor (π := π) (H₂ := H₂) (R₁ := R₁) (R₂ := R₂) (j := j) hj hev hs => by
    have hπ : π ≠ .zero := fun h0 => hk 0 j π rfl rfl h0
    have hD := hDs.getElem? j hj
    obtain ⟨Dr, hvr, hDr⟩ := EvalRec.conserve hP (Multiplicity.mul_ne_zero κ π hκ hπ) hev hNs hE hD
    obtain ⟨Drs, hDrs, hDt⟩ := EvalResults.conserve hP hκ hs hNs (hE.mono hev.extends)
      (hDs.mono hev.extends) (fun j l π h₁ h₂ => hk (j + 1) l π h₁ h₂)
    refine ⟨Dr :: Drs, .cons (hvr.mono hs.extends) hDrs, ?_⟩
    rw [Demand.allocated_trans hev.extends hs.extends, Demand.uses_append]
    show κ ·ᶜ ((π + Multiplicity.computed _ _) ·ᶜ Dχ +ᶜ
        ρ ·ᶜ (π ·ᶜ Ds.getD j 𝟘ᵛ +ᶜ Demand.recursions _ _ Ds)) +ᶜ _ ≤ᶜ
      _ +ᶜ κ ·ᶜ (π ·ᶜ Dr +ᶜ Demand.positions _ Drs)
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
    have e₁ : κ ·ᶜ ((π + c) ·ᶜ Dχ +ᶜ ρ ·ᶜ (π ·ᶜ Da +ᶜ Rc)) =
        (κ * π) ·ᶜ Dχ +ᶜ (κ * π) ·ᶜ ρ ·ᶜ Da +ᶜ (κ ·ᶜ c ·ᶜ Dχ +ᶜ κ ·ᶜ ρ ·ᶜ Rc) := by
      funext x
      exact (by decide : ∀ κ π c ρ d a r : Multiplicity,
        κ * ((π + c) * d + ρ * (π * a + r)) =
          κ * π * d + κ * π * (ρ * a) + (κ * (c * d) + κ * (ρ * r))) κ π c ρ (Dχ x) (Da x) (Rc x)
    rw [e₁, Demand.smul_add, ← Demand.mul_smul κ π]
    calc (κ * π) ·ᶜ Dχ +ᶜ (κ * π) ·ᶜ ρ ·ᶜ Da +ᶜ (κ ·ᶜ c ·ᶜ Dχ +ᶜ κ ·ᶜ ρ ·ᶜ Rc) +ᶜ (A₁ +ᶜ A₂)
        = ((κ * π) ·ᶜ Dχ +ᶜ (κ * π) ·ᶜ ρ ·ᶜ Da +ᶜ A₁) +ᶜ
            (κ ·ᶜ c ·ᶜ Dχ +ᶜ κ ·ᶜ ρ ·ᶜ Rc +ᶜ A₂) := by ac_rfl
      _ ≤ᶜ (U₁ +ᶜ (κ * π) ·ᶜ Dr) +ᶜ (U₂ +ᶜ κ ·ᶜ Q) := Demand.add_le_add hDr hDt
      _ = U₁ +ᶜ U₂ +ᶜ ((κ * π) ·ᶜ Dr +ᶜ κ ·ᶜ Q) := by ac_rfl
termination_by structural h

-- ADE: none.
/-- The invariant of an observation: the demand of the closure and of the arguments pay the reads
of the run and the demand of its value. -/
theorem EvalObs.conserve {P : Program} (hP : P.Usage) {κ : Multiplicity} (hκ : κ ≠ .zero)
    {H H' : Heap} {a i : Nat} {πb : List Multiplicity} {bs : List Nat} {v : Nat} {R : List Nat}
    (h : EvalObs P κ H a i πb bs v H' R) {Da Db : Demand} (ha : H.ValueDemand a Da)
    (hb : H.PositionsDemand πb bs Db) :
    ∃ D, H'.ValueDemand v D ∧
      κ ·ᶜ (Da +ᶜ Db) +ᶜ Demand.allocated H H' ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ D :=
  match h with
  | .beta (H₂ := H₂) (w := w) (n := n) (E := E) (Ps := Ps) (πs₁ := πs₁) (ss := ss) (o := o)
      (b := b) (c := c) (πs := πs) (πs' := πs') (N := N) (R := R) hclo hget hlb hlc hπ₁ hπ₂ hw
      hr => by
    obtain ⟨δ, Dδ, Dss, hPs, hEδ, hss, rfl⟩ := ha.corec_inv hclo
    obtain ⟨δᵢ, hN, hδ, hres⟩ := hPs.get i hget
    obtain ⟨Dsl, hDsl, rfl, hlss⟩ := hss.inv
    obtain ⟨Dbl, hDbl, rfl, hlbs⟩ := hb.inv
    have hH₁ : H.Extends (H.bind ((List.ofFn πs ++ List.ofFn πs').map (κ * ·)) (ss ++ bs)) :=
      List.prefix_append _ _
    -- The branch runs from a demand `Di` of the scope for its reads, the closure keeping `Drest`.
    have key : ∀ Di Drest, H.EnvDemand E δᵢ Di → Dδ ≤ᶜ Di +ᶜ Drest →
        ∃ Dw, H₂.ValueDemand w Dw ∧
          κ ·ᶜ (Dδ +ᶜ Demand.positions πs₁ Dsl +ᶜ Demand.positions πb Dbl) +ᶜ
            Demand.allocated H H₂ ≤ᶜ Demand.uses R +ᶜ κ ·ᶜ (Dw +ᶜ Drest) := by
      intro Di Drest hEi hDi
      obtain ⟨C, hEbr, hal⟩ := Heap.EnvDemand.bindBranch κ πs πs' (hEi.mono hH₁)
        (hDsl.mono hH₁) (hDbl.mono hH₁) hlb hlc
      obtain ⟨Dw, hvw, hDw⟩ := Eval.conserve hP hκ hw hN hEbr
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
      calc κ ·ᶜ (Dδ +ᶜ P₁ +ᶜ P₂) +ᶜ (κ ·ᶜ C +ᶜ A)
          ≤ᶜ κ ·ᶜ (Di +ᶜ Drest +ᶜ Q₁ +ᶜ Q₂) +ᶜ (κ ·ᶜ C +ᶜ A) :=
            Demand.add_le_add_right (Demand.smul_le_smul κ
              (Demand.add_le_add (Demand.add_le_add hDi h₁) h₂)) _
        _ = (κ ·ᶜ Di +ᶜ κ ·ᶜ C +ᶜ (κ ·ᶜ Q₁ +ᶜ κ ·ᶜ Q₂) +ᶜ A) +ᶜ κ ·ᶜ Drest := by
            rw [Demand.smul_add, Demand.smul_add, Demand.smul_add]
            ac_rfl
        _ ≤ᶜ (U +ᶜ κ ·ᶜ Dw) +ᶜ κ ·ᶜ Drest := Demand.add_le_add_right hDw _
        _ = U +ᶜ κ ·ᶜ (Dw +ᶜ Drest) := by
            rw [Demand.smul_add]
            ac_rfl
    cases hr with
    | none =>
      obtain ⟨Di, hDi, hEi⟩ := hEδ.le hδ
      obtain ⟨Dw, hvw, hDw⟩ := key Di 𝟘ᵛ hEi (by rwa [Demand.add_zero])
      rw [Demand.add_zero] at hDw
      exact ⟨Dw, hvw, by rw [Demand.add_assoc] at hDw; rwa [Demand.add_assoc]⟩
    | done _ hwv hπd =>
      obtain ⟨Di, hDi, hEi⟩ := hEδ.le hδ
      obtain ⟨Dw, hvw, hDw⟩ := key Di 𝟘ᵛ hEi (by rwa [Demand.add_zero])
      obtain ⟨Ds, hDs, rfl, -⟩ := (hvw.ctor_inv hwv).inv
      obtain _ | ⟨hx, hDs⟩ := hDs
      cases hDs
      refine ⟨_, hx, ?_⟩
      refine Demand.le_trans hDw (Demand.add_le_add_left _ fun y => ?_)
      exact Multiplicity.done_le κ _ _ hπd
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
            (Heap.ValueDemands.replicate (hx.mono (List.prefix_append _ _)) _) (by simp)), ?_⟩
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

/-- The uses of a trace are `1` exactly when the trace reads the cell once. -/
theorem Demand.uses_eq_one {R : List Nat} {c : Nat} : Demand.uses R c = .one ↔ R.count c = 1 := by
  simp only [Demand.uses]
  split <;> simp_all

/-- The uses of a trace are `0` exactly when the trace never reads the cell. -/
theorem Demand.uses_eq_zero {R : List Nat} {c : Nat} : Demand.uses R c = .zero ↔ R.count c = 0 := by
  simp only [Demand.uses]
  split <;> simp_all

-- ADE: none.
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
