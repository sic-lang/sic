module

public import Sic.Core.Evaluation.Demand
import Sic.Core.Evaluation.Conservation.Demands

/-!
# Sums of Demands

The sums of the demands of the positions of a value, for the proof of the invariant of the
conservation of the bindings: the demand of positions is the sum of the demands of their values,
each as many times as its multiplicity, and so are the demands of the cells and of the values that
binders bind.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- `H ⊢ ℓ̄ ▶ D̄`: the values at the addresses `ℓ̄` have the demands `D̄`, one by one. -/
abbrev Heap.ValueDemands (H : Heap) : List Nat → List Demand → Prop :=
  List.Pointwise (Heap.ValueDemand H)

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

/-- The demand of a constructor is that of its fields. -/
theorem Heap.ValueDemand.ctor_inv {H : Heap} {ℓ i : Nat} {πs ϱs : List Multiplicity}
    {as : List Nat} {D : Demand} (hℓ : H[ℓ]? = some (.ctor i πs ϱs as)) :
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
    {Ps : TargetCorecBranches n} {πs ϱs : List Multiplicity} {as : List Nat} {D : Demand}
    (hℓ : H[ℓ]? = some (.corec n E Ps πs ϱs as)) :
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
theorem Unpack.demand {H : Heap} : {k x : Nat} → {πs ϱs : List Multiplicity} → {ss : List Nat} →
    Unpack H k x πs ϱs ss → {D : Demand} → Heap.ValueDemand H x D →
      ∃ Ds, Heap.ValueDemands H ss Ds ∧ D = Demand.positions πs Ds
  | _, _, _, _, _, .zero h, _, hD => by
    obtain ⟨Ds, hDs, rfl, -⟩ := (hD.ctor_inv h).inv
    cases hDs
    exact ⟨[], .nil, rfl⟩
  | _, _, _, _, _, .pair (π := π) (π' := π') (πs := πs) h hs, _, hD => by
    obtain ⟨Ds, hDs, rfl, -⟩ := (hD.ctor_inv h).inv
    obtain _ | ⟨hy, hDs⟩ := hDs
    obtain _ | ⟨hz, hDs⟩ := hDs
    cases hDs
    obtain ⟨Dss, hDss, rfl⟩ := Unpack.demand hs hz
    refine ⟨_ :: Dss, .cons hy hDss, ?_⟩
    simp only [Demand.positions, Demand.positions_map_mul, Demand.add_zero]

/-- The demands of values hold in each heap that extends their heap. -/
theorem Heap.ValueDemands.mono {H H' : Heap} (hH : H.Extends H') {as : List Nat}
    {Ds : List Demand} (h : Heap.ValueDemands H as Ds) : Heap.ValueDemands H' as Ds :=
  List.Pointwise.imp (fun _ _ h => h.mono hH) h

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

/-- The cells that a binder allocates from the address `c` are not read before it. -/
theorem Demand.cells_lt : (c : Nat) → (bs : List (Multiplicity × Nat × Demand)) → ∀ b, b < c →
    Demand.cells c bs b = .zero
  | _, [], _, _ => rfl
  | c, x :: bs, b, hb => by
    show x.1 * Demand.unit c b + Demand.cells (c + 1) bs b = _
    rw [Demand.cells_lt (c + 1) bs b (Nat.lt_succ_of_lt hb),
      show Demand.unit c b = .zero by simp [Demand.unit, Nat.ne_of_lt hb]]
    cases x.1 <;> rfl

/-- The cell that a binder allocates for its variable at a position is read as many times as the
multiplicity of the variable. -/
theorem Demand.cells_get : (c : Nat) → (bs : List (Multiplicity × Nat × Demand)) → (j : Nat) →
    (x : Multiplicity × Nat × Demand) → bs[j]? = some x → Demand.cells c bs (c + j) = x.1
  | c, x :: bs, 0, _, h => by
    cases h
    show x.1 * Demand.unit c (c + 0) + Demand.cells (c + 1) bs (c + 0) = _
    rw [Demand.cells_lt (c + 1) bs (c + 0) (by omega),
      show Demand.unit c (c + 0) = .one by simp [Demand.unit]]
    cases x.1 <;> rfl
  | c, x :: bs, j + 1, y, h => by
    show x.1 * Demand.unit c (c + (j + 1)) + Demand.cells (c + 1) bs (c + (j + 1)) = _
    rw [show c + (j + 1) = c + 1 + j by omega, Demand.cells_get (c + 1) bs j y (by simpa using h),
      show Demand.unit c (c + 1 + j) = .zero by simp [Demand.unit]; omega]
    cases x.1 <;> cases y.1 <;> rfl

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

/-- The values with demands have a demand at each of their positions. -/
theorem Heap.ValueDemands.getElem? {H : Heap} :
    {as : List Nat} → {Ds : List Demand} → Heap.ValueDemands H as Ds → (j : Nat) → {a : Nat} →
      as[j]? = some a → Heap.ValueDemand H a (Ds.getD j 𝟘ᵛ)
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons hv _, 0, _, h => by
    cases h
    exact hv
  | _, _, .cons _ hs, j + 1, _, h => Heap.ValueDemands.getElem? hs j h

end Sic.Core
