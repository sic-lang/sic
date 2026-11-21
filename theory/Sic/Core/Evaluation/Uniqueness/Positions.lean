module

public import Sic.Core.Evaluation.Conservation.Positions
public import Sic.Core.Evaluation.Paths

/-!
# Sums of Reaches

The sums of the reaches of the positions of a value, for the proof of the invariant of the
uniqueness at run time: when the sum refers to an address, and when the binders of a branch, whose
multiplicities are above those at which their values are stored, refer to it as the stored
positions do.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-- The reach of positions is the sum of the reaches of their values, each times the references of
its multiplicity. -/
theorem Heap.PositionsReach.inv {H : Heap} {g : Heap.Annotation} : {πs : List Multiplicity} →
    {as : List Nat} → {U : Demand} → Heap.PositionsReach H g πs as U →
      ∃ Us, List.Pointwise (Heap.ValueReach H g) as Us ∧
        U = Demand.positions (πs.map Multiplicity.references) Us ∧ πs.length = as.length
  | _, _, _, .nil => ⟨[], .nil, rfl, rfl⟩
  | _, _, _, .cons h hs => by
    obtain ⟨Us, hUs, rfl, hl⟩ := Heap.PositionsReach.inv hs
    exact ⟨_ :: Us, .cons h hUs, rfl, congrArg (· + 1) hl⟩

/-- Positions whose values have reaches have the sum of these reaches, each times the references of
its multiplicity. -/
theorem Heap.PositionsReach.of_forall₂ {H : Heap} {g : Heap.Annotation} :
    {πs : List Multiplicity} → {as : List Nat} → {Us : List Demand} →
      List.Pointwise (Heap.ValueReach H g) as Us → πs.length = as.length →
      Heap.PositionsReach H g πs as (Demand.positions (πs.map Multiplicity.references) Us)
  | [], _, _, .nil, _ => .nil
  | _ :: _, _, _, .cons h hs, hl => .cons h (Heap.PositionsReach.of_forall₂ hs (Nat.succ.inj hl))
  | [], _, _, .cons _ _, hl | _ :: _, _, _, .nil, hl => nomatch hl

/-- Reaches that refer to no reference of an address sum to none. -/
theorem Demand.positions_eq_zero {b : Nat} : (πs : List Multiplicity) → (Us : List Demand) →
    (∀ U ∈ Us, U b = .zero) → Demand.positions πs Us b = .zero
  | π :: πs, U :: Us, h => by
    show π * U b + Demand.positions πs Us b = _
    rw [h U List.mem_cons_self,
      Demand.positions_eq_zero πs Us fun U' h' => h U' (List.mem_cons_of_mem _ h')]
    cases π <;> rfl
  | [], _, _ | _ :: _, [], _ => rfl

/-- Each term of a sum of reaches that refers to no reference of an address refers to none. -/
theorem Demand.positions_get_zero {b : Nat} : (πs : List Multiplicity) → (Us : List Demand) →
    Demand.positions πs Us b = .zero → ∀ {j : Nat} {π : Multiplicity} {U : Demand},
      πs[j]? = some π → Us[j]? = some U → π * U b = .zero
  | π' :: πs, U' :: Us, h, 0, _, _, hπ, hU => by
    cases hπ
    cases hU
    exact (by decide : ∀ x y : Multiplicity, x + y = .zero → x = .zero) _ _ h
  | π' :: πs, U' :: Us, h, j + 1, _, _, hπ, hU =>
    Demand.positions_get_zero πs Us
      ((by decide : ∀ x y : Multiplicity, x + y = .zero → y = .zero) _ _ h)
      (by simpa using hπ) (by simpa using hU)
  | [], _, _, _, _, _, hπ, _ => by simp at hπ
  | _ :: _, [], _, _, _, _, _, hU => by simp at hU

/-- A sum of reaches whose terms refer to no reference of an address refers to none. -/
theorem Demand.positions_of_zero {b : Nat} : (πs : List Multiplicity) → (Us : List Demand) →
    (∀ (j : Nat) (π : Multiplicity) (U : Demand), πs[j]? = some π → Us[j]? = some U →
      π * U b = .zero) → Demand.positions πs Us b = .zero
  | π :: πs, U :: Us, h => by
    show π * U b + Demand.positions πs Us b = _
    rw [h 0 π U rfl rfl, Demand.positions_of_zero πs Us fun j => h (j + 1)]
    rfl
  | [], _, _ | _ :: _, [], _ => rfl

/-- A sum of reaches one of whose terms refers to an address refers to it. -/
theorem Demand.positions_ne_zero {b : Nat} : (πs : List Multiplicity) → (Us : List Demand) →
    {j : Nat} → {π : Multiplicity} → {U : Demand} → πs[j]? = some π → Us[j]? = some U →
      π * U b ≠ .zero → Demand.positions πs Us b ≠ .zero
  | π' :: πs, U' :: Us, 0, _, _, hπ, hU, h => by
    cases hπ
    cases hU
    exact Multiplicity.add_ne_zero_left _ _ h
  | π' :: πs, U' :: Us, j + 1, _, _, hπ, hU, h =>
    Multiplicity.add_ne_zero_right _ _
      (Demand.positions_ne_zero πs Us (by simpa using hπ) (by simpa using hU) h)
  | [], _, _, _, _, hπ, _, _ => by simp at hπ
  | _ :: _, [], _, _, _, _, hU, _ => by simp at hU

/-- Positions whose references refer to no reference of an address use it at no multiplicity. -/
theorem Demand.positions_references_eq_zero {b : Nat} (πs : List Multiplicity) (Us : List Demand)
    (h : Demand.positions (πs.map Multiplicity.references) Us b = .zero) :
    Demand.positions πs Us b = .zero :=
  Demand.positions_of_zero πs Us fun j π U hπ hU =>
    (by decide : ∀ π u : Multiplicity, π.references * u = .zero → π * u = .zero) π (U b)
      (Demand.positions_get_zero _ _ h (by rw [List.getElem?_map, hπ]; rfl) hU)

/-- The element of a list of reaches that refer to no reference of an address, or the reach `0`,
refers to none. -/
theorem Demand.getD_eq_zero {b : Nat} {Us : List Demand} (h : ∀ U ∈ Us, U b = .zero) (l : Nat) :
    Us.getD l 𝟘ᵛ b = .zero := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : Us[l]? with
  | none => rfl
  | some U => exact h U (List.mem_of_getElem? hl)

/-- The values of a heap, related to their reaches one by one, refer to no address after it. -/
theorem Heap.ValueReach.pointwise_eq_zero {H : Heap} {g : Heap.Annotation} :
    {as : List Nat} → {Us : List Demand} → List.Pointwise (Heap.ValueReach H g) as Us →
      ∀ {b : Nat}, H.length ≤ b → ∀ U ∈ Us, U b = .zero
  | _, _, .nil, _, _, _, h => nomatch h
  | _, _, .cons h hs, b, hb, U, hU => by
    rcases List.mem_cons.1 hU with rfl | hU
    · exact h.eq_zero b hb
    · exact Heap.ValueReach.pointwise_eq_zero hs hb U hU

/-- Binders within the multiplicities at which their values are stored use no address that the
stored positions do not refer to. -/
theorem Demand.positions_eq_zero_of_le {b : Nat} (πs₁ πs : List Multiplicity) (Us : List Demand)
    (hl : Us.length ≤ πs₁.length)
    (hle : ∀ (j : Nat) (π₁ π : Multiplicity), πs₁[j]? = some π₁ → πs[j]? = some π → π₁ ≤ π)
    (h : Demand.positions (πs₁.map Multiplicity.references) Us b = .zero) :
    Demand.positions πs Us b = .zero :=
  Demand.positions_of_zero πs Us fun j π U hπ hU => by
    obtain ⟨π₁, hπ₁⟩ : ∃ π₁, πs₁[j]? = some π₁ :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hU).1 hl)⟩
    exact (by decide : ∀ π₁ π u : Multiplicity, π₁ ≤ π → π₁.references * u = .zero →
      π * u = .zero) _ _ _ (hle j π₁ π hπ₁ hπ)
      (Demand.positions_get_zero _ _ h (by rw [List.getElem?_map, hπ₁]; rfl) hU)

/-- Binders within the multiplicities at which their values are stored, one of which, of the
multiplicity `1`, binds a value that refers to an address that the stored positions refer to once
at most, use the address as the stored positions refer to it. -/
theorem Demand.positions_eq_references_of_le {b : Nat} : (πs₁ πs : List Multiplicity) →
    (Us : List Demand) → Us.length ≤ πs₁.length →
      (∀ (j : Nat) (π₁ π : Multiplicity), πs₁[j]? = some π₁ → πs[j]? = some π → π₁ ≤ π) →
      {l : Nat} → {U : Demand} → πs[l]? = some Multiplicity.one → Us[l]? = some U →
      U b ≠ .zero → Demand.positions (πs₁.map Multiplicity.references) Us b ≠ .omega →
      Demand.positions πs Us b = Demand.positions (πs₁.map Multiplicity.references) Us b
  | π₁ :: πs₁, π :: πs, U' :: Us, hl, hle, 0, _, hπ, hU, hb, hω => by
    cases hπ
    cases hU
    have hπ₁ := hle 0 π₁ .one rfl rfl
    have hω' : π₁.references * U' b +
        Demand.positions (πs₁.map Multiplicity.references) Us b ≠ .omega := hω
    have h0 : Demand.positions (πs₁.map Multiplicity.references) Us b = .zero :=
      (by decide : ∀ π₁ u r : Multiplicity, π₁ ≤ .one → u ≠ .zero →
        π₁.references * u + r ≠ .omega → r = .zero) _ _ _ hπ₁ hb hω'
    show Multiplicity.one * U' b + Demand.positions πs Us b =
      π₁.references * U' b + Demand.positions (πs₁.map Multiplicity.references) Us b
    rw [h0, Demand.positions_eq_zero_of_le πs₁ πs Us (Nat.le_of_succ_le_succ hl)
      (fun j => hle (j + 1)) h0]
    exact (by decide : ∀ π₁ u : Multiplicity, π₁ ≤ .one →
      Multiplicity.one * u + .zero = π₁.references * u + .zero) _ _ hπ₁
  | π₁ :: πs₁, π :: πs, U' :: Us, hl, hle, l + 1, U, hπ, hU, hb, hω => by
    have hπ' : πs[l]? = some Multiplicity.one := by simpa using hπ
    have hU' : Us[l]? = some U := by simpa using hU
    have hl' : Us.length ≤ πs₁.length := Nat.le_of_succ_le_succ hl
    obtain ⟨π₁l, hπ₁l⟩ : ∃ π₁l, πs₁[l]? = some π₁l :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hU').1 hl')⟩
    have hω' : π₁.references * U' b +
        Demand.positions (πs₁.map Multiplicity.references) Us b ≠ .omega := hω
    have hr : Demand.positions (πs₁.map Multiplicity.references) Us b ≠ .zero :=
      Demand.positions_ne_zero _ _ (by rw [List.getElem?_map, hπ₁l]; rfl) hU'
        ((by decide : ∀ π₁ u : Multiplicity, π₁ ≤ .one → u ≠ .zero →
          π₁.references * u ≠ .zero) _ _ (hle (l + 1) π₁l .one (by simpa using hπ₁l) hπ) hb)
    have h0 : π₁.references * U' b = .zero := (by decide : ∀ x r : Multiplicity,
      x + r ≠ .omega → r ≠ .zero → x = .zero) _ _ hω' hr
    show π * U' b + Demand.positions πs Us b =
      π₁.references * U' b + Demand.positions (πs₁.map Multiplicity.references) Us b
    rw [Demand.positions_eq_references_of_le πs₁ πs Us hl' (fun j => hle (j + 1)) hπ' hU' hb
      ((by decide : ∀ x r : Multiplicity, x + r ≠ .omega → r ≠ .omega) _ _ hω'), h0,
      (by decide : ∀ π₁ π u : Multiplicity, π₁ ≤ π → π₁.references * u = .zero →
        π * u = .zero) _ _ _ (hle 0 π₁ π rfl rfl) h0]
  | _, [], _, _, _, _, _, hπ, _, _, _ => by simp at hπ
  | _, _ :: _, [], _, _, _, _, _, hU, _, _ => by simp at hU
  | [], _ :: _, _ :: _, hl, _, _, _, _, _, _, _ => by simp at hl

/-- Positions that refer once at most to an address, one of which, of the multiplicity `1`, refers
to it, use it as they refer to it. -/
theorem Demand.positions_eq_references {b : Nat} (πs : List Multiplicity) (Us : List Demand)
    (hl : Us.length ≤ πs.length) {l : Nat} {U : Demand} (hπ : πs[l]? = some Multiplicity.one)
    (hU : Us[l]? = some U) (hb : U b ≠ .zero)
    (hω : Demand.positions (πs.map Multiplicity.references) Us b ≠ .omega) :
    Demand.positions πs Us b = Demand.positions (πs.map Multiplicity.references) Us b :=
  Demand.positions_eq_references_of_le πs πs Us hl (fun j π₁ π h₁ h₂ => by
    rw [h₁] at h₂
    cases h₂
    exact Multiplicity.le_refl' _) hπ hU hb hω

/-- The multiplicities of the binders of a branch are above those at which their values are stored,
on the lists. -/
theorem Multiplicity.le_ofFn {b : Nat} (πs₁ : List Multiplicity) (πs : Fin b → Multiplicity)
    (h : ∀ j : Fin b, ∃ π₁, πs₁[(j : Nat)]? = some π₁ ∧ π₁ ≤ πs j) (j : Nat)
    (π₁ π : Multiplicity) (h₁ : πs₁[j]? = some π₁) (h₂ : (List.ofFn πs)[j]? = some π) :
    π₁ ≤ π := by
  rw [List.getElem?_ofFn] at h₂
  split at h₂
  · rename_i hj
    cases h₂
    obtain ⟨π₁', h₁', hle⟩ := h ⟨j, hj⟩
    rw [h₁] at h₁'
    cases h₁'
    exact hle
  · cases h₂

/-- The references of multiplicities each times `π` are theirs, each times those of `π`. -/
theorem Multiplicity.map_references_mul (π : Multiplicity) (πs : List Multiplicity) :
    (πs.map (π * ·)).map Multiplicity.references =
      (πs.map Multiplicity.references).map (π.references * ·) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun π' _ => ?_
  cases π <;> cases π' <;> rfl

/-- The reach of a constructor is itself and the sum of the reaches of its fields. -/
theorem Heap.ValueReach.ctor_inv {H : Heap} {g : Heap.Annotation} {ℓ i : Nat}
    {πs ϱs : List Multiplicity} {as : List Nat} {U : Demand}
    (h : H[ℓ]? = some (.ctor i πs ϱs as)) (hU : Heap.ValueReach H g ℓ U) :
    ∃ Us, List.Pointwise (Heap.ValueReach H g) as Us ∧
      U = Demand.unit ℓ +ᶜ Demand.positions (πs.map Multiplicity.references) Us ∧
      πs.length = as.length := by
  cases hU with
  | erased h' | corec h' => cases h.symm.trans h'
  | ctor h' hs' =>
    cases h.symm.trans h'
    obtain ⟨Us, hUs, rfl, hl⟩ := hs'.inv
    exact ⟨Us, hUs, rfl, hl⟩

/-- The reach of a closure is itself, the reach of its scope and the sum of the reaches of the
entries of its state. -/
theorem Heap.ValueReach.corec_inv {H : Heap} {g : Heap.Annotation} {ℓ n : Nat} {E : List Nat}
    {Ps : TargetDestructorBranches n} {πs ϱs : List Multiplicity} {as : List Nat} {U : Demand}
    (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (hU : Heap.ValueReach H g ℓ U) :
    ∃ U₁ Us, Heap.EnvReach H g E (g.usage ℓ n) U₁ ∧
      List.Pointwise (Heap.ValueReach H g) as Us ∧
      U = Demand.unit ℓ +ᶜ (U₁ +ᶜ Demand.positions (πs.map Multiplicity.references) Us) ∧
      πs.length = as.length := by
  cases hU with
  | erased h' | ctor h' => cases h.symm.trans h'
  | corec h' hE hs' =>
    cases h.symm.trans h'
    obtain ⟨Us, hUs, rfl, hl⟩ := hs'.inv
    exact ⟨_, Us, hE, hUs, rfl, hl⟩

end Sic.Core
