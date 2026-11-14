module

public import Sic.Core.Evaluation.Conservation.Positions
import Sic.Core.Evaluation.Conservation.Demands

/-!
# Binders

The cells that the evaluation binds for a branch, for the proof of the invariant of the
conservation of the bindings: the multiplicities that they allocate, and the demand of the
environment that they extend.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

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
theorem Demand.allocated_bind (ϖ : Multiplicity) :
    (H : Heap) → (bs : List (Multiplicity × Nat × Demand)) →
      Demand.allocated H (H.bind (bs.map fun b => ϖ * b.1) (bs.map (·.2.1))) =
        ϖ ·ᶜ Demand.cells H.length bs
  | H, [] => by
    show Demand.allocated H (H ++ []) = _
    rw [List.append_nil, Demand.allocated_self, Demand.cells, Demand.smul_zero]
  | H, b :: bs => by
    have e : H.bind ((b :: bs).map fun b => ϖ * b.1) ((b :: bs).map (·.2.1)) =
        (H ++ [Value.cell (ϖ * b.1) b.2.1]).bind (bs.map fun b => ϖ * b.1) (bs.map (·.2.1)) := by
      simp only [Heap.bind, List.map_cons, List.zipWith_cons_cons, List.append_assoc,
        List.singleton_append]
    have h₂ : (H ++ [Value.cell (ϖ * b.1) b.2.1]).Extends
        ((H ++ [Value.cell (ϖ * b.1) b.2.1]).bind (bs.map fun b => ϖ * b.1) (bs.map (·.2.1))) :=
      List.prefix_append _ _
    rw [e, Demand.allocated_trans (List.prefix_append _ _) h₂,
      Demand.allocated_cell, Demand.allocated_bind ϖ _ bs, Demand.cells, Demand.smul_add,
      Demand.mul_smul, List.length_append, List.length_singleton]

/-- The sum over an environment extended by the cells that a binder allocates from the address `c`,
for the vector extended by the multiplicities of the binder, the last variable first, adds their
reads and what `R` gives their values, each as many times as its multiplicity. -/
theorem Heap.EnvSum.bindAll {H : Heap} {R : Nat → Demand → Prop} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {D : Demand} (hE : Heap.EnvSum H R E ν D) (c : Nat) :
    (m : Nat) → (bs : List (Multiplicity × Nat × Demand)) → bs.length = m →
      (∀ l b, bs[l]? = some b → ∃ π, H[c + l]? = some (.cell π b.2.1)) →
      (∀ b ∈ bs, R b.2.1 b.2.2) →
      (μ : MultiplicityVector (n + m)) →
      (∀ i : Fin (n + m), (i : Nat) < m → some (μ i) = (bs[m - 1 - i]?).map (·.1)) →
      (∀ i : Fin n, μ ⟨i + m, by omega⟩ = ν i) →
      Heap.EnvSum H R ((List.range' c m).reverse ++ E) μ
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
    have ih := Heap.EnvSum.bindAll hE c m bs' hl'
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
    have hcons := Heap.EnvSum.cons hπ
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

/-- The cells that a binder allocates hold its addresses, at its multiplicities. -/
theorem Heap.bind_getElem? (H : Heap) : (πs : List Multiplicity) → (as : List Nat) →
    (l : Nat) → (π : Multiplicity) → (a : Nat) → πs[l]? = some π → as[l]? = some a →
      (H.bind πs as)[H.length + l]? = some (.cell π a) := by
  intro πs as l π a hπ ha
  simp only [Heap.bind]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_zipWith, hπ, ha]

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
binders times the weight, give the environment of the branch a sum for the extended vector: that of
the scope, the reads `C` of the new cells, each the multiplicity of its binder at its address, and
what `R` gives their values, each as many times as the multiplicity of its binder. -/
theorem Heap.EnvSum.bindBranch {H : Heap} {R : Nat → Demand → Prop} (ϖ : Multiplicity) {n a b : Nat} {E : List Nat}
    {δ : MultiplicityVector n} {D : Demand} (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity)
    {vs₁ vs₂ : List Nat} {Ds₁ Ds₂ : List Demand}
    (hE : Heap.EnvSum (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)) R E δ D)
    (h₁ : List.Pointwise R vs₁ Ds₁)
    (h₂ : List.Pointwise R vs₂ Ds₂)
    (hl₁ : vs₁.length = a) (hl₂ : vs₂.length = b) :
    ∃ C, Heap.EnvSum (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)) R
        ((List.range' H.length (vs₁ ++ vs₂).length).reverse ++ E) (δ.extendBinders πs πs')
        (D +ᶜ C +ᶜ (Demand.positions (List.ofFn πs) Ds₁ +ᶜ Demand.positions (List.ofFn πs') Ds₂)) ∧
      Demand.allocated H (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)) =
        ϖ ·ᶜ C ∧ (∀ c, c < H.length → C c = .zero) ∧
      ∀ (j : Nat) (π : Multiplicity), (List.ofFn πs ++ List.ofFn πs')[j]? = some π →
        C (H.length + j) = π := by
  have hd₁ := h₁.length
  have hd₂ := h₂.length
  let bs := (List.ofFn πs ++ List.ofFn πs').zip ((vs₁ ++ vs₂).zip (Ds₁ ++ Ds₂))
  have hlen : (List.ofFn πs ++ List.ofFn πs').length = (vs₁ ++ vs₂).length := by simp; omega
  have hlen' : (vs₁ ++ vs₂).length = (Ds₁ ++ Ds₂).length := by simp; omega
  have hfst : bs.map Prod.fst = List.ofFn πs ++ List.ofFn πs' :=
    List.map_fst_zip (by simp; omega)
  have hsnd : bs.map Prod.snd = (vs₁ ++ vs₂).zip (Ds₁ ++ Ds₂) :=
    List.map_snd_zip (by simp; omega)
  have hm₁ : bs.map (fun b => ϖ * b.1) = (List.ofFn πs ++ List.ofFn πs').map (ϖ * ·) := by
    rw [← hfst, List.map_map]
    rfl
  have hm₂ : bs.map (·.2.1) = vs₁ ++ vs₂ := by
    rw [show (fun x : Multiplicity × Nat × Demand => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← List.map_map, hsnd, List.map_fst_zip (by simp; omega)]
  have hbl : bs.length = a + b := by simp [bs]; omega
  refine ⟨Demand.cells H.length bs, ?_, ?_, Demand.cells_lt _ _, fun j π hπ => ?_⟩
  · have hb := Heap.EnvSum.bindAll hE H.length (a + b) bs hbl
      (fun l x hx => by
        obtain ⟨hx₁, hx₂⟩ := List.getElem?_zip_eq_some.1 hx
        obtain ⟨hx₂, -⟩ := List.getElem?_zip_eq_some.1 hx₂
        refine ⟨ϖ * x.1, Heap.bind_getElem? H _ _ l _ _ ?_ hx₂⟩
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
  · rw [← Demand.allocated_bind ϖ H bs, hm₁, hm₂]
  · rw [← hfst, List.getElem?_map] at hπ
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hπ
    exact Demand.cells_get _ _ j x hx

/-- The cells that a branch allocates for its `a + b` variables, at the multiplicities of its
binders times the weight, give the environment of the branch a demand for the extended vector: that
of the scope, the reads of the new cells, and the uses of their values. -/
theorem Heap.EnvDemand.bindBranch {H : Heap} (ϖ : Multiplicity) {n a b : Nat} {E : List Nat}
    {δ : MultiplicityVector n} {D : Demand} (πs : Fin a → Multiplicity) (πs' : Fin b → Multiplicity)
    {vs₁ vs₂ : List Nat} {Ds₁ Ds₂ : List Demand}
    (hE : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)).EnvDemand E δ D)
    (h₁ : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)).ValueDemands vs₁ Ds₁)
    (h₂ : (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)).ValueDemands vs₂ Ds₂)
    (hl₁ : vs₁.length = a) (hl₂ : vs₂.length = b) :
    ∃ C, (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)).EnvDemand
        ((List.range' H.length (vs₁ ++ vs₂).length).reverse ++ E) (δ.extendBinders πs πs')
        (D +ᶜ C +ᶜ (Demand.positions (List.ofFn πs) Ds₁ +ᶜ Demand.positions (List.ofFn πs') Ds₂)) ∧
      Demand.allocated H (H.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (vs₁ ++ vs₂)) =
        ϖ ·ᶜ C := by
  obtain ⟨C, hC, hal, -, -⟩ := Heap.EnvSum.bindBranch ϖ πs πs' hE.toEnvSum h₁ h₂ hl₁ hl₂
  exact ⟨C, hC.toEnvDemand, hal⟩

/-- A term already built, of a multiplicity other than `0`, pays the demand of its value. -/
theorem Multiplicity.done_le : ∀ ϖ π d : Multiplicity, π ≠ .zero →
    ϖ * (π * d + .zero + .zero) ≤ ϖ * d := by decide

end Sic.Core
