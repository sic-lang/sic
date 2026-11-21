module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Evaluation.Paths

/-!
# Claims

The claims of the uniqueness at run time of annex 20 of RFC 36: a value owned alone claims the
addresses that it holds alone, `H; g ⊢ ℓ ⊳ b`, itself, the fields and the entries of the state that
it stores at the requirement `1` and at a multiplicity other than `0`, the cells of the variables of
its scope that its closure owns alone and reads, as the annotation `g` of the heap gives the
ownership and the usage of its scope, and what the value bound by each cell that it claims claims.
The uniqueness at run time compares the claims of the values owned alone with the references that
the reaches of `Sic/Core/Evaluation/Paths.lean` count: an address claimed is referred to at most
once.
A claim follows a reference that the reach of the value counts, so that what a value claims is in
its reach: the claims of a closure read the usage of its scope in the annotation, which its reach
reads too.

The annotation is valid for a heap, `⊢_Ω H ◀ g`, when the branches of each closure have their
ownership under the ownership of its scope, and their usage under the usage of its scope, which the
evaluation gives each closure that it builds, from the corecursor that builds it; the program has
its ownership, `⊢ 𝒫 ◀ Ω`, when each of its bodies has the ownership that `Ω` gives its constant.

ADE have no ownership, and no claims.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- `H; g ⊢ ℓ ⊳ b`: the value at the address `ℓ` of the heap `H`, annotated by `g`, claims the
address `b`, which it holds alone when it is owned alone. -/
inductive Heap.Claims (H : Heap) (g : Heap.Annotation) : Nat → Nat → Prop where
  /-- A value claims itself.
  RFC: `\mathsf{claim}.\mathsf{self}` -/
  | self (ℓ : Nat) : Heap.Claims H g ℓ ℓ
  /-- A constructor claims what each field that it stores at the requirement `1` and at a
  multiplicity other than `0` claims.
  RFC: `\mathsf{claim}.c` -/
  | ctor {ℓ i k a b : Nat} {πs ϱs : List Multiplicity} {as : List Nat} {π : Multiplicity}
      (h : H[ℓ]? = some (.ctor i πs ϱs as)) (ha : as[k]? = some a) (hπ : πs[k]? = some π)
      (hπ₀ : π ≠ .zero) (hϱ : ϱs[k]? = some .one) (hb : Heap.Claims H g a b) :
      Heap.Claims H g ℓ b
  /-- A closure claims what each entry of its state that it stores at the requirement `1` and at a
  multiplicity other than `0` claims.
  RFC: `\mathsf{claim}.\mathsf{state}` -/
  | state {ℓ n k a b : Nat} {E : List Nat} {Ps : TargetDestructorBranches n}
      {πs ϱs : List Multiplicity} {as : List Nat} {π : Multiplicity}
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (ha : as[k]? = some a) (hπ : πs[k]? = some π)
      (hπ₀ : π ≠ .zero) (hϱ : ϱs[k]? = some .one) (hb : Heap.Claims H g a b) :
      Heap.Claims H g ℓ b
  /-- A closure claims what the cell of each variable of its scope that it owns alone and reads,
  as the annotation gives the ownership and the usage of its scope, claims.
  RFC: `\mathsf{claim}.\mathsf{scope}` -/
  | scope {ℓ n c b : Nat} {E : List Nat} {Ps : TargetDestructorBranches n}
      {πs ϱs : List Multiplicity} {as : List Nat} (x : Fin n)
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (hc : E[(x : Nat)]? = some c)
      (hδ : g.usage ℓ n x ≠ .zero) (hφ : g.ownership ℓ n x = .one) (hb : Heap.Claims H g c b) :
      Heap.Claims H g ℓ b
  /-- A cell claims what the value that it binds claims.
  RFC: `\mathsf{claim}.\mathsf{bind}` -/
  | cell {c a b : Nat} {π : Multiplicity} (h : H[c]? = some (.cell π a))
      (hb : Heap.Claims H g a b) : Heap.Claims H g c b

-- ADE: none.
/-- `H; g ⊢ E ⊳_{φ;ν} b`: a term that owns the variables of the environment `E` as `φ` gives and
reads them as `ν` allows claims the address `b`, which the cell of a variable that it owns alone and
reads claims.
RFC: `\mathsf{claim}_E` -/
def Heap.EnvClaims (H : Heap) (g : Heap.Annotation) {n : Nat} (E : List Nat)
    (φ ν : MultiplicityVector n) (b : Nat) : Prop :=
  ∃ (x : Fin n) (c : Nat), E[(x : Nat)]? = some c ∧ φ x = .one ∧ ν x ≠ .zero ∧
    Heap.Claims H g c b

-- ADE: none.
/-- `⊢_Ω H ◀ g`: the annotation `g` is valid for the heap `H`: the branches of each closure have
their ownership under the ownership of its scope, given the ownership `Ω` of each constant, and
their usage under the usage of its scope.
RFC: `\mathsf{valid}_g` -/
def Heap.Annotation.Valid (Ω : Name → Multiplicity) (H : Heap) (g : Heap.Annotation) : Prop :=
  ∀ ℓ n E Ps πs ϱs as, H[ℓ]? = some (.corec n E Ps πs ϱs as) →
    TargetDestructorBranches.Ownership Ω (g.ownership ℓ n) Ps ∧ TargetDestructorBranches.Usage (g.usage ℓ n) Ps

-- ADE: none.
/-- `⊢ 𝒫 ◀ Ω`: each body of the program, a closed term, has the ownership that `Ω` gives its
constant.
RFC: `\mathsf{own}_{\mathcal{P}}` -/
def Program.Ownership (P : Program) (Ω : Name → Multiplicity) : Prop :=
  ∀ f qs ps M, P f qs ps = some M → Target.Ownership Ω (𝟘ᵛ : MultiplicityVector 0) (Ω f) M

/-! ## Properties -/

/-- A cell claims itself and what the value that it binds claims. -/
theorem Heap.Claims.cell_inv {H : Heap} {g : Heap.Annotation} {c a b : Nat} {π : Multiplicity}
    (hc : H[c]? = some (.cell π a)) (h : Heap.Claims H g c b) : b = c ∨ Heap.Claims H g a b := by
  cases h with
  | self => exact .inl rfl
  | ctor h' | state h' | scope _ h' => cases hc.symm.trans h'
  | cell h' hb =>
    cases hc.symm.trans h'
    exact .inr hb

/-- `↯` claims itself alone. -/
theorem Heap.Claims.erased_inv {H : Heap} {g : Heap.Annotation} {ℓ b : Nat}
    (hℓ : H[ℓ]? = some .erased) (h : Heap.Claims H g ℓ b) : b = ℓ := by
  cases h with
  | self => rfl
  | ctor h' | state h' | scope _ h' | cell h' => cases hℓ.symm.trans h'

-- ADE: none.
/-- What a value claims is in its reach, and what a cell claims is the cell or in the reach of the
value that it binds: each claim follows a reference that the reach counts.
RFC: `\mathsf{claim}.{⇝}`
RFC: `\mathsf{claim}.\mathsf{bind}_{⇝}` -/
theorem Heap.Claims.reach_ne_zero {H : Heap} {g : Heap.Annotation} {ℓ b : Nat}
    (h : Heap.Claims H g ℓ b) :
    (∀ U, Heap.ValueReach H g ℓ U → U b ≠ .zero) ∧
      ∀ π a U, H[ℓ]? = some (.cell π a) → Heap.ValueReach H g a U →
        (Demand.unit ℓ +ᶜ U) b ≠ .zero := by
  have hunit : ∀ ℓ : Nat, Demand.unit ℓ ℓ ≠ .zero := fun ℓ => by simp [Demand.unit] <;> decide
  induction h with
  | self ℓ =>
    refine ⟨fun U hU => ?_, fun π a U _ _ => Multiplicity.add_ne_zero_left _ _ (hunit ℓ)⟩
    cases hU with
    | erased => exact hunit ℓ
    | ctor | corec => exact Multiplicity.add_ne_zero_left _ _ (hunit ℓ)
  | ctor h ha hπ hπ₀ hϱ _ ih =>
    refine ⟨fun U hU => ?_, fun π a U hc _ => by cases h.symm.trans hc⟩
    cases hU with
    | erased h' | corec h' => cases h.symm.trans h'
    | ctor h' hs =>
      cases h.symm.trans h'
      exact Multiplicity.add_ne_zero_right _ _ (hs.ne_zero ha hπ hπ₀ ih.1)
  | state h ha hπ hπ₀ hϱ _ ih =>
    refine ⟨fun U hU => ?_, fun π a U hc _ => by cases h.symm.trans hc⟩
    cases hU with
    | erased h' | ctor h' => cases h.symm.trans h'
    | corec h' hE hs =>
      cases h.symm.trans h'
      exact Multiplicity.add_ne_zero_right _ _
        (Multiplicity.add_ne_zero_right _ _ (hs.ne_zero ha hπ hπ₀ ih.1))
  | scope x h hc hδ hφ _ ih =>
    refine ⟨fun U hU => ?_, fun π a U hc' _ => by cases h.symm.trans hc'⟩
    cases hU with
    | erased h' | ctor h' => cases h.symm.trans h'
    | corec h' hE hs =>
      cases h.symm.trans h'
      exact Multiplicity.add_ne_zero_right _ _
        (Multiplicity.add_ne_zero_left _ _ (hE.ne_zero x hc hδ ih.2))
  | cell h _ ih =>
    refine ⟨fun U hU => ?_, fun π a U hc hU => ?_⟩
    · cases hU with
      | erased h' | ctor h' | corec h' => cases h.symm.trans h'
    · cases h.symm.trans hc
      exact Multiplicity.add_ne_zero_right _ _ (ih.1 U hU)

-- ADE: none.
/-- What a term claims through its environment is in the reach of the environment.
RFC: `\mathsf{claim}_E.{⇝}` -/
theorem Heap.EnvClaims.reach_ne_zero {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {φ ν : MultiplicityVector n} {b : Nat} (h : Heap.EnvClaims H g E φ ν b) {U : Demand}
    (hU : Heap.EnvReach H g E ν U) : U b ≠ .zero := by
  obtain ⟨x, c, hc, -, hν, hb⟩ := h
  exact hU.ne_zero x hc hν hb.reach_ne_zero.2

-- ADE: none.
/-- The claims of a value hold in each heap that extends its heap, annotated by an annotation that
extends its annotation.
RFC: `\mathsf{claim}.{\sqsubseteq}` -/
theorem Heap.Claims.mono {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {ℓ b : Nat} (h : Heap.Claims H g ℓ b) :
    Heap.Claims H' g' ℓ b := by
  induction h with
  | self ℓ => exact .self ℓ
  | ctor h ha hπ hπ₀ hϱ _ ih => exact .ctor (hH.getElem? h) ha hπ hπ₀ hϱ ih
  | state h ha hπ hπ₀ hϱ _ ih => exact .state (hH.getElem? h) ha hπ hπ₀ hϱ ih
  | scope x h hc hδ hφ _ ih =>
    have hℓ := (List.getElem?_eq_some_iff.1 h).1
    exact .scope x (hH.getElem? h) hc (by rw [(hg _ hℓ).2]; exact hδ)
      (by rw [(hg _ hℓ).1]; exact hφ) ih
  | cell h _ ih => exact .cell (hH.getElem? h) ih

-- ADE: none.
/-- A value that has a reach in a heap, or a cell that binds one, claims in a heap that extends it,
annotated by an annotation that extends its annotation, only what it claims in the heap: its paths
stay in the heap.
RFC: `\mathsf{claim}.{\sqsupseteq}` -/
theorem Heap.Claims.of_extends {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {ℓ b : Nat} (h : Heap.Claims H' g' ℓ b) :
    ((∃ U, Heap.ValueReach H g ℓ U) ∨
      ∃ π a U, H[ℓ]? = some (.cell π a) ∧ Heap.ValueReach H g a U) → Heap.Claims H g ℓ b := by
  induction h with
  | self ℓ => exact fun _ => .self ℓ
  | ctor h' ha hπ hπ₀ hϱ _ ih =>
    rintro (⟨U, hU⟩ | ⟨π, a, U, hc, -⟩)
    · cases hU with
      | erased h | corec h => cases (hH.getElem? h).symm.trans h'
      | ctor h hs =>
        cases (hH.getElem? h).symm.trans h'
        exact .ctor h ha hπ hπ₀ hϱ (ih (.inl (hs.get ha)))
    · cases (hH.getElem? hc).symm.trans h'
  | state h' ha hπ hπ₀ hϱ _ ih =>
    rintro (⟨U, hU⟩ | ⟨π, a, U, hc, -⟩)
    · cases hU with
      | erased h | ctor h => cases (hH.getElem? h).symm.trans h'
      | corec h hE hs =>
        cases (hH.getElem? h).symm.trans h'
        exact .state h ha hπ hπ₀ hϱ (ih (.inl (hs.get ha)))
    · cases (hH.getElem? hc).symm.trans h'
  | scope x h' hc hδ hφ _ ih =>
    rintro (⟨U, hU⟩ | ⟨π, a, U, hc', -⟩)
    · cases hU with
      | erased h | ctor h => cases (hH.getElem? h).symm.trans h'
      | corec h hE hs =>
        cases (hH.getElem? h).symm.trans h'
        have hℓ := (List.getElem?_eq_some_iff.1 h).1
        exact .scope x h hc (by rw [← (hg _ hℓ).2]; exact hδ) (by rw [← (hg _ hℓ).1]; exact hφ)
          (ih (.inr (hE.get x hc)))
    · cases (hH.getElem? hc').symm.trans h'
  | cell h' _ ih =>
    rintro (⟨U, hU⟩ | ⟨π, a, U, hc, hU⟩)
    · cases hU with
      | erased h | ctor h | corec h => cases (hH.getElem? h).symm.trans h'
    · cases (hH.getElem? hc).symm.trans h'
      exact .cell hc (ih (.inl ⟨U, hU⟩))

-- ADE: none.
/-- A term claims through an environment that has a reach in a heap, in a heap that extends it,
only what it claims in the heap.
RFC: `\mathsf{claim}_E.{\sqsupseteq}` -/
theorem Heap.EnvClaims.of_extends {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {n : Nat} {E : List Nat} {φ ν : MultiplicityVector n}
    {b : Nat} (h : Heap.EnvClaims H' g' E φ ν b) {U : Demand} (hU : Heap.EnvReach H g E ν U) :
    Heap.EnvClaims H g E φ ν b := by
  obtain ⟨x, c, hc, hφ, hν, hb⟩ := h
  exact ⟨x, c, hc, hφ, hν, hb.of_extends hH hg (.inr (hU.get x hc))⟩

/-- A term that reads variables as a vector allows claims what it claims reading them as a vector
that reads each variable that it reads. -/
theorem Heap.EnvClaims.imp {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {φ ν ν' : MultiplicityVector n} {b : Nat} (h : Heap.EnvClaims H g E φ ν b)
    (hν : ∀ x, ν x ≠ .zero → ν' x ≠ .zero) : Heap.EnvClaims H g E φ ν' b := by
  obtain ⟨x, c, hc, hφ, hx, hb⟩ := h
  exact ⟨x, c, hc, hφ, hν x hx, hb⟩

end Sic.Core
