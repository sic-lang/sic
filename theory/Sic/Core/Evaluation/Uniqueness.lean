module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Evaluation.Conservation
public import Sic.Core.Evaluation.Paths

/-!
# Uniqueness

The claims of the uniqueness at run time of annex 17 of RFC 36: a value owned alone claims the
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

ADE have no ownership, and no uniqueness at run time.
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
  | state {ℓ n k a b : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
      {πs ϱs : List Multiplicity} {as : List Nat} {π : Multiplicity}
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (ha : as[k]? = some a) (hπ : πs[k]? = some π)
      (hπ₀ : π ≠ .zero) (hϱ : ϱs[k]? = some .one) (hb : Heap.Claims H g a b) :
      Heap.Claims H g ℓ b
  /-- A closure claims what the cell of each variable of its scope that it owns alone and reads,
  as the annotation gives the ownership and the usage of its scope, claims.
  RFC: `\mathsf{claim}.\mathsf{scope}` -/
  | scope {ℓ n c b : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
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
    TargetCorecBranches.Ownership Ω (g.ownership ℓ n) Ps ∧ TargetCorecBranches.Usage (g.usage ℓ n) Ps

-- ADE: none.
/-- `⊢ 𝒫 ◀ Ω`: each body of the program, a closed term, has the ownership that `Ω` gives its
constant.
RFC: `\mathsf{own}_{\mathcal{P}}` -/
def Program.Ownership (P : Program) (Ω : Name → Multiplicity) : Prop :=
  ∀ f qs ps M, P f qs ps = some M → Target.Ownership Ω (𝟘ᵛ : MultiplicityVector 0) (Ω f) M

/-! ## Multiplicities -/

/-- A sum whose first operand is not `0` is not `0`. -/
theorem Multiplicity.add_ne_zero_left : ∀ x y : Multiplicity, x ≠ .zero → x + y ≠ .zero := by decide

/-- A sum whose second operand is not `0` is not `0`. -/
theorem Multiplicity.add_ne_zero_right : ∀ x y : Multiplicity, y ≠ .zero → x + y ≠ .zero := by
  decide

/-- A product whose operands are not `0` is not `0`. -/
theorem Multiplicity.mul_ne_zero : ∀ x y : Multiplicity, x ≠ .zero → y ≠ .zero → x * y ≠ .zero := by
  decide

/-! ## Reaches -/

mutual

-- ADE: none.
/-- The reach of a value is unique. -/
theorem Heap.ValueReach.det {H : Heap} {g : Heap.Annotation} {ℓ : Nat} {U U' : Demand} :
    Heap.ValueReach H g ℓ U → Heap.ValueReach H g ℓ U' → U = U'
  | .erased _, .erased _ => rfl
  | .ctor h hs, .ctor h' hs' => by
    cases h.symm.trans h'
    rw [hs.det hs']
  | .corec h hE hs, .corec h' hE' hs' => by
    cases h.symm.trans h'
    rw [hE.det hE', hs.det hs']
  | .erased h, .ctor h' _ | .erased h, .corec h' _ _ | .ctor h _, .erased h'
  | .ctor h _, .corec h' _ _ | .corec h _ _, .erased h' | .corec h _ _, .ctor h' _ => by
    cases h.symm.trans h'

-- ADE: none.
/-- The reach of positions is unique. -/
theorem Heap.PositionsReach.det {H : Heap} {g : Heap.Annotation} {πs : List Multiplicity}
    {as : List Nat} {U U' : Demand} :
    Heap.PositionsReach H g πs as U → Heap.PositionsReach H g πs as U' → U = U'
  | .nil, .nil => rfl
  | .cons h hs, .cons h' hs' => by rw [h.det h', hs.det hs']

-- ADE: none.
/-- The reach of an environment is unique. -/
theorem Heap.EnvReach.det {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {ν : MultiplicityVector n} {U U' : Demand} :
    Heap.EnvReach H g E ν U → Heap.EnvReach H g E ν U' → U = U'
  | .nil, .nil => rfl
  | .cons hc h hE, .cons hc' h' hE' => by
    cases hc.symm.trans hc'
    rw [h.det h', hE.det hE']

end

/-- The reach of an environment is a sum of the reaches of its values. -/
theorem Heap.EnvReach.toEnvSum {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {ν : MultiplicityVector n} {U : Demand} :
    Heap.EnvReach H g E ν U → Heap.EnvSum H (Heap.ValueReach H g) E ν U
  | .nil => .nil
  | .cons hc h hE => .cons hc h hE.toEnvSum

/-- A sum of the reaches of the values of an environment is a reach of the environment. -/
theorem Heap.EnvSum.toEnvReach {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {ν : MultiplicityVector n} {U : Demand} :
    Heap.EnvSum H (Heap.ValueReach H g) E ν U → Heap.EnvReach H g E ν U
  | .nil => .nil
  | .cons hc h hE => .cons hc h hE.toEnvReach

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

/-- A value that refers to an address is at an address of its heap, as the address is. -/
theorem Heap.ValueReach.lt {H : Heap} {g : Heap.Annotation} {ℓ : Nat} {U : Demand}
    (h : Heap.ValueReach H g ℓ U) {b : Nat} (hb : U b ≠ .zero) : b < H.length :=
  Nat.lt_of_not_le fun hle => hb (h.eq_zero b hle)

/-- An environment that refers to an address refers to an address of its heap. -/
theorem Heap.EnvReach.lt {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {ν : MultiplicityVector n} {U : Demand} (h : Heap.EnvReach H g E ν U) {b : Nat}
    (hb : U b ≠ .zero) : b < H.length :=
  Nat.lt_of_not_le fun hle => hb (h.eq_zero b hle)

/-- The value at a position has a reach. -/
theorem Heap.PositionsReach.get {H : Heap} {g : Heap.Annotation} : {πs : List Multiplicity} →
    {as : List Nat} → {U : Demand} → Heap.PositionsReach H g πs as U → {k a : Nat} →
      as[k]? = some a → ∃ U', Heap.ValueReach H g a U'
  | _, _, _, .cons h _, 0, _, ha => by cases ha; exact ⟨_, h⟩
  | _, _, _, .cons _ hs, _ + 1, _, ha => hs.get (by simpa using ha)

/-- The cell of a variable of an environment binds a value that has a reach. -/
theorem Heap.EnvReach.get {H : Heap} {g : Heap.Annotation} : {n : Nat} → {E : List Nat} →
    {ν : MultiplicityVector n} → {U : Demand} → Heap.EnvReach H g E ν U → (x : Fin n) → {c : Nat} →
      E[(x : Nat)]? = some c → ∃ π a U', H[c]? = some (.cell π a) ∧ Heap.ValueReach H g a U'
  | _, _, _, _, .cons hc h hE, x, c, hx => by
    cases x using Fin.cases with
    | zero => cases hx; exact ⟨_, _, _, hc, h⟩
    | succ x => exact hE.get x (by simpa using hx)

/-- Positions refer to what the value at one of them, of a multiplicity other than `0`, refers to. -/
theorem Heap.PositionsReach.ne_zero {H : Heap} {g : Heap.Annotation} {b : Nat} :
    {πs : List Multiplicity} → {as : List Nat} → {U : Demand} → Heap.PositionsReach H g πs as U →
      {k a : Nat} → {π : Multiplicity} → as[k]? = some a → πs[k]? = some π → π ≠ .zero →
      (∀ U', Heap.ValueReach H g a U' → U' b ≠ .zero) → U b ≠ .zero
  | _, _, _, .cons (π := π') h _, 0, _, _, ha, hπ, hπ₀, hb => by
    cases ha
    cases hπ
    refine Multiplicity.add_ne_zero_left _ _ ?_
    show π'.references * _ ≠ _
    exact Multiplicity.mul_ne_zero _ _ (by cases π' <;> simp_all [Multiplicity.references])
      (hb _ h)
  | _, _, _, .cons _ hs, _ + 1, _, _, ha, hπ, hπ₀, hb =>
    Multiplicity.add_ne_zero_right _ _
      (hs.ne_zero (by simpa using ha) (by simpa using hπ) hπ₀ hb)

/-- An environment refers to what the cell of one of its variables, read at a multiplicity other
than `0`, and the value that it binds refer to. -/
theorem Heap.EnvReach.ne_zero {H : Heap} {g : Heap.Annotation} {b : Nat} : {n : Nat} →
    {E : List Nat} → {ν : MultiplicityVector n} → {U : Demand} → Heap.EnvReach H g E ν U →
      (x : Fin n) → {c : Nat} → E[(x : Nat)]? = some c → ν x ≠ .zero →
      (∀ π a U', H[c]? = some (.cell π a) → Heap.ValueReach H g a U' →
        (Demand.unit c +ᶜ U') b ≠ .zero) → U b ≠ .zero
  | _, _, _, _, .cons hc h hE, x, c, hx, hν, hb => by
    cases x using Fin.cases with
    | zero =>
      cases hx
      exact Multiplicity.add_ne_zero_left _ _ (Multiplicity.mul_ne_zero _ _ hν (hb _ _ _ hc h))
    | succ x =>
      exact Multiplicity.add_ne_zero_right _ _ (hE.ne_zero x (by simpa using hx) hν hb)

/-! ## Claims -/

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
value that it binds: each claim follows a reference that the reach counts. -/
theorem Heap.Claims.reach_ne_zero {H : Heap} {g : Heap.Annotation} {ℓ b : Nat}
    (h : Heap.Claims H g ℓ b) :
    (∀ U, Heap.ValueReach H g ℓ U → U b ≠ .zero) ∧
      ∀ π a U, H[ℓ]? = some (.cell π a) → Heap.ValueReach H g a U →
        (Demand.unit ℓ +ᶜ U) b ≠ .zero := by
  have hunit : ∀ ℓ : Nat, Demand.unit ℓ ℓ ≠ .zero := fun ℓ => by simp [Demand.unit]
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
/-- What a term claims through its environment is in the reach of the environment. -/
theorem Heap.EnvClaims.reach_ne_zero {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat}
    {φ ν : MultiplicityVector n} {b : Nat} (h : Heap.EnvClaims H g E φ ν b) {U : Demand}
    (hU : Heap.EnvReach H g E ν U) : U b ≠ .zero := by
  obtain ⟨x, c, hc, -, hν, hb⟩ := h
  exact hU.ne_zero x hc hν hb.reach_ne_zero.2

-- ADE: none.
/-- The claims of a value hold in each heap that extends its heap, annotated by an annotation that
extends its annotation. -/
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
stay in the heap. -/
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
only what it claims in the heap. -/
theorem Heap.EnvClaims.of_extends {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {n : Nat} {E : List Nat} {φ ν : MultiplicityVector n}
    {b : Nat} (h : Heap.EnvClaims H' g' E φ ν b) {U : Demand} (hU : Heap.EnvReach H g E ν U) :
    Heap.EnvClaims H g E φ ν b := by
  obtain ⟨x, c, hc, hφ, hν, hb⟩ := h
  exact ⟨x, c, hc, hφ, hν, hb.of_extends hH hg (.inr (hU.get x hc))⟩

/-! ## Annotations -/

/-- An annotation extends itself. -/
theorem Heap.Annotation.Extends.refl (H : Heap) (g : Heap.Annotation) :
    Heap.Annotation.Extends H g g := fun _ _ => ⟨rfl, rfl⟩

/-- The extension of the annotations is transitive along the extension of the heaps. -/
theorem Heap.Annotation.Extends.trans {H H' : Heap} {g₁ g₂ g₃ : Heap.Annotation}
    (hH : H.Extends H') (h₁ : Heap.Annotation.Extends H g₁ g₂)
    (h₂ : Heap.Annotation.Extends H' g₂ g₃) : Heap.Annotation.Extends H g₁ g₃ := fun ℓ hℓ =>
  have hℓ' : ℓ < H'.length := Nat.lt_of_lt_of_le hℓ hH.length_le
  ⟨(h₂ ℓ hℓ').1.trans (h₁ ℓ hℓ).1, (h₂ ℓ hℓ').2.trans (h₁ ℓ hℓ).2⟩

-- ADE: none.
/-- The annotation `g` with the ownership `φ` and the usage `δ` of the scope of `n` variables of
the closure at the address `ℓ`. -/
def Heap.Annotation.set (g : Heap.Annotation) (ℓ n : Nat) (φ δ : MultiplicityVector n) :
    Heap.Annotation where
  ownership ℓ' n' := if h : ℓ' = ℓ ∧ n' = n then h.2 ▸ φ else g.ownership ℓ' n'
  usage ℓ' n' := if h : ℓ' = ℓ ∧ n' = n then h.2 ▸ δ else g.usage ℓ' n'

/-- The annotation of a closure is the one that it is given. -/
theorem Heap.Annotation.set_self (g : Heap.Annotation) (ℓ n : Nat) (φ δ : MultiplicityVector n) :
    (g.set ℓ n φ δ).ownership ℓ n = φ ∧ (g.set ℓ n φ δ).usage ℓ n = δ := by
  simp [Heap.Annotation.set]

/-- The annotation of a new closure extends the annotation of the heap before it. -/
theorem Heap.Annotation.set_extends (H : Heap) (g : Heap.Annotation) (n : Nat)
    (φ δ : MultiplicityVector n) : Heap.Annotation.Extends H g (g.set H.length n φ δ) :=
  fun ℓ hℓ => by
    have hne : ℓ ≠ H.length := Nat.ne_of_lt hℓ
    constructor <;> funext n' <;> simp [Heap.Annotation.set, hne]

/-- An annotation valid for a heap is valid for the heap with a new value that is not a closure. -/
theorem Heap.Annotation.Valid.concat {Ω : Name → Multiplicity} {H : Heap} {g : Heap.Annotation}
    (hg : g.Valid Ω H) {v : Value} (hv : ∀ n E Ps πs ϱs as, v ≠ .corec n E Ps πs ϱs as) :
    g.Valid Ω (H ++ [v]) := fun ℓ n E Ps πs ϱs as h => by
  by_cases hℓ : ℓ < H.length
  · rw [List.getElem?_append_left hℓ] at h
    exact hg ℓ n E Ps πs ϱs as h
  · have hlt := (List.getElem?_eq_some_iff.1 h).1
    obtain rfl : ℓ = H.length := by simp at hlt; omega
    rw [List.getElem?_concat_length] at h
    exact absurd (Option.some.inj h) (hv n E Ps πs ϱs as)

/-- An annotation valid for a heap, with the ownership and the usage of the branches of a new
closure, is valid for the heap with the closure. -/
theorem Heap.Annotation.Valid.concat_corec {Ω : Name → Multiplicity} {H : Heap}
    {g : Heap.Annotation} (hg : g.Valid Ω H) {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
    {πs ϱs : List Multiplicity} {as : List Nat} {φ δ : MultiplicityVector n}
    (hφ : TargetCorecBranches.Ownership Ω φ Ps) (hδ : TargetCorecBranches.Usage δ Ps) :
    (g.set H.length n φ δ).Valid Ω (H ++ [.corec n E Ps πs ϱs as]) :=
  fun ℓ n' E' Ps' πs' ϱs' as' h => by
    by_cases hℓ : ℓ < H.length
    · rw [List.getElem?_append_left hℓ] at h
      rw [((Heap.Annotation.set_extends H g n φ δ) ℓ hℓ).1,
        ((Heap.Annotation.set_extends H g n φ δ) ℓ hℓ).2]
      exact hg ℓ n' E' Ps' πs' ϱs' as' h
    · have hlt := (List.getElem?_eq_some_iff.1 h).1
      obtain rfl : ℓ = H.length := by simp at hlt; omega
      rw [List.getElem?_concat_length] at h
      cases h
      rw [(Heap.Annotation.set_self g H.length n φ δ).1,
        (Heap.Annotation.set_self g H.length n φ δ).2]
      exact ⟨hφ, hδ⟩

end Sic.Core
