module

public import Sic.Core.Evaluation.Demand

/-!
# Paths

The reaches of annex 20 of RFC 36: the reach of a value, `H ⊢ ℓ ⇝ U`, counts the references that a
use of the value at the address `ℓ` of the heap `H` makes to each address, a value or a cell, along
the paths that start from it, so that the uniqueness at run time compares the references to an
address with its ownership.
A value refers to itself once, a constructor to each of its fields, and a closure to each entry of
its state, once whatever the multiplicity of the position, other than `0`, since a value owned alone
is used once and reads a position once, whatever its multiplicity bounds over all its uses: a
position of the multiplicity `0` is never read, and makes no reference.
A closure also reads the cells of the variables of its scope as the usage `δ` that an annotation
`g` of the heap gives it allows, each read referring to the cell and to its value: the annotation
gives each closure the ownership and the usage of its scope at its creation, which the value does
not hold, so that the reach of a value is unique, and the claims of the uniqueness at run time,
which read the same annotation, follow the references that the reach counts.
The reach of an environment, `H ⊢ E ⇝_ν U`, counts the references of a term that reads its variables
as `ν` allows: `ν(x)` reads of the cell of `x`, each referring to its value.
A reach is a demand of `Sic/Core/Evaluation/Demand.lean`, a multiplicity for each address, with its
operations, and differs from the demand of the value by counting the values as well as the cells,
the positions by their references rather than their uses, and by reading the usage of each closure
in the annotation rather than choosing one.
ADE have no reaches: their usage states no uniqueness.
-/

@[expose] public section

namespace Sic.Grading

/-- `⌈π⌉`: the references that a position of the multiplicity `π` makes to its value, none for `0`,
whose position is never read, and one otherwise.
RFC: `\mathsf{refs}_\pi` -/
def Multiplicity.references : Multiplicity → Multiplicity
  | .zero => .zero
  | _ => .one

/-- The references of a multiplicity that is not `0`, times a multiplicity that is not `0`, are not
`0`. -/
theorem Multiplicity.references_mul_ne_zero :
    ∀ x y : Multiplicity, x ≠ .zero → y ≠ .zero → x.references * y ≠ .zero := by decide

end Sic.Grading

namespace Sic.Core

open Sic.Grading Sic.Math

/-- `g`: an annotation of the heap, which gives the closure at each address, of a scope of `n`
variables, the ownership `φ_ℓ` and the usage `δ_ℓ` of its scope, those of the corecursor that built
it, which its value does not hold.
RFC: `\mathsf{annotation}_H` -/
structure Heap.Annotation where
  /-- `φ_ℓ`: the ownership of the scope of the closure at the address `ℓ`. -/
  ownership : Nat → (n : Nat) → MultiplicityVector n
  /-- `δ_ℓ`: the usage of the scope of the closure at the address `ℓ`. -/
  usage : Nat → (n : Nat) → MultiplicityVector n

/-- `g ⊑_H g'`: the annotation `g'` extends the annotation `g` of the heap `H`, with the same
ownership and usage at each address of `H`.
RFC: `\sqsubseteq_g` -/
def Heap.Annotation.Extends (H : Heap) (g g' : Heap.Annotation) : Prop :=
  ∀ ℓ, ℓ < H.length → g'.ownership ℓ = g.ownership ℓ ∧ g'.usage ℓ = g.usage ℓ

mutual

/-- `H; g ⊢ ℓ ⇝ U`: a use of the value at the address `ℓ` of the heap `H`, annotated by `g`, refers to the addresses as
`U` counts. -/
inductive Heap.ValueReach (H : Heap) (g : Heap.Annotation) : Nat → Demand → Prop where
  /-- `↯` refers to itself.
  RFC: `\mathsf{reach}_\ell.\text{↯}` -/
  | erased {ℓ : Nat} (h : H[ℓ]? = some .erased) : Heap.ValueReach H g ℓ (Demand.unit ℓ)
  /-- A constructor refers to itself and to its fields, each once unless its multiplicity is `0`.
  RFC: `\mathsf{reach}_\ell.c` -/
  | ctor {ℓ i : Nat} {πs ϱs : List Multiplicity} {as : List Nat} {U : Demand}
      (h : H[ℓ]? = some (.ctor i πs ϱs as)) (hs : Heap.PositionsReach H g πs as U) :
      Heap.ValueReach H g ℓ (Demand.unit ℓ +ᶜ U)
  /-- A closure refers to itself, to the cells of its scope as its branches read them, which read
  the variables of its scope as the usage `δ_ℓ` that the annotation gives it allows, and to its
  state, each entry once unless its multiplicity is `0`.
  RFC: `\mathsf{reach}_\ell.\mathsf{corec}` -/
  | corec {ℓ n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {πs ϱs : List Multiplicity}
      {as : List Nat} {U₁ U₂ : Demand} (h : H[ℓ]? = some (.corec n E Ps πs ϱs as))
      (hE : Heap.EnvReach H g E (g.usage ℓ n) U₁) (hs : Heap.PositionsReach H g πs as U₂) :
      Heap.ValueReach H g ℓ (Demand.unit ℓ +ᶜ (U₁ +ᶜ U₂))

/-- `H; g ⊢ ℓ̄ ⇝ π̄ ⇝ U`: the values at the addresses `ℓ̄`, each at the multiplicity at its position in
`π̄`, refer to the addresses as `U` counts. -/
inductive Heap.PositionsReach (H : Heap) (g : Heap.Annotation) :
    List Multiplicity → List Nat → Demand → Prop where
  /-- No position refers to nothing.
  RFC: `\mathsf{reach}_{\bar\ell}.\varepsilon` -/
  | nil : Heap.PositionsReach H g [] [] 𝟘ᵛ
  /-- The first position, once unless its multiplicity is `0`, and the others.
  RFC: `\mathsf{reach}_{\bar\ell}.{,}` -/
  | cons {π : Multiplicity} {πs : List Multiplicity} {ℓ : Nat} {as : List Nat} {U₁ U₂ : Demand}
      (h : Heap.ValueReach H g ℓ U₁) (hs : Heap.PositionsReach H g πs as U₂) :
      Heap.PositionsReach H g (π :: πs) (ℓ :: as) ((π.references ·ᶜ U₁) +ᶜ U₂)

/-- `H; g ⊢ E ⇝_ν U`: a term that reads the variables of the environment `E`, the last one first, as
`ν` allows, refers to the addresses as `U` counts: `ν(x)` reads of the cell of `x`, each referring
to the cell and to its value. -/
inductive Heap.EnvReach (H : Heap) (g : Heap.Annotation) :
    {n : Nat} → List Nat → MultiplicityVector n → Demand → Prop where
  /-- The empty environment refers to nothing.
  RFC: `\mathsf{reach}_E.\varepsilon` -/
  | nil {ν : MultiplicityVector 0} : Heap.EnvReach H g [] ν 𝟘ᵛ
  /-- The last variable, a cell of the address `c` bound to the address `ℓ`, read `ν(x)` times,
  and the others.
  RFC: `\mathsf{reach}_E.{,}` -/
  | cons {n : Nat} {c : Nat} {π : Multiplicity} {ℓ : Nat} {E : List Nat}
      {ν : MultiplicityVector (n + 1)} {U₁ U₂ : Demand} (hc : H[c]? = some (.cell π ℓ))
      (h : Heap.ValueReach H g ℓ U₁) (hE : Heap.EnvReach H g E (fun x => ν x.succ) U₂) :
      Heap.EnvReach H g (c :: E) ν ((ν 0 ·ᶜ (Demand.unit c +ᶜ U₁)) +ᶜ U₂)

end

/-! ## Properties -/

mutual

/-- The reach of a value holds in each heap that extends its heap, annotated by an annotation that
extends its annotation.
RFC: `\mathsf{reach}_\ell.{\sqsubseteq}` -/
theorem Heap.ValueReach.mono {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {ℓ : Nat} {U : Demand} :
    Heap.ValueReach H g ℓ U → Heap.ValueReach H' g' ℓ U
  | .erased h => .erased (hH.getElem? h)
  | .ctor h hs => .ctor (hH.getElem? h) (hs.mono hH hg)
  | .corec h hE hs => by
    have hℓ := (List.getElem?_eq_some_iff.1 h).1
    refine .corec (hH.getElem? h) ?_ (hs.mono hH hg)
    rw [(hg _ hℓ).2]
    exact hE.mono hH hg

/-- The reach of positions holds in each heap that extends their heap, annotated by an annotation
that extends their annotation. -/
theorem Heap.PositionsReach.mono {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {πs : List Multiplicity} {as : List Nat} {U : Demand} :
    Heap.PositionsReach H g πs as U → Heap.PositionsReach H' g' πs as U
  | .nil => .nil
  | .cons h hs => .cons (h.mono hH hg) (hs.mono hH hg)

/-- The reach of an environment holds in each heap that extends its heap, annotated by an
annotation that extends its annotation.
RFC: `\mathsf{reach}_E.{\sqsubseteq}` -/
theorem Heap.EnvReach.mono {H H' : Heap} {g g' : Heap.Annotation} (hH : H.Extends H')
    (hg : Heap.Annotation.Extends H g g') {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {U : Demand} : Heap.EnvReach H g E ν U → Heap.EnvReach H' g' E ν U
  | .nil => .nil
  | .cons hc h hE => .cons (hH.getElem? hc) (h.mono hH hg) (hE.mono hH hg)

end

/-- The demand of one read of an address of the heap is `0` at each address from the length of the
heap. -/
theorem Demand.unit_eq_zero_of_length_le {H : Heap} {ℓ : Nat} {v : Value} (h : H[ℓ]? = some v)
    {a : Nat} (ha : H.length ≤ a) : Demand.unit ℓ a = .zero := by
  have := (List.getElem?_eq_some_iff.1 h).1
  simp only [Demand.unit, show a ≠ ℓ by omega, ↓reduceIte]

mutual

/-- A value refers only to addresses of its heap: the allocations of a later run, at the end of
the heap, are reached by no value that the heap holds before them.
RFC: `\mathsf{reach}_\ell.{<}` -/
theorem Heap.ValueReach.eq_zero {H : Heap} {g : Heap.Annotation} {ℓ : Nat} {U : Demand} :
    Heap.ValueReach H g ℓ U → ∀ a, H.length ≤ a → U a = .zero
  | .erased h, a, ha => Demand.unit_eq_zero_of_length_le h ha
  | .ctor h hs, a, ha => by
    show Demand.unit _ a + _ = _
    rw [Demand.unit_eq_zero_of_length_le h ha, hs.eq_zero a ha]
    rfl
  | .corec h hE hs, a, ha => by
    show Demand.unit _ a + (_ + _) = _
    rw [Demand.unit_eq_zero_of_length_le h ha, hE.eq_zero a ha, hs.eq_zero a ha]
    rfl

/-- Positions refer only to addresses of their heap. -/
theorem Heap.PositionsReach.eq_zero {H : Heap} {g : Heap.Annotation} {πs : List Multiplicity} {as : List Nat}
    {U : Demand} : Heap.PositionsReach H g πs as U → ∀ a, H.length ≤ a → U a = .zero
  | .nil, _, _ => rfl
  | .cons (π := π) h hs, a, ha => by
    show π.references * _ + _ = _
    rw [h.eq_zero a ha, hs.eq_zero a ha]
    cases π <;> rfl

/-- An environment refers only to addresses of its heap.
RFC: `\mathsf{reach}_E.{<}` -/
theorem Heap.EnvReach.eq_zero {H : Heap} {g : Heap.Annotation} {n : Nat} {E : List Nat} {ν : MultiplicityVector n}
    {U : Demand} : Heap.EnvReach H g E ν U → ∀ a, H.length ≤ a → U a = .zero
  | .nil, _, _ => rfl
  | .cons (ν := ν) hc h hE, a, ha => by
    show ν 0 * (Demand.unit _ a + _) + _ = _
    rw [Demand.unit_eq_zero_of_length_le hc ha, h.eq_zero a ha, hE.eq_zero a ha]
    cases ν 0 <;> rfl

end

mutual

/-- The reach of a value is unique.
RFC: `\mathsf{reach}_\ell.\mathsf{det}` -/
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

/-- The reach of positions is unique.
RFC: `\mathsf{reach}_{\bar\ell}.\mathsf{det}` -/
theorem Heap.PositionsReach.det {H : Heap} {g : Heap.Annotation} {πs : List Multiplicity}
    {as : List Nat} {U U' : Demand} :
    Heap.PositionsReach H g πs as U → Heap.PositionsReach H g πs as U' → U = U'
  | .nil, .nil => rfl
  | .cons h hs, .cons h' hs' => by rw [h.det h', hs.det hs']

/-- The reach of an environment is unique.
RFC: `\mathsf{reach}_E.\mathsf{det}` -/
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

end Sic.Core
