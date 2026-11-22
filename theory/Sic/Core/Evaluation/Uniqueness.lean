module

public import Sic.Core.Evaluation.Uniqueness.Annotations
public import Sic.Core.Evaluation.Uniqueness.Binders
public import Sic.Core.Evaluation.Uniqueness.Environments
public import Sic.Core.Evaluation.Uniqueness.Need
public import Sic.Core.Evaluation.Uniqueness.Ownership
public import Sic.Core.Evaluation.Uniqueness.Positions
import Sic.Core.Erasure.Ownership.Nested
import Sic.Core.Erasure.Usage.Nested
import Sic.Core.Evaluation.Conservation.Binders
import Sic.Core.Evaluation.Conservation.Demands
import Sic.Core.Evaluation.Conservation.Environments
import Sic.Core.Evaluation.Conservation.Usage

/-!
# Uniqueness

The uniqueness at run time of annex 20 of RFC 36, on the claims of
`Sic/Core/Evaluation/Claims.lean` and the reaches of `Sic/Core/Evaluation/Paths.lean`.

The invariant, `reach_⇓`, follows a run of a term that has an ownership and a usage: its value has
a reach that refers to no address of the heap that its environment does not refer to, and, when the
term is owned alone, each address that its value claims is referred to once at most by its value
and by a frame of the heap, the reach of what the rest of the program still uses, when each address
that the term claims through its environment is referred to once at most by the environment and
the frame.
The frame of a subterm adds, to that of the term, the reach of what the term evaluates or reads
after it, so that a value that a subterm owns alone is reached by nothing that remains.
The uniqueness at run time, `uniq_⇓`, follows: the frame does not refer to the value of a term
owned alone.

The modules of `Sic/Core/Evaluation/Uniqueness/` hold the lemmas that the proof of the invariant
reads, which the RFC does not state.

ADE have no ownership, and no uniqueness at run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-! ## Invariant -/

mutual

/-- `reach_⇓`: a run of a term of the target language that has an ownership and a usage, in a heap
whose annotation is valid, keeps the references: its value has a reach, under an annotation that
extends that of the heap and is valid for the heap of its end, which refers to no address of the
heap that the environment does not refer to, and, when the term is owned alone, each address that
its value claims is referred to once at most by its value and a frame `F` of the heap, when each
address that the term claims through its environment is referred to once at most by the
environment and the frame.
RFC: `\mathsf{reach}_\Downarrow` -/
theorem Eval.reach {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω) (hP : P.Usage)
    {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {M : Target n} {a : Nat}
    {R : List Nat} (h : Eval P ϖ H E M a H' R) {φ ν : MultiplicityVector n} {o : Multiplicity}
    (hM : Target.Ownership Ω φ o M) (hν : Target.Usage ν M) {g : Heap.Annotation}
    (hg : g.Valid Ω H) {U_E : Demand} (hE : Heap.EnvReach H g E ν U_E) {F : Demand}
    (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hc : ∀ b, Heap.EnvClaims H g E φ ν b → F b + U_E b ≠ .omega) :
    ∃ g' U, Heap.Annotation.Extends H g g' ∧ g'.Valid Ω H' ∧ Heap.ValueReach H' g' a U ∧
      (∀ b, b < H.length → U_E b = .zero → U b = .zero) ∧
      (o = .one → ∀ b, Heap.Claims H' g' a b → F b + U b ≠ .omega) :=
  match h with
  | .var (x := x) hx hcx => by
    have hle := hν.var_inv (x := x) rfl
    obtain ⟨U', hU', hE'⟩ := hE.toEnvSum.le hle
    obtain ⟨c', π', ℓ', Ux, hx', hc', hv, rfl⟩ := hE'.var_inv x
      (by simp [MultiplicityVector.update, Sic.Math.Vector.update])
      (fun y hy => by simp [MultiplicityVector.update, Sic.Math.Vector.update, hy]; rfl)
    rw [hx] at hx'
    cases hx'
    rw [hcx] at hc'
    cases hc'
    refine ⟨g, Ux, .refl _ _, hg, hv, fun b _ hb => ?_, fun ho b hb => ?_⟩
    · have h' : U_E b ≤ Demand.unit _ b + Ux b := hU' b
      rw [hb] at h'
      exact (by decide : ∀ u x : Multiplicity, Multiplicity.zero ≤ u + x → x = .zero) _ _ h'
    · have hφ : φ x = .one :=
        Multiplicity.eq_one_of_one_le _ (ho ▸ hM.var_inv rfl)
      have hνx : ν x ≠ .zero := by
        have h' := hle x
        simp only [MultiplicityVector.update, Sic.Math.Vector.update, ↓reduceIte] at h'
        exact (by decide : ∀ y : Multiplicity, y ≤ .one → y ≠ .zero) _ h'
      have h₁ := hc b ⟨x, _, hx, hφ, hνx, .cell hcx hb⟩
      have h₂ : U_E b ≤ Demand.unit _ b + Ux b := hU' b
      exact (by decide : ∀ f e u x : Multiplicity, f + e ≠ .omega → e ≤ u + x →
        f + x ≠ .omega) _ _ _ _ h₁ h₂
  | .const hf hb => by
    obtain ⟨g', U, hgg, hg', hU, hA, hB⟩ := Eval.reach hΩ hP hb
      (.sub (hΩ _ _ _ _ hf) (hM.const_inv rfl)) (hP _ _ _ _ hf) hg .nil hF
      (fun b ⟨x, _⟩ => x.elim0)
    exact ⟨g', U, hgg, hg', hU, fun b hb _ => hA b hb rfl, hB⟩
  | .erased => by
    refine ⟨g, Demand.unit H.length, .refl _ _, hg.concat (fun _ _ _ _ _ _ h => nomatch h),
      .erased List.getElem?_concat_length, fun b hb _ => ?_, fun _ b hb => ?_⟩
    · simp [Demand.unit, Nat.ne_of_lt hb]
    · obtain rfl := hb.erased_inv List.getElem?_concat_length
      rw [hF _ (Nat.le_refl _)]
      simp [Demand.unit] <;> decide
  | .ctor (H' := H₂) (i := i) (Ms := Ms) (as := as) hs => by
    obtain ⟨os, hMs⟩ := hM.ctor_inv rfl
    obtain ⟨ν', hle, hνs⟩ := hν.ctor_inv rfl
    obtain ⟨U', hE', hc', h0'⟩ := hE.sub hle hc
    obtain ⟨g', Us, hgg, hg', hUs, hA, hB⟩ := EvalAll.reach hΩ hP hs hMs hνs hg hE' hF hc'
    have hH₂ : H₂.Extends (H₂ ++ [.ctor i Ms.multiplicities Ms.requirements as]) :=
      List.prefix_append _ _
    have hUs' := hUs.imp fun _ _ h => h.mono hH₂ (.refl _ _)
    have hℓ : ∀ b, H₂.length ≤ b →
        Demand.positions (Ms.multiplicities.map Multiplicity.references) Us b = .zero :=
      fun b hb => Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hUs hb)
    refine ⟨g', _, hgg, hg'.concat (fun _ _ _ _ _ _ h => nomatch h),
      .ctor List.getElem?_concat_length
        (Heap.PositionsReach.of_forall₂ hUs' hs.length), fun b hb hb0 => ?_, fun _ b hb => ?_⟩
    · show Demand.unit _ b + _ = _
      rw [Demand.positions_eq_zero _ _ (hA b hb (h0' b hb0))]
      have : b ≠ H₂.length := Nat.ne_of_lt (Nat.lt_of_lt_of_le hb hs.extends.length_le)
      simp [Demand.unit, this] <;> decide
    · show F b + (Demand.unit _ b + _) ≠ _
      by_cases hbℓ : b = H₂.length
      · subst hbℓ
        rw [hF _ hs.extends.length_le, hℓ _ (Nat.le_refl _)]
        simp [Demand.unit] <;> decide
      · have hu : Demand.unit H₂.length b = .zero := by simp [Demand.unit, hbℓ]
        rw [hu]
        cases hb with
        | self => exact absurd rfl hbℓ
        | state h' | scope _ h' | cell h' =>
          cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
        | ctor h' ha hπ hπ₀ hϱ hb' =>
          cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
          obtain ⟨o', ho', hle'⟩ := hMs.get hϱ
          cases Multiplicity.eq_one_of_one_le _ hle'
          obtain ⟨U'', -, hU''⟩ := hUs.getElem? ha
          have h := hB b _ _ _ ha ho' hπ hπ₀ (hb'.of_extends hH₂ (.refl _ _) (.inl ⟨_, hU''⟩))
          exact (by decide : ∀ f x : Multiplicity, f + x ≠ .omega → f + (.zero + x) ≠ .omega)
            _ _ h
  | .recursor (H₂ := H₂) (ρ := ρ) (ϱ := ϱ) (M := M₁) (Ns := Ns) (a := a₁) hev hr => by
    obtain ⟨o₁, o', _, _, hoM, hoNs, hoo⟩ := hM.recursor_inv rfl
    obtain ⟨ν₁, χ, hle, hν₁, hz, hχ⟩ := hν.recursor_inv rfl
    obtain ⟨U', hE', hc', h0'⟩ := hE.sub hle hc
    obtain ⟨U₁', Uχ, rfl, hE₁', hEχ⟩ := hE'.toEnvSum.split
    obtain ⟨U₁, rfl, hE₁⟩ := hE₁'.unsmul
    obtain ⟨ν₁', U₁s, hν₁', hE₁s, hzero, hc₁⟩ := hν₁.atPosition hz hE₁ hc'
    have hH₁₂ := hev.extends
    obtain ⟨g₂, U_a, hg₁₂, hg₂, hUa, hA₁, hB₁⟩ := Eval.reach hΩ hP hev hoM hν₁' hg hE₁s
      (F := F +ᶜ Uχ) (fun b hb => by
        show F b + Uχ b = _
        rw [hF b hb, hEχ.toEnvReach.eq_zero b hb]
        rfl) hc₁
    have hEχ₂ := hEχ.toEnvReach.mono hH₁₂ hg₁₂
    -- At the multiplicity `0`, the term is data, which evaluates to a constructor, a new value of
    -- an ownership at most `1`.
    have hθz : ρ = .zero → ∃ o₀, o₀ ≤ .one ∧ o₀ * ϱ = o₁ * ϱ := fun hρ0 => ⟨o₁, by
      cases hz hρ0 with
      | erased =>
        cases hev
        cases hr with
        | iota hlook => simp at hlook
      | ctor _ => exact hoM.ctor_le rfl, rfl⟩
    obtain ⟨g₃, U, hg₂₃, hg₃, hU, hA, hB⟩ := EvalRec.reach hΩ hP hr hoNs hχ
      (fun h => (Multiplicity.mul_eq_one _ _ h).2)
      ((by decide : ∀ o ϱ : Multiplicity, o * ϱ * ϱ = o * ϱ) _ _) hθz hg₂ hEχ₂ hUa (F := F)
      (fun b hb => hF b (Nat.le_trans hH₁₂.length_le hb))
      (fun b hb => by
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ hEχ.toEnvReach
        have hχb : Uχ b ≠ .zero := hb₁.reach_ne_zero hEχ.toEnvReach
        have h : F b + (ρ * U₁ b + Uχ b) ≠ .omega := hc' b (hb₁.imp fun x hx =>
          Multiplicity.add_ne_zero_right _ _ hx)
        have hρU : ρ * U₁ b = .zero := (by decide : ∀ f x v : Multiplicity,
          f + (x + v) ≠ .omega → v ≠ .zero → x = .zero) _ _ _ h hχb
        rw [hA₁ b (hEχ.toEnvReach.lt hχb) (hzero b hρU)]
        exact (by decide : ∀ f r x v : Multiplicity, f + (x + v) ≠ .omega → x = .zero →
          f + (r * .zero + v) ≠ .omega) _ _ _ _ h hρU)
      (fun hθ _ b hb => by
        have h : (F b + Uχ b) + U_a b ≠ .omega := hB₁
          (Multiplicity.mul_eq_one _ _ hθ).1 b hb
        exact (by decide : ∀ f c u : Multiplicity, f + c + u ≠ .omega → f + (u + c) ≠ .omega)
          _ _ _ h)
    refine ⟨g₃, U, hg₁₂.trans hH₁₂ hg₂₃, hg₃, hU, fun b hb hb0 => ?_, fun ho => hB
      (Multiplicity.eq_one_of_one_le _ (ho ▸ hoo))⟩
    have h0 : ρ * U₁ b + Uχ b = .zero := h0' b hb0
    have hρU : ρ * U₁ b = .zero :=
      Multiplicity.add_eq_zero_left _ _ h0
    have hχ0 : Uχ b = .zero :=
      Multiplicity.add_eq_zero_right _ _ h0
    refine hA b (Nat.lt_of_lt_of_le hb hH₁₂.length_le) ?_
    rw [hA₁ b hb (hzero b hρU), hχ0]
    cases ρ <;> rfl
  | .obs (H₂ := H₂) (H₃ := H₃) (M := M₁) (ψ := ψ) (ς := ς) (Ms := Ms) (a := a₁) (bs := bs)
      hev hs ho => by
    obtain ⟨o₁, w, os, hoM, hoMs, hw, hς, hoo⟩ := hM.obs_inv rfl
    obtain ⟨ν₁, ν₂, hle, hν₁, hν₂⟩ := hν.obs_inv rfl
    obtain ⟨U', hE', hc', h0'⟩ := hE.sub hle hc
    obtain ⟨U₁, U₂, rfl, hE₁, hE₂⟩ := hE'.toEnvSum.split
    have hH₁₂ := hev.extends
    have hH₂₃ := hs.extends
    obtain ⟨g₂, U_a, hg₁₂, hg₂, hUa, hA₁, hB₁⟩ := Eval.reach hΩ hP hev hoM hν₁ hg
      hE₁.toEnvReach (F := F +ᶜ U₂) (fun b hb => by
        show F b + U₂ b = _
        rw [hF b hb, hE₂.toEnvReach.eq_zero b hb]
        rfl)
      (fun b hb => by
        have h : F b + (U₁ b + U₂ b) ≠ .omega := hc' b (hb.imp fun x hx =>
          Multiplicity.add_ne_zero_left _ _ hx)
        exact (by decide : ∀ f u v : Multiplicity, f + (u + v) ≠ .omega → f + v + u ≠ .omega)
          _ _ _ h)
    obtain ⟨g₃, Us, hg₂₃, hg₃, hUs, hA₂, hB₂⟩ := EvalAll.reach hΩ hP hs hoMs hν₂ hg₂
      (hE₂.toEnvReach.mono hH₁₂ hg₁₂) (F := F +ᶜ U_a) (fun b hb => by
        show F b + U_a b = _
        rw [hF b (Nat.le_trans hH₁₂.length_le hb), hUa.eq_zero b hb]
        rfl)
      (fun b hb => by
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ hE₂.toEnvReach
        have h2 : U₂ b ≠ .zero := hb₁.reach_ne_zero hE₂.toEnvReach
        have h : F b + (U₁ b + U₂ b) ≠ .omega := hc' b (hb₁.imp fun x hx =>
          Multiplicity.add_ne_zero_right _ _ hx)
        have h1 : U₁ b = .zero := (by decide : ∀ f x v : Multiplicity,
          f + (x + v) ≠ .omega → v ≠ .zero → x = .zero) _ _ _ h h2
        show (F b + U_a b) + U₂ b ≠ _
        rw [hA₁ b (hE₂.toEnvReach.lt h2) h1]
        exact (by decide : ∀ f x v : Multiplicity, f + (x + v) ≠ .omega → x = .zero →
          f + .zero + v ≠ .omega) _ _ _ h h1)
    have hUa₃ := hUa.mono hH₂₃ hg₂₃
    obtain ⟨g₄, U, hg₃₄, hg₄, hU, hA, hB⟩ := EvalObs.reach hΩ hP ho hς hw
      (fun k ϱ hk => hoMs.get hk) (hoMs.length.trans hs.length) hg₃ hUa₃ hUs (F := F)
      (fun b hb => hF b (Nat.le_trans (hH₁₂.trans hH₂₃).length_le hb))
      (fun ho₁ b hb => by
        have hb₂ := hb.of_extends hH₂₃ hg₂₃ (.inl ⟨_, hUa⟩)
        have h : (F b + U₂ b) + U_a b ≠ .omega := hB₁ ho₁ b hb₂
        have ha0 : U_a b ≠ .zero := hb₂.reach_ne_zero.1 _ hUa
        have h2 : U₂ b = .zero := (by decide : ∀ f v u : Multiplicity,
          f + v + u ≠ .omega → u ≠ .zero → v = .zero) _ _ _ h ha0
        rw [Demand.positions_eq_zero _ _ (hA₂ b (hUa.lt ha0) h2)]
        exact (by decide : ∀ f v u : Multiplicity, f + v + u ≠ .omega →
          f + (u + .zero) ≠ .omega) _ _ _ h)
      (fun b k b' π hk hok hπ hπ₀ hb => by
        have h : (F b + U_a b) + _ ≠ .omega := hB₂ b k b' π hk hok hπ hπ₀ hb
        exact (by decide : ∀ f u x : Multiplicity, f + u + x ≠ .omega → f + (u + x) ≠ .omega)
          _ _ _ h)
    refine ⟨g₄, U, (hg₁₂.trans hH₁₂ hg₂₃).trans (hH₁₂.trans hH₂₃) hg₃₄, hg₄, hU,
      fun b hb hb0 => ?_, fun ho' => hB
        (Multiplicity.eq_one_of_one_le _ (ho' ▸ hoo))⟩
    have h0 : U₁ b + U₂ b = .zero := h0' b hb0
    have h1 : U₁ b = .zero :=
      Multiplicity.add_eq_zero_left _ _ h0
    have h2 : U₂ b = .zero :=
      Multiplicity.add_eq_zero_right _ _ h0
    refine hA b (Nat.lt_of_lt_of_le hb (hH₁₂.trans hH₂₃).length_le) ?_
    rw [hA₁ b hb h1, Demand.positions_eq_zero _ _
      (hA₂ b (Nat.lt_of_lt_of_le hb hH₁₂.length_le) h2)]
    rfl
  | .corec (H' := H₂) (Ms := Ms) (Ps := Ps) (as := as) hs => by
    obtain ⟨os, hMs, hPs⟩ := hM.corec_inv rfl
    obtain ⟨ν₁, δ, hle, hνs, hδ⟩ := hν.corec_inv rfl
    obtain ⟨U', hE', hc', h0'⟩ := hE.sub hle hc
    obtain ⟨U₁, Uδ, rfl, hE₁, hEδ⟩ := hE'.toEnvSum.split
    have hH₁₂ := hs.extends
    obtain ⟨g₂, Us, hg₁₂, hg₂, hUs, hA, hB⟩ := EvalAll.reach hΩ hP hs hMs hνs hg hE₁.toEnvReach
      (F := F +ᶜ Uδ) (fun b hb => by
        show F b + Uδ b = _
        rw [hF b hb, hEδ.toEnvReach.eq_zero b hb]
        rfl)
      (fun b hb => by
        have h : F b + (U₁ b + Uδ b) ≠ .omega := hc' b (hb.imp fun x hx =>
          Multiplicity.add_ne_zero_left _ _ hx)
        exact (by decide : ∀ f u v : Multiplicity, f + (u + v) ≠ .omega → f + v + u ≠ .omega)
          _ _ _ h)
    let v : Value := .corec n E Ps Ms.multiplicities Ms.requirements as
    have hH₂ : H₂.Extends (H₂ ++ [v]) := List.prefix_append _ _
    have hgs := Heap.Annotation.set_extends H₂ g₂ n φ δ
    have hUs' := hUs.imp fun _ _ h => h.mono hH₂ hgs
    have hEδ' : Heap.EnvReach (H₂ ++ [v]) (g₂.set H₂.length n φ δ) E
        ((g₂.set H₂.length n φ δ).usage H₂.length n) Uδ := by
      rw [(Heap.Annotation.set_self g₂ H₂.length n φ δ).2]
      exact hEδ.toEnvReach.mono (hH₁₂.trans hH₂) (hg₁₂.trans hH₁₂ hgs)
    have hℓ : ∀ b, H₂.length ≤ b →
        Demand.positions (Ms.multiplicities.map Multiplicity.references) Us b = .zero :=
      fun b hb => Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hUs hb)
    refine ⟨g₂.set H₂.length n φ δ, _, hg₁₂.trans hH₁₂ hgs, hg₂.concat_corec hPs hδ,
      .corec List.getElem?_concat_length hEδ' (Heap.PositionsReach.of_forall₂ hUs' hs.length),
      fun b hb hb0 => ?_, fun _ b hb => ?_⟩
    · have h0 : U₁ b + Uδ b = .zero := h0' b hb0
      have h1 : U₁ b = .zero :=
        Multiplicity.add_eq_zero_left _ _ h0
      have h2 : Uδ b = .zero :=
        Multiplicity.add_eq_zero_right _ _ h0
      show Demand.unit _ b + (Uδ b + _) = _
      rw [Demand.positions_eq_zero _ _ (hA b hb h1), h2]
      have : b ≠ H₂.length := Nat.ne_of_lt (Nat.lt_of_lt_of_le hb hH₁₂.length_le)
      simp [Demand.unit, this] <;> decide
    · show F b + (Demand.unit _ b + (Uδ b + _)) ≠ _
      by_cases hbℓ : b = H₂.length
      · subst hbℓ
        rw [hF _ hH₁₂.length_le, hℓ _ (Nat.le_refl _),
          hEδ.toEnvReach.eq_zero _ hH₁₂.length_le]
        simp [Demand.unit] <;> decide
      · have hu : Demand.unit H₂.length b = .zero := by simp [Demand.unit, hbℓ]
        rw [hu]
        cases hb with
        | self => exact absurd rfl hbℓ
        | ctor h' | cell h' =>
          cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
        | state h' ha hπ hπ₀ hϱ hb' =>
          cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
          obtain ⟨o', ho', hle'⟩ := hMs.get hϱ
          cases Multiplicity.eq_one_of_one_le _ hle'
          obtain ⟨U'', -, hU''⟩ := hUs.getElem? ha
          have h : (F b + Uδ b) + _ ≠ .omega :=
            hB b _ _ _ ha ho' hπ hπ₀ (hb'.of_extends hH₂ hgs (.inl ⟨_, hU''⟩))
          exact (by decide : ∀ f d x : Multiplicity, f + d + x ≠ .omega →
            f + (.zero + (d + x)) ≠ .omega) _ _ _ h
        | scope x h' hcx hδx hφx hb' =>
          cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
          rw [(Heap.Annotation.set_self g₂ H₂.length n φ δ).2] at hδx
          rw [(Heap.Annotation.set_self g₂ H₂.length n φ δ).1] at hφx
          have hb₁ : Heap.EnvClaims H g E φ δ b := ⟨x, _, hcx, hφx, hδx,
            hb'.of_extends (hH₁₂.trans hH₂) (hg₁₂.trans hH₁₂ hgs)
              (.inr (hEδ.toEnvReach.get x hcx))⟩
          have hd : Uδ b ≠ .zero := hb₁.reach_ne_zero hEδ.toEnvReach
          have h : F b + (U₁ b + Uδ b) ≠ .omega := hc' b (hb₁.imp fun x hx =>
            Multiplicity.add_ne_zero_right _ _ hx)
          have h1 : U₁ b = .zero := (by decide : ∀ f x v : Multiplicity,
            f + (x + v) ≠ .omega → v ≠ .zero → x = .zero) _ _ _ h hd
          rw [Demand.positions_eq_zero _ _ (hA b (hEδ.toEnvReach.lt hd) h1)]
          exact (by decide : ∀ f x v : Multiplicity, f + (x + v) ≠ .omega → x = .zero →
            f + (.zero + (v + .zero)) ≠ .omega) _ _ _ h h1
termination_by structural h

/-- The invariant of the evaluation of terms: their values have reaches, which refer to no address
of the heap that the environment does not refer to, and each address that a value of a term owned
alone, at a position of a multiplicity other than `0`, claims is referred to once at most by the
values and the frame. -/
theorem EvalAll.reach {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω) (hP : P.Usage)
    {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n} {as : List Nat}
    {R : List Nat} (h : EvalAll P ϖ H E Ms as H' R) {φ ν : MultiplicityVector n}
    {os : List Multiplicity} (hMs : Targets.Ownership Ω φ os Ms) (hν : Targets.Usage ν Ms)
    {g : Heap.Annotation} (hg : g.Valid Ω H) {U_E : Demand} (hE : Heap.EnvReach H g E ν U_E)
    {F : Demand} (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hc : ∀ b, Heap.EnvClaims H g E φ ν b → F b + U_E b ≠ .omega) :
    ∃ g' Us, Heap.Annotation.Extends H g g' ∧ g'.Valid Ω H' ∧
      List.Pointwise (Heap.ValueReach H' g') as Us ∧
      (∀ b, b < H.length → U_E b = .zero → ∀ U ∈ Us, U b = .zero) ∧
      ∀ (b k a : Nat) (π : Multiplicity), as[k]? = some a → os[k]? = some Multiplicity.one →
        Ms.multiplicities[k]? = some π → π ≠ Multiplicity.zero → Heap.Claims H' g' a b →
        F b + Demand.positions (Ms.multiplicities.map Multiplicity.references) Us b ≠ .omega :=
  match h with
  | .nil => ⟨g, [], .refl _ _, hg, .nil, fun _ _ _ _ h => by simp at h,
      fun _ _ _ _ h => by simp at h⟩
  | .cons (H₂ := H₂) (M := M) (Ms := Ms') (a := a) (as := as') (π := π) (ϱ := ϱ) hev hs => by
    cases hMs with
    | cons hoM hϱ hoMs =>
    cases hν with
    | cons hν₁ hz hν₂ =>
    rename_i o os' ν₁ ν₂
    obtain ⟨U₁', U₂, rfl, hE₁', hE₂⟩ := hE.toEnvSum.split
    obtain ⟨U₁, rfl, hE₁⟩ := hE₁'.unsmul
    obtain ⟨ν₁', U₁s, hν₁', hE₁s, hzero, hc₁⟩ := hν₁.atPosition hz hE₁ hc
    have hH₁₂ := hev.extends
    obtain ⟨g₂, U_a, hg₁₂, hg₂, hUa, hA₁, hB₁⟩ := Eval.reach hΩ hP hev hoM hν₁' hg hE₁s
      (F := F +ᶜ U₂) (fun b hb => by
        show F b + U₂ b = _
        rw [hF b hb, hE₂.toEnvReach.eq_zero b hb]
        rfl) hc₁
    obtain ⟨g₃, Us, hg₂₃, hg₃, hUs, hA₂, hB₂⟩ := EvalAll.reach hΩ hP hs hoMs hν₂ hg₂
      (hE₂.toEnvReach.mono hH₁₂ hg₁₂) (F := F +ᶜ π.references ·ᶜ U_a) (fun b hb => by
        show F b + π.references * U_a b = _
        rw [hF b (Nat.le_trans hH₁₂.length_le hb), hUa.eq_zero b hb]
        cases π <;> rfl)
      (fun b hb => by
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ hE₂.toEnvReach
        have h2 : U₂ b ≠ .zero := hb₁.reach_ne_zero hE₂.toEnvReach
        have h : F b + (π * U₁ b + U₂ b) ≠ .omega := hc b (hb₁.imp fun x hx =>
          Multiplicity.add_ne_zero_right _ _ hx)
        have h1 : π * U₁ b = .zero := (by decide : ∀ f x v : Multiplicity,
          f + (x + v) ≠ .omega → v ≠ .zero → x = .zero) _ _ _ h h2
        show (F b + π.references * U_a b) + U₂ b ≠ _
        rw [hA₁ b (hE₂.toEnvReach.lt h2) (hzero b h1)]
        exact (by decide : ∀ f r x v : Multiplicity, f + (x + v) ≠ .omega → x = .zero →
          f + r * .zero + v ≠ .omega) _ _ _ _ h h1)
    refine ⟨g₃, U_a :: Us, hg₁₂.trans hH₁₂ hg₂₃, hg₃, .cons (hUa.mono hs.extends hg₂₃) hUs,
      fun b hb hb0 U hU => ?_, fun b k a' π' ha ho hπ' hπ'₀ hcl => ?_⟩
    · have h0 : π * U₁ b + U₂ b = .zero := hb0
      have h1 : π * U₁ b = .zero :=
        Multiplicity.add_eq_zero_left _ _ h0
      have h2 : U₂ b = .zero :=
        Multiplicity.add_eq_zero_right _ _ h0
      rcases List.mem_cons.1 hU with rfl | hU
      · exact hA₁ b hb (hzero b h1)
      · exact hA₂ b (Nat.lt_of_lt_of_le hb hH₁₂.length_le) h2 U hU
    · show F b + (π.references * U_a b +
        Demand.positions (Ms'.multiplicities.map Multiplicity.references) Us b) ≠ _
      cases k with
      | zero =>
        cases ha
        cases ho
        cases hπ'
        have hcl₂ := hcl.of_extends hs.extends hg₂₃ (.inl ⟨_, hUa⟩)
        have h : (F b + U₂ b) + U_a b ≠ .omega := hB₁ rfl b hcl₂
        have ha0 : U_a b ≠ .zero := hcl₂.reach_ne_zero.1 _ hUa
        have h2 : U₂ b = .zero := (by decide : ∀ f v u : Multiplicity,
          f + v + u ≠ .omega → u ≠ .zero → v = .zero) _ _ _ h ha0
        rw [Demand.positions_eq_zero _ _ (hA₂ b (hUa.lt ha0) h2)]
        exact (by decide : ∀ f v u π : Multiplicity, π ≠ .zero → f + v + u ≠ .omega →
          f + (π.references * u + .zero) ≠ .omega) _ _ _ _ hπ'₀ h
      | succ k =>
        have h : (F b + π.references * U_a b) + _ ≠ .omega :=
          hB₂ b k a' π' (by simpa using ha) (by simpa using ho)
            (by simpa [Targets.multiplicities] using hπ') hπ'₀ hcl
        exact (by decide : ∀ f x y : Multiplicity, f + x + y ≠ .omega → f + (x + y) ≠ .omega)
          _ _ _ h
termination_by structural h

/-- The invariant of the elimination of a value by a recursor, whose branches see the value at the
ownership `θ` at each level of the recursion. -/
theorem EvalRec.reach {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω) (hP : P.Usage)
    {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {ρ ϱ : Multiplicity}
    {Ns : TargetBranches n} {a v : Nat} {R : List Nat} (h : EvalRec P ϖ H E ρ ϱ Ns a v H' R)
    {φ χ : MultiplicityVector n} {θ o' : Multiplicity}
    {ς χ' : Multiplicity} (hNs : TargetBranches.Ownership Ω φ ρ θ o' ς χ' Ns)
    (hχ : TargetBranches.Usage ρ χ Ns) (hθ : θ = .one → ϱ = .one) (hθϱ : θ * ϱ = θ)
    (hθz : ρ = .zero → ∃ o₀, o₀ ≤ .one ∧ o₀ * ϱ = θ) {g : Heap.Annotation} (hg : g.Valid Ω H) {U_χ U_a : Demand}
    (hE : Heap.EnvReach H g E χ U_χ) (ha : Heap.ValueReach H g a U_a) {F : Demand}
    (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hc : ∀ b, Heap.EnvClaims H g E φ χ b → F b + (ρ.references * U_a b + U_χ b) ≠ .omega)
    (hca : θ = .one → ρ ≠ .zero → ∀ b, Heap.Claims H g a b → F b + (U_a b + U_χ b) ≠ .omega) :
    ∃ g' U, Heap.Annotation.Extends H g g' ∧ g'.Valid Ω H' ∧ Heap.ValueReach H' g' v U ∧
      (∀ b, b < H.length → ρ.references * U_a b + U_χ b = .zero → U b = .zero) ∧
      (o' = .one → ∀ b, Heap.Claims H' g' v b → F b + U b ≠ .omega) :=
  match h with
  | .iota (H₂ := H₂) (i := i) (πs₀ := πs₀) (ϱs₀ := ϱs₀) (as := as) (a' := a') (b := b')
      (πs := πs) (κs := κs) (πs' := πs') (ks := ks) (N := N) (rs := rs) hlook hN hla hπ hκ hϱ
      hres hv => by
    -- The reach of the constructor, the sum of those of its fields.
    obtain ⟨Us, hUs, rfl, hl₀⟩ := ha.ctor_inv hlook
    obtain ⟨hN_own, hks⟩ := hNs.get _ hN
    obtain ⟨δ, hNu, hχle, hk, hσ⟩ := hχ.get _ hN
    -- The reads of the scope by the branch and by its recursions.
    obtain ⟨U', hU', hE'⟩ := hE.toEnvSum.le hχle
    obtain ⟨U_δ, Uχs, rfl, hEδ, hEs⟩ := hE'.split
    obtain ⟨Uχ', rfl, hEχ'⟩ := hEs.unsmul
    obtain rfl := hE.det hEχ'.toEnvReach
    have hχpt : ∀ b, U_χ b ≤ U_δ b +
        Multiplicity.sum (fun j => πs' j * (ks j).factor) * U_χ b := hU'
    have hcomp := Multiplicity.computed_ofFn ks πs'
    have hlr := hres.length
    have hlU : as.length = Us.length := hUs.length
    have hlen : (List.ofFn ks).length = (List.ofFn πs').length := by simp
    -- The checks of the evaluation, on the lists.
    have hπL : ∀ (l : Nat) (π₀ π : Multiplicity), πs₀[l]? = some π₀ →
        (List.ofFn πs)[l]? = some π →
        ρ * π₀ ≤ π + ρ * recursionsAt (List.ofFn ks) (List.ofFn πs') l := fun l π₀ π h₀ h₁ => by
      rw [List.getElem?_ofFn] at h₁
      split at h₁
      · rename_i hl
        cases h₁
        obtain ⟨π₀', h₀', hle⟩ := hπ ⟨l, hl⟩
        rw [h₀] at h₀'
        cases h₀'
        exact hle
      · cases h₁
    have hkL : ∀ (j : Nat) (k : RecursiveResult) (π : Multiplicity), (List.ofFn ks)[j]? = some k →
        k ≠ .erased → (List.ofFn πs')[j]? = some π → π ≠ .zero := fun j k π h₁ hke h₂ => by
      by_cases hj : j < b'
      · simp only [List.getElem?_ofFn, hj, ↓reduceDIte, Option.some.injEq] at h₁ h₂
        subst h₂
        exact hk ⟨j, hj⟩ (by rw [h₁]; exact hke)
      · simp [hj] at h₁
    have hrecL : ∀ (j : Nat) (k : RecursiveResult) (l : Nat), (List.ofFn ks)[j]? = some k →
        k.fieldPosition = some l → l < Us.length :=
      fun j k l h hk => hlU ▸ hres.lt j k l h hk
    -- A field on which a result recurses is referred to by the value, unless `ρ` is `0`.
    have hrec0 : ∀ b, ρ.references * (Demand.unit a b +
        Demand.positions (πs₀.map Multiplicity.references) Us b) = .zero →
        ∀ (j : Nat) (k : RecursiveResult) (l : Nat), (List.ofFn ks)[j]? = some k →
        k.fieldPosition = some l → k.factor ≠ .zero →
        ρ.references * Us.getD l 𝟘ᵛ b = .zero := fun b h0 j k l hj hkl hf => by
      by_cases hρ : ρ = .zero
      · subst hρ
        exact (by decide : ∀ x : Multiplicity, Multiplicity.zero.references * x = .zero) _
      · have hl := hrecL j k l hj hkl
        have hp0 : Demand.positions (πs₀.map Multiplicity.references) Us b = .zero :=
          (by decide : ∀ ρ u p : Multiplicity, ρ ≠ .zero → ρ.references * (u + p) = .zero →
            p = .zero) _ _ _ hρ h0
        obtain ⟨π₀, hπ₀⟩ : ∃ π₀, πs₀[l]? = some π₀ :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hU := List.getElem?_eq_getElem hl
        have ht := Demand.positions_get_zero _ _ hp0 (j := l)
          (by rw [List.getElem?_map, hπ₀]; rfl) hU
        obtain ⟨π, hπl⟩ : ∃ π, (List.ofFn πs)[l]? = some π :=
          ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
        obtain ⟨π', hπ'⟩ : ∃ π', (List.ofFn πs')[j]? = some π' :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.1 hj).1
            simpa using this)⟩
        have hke : k ≠ .erased := fun he => by subst he; exact hf rfl
        have hne := recursionsAt_ne_zero hkl
          (Multiplicity.mul_ne_zero _ _ (hkL j k π' hj hke hπ') hf) hj hπ'
        rw [List.getD_eq_getElem?_getD, hU]
        exact (by decide : ∀ ρ π₀ π x u : Multiplicity, ρ ≠ .zero → x ≠ .zero →
          ρ * π₀ ≤ π + ρ * x → π₀.references * u = .zero → ρ.references * u = .zero)
          _ _ _ _ _ hρ hne (hπL l π₀ π hπ₀ hπl) ht
    -- The branch reads no field that the value does not refer to.
    have hP0 : ∀ b, ρ.references * (Demand.unit a b +
        Demand.positions (πs₀.map Multiplicity.references) Us b) = .zero →
        Demand.positions (List.ofFn πs) Us b = .zero := fun b h0 =>
      Demand.positions_of_zero _ _ fun l π U hπl hU => by
        obtain ⟨π₀, hπ₀⟩ : ∃ π₀, πs₀[l]? = some π₀ :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.1 hU).1
            omega)⟩
        have hle := hπL l π₀ π hπ₀ hπl
        by_cases hρ : ρ = .zero
        · subst hρ
          exact (by decide : ∀ π₀ π x u : Multiplicity,
            Multiplicity.zero * π₀ ≤ π + Multiplicity.zero * x → π * u = .zero) _ _ _ _ hle
        · have hp0 : Demand.positions (πs₀.map Multiplicity.references) Us b = .zero :=
            (by decide : ∀ ρ u p : Multiplicity, ρ ≠ .zero → ρ.references * (u + p) = .zero →
              p = .zero) _ _ _ hρ h0
          have ht := Demand.positions_get_zero _ _ hp0 (j := l)
            (by rw [List.getElem?_map, hπ₀]; rfl) hU
          exact (by decide : ∀ ρ π₀ π x u : Multiplicity, ρ * π₀ ≤ π + ρ * x → ρ ≠ .zero →
            π₀.references * u = .zero → π * u = .zero) _ _ _ _ _ hle hρ ht
    -- A field that the value owns alone and holds once: the frame and the scope do not refer to
    -- what it claims, and the branch and its recursions use it once.
    have hfield : ∀ (b l a_l : Nat), θ = .one → ρ = .one → as[l]? = some a_l →
        πs₀[l]? = some Multiplicity.one → ϱs₀[l]? = some Multiplicity.one →
        Heap.Claims H g a_l b →
        F b = .zero ∧ U_δ b = .zero ∧ U_χ b = .zero ∧ b < H.length ∧
        (∃ U_l, Us[l]? = some U_l ∧ U_l b ≠ .zero) ∧
        Multiplicity.one ≤ Demand.positions (List.ofFn πs) Us b +
          Demand.recursions (List.ofFn ks) (List.ofFn πs') Us b ∧
        Demand.recursions (List.ofFn ks) (List.ofFn πs') Us b ≤
          Demand.need ρ Us U_χ (List.ofFn ks) b := fun b l a_l hθ' hρ hal hπ₀ hϱ₀ hb => by
      have hρ0 : ρ ≠ .zero := by rw [hρ]; decide
      have h : F b + ((Demand.unit a b +
          Demand.positions (πs₀.map Multiplicity.references) Us b) + U_χ b) ≠ .omega :=
        hca hθ' hρ0 b (.ctor hlook hal hπ₀ (by decide) hϱ₀ hb)
      obtain ⟨U_l, hUl, hUal⟩ := hUs.getElem? hal
      have hul : U_l b ≠ .zero := hb.reach_ne_zero.1 _ hUal
      have hT0 : Demand.positions (πs₀.map Multiplicity.references) Us b ≠ .zero :=
        Demand.positions_ne_zero _ _ (by rw [List.getElem?_map, hπ₀]; rfl) hUl
          ((by decide : ∀ u : Multiplicity, u ≠ .zero →
            Multiplicity.one.references * u ≠ .zero) _ hul)
      have hTω : Demand.positions (πs₀.map Multiplicity.references) Us b ≠ .omega :=
        (by decide : ∀ f u t c : Multiplicity, f + ((u + t) + c) ≠ .omega → t ≠ .omega)
          _ _ _ _ h
      have hL := Demand.positions_eq_references πs₀ Us (by omega) hπ₀ hUl hul hTω
      have hχ0 : U_χ b = .zero := (by decide : ∀ f u t c : Multiplicity,
        f + ((u + t) + c) ≠ .omega → t ≠ .zero → c = .zero) _ _ _ _ h hT0
      have hf0 : F b = .zero := (by decide : ∀ f u t c : Multiplicity,
        f + ((u + t) + c) ≠ .omega → t ≠ .zero → f = .zero) _ _ _ _ h hT0
      have hδ0 : U_δ b = .zero := (by decide : ∀ c d s : Multiplicity, c ≤ d + s * c →
        c = .zero → d = .zero) _ _ _ (hχpt b) hχ0
      have hQ3 := Demand.positions_le_add ρ πs₀ (List.ofFn πs)
        ((List.range Us.length).map (recursionsAt (List.ofFn ks) (List.ofFn πs'))) Us
        (by omega) (by simp; omega) (by simp)
        (fun l π₀ π r h₀ h₁ h₂ => by
          by_cases hl : l < Us.length
          · rw [List.getElem?_map, List.getElem?_range hl] at h₂
            cases h₂
            exact hπL l π₀ π h₀ h₁
          · rw [List.getElem?_eq_none (by simpa using hl)] at h₂
            cases h₂) b
      rw [← Demand.recursions_eq (List.ofFn ks) (List.ofFn πs') Us hlen hrecL] at hQ3
      have hQ3' : ρ * Demand.positions πs₀ Us b ≤ Demand.positions (List.ofFn πs) Us b +
          ρ * Demand.recursions (List.ofFn ks) (List.ofFn πs') Us b := hQ3
      rw [hL, hρ] at hQ3'
      exact ⟨hf0, hδ0, hχ0, hUal.lt hul, ⟨U_l, hUl, hul⟩,
        (by decide : ∀ t p r : Multiplicity, t ≠ .zero → t ≠ .omega →
          Multiplicity.one * t ≤ p + Multiplicity.one * r → Multiplicity.one ≤ p + r)
          _ _ _ hT0 hTω hQ3',
        Demand.recursions_le_need hρ hχ0 hlen hkL⟩
    -- The recursive results, in the frame of what the branch reads after them.
    have hH₁₂ := hres.extends
    obtain ⟨g₂, Vs, hg₁₂, hg₂, hVs, hA_R, hB_R⟩ := EvalResults.reach hΩ hP hres hNs hχ hθ hθϱ hθz
      (κs := List.ofFn κs)
      (fun j l σ a_l hj hal => by
        have hjlt : j < b' := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa using this
        have hkj : ks ⟨j, hjlt⟩ = .nested l σ := by simpa [List.getElem?_ofFn, hjlt] using hj
        have hlt : l < a' := hla ▸ (List.getElem?_eq_some_iff.1 hal).1
        obtain ⟨huni, hreq⟩ := hks ⟨j, hjlt⟩ ⟨l, hlt⟩ σ hkj
        exact ⟨κs ⟨l, hlt⟩, by simp [hlt], hσ ⟨j, hjlt⟩ l σ hkj, huni, hreq⟩)
      hg hE hUs (F := F +ᶜ (U_δ +ᶜ Demand.positions (List.ofFn πs) Us))
      (fun b hb => by
        show F b + (U_δ b + Demand.positions (List.ofFn πs) Us b) = _
        rw [hF b hb, hEδ.toEnvReach.eq_zero b hb,
          Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hUs hb)]
        rfl)
      (fun j k hj hf b hb => by
        have hχb : U_χ b ≠ .zero := hb.reach_ne_zero hE
        have h : F b + (ρ.references * (Demand.unit a b +
            Demand.positions (πs₀.map Multiplicity.references) Us b) + U_χ b) ≠ .omega := hc b hb
        have hra := (by decide : ∀ f x c : Multiplicity, f + (x + c) ≠ .omega → c ≠ .zero →
          x = .zero) _ _ _ h hχb
        have hs0 := Demand.computed_ne_zero hlen hj hf hkL
        have hn := Demand.computed_mul_le_need (ρ := ρ) (Us := Us) (Uχ := U_χ) (b := b) hlen
          (hrec0 b hra) hkL
        rw [hcomp] at hs0 hn
        show (F b + (U_δ b + Demand.positions (List.ofFn πs) Us b)) + _ ≠ _
        rw [hP0 b hra]
        have hfc : F b + U_χ b ≠ .omega := (by decide : ∀ f x c : Multiplicity,
          f + (x + c) ≠ .omega → x = .zero → f + c ≠ .omega) _ _ _ h hra
        exact (by decide : ∀ f c d s n : Multiplicity, f + c ≠ .omega → c ≠ .zero →
          c ≤ d + s * c → s ≠ .zero → s * c ≤ n → (f + (d + .zero)) + n ≠ .omega)
          _ _ _ _ _ hfc hχb (hχpt b) hs0 hn)
      (fun hθ' hρ j l a_l hj hal b hb => by
        have hjlt : j < b' := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa using this
        have hkj : ks ⟨j, hjlt⟩ = .field l := by
          simpa [List.getElem?_ofFn, hjlt] using hj
        obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hϱ ⟨j, hjlt⟩ l hkj
        rw [hθ hθ'] at hle
        obtain ⟨rfl, hρ1, rfl⟩ := (by decide : ∀ ϱ₀ ρ π₀ : Multiplicity,
          Multiplicity.one ≤ ϱ₀ * (ρ * π₀) → ϱ₀ = .one ∧ ρ = .one ∧ π₀ = .one) _ _ _ hle
        obtain ⟨hf0, hδ0, -, -, -, h1, h4⟩ := hfield b l a_l hθ' hρ1 hal hπ₀ hϱ₀ hb
        show (F b + (U_δ b + Demand.positions (List.ofFn πs) Us b)) + _ ≠ _
        rw [hf0, hδ0]
        exact (by decide : ∀ p r n : Multiplicity, Multiplicity.one ≤ p + r → r ≤ n →
          (.zero + (.zero + p)) + n ≠ .omega) _ _ _ h1 h4)
      (fun j l σ a_l κ hj hκl hθκ hfρ hal b hb => by
        have hlt : l < a' := hla ▸ (List.getElem?_eq_some_iff.1 hal).1
        have hκeq : κs ⟨l, hlt⟩ = κ := by simpa [List.getElem?_ofFn, hlt] using hκl
        obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hκle⟩ := hκ ⟨l, hlt⟩
        rw [hκeq] at hκle
        obtain ⟨hθ', rfl, hρ1, rfl⟩ := (by decide : ∀ θ κ ϱ₀ ρ π₀ : Multiplicity,
          θ * κ = .one → κ ≤ ϱ₀ * (ρ * π₀) → θ = .one ∧ ϱ₀ = .one ∧ ρ = .one ∧ π₀ = .one)
          _ _ _ _ _ hθκ hκle
        obtain ⟨hf0, hδ0, -, -, -, h1, h4⟩ := hfield b l a_l hθ' hρ1 hal hπ₀ hϱ₀ hb
        show (F b + (U_δ b + Demand.positions (List.ofFn πs) Us b)) + _ ≠ _
        rw [hf0, hδ0]
        exact (by decide : ∀ p r n : Multiplicity, Multiplicity.one ≤ p + r → r ≤ n →
          (.zero + (.zero + p)) + n ≠ .omega) _ _ _ h1 h4)
    -- The cells of the branch and the reach of its environment.
    have hH₂' : H₂.Extends (H₂.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (as ++ rs)) :=
      List.prefix_append _ _
    have hgr := Heap.Annotation.Extends.refl H₂ g₂
    have hlrs : rs.length = b' := hlr.1.trans (by simp)
    obtain ⟨C, hEN, -, hC0, hCc⟩ := Heap.EnvSum.bindBranch ϖ πs πs'
      (hEδ.toEnvReach.mono (hH₁₂.trans hH₂') hg₁₂).toEnvSum
      (hUs.imp fun _ _ h => h.mono (hH₁₂.trans hH₂') hg₁₂) (hVs.imp fun _ _ h => h.mono hH₂' hgr)
      hla hlrs
    have hlen₂ : (as ++ rs).length = a' + b' := by simp [hla, hlrs]
    have hUs0 : ∀ b, H.length ≤ b → Demand.positions (List.ofFn πs) Us b = .zero := fun b hb =>
      Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hUs hb)
    have hVs0 : ∀ b, H₂.length ≤ b → Demand.positions (List.ofFn πs') Vs b = .zero := fun b hb =>
      Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hVs hb)
    have hcell : ∀ (j : Nat) (π : Multiplicity) (a₀ : Nat),
        (List.ofFn πs ++ List.ofFn πs')[j]? = some π → (as ++ rs)[j]? = some a₀ →
        (H₂.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (as ++ rs))[H₂.length + j]? =
          some (.cell (ϖ * π) a₀) := fun j π a₀ h₁ h₂ =>
      Heap.bind_getElem? H₂ _ _ j _ _ (by rw [List.getElem?_map, h₁]; rfl) h₂
    -- A new cell that the branch owns alone is read once, and nothing else refers to it.
    have hnew : ∀ (j : Nat), (List.ofFn πs ++ List.ofFn πs')[j]? = some Multiplicity.one →
        F (H₂.length + j) + (U_δ (H₂.length + j) + C (H₂.length + j) +
          (Demand.positions (List.ofFn πs) Us (H₂.length + j) +
            Demand.positions (List.ofFn πs') Vs (H₂.length + j))) ≠ .omega := fun j hj => by
      have hle : H.length ≤ H₂.length + j := Nat.le_trans hH₁₂.length_le (Nat.le_add_right _ _)
      rw [hF _ hle, hEδ.toEnvReach.eq_zero _ hle, hCc j _ hj, hUs0 _ hle,
        hVs0 _ (Nat.le_add_right _ _)]
      decide
    -- The branch.
    obtain ⟨g₃, U, hg₂₃, hg₃, hU, hA_N, hB_N⟩ := Eval.reach hΩ hP hv hN_own hNu
      (hg₂.bind _ _) hEN.toEnvReach (F := F)
      (fun b hb => hF b (Nat.le_trans (hH₁₂.trans hH₂').length_le hb))
      (fun b hb => by
        show F b + (U_δ b + C b + (Demand.positions (List.ofFn πs) Us b +
          Demand.positions (List.ofFn πs') Vs b)) ≠ _
        rw [hlen₂] at hb
        rcases Heap.EnvClaims.bind_cases hb with ⟨l, hφl, hπl, hcl⟩ | ⟨j, hφj, hπj, hcl⟩ | hsc
        · -- The variable of a field that the branch owns alone.
          obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hκle⟩ := hκ l
          obtain ⟨hθ', rfl, hρ1, rfl⟩ := (by decide : ∀ θ κ ϱ₀ ρ π₀ : Multiplicity,
            θ * κ = .one → κ ≤ ϱ₀ * (ρ * π₀) → θ = .one ∧ ϱ₀ = .one ∧ ρ = .one ∧ π₀ = .one)
            _ _ _ _ _ hφl hκle
          obtain ⟨π₀', h₀', hπle⟩ := hπ l
          cases hπ₀.symm.trans h₀'
          rw [hρ1] at hπle
          have hπ1 : πs l = .one := (by decide : ∀ π x : Multiplicity,
            Multiplicity.one * Multiplicity.one ≤ π + Multiplicity.one * x → π ≠ .zero →
            π = .one) _ _ hπle hπl
          have hal : as[(l : Nat)]? = some as[(l : Nat)] := List.getElem?_eq_getElem (hla ▸ l.2)
          have hπsl : (List.ofFn πs ++ List.ofFn πs')[(l : Nat)]? = some Multiplicity.one := by
            rw [List.getElem?_append_left (by simp), List.getElem?_ofFn]
            simp [hπ1]
          rcases hcl.cell_inv (hcell l _ _ hπsl (by
            rw [List.getElem?_append_left (hla ▸ l.2)]; exact hal)) with rfl | hcl'
          · exact hnew l hπsl
          · obtain ⟨U_l, -, hUal⟩ := hUs.getElem? hal
            obtain ⟨hf0, hδ0, hχ0, hblt, ⟨U_l', hUl', hul⟩, h1, h4⟩ := hfield b l _ hθ' hρ1 hal
              hπ₀ hϱ₀ (hcl'.of_extends (hH₁₂.trans hH₂') hg₁₂ (.inl ⟨_, hUal⟩))
            have hPne : Demand.positions (List.ofFn πs) Us b ≠ .zero :=
              Demand.positions_ne_zero _ _ (π := .one) (by
                rw [List.getElem?_ofFn]
                simp [hπ1]) hUl'
                ((by decide : ∀ u : Multiplicity, u ≠ .zero → Multiplicity.one * u ≠ .zero) _ hul)
            obtain ⟨hr0, hp1⟩ := (by decide : ∀ p r : Multiplicity, Multiplicity.one ≤ p + r →
              p ≠ .zero → r = .zero ∧ p = .one) _ _ h1 hPne
            rw [hr0] at h4
            have hn0 := (by decide : ∀ n : Multiplicity, Multiplicity.zero ≤ n → n = .zero) _ h4
            rw [hf0, hδ0, hC0 b (Nat.lt_of_lt_of_le hblt hH₁₂.length_le), hp1,
              Demand.positions_eq_zero _ _ (hA_R b hblt hn0)]
            decide
        · -- The variable of a recursive result that the branch owns alone.
          obtain ⟨hw1, hπ1⟩ := Multiplicity.mul_eq_one _ _ hφj
          obtain ⟨r_j, hrj⟩ : ∃ r_j, rs[(j : Nat)]? = some r_j :=
            ⟨_, List.getElem?_eq_getElem (hlrs ▸ j.2)⟩
          have hπsj : (List.ofFn πs ++ List.ofFn πs')[a' + (j : Nat)]? =
              some Multiplicity.one := by
            rw [List.getElem?_append_right (by simp), List.getElem?_ofFn]
            simp [hπ1]
          rcases hcl.cell_inv (hcell (a' + j) _ r_j hπsj (by
            rw [List.getElem?_append_right (by omega), hla, Nat.add_sub_cancel_left]
            exact hrj)) with rfl | hcl'
          · exact hnew (a' + j) hπsj
          · obtain ⟨V_j, -, hVj⟩ := hVs.getElem? hrj
            have hcl₂ := hcl'.of_extends hH₂' hgr (.inl ⟨_, hVj⟩)
            have h : (F b + (U_δ b + Demand.positions (List.ofFn πs) Us b)) +
                Demand.positions (List.ofFn πs') Vs b ≠ .omega :=
              hB_R b j _ hrj (by rw [List.getElem?_ofFn]; simp [hπ1])
                (fun k hk _ => by
                  rw [List.getElem?_ofFn] at hk
                  simp at hk
                  rw [← hk]
                  exact hw1) hcl₂
            rw [hC0 b (hVj.lt (hcl₂.reach_ne_zero.1 _ hVj))]
            exact (by decide : ∀ f d p v : Multiplicity, (f + (d + p)) + v ≠ .omega →
              f + (d + .zero + (p + v)) ≠ .omega) _ _ _ _ h
        · -- A variable of the scope that the branch owns alone and reads.
          have hsc₀ := hsc.of_extends (hH₁₂.trans hH₂') hg₁₂ hEδ.toEnvReach
          have hδb : U_δ b ≠ .zero := hsc₀.reach_ne_zero hEδ.toEnvReach
          have hχcl : Heap.EnvClaims H g E φ χ b := hsc₀.imp fun x hx =>
            (by decide : ∀ c d s : Multiplicity, c ≤ d + s * c → d ≠ .zero → c ≠ .zero)
              _ _ _ (hχle x) hx
          have hχb : U_χ b ≠ .zero := hχcl.reach_ne_zero hE
          have h : F b + (ρ.references * (Demand.unit a b +
              Demand.positions (πs₀.map Multiplicity.references) Us b) + U_χ b) ≠ .omega :=
            hc b hχcl
          have hra := (by decide : ∀ f x c : Multiplicity, f + (x + c) ≠ .omega → c ≠ .zero →
            x = .zero) _ _ _ h hχb
          have hfc : F b + U_χ b ≠ .omega := (by decide : ∀ f x c : Multiplicity,
            f + (x + c) ≠ .omega → x = .zero → f + c ≠ .omega) _ _ _ h hra
          have hs0 := (by decide : ∀ f c d s : Multiplicity, f + c ≠ .omega → c ≠ .zero →
            d ≠ .zero → c ≤ d + s * c → s = .zero) _ _ _ _ hfc hχb hδb (hχpt b)
          have hblt := hE.lt hχb
          have hn0 : Demand.need ρ Us U_χ (List.ofFn ks) b = .zero :=
            Demand.need_eq_zero_of_computed hlen (hcomp.trans hs0) hkL
          rw [hP0 b hra, hC0 b (Nat.lt_of_lt_of_le hblt hH₁₂.length_le),
            Demand.positions_eq_zero _ _ (hA_R b hblt hn0)]
          exact (by decide : ∀ f c d s : Multiplicity, f + c ≠ .omega → c ≠ .zero →
            d ≠ .zero → c ≤ d + s * c → f + (d + .zero + (.zero + .zero)) ≠ .omega)
            _ _ _ _ hfc hχb hδb (hχpt b))
    refine ⟨g₃, U, hg₁₂.trans (hH₁₂.trans hH₂') hg₂₃, hg₃, hU, fun b hb h0 => ?_, hB_N⟩
    have h0' : ρ.references * (Demand.unit a b +
        Demand.positions (πs₀.map Multiplicity.references) Us b) + U_χ b = .zero := h0
    have hra := Multiplicity.add_eq_zero_left _ _ h0'
    have hχ0 := Multiplicity.add_eq_zero_right _ _ h0'
    have hδ0 : U_δ b = .zero := (by decide : ∀ c d s : Multiplicity, c ≤ d + s * c →
      c = .zero → d = .zero) _ _ _ (hχpt b) hχ0
    refine hA_N b (Nat.lt_of_lt_of_le hb (hH₁₂.trans hH₂').length_le) ?_
    show U_δ b + C b + (Demand.positions (List.ofFn πs) Us b +
      Demand.positions (List.ofFn πs') Vs b) = _
    rw [hδ0, hC0 b (Nat.lt_of_lt_of_le hb hH₁₂.length_le), hP0 b hra,
      Demand.positions_eq_zero _ _ (hA_R b hb (Demand.need_eq_zero (hrec0 b hra) hχ0))]
    rfl
termination_by structural h

/-- The invariant of the evaluation of the recursive results of a branch: their values have
reaches, which refer to no address of the heap that the recursions do not need, and each address
that a result owned alone and read once claims is referred to once at most by the results, each as
many times as its binder reads it, and the frame. -/
theorem EvalResults.reach {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω)
    (hP : P.Usage) {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat}
    {ρ ϱ : Multiplicity} {Ns : TargetBranches n} {as : List Nat} {ks : List RecursiveResult}
    {πs' : List Multiplicity} {rs : List Nat} {R : List Nat}
    (h : EvalResults P ϖ H E ρ ϱ Ns as ks πs' rs H' R) {φ χ : MultiplicityVector n}
    {θ o' ς χ' : Multiplicity} (hNs : TargetBranches.Ownership Ω φ ρ θ o' ς χ' Ns)
    (hχ : TargetBranches.Usage ρ χ Ns) (hθ : θ = .one → ϱ = .one) (hθϱ : θ * ϱ = θ)
    (hθz : ρ = .zero → ∃ o₀, o₀ ≤ .one ∧ o₀ * ϱ = θ) {κs : List Multiplicity}
    (hks : ∀ (j l : Nat) (σ : Shape) (a : Nat), ks[j]? = some (.nested l σ) → as[l]? = some a →
      ∃ κ, κs[l]? = some κ ∧ σ.Fits ρ ∧ σ.Uniform ς χ' ∧
        (ρ * σ.factor ≠ .zero → σ.Requires θ ς ∧ θ ≤ ς * (θ * κ)))
    {g : Heap.Annotation} (hg : g.Valid Ω H) {U_χ : Demand} (hE : Heap.EnvReach H g E χ U_χ)
    {Us : List Demand} (has : List.Pointwise (Heap.ValueReach H g) as Us) {F : Demand}
    (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hc : ∀ (j : Nat) (k : RecursiveResult), ks[j]? = some k → k.factor ≠ .zero →
      ∀ b, Heap.EnvClaims H g E φ χ b → F b + Demand.need ρ Us U_χ ks b ≠ .omega)
    (hca : θ = .one → ρ ≠ .zero → ∀ (j l a : Nat), ks[j]? = some (.field l) → as[l]? = some a →
      ∀ b, Heap.Claims H g a b → F b + Demand.need ρ Us U_χ ks b ≠ .omega)
    (hcn : ∀ (j l : Nat) (σ : Shape) (a : Nat) (κ : Multiplicity), ks[j]? = some (.nested l σ) →
      κs[l]? = some κ → θ * κ = .one → σ.factor * ρ ≠ .zero → as[l]? = some a →
      ∀ b, Heap.Claims H g a b → F b + Demand.need ρ Us U_χ ks b ≠ .omega) :
    ∃ g' Vs, Heap.Annotation.Extends H g g' ∧ g'.Valid Ω H' ∧
      List.Pointwise (Heap.ValueReach H' g') rs Vs ∧
      (∀ b, b < H.length → Demand.need ρ Us U_χ ks b = .zero → ∀ V ∈ Vs, V b = .zero) ∧
      (∀ (b j r : Nat), rs[j]? = some r → πs'[j]? = some Multiplicity.one →
        (∀ k, ks[j]? = some k → k ≠ .erased → k.ownership o' = .one) → Heap.Claims H' g' r b →
          F b + Demand.positions πs' Vs b ≠ .omega) :=
  match h with
  | .nil => ⟨g, [], .refl _ _, hg, .nil, fun _ _ _ _ h => by simp at h,
      fun _ _ _ h => by simp at h⟩
  | .erased (H₂ := H₂) (ks := ks') (π := π) (πs := πs'') (rs := rs') hs => by
    have hH₁ : H.Extends (H ++ [.erased]) := List.prefix_append _ _
    have hgr := Heap.Annotation.Extends.refl H g
    have hu : ∀ b, b < H.length → Demand.unit H.length b = .zero := fun b hb => by
      simp [Demand.unit, Nat.ne_of_lt hb]
    obtain ⟨g₂, Vs, hg₁₂, hg₂, hVs, hA, hB⟩ := EvalResults.reach hΩ hP hs hNs hχ hθ hθϱ hθz
      (fun j => hks (j + 1)) (hg.concat (fun _ _ _ _ _ _ h => nomatch h)) (hE.mono hH₁ hgr)
      (has.imp fun _ _ h => h.mono hH₁ hgr) (F := F +ᶜ π ·ᶜ Demand.unit H.length)
      (fun b hb => by
        have hb' : H.length < b := by
          have := hb
          simp at this
          omega
        show F b + π * Demand.unit H.length b = _
        rw [hF b (Nat.le_of_lt hb'),
          show Demand.unit H.length b = .zero by simp [Demand.unit, Nat.ne_of_gt hb']]
        cases π <;> rfl)
      (fun j k hj hf b hb => by
        have hb₁ := hb.of_extends hH₁ hgr hE
        have h : F b + Demand.need ρ Us U_χ ks' b ≠ .omega := hc (j + 1) k hj hf b hb₁
        show (F b + π * Demand.unit H.length b) + _ ≠ _
        rw [hu b (hE.lt (hb₁.reach_ne_zero hE))]
        exact (by decide : ∀ f π n : Multiplicity, f + n ≠ .omega → f + π * .zero + n ≠ .omega)
          _ _ _ h)
      (fun hθ' hρ j l a hj ha b hb => by
        obtain ⟨U', -, hUa⟩ := has.getElem? ha
        have hb₁ := hb.of_extends hH₁ hgr (.inl ⟨_, hUa⟩)
        have h : F b + Demand.need ρ Us U_χ ks' b ≠ .omega :=
          hca hθ' hρ (j + 1) l a hj ha b hb₁
        show (F b + π * Demand.unit H.length b) + _ ≠ _
        rw [hu b (hUa.lt (hb₁.reach_ne_zero.1 _ hUa))]
        exact (by decide : ∀ f π n : Multiplicity, f + n ≠ .omega → f + π * .zero + n ≠ .omega)
          _ _ _ h)
      (fun j l σ a κ hj hκ hθκ hfρ ha b hb => by
        obtain ⟨U', -, hUa⟩ := has.getElem? ha
        have hb₁ := hb.of_extends hH₁ hgr (.inl ⟨_, hUa⟩)
        have h : F b + Demand.need ρ Us U_χ ks' b ≠ .omega :=
          hcn (j + 1) l σ a κ hj hκ hθκ hfρ ha b hb₁
        show (F b + π * Demand.unit H.length b) + _ ≠ _
        rw [hu b (hUa.lt (hb₁.reach_ne_zero.1 _ hUa))]
        exact (by decide : ∀ f π n : Multiplicity, f + n ≠ .omega → f + π * .zero + n ≠ .omega)
          _ _ _ h)
    have hr : H₂[H.length]? = some .erased := hs.extends.getElem? List.getElem?_concat_length
    refine ⟨g₂, Demand.unit H.length :: Vs, hgr.trans hH₁ hg₁₂, hg₂, .cons (.erased hr) hVs,
      fun b hb h0 V hV => ?_, fun b j r hr' hπ' ho' hcl => ?_⟩
    · rcases List.mem_cons.1 hV with rfl | hV
      · exact hu b hb
      · exact hA b (by simp; omega) h0 V hV
    · show F b + (π * Demand.unit H.length b + Demand.positions πs'' Vs b) ≠ _
      cases j with
      | zero =>
        cases hr'
        cases hπ'
        obtain rfl := hcl.erased_inv hr
        have hn : Demand.need ρ Us U_χ ks' H.length = .zero :=
          Demand.need_eq_zero (fun j k l _ _ _ => by
            rw [Demand.getD_eq_zero (Heap.ValueReach.pointwise_eq_zero has (Nat.le_refl _)) l]
            cases ρ <;> rfl) (hE.eq_zero _ (Nat.le_refl _))
        rw [hF _ (Nat.le_refl _), Demand.positions_eq_zero _ _ (hA _ (by simp) hn)]
        simp [Demand.unit] <;> decide
      | succ j =>
        have h : (F b + π * Demand.unit H.length b) + Demand.positions πs'' Vs b ≠ .omega :=
          hB b j r (by simpa using hr') (by simpa using hπ') (fun k hk hke => ho' k hk hke) hcl
        exact (by decide : ∀ f x y : Multiplicity, f + x + y ≠ .omega → f + (x + y) ≠ .omega)
          _ _ _ h
  | .recursor (H₂ := H₂) (j := l) (a := a) (r := r) (ks := ks') (π := π) (πs := πs'')
      (rs := rs') hj hrec hs => by
    obtain ⟨U_l, hUl, hUa⟩ := has.getElem? hj
    have hneed : ∀ b, Demand.need ρ Us U_χ (.field l :: ks') b =
        (ρ.references * U_l b + U_χ b) + Demand.need ρ Us U_χ ks' b := fun b => by
      show (ρ.references * Us.getD l 𝟘ᵛ b + U_χ b) + _ = _
      rw [List.getD_eq_getElem?_getD, hUl]
      rfl
    have hn0 : ∀ b, H.length ≤ b → Demand.need ρ Us U_χ ks' b = .zero := fun b hb =>
      Demand.need_eq_zero (fun j k l _ _ _ => by
        rw [Demand.getD_eq_zero (Heap.ValueReach.pointwise_eq_zero has hb) l]
        cases ρ <;> rfl) (hE.eq_zero b hb)
    obtain ⟨g₂, V, hg₁₂, hg₂, hV, hA₁, hB₁⟩ := EvalRec.reach hΩ hP hrec hNs hχ hθ hθϱ hθz hg
      hE hUa (F := F +ᶜ Demand.need ρ Us U_χ ks')
      (fun b hb => by
        show F b + Demand.need ρ Us U_χ ks' b = _
        rw [hF b hb, hn0 b hb]
        rfl)
      (fun b hb => by
        have h := hc 0 _ rfl (by simp [RecursiveResult.factor]) b hb
        rw [hneed] at h
        exact (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega → f + n + x ≠ .omega)
          _ _ _ h)
      (fun hθ' hρ b hb => by
        have h := hca hθ' hρ 0 l a rfl hj b hb
        rw [hneed] at h
        exact (by decide : ∀ f ρ u c n : Multiplicity, ρ ≠ .zero →
          f + ((ρ.references * u + c) + n) ≠ .omega → f + n + (u + c) ≠ .omega) _ _ _ _ _ hρ h)
    have hH₁₂ := hrec.extends
    obtain ⟨g₃, Vs, hg₂₃, hg₃, hVs, hA₂, hB₂⟩ := EvalResults.reach hΩ hP hs hNs hχ hθ hθϱ hθz
      (fun j => hks (j + 1)) hg₂ (hE.mono hH₁₂ hg₁₂) (has.imp fun _ _ h => h.mono hH₁₂ hg₁₂)
      (F := F +ᶜ π ·ᶜ V)
      (fun b hb => by
        show F b + π * V b = _
        rw [hF b (Nat.le_trans hH₁₂.length_le hb), hV.eq_zero b hb]
        cases π <;> rfl)
      (fun j k hj' hf b hb => by
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ hE
        have hχb := hb₁.reach_ne_zero hE
        have h := hc 0 _ rfl (by simp [RecursiveResult.factor]) b hb₁
        rw [hneed] at h
        exact absurd ((by decide : ∀ f x c n : Multiplicity, c ≠ .zero → n ≠ .zero →
          f + ((x + c) + n) = .omega) _ _ _ _ hχb (Demand.need_ne_zero_scope hj' hf hχb)) h)
      (fun hθ' hρ j l' a' hj' ha' b hb => by
        obtain ⟨U', hU', hUa'⟩ := has.getElem? ha'
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ (.inl ⟨_, hUa'⟩)
        have hu' : U' b ≠ .zero := hb₁.reach_ne_zero.1 _ hUa'
        have hnf : Demand.need ρ Us U_χ ks' b ≠ .zero := Demand.need_ne_zero_field hj' (by
          rw [List.getD_eq_getElem?_getD, hU']
          exact Multiplicity.references_mul_ne_zero _ _ hρ hu')
        have h := hca hθ' hρ (j + 1) l' a' hj' ha' b hb₁
        rw [hneed] at h
        have hx := (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega → n ≠ .zero →
          x = .zero) _ _ _ h hnf
        show (F b + π * V b) + _ ≠ _
        rw [hA₁ b (hUa'.lt hu') hx]
        exact (by decide : ∀ f π x n : Multiplicity, f + (x + n) ≠ .omega →
          f + π * .zero + n ≠ .omega) _ _ _ _ h)
      (fun j l' σ' a' κ hj' hκ hθκ hfρ ha' b hb => by
        obtain ⟨U', hU', hUa'⟩ := has.getElem? ha'
        have hb₁ := hb.of_extends hH₁₂ hg₁₂ (.inl ⟨_, hUa'⟩)
        have hu' : U' b ≠ .zero := hb₁.reach_ne_zero.1 _ hUa'
        have hnf : Demand.need ρ Us U_χ ks' b ≠ .zero := Demand.need_ne_zero_nested hj' (by
          rw [List.getD_eq_getElem?_getD, hU']
          exact Multiplicity.mul_ne_zero _ _ hfρ hu')
        have h := hcn (j + 1) l' σ' a' κ hj' hκ hθκ hfρ ha' b hb₁
        rw [hneed] at h
        have hx := (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega → n ≠ .zero →
          x = .zero) _ _ _ h hnf
        show (F b + π * V b) + _ ≠ _
        rw [hA₁ b (hUa'.lt hu') hx]
        exact (by decide : ∀ f π x n : Multiplicity, f + (x + n) ≠ .omega →
          f + π * .zero + n ≠ .omega) _ _ _ _ h)
    refine ⟨g₃, V :: Vs, hg₁₂.trans hH₁₂ hg₂₃, hg₃, .cons (hV.mono hs.extends hg₂₃) hVs,
      fun b hb h0 V' hV' => ?_, fun b j r' hr' hπ' ho' hcl => ?_⟩
    · rw [hneed] at h0
      rcases List.mem_cons.1 hV' with rfl | hV'
      · exact hA₁ b hb (Multiplicity.add_eq_zero_left _ _ h0)
      · exact hA₂ b (Nat.lt_of_lt_of_le hb hH₁₂.length_le)
          (Multiplicity.add_eq_zero_right _ _ h0) V' hV'
    · show F b + (π * V b + Demand.positions πs'' Vs b) ≠ _
      cases j with
      | zero =>
        cases hr'
        cases hπ'
        have hcl₂ := hcl.of_extends hs.extends hg₂₃ (.inl ⟨_, hV⟩)
        have h : (F b + Demand.need ρ Us U_χ ks' b) + V b ≠ .omega :=
          hB₁ (ho' _ rfl (fun h => nomatch h)) b hcl₂
        have hv0 : V b ≠ .zero := hcl₂.reach_ne_zero.1 _ hV
        have hn := (by decide : ∀ f n v : Multiplicity, f + n + v ≠ .omega → v ≠ .zero →
          n = .zero) _ _ _ h hv0
        rw [Demand.positions_eq_zero _ _ (hA₂ b (hV.lt hv0) hn)]
        exact (by decide : ∀ f n v : Multiplicity, f + n + v ≠ .omega →
          f + (Multiplicity.one * v + .zero) ≠ .omega) _ _ _ h
      | succ j =>
        have h : (F b + π * V b) + Demand.positions πs'' Vs b ≠ .omega :=
          hB₂ b j r' (by simpa using hr') (by simpa using hπ') (fun k hk hke => ho' k hk hke) hcl
        exact (by decide : ∀ f x y : Multiplicity, f + x + y ≠ .omega → f + (x + y) ≠ .omega)
          _ _ _ h
  | .nested (H₂ := H₂) (l := l) (a := a) (r := r) (σ := σ) (ks := ks') (π := π) (πs := πs'')
      (rs := rs') hl hev hs => by
    obtain ⟨U_l, hUl, hUa⟩ := has.getElem? hl
    obtain ⟨κ, hκ, hfits, huni, hreq⟩ := hks 0 l σ a rfl hl
    have hneed : ∀ b, Demand.need ρ Us U_χ (.nested l σ :: ks') b =
        (σ.factor * ρ * U_l b + σ.factor * U_χ b) + Demand.need ρ Us U_χ ks' b := fun b => by
      show (σ.factor * ρ * Us.getD l 𝟘ᵛ b + σ.factor * U_χ b) + _ = _
      rw [List.getD_eq_getElem?_getD, hUl]
      rfl
    have hn0 : ∀ b, H.length ≤ b → Demand.need ρ Us U_χ ks' b = .zero := fun b hb =>
      Demand.need_eq_zero (fun j k l _ _ _ => by
        rw [Demand.getD_eq_zero (Heap.ValueReach.pointwise_eq_zero has hb) l]
        cases ρ <;> rfl) (hE.eq_zero b hb)
    -- The cell of the field, which the corecursor captures with the scope of the recursor.
    have hH₁ : H.Extends (H ++ [.cell (ϖ * π * (σ.factor * ρ)) a]) := List.prefix_append _ _
    have hgr := Heap.Annotation.Extends.refl H g
    have hcell : (H ++ [.cell (ϖ * π * (σ.factor * ρ)) a])[H.length]? =
        some (.cell (ϖ * π * (σ.factor * ρ)) a) := List.getElem?_concat_length
    have hu : ∀ b, b < H.length → Demand.unit H.length b = .zero := fun b hb => by
      simp [Demand.unit, Nat.ne_of_lt hb]
    have hEn := Heap.EnvReach.cons (ν := σ.factor ·ᶜ ((ρ ·ᶜ MultiplicityVector.update 𝟘ᵛ 0 .one)
        +ᶜ MultiplicityVector.rename (TargetRen.shift n 1) χ)) hcell (hUa.mono hH₁ hgr)
      (by
        rw [funext (MultiplicityVector.nested_succ σ.factor ρ χ)]
        exact ((hE.mono hH₁ hgr).toEnvSum.smul σ.factor).toEnvReach)
    rw [MultiplicityVector.nested_zero] at hEn
    -- The corecursor, a new value, owns the field as the branch owns its variable.
    have hM := Target.Ownership.nested (Ω := Ω) (ρ := ρ) (ϱ := ϱ) (o' := o') hθϱ hθz
      (φ' := (φ.extendBinders (fun _ : Fin 0 => .zero) (fun _ : Fin 1 => θ * κ) :
        MultiplicityVector (n + 1)))
      (fun x => MultiplicityVector.extendBinders_shift (a := 0) (b := 1) _ _ _ x)
      (fun h => (hreq h).2) hNs huni (fun h => (hreq h).1)
    have hsum : ∀ b, b < H.length →
        σ.factor * ρ * (Demand.unit H.length b + U_l b) + σ.factor * U_χ b =
          σ.factor * ρ * U_l b + σ.factor * U_χ b := fun b hb => by
      rw [hu b hb]
      cases U_l b <;> rfl
    obtain ⟨g₂, V, hg₁₂, hg₂, hV, hA₁, hB₁⟩ := Eval.reach hΩ hP hev hM
      (Target.Usage.nested hχ hfits) (hg.concat (fun _ _ _ _ _ _ h => nomatch h)) hEn
      (F := F +ᶜ Demand.need ρ Us U_χ ks')
      (fun b hb => by
        show F b + Demand.need ρ Us U_χ ks' b = _
        have hb' : H.length ≤ b := by simp at hb; omega
        rw [hF b hb', hn0 b hb']
        rfl)
      (fun b ⟨x, c', hx, hφx, hνx, hcl⟩ => by
        show (F b + Demand.need ρ Us U_χ ks' b) +
          (σ.factor * ρ * (Demand.unit H.length b + U_l b) + σ.factor * U_χ b) ≠ _
        cases x using Fin.cases with
        | zero =>
          cases hx
          have hθκ1 : θ * κ = .one := hφx
          have hfρ : σ.factor * ρ ≠ .zero := by
            rwa [MultiplicityVector.nested_zero] at hνx
          rcases hcl.cell_inv hcell with rfl | hcl'
          · -- The cell itself, new: the corecursor reads it once.
            have ha := hcn 0 l σ a κ rfl hκ hθκ1 hfρ hl a (.self a)
            rw [hneed] at ha
            have hua : U_l a ≠ .zero := (Heap.Claims.self a).reach_ne_zero.1 _ hUa
            rw [hF _ (Nat.le_refl _), hn0 _ (Nat.le_refl _), hUa.eq_zero _ (Nat.le_refl _),
              hE.eq_zero _ (Nat.le_refl _)]
            simp only [Demand.unit, ↓reduceIte]
            exact (by decide : ∀ f x u c n s : Multiplicity, f + ((x * u + c) + n) ≠ .omega →
              u ≠ .zero → (.zero + .zero) + (x * (.one + .zero) + s * .zero) ≠ .omega)
              _ _ _ _ _ _ ha hua
          · -- What the field claims, which the branch owns alone.
            have hb₁ := hcl'.of_extends hH₁ hgr (.inl ⟨_, hUa⟩)
            have hb := hb₁.reach_ne_zero.1 _ hUa
            have h := hcn 0 l σ a κ rfl hκ hθκ1 hfρ hl b hb₁
            rw [hneed] at h
            rw [hsum b (hUa.lt hb)]
            exact (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega →
              (f + n) + x ≠ .omega) _ _ _ h
        | succ y =>
          have hφy : φ y = .one := by
            rw [← MultiplicityVector.extendBinders_shift φ (fun _ : Fin 0 => .zero)
              (fun _ : Fin 1 => θ * κ) y]
            exact hφx
          have hνy : σ.factor * χ y ≠ .zero := by
            rwa [MultiplicityVector.nested_succ] at hνx
          have hf : σ.factor ≠ .zero := fun h0 => hνy (by rw [h0]; cases χ y <;> rfl)
          have hb₁ : Heap.EnvClaims H g E φ χ b :=
            Heap.EnvClaims.of_extends hH₁ hgr (⟨y, c', hx, hφy, fun h0 => hνy (by
              rw [h0]
              cases σ.factor <;> rfl), hcl⟩ : Heap.EnvClaims _ g E φ χ b) hE
          have hχb := hb₁.reach_ne_zero hE
          have h := hc 0 _ rfl hf b hb₁
          rw [hneed] at h
          rw [hsum b (hE.lt hχb)]
          exact (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega →
            (f + n) + x ≠ .omega) _ _ _ h)
    have hH₁₂ := hev.extends
    have hg₀ := hgr.trans hH₁ hg₁₂
    have hH₀ := hH₁.trans hH₁₂
    -- The summand of the result, by which the scope and the field are read.
    have hV0 : ∀ b, b < H.length → σ.factor * ρ * U_l b + σ.factor * U_χ b = .zero →
        V b = .zero := fun b hb h0 =>
      hA₁ b (by simp; omega) (by
        show σ.factor * ρ * (Demand.unit H.length b + U_l b) + σ.factor * U_χ b = _
        rw [hsum b hb]
        exact h0)
    obtain ⟨g₃, Vs, hg₂₃, hg₃, hVs, hA₂, hB₂⟩ := EvalResults.reach hΩ hP hs hNs hχ hθ hθϱ hθz
      (fun j => hks (j + 1)) hg₂ (hE.mono hH₀ hg₀) (has.imp fun _ _ h => h.mono hH₀ hg₀)
      (F := F +ᶜ π ·ᶜ V)
      (fun b hb => by
        show F b + π * V b = _
        rw [hF b (Nat.le_trans hH₀.length_le hb), hV.eq_zero b hb]
        cases π <;> rfl)
      (fun j k hj' hf' b hb => by
        have hb₁ := hb.of_extends hH₀ hg₀ hE
        have hχb := hb₁.reach_ne_zero hE
        show (F b + π * V b) + _ ≠ _
        by_cases hf : σ.factor = .zero
        · have h := hc (j + 1) k hj' hf' b hb₁
          rw [hneed, hf] at h
          rw [hV0 b (hE.lt hχb) (by rw [hf]; cases ρ <;> cases U_l b <;> cases U_χ b <;> rfl)]
          exact (by decide : ∀ f π ρ u c n : Multiplicity,
            f + ((.zero * ρ * u + .zero * c) + n) ≠ .omega → f + π * .zero + n ≠ .omega)
            _ _ _ _ _ _ h
        · have h := hc 0 _ rfl hf b hb₁
          rw [hneed] at h
          exact absurd ((by decide : ∀ f x c n : Multiplicity, c ≠ .zero → n ≠ .zero →
            f + ((x + c) + n) = .omega) _ _ _ _ (Multiplicity.mul_ne_zero _ _ hf hχb)
            (Demand.need_ne_zero_scope hj' hf' hχb)) h)
      (fun hθ' hρ j l' a' hj' ha' b hb => by
        obtain ⟨U', hU', hUa'⟩ := has.getElem? ha'
        have hb₁ := hb.of_extends hH₀ hg₀ (.inl ⟨_, hUa'⟩)
        have hu' : U' b ≠ .zero := hb₁.reach_ne_zero.1 _ hUa'
        have hnf : Demand.need ρ Us U_χ ks' b ≠ .zero := Demand.need_ne_zero_field hj' (by
          rw [List.getD_eq_getElem?_getD, hU']
          exact Multiplicity.references_mul_ne_zero _ _ hρ hu')
        have h := hca hθ' hρ (j + 1) l' a' hj' ha' b hb₁
        rw [hneed] at h
        have hx := (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega → n ≠ .zero →
          x = .zero) _ _ _ h hnf
        show (F b + π * V b) + _ ≠ _
        rw [hV0 b (hUa'.lt hu') hx]
        exact (by decide : ∀ f π x n : Multiplicity, f + (x + n) ≠ .omega →
          f + π * .zero + n ≠ .omega) _ _ _ _ h)
      (fun j l' σ' a' κ' hj' hκ' hθκ' hfρ' ha' b hb => by
        obtain ⟨U', hU', hUa'⟩ := has.getElem? ha'
        have hb₁ := hb.of_extends hH₀ hg₀ (.inl ⟨_, hUa'⟩)
        have hu' : U' b ≠ .zero := hb₁.reach_ne_zero.1 _ hUa'
        have hnf : Demand.need ρ Us U_χ ks' b ≠ .zero := Demand.need_ne_zero_nested hj' (by
          rw [List.getD_eq_getElem?_getD, hU']
          exact Multiplicity.mul_ne_zero _ _ hfρ' hu')
        have h := hcn (j + 1) l' σ' a' κ' hj' hκ' hθκ' hfρ' ha' b hb₁
        rw [hneed] at h
        have hx := (by decide : ∀ f x n : Multiplicity, f + (x + n) ≠ .omega → n ≠ .zero →
          x = .zero) _ _ _ h hnf
        show (F b + π * V b) + _ ≠ _
        rw [hV0 b (hUa'.lt hu') hx]
        exact (by decide : ∀ f π x n : Multiplicity, f + (x + n) ≠ .omega →
          f + π * .zero + n ≠ .omega) _ _ _ _ h)
    refine ⟨g₃, V :: Vs, hg₀.trans hH₀ hg₂₃, hg₃, .cons (hV.mono hs.extends hg₂₃) hVs,
      fun b hb h0 V' hV' => ?_, fun b j r' hr' hπ' ho' hcl => ?_⟩
    · rw [hneed] at h0
      rcases List.mem_cons.1 hV' with rfl | hV'
      · exact hV0 b hb (Multiplicity.add_eq_zero_left _ _ h0)
      · exact hA₂ b (Nat.lt_of_lt_of_le hb hH₀.length_le)
          (Multiplicity.add_eq_zero_right _ _ h0) V' hV'
    · show F b + (π * V b + Demand.positions πs'' Vs b) ≠ _
      cases j with
      | zero =>
        cases hr'
        cases hπ'
        have hcl₂ := hcl.of_extends hs.extends hg₂₃ (.inl ⟨_, hV⟩)
        have h : (F b + Demand.need ρ Us U_χ ks' b) + V b ≠ .omega := hB₁ rfl b hcl₂
        have hv0 : V b ≠ .zero := hcl₂.reach_ne_zero.1 _ hV
        have hn := (by decide : ∀ f n v : Multiplicity, f + n + v ≠ .omega → v ≠ .zero →
          n = .zero) _ _ _ h hv0
        rw [Demand.positions_eq_zero _ _ (hA₂ b (hV.lt hv0) hn)]
        exact (by decide : ∀ f n v : Multiplicity, f + n + v ≠ .omega →
          f + (Multiplicity.one * v + .zero) ≠ .omega) _ _ _ h
      | succ j =>
        have h : (F b + π * V b) + Demand.positions πs'' Vs b ≠ .omega :=
          hB₂ b j r' (by simpa using hr') (by simpa using hπ') (fun k hk hke => ho' k hk hke) hcl
        exact (by decide : ∀ f x y : Multiplicity, f + x + y ≠ .omega → f + (x + y) ≠ .omega)
          _ _ _ h
termination_by structural h

/-- The invariant of the observation of a value. -/
theorem EvalObs.reach {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω) (hP : P.Usage)
    {ϖ : Multiplicity} {H H' : Heap} {a i c : Nat} {ψ : ResultOwnership Multiplicity c}
    {ς : Multiplicity} {πs ϱs : List Multiplicity} {bs : List Nat} {v : Nat} {R : List Nat}
    (h : EvalObs P ϖ H a i ψ ς πs ϱs bs v H' R) {o₁ u : Multiplicity} {os : List Multiplicity}
    (hς : ς ≤ o₁) (hu : ψ.value os = some u)
    (hos : ∀ (k : Nat) (ϱ : Multiplicity), ϱs[k]? = some ϱ → ∃ o, os[k]? = some o ∧ ϱ ≤ o)
    (hol : os.length = bs.length)
    {g : Heap.Annotation} (hg : g.Valid Ω H) {U_a : Demand} (ha : Heap.ValueReach H g a U_a)
    {Us : List Demand} (hbs : List.Pointwise (Heap.ValueReach H g) bs Us) {F : Demand}
    (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hca : o₁ = .one → ∀ b, Heap.Claims H g a b →
      F b + (U_a b + Demand.positions (πs.map Multiplicity.references) Us b) ≠ .omega)
    (hcb : ∀ (b k b' : Nat) (π : Multiplicity), bs[k]? = some b' →
      os[k]? = some Multiplicity.one → πs[k]? = some π → π ≠ Multiplicity.zero →
      Heap.Claims H g b' b →
      F b + (U_a b + Demand.positions (πs.map Multiplicity.references) Us b) ≠ .omega) :
    ∃ g' U, Heap.Annotation.Extends H g g' ∧ g'.Valid Ω H' ∧ Heap.ValueReach H' g' v U ∧
      (∀ b, b < H.length →
        U_a b + Demand.positions (πs.map Multiplicity.references) Us b = .zero → U b = .zero) ∧
      (o₁ * u = .one → ∀ b, Heap.Claims H' g' v b → F b + U b ≠ .omega) :=
  match h with
  | .beta (H₂ := H₂) (n := n) (E := Ec) (Ps := Ps) (πs₁ := πs₁) (ϱs₁ := ϱs₁) (ss := ss)
      (o := k) (b := b') (c := c') (πs := πb) (ϱs := ϱb) (πs' := πb') (ϱs' := ϱb') (ψ := ψ')
      (ς := ς') (N := N) (w := w) hlook hPi hlb hlc hπ₁ hπ₂ hϱ₁ hϱ₂ hψ hς' hw hr => by
    have hu' : ψ'.value os = some u := by
      cases hψ
      exact hu
    -- The reach of the closure: itself, its scope and its state.
    obtain ⟨U_δc, Ss, hEc, hSs, rfl, hl₁⟩ := ha.corec_inv hlook
    obtain ⟨hval₁, hval₂⟩ := hg _ _ _ _ _ _ _ hlook
    obtain ⟨hown, hψc⟩ := hval₁.get _ hPi
    obtain ⟨δi, hNu, hδ, hres⟩ := hval₂.get _ hPi
    -- The ownership of the branch, at the ownerships of the arguments.
    have hosF := List.ofFn_getFin os (hol.trans hlc)
    have hreq : ∀ l, ϱb' l ≤ os.getFin (hol.trans hlc) l := fun l => by
      obtain ⟨ϱ₂, hϱ₂', hle⟩ := hϱ₂ l
      obtain ⟨o, ho, hle'⟩ := hos l ϱ₂ hϱ₂'
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 ho
      exact Multiplicity.le_trans' _ _ _ hle hle'
    obtain ⟨vN, Φ, hvN, hΦ⟩ : ∃ (vN : Multiplicity) (Φ : Demand),
        (k = .none ∧ vN = u ∨ k ≠ .none ∧ vN = .one) ∧
        (k = .none ∧ Φ = 𝟘ᵛ ∨ k ≠ .none ∧ Φ = U_δc) := by
      cases k with
      | none => exact ⟨u, 𝟘ᵛ, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩
      | unpack m => exact ⟨.one, U_δc, .inr ⟨nofun, rfl⟩, .inr ⟨nofun, rfl⟩⟩
      | erased m => exact ⟨.one, U_δc, .inr ⟨nofun, rfl⟩, .inr ⟨nofun, rfl⟩⟩
    have hN_own := hown (os.getFin (hol.trans hlc)) vN hreq (by
      rcases hvN with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · exact .inl ⟨hk, by rw [hosF]; exact hu'⟩
      · exact .inr ⟨hk, rfl⟩)
    -- The reads of the scope by the branch, and by the closure that it resumes.
    obtain ⟨U_δi, hle_i, hEi⟩ := hEc.toEnvSum.le hδ
    have hle_r : k ≠ .none → ∀ b, U_δc b ≤ U_δi b + U_δc b := fun hk => by
      obtain ⟨U'', hU'', hE''⟩ := hEc.toEnvSum.le (hres hk)
      obtain ⟨X₁, X₂, rfl, hX₁, hX₂⟩ := hE''.split
      rw [hX₁.toEnvReach.det hEi.toEnvReach, hX₂.toEnvReach.det hEc] at hU''
      exact hU''
    have hΦ0 : ∀ b, U_δc b = .zero → Φ b = .zero := fun b hb => by
      rcases hΦ with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rfl
      · exact hb
    have ho₁ : ς' = .one → o₁ = .one := fun h1 => (by decide : ∀ x y z : Multiplicity,
      x = .one → x ≤ y → y ≤ z → z = .one) _ _ _ h1 hς' hς
    -- A variable of the scope that the closure owns alone and reads is read by no branch that
    -- resumes the closure, which captures it again.
    have hscope : ∀ (x : Fin n) (cx b : Nat), Ec[(x : Nat)]? = some cx →
        g.usage a n x ≠ .zero → g.ownership a n x = .one → Heap.Claims H g cx b → o₁ = .one →
        F b = .zero ∧ U_δc b ≠ .zero ∧ U_δc b ≠ .omega ∧
        Demand.positions (πs₁.map Multiplicity.references) Ss b = .zero ∧
        Demand.positions (πs.map Multiplicity.references) Us b = .zero ∧ k = .none :=
      fun x cx b hcx hδx hφx hclx ho => by
        have h : F b + ((Demand.unit a b + (U_δc b +
            Demand.positions (πs₁.map Multiplicity.references) Ss b)) +
            Demand.positions (πs.map Multiplicity.references) Us b) ≠ .omega :=
          hca ho b (.scope x hlook hcx hδx hφx hclx)
        have hdc : U_δc b ≠ .zero :=
          Heap.EnvClaims.reach_ne_zero ⟨x, cx, hcx, hφx, hδx, hclx⟩ hEc
        obtain ⟨hf, hdω, hp, hq⟩ := (by decide : ∀ f u d p q : Multiplicity,
          f + ((u + (d + p)) + q) ≠ .omega → d ≠ .zero →
          f = .zero ∧ d ≠ .omega ∧ p = .zero ∧ q = .zero) _ _ _ _ _ h hdc
        refine ⟨hf, hdc, hdω, hp, hq, ?_⟩
        rcases hΦ with ⟨hk, -⟩ | ⟨hk, -⟩
        · exact hk
        · exact absurd (hle_r hk b) ((by decide : ∀ d di : Multiplicity, d ≠ .zero →
            d ≠ .omega → d ≤ di → ¬ d ≤ di + d) _ _ hdc hdω (hle_i b))
    -- The cells of the branch and the reach of its environment.
    have hH' : H.Extends (H.bind ((List.ofFn πb ++ List.ofFn πb').map (ϖ * ·)) (ss ++ bs)) :=
      List.prefix_append _ _
    have hgr := Heap.Annotation.Extends.refl H g
    obtain ⟨C, hEN, -, hC0, hCc⟩ := Heap.EnvSum.bindBranch ϖ πb πb'
      (hEi.toEnvReach.mono hH' hgr).toEnvSum (hSs.imp fun _ _ h => h.mono hH' hgr)
      (hbs.imp fun _ _ h => h.mono hH' hgr) hlb hlc
    have hlen₂ : (ss ++ bs).length = b' + c' := by simp [hlb, hlc]
    have hπ₁L := Multiplicity.le_ofFn πs₁ πb hπ₁
    have hπ₂L := Multiplicity.le_ofFn πs πb' hπ₂
    have hlS : Ss.length ≤ πs₁.length := by
      have := hSs.length
      omega
    have hlU : Us.length ≤ πs.length := by
      have h₁ := hbs.length
      by_cases hc0 : bs.length = 0
      · omega
      · obtain ⟨π, hπ, -⟩ := hπ₂ ⟨bs.length - 1, by omega⟩
        have := (List.getElem?_eq_some_iff.1 hπ).1
        simp only at this
        omega
    have hS0 := fun b => Demand.positions_eq_zero_of_le (b := b) πs₁ (List.ofFn πb) Ss hlS hπ₁L
    have hU0 := fun b => Demand.positions_eq_zero_of_le (b := b) πs (List.ofFn πb') Us hlU hπ₂L
    have hcell : ∀ (j : Nat) (π : Multiplicity) (a₀ : Nat),
        (List.ofFn πb ++ List.ofFn πb')[j]? = some π → (ss ++ bs)[j]? = some a₀ →
        (H.bind ((List.ofFn πb ++ List.ofFn πb').map (ϖ * ·)) (ss ++ bs))[H.length + j]? =
          some (.cell (ϖ * π) a₀) := fun j π a₀ h₁ h₂ =>
      Heap.bind_getElem? H _ _ j _ _ (by rw [List.getElem?_map, h₁]; rfl) h₂
    have hSs0 : ∀ b, H.length ≤ b → Demand.positions (List.ofFn πb) Ss b = .zero := fun b hb =>
      Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hSs hb)
    have hUs0 : ∀ b, H.length ≤ b → Demand.positions (List.ofFn πb') Us b = .zero := fun b hb =>
      Demand.positions_eq_zero _ _ (Heap.ValueReach.pointwise_eq_zero hbs hb)
    -- A new cell that the branch owns alone is read once, and nothing else refers to it.
    have hnew : ∀ (j : Nat), (List.ofFn πb ++ List.ofFn πb')[j]? = some Multiplicity.one →
        (F (H.length + j) + Φ (H.length + j)) + (U_δi (H.length + j) + C (H.length + j) +
          (Demand.positions (List.ofFn πb) Ss (H.length + j) +
            Demand.positions (List.ofFn πb') Us (H.length + j))) ≠ .omega := fun j hj => by
      have hle : H.length ≤ H.length + j := Nat.le_add_right _ _
      rw [hF _ hle, hΦ0 _ (hEc.eq_zero _ hle), hEi.toEnvReach.eq_zero _ hle, hCc j _ hj,
        hSs0 _ hle, hUs0 _ hle]
      decide
    -- What the branch uses of the heap, when the closure and the arguments refer to none of it.
    have hzeroN : ∀ b, b < H.length → (Demand.unit a b + (U_δc b +
        Demand.positions (πs₁.map Multiplicity.references) Ss b)) +
        Demand.positions (πs.map Multiplicity.references) Us b = .zero →
        U_δi b + C b + (Demand.positions (List.ofFn πb) Ss b +
          Demand.positions (List.ofFn πb') Us b) = .zero := fun b hb h0 => by
      obtain ⟨hd, hp, hq⟩ := (by decide : ∀ u d p q : Multiplicity, (u + (d + p)) + q = .zero →
        d = .zero ∧ p = .zero ∧ q = .zero) _ _ _ _ h0
      rw [Multiplicity.eq_zero_of_le_of_eq_zero _ _ (hle_i b) hd,
        hC0 b hb, hS0 b hp, hU0 b hq]
      rfl
    -- The branch.
    obtain ⟨g₂, U_w, hg₁₂, hg₂, hUw, hA_N, hB_N⟩ := Eval.reach hΩ hP hw hN_own hNu
      (hg.bind _ _) hEN.toEnvReach (F := F +ᶜ Φ)
      (fun b hb => by
        have hle := Nat.le_trans hH'.length_le hb
        show F b + Φ b = _
        rw [hF b hle, hΦ0 b (hEc.eq_zero b hle)]
        rfl)
      (fun b hb => by
        show (F b + Φ b) + (U_δi b + C b + (Demand.positions (List.ofFn πb) Ss b +
          Demand.positions (List.ofFn πb') Us b)) ≠ _
        rw [hlen₂] at hb
        rcases Heap.EnvClaims.bind_cases hb with ⟨l, hφl, hπl, hcl⟩ | ⟨j, hφj, hπj, hcl⟩ | hsc
        · -- The variable of an entry of the state that the branch owns alone.
          obtain ⟨hς1, hϱ1, hπ1⟩ := (by decide : ∀ x y z : Multiplicity, x * y * z = .one →
            x = .one ∧ y = .one ∧ z = .one) _ _ _ hφl
          obtain ⟨ϱ₁, hϱ₁', hϱle⟩ := hϱ₁ l
          obtain ⟨π₁, hπ₁', hπle⟩ := hπ₁ l
          rw [hϱ1, hπ1] at hϱle
          rw [hπ1] at hπle
          obtain rfl := (by decide : ∀ y : Multiplicity,
            Multiplicity.one * Multiplicity.one ≤ y * Multiplicity.one → y = .one) _ hϱle
          have hπ₁0 := (by decide : ∀ y : Multiplicity, y ≤ .one → y ≠ .zero) _ hπle
          obtain ⟨s_l, hsl⟩ : ∃ s_l, ss[(l : Nat)]? = some s_l :=
            ⟨_, List.getElem?_eq_getElem (hlb ▸ l.2)⟩
          have hπbl : (List.ofFn πb)[(l : Nat)]? = some Multiplicity.one := by
            rw [List.getElem?_ofFn]
            simp [hπ1]
          have hπsl : (List.ofFn πb ++ List.ofFn πb')[(l : Nat)]? = some Multiplicity.one := by
            rw [List.getElem?_append_left (by simp)]
            exact hπbl
          rcases hcl.cell_inv (hcell l _ s_l hπsl (by
            rw [List.getElem?_append_left (hlb ▸ l.2)]
            exact hsl)) with rfl | hcl'
          · exact hnew l hπsl
          · obtain ⟨S_l, hSl, hSal⟩ := hSs.getElem? hsl
            have hcl₀ := hcl'.of_extends hH' hgr (.inl ⟨_, hSal⟩)
            have h : F b + ((Demand.unit a b + (U_δc b +
                Demand.positions (πs₁.map Multiplicity.references) Ss b)) +
                Demand.positions (πs.map Multiplicity.references) Us b) ≠ .omega :=
              hca (ho₁ hς1) b (.state hlook hsl hπ₁' hπ₁0 hϱ₁' hcl₀)
            have hsl0 : S_l b ≠ .zero := hcl₀.reach_ne_zero.1 _ hSal
            have hp0 : Demand.positions (πs₁.map Multiplicity.references) Ss b ≠ .zero :=
              Demand.positions_ne_zero _ _ (by rw [List.getElem?_map, hπ₁']; rfl) hSl
                (Multiplicity.references_mul_ne_zero _ _ hπ₁0 hsl0)
            obtain ⟨hf, hd, hq, hpω⟩ := (by decide : ∀ f u d p q : Multiplicity,
              f + ((u + (d + p)) + q) ≠ .omega → p ≠ .zero →
              f = .zero ∧ d = .zero ∧ q = .zero ∧ p ≠ .omega) _ _ _ _ _ h hp0
            rw [hf, hΦ0 b hd,
              Multiplicity.eq_zero_of_le_of_eq_zero _ _
                (hle_i b) hd,
              hC0 b (hSal.lt hsl0), hU0 b hq,
              Demand.positions_eq_references_of_le πs₁ (List.ofFn πb) Ss hlS hπ₁L hπbl hSl hsl0
                hpω]
            exact (by decide : ∀ p : Multiplicity, p ≠ .omega →
              (.zero + .zero) + (.zero + .zero + (p + .zero)) ≠ .omega) _ hpω
        · -- The variable of an argument that the branch owns alone.
          obtain ⟨ho1, hπ1⟩ := Multiplicity.mul_eq_one _ _ hφj
          obtain ⟨π₂, hπ₂', hπle⟩ := hπ₂ j
          rw [hπ1] at hπle
          have hπ₂0 := (by decide : ∀ y : Multiplicity, y ≤ .one → y ≠ .zero) _ hπle
          obtain ⟨b_j, hbj⟩ : ∃ b_j, bs[(j : Nat)]? = some b_j :=
            ⟨_, List.getElem?_eq_getElem (hlc ▸ j.2)⟩
          have hosj : os[(j : Nat)]? = some Multiplicity.one := by
            rw [← ho1]
            exact List.getElem?_eq_getElem _
          have hπbj : (List.ofFn πb')[(j : Nat)]? = some Multiplicity.one := by
            rw [List.getElem?_ofFn]
            simp [hπ1]
          have hπsj : (List.ofFn πb ++ List.ofFn πb')[b' + (j : Nat)]? =
              some Multiplicity.one := by
            rw [List.getElem?_append_right (by simp)]
            simpa using hπbj
          rcases hcl.cell_inv (hcell (b' + j) _ b_j hπsj (by
            rw [List.getElem?_append_right (by omega), hlb, Nat.add_sub_cancel_left]
            exact hbj)) with rfl | hcl'
          · exact hnew (b' + j) hπsj
          · obtain ⟨U_j, hUj, hUbj⟩ := hbs.getElem? hbj
            have hcl₀ := hcl'.of_extends hH' hgr (.inl ⟨_, hUbj⟩)
            have h : F b + ((Demand.unit a b + (U_δc b +
                Demand.positions (πs₁.map Multiplicity.references) Ss b)) +
                Demand.positions (πs.map Multiplicity.references) Us b) ≠ .omega :=
              hcb b j b_j π₂ hbj hosj hπ₂' hπ₂0 hcl₀
            have huj0 : U_j b ≠ .zero := hcl₀.reach_ne_zero.1 _ hUbj
            have hq0 : Demand.positions (πs.map Multiplicity.references) Us b ≠ .zero :=
              Demand.positions_ne_zero _ _ (by rw [List.getElem?_map, hπ₂']; rfl) hUj
                (Multiplicity.references_mul_ne_zero _ _ hπ₂0 huj0)
            obtain ⟨hf, hd, hp, hqω⟩ := (by decide : ∀ f u d p q : Multiplicity,
              f + ((u + (d + p)) + q) ≠ .omega → q ≠ .zero →
              f = .zero ∧ d = .zero ∧ p = .zero ∧ q ≠ .omega) _ _ _ _ _ h hq0
            rw [hf, hΦ0 b hd,
              Multiplicity.eq_zero_of_le_of_eq_zero _ _
                (hle_i b) hd,
              hC0 b (hUbj.lt huj0), hS0 b hp,
              Demand.positions_eq_references_of_le πs (List.ofFn πb') Us hlU hπ₂L hπbj hUj huj0
                hqω]
            exact (by decide : ∀ q : Multiplicity, q ≠ .omega →
              (.zero + .zero) + (.zero + .zero + (.zero + q)) ≠ .omega) _ hqω
        · -- A variable of the scope that the branch owns alone and reads.
          obtain ⟨x, cx, hcx, hφx, hδx, hclx⟩ := hsc.of_extends hH' hgr hEi.toEnvReach
          obtain ⟨hς1, hφ1⟩ := Multiplicity.mul_eq_one _ _ hφx
          have hδcx : g.usage a n x ≠ .zero := (by decide : ∀ d di : Multiplicity, d ≤ di →
            di ≠ .zero → d ≠ .zero) _ _ (hδ x) hδx
          obtain ⟨hf, hd0, hdω, hp, hq, hk⟩ := hscope x cx b hcx hδcx hφ1 hclx (ho₁ hς1)
          have hΦb : Φ b = .zero := by
            rcases hΦ with ⟨-, rfl⟩ | ⟨hk', -⟩
            · rfl
            · exact absurd hk hk'
          rw [hf, hΦb, hC0 b (hEc.lt hd0), hS0 b hp, hU0 b hq]
          exact (by decide : ∀ d di : Multiplicity, d ≠ .zero → d ≠ .omega → d ≤ di →
            (.zero + .zero) + (di + .zero + (.zero + .zero)) ≠ .omega) _ _ hd0 hdω (hle_i b))
    have hgH := hgr.trans hH' hg₁₂
    have hH₁₂ := hH'.trans hw.extends
    have hwzero : ∀ b, b < H.length → (Demand.unit a b + (U_δc b +
        Demand.positions (πs₁.map Multiplicity.references) Ss b)) +
        Demand.positions (πs.map Multiplicity.references) Us b = .zero → U_w b = .zero :=
      fun b hb h0 => hA_N b (Nat.lt_of_lt_of_le hb hH'.length_le) (hzeroN b hb h0)
    -- The resumption of the value of the branch.
    cases hr with
    | none =>
      refine ⟨g₂, U_w, hgH, hg₂, hUw, hwzero, fun ho b hb => ?_⟩
      rcases hvN with ⟨-, rfl⟩ | ⟨hk, -⟩
      · rcases hΦ with ⟨-, rfl⟩ | ⟨hk, -⟩
        · have h : (F b + Multiplicity.zero) + U_w b ≠ .omega := hB_N
            (Multiplicity.mul_eq_one _ _ ho).2 b hb
          exact (by decide : ∀ f x : Multiplicity, f + .zero + x ≠ .omega → f + x ≠ .omega)
            _ _ h
        · exact absurd rfl hk
      · exact absurd rfl hk
    | next hlw hs =>
      rename_i π ϱ πsn ϱsn k₀ x ss'
      have hk : Resumption.unpack k₀ ≠ .none := nofun
      obtain ⟨Xs, hXs, rfl, -⟩ := hUw.ctor_inv hlw
      obtain _ | ⟨hx, hXs⟩ := hXs
      cases hXs
      obtain ⟨Ss', Z, hSs', rfl⟩ := hs.reach hx
      have hdec : Demand.unit w +ᶜ Demand.positions ([π].map Multiplicity.references)
            [Demand.positions (πsn.map Multiplicity.references) Ss' +ᶜ Z] =
          Demand.positions ((πsn.map (π * ·)).map Multiplicity.references) Ss' +ᶜ
            (Demand.unit w +ᶜ π.references ·ᶜ Z) := by
        simp only [List.map_cons, List.map_nil, Demand.positions, Multiplicity.map_references_mul,
          Demand.positions_map_mul, Demand.add_zero, Demand.smul_add]
        ac_rfl
      rw [hdec] at hUw hwzero hB_N
      have hH₂₃ : H₂.Extends (H₂ ++ [.corec n Ec Ps (πsn.map (π * ·)) (ϱsn.map (ϱ * ·)) ss']) :=
        List.prefix_append _ _
      have hgs := Heap.Annotation.set_extends H₂ g₂ n (g.ownership a n) (g.usage a n)
      have hg₃ := hgH.trans hH₁₂ hgs
      have hEc₃ : Heap.EnvReach (H₂ ++ [.corec n Ec Ps (πsn.map (π * ·)) (ϱsn.map (ϱ * ·)) ss'])
          (g₂.set H₂.length n (g.ownership a n) (g.usage a n)) Ec
          ((g₂.set H₂.length n (g.ownership a n) (g.usage a n)).usage H₂.length n) U_δc := by
        rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).2]
        exact hEc.mono (hH₁₂.trans hH₂₃) hg₃
      have hvk : vN = .one := by
        rcases hvN with ⟨hk', -⟩ | ⟨-, rfl⟩
        · exact absurd hk' hk
        · rfl
      have hΦk : Φ = U_δc := by
        rcases hΦ with ⟨hk', -⟩ | ⟨-, rfl⟩
        · exact absurd hk' hk
        · rfl
      rw [hΦk] at hB_N
      refine ⟨_, _, hg₃, hg₂.concat_corec hval₁ hval₂,
        .corec List.getElem?_concat_length hEc₃ (Heap.PositionsReach.of_forall₂
          (hSs'.imp fun _ _ h => h.mono hH₂₃ hgs) (by simp [hs.length])),
        fun b hb h0 => ?_, fun ho b hb => ?_⟩
      · have hw0 : Demand.positions ((πsn.map (π * ·)).map Multiplicity.references) Ss' b +
            (Demand.unit w b + π.references * Z b) = .zero := hwzero b hb h0
        have hd := (by decide : ∀ u d p q : Multiplicity, (u + (d + p)) + q = .zero →
          d = .zero) _ _ _ _ h0
        show Demand.unit H₂.length b + (U_δc b + _) = _
        rw [hd, Multiplicity.add_eq_zero_left _ _ hw0]
        have : b ≠ H₂.length := Nat.ne_of_lt (Nat.lt_of_lt_of_le hb hH₁₂.length_le)
        simp [Demand.unit, this] <;> decide
      · have ho1 := (Multiplicity.mul_eq_one _ _ ho).1
        show F b + (Demand.unit H₂.length b + (U_δc b +
          Demand.positions ((πsn.map (π * ·)).map Multiplicity.references) Ss' b)) ≠ _
        by_cases hbℓ : b = H₂.length
        · subst hbℓ
          rw [hF _ hH₁₂.length_le, hEc.eq_zero _ hH₁₂.length_le, Demand.positions_eq_zero _ _
            (Heap.ValueReach.pointwise_eq_zero hSs' (Nat.le_refl _))]
          simp [Demand.unit] <;> decide
        · have hu0 : Demand.unit H₂.length b = .zero := by simp [Demand.unit, hbℓ]
          rw [hu0]
          cases hb with
          | self => exact absurd rfl hbℓ
          | ctor h' | cell h' => cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
          | state h' hsj hπj hπ₀ hϱj hb' =>
            cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
            rw [List.getElem?_map] at hπj hϱj
            obtain ⟨π₃, hπ₃, rfl⟩ := Option.map_eq_some_iff.1 hπj
            obtain ⟨ϱ₃, hϱ₃, hϱe⟩ := Option.map_eq_some_iff.1 hϱj
            obtain ⟨rfl, rfl⟩ := Multiplicity.mul_eq_one _ _ hϱe
            obtain ⟨S, -, hS⟩ := hSs'.getElem? hsj
            have hclx := hs.claims hsj hπ₃
              ((by decide : ∀ x y : Multiplicity, x * y ≠ .zero → y ≠ .zero) _ _ hπ₀) hϱ₃
              (hb'.of_extends hH₂₃ hgs (.inl ⟨_, hS⟩))
            have h : (F b + U_δc b) +
                (Demand.positions ((πsn.map (π * ·)).map Multiplicity.references) Ss' b +
                  (Demand.unit w b + π.references * Z b)) ≠ .omega :=
              hB_N hvk b (.ctor hlw (k := 0) rfl rfl
                ((by decide : ∀ x y : Multiplicity, x * y ≠ .zero → x ≠ .zero) _ _ hπ₀) rfl hclx)
            exact (by decide : ∀ f d p z : Multiplicity, (f + d) + (p + z) ≠ .omega →
              f + (.zero + (d + p)) ≠ .omega) _ _ _ _ h
          | scope x h' hcx hδx hφx hb' =>
            cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
            rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).2] at hδx
            rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).1] at hφx
            obtain ⟨-, -, -, -, -, hk'⟩ := hscope x _ b hcx hδx hφx
              (hb'.of_extends (hH₁₂.trans hH₂₃) hg₃ (.inr (hEc.get x hcx))) ho1
            exact absurd hk' hk
    | erased hlw =>
      rename_i ϱ k₀ x
      have hk : Resumption.erased k₀ ≠ .none := nofun
      obtain ⟨Xs, hXs, -, -⟩ := hUw.ctor_inv hlw
      obtain _ | ⟨hx, hXs⟩ := hXs
      have hH₂₃ : H₂.Extends (H₂ ++ [.corec n Ec Ps (List.replicate k₀ .zero)
          (List.replicate k₀ .zero) (List.replicate k₀ x)]) := List.prefix_append _ _
      have hgs := Heap.Annotation.set_extends H₂ g₂ n (g.ownership a n) (g.usage a n)
      have hg₃ := hgH.trans hH₁₂ hgs
      have hEc₃ : Heap.EnvReach (H₂ ++ [.corec n Ec Ps (List.replicate k₀ .zero)
            (List.replicate k₀ .zero) (List.replicate k₀ x)])
          (g₂.set H₂.length n (g.ownership a n) (g.usage a n)) Ec
          ((g₂.set H₂.length n (g.ownership a n) (g.usage a n)).usage H₂.length n) U_δc := by
        rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).2]
        exact hEc.mono (hH₁₂.trans hH₂₃) hg₃
      have hP0 : ∀ (D : Demand) b, Demand.positions ((List.replicate k₀ Multiplicity.zero).map
          Multiplicity.references) (List.replicate k₀ D) b = .zero := fun D b => by
        rw [List.map_replicate, show Multiplicity.zero.references = .zero from rfl,
          Demand.positions_replicate_zero]
        rfl
      refine ⟨_, _, hg₃, hg₂.concat_corec hval₁ hval₂,
        .corec List.getElem?_concat_length hEc₃ (Heap.PositionsReach.of_forall₂
          (List.Pointwise.replicate (hx.mono hH₂₃ hgs) k₀) (by simp)),
        fun b hb h0 => ?_, fun ho b hb => ?_⟩
      · have hd := (by decide : ∀ u d p q : Multiplicity, (u + (d + p)) + q = .zero →
          d = .zero) _ _ _ _ h0
        show Demand.unit H₂.length b + (U_δc b + _) = _
        rw [hd, hP0 _ b]
        have : b ≠ H₂.length := Nat.ne_of_lt (Nat.lt_of_lt_of_le hb hH₁₂.length_le)
        simp [Demand.unit, this] <;> decide
      · have ho1 := (Multiplicity.mul_eq_one _ _ ho).1
        show F b + (Demand.unit H₂.length b + (U_δc b + _)) ≠ _
        rw [hP0 _ b]
        by_cases hbℓ : b = H₂.length
        · subst hbℓ
          rw [hF _ hH₁₂.length_le, hEc.eq_zero _ hH₁₂.length_le]
          simp [Demand.unit] <;> decide
        · cases hb with
          | self => exact absurd rfl hbℓ
          | ctor h' | cell h' => cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
          | state h' hsj hπj hπ₀ hϱj hb' =>
            cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
            rw [List.getElem?_replicate] at hπj
            split at hπj
            · cases hπj
              exact absurd rfl hπ₀
            · cases hπj
          | scope x' h' hcx hδx hφx hb' =>
            cases (List.getElem?_concat_length (l := H₂)).symm.trans h'
            rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).2] at hδx
            rw [(Heap.Annotation.set_self g₂ H₂.length n _ _).1] at hφx
            obtain ⟨-, -, -, -, -, hk'⟩ := hscope x' _ b hcx hδx hφx
              (hb'.of_extends (hH₁₂.trans hH₂₃) hg₃ (.inr (hEc.get x' hcx))) ho1
            exact absurd hk' hk
    | done hk hlw hπw hϱw =>
      rename_i π ϱ
      obtain ⟨Xs, hXs, rfl, -⟩ := hUw.ctor_inv hlw
      obtain _ | ⟨hx, hXs⟩ := hXs
      cases hXs
      rename_i U_x
      refine ⟨g₂, U_x, hgH, hg₂, hx, fun b hb h0 => ?_, fun ho b hb => ?_⟩
      · have hw0 : Demand.unit w b + (π.references * U_x b + .zero) = .zero := hwzero b hb h0
        exact (by decide : ∀ uw π x : Multiplicity, π ≠ .zero →
          uw + (π.references * x + .zero) = .zero → x = .zero) _ _ _ hπw hw0
      · have hu1 := (Multiplicity.mul_eq_one _ _ ho).2
        obtain ⟨χ, hψχ⟩ := hψc hk
        rw [hψχ] at hu' hϱw
        rw [ResultOwnership.value_const] at hu'
        cases hu'
        have hϱ1 : ϱ = .one := Multiplicity.eq_one_of_one_le _ (hu1 ▸ hϱw)
        have hvk : vN = .one := by
          rcases hvN with ⟨hk', -⟩ | ⟨-, rfl⟩
          · exact absurd hk' hk
          · rfl
        have h : (F b + Φ b) + (Demand.unit w b + (π.references * U_x b + .zero)) ≠ .omega :=
          hB_N hvk b (.ctor hlw (k := 0) rfl rfl hπw (by rw [hϱ1]; rfl) hb)
        exact (by decide : ∀ f d uw π x : Multiplicity, π ≠ .zero →
          (f + d) + (uw + (π.references * x + .zero)) ≠ .omega → f + x ≠ .omega)
          _ _ _ _ _ hπw h
termination_by structural h

end

/-! ## Uniqueness -/

/-- `uniq_⇓`: the value of a term owned alone is referred to by no frame of the heap: a frame that
refers once at most, with the environment, to each address that the term claims through its
environment does not refer to the address of the value of the term.
RFC: `\mathsf{uniq}_\Downarrow` -/
theorem Eval.uniqueness {P : Program} {Ω : Name → Multiplicity} (hΩ : P.Ownership Ω)
    (hP : P.Usage) {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {M : Target n}
    {a : Nat} {R : List Nat} (h : Eval P ϖ H E M a H' R) {φ ν : MultiplicityVector n}
    (hM : Target.Ownership Ω φ .one M) (hν : Target.Usage ν M) {g : Heap.Annotation}
    (hg : g.Valid Ω H) {U_E : Demand} (hE : Heap.EnvReach H g E ν U_E) {F : Demand}
    (hF : ∀ b, H.length ≤ b → F b = .zero)
    (hc : ∀ b, Heap.EnvClaims H g E φ ν b → F b + U_E b ≠ .omega) : F a = .zero := by
  obtain ⟨g', U, -, -, hU, -, hB⟩ := Eval.reach hΩ hP h hM hν hg hE hF hc
  exact (by decide : ∀ f u : Multiplicity, f + u ≠ .omega → u ≠ .zero → f = .zero) _ _
    (hB rfl a (.self a)) ((Heap.Claims.self a).reach_ne_zero.1 U hU)

end Sic.Core
