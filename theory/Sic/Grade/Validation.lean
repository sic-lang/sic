import Sic.Grade
import Sic.Usage.Validation

/-!
# Validation of the Grades

The definitions of `Sic.Grade` checked against RFC 24 and against their meaning.
-/

namespace Sic.Grade.Validation

open Usage.Validation (witness)

/-- The grade of the usages `r` at run time and `t` in total, written as in RFC 24. -/
local notation "⟪" r ", " t "⟫" => (Grade.mk r t (by decide) : Grade)

/-! The claims and examples of RFC 24. -/

/-- Of the nine pairs of usages, the grades exclude exactly `⟨1, 0⟩` and `⟨ω, 0⟩`. -/
example : ∀ r t : Usage,
    ¬(t = .zero → r = .zero) ↔ (r, t) = (.one, .zero) ∨ (r, t) = (.omega, .zero) := by
  decide

/-!
Without `⟨ω, 1⟩`, the meet `⟨0, 1⟩ ⊓ 𝟙` would be `⟨ω, ω⟩`, and the two sides of the distributivity
`⟨0, 1⟩ * (⟨0, 1⟩ ⊓ 𝟙) = (⟨0, 1⟩ * ⟨0, 1⟩) ⊓ (⟨0, 1⟩ * 𝟙)` would differ: `⟨0, ω⟩` on the left, with
this value of the meet, and `⟨0, 1⟩` on the right.
-/
example : ⟪.zero, .one⟫ * ⟪.omega, .omega⟫ = ⟪.zero, .omega⟫ := rfl
example : (⟪.zero, .one⟫ * ⟪.zero, .one⟫) ⊓ (⟪.zero, .one⟫ * 𝟙) = ⟪.zero, .one⟫ := rfl

/-! The excluded pairs would break the zero: a product of each with `⟨0, 1⟩` has no use at all. -/
example : ((.one * .zero, .zero * .one) : Usage × Usage) = (.zero, .zero) := rfl
example : ((.omega * .zero, .zero * .one) : Usage × Usage) = (.zero, .zero) := rfl

/-! The meet of `⟨0, 1⟩` and `𝟙`, and the permission of grade `none / linear` passed once. -/
example : ⟪.zero, .one⟫ ⊓ 𝟙 = ⟪.omega, .one⟫ := rfl
example : ⟪.zero, .one⟫ * 𝟙 = ⟪.zero, .one⟫ := rfl

/-!
The meaning of the grades: a grade allows some numbers of uses at run time and in total, those its
usages allow, the uses at run time being among all the uses.
As for the usages, each operation gives the best grade (`IsBest`), and the order is the inclusion;
the meet of `⟨0, 1⟩` and `𝟙` above, `⟨ω, 1⟩`, is thus the grade that allows exactly their uses.
-/

/-- The numbers of uses, at run time and in total, that a grade allows. -/
def Allows (p : Grade) (r t : Nat) : Prop :=
  Usage.Validation.Allows p.run r ∧ Usage.Validation.Allows p.total t ∧ r ≤ t

/--
`p` is the grade that best describes the numbers of uses that `S` holds of: it allows all of them,
and any grade that allows all of them allows everything `p` allows.
-/
def IsBest (S : Nat → Nat → Prop) (p : Grade) : Prop :=
  (∀ r t, S r t → Allows p r t) ∧
    ∀ w, (∀ r t, S r t → Allows w r t) → ∀ r t, Allows p r t → Allows w r t

/-!
How precision is proved. A sound grade `w` allows in particular the results of the operation on the
witnesses below, two pairs of numbers of uses per grade, chosen so that a grade allowing both is at
most the grade they come from. Those few facts on `w` decide its usages: for each of the finitely
many grades `p`, `q` and `w`, either the usages of `w` are at most those of the result, and
`allows_of_le` turns this order into the inclusion, or `w` fails to allow one of the results on the
witnesses, a contradiction. `cases_grades` goes through these cases, which only computation closes.
-/

/--
Two pairs of numbers of uses that `p` allows, such that every grade allowing both is at most `p`.
-/
def witnesses (p : Grade) : (Nat × Nat) × (Nat × Nat) :=
  let r := Nat.min (witness p.run) (witness p.total)
  ((r, witness p.total), (if p.run = .omega then 0 else r, witness p.total))

/--
Proves a statement on grades by cases on the usages of each, refuting the two excluded pairs; each
case closes by computation (`rfl`), or by simplifying the hypotheses on the witnesses to `False`.
-/
local macro "cases_grades " ps:ident* : tactic => do
  let mut tac ← `(tactic| skip)
  for p in ps do
    tac ← `(tactic| ($tac <;> (obtain ⟨r, t, h⟩ := $p:ident; cases r <;> cases t <;>
      try exact absurd (h rfl) (by decide))))
  `(tactic| ($tac <;> first | rfl | simp_all [witnesses, witness, Allows, Usage.Validation.Allows]))

theorem allows_witnesses (p : Grade) :
    Allows p (witnesses p).1.1 (witnesses p).1.2 ∧
      Allows p (witnesses p).2.1 (witnesses p).2.2 := by
  cases_grades p

theorem allows_of_le {p w : Grade} (hr : w.run = w.run ⊓ p.run) (ht : w.total = w.total ⊓ p.total) :
    ∀ r t, Allows p r t → Allows w r t :=
  fun _ _ ⟨hpr, hpt, h⟩ =>
    ⟨Usage.Validation.le_iff.1 hr _ hpr, Usage.Validation.le_iff.1 ht _ hpt, h⟩

theorem add_sound {p q : Grade} {r₁ t₁ r₂ t₂ : Nat} :
    Allows p r₁ t₁ → Allows q r₂ t₂ → Allows (p + q) (r₁ + r₂) (t₁ + t₂) :=
  fun ⟨hr₁, ht₁, h₁⟩ ⟨hr₂, ht₂, h₂⟩ =>
    ⟨Usage.Validation.add_sound hr₁ hr₂, Usage.Validation.add_sound ht₁ ht₂, Nat.add_le_add h₁ h₂⟩

theorem add_precise {p q w : Grade}
    (h : ∀ r₁ t₁ r₂ t₂, Allows p r₁ t₁ → Allows q r₂ t₂ → Allows w (r₁ + r₂) (t₁ + t₂)) :
    ∀ r t, Allows (p + q) r t → Allows w r t := by
  have ⟨p₁, p₂⟩ := allows_witnesses p
  have ⟨q₁, q₂⟩ := allows_witnesses q
  have := h _ _ _ _ p₁ q₁; have := h _ _ _ _ p₁ q₂; have := h _ _ _ _ p₂ q₁; have := h _ _ _ _ p₂ q₂
  clear h p₁ p₂ q₁ q₂
  apply allows_of_le <;> cases_grades p q w

theorem add_best (p q : Grade) :
    IsBest (fun r t => ∃ r₁ t₁ r₂ t₂, Allows p r₁ t₁ ∧ Allows q r₂ t₂ ∧ r = r₁ + r₂ ∧ t = t₁ + t₂)
      (p + q) :=
  ⟨fun _ _ ⟨_, _, _, _, h₁, h₂, hr, ht⟩ => hr ▸ ht ▸ add_sound h₁ h₂,
    fun _ hw => add_precise fun _ _ _ _ h₁ h₂ => hw _ _ ⟨_, _, _, _, h₁, h₂, rfl, rfl⟩⟩

theorem mul_sound {p q : Grade} {r₁ t₁ r₂ t₂ : Nat} :
    Allows p r₁ t₁ → Allows q r₂ t₂ → Allows (p * q) (r₁ * r₂) (t₁ * t₂) :=
  fun ⟨hr₁, ht₁, h₁⟩ ⟨hr₂, ht₂, h₂⟩ =>
    ⟨Usage.Validation.mul_sound hr₁ hr₂, Usage.Validation.mul_sound ht₁ ht₂, Nat.mul_le_mul h₁ h₂⟩

theorem mul_precise {p q w : Grade}
    (h : ∀ r₁ t₁ r₂ t₂, Allows p r₁ t₁ → Allows q r₂ t₂ → Allows w (r₁ * r₂) (t₁ * t₂)) :
    ∀ r t, Allows (p * q) r t → Allows w r t := by
  have ⟨p₁, p₂⟩ := allows_witnesses p
  have ⟨q₁, q₂⟩ := allows_witnesses q
  have := h _ _ _ _ p₁ q₁; have := h _ _ _ _ p₁ q₂; have := h _ _ _ _ p₂ q₁; have := h _ _ _ _ p₂ q₂
  clear h p₁ p₂ q₁ q₂
  apply allows_of_le <;> cases_grades p q w

theorem mul_best (p q : Grade) :
    IsBest (fun r t => ∃ r₁ t₁ r₂ t₂, Allows p r₁ t₁ ∧ Allows q r₂ t₂ ∧ r = r₁ * r₂ ∧ t = t₁ * t₂)
      (p * q) :=
  ⟨fun _ _ ⟨_, _, _, _, h₁, h₂, hr, ht⟩ => hr ▸ ht ▸ mul_sound h₁ h₂,
    fun _ hw => mul_precise fun _ _ _ _ h₁ h₂ => hw _ _ ⟨_, _, _, _, h₁, h₂, rfl, rfl⟩⟩

theorem min_sound {p q : Grade} {r t : Nat} : Allows p r t ∨ Allows q r t → Allows (p ⊓ q) r t
  | .inl ⟨hr, ht, h⟩ =>
    ⟨Usage.Validation.min_sound (.inl hr), Usage.Validation.min_sound (.inl ht), h⟩
  | .inr ⟨hr, ht, h⟩ =>
    ⟨Usage.Validation.min_sound (.inr hr), Usage.Validation.min_sound (.inr ht), h⟩

theorem min_precise {p q w : Grade} (h : ∀ r t, Allows p r t ∨ Allows q r t → Allows w r t) :
    ∀ r t, Allows (p ⊓ q) r t → Allows w r t := by
  have ⟨p₁, p₂⟩ := allows_witnesses p
  have ⟨q₁, q₂⟩ := allows_witnesses q
  have := h _ _ (.inl p₁); have := h _ _ (.inl p₂); have := h _ _ (.inr q₁); have := h _ _ (.inr q₂)
  clear h p₁ p₂ q₁ q₂
  apply allows_of_le <;> cases_grades p q w

theorem min_best (p q : Grade) : IsBest (fun r t => Allows p r t ∨ Allows q r t) (p ⊓ q) :=
  ⟨fun _ _ h => min_sound h, fun _ hw => min_precise hw⟩

theorem le_iff {p q : Grade} : p ≤ q ↔ ∀ r t, Allows q r t → Allows p r t := by
  constructor
  · intro h r t hq
    rw [show p = p ⊓ q from h]
    exact min_sound (.inr hq)
  · intro h
    have ⟨q₁, q₂⟩ := allows_witnesses q
    have := h _ _ q₁; have := h _ _ q₂
    clear h q₁ q₂
    show p = p ⊓ q
    cases_grades p q

end Sic.Grade.Validation
