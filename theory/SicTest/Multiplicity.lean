module

public import Sic.Multiplicity

/-!
# Multiplicities

The definitions of `Sic.Multiplicity` checked against RFC 24, entry by entry, and against their
meaning.
-/

@[expose] public section

namespace SicTest.Multiplicity

open Sic Sic.Multiplicity

/-! The tables of RFC 24, entry by entry, so that a difference with them fails to build. -/

example : zero  + zero  = zero  := rfl
example : zero  + one   = one   := rfl
example : zero  + omega = omega := rfl
example : one   + zero  = one   := rfl
example : one   + one   = omega := rfl
example : one   + omega = omega := rfl
example : omega + zero  = omega := rfl
example : omega + one   = omega := rfl
example : omega + omega = omega := rfl

example : zero  * zero  = zero  := rfl
example : zero  * one   = zero  := rfl
example : zero  * omega = zero  := rfl
example : one   * zero  = zero  := rfl
example : one   * one   = one   := rfl
example : one   * omega = omega := rfl
example : omega * zero  = zero  := rfl
example : omega * one   = omega := rfl
example : omega * omega = omega := rfl

example : zero  ⊓ zero  = zero  := rfl
example : zero  ⊓ one   = omega := rfl
example : zero  ⊓ omega = omega := rfl
example : one   ⊓ zero  = omega := rfl
example : one   ⊓ one   = one   := rfl
example : one   ⊓ omega = omega := rfl
example : omega ⊓ zero  = omega := rfl
example : omega ⊓ one   = omega := rfl
example : omega ⊓ omega = omega := rfl

/-! The order of RFC 24: `ω` is below `0` and `1`, which are not comparable. -/

example : omega ≤ zero := by decide
example : omega ≤ one := by decide
example : ¬ zero ≤ one := by decide
example : ¬ one ≤ zero := by decide

/-!
The meaning of the multiplicities, from which the tables follow: a multiplicity allows some numbers
of uses, and each operation gives the best multiplicity for the results of the same operation on
numbers (`IsBest`): it is sound, allowing every result, and precise, allowing the fewest numbers
among the sound ones. The order follows too: `u ≤ v` when `u` allows every number that `v` allows.
-/

/-- The numbers of uses that a multiplicity allows. -/
def Allows : Multiplicity → Nat → Prop
  | zero, n => n = 0
  | one, n => n = 1
  | omega, _ => True

/--
`u` is the multiplicity that best describes the numbers that `S` holds of: it allows all of them,
and any multiplicity that allows all of them allows everything `u` allows.
-/
def IsBest (S : Nat → Prop) (u : Multiplicity) : Prop :=
  (∀ n, S n → Allows u n) ∧ ∀ w, (∀ n, S n → Allows w n) → ∀ n, Allows u n → Allows w n

/-!
Precision is proved the same way for each operation: a sound multiplicity allows in particular the
result of the operation on the witnesses below, one number per multiplicity, and that single fact
decides, for each of the three multiplicities, whether it is at most the result or contradicts the
hypothesis.
-/

/-- A number of uses that `u` allows, such that every multiplicity allowing it is at most `u`. -/
def witness (u : Multiplicity) : Nat :=
  match u with
  | zero => 0
  | one => 1
  | omega => 2

theorem allows_witness (u : Multiplicity) : Allows u (witness u) := by
  cases u <;> first | rfl | trivial

theorem add_sound {u v : Multiplicity} {a b : Nat} :
    Allows u a → Allows v b → Allows (u + v) (a + b) := by
  cases u <;> cases v <;> intro ha hb <;> simp only [Allows] at ha hb <;> subst_vars <;>
    first | trivial | rfl

theorem add_precise {u v w : Multiplicity} (h : ∀ a b, Allows u a → Allows v b → Allows w (a + b)) :
    ∀ n, Allows (u + v) n → Allows w n := by
  have hw := h _ _ (allows_witness u) (allows_witness v)
  intro n hn
  cases u <;> cases v <;> cases w <;> first | trivial | exact hn | simp [Allows, witness] at hw

theorem add_best (u v : Multiplicity) :
    IsBest (fun n => ∃ a b, Allows u a ∧ Allows v b ∧ n = a + b) (u + v) :=
  ⟨fun _ ⟨_, _, ha, hb, h⟩ => h ▸ add_sound ha hb,
    fun _ hw => add_precise fun _ _ ha hb => hw _ ⟨_, _, ha, hb, rfl⟩⟩

theorem mul_sound {u v : Multiplicity} {a b : Nat} :
    Allows u a → Allows v b → Allows (u * v) (a * b) := by
  cases u <;> cases v <;> intro ha hb <;> simp only [Allows] at ha hb <;> subst_vars <;>
    first | trivial | rfl | (simp only [Nat.zero_mul]; rfl)

theorem mul_precise {u v w : Multiplicity} (h : ∀ a b, Allows u a → Allows v b → Allows w (a * b)) :
    ∀ n, Allows (u * v) n → Allows w n := by
  have hw := h _ _ (allows_witness u) (allows_witness v)
  intro n hn
  cases u <;> cases v <;> cases w <;> first | trivial | exact hn | simp [Allows, witness] at hw

theorem mul_best (u v : Multiplicity) :
    IsBest (fun n => ∃ a b, Allows u a ∧ Allows v b ∧ n = a * b) (u * v) :=
  ⟨fun _ ⟨_, _, ha, hb, h⟩ => h ▸ mul_sound ha hb,
    fun _ hw => mul_precise fun _ _ ha hb => hw _ ⟨_, _, ha, hb, rfl⟩⟩

theorem min_sound {u v : Multiplicity} {a : Nat} : Allows u a ∨ Allows v a → Allows (u ⊓ v) a := by
  cases u <;> cases v <;> intro h <;> simp only [Allows, or_self] at h <;> first | trivial | exact h

theorem min_precise {u v w : Multiplicity} (h : ∀ a, Allows u a ∨ Allows v a → Allows w a) :
    ∀ n, Allows (u ⊓ v) n → Allows w n := by
  have hu := h _ (.inl (allows_witness u))
  have hv := h _ (.inr (allows_witness v))
  intro n hn
  cases u <;> cases v <;> cases w <;> first | trivial | exact hn | simp [Allows, witness] at hu hv

theorem min_best (u v : Multiplicity) : IsBest (fun n => Allows u n ∨ Allows v n) (u ⊓ v) :=
  ⟨fun _ h => min_sound h, fun _ hw => min_precise hw⟩

theorem le_iff {u v : Multiplicity} : u ≤ v ↔ ∀ n, Allows v n → Allows u n := by
  constructor
  · intro h n hn
    rw [show u = u ⊓ v from h]
    exact min_sound (.inr hn)
  · intro h
    have := h _ (allows_witness v)
    cases u <;> cases v <;> first | rfl | simp [Allows, witness] at this

end SicTest.Multiplicity
