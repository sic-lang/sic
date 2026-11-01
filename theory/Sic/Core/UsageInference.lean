module

public import Sic.Core.Usage

/-!
# Usage Inference

The usage that a term infers, `⌈t⌉[m]`, which is the greatest of its usages in the mode `m`, and the
condition `Usable m t` on the grades of its binders, under which it has one: a term is well used
with the vector `γ` exactly when it is usable and `γ` is below the usage that it infers, so that the
usage is decidable.

## Correspondence with the Formalization of ADE

ADE infer the same usage, `⌈ t ⌉ m`, and prove that it bounds every usage, `usage-upper-bound`, and
that it is a usage of every term that has one, `usage-inf`, through a lemma that exchanges the grade
of a variable between two usages of a term, `Conₘ-interchange`.
Their usage is decided by a separate function, `⌈⌉▸[_]?_`, which checks the grade of each binder of
the term against the usage that its body infers.
Here, these checks are a definition, `Usable`, under which the inferred usage is a usage of the term
by induction on the term alone, so that no exchange lemma is needed, and the decision follows from
the characterization `usage_iff`.
-/

@[expose] public section

namespace Sic.Core

open Grade GradeVector Mode Term

-- ADE: `⌈_⌉`, in `Graded/Usage.agda`.
/--
`⌈t⌉[m]`: the usage that the term `t` infers in the mode `m`, from the rules of `Sic.Core.Usage`
without `(sub)`, whatever the grades of its binders.
-/
def Term.usage : Term k n → Mode → GradeVector n
  | var x, m => (𝟘ᶜ, x ≔ ⌜m⌝)
  | univ _, _ => 𝟘ᶜ
  | pi p _ A B, m => (p • A.usage (m ⊙ p)) + tail (B.usage m)
  | lam _ _ t, m => tail (t.usage m)
  | app p t a, m => t.usage m + (p • a.usage (m ⊙ p))

@[inherit_doc] notation:max "⌈" t "⌉[" m "]" => Term.usage t m

-- ADE: none.
/--
`Usable m t`: the grade of each binder of `t` is below the usage of its variable that the body
infers, as the rules `(Π_m)` and `(λ_m)` require.
-/
def Usable : Mode → Term k n → Prop
  | _, var _ => True
  | _, univ _ => True
  | m, pi p q A B => Usable (m ⊙ p) A ∧ Usable m B ∧ (⌜m⌝ * q) ≤ head ⌈B⌉[m]
  | m, lam p _ t => Usable m t ∧ (⌜m⌝ * p) ≤ head ⌈t⌉[m]
  | m, app p t a => Usable m t ∧ Usable (m ⊙ p) a

-- ADE: `⌈⌉▸[_]?_`, in `Graded/Usage/Decidable.agda`.
/-- `Usable` is decided by checking the grade of each binder. -/
instance Usable.decidable : (m : Mode) → (t : Term k n) → Decidable (Usable m t)
  | _, var _ => isTrue trivial
  | _, univ _ => isTrue trivial
  | m, pi p _ A B =>
    have := Usable.decidable (m ⊙ p) A
    have := Usable.decidable m B
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | m, lam _ _ t =>
    have := Usable.decidable m t
    inferInstanceAs (Decidable (_ ∧ _))
  | m, app p t a =>
    have := Usable.decidable m t
    have := Usable.decidable (m ⊙ p) a
    inferInstanceAs (Decidable (_ ∧ _))

-- ADE: `usage-upper-bound`, in `Graded/Usage/Properties.agda`.
/-- The inferred usage bounds every usage of the term. -/
theorem Usage.le_usage : γ ▶[m] t → γ ≤ ⌈t⌉[m]
  | .sub h hγ => GradeVector.le_trans hγ h.le_usage
  | .var | .univ => GradeVector.le_refl _
  | .pi hA hB => add_mono (smul_mono (Grade.le_refl _) hA.le_usage) (tail_mono hB.le_usage)
  | .lam ht => tail_mono ht.le_usage
  | .app ht ha => add_mono ht.le_usage (smul_mono (Grade.le_refl _) ha.le_usage)

-- ADE: none.
/-- A term that has a usage is usable: the grade of each binder is below the uses of its variable. -/
theorem Usage.usable : γ ▶[m] t → Usable m t
  | .sub h _ => h.usable
  | .var | .univ => trivial
  | .pi hA hB => ⟨hA.usable, hB.usable, hB.le_usage 0⟩
  | .lam ht => ⟨ht.usable, ht.le_usage 0⟩
  | .app ht ha => ⟨ht.usable, ha.usable⟩

-- ADE: none.
/-- The usage that a usable term infers is a usage of the term. -/
theorem Usable.usage : {m : Mode} → {t : Term k n} → Usable m t → ⌈t⌉[m] ▶[m] t
  | _, var _, _ => .var
  | _, univ _, _ => .univ
  | _, pi .., h => .pi h.1.usage (.sub h.2.1.usage (cons_tail_le h.2.2))
  | _, lam .., h => .lam (.sub h.1.usage (cons_tail_le h.2))
  | _, app .., h => .app h.1.usage h.2.usage

-- ADE: `usage-inf`, in `Graded/Usage/Properties.agda`.
/-- The usage that a term infers is a usage of the term, as soon as the term has one. -/
theorem Usage.usage_inf (h : γ ▶[m] t) : ⌈t⌉[m] ▶[m] t :=
  h.usable.usage

-- ADE: none.
/-- A term is well used with `γ` exactly when it is usable and `γ` is below its inferred usage. -/
theorem usage_iff : γ ▶[m] t ↔ Usable m t ∧ γ ≤ ⌈t⌉[m] :=
  ⟨fun h => ⟨h.usable, h.le_usage⟩, fun ⟨h, hγ⟩ => .sub h.usage hγ⟩

-- ADE: `_▸[_]?_`, in `Graded/Usage/Decidable.agda`.
/-- The usage is decided by the inferred usage, through `usage_iff`. -/
instance Usage.decidable (γ : GradeVector n) (m : Mode) (t : Term k n) : Decidable (γ ▶[m] t) :=
  decidable_of_iff _ usage_iff.symm

end Sic.Core
