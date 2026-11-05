module

public import Sic.Core.Erasure
public import Sic.Core.Reduction

/-!
# Constants and a Definition

The annex `constants-and-a-definition` of RFC 24: since the core names no type, a signature of the
core alone declares types and values as constants, a foreign type `Int` and its value `zero`, a
ghost value `bound`, a foreign proposition `Sorted` and its axiom `sorted`, and a definition
`origin`, which unfolds to `zero`.
The formulas `(ex_sig)` and `(ex_use)` are derived from the rules of the core, and the program
`origin.{}` computes to `zero.{}` and is extracted to `origin`, as the annex says in prose.
-/

@[expose] public section

namespace SicExample.Core

open Sic Sic.Core

/-- `Int.{}`, the term of the foreign type. -/
def int {k : Nat} {Γ : Scope} : Term k Γ := .const "Int" [] [] []

/-- `zero.{}`. -/
def zero {k : Nat} {Γ : Scope} : Term k Γ := .const "zero" [] [] []

/-- `bound.{}`. -/
def bound {k : Nat} {Γ : Scope} : Term k Γ := .const "bound" [] [] []

/-- `Sorted.{}`. -/
def sorted {k : Nat} {Γ : Scope} : Term k Γ := .const "Sorted" [] [] []

/-- `origin.{}`. -/
def origin {k : Nat} {Γ : Scope} : Term k Γ := .const "origin" [] [] []

/-- `Int.{} :_{𝟙𝟙ᵐ} U_0`. -/
def intEntry : Constant := ⟨"Int", 0, 0, 0, .oneOne, fun _ => .sort ⟨.type, .zero⟩⟩

/-- `zero.{} :_{𝟙𝟙ᵐ} Int.{}`. -/
def zeroEntry : Constant := ⟨"zero", 0, 0, 0, .oneOne, fun _ => int⟩

/-- `bound.{} :_{𝟘𝟙ᵐ} Int.{}`. -/
def boundEntry : Constant := ⟨"bound", 0, 0, 0, .zeroOne, fun _ => int⟩

/-- `Sorted.{} :_{𝟙𝟙ᵐ} Ω_0`. -/
def sortedEntry : Constant := ⟨"Sorted", 0, 0, 0, .oneOne, fun _ => .sort ⟨.prop, .zero⟩⟩

/-- `sorted.{} :_{𝟘𝟙ᵐ} Sorted.{}`. -/
def sortedProofEntry : Constant := ⟨"sorted", 0, 0, 0, .zeroOne, fun _ => sorted⟩

/-- `origin.{} :_{𝟙𝟙ᵐ} Int.{} ≔ zero.{}`. -/
def originEntry : Definition := ⟨"origin", 0, 0, 0, .oneOne, fun _ => int, fun _ => zero⟩

/-- `(ex_sig)`: the signature `Σ_ex`, the last entry first. -/
def sigEx : Signature :=
  [.definition originEntry, .constant sortedProofEntry, .constant sortedEntry,
    .constant boundEntry, .constant zeroEntry, .constant intEntry]

/-- The signatures before each entry of `Σ_ex`. -/
def sig₁ : Signature := [.constant intEntry]
/-- `Int, zero`. -/
def sig₂ : Signature := .constant zeroEntry :: sig₁
/-- `Int, zero, bound`. -/
def sig₃ : Signature := .constant boundEntry :: sig₂
/-- `Int, zero, bound, Sorted`. -/
def sig₄ : Signature := .constant sortedEntry :: sig₃
/-- `Int, zero, bound, Sorted, sorted`. -/
def sig₅ : Signature := .constant sortedProofEntry :: sig₄

theorem wf₁ : WfSig sig₁ :=
  .constant (.intro (fun _ => ⟨.type, .succ .zero⟩) fun _ => .univ (.empty .empty)) (by decide)

/-- `Int.{}` is a type of `U_0` in every signature that extends `sig₁`. -/
theorem int_type {sig : Signature} (hsig : WfSig sig) (hmem : .constant intEntry ∈ sig) :
    HasType sig (.empty : Context 0 []) int (.sort ⟨.type, .zero⟩) :=
  .const (qs := []) (ls := []) (ps := []) (.empty hsig) (.constant (c := intEntry) hmem) rfl rfl rfl

theorem wf₂ : WfSig sig₂ :=
  .constant (.intro (fun _ => ⟨.type, .zero⟩) fun _ => int_type wf₁ (by simp [sig₁])) (by decide)

theorem wf₃ : WfSig sig₃ :=
  .constant (.intro (fun _ => ⟨.type, .zero⟩) fun _ => int_type wf₂ (by simp [sig₂, sig₁]))
    (by decide)

theorem wf₄ : WfSig sig₄ :=
  .constant (.intro (fun _ => ⟨.type, .succ .zero⟩) fun _ => .prop (.empty wf₃)) (by decide)

theorem wf₅ : WfSig sig₅ :=
  .constant (.intro (fun _ => ⟨.prop, .zero⟩) fun _ =>
    .const (qs := []) (ls := []) (ps := []) (.empty wf₄)
      (.constant (c := sortedEntry) (by simp [sig₄])) rfl rfl rfl) (by decide)

/-- `(ex_sig)`: the signature `Σ_ex` is well formed. -/
theorem wf_sigEx : WfSig sigEx :=
  .definition (sig := sig₅) (d := originEntry)
    (.intro (fun _ => ⟨.type, .zero⟩)
      (fun _ => int_type wf₅ (by simp [sig₅, sig₄, sig₃, sig₂, sig₁]))
      (fun _ => .const (qs := []) (ls := []) (ps := []) (.empty wf₅)
        (.constant (c := zeroEntry) (by simp [sig₅, sig₄, sig₃, sig₂])) rfl rfl rfl)
      (fun _ => .const (qs := []) (ls := []) (ps := [])
        (.constant (c := zeroEntry) (by simp [sig₅, sig₄, sig₃, sig₂])) rfl))
    (by decide)

/-- `(ex_use)`: the definition `origin` unfolds to `zero`. -/
theorem origin_eq_zero : EqTerm sigEx (.empty : Context 0 []) origin zero int :=
  .delta (d := originEntry) (qs := []) (ls := []) (ps := []) (.empty wf_sigEx) (by simp [sigEx])
    rfl rfl rfl

/-- `(ex_use)`: a proof may use the ghost value `bound`. -/
theorem bound_in_proofs : Usage sigEx (Γ := []) 𝟘ᶜ .zeroOne (bound : Term 0 []) :=
  .const (qs := []) (ls := []) (ps := []) (.constant (c := boundEntry) (by simp [sigEx])) rfl

/-- The only entry of `Σ_ex` named `bound` is the ghost value, of mode `𝟘𝟙ᵐ`. -/
theorem mode_of_bound {c : Name} {j k g : Nat} {m : Mode} {A : Instance j g → Term k []}
    (h : sigEx.HasEntry c j k g m A) (hc : c = "bound") : m = .zeroOne := by
  cases h with
  | definition hmem =>
    simp only [sigEx, List.mem_cons, Entry.definition.injEq, reduceCtorEq, List.not_mem_nil,
      or_false] at hmem
    subst hmem
    exact absurd hc (by decide)
  | constant hmem =>
    simp only [sigEx, List.mem_cons, Entry.constant.injEq, reduceCtorEq, List.not_mem_nil,
      or_false, false_or] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · rfl
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)

/-- A derivation of the usage of `bound` in the mode `𝟙𝟙ᵐ` ends with the rule `(c_m)`, after
uses of the rule `(sub)`, whose mode condition fails. -/
theorem not_usage_bound : ∀ {γ : GradeVector 0} {m : Mode} {t : Term 0 []},
    Usage sigEx (Γ := []) γ m t → t = bound → m = .oneOne → False
  | _, _, _, .var _, ht, _ => by cases ht
  | _, _, _, .const hE hmm, ht, hm => by
    cases ht
    subst hm
    rw [mode_of_bound hE rfl] at hmm
    exact absurd hmm (by decide)
  | _, _, _, .sort, ht, _ => by cases ht
  | _, _, _, .sub h _, ht, hm => not_usage_bound h ht hm

/-- `(ex_use)`: a program cannot use the ghost value `bound`, in whatever grades. -/
theorem bound_not_in_programs (γ : GradeVector 0) :
    ¬ Usage sigEx (Γ := []) γ .oneOne (bound : Term 0 []) :=
  fun h => not_usage_bound h rfl rfl

/-- The definition `origin` reduces to `zero` by the rule `(δ_⟶)`. -/
theorem origin_red : Red sigEx (origin : Term 0 []) zero :=
  .delta (d := originEntry) (qs := []) (ls := []) (ps := []) (by simp [sigEx]) rfl rfl rfl

/-- `zero` is a constant, a neutral term, which is a head normal form. -/
theorem zero_whnf : Whnf sigEx (zero : Term 0 []) :=
  .ne (.const (c := zeroEntry) (qs := []) (ls := []) (ps := []) (by simp [sigEx]))

/-- The program `origin.{}` computes to `zero.{}`. -/
theorem origin_computes : Computes sigEx origin zero :=
  ⟨.step origin_red (.refl _), zero_whnf⟩

/-- The empty scope declares variables only. -/
theorem firstOrder_empty : Scope.FirstOrder [] := fun _ h => nomatch h

/-- The extraction of the program `origin.{}` is `origin`, which stands for `zero`. -/
theorem origin_extract : (origin : Term 0 []).extract firstOrder_empty = .const "origin" [] := rfl

end SicExample.Core
