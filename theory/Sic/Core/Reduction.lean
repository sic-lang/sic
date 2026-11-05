module

public import Sic.Core.Typing

/-!
# Reduction

The weak head reduction of RFC 24, `Σ ⊢ t ⟶ u`, the computation of the type theory: the conversion
reduces the terms to their weak head normal forms to compare them, the meaning computes the closed
terms to their canonical forms, `t ⇓ v`, and the erasure is sound for this computation.
The core reduces by the rule `(δ_⟶)` alone, which unfolds a definition; the kinds of declarations
add their computations, and say which of their terms are head normal forms.
A head normal form is a sort, an instance of a declared type, or a neutral term, stuck on a variable
or on a constant, which no rule unfolds.

The reduction is untyped and defined on open terms, since the meaning defines the judgments from it
and the algorithm of the conversion reduces terms of a context.

ADE reduce typed terms, `Γ ⊢ t ⇒ u ∷ A`, so that a step gives the equality of its two sides at once,
which their logical relation needs before it proves the preservation of the types; their definitions
are numbered in their context, so that two definitions never share a name, while the names of a
signature are distinct when it is well formed.
-/

@[expose] public section

namespace Sic.Core

-- ADE: `Neutral`, in `Definition/Untyped/Neutral.agda`.
/-- `t` is neutral: its reduction is stuck on a variable or on a constant. -/
inductive Neutral (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Prop where
  -- ADE: `Neutral.var`, in `Definition/Untyped/Neutral.agda`.
  /-- `x[t̄]`: a variable, or a second-order variable applied to arguments. -/
  | var {ps : List Grade} (x : Var Γ ps) (ts : Args k Γ ps) : Neutral sig (.var x ts)
  -- ADE: `Neutral.defn`, in `Definition/Untyped/Neutral.agda`, for the opaque definitions.
  /-- `c.{s̄; l̄; p̄}`: a constant, an entry without body. -/
  | const {c : Constant} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : .constant c ∈ sig) : Neutral sig (.const c.name qs ls ps)

-- ADE: `Whnf`, in `Definition/Untyped/Whnf.agda`.
/-- `t` is a head normal form of the core. -/
inductive Whnf (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Prop where
  -- ADE: `Whnf.Uₙ`, in `Definition/Untyped/Whnf.agda`.
  /-- `U_l` and `Ω_l`. -/
  | sort (κ : Universe k) : Whnf sig (.sort κ)
  -- ADE: none.
  /-- `T = D.{s̄; l̄; p̄} ā`, an instance of a declared type. -/
  | inst {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
      (as : InstanceArgs k Γ Δ) : Whnf sig (.inst D qs ls ps as)
  -- ADE: `Whnf.ne`, in `Definition/Untyped/Whnf.agda`.
  /-- A neutral term. -/
  | ne {t : Term k Γ} (h : Neutral sig t) : Whnf sig t

-- ADE: `_⊢_⇒_∷_`, in `Definition/Typed.agda`, and `_⊢_⇒_`, in `Graded/Erasure/Target.agda`.
/-- `Σ ⊢ t ⟶ u`: `t` reduces to `u` in one step of weak head reduction. -/
inductive Red (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Term k Γ → Prop where
  -- ADE: `δ-red`, in `Definition/Typed.agda`.
  /-- `(δ_⟶)`: a definition unfolds to its body, at an instance of its variables. -/
  | delta {d : Definition} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : .definition d ∈ sig) (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
      (hp : ps.length = d.grades) :
      Red sig (.const d.name qs ls ps)
        (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))

-- ADE: `_⊢_⇒*_∷_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ t ⟶* u`: `t` reduces to `u` in some steps. -/
inductive RedStar (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Term k Γ → Prop where
  /-- No step. -/
  | refl (t : Term k Γ) : RedStar sig t t
  /-- A step, then the others. -/
  | step {t u v : Term k Γ} (h : Red sig t u) (hs : RedStar sig u v) : RedStar sig t v

-- ADE: `_⊢_↘_∷_`, in `Definition/Typed.agda`.
/-- `t ⇓ v`: the closed term `t` computes to the head normal form `v`, which is canonical. -/
def Computes (sig : Signature) (t v : Term 0 []) : Prop :=
  RedStar sig t v ∧ Whnf sig v

/-! ## Determinism -/

/-- A step of reduction unfolds a definition of the signature. -/
theorem Red.inv {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ} :
    Red sig t u → ∃ (d : Definition) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
      (hq : qs.length = d.sorts) (hl : ls.length = d.levels) (hp : ps.length = d.grades),
      .definition d ∈ sig ∧ t = .const d.name qs ls ps ∧
        u = Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl)
  | .delta h hq hl hp => ⟨_, _, _, _, hq, hl, hp, h, rfl, rfl⟩

-- ADE: `whnfRedTerm`, in `Definition/Typed/Properties/Reduction.agda`.
/-- A head normal form does not reduce. -/
theorem Whnf.not_red {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ} (hsig : WfSig sig)
    (hw : Whnf sig t) (h : Red sig t u) : False := by
  obtain ⟨d, qs, ls, ps, _, _, _, hd, ht, -⟩ := h.inv
  cases hw with
  | sort => cases ht
  | inst => cases ht
  | ne hn =>
    cases hn with
    | var => cases ht
    | const hc =>
      injection ht with _ hn
      exact nomatch hsig.entry_unique hc hd (n := d.name) (by simp [Entry.names, hn])
        (by simp [Entry.names])

-- ADE: `whrDetTerm`, in `Definition/Typed/Properties/Reduction.agda`.
/-- The reduction is deterministic. -/
theorem Red.det {sig : Signature} {k : Nat} {Γ : Scope} {t u₁ u₂ : Term k Γ} (hsig : WfSig sig)
    (h₁ : Red sig t u₁) (h₂ : Red sig t u₂) : u₁ = u₂ := by
  obtain ⟨d₁, qs₁, ls₁, ps₁, _, _, _, hd₁, rfl, rfl⟩ := h₁.inv
  obtain ⟨d₂, qs₂, ls₂, ps₂, _, _, _, hd₂, ht, rfl⟩ := h₂.inv
  injection ht with _ hn hq hl hp
  subst hq hl hp
  have hd := hsig.entry_unique hd₁ hd₂ (n := d₁.name) (by simp [Entry.names])
    (by simp [Entry.names, hn])
  cases hd
  rfl

-- ADE: `whrDet*Term`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Two reductions to head normal forms end on the same term. -/
theorem RedStar.det {sig : Signature} {k : Nat} {Γ : Scope} {t v₁ v₂ : Term k Γ}
    (hsig : WfSig sig) : RedStar sig t v₁ → Whnf sig v₁ → RedStar sig t v₂ → Whnf sig v₂ →
    v₁ = v₂
  | .refl _, _, .refl _, _ => rfl
  | .refl _, hw₁, .step h _, _ => (hw₁.not_red hsig h).elim
  | .step h _, _, .refl _, hw₂ => (hw₂.not_red hsig h).elim
  | .step h₁ hs₁, hw₁, .step h₂ hs₂, hw₂ => by
    cases h₁.det hsig h₂
    exact hs₁.det hsig hw₁ hs₂ hw₂

/-- A closed term computes to one canonical term at most. -/
theorem Computes.det {sig : Signature} {t v₁ v₂ : Term 0 []} (hsig : WfSig sig)
    (h₁ : Computes sig t v₁) (h₂ : Computes sig t v₂) : v₁ = v₂ :=
  h₁.1.det hsig h₁.2 h₂.1 h₂.2

end Sic.Core
