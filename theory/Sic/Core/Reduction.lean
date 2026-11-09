module

public import Sic.Core.Typing

/-!
# Reduction

The weak head reduction of annex 14 of RFC 36, `Σ ⊢ t ⟶ u`, the computation of the type theory:
the conversion reduces the terms to their weak head normal forms to compare them, the meaning
computes the closed terms, `Σ ⊢ t ⇓ v`, and the erasure is sound for this computation.
The core reduces by the rule `(δ_⟶)`, which unfolds a definition, and the data types by `(ι_⟶)`,
which runs the branch of a constructor that a recursor eliminates, and `(rec_⟶)`, which reduces the
term that a recursor eliminates.
A head normal form is a sort, an instance of a declared type, a constructor applied to the terms of
its fields, or a neutral term, stuck on a variable or on a constant, which no rule unfolds, or a
recursor on a neutral term.

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
/-- `t` is neutral: its reduction is stuck on a variable or on a declared constant.
RFC: `\mathsf{neutral}_t` -/
inductive Neutral (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Prop where
  -- ADE: `Neutral.var`, in `Definition/Untyped/Neutral.agda`.
  /-- `x[t̄]`: a variable, or a second-order variable applied to arguments. -/
  | var {e : Scope.Entry} (x : Var Γ e) (ts : Args k Γ e.params) : Neutral sig (.var x ts)
  -- ADE: `Neutral.defn`, in `Definition/Untyped/Neutral.agda`, for the opaque definitions.
  /-- `f.{s̄; l̄; p̄}`: a declared constant, which has no body. -/
  | const {c : ConstantDeclaration} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : .constantDeclaration c ∈ sig) : Neutral sig (.const c.name qs ls ps)
  -- ADE: `natrecₙ`, `prodrecₙ`, `unitrecₙ` and `emptyrecₙ`, in `Definition/Untyped/Neutral.agda`.
  /-- `rec_r T t return C̄ with ū`: a recursor on a neutral term. -/
  | recursor {Δ : Scope} {r : Grade} {D : Name} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} {as : InstanceArgs k Γ Δ} {t : Term k Γ} {Cs : Motives k Γ}
      {us : Branches k Γ} (h : Neutral sig t) : Neutral sig (.recursor r D qs ls ps as t Cs us)

-- ADE: `Whnf`, in `Definition/Untyped/Whnf.agda`.
/-- `t` is a head normal form of the core.
RFC: `\mathsf{whnf}_t` -/
inductive Whnf (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Prop where
  -- ADE: `Whnf.Uₙ`, in `Definition/Untyped/Whnf.agda`.
  /-- `U_l` and `Ω_l`. -/
  | sort (κ : Universe k) : Whnf sig (.sort κ)
  -- ADE: none.
  /-- `T = D.{s̄; l̄; p̄} ā`, an instance of a declared type. -/
  | inst {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
      (as : InstanceArgs k Γ Δ) : Whnf sig (.inst D qs ls ps as)
  -- ADE: `Whnf.zeroₙ`, `Whnf.sucₙ`, `Whnf.prodₙ` and `Whnf.starₙ`, in
  -- `Definition/Untyped/Whnf.agda`, for their constructors.
  /-- `T.c(t̄)`, a constructor applied to the terms of its fields, which it does not compute. -/
  | ctor {Δ : Scope} (D : Name) (qs : List Quality) (ls : List (Level k)) (ps : List Grade)
      (as : InstanceArgs k Γ Δ) (c : Name) (ts : Terms k Γ) :
      Whnf sig (.ctor D qs ls ps as c ts)
  -- ADE: `Whnf.ne`, in `Definition/Untyped/Whnf.agda`.
  /-- A neutral term. -/
  | ne {t : Term k Γ} (h : Neutral sig t) : Whnf sig t

-- ADE: `_⊢_⇒_∷_`, in `Definition/Typed.agda`, and `_⊢_⇒_`, in `Graded/Erasure/Target.agda`.
/-- `Σ ⊢ t ⟶ u`: `t` reduces to `u` in one step of weak head reduction. -/
inductive Red (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Term k Γ → Prop where
  -- ADE: `δ-red`, in `Definition/Typed.agda`.
  /-- A constant definition unfolds to its body, at the instance of its variables.
  RFC: `\delta_{\longrightarrow}` -/
  | delta {d : ConstantDefinition} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      (h : .constantDefinition d ∈ sig) (hq : qs.length = d.sorts) (hl : ls.length = d.levels)
      (hp : ps.length = d.grades) :
      Red sig (.const d.name qs ls ps)
        (Signature.instanceType d.body (.ofLists qs ps hq hp) (ls.getFin hl))
  -- ADE: `natrec-zero`, `natrec-suc`, `prodrec-β` and `unitrec-β`, in `Definition/Typed.agda`.
  /-- A recursor on a constructor applied to the terms of its fields steps to the branch of the
  constructor, the case `i` of the block of its type, with the terms of the fields substituted for
  its variables; the branch binds no recursive result, the block not being recursive.
  RFC: `\iota_{\longrightarrow}` -/
  | iota {decl : TypeDeclaration} {i j : Nat}
      {T : DataType decl.sorts decl.grades decl.levels decl.scope}
      {con : Constructor decl.sorts decl.grades decl.levels decl.scope} {Δ Δ' : Scope} {r : Grade}
      {D D' : Name} {qs qs' : List Quality} {ls ls' : List (Level k)} {ps ps' : List Grade}
      {as : InstanceArgs k Γ Δ} {as' : InstanceArgs k Γ Δ'} {c : Name} {ts : Terms k Γ}
      {Cs : Motives k Γ} {us : Branches k Γ} {n : Nat} {u : Term k (Γ.extend (n + 0))}
      {v : Term k Γ} (h : .typeDeclaration decl ∈ sig) (hi : decl.cases[i]? = some (j, T, con))
      (hD : T.name = D) (hc : con.name = c) (hu : us.get i = some ⟨n, 0, u⟩)
      (hv : u.instantiateTerms ts = some v) :
      Red sig (.recursor r D' qs' ls' ps' as' (.ctor D qs ls ps as c ts) Cs us) v
  -- ADE: `natrec-subst`, `prodrec-subst`, `unitrec-subst` and `emptyrec-subst`, in
  -- `Definition/Typed.agda`.
  /-- A recursor reduces the term it eliminates.
  RFC: `\mathsf{rec}_{\longrightarrow}` -/
  | recursor {Δ : Scope} {r : Grade} {D : Name} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} {as : InstanceArgs k Γ Δ} {t t' : Term k Γ} {Cs : Motives k Γ}
      {us : Branches k Γ} (h : Red sig t t') :
      Red sig (.recursor r D qs ls ps as t Cs us) (.recursor r D qs ls ps as t' Cs us)

-- ADE: `_⊢_⇒*_∷_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ t ⟶* u`: `t` reduces to `u` in some steps. -/
inductive RedStar (sig : Signature) {k : Nat} {Γ : Scope} : Term k Γ → Term k Γ → Prop where
  /-- No step.
  RFC: `{\longrightarrow^{*}}.\mathsf{refl}` -/
  | refl (t : Term k Γ) : RedStar sig t t
  /-- A step, then the others.
  RFC: `{\longrightarrow^{*}}.\mathsf{step}` -/
  | step {t u₁ u₂ : Term k Γ} (h : Red sig t u₁) (hs : RedStar sig u₁ u₂) : RedStar sig t u₂

-- ADE: `_⊢_↘_∷_`, in `Definition/Typed.agda`.
/-- `Σ ⊢ t ⇓ v`: the closed term `t` computes to the head normal form `v`, stuck on no variable.
RFC: `\Downarrow` -/
def Computes (sig : Signature) (t v : Term 0 []) : Prop :=
  RedStar sig t v ∧ Whnf sig v

/-! ## Determinism -/

/-- A neutral term does not reduce. -/
theorem Neutral.not_red {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ}
    (hsig : sig.Distinct) (hn : Neutral sig t) (h : Red sig t u) : False := by
  induction h with
  | @delta d _ _ _ hd =>
    generalize hx : d.name = x at hn
    cases hn with
    | const hc =>
      have he := hsig.entry_unique hc hd (n := d.name) (by simp [Entry.names, hx])
        (by simp [Entry.names])
      exact nomatch he
  | iota => cases hn with | recursor hn => exact nomatch hn
  | recursor _ ih => cases hn with | recursor hn => exact ih hn

-- ADE: `whnfRedTerm`, in `Definition/Typed/Properties/Reduction.agda`.
/-- A head normal form does not reduce.
RFC: `\mathsf{normal}_{\longrightarrow}` -/
theorem Whnf.not_red {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ}
    (hsig : sig.Distinct) : Whnf sig t → Red sig t u → False
  | .sort _, h => nomatch h
  | .inst .., h => nomatch h
  | .ctor .., h => nomatch h
  | .ne hn, h => hn.not_red hsig h

-- ADE: `whrDetTerm`, in `Definition/Typed/Properties/Reduction.agda`.
/-- The reduction is deterministic.
RFC: `\mathsf{det}_{\longrightarrow}` -/
theorem Red.det {sig : Signature} {k : Nat} {Γ : Scope} {t u₁ u₂ : Term k Γ}
    (hsig : sig.Distinct) (h₁ : Red sig t u₁) (h₂ : Red sig t u₂) : u₁ = u₂ := by
  induction h₁ generalizing u₂ with
  | @delta d₁ _ _ _ hd₁ =>
    generalize hx : d₁.name = x at h₂
    cases h₂ with
    | @delta d₂ _ _ _ hd₂ =>
      have he := hsig.entry_unique hd₁ hd₂ (n := d₁.name) (by simp [Entry.names])
        (by simp [Entry.names, hx])
      cases he
      rfl
  | iota h₁ hi₁ hD₁ hc₁ hu₁ hv₁ =>
    cases h₂ with
    | iota h₂ hi₂ hD₂ hc₂ hu₂ hv₂ =>
      have hT₁ := (TypeDeclaration.mem_casesFrom (List.mem_of_getElem? hi₁)).1
      have hT₂ := (TypeDeclaration.mem_casesFrom (List.mem_of_getElem? hi₂)).1
      have he := hsig.entry_unique h₁ h₂ (TypeDeclaration.name_mem_names hT₁)
        (by rw [hD₁, ← hD₂]; exact TypeDeclaration.name_mem_names hT₂)
      cases he
      have hi := List.getElem?_inj_of_nodup_map (hsig.cases_nodup h₁) hi₁ hi₂
        (by simp only [hD₁, hD₂, hc₁, hc₂])
      subst hi
      have hu := Option.some.inj (hu₁.symm.trans hu₂)
      injection hu with hn hu
      subst hn
      cases eq_of_heq (Sigma.ext_iff.1 (eq_of_heq hu)).2
      exact Option.some.inj (hv₁.symm.trans hv₂)
    | recursor h => exact (Whnf.not_red hsig (.ctor ..) h).elim
  | recursor h₁ ih =>
    cases h₂ with
    | iota => exact (Whnf.not_red hsig (.ctor ..) h₁).elim
    | recursor h₂ => rw [ih h₂]

-- ADE: `whrDet*Term`, in `Definition/Typed/Properties/Reduction.agda`.
/-- Two reductions to head normal forms end on the same term.
RFC: `\mathsf{det}_{\longrightarrow^{*}}` -/
theorem RedStar.det {sig : Signature} {k : Nat} {Γ : Scope} {t u₁ u₂ : Term k Γ}
    (hsig : sig.Distinct) : RedStar sig t u₁ → Whnf sig u₁ → RedStar sig t u₂ → Whnf sig u₂ →
    u₁ = u₂
  | .refl _, _, .refl _, _ => rfl
  | .refl _, hw₁, .step h _, _ => (hw₁.not_red hsig h).elim
  | .step h _, _, .refl _, hw₂ => (hw₂.not_red hsig h).elim
  | .step h₁ hs₁, hw₁, .step h₂ hs₂, hw₂ => by
    cases h₁.det hsig h₂
    exact hs₁.det hsig hw₁ hs₂ hw₂

/-- A closed term computes to one head normal form at most.
RFC: `\mathsf{det}_{\Downarrow}` -/
theorem Computes.det {sig : Signature} {t v₁ v₂ : Term 0 []} (hsig : sig.Distinct)
    (h₁ : Computes sig t v₁) (h₂ : Computes sig t v₂) : v₁ = v₂ :=
  h₁.1.det hsig h₁.2 h₂.1 h₂.2

end Sic.Core
