module

public import Sic.Core.Meaning
import Sic.Core.Syntax.Signature

/-!
# Relations of the Meaning

The relations of annex 18 of RFC 36 are partial equivalence relations, and each type has one: the
relations built from others, the least fixed points of the data types and the greatest fixed points
of the codata types, and the relations of a level, by mutual recursion on the graph, which gives a
type a single level and a single sort.

ADE prove the symmetry, the transitivity and the irrelevance of the derivations of their logical
relation, in `Definition/LogicalRelation/Properties/`, for their universes and without data or codata
types.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Equality of the Canonical Terms -/

/-- `ty(U_n)` at the level `n`. -/
theorem levelRel_univ (sig : Signature) (ι : Interpretation) (n : Nat) :
    (levelRel sig ι n).univ = UnivRel sig ι n fun m _ => levelRel sig ι m := by
  rw [levelRel]

/-- `ty(Ω_n)` at the level `n`. -/
theorem levelRel_prop (sig : Signature) (ι : Interpretation) (n : Nat) :
    (levelRel sig ι n).prop = PropRel sig ι n fun m _ => levelRel sig ι m := by
  rw [levelRel]

/-! ## Partial Equivalence Relations

The equality `eq(v)` of the terms of a type is a partial equivalence relation, and it is unique, in a
signature whose names are distinct, so that a closed term computes to one canonical term at most and
a declared type is the data type of one declaration.
These properties are proved level by level: those of the relations of a level, `LevelRel.IsPer`,
follow from those of the levels below it, by induction on the clauses that give a type of the level,
together with the telescopes of the fields of its constructors, so that each kind of declaration
adds the cases of its clauses.
A type is given by the clauses of one level and one sort at most, which `UnivRel.level`,
`UnivRel.not_prop` and `PropRel.level` show by cases, without induction. -/

/-- The names of a signature stay distinct when its constants are interpreted. -/
theorem Signature.Distinct.interpret {ι : Interpretation} :
    {sig : Signature} → sig.Distinct → (sig.interpret ι).Distinct
  | [], _ => trivial
  | e :: _, ⟨h, hnodup, hfresh, hc⟩ => by
    have hnames : ∀ e : Entry, (e.interpret ι).names = e.names := by
      intro e; cases e <;> rfl
    refine ⟨h.interpret, (hnames e).symm ▸ hnodup, fun e' he' n hn => ?_, ?_⟩
    · obtain ⟨e'', he'', rfl⟩ := List.mem_map.1 he'
      rw [hnames] at hn ⊢
      exact hfresh e'' he'' n hn
    · cases e <;> exact hc

/-- In a signature whose names are distinct, a closed term computes to one canonical term at
most. -/
theorem Computesι.det {sig : Signature} {ι : Interpretation} {t v₁ v₂ : Term 0 []}
    (hd : sig.Distinct) (h₁ : Computesι sig ι t v₁) (h₂ : Computesι sig ι t v₂) : v₁ = v₂ :=
  Computes.det hd.interpret h₁ h₂

/-- The equality that `ty(U_n)` gives a type is unique. -/
theorem LevelRel.IsPer.univ_eq {L : LevelRel} (hL : L.IsPer) {v : Term 0 []} {R R' : TermRel}
    (h : L.univ v R) (h' : L.univ v R') : R = R' :=
  funext fun t => funext fun u => propext (hL.univ_unique h h' t u)

/-- `ty(U_n)` at the level `n`, as the clauses of `UnivRel`. -/
theorem levelRel_univ_iff {sig : Signature} {ι : Interpretation} {n : Nat} {v : Term 0 []}
    {R : TermRel} :
    (levelRel sig ι n).univ v R ↔ UnivRel sig ι n (fun m _ => levelRel sig ι m) v R := by
  rw [levelRel_univ]

/-- `ty(Ω_n)` at the level `n`, as the clauses of `PropRel`. -/
theorem levelRel_prop_iff {sig : Signature} {ι : Interpretation} {n : Nat} {v : Term 0 []}
    {b : Prop} : (levelRel sig ι n).prop v b ↔ PropRel sig ι n (fun m _ => levelRel sig ι m) v b := by
  rw [levelRel_prop]

/-! ### Relations Built From Others -/

/-- `eq⇓(R)` is a partial equivalence relation when `R` is one, in a signature whose names are
distinct. -/
theorem TermRel.computed_isPer {sig : Signature} {ι : Interpretation} {R : TermRel}
    (hd : sig.Distinct) (hR : IsPer R) : IsPer (R.computed sig ι) where
  symm := fun ⟨v, w, ht, hu, h⟩ => ⟨w, v, hu, ht, hR.symm h⟩
  trans := fun ⟨v, _, ht, hu, h⟩ ⟨_, x, hu', hx, h'⟩ => by
    cases Computesι.det hd hu hu'
    exact ⟨v, x, ht, hx, hR.trans h h'⟩

/-- `eq⇓(R)` relates the same terms for relations `R` that relate the same terms. -/
theorem TermRel.computed_congr {sig : Signature} {ι : Interpretation} {R R' : TermRel}
    (h : ∀ t u, R t u ↔ R' t u) : ∀ t u, R.computed sig ι t u ↔ R'.computed sig ι t u :=
  fun _ _ => ⟨fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, (h v w).1 hvw⟩,
    fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, (h v w).2 hvw⟩⟩

/-- The equality of the terms of the fields of the empty telescope is a partial equivalence
relation. -/
theorem FieldsRel.nil_isPer : IsPer FieldsRel.nil where
  symm {ts us} h := match ts, us, h with
    | .nil, .nil, _ => trivial
  trans {ts us ws} h h' := match ts, us, ws, h, h' with
    | .nil, .nil, .nil, _, _ => trivial

/-- The equality of the terms of the fields of a telescope `x : A, Θ` is a partial equivalence
relation, when the equality of the terms of `A` is one, and so is the equality of the terms of
`Θ[a / x]` for each term `a` of `A`, the same for equal terms. -/
theorem FieldsRel.cons_isPer {F : TermRel} {G : Term 0 [] → FieldsRel} (hF : IsPer F)
    (hG : ∀ a, F a a → IsPer (G a))
    (hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us) :
    IsPer (FieldsRel.cons F G) where
  symm {ts us} h := match ts, us, h with
    | .cons t ts, .cons u us, ⟨h₁, h₂⟩ =>
      ⟨hF.symm h₁, (hG u (hF.trans (hF.symm h₁) h₁)).symm ((hresp t u h₁ ts us).1 h₂)⟩
  trans {ts us ws} h h' := match ts, us, ws, h, h' with
    | .cons t _ts, .cons u us, .cons _w ws, ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩ =>
      ⟨hF.trans h₁ h₁', (hG t (hF.trans h₁ (hF.symm h₁))).trans h₂ ((hresp t u h₁ us ws).2 h₂')⟩

/-- The equalities of the terms of the fields of two telescopes `x : A, Θ` relate the same terms,
when those of `A` do, and those of `Θ[a / x]` do for each term `a` of `A`. -/
theorem FieldsRel.cons_congr {F F' : TermRel} {G G' : Term 0 [] → FieldsRel} (hFp : IsPer F)
    (hF : ∀ t u, F t u ↔ F' t u) (hG : ∀ a, F a a → ∀ ts us, G a ts us ↔ G' a ts us) :
    ∀ ts us, FieldsRel.cons F G ts us ↔ FieldsRel.cons F' G' ts us
  | .nil, _ => .rfl
  | .cons _ _, .nil => .rfl
  | .cons t ts, .cons u us =>
    ⟨fun ⟨h₁, h₂⟩ => ⟨(hF t u).1 h₁, (hG t (hFp.trans h₁ (hFp.symm h₁)) ts us).1 h₂⟩,
      fun ⟨h₁, h₂⟩ =>
        have h₁' := (hF t u).2 h₁
        ⟨h₁', (hG t (hFp.trans h₁' (hFp.symm h₁')) ts us).2 h₂⟩⟩

/-- A closed term is a constructor of one declared type, one name, and one list of fields. -/
theorem Term.IsCtor.inj {D D' c c' : Name} {ts ts' : Terms 0 []} {v : Term 0 []}
    (h : v.IsCtor D c ts) (h' : v.IsCtor D' c' ts') : D = D' ∧ c = c' ∧ ts = ts' := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  obtain ⟨_, _, _, _, _, h'⟩ := h'
  cases h'
  exact ⟨rfl, rfl, rfl⟩

/-- `(eq_c)` is a partial equivalence relation when the equalities of the terms of the fields of the
constructors are, which have distinct names. -/
theorem DataType.ctorRel_isPer {j g k : Nat} {Δ : Scope} {D : Name} {T : DataType j g k Δ}
    {S : Constructor j g k Δ → FieldsRel} (hc : (T.constructors.map (·.name)).Nodup)
    (hS : ∀ c ∈ T.constructors, IsPer (S c)) : IsPer (T.ctorRel D S) where
  symm := fun ⟨c, hcm, ts, us, hv, hw, h⟩ => ⟨c, hcm, us, ts, hw, hv, (hS c hcm).symm h⟩
  trans := fun ⟨c, hcm, ts, _, hv, hw, h⟩ ⟨_, hcm', _, vs, hw', hx, h'⟩ => by
    obtain ⟨-, hn, rfl⟩ := hw.inj hw'
    cases List.eq_of_nodup_map hc hcm hcm' hn
    exact ⟨c, hcm, ts, vs, hv, hx, (hS c hcm).trans h h'⟩

/-- `(eq_c)` relates the same terms for equalities of the terms of the fields that relate the same
terms. -/
theorem DataType.ctorRel_congr {j g k : Nat} {Δ : Scope} {D : Name} {T : DataType j g k Δ}
    {S S' : Constructor j g k Δ → FieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ ts us, S c ts us ↔ S' c ts us) :
    ∀ v w, T.ctorRel D S v w ↔ T.ctorRel D S' v w :=
  fun _ _ => ⟨fun ⟨c, hcm, ts, us, hv, hw, hS⟩ => ⟨c, hcm, ts, us, hv, hw, (h c hcm ts us).1 hS⟩,
    fun ⟨c, hcm, ts, us, hv, hw, hS⟩ => ⟨c, hcm, ts, us, hv, hw, (h c hcm ts us).2 hS⟩⟩

/-- `(true_D)` is the same for equalities of the terms of the fields that relate the same terms. -/
theorem DataType.truth_congr {j g k : Nat} {Δ : Scope} {T : DataType j g k Δ}
    {S S' : Constructor j g k Δ → FieldsRel}
    (h : ∀ c ∈ T.constructors, ∀ ts us, S c ts us ↔ S' c ts us) : T.truth S ↔ T.truth S' :=
  ⟨fun ⟨c, hcm, ts, hS⟩ => ⟨c, hcm, ts, (h c hcm ts ts).1 hS⟩,
    fun ⟨c, hcm, ts, hS⟩ => ⟨c, hcm, ts, (h c hcm ts ts).2 hS⟩⟩

/-- The equalities of the terms of the fields of two telescopes `x : A, Θ` relate the terms that the
first one relates, when those of `A` do, and those of `Θ[a / x]` do for the terms `a` of `A`. -/
theorem FieldsRel.cons_mono {F₁ F₂ : TermRel} {G₁ G₂ : Term 0 [] → FieldsRel}
    (hF : ∀ t u, F₁ t u → F₂ t u) (hG : ∀ t u, F₁ t u → ∀ ts us, G₁ t ts us → G₂ t ts us) :
    ∀ ts us, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ ts us
  | .nil, _, h => h.elim
  | .cons _ _, .nil, h => h.elim
  | .cons t ts, .cons u us, ⟨h₁, h₂⟩ => ⟨hF t u h₁, hG t u h₁ ts us h₂⟩

/-- The equality of the terms of the fields of a telescope `x : A, Θ` relates in the other order the
terms that the equality of another one relates, when those of `A` do, and those of `Θ[a / x]` do. -/
theorem FieldsRel.cons_symm {F₁ F₂ : TermRel} {G₁ G₂ : Term 0 [] → FieldsRel}
    (hF : ∀ t u, F₁ t u → F₂ u t) (hG : ∀ t u, F₁ t u → ∀ ts us, G₁ t ts us → G₂ u us ts) :
    ∀ ts us, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ us ts
  | .nil, _, h => h.elim
  | .cons _ _, .nil, h => h.elim
  | .cons t ts, .cons u us, ⟨h₁, h₂⟩ => ⟨hF t u h₁, hG t u h₁ ts us h₂⟩

/-- The equality of the terms of the fields of a telescope `x : A, Θ` relates the terms that two
others relate in a chain, when those of `A` do, and those of `Θ[a / x]` do. -/
theorem FieldsRel.cons_trans {F₁ F₂ F₃ : TermRel} {G₁ G₂ G₃ : Term 0 [] → FieldsRel}
    (hF : ∀ t u v, F₁ t u → F₂ u v → F₃ t v)
    (hG : ∀ t u v, F₁ t u → F₂ u v → ∀ ts us vs, G₁ t ts us → G₂ u us vs → G₃ t ts vs) :
    ∀ ts us vs, FieldsRel.cons F₁ G₁ ts us → FieldsRel.cons F₂ G₂ us vs →
      FieldsRel.cons F₃ G₃ ts vs
  | .nil, _, _, h, _ => h.elim
  | .cons _ _, .nil, _, h, _ => h.elim
  | .cons _ _, .cons _ _, .nil, _, h => h.elim
  | .cons t ts, .cons u us, .cons v vs, ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩ =>
    ⟨hF t u v h₁ h₁', hG t u v h₁ h₁' ts us vs h₂ h₂'⟩

/-- `eq⇓(R₂)` relates the terms that `eq⇓(R₁)` relates, when `R₂` relates the canonical terms that
`R₁` relates. -/
theorem TermRel.computed_mono {sig : Signature} {ι : Interpretation} {R₁ R₂ : TermRel}
    (h : ∀ v w, R₁ v w → R₂ v w) {t u : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι t u :=
  fun ⟨v, w, ht, hu, hvw⟩ => ⟨v, w, ht, hu, h v w hvw⟩

/-- `eq⇓(R₂)` relates in the other order the terms that `eq⇓(R₁)` relates, when `R₂` relates so the
canonical terms that `R₁` relates. -/
theorem TermRel.computed_symm {sig : Signature} {ι : Interpretation} {R₁ R₂ : TermRel}
    (h : ∀ v w, R₁ v w → R₂ w v) {t u : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι u t :=
  fun ⟨v, w, ht, hu, hvw⟩ => ⟨w, v, hu, ht, h v w hvw⟩

/-- `eq⇓(R₃)` relates the terms that `eq⇓(R₁)` and `eq⇓(R₂)` relate in a chain, when `R₃` relates so
the canonical terms, in a signature whose names are distinct. -/
theorem TermRel.computed_trans {sig : Signature} {ι : Interpretation} {R₁ R₂ R₃ : TermRel}
    (hd : sig.Distinct) (h : ∀ v w x, R₁ v w → R₂ w x → R₃ v x) {t u w : Term 0 []} :
    R₁.computed sig ι t u → R₂.computed sig ι u w → R₃.computed sig ι t w :=
  fun ⟨v, _, ht, hu, h₁⟩ ⟨_, x, hu', hw, h₂⟩ => by
    cases Computesι.det hd hu hu'
    exact ⟨v, x, ht, hw, h _ _ _ h₁ h₂⟩

/-- The images of an option by two functions are related when the images of each value are. -/
theorem Option.rel_map {α β γ : Type} {r : β → γ → Prop} {f : α → β} {g : α → γ}
    (h : ∀ x, r (f x) (g x)) : (o : Option α) → Option.Rel r (o.map f) (o.map g)
  | none => .none
  | some x => .some (h x)

/-- The images of an option by three functions are all none, or related when the images of each
value are. -/
theorem Option.rel_map₃ {α β : Type} {r : β → β → β → Prop} {f g h : α → β}
    (hr : ∀ x, r (f x) (g x) (h x)) (o : Option α) :
    (o.map f = none ∧ o.map g = none ∧ o.map h = none) ∨
      ∃ x y z, o.map f = some x ∧ o.map g = some y ∧ o.map h = some z ∧ r x y z :=
  match o with
  | none => .inl ⟨rfl, rfl, rfl⟩
  | some x => .inr ⟨_, _, _, rfl, rfl, rfl, hr x⟩

/-- A telescope that is not the fields of a constructor relates its recursive fields as any
other. -/
theorem TelRel.none_rel {α β : Type} {r : α → β → Prop} (i : Nat) :
    Option.Rel r ((fun _ => none : Nat → Option α) i) ((fun _ => none : Nat → Option β) i) :=
  .none

/-- The same values at the recursive fields are related, when each one is related to itself. -/
theorem Option.rel_refl {α : Type} {r : α → α → Prop} (h : ∀ x, r x x) :
    (o : Option α) → Option.Rel r o o
  | none => .none
  | some x => .some (h x)

/-! ### Least Fixed Points

The equality `(eq_μ)` of the terms of the instances of a block is the least relation closed under
the clauses of its constructors, which every relation closed under them contains; it is closed
under them itself, and is a partial equivalence relation, when the equality of the terms of the
fields grows with the relations of the recursive fields, and inverts and composes them, by the
strict positivity of their occurrences. -/

section LeastFixedPoints

variable {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
  {S : (Name → TermRel) → Constructor j g k Δ → FieldsRel}

/-- `(eq_μ)` is closed under the clauses of the constructors, when the equality of the terms of the
fields grows with the relations of the recursive fields. -/
theorem DataType.blockRel_closed
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    {T : DataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : T.ctorRel T.name (S (DataType.blockRel Ts S)) v w) :
    DataType.blockRel Ts S T.name v w :=
  fun X hX =>
    have ⟨c, hc, ts, us, hv, hw, hs⟩ := h
    hX T hT v w ⟨c, hc, ts, us, hv, hw, hmono _ X (fun _ _ _ h => h X hX) T hT c hc ts us hs⟩

/-- `(eq_μ)` relates the constructors that the clauses relate only, when the equality of the terms
of the fields grows with the relations of the recursive fields. -/
theorem DataType.blockRel_inv
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    {D : Name} {v w : Term 0 []} (h : DataType.blockRel Ts S D v w) :
    ∃ T ∈ Ts, T.name = D ∧ T.ctorRel T.name (S (DataType.blockRel Ts S)) v w :=
  h (fun D v w => ∃ T ∈ Ts, T.name = D ∧ T.ctorRel T.name (S (DataType.blockRel Ts S)) v w)
    fun T hT _ _ ⟨c, hc, ts, us, hv, hw, hs⟩ =>
      ⟨T, hT, rfl, c, hc, ts, us, hv, hw,
        hmono _ _ (fun _ _ _ ⟨_, hT', hD, hr⟩ => hD ▸ DataType.blockRel_closed hmono hT' hr)
          T hT c hc ts us hs⟩

/-- `(eq_μ)` is a partial equivalence relation, when the equality of the terms of the fields grows
with the relations of the recursive fields, and inverts and composes them, and when the names of the
types and of the constructors of each type are distinct. -/
theorem DataType.blockRel_isPer
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us)
    (hsymm : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D w v) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c us ts)
    (htrans : ∀ X Y Z : Name → TermRel, (∀ D u v w, X D u v → Y D v w → Z D u w) → ∀ T ∈ Ts,
      ∀ c ∈ T.constructors, ∀ ts us vs, S X c ts us → S Y c us vs → S Z c ts vs)
    (hn : (Ts.map (·.name)).Nodup) (hc : ∀ T ∈ Ts, (T.constructors.map (·.name)).Nodup)
    (D : Name) : IsPer (DataType.blockRel Ts S D) where
  symm h := h (fun D v w => DataType.blockRel Ts S D w v) fun T hT v w ⟨c, hcm, ts, us, hv, hw, hs⟩ =>
    DataType.blockRel_closed hmono hT
      ⟨c, hcm, us, ts, hw, hv, hsymm _ _ (fun _ _ _ h => h) T hT c hcm ts us hs⟩
  trans h₁ h₂ := h₁ (fun D u v => ∀ w, DataType.blockRel Ts S D v w → DataType.blockRel Ts S D u w)
    (fun T hT u v ⟨c, hcm, ts, us, hu, hv, hs⟩ w hw => by
      obtain ⟨T', hT', hn', c', hcm', us', vs, hv', hw', hs'⟩ := DataType.blockRel_inv hmono hw
      cases List.eq_of_nodup_map hn hT' hT hn'
      obtain ⟨-, hcn, rfl⟩ := hv.inj hv'
      cases List.eq_of_nodup_map (hc T hT) hcm hcm' hcn
      exact DataType.blockRel_closed hmono hT
        ⟨c, hcm, ts, vs, hu, hw', htrans _ _ _ (fun _ _ _ _ h₁ h₂ => h₁ _ h₂) T hT c hcm ts us vs hs hs'⟩)
    _ h₂

/-- `(true_μ)` is closed under the clauses of the constructors, when the equality of the terms of
the fields grows with the truths of the recursive fields. -/
theorem DataType.blockTruth_closed {S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us,
      S' B c ts us → S' B' c ts us)
    {T : DataType j g k Δ} (hT : T ∈ Ts) (h : T.truth (S' (DataType.blockTruth Ts S'))) :
    DataType.blockTruth Ts S' T.name :=
  fun B hB =>
    have ⟨c, hc, ts, hs⟩ := h
    hB T hT ⟨c, hc, ts, hmono _ B (fun _ h => h B hB) T hT c hc ts ts hs⟩

/-- `(true_μ)` holds by the clause of a constructor only, when the equality of the terms of the
fields grows with the truths of the recursive fields. -/
theorem DataType.blockTruth_inv {S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us,
      S' B c ts us → S' B' c ts us)
    {D : Name} (h : DataType.blockTruth Ts S' D) :
    ∃ T ∈ Ts, T.name = D ∧ T.truth (S' (DataType.blockTruth Ts S')) :=
  h (fun D => ∃ T ∈ Ts, T.name = D ∧ T.truth (S' (DataType.blockTruth Ts S')))
    fun T hT ⟨c, hc, ts, hs⟩ =>
      ⟨T, hT, rfl, c, hc, ts, hmono _ _ (fun _ ⟨_, hT', hD, ht⟩ => hD ▸
        DataType.blockTruth_closed hmono hT' ht) T hT c hc ts ts hs⟩

end LeastFixedPoints

/-- `(eq_μ)` relates the same terms for equalities of the terms of the fields that relate the same
terms. -/
theorem DataType.blockRel_congr {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
    {S S' : (Name → TermRel) → Constructor j g k Δ → FieldsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us ↔ S' X c ts us) (D : Name) :
    ∀ v w, DataType.blockRel Ts S D v w ↔ DataType.blockRel Ts S' D v w :=
  fun _ _ => ⟨fun hr X hX => hr X fun T hT v w hc =>
      hX T hT v w ((DataType.ctorRel_congr (h X T hT) v w).1 hc),
    fun hr X hX => hr X fun T hT v w hc => hX T hT v w ((DataType.ctorRel_congr (h X T hT) v w).2 hc)⟩

/-- `(true_μ)` is the same for equalities of the terms of the fields that relate the same terms. -/
theorem DataType.blockTruth_congr {j g k : Nat} {Δ : Scope} {Ts : List (DataType j g k Δ)}
    {S S' : (Name → Prop) → Constructor j g k Δ → FieldsRel}
    (h : ∀ B, ∀ T ∈ Ts, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us ↔ S' B c ts us) (D : Name) :
    DataType.blockTruth Ts S D ↔ DataType.blockTruth Ts S' D :=
  ⟨fun hr B hB => hr B fun T hT hc => hB T hT ((DataType.truth_congr (h B T hT)).1 hc),
    fun hr B hB => hr B fun T hT hc => hB T hT ((DataType.truth_congr (h B T hT)).2 hc)⟩

/-- A closed term has the observations of one corecursor at most. -/
theorem Term.CorecObservations.unique {D D' : Name} {v : Term 0 []} {o o' : Observations}
    (h : v.CorecObservations D o) (h' : v.CorecObservations D' o') : o = o' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, h', rfl⟩ := h'
  cases h'
  rfl

/-- The equality of the abstractions for a destructor is a partial equivalence relation, when the
equality of its arguments is one, and so is the equality of the terms of its result at equal
arguments, the same for equal arguments. -/
theorem AbstractionRel.isPer {ps : List Parameter} {SΘ : FieldsRel} {F : Terms 0 [] → TermRel}
    (hS : IsPer SΘ) (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → IsPer (F ts.terms))
    (hresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u) :
    IsPer (AbstractionRel (ps := ps) SΘ F) where
  symm {_ _} h ts us hts :=
    have hst := hS.symm hts
    (hresp _ _ hst _ _).1 ((hF us (hS.trans hst hts)).symm (h us ts hst))
  trans {_ _ _} h h' ts us hts :=
    have huu := hS.trans (hS.symm hts) hts
    (hF ts (hS.trans hts (hS.symm hts))).trans (h ts us hts) ((hresp _ _ hts _ _).2 (h' us us huu))

/-- The equalities of the abstractions for a destructor relate the same abstractions, when the
equalities of its arguments relate the same arguments, and those of its result the same terms. -/
theorem AbstractionRel.congr {ps : List Parameter} {SΘ SΘ' : FieldsRel} {F F' : Terms 0 [] → TermRel}
    (hSp : IsPer SΘ) (hS : ∀ ts us, SΘ ts us ↔ SΘ' ts us)
    (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u, F ts.terms t u ↔ F' ts.terms t u) :
    ∀ f₁ f₂, AbstractionRel (ps := ps) SΘ F f₁ f₂ ↔ AbstractionRel SΘ' F' f₁ f₂ :=
  fun _ _ =>
    ⟨fun h ts us hts =>
      have hts' := (hS _ _).2 hts
      (hF ts (hSp.trans hts' (hSp.symm hts')) _ _).1 (h ts us hts'),
    fun h ts us hts => (hF ts (hSp.trans hts (hSp.symm hts)) _ _).2 (h ts us ((hS _ _).1 hts))⟩

/-- The equality of the abstractions for a destructor `d` followed by the destructors after it is a
partial equivalence relation, when the equality `E` of the abstractions for `d` is one, and so is
the equality `G f` of the destructors after it for each abstraction `f`, the same for equal
abstractions. -/
theorem ObsRel.cons_isPer {d : Name} {ps : List Parameter}
    {E : Term 0 (Scope.extend [] ps.length) → Term 0 (Scope.extend [] ps.length) → Prop}
    {G : Term 0 (Scope.extend [] ps.length) → ObsRel} (hE : IsPer E) (hG : ∀ f, E f f → IsPer (G f))
    (hresp : ∀ f₁ f₂, E f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂) :
    IsPer (fun o₁ o₂ : Observations => E (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂) where
  symm := fun ⟨h₁, h₂⟩ =>
    ⟨hE.symm h₁, (hG _ (hE.trans (hE.symm h₁) h₁)).symm ((hresp _ _ h₁ _ _).1 h₂)⟩
  trans := fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨hE.trans h₁ h₁', (hG _ (hE.trans h₁ (hE.symm h₁))).trans h₂ ((hresp _ _ h₁ _ _).2 h₂')⟩

/-- The equalities of the abstractions for a destructor `d` followed by the destructors after it
relate the same abstractions, when those for `d` do, and those of the destructors after it do for
each abstraction for `d`. -/
theorem ObsRel.cons_congr {d : Name} {ps : List Parameter}
    {E E' : Term 0 (Scope.extend [] ps.length) → Term 0 (Scope.extend [] ps.length) → Prop}
    {G G' : Term 0 (Scope.extend [] ps.length) → ObsRel} (hEp : IsPer E)
    (hE : ∀ f₁ f₂, E f₁ f₂ ↔ E' f₁ f₂) (hG : ∀ f, E f f → ∀ o₁ o₂, G f o₁ o₂ ↔ G' f o₁ o₂) :
    ∀ o₁ o₂ : Observations, (E (o₁ d ps) (o₂ d ps) ∧ G (o₁ d ps) o₁ o₂) ↔
      (E' (o₁ d ps) (o₂ d ps) ∧ G' (o₁ d ps) o₁ o₂) :=
  fun _ _ =>
    ⟨fun ⟨h₁, h₂⟩ => ⟨(hE _ _).1 h₁, (hG _ (hEp.trans h₁ (hEp.symm h₁)) _ _).1 h₂⟩,
      fun ⟨h₁, h₂⟩ =>
        have h₁' := (hE _ _).2 h₁
        ⟨h₁', (hG _ (hEp.trans h₁' (hEp.symm h₁')) _ _).2 h₂⟩⟩

/-- `(eq_d)` relates the terms that it relates for an equality of the destructors that relates
fewer abstractions. -/
theorem corecRel_mono {D : Name} {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ → S' o₁ o₂) :
    ∀ v w, corecRel D S v w → corecRel D S' v w :=
  fun _ _ ⟨o₁, o₂, hv, hw, hS⟩ => ⟨o₁, o₂, hv, hw, h _ _ hS⟩

/-- `(true_d)` holds when it holds for an equality of the destructors that relates fewer
abstractions. -/
theorem ObsRel.truth_mono {S S' : ObsRel} (h : ∀ o₁ o₂, S o₁ o₂ → S' o₁ o₂) :
    S.truth → S'.truth :=
  fun ⟨o, ho⟩ => ⟨o, h o o ho⟩

/-! ### Greatest Fixed Points

The equality `(eq_ν)` of the terms of the instances of a block of codata types is the greatest
relation consistent with the clauses of its destructors, which contains every relation consistent
with them; it is consistent with them itself, closed under them, and a partial equivalence
relation, when the equality of the destructors grows with the relations of the recursive
destructors, and inverts and composes them, by the strict positivity of their occurrences. -/

section GreatestFixedPoints

variable {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
  {S : (Name → TermRel) → CodataType j g k Δ → ObsRel}

/-- `(eq_ν)` is consistent with the clauses of the destructors, when the equality of the destructors
grows with the relations of the recursive destructors. -/
theorem CodataType.blockRel_unfold
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₁ o₂)
    {T : CodataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : CodataType.blockRel Ts S T.name v w) :
    corecRel T.name (S (CodataType.blockRel Ts S) T) v w :=
  have ⟨X, hX, hv⟩ := h
  corecRel_mono (hmono X _ (fun _ _ _ h => ⟨X, hX, h⟩) T hT) _ _ (hX T hT v w hv)

/-- `(eq_ν)` is closed under the clauses of the destructors, when the equality of the destructors
grows with the relations of the recursive destructors, and when the names of the types are
distinct. -/
theorem CodataType.blockRel_fold
    (hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₁ o₂)
    (hn : (Ts.map (·.name)).Nodup) {T : CodataType j g k Δ} (hT : T ∈ Ts) {v w : Term 0 []}
    (h : corecRel T.name (S (CodataType.blockRel Ts S) T) v w) :
    CodataType.blockRel Ts S T.name v w :=
  ⟨fun D a b => CodataType.blockRel Ts S D a b ∨
      (D = T.name ∧ corecRel T.name (S (CodataType.blockRel Ts S) T) a b),
    fun T' hT' a b hab => by
      rcases hab with hab | ⟨hD, hab⟩
      · exact corecRel_mono (hmono _ _ (fun _ _ _ h => .inl h) T' hT') _ _
          (CodataType.blockRel_unfold hmono hT' hab)
      · cases List.eq_of_nodup_map hn hT hT' hD.symm
        exact corecRel_mono (hmono _ _ (fun _ _ _ h => .inl h) T hT) _ _ hab,
    .inr ⟨rfl, h⟩⟩

/-- `(eq_ν)` is a partial equivalence relation, when the equality of the destructors inverts and
composes the relations of the recursive destructors. -/
theorem CodataType.blockRel_isPer
    (hsymm : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D w v) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S X T o₁ o₂ → S Y T o₂ o₁)
    (htrans : ∀ X Y Z : Name → TermRel, (∀ D u v w, X D u v → Y D v w → Z D u w) → ∀ T ∈ Ts,
      ∀ o₁ o₂ o₃, S X T o₁ o₂ → S Y T o₂ o₃ → S Z T o₁ o₃)
    (D : Name) : IsPer (CodataType.blockRel Ts S D) where
  symm := fun ⟨X, hX, h⟩ => ⟨fun D v w => X D w v, fun T hT v w hvw =>
      have ⟨o₁, o₂, hw, hv, hs⟩ := hX T hT w v hvw
      ⟨o₂, o₁, hv, hw, hsymm X _ (fun _ _ _ h => h) T hT o₁ o₂ hs⟩, h⟩
  trans := fun ⟨X, hX, h⟩ ⟨Y, hY, h'⟩ => ⟨fun D u w => ∃ v, X D u v ∧ Y D v w,
      fun T hT u w ⟨v, huv, hvw⟩ => by
        obtain ⟨o₁, o₂, hu, hv, hs⟩ := hX T hT u v huv
        obtain ⟨o₂', o₃, hv', hw, hs'⟩ := hY T hT v w hvw
        rw [← hv.unique hv'] at hs'
        exact ⟨o₁, o₃, hu, hw, htrans X Y _ (fun _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩) T hT o₁ o₂ o₃ hs hs'⟩,
      _, h, h'⟩

/-- `(true_ν)` is consistent with the clauses of the destructors, when the equality of the
destructors grows with the truths of the recursive destructors. -/
theorem CodataType.blockTruth_unfold {S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S' B T o₁ o₂ → S' B' T o₁ o₂)
    {T : CodataType j g k Δ} (hT : T ∈ Ts) (h : CodataType.blockTruth Ts S' T.name) :
    (S' (CodataType.blockTruth Ts S') T).truth :=
  have ⟨B, hB, hb⟩ := h
  ObsRel.truth_mono (hmono B _ (fun _ h => ⟨B, hB, h⟩) T hT) (hB T hT hb)

/-- `(true_ν)` holds by the clause of the destructors of its type, when the equality of the
destructors grows with the truths of the recursive destructors, and when the names of the types are
distinct. -/
theorem CodataType.blockTruth_fold {S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ Ts, ∀ o₁ o₂,
      S' B T o₁ o₂ → S' B' T o₁ o₂)
    (hn : (Ts.map (·.name)).Nodup) {T : CodataType j g k Δ} (hT : T ∈ Ts)
    (h : (S' (CodataType.blockTruth Ts S') T).truth) : CodataType.blockTruth Ts S' T.name :=
  ⟨fun D => CodataType.blockTruth Ts S' D ∨ (D = T.name ∧ (S' (CodataType.blockTruth Ts S') T).truth),
    fun T' hT' hb => by
      rcases hb with hb | ⟨hD, hb⟩
      · exact ObsRel.truth_mono (hmono _ _ (fun _ h => .inl h) T' hT')
          (CodataType.blockTruth_unfold hmono hT' hb)
      · cases List.eq_of_nodup_map hn hT hT' hD.symm
        exact ObsRel.truth_mono (hmono _ _ (fun _ h => .inl h) T hT) hb,
    .inr ⟨rfl, h⟩⟩

end GreatestFixedPoints

/-- `(eq_ν)` relates the same terms for equalities of the destructors that relate the same
abstractions. -/
theorem CodataType.blockRel_congr {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
    {S S' : (Name → TermRel) → CodataType j g k Δ → ObsRel}
    (h : ∀ X, ∀ T ∈ Ts, ∀ o₁ o₂, S X T o₁ o₂ ↔ S' X T o₁ o₂) (D : Name) :
    ∀ v w, CodataType.blockRel Ts S D v w ↔ CodataType.blockRel Ts S' D v w :=
  fun _ _ => ⟨fun ⟨X, hX, hv⟩ => ⟨X, fun T hT v w hx =>
      corecRel_mono (fun o₁ o₂ => (h X T hT o₁ o₂).1) _ _ (hX T hT v w hx), hv⟩,
    fun ⟨X, hX, hv⟩ => ⟨X, fun T hT v w hx =>
      corecRel_mono (fun o₁ o₂ => (h X T hT o₁ o₂).2) _ _ (hX T hT v w hx), hv⟩⟩

/-- `(true_ν)` is the same for equalities of the destructors that relate the same abstractions. -/
theorem CodataType.blockTruth_congr {j g k : Nat} {Δ : Scope} {Ts : List (CodataType j g k Δ)}
    {S S' : (Name → Prop) → CodataType j g k Δ → ObsRel}
    (h : ∀ B, ∀ T ∈ Ts, ∀ o₁ o₂, S B T o₁ o₂ ↔ S' B T o₁ o₂) (D : Name) :
    CodataType.blockTruth Ts S D ↔ CodataType.blockTruth Ts S' D :=
  ⟨fun ⟨B, hB, hb⟩ => ⟨B, fun T hT h' => ObsRel.truth_mono (fun o₁ o₂ => (h B T hT o₁ o₂).1)
      (hB T hT h'), hb⟩,
    fun ⟨B, hB, hb⟩ => ⟨B, fun T hT h' => ObsRel.truth_mono (fun o₁ o₂ => (h B T hT o₁ o₂).2)
      (hB T hT h'), hb⟩⟩

/-! ### A Type Has One Level and One Sort -/

/-- Two instances of a declared type of a signature whose names are distinct, given by a data type
and by a codata type, do not exist. -/
theorem Signature.Distinct.inst_data_codata {sig : Signature} (hd : sig.Distinct)
    {decl₁ decl₂ : TypeDeclaration} {D₁ D₂ : Name}
    {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope} {qs₁ qs₂ : List Quality}
    {ls₁ ls₂ : List (Level 0)} {ps₁ ps₂ : List Grade} {as₁ : InstanceArgs 0 [] decl₁.scope}
    {as₂ : InstanceArgs 0 [] decl₂.scope} (h₁ : sig.HasDataType D₁ decl₁ T₁)
    (h₂ : sig.HasCodataType D₂ decl₂ T₂)
    (hv : Term.inst D₁ qs₁ ls₁ ps₁ as₁ = Term.inst D₂ qs₂ ls₂ ps₂ as₂) : False := by
  obtain ⟨-, hD, -⟩ := Term.inst.inj hv
  subst hD
  exact hd.not_hasDataType_hasCodataType h₁ h₂

/-- A type of a universe has one level, in a signature whose names are distinct. -/
theorem UnivRel.level {sig : Signature} {ι : Interpretation} {n m : Nat} {below₁ : LevelRel.Below n}
    {below₂ : LevelRel.Below m} {v : Term 0 []} {R R' : TermRel} (hd : sig.Distinct)
    (h : UnivRel sig ι n below₁ v R) (h' : UnivRel sig ι m below₂ v R') : n = m := by
  cases h with
  | univ hl hk => cases h' with
    | univ hl' hk' => omega
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop hl hk => cases h' with
    | prop hl' hk' => omega
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | data h _ _ _ hv _ hn => cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact hn.symm.trans hn'
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | codata h _ _ _ hv _ hn => cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact hn.symm.trans hn'

/-- A type of a universe is not a proposition, in a signature whose names are distinct. -/
theorem UnivRel.not_prop {sig : Signature} {ι : Interpretation} {n m : Nat}
    {below₁ : LevelRel.Below n} {below₂ : LevelRel.Below m} {v : Term 0 []} {R : TermRel} {b : Prop}
    (hd : sig.Distinct) (h : UnivRel sig ι n below₁ v R) (h' : PropRel sig ι m below₂ v b) :
    False := by
  cases h' with
  | data h' _ _ _ hv' hs' =>
    subst hv'
    cases h with
    | data h _ _ _ hv hs =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata h _ _ _ hv => exact hd.inst_data_codata h' h hv
  | codata h' _ _ _ hv' hs' =>
    subst hv'
    cases h with
    | data h _ _ _ hv => exact hd.inst_data_codata h h' hv.symm
    | codata h _ _ _ hv hs =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact nomatch hs.symm.trans hs'

/-- A proposition has one level, in a signature whose names are distinct. -/
theorem PropRel.level {sig : Signature} {ι : Interpretation} {n m : Nat} {below₁ : LevelRel.Below n}
    {below₂ : LevelRel.Below m} {v : Term 0 []} {b b' : Prop} (hd : sig.Distinct)
    (h : PropRel sig ι n below₁ v b) (h' : PropRel sig ι m below₂ v b') : n = m := by
  cases h with
  | data h _ _ _ hv _ hn => cases h' with
    | data h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact hn.symm.trans hn'
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | codata h _ _ _ hv _ hn => cases h' with
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ hn' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      exact hn.symm.trans hn'

/-! ### The Relations of a Level

The partial equivalence and the uniqueness are proved together, since the equality `(eq_μ)` of a
block is a partial equivalence relation by the transfer of the equalities of the fields between
relations of the recursive fields, which identifies the equalities of the fields that are not
recursive by their uniqueness. -/

mutual

/-- The equality of the terms of a type of `U_n` is a partial equivalence relation, if the relations
of the levels below `n` are partial equivalence relations. -/
theorem UnivRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {R : TermRel} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R → IsPer R
  | .univ (k := k) _ hk =>
    have hL := ih k (hk ▸ Nat.lt_succ_self k)
    ⟨fun ⟨R', h₁, h₂⟩ => ⟨R', h₂, h₁⟩,
      fun ⟨R₁, h₁, h₂⟩ ⟨_, h₂', h₃⟩ => ⟨R₁, h₁, hL.univ_eq h₂' h₂ ▸ h₃⟩⟩
  | .prop (k := k) _ hk =>
    have hL := ih k (hk ▸ Nat.lt_succ_self k)
    ⟨fun ⟨b₁, b₂, h₁, h₂, hb⟩ => ⟨b₂, b₁, h₂, h₁, hb.symm⟩,
      fun ⟨b₁, _, h₁, h₂, hb⟩ ⟨_, b₃, h₂', h₃, hb'⟩ =>
        ⟨b₁, b₃, h₁, h₃, hb.trans ((hL.prop_unique h₂ h₂').trans hb')⟩⟩
  | .data h _ _ _ _ _ _ _ hS =>
    DataType.blockRel_isPer
      (fun X Y hXY T hT c hc ts us hs => TelRel.mono hd ih (hS X T hT c hc) _ _ _ (hS Y T hT c hc)
        (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _) ts us hs)
      (fun X Y hXY T hT c hc ts us hs => TelRel.symm_of hd ih (hS X T hT c hc) _ _ _
        (hS Y T hT c hc) (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_symm (hXY D)) _)
        ts us hs)
      (fun X Y Z hXYZ T hT c hc ts us vs hs hs' => TelRel.trans_of hd ih (hS X T hT c hc) _ _ _
        (hS Y T hT c hc) _ _ _ (hS Z T hT c hc)
        (fun _ => Option.rel_map₃
          (r := fun (x y z : TermRel) => ∀ t u w, x t u → y u w → z t w)
          (f := fun D => (X D).computed sig ι) (g := fun D => (Y D).computed sig ι)
          (h := fun D => (Z D).computed sig ι)
          (fun D _ _ _ => TermRel.computed_trans hd (hXYZ D)) _)
        ts us vs hs hs')
      (TypeDeclaration.dataTypes_nodup (hd.nodup h.1))
      (fun _ hT => hd.constructors_nodup ⟨h.1, hT, rfl⟩) _
  | .codata _ _ _ _ _ _ _ _ hS =>
    CodataType.blockRel_isPer
      (fun X Y hXY T hT o₁ o₂ hs => DesRel.symm_of hd ih (hS X T hT) _ _ _ (hS Y T hT)
        (fun _ => Option.rel_map (fun D _ _ => TermRel.computed_symm (hXY D)) _) o₁ o₂ hs)
      (fun X Y Z hXYZ T hT o₁ o₂ o₃ hs hs' => DesRel.trans_of hd ih (hS X T hT) _ _ _ (hS Y T hT)
        _ _ _ (hS Z T hT)
        (fun _ => Option.rel_map₃
          (r := fun (x y z : TermRel) => ∀ t u w, x t u → y u w → z t w)
          (f := fun D => (X D).computed sig ι) (g := fun D => (Y D).computed sig ι)
          (h := fun D => (Z D).computed sig ι)
          (fun D _ _ _ => TermRel.computed_trans hd (hXYZ D)) _)
        o₁ o₂ o₃ hs hs') _
termination_by structural h => h

/-- The equality of the abstractions for destructors relates in the other order the abstractions
that the equality of the same destructors relates, at relations of the recursive destructors that do
so. -/
theorem DesRel.symm_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y u t) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ → S₂ o₂ o₁
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' hresp' _ =>
      have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
        have hf := hEp.trans h₁ (hEp.symm h₁)
        ⟨(hEE _ _).1 (hEp.symm h₁), (hresp' _ _ ((hEE _ _).1 h₁) _ _).1
          (DesRel.symm_of hd ih (hG _ hf) _ _ _ (hG' _ ((hEE _ _).1 hf)) (fun i => hR (i + 1))
            _ _ h₂)⟩
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
          ⟨fun ts us hts => hr _ _ (h₁ us ts (hSΘp.symm ((hSS _ _).2 hts))),
            DesRel.symm_of hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
              (fun i => hR (i + 1)) _ _ h₂⟩
termination_by structural h _ _ _ _ _ => h

/-- The equality of the abstractions for destructors relates the abstractions that two equalities of
the same destructors relate in a chain, at relations of the recursive destructors that do so. -/
theorem DesRel.trans_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
      ∀ (s₃ : Quality) (rs₃ : Nat → Option TermRel) (S₃ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₃ rs₃ ds @θ S₃ →
        (∀ i, (rs₁ i = none ∧ rs₂ i = none ∧ rs₃ i = none) ∨
          ∃ x y z, rs₁ i = some x ∧ rs₂ i = some y ∧ rs₃ i = some z ∧
            ∀ t u w, x t u → y u w → z t w) →
        ∀ o₁ o₂ o₃, S₁ o₁ o₂ → S₂ o₂ o₃ → S₃ o₁ o₃
  | .nil, _, _, _, h', _, _, _, h'', _ => by
    cases h'; cases h''; exact fun _ _ _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', _, _, _, h'', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' hresp' _ =>
      cases h'' with
      | cons hΘ'' F'' _ hF'' _ _ hG'' _ _ =>
        have hSS' := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        have hSS'' := TelRel.congr hd ih hΘ _ _ _ hΘ'' TelRel.none_rel
        have hFF' : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
            F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
          have ⟨_, hv⟩ := hB ts hts
          FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS' _ _).1 hts) _ hv)
        have hFF'' : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
            F ts.terms t u ↔ F'' ts.terms t u := fun ts hts =>
          have ⟨_, hv⟩ := hB ts hts
          FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF'' ts ((hSS'' _ _).1 hts) _ hv)
        have hEE' := AbstractionRel.congr hSΘp hSS' hFF'
        have hEE'' := AbstractionRel.congr hSΘp hSS'' hFF''
        exact fun o₁ o₂ o₃ ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
          have hf := hEp.trans h₁ (hEp.symm h₁)
          ⟨(hEE'' _ _).1 (hEp.trans h₁ ((hEE' _ _).2 h₁')),
            DesRel.trans_of hd ih (hG _ hf) _ _ _ (hG' _ ((hEE' _ _).1 hf)) _ _ _
              (hG'' _ ((hEE'' _ _).1 hf)) (fun i => hR (i + 1)) _ _ _ h₂
              ((hresp' _ _ ((hEE' _ _).1 h₁) _ _).2 h₂')⟩
      | recursive hrs'' =>
        rcases hR 0 with ⟨-, -, h0⟩ | ⟨_, _, _, h0, -⟩
        · rw [hrs''] at h0; cases h0
        · rw [hrs] at h0; cases h0
    | recursive hrs' =>
      rcases hR 0 with ⟨-, h0, -⟩ | ⟨_, _, _, h0, -⟩
      · rw [hrs'] at h0; cases h0
      · rw [hrs] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', _, _, _, h'', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' =>
      rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, h0, -⟩
      · rw [hrs] at h0; cases h0
      · rw [hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      cases h'' with
      | cons _ _ _ _ _ _ _ _ hrs'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, -, h0, -⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs''] at h0; cases h0
      | recursive hrs'' hΘ'' _ hG'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨x, y, z, hx, hy, hz, hr⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs] at hx; rw [hrs'] at hy; rw [hrs''] at hz
          cases hx; cases hy; cases hz
          have hSS' := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
          have hSS'' := TelRel.congr hd ih hΘ _ _ _ hΘ'' TelRel.none_rel
          exact fun o₁ o₂ o₃ ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
            ⟨fun ts us hts =>
              have hts' := (hSS'' _ _).2 hts
              have hus := hSΘp.trans (hSΘp.symm hts') hts'
              hr _ _ _ (h₁ ts us hts') (h₁' us us ((hSS' _ _).1 hus)),
              DesRel.trans_of hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
                _ _ _ (hG'' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1)) _ _ _ h₂ h₂'⟩
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-- The equalities of the abstractions for destructors relate the same abstractions, at relations of
the recursive destructors that relate the same terms. -/
theorem DesRel.congr {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u ↔ y t u) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ ↔ S₂ o₁ o₂
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ => .rfl
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' _ _ =>
      have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact ObsRel.cons_congr hEp hEE fun f hf =>
        DesRel.congr hd ih (hG f hf) _ _ _ (hG' f ((hEE f f).1 hf)) (fun i => hR (i + 1))
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (SΘ := SΘ) hrs hΘ _ hG, _, _, _, h', hR => by
    have hSΘp : IsPer SΘ :=
      ⟨fun h => TelRel.symm_of hd ih hΘ _ _ _ hΘ TelRel.none_rel _ _ h,
        fun h h' => TelRel.trans_of hd ih hΘ _ _ _ hΘ _ _ _ hΘ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
          _ _ _ h h'⟩
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.congr hd ih hΘ _ _ _ hΘ' TelRel.none_rel
        have hGG := DesRel.congr hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _
          (hG' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1))
        exact fun o₁ o₂ =>
          and_congr (AbstractionRel.congr hSΘp hSS (fun _ _ => hr) _ _) (hGG o₁ o₂)
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the type of a field is a partial equivalence relation. -/
theorem FieldRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {v : Term 0 []} {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → IsPer F
  | .univ _ h => TermRel.computed_isPer hd (UnivRel.isPer hd ih h)
  | .univBelow _ m hm h => TermRel.computed_isPer hd ((ih m hm).univ_isPer h)
  | .prop _ => ⟨id, fun h _ => h⟩
  | .propBelow _ _ _ => ⟨id, fun h _ => h⟩
termination_by structural h => h

/-- The equality of the terms of the fields of a telescope relates the terms that the equality of
the same telescope relates, at relations of the recursive fields that relate more terms. -/
theorem TelRel.mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y t u) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us → S₂ ts us
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ h => h
  | .cons hA hF _ hG hresp hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      refine FieldsRel.cons_mono (fun t u h => (hFF t u).1 h) fun t u htu ts us hg => ?_
      have htt := hFp.trans htu (hFp.symm htu)
      exact TelRel.mono hd ih (hG t htt) _ _ _ (hG' t ((hFF t t).1 htt)) (fun i => hR (i + 1))
        ts us hg
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact FieldsRel.cons_mono hr fun t _ _ ts us hg =>
          TelRel.mono hd ih (hG t) _ _ _ (hG' t) (fun i => hR (i + 1)) ts us hg
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the fields of a telescope relates in the other order the terms that
the equality of the same telescope relates, at relations of the recursive fields that do so. -/
theorem TelRel.symm_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y u t) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us → S₂ us ts
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ h => FieldsRel.nil_isPer.symm h
  | .cons hA hF _ hG hresp hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      refine FieldsRel.cons_symm (fun t u h => (hFF u t).1 (hFp.symm h)) fun t u htu ts us hg => ?_
      have huu := hFp.trans (hFp.symm htu) htu
      exact TelRel.symm_of hd ih (hG u huu) _ _ _ (hG' u ((hFF u u).1 huu)) (fun i => hR (i + 1))
        ts us ((hresp t u htu ts us).1 hg)
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        exact FieldsRel.cons_symm hr fun _ u _ ts us hg =>
          TelRel.symm_of hd ih (hG u) _ _ _ (hG' u) (fun i => hR (i + 1)) ts us hg
termination_by structural h _ _ _ _ _ => h

/-- The equality of the terms of the fields of a telescope relates the terms that two equalities of
the same telescope relate in a chain, at relations of the recursive fields that do so. -/
theorem TelRel.trans_of {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
      ∀ (s₃ : Quality) (rs₃ : Nat → Option TermRel) (S₃ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₃ rs₃ Θ S₃ →
        (∀ i, (rs₁ i = none ∧ rs₂ i = none ∧ rs₃ i = none) ∨
          ∃ x y z, rs₁ i = some x ∧ rs₂ i = some y ∧ rs₃ i = some z ∧
            ∀ t u w, x t u → y u w → z t w) →
        ∀ ts us vs, S₁ ts us → S₂ us vs → S₃ ts vs
  | .nil, _, _, _, h', _, _, _, h'', _ => by
    cases h'; cases h''; exact fun _ _ _ h h' => FieldsRel.nil_isPer.trans h h'
  | .cons hA hF _ hG _ hrs, _, _, _, h', _, _, _, h'', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' hresp' _ =>
      cases h'' with
      | cons hA'' hF'' _ hG'' _ _ =>
        cases Computesι.det hd hA hA'
        cases Computesι.det hd hA hA''
        have hFF' := FieldRel.unique hd ih hF _ _ hF'
        have hFF'' := FieldRel.unique hd ih hF _ _ hF''
        refine FieldsRel.cons_trans
          (fun t u w h₁ h₂ => (hFF'' t w).1 (hFp.trans h₁ ((hFF' u w).2 h₂)))
          fun t u w htu huw ts us vs hg hg' => ?_
        have htt := hFp.trans htu (hFp.symm htu)
        exact TelRel.trans_of hd ih (hG t htt) _ _ _ (hG' t ((hFF' t t).1 htt)) _ _ _
          (hG'' t ((hFF'' t t).1 htt)) (fun i => hR (i + 1)) ts us vs hg
          ((hresp' t u ((hFF' t u).1 htu) us vs).2 hg')
      | recursive hrs'' _ _ =>
        rcases hR 0 with ⟨-, -, h0⟩ | ⟨_, _, _, h0, -⟩
        · rw [hrs''] at h0; cases h0
        · rw [hrs] at h0; cases h0
    | recursive hrs' _ _ =>
      rcases hR 0 with ⟨-, h0, -⟩ | ⟨_, _, _, h0, -⟩
      · rw [hrs'] at h0; cases h0
      · rw [hrs] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', _, _, _, h'', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' =>
      rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, h0, -⟩
      · rw [hrs] at h0; cases h0
      · rw [hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      cases h'' with
      | cons _ _ _ _ _ hrs'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨_, _, _, -, -, h0, -⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs''] at h0; cases h0
      | recursive hrs'' _ hG'' =>
        rcases hR 0 with ⟨h0, -, -⟩ | ⟨x, y, z, hx, hy, hz, hr⟩
        · rw [hrs] at h0; cases h0
        · rw [hrs] at hx; rw [hrs'] at hy; rw [hrs''] at hz
          cases hx; cases hy; cases hz
          exact FieldsRel.cons_trans hr fun t _ _ _ _ ts us vs hg hg' =>
            TelRel.trans_of hd ih (hG t) _ _ _ (hG' t) _ _ _ (hG'' t) (fun i => hR (i + 1))
              ts us vs hg hg'
termination_by structural h _ _ _ _ _ _ _ _ _ => h

/-- The equalities of the terms of the fields of a telescope relate the same terms, at relations of
the recursive fields that relate the same terms. -/
theorem TelRel.congr {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S₁ : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u ↔ y t u) (rs₁ i) (rs₂ i)) →
        ∀ ts us, S₁ ts us ↔ S₂ ts us
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ => .rfl
  | .cons hA hF _ hG _ hrs, _, _, _, h', hR => by
    have hFp := FieldRel.isPer hd ih hF
    cases h' with
    | cons hA' hF' _ hG' _ _ =>
      cases Computesι.det hd hA hA'
      have hFF := FieldRel.unique hd ih hF _ _ hF'
      exact FieldsRel.cons_congr hFp hFF fun a ha =>
        TelRel.congr hd ih (hG a ha) _ _ _ (hG' a ((hFF a a).1 ha)) (fun i => hR (i + 1))
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hGG := TelRel.congr hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
          (fun i => hR (i + 1))
        intro ts us
        match ts, us with
        | .nil, _ => exact .rfl
        | .cons _ _, .nil => exact .rfl
        | .cons t ts, .cons u us => exact and_congr (hr t u) (hGG ts us)
termination_by structural h _ _ _ _ _ => h

/-- A type of `U_n` has a unique equality of its terms, if the relations of the levels below `n` are
partial equivalence relations. -/
theorem UnivRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {R : TermRel} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R →
      ∀ (R' : TermRel), UnivRel sig ι n (fun m _ => levelRel sig ι m) v R' →
        ∀ t u, R t u ↔ R' t u
  | .univ hl _, _, h' => by
    cases h' with
    | univ hl' _ => subst hl; subst hl'; exact fun _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .prop hl _, _, h' => by
    cases h' with
    | prop hl' _ => subst hl; subst hl'; exact fun _ _ => .rfl
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases hT
      cases has
      exact DataType.blockRel_congr (fun X T hT c hc => TelRel.congr hd ih (hS X T hT c hc) _ _ _
        (hS' X T hT c hc) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | univ => cases hv
    | prop => cases hv
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      cases hT
      cases has
      exact CodataType.blockRel_congr (fun X T hT => DesRel.congr hd ih (hS X T hT) _ _ _
        (hS' X T hT) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- A proposition of `Ω_n` has a unique truth. -/
theorem PropRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {v : Term 0 []} {b : Prop} :
    PropRel sig ι n (fun m _ => levelRel sig ι m) v b →
      ∀ (b' : Prop), PropRel sig ι n (fun m _ => levelRel sig ι m) v b' → (b ↔ b')
  | .data h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | data h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases hT
      cases has
      exact DataType.blockTruth_congr (fun B T hT c hc => TelRel.congr hd ih (hS B T hT c hc) _ _ _
        (hS' B T hT c hc) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
    | codata h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h h' hv').elim
  | .codata h _ _ _ hv _ _ _ hS, _, h' => by
    cases h' with
    | data h' _ _ _ hv' => subst hv; exact (hd.inst_data_codata h' h hv'.symm).elim
    | codata h' _ _ _ hv' _ _ _ hS' =>
      subst hv
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
      cases hT
      cases has
      exact CodataType.blockTruth_congr (fun B T hT => DesRel.congr hd ih (hS B T hT) _ _ _
        (hS' B T hT) fun _ => Option.rel_refl (fun _ _ _ => .rfl) _) _
termination_by structural h _ _ => h

/-- The type of a field has a unique equality of its terms. -/
theorem FieldRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {v : Term 0 []} {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F →
      ∀ (s' : Quality) (F' : TermRel), FieldRel sig ι n (fun m _ => levelRel sig ι m) s' v F' →
        ∀ t u, F t u ↔ F' t u
  | .univ _ h, _, _, h' => by
    have hu := UnivRel.unique hd ih h
    cases h' with
    | univ _ h' => exact TermRel.computed_congr (hu _ h')
    | univBelow _ m hm h' => exact absurd (UnivRel.level hd h (levelRel_univ_iff.1 h')) (by omega)
    | prop h' => exact (UnivRel.not_prop hd h h').elim
    | propBelow m _ h' => exact (UnivRel.not_prop hd h (levelRel_prop_iff.1 h')).elim
  | .univBelow _ m hm h, _, _, h' => by
    cases h' with
    | univ _ h' => exact absurd (UnivRel.level hd h' (levelRel_univ_iff.1 h)) (by omega)
    | univBelow _ m' hm' h' =>
      cases UnivRel.level hd (levelRel_univ_iff.1 h) (levelRel_univ_iff.1 h')
      exact TermRel.computed_congr ((ih m hm).univ_unique h h')
    | prop h' => exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h) h').elim
    | propBelow m' _ h' =>
      exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h) (levelRel_prop_iff.1 h')).elim
  | .prop h, _, _, h' => by
    have hu := PropRel.unique hd ih h
    cases h' with
    | univ _ h' => exact (UnivRel.not_prop hd h' h).elim
    | univBelow _ m _ h' => exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h') h).elim
    | prop h' => exact fun _ _ => hu _ h'
    | propBelow m hm h' => exact absurd (PropRel.level hd h (levelRel_prop_iff.1 h')) (by omega)
  | .propBelow m hm h, _, _, h' => by
    cases h' with
    | univ _ h' => exact (UnivRel.not_prop hd h' (levelRel_prop_iff.1 h)).elim
    | univBelow _ m' _ h' =>
      exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h') (levelRel_prop_iff.1 h)).elim
    | prop h' => exact absurd (PropRel.level hd h' (levelRel_prop_iff.1 h)) (by omega)
    | propBelow m' hm' h' =>
      cases PropRel.level hd (levelRel_prop_iff.1 h) (levelRel_prop_iff.1 h')
      exact fun _ _ => (ih m hm).prop_unique h h'
termination_by structural h _ _ _ => h

end

/-- The equality of the terms of the fields of a telescope is a partial equivalence relation, at
relations of the recursive fields that are. -/
theorem TelRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} (hrs : ∀ i x, rs i = some x → IsPer x)
    {ps : List Parameter} {Θ : Telescope 0 [] ps} {S : FieldsRel}
    (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S) : IsPer S where
  symm h' := TelRel.symm_of hd ih h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .none
    | some x => exact .some fun _ _ => (hrs i x hi).symm) _ _ h'
  trans h₁ h₂ := TelRel.trans_of hd ih h _ _ _ h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .inl ⟨rfl, rfl, rfl⟩
    | some x => exact .inr ⟨x, x, x, rfl, rfl, rfl, fun _ _ _ => (hrs i x hi).trans⟩) _ _ _ h₁ h₂

/-- A telescope has a unique equality of the terms of its fields, at given relations of its
recursive fields. -/
theorem TelRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps}
    {S : FieldsRel} (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S) (s' : Quality)
    (S' : FieldsRel) (h' : TelRel sig ι n (fun m _ => levelRel sig ι m) s' rs Θ S') :
    ∀ ts us, S ts us ↔ S' ts us :=
  TelRel.congr hd ih h _ _ _ h' fun _ => Option.rel_refl (fun _ _ _ => .rfl) _

/-- The equality of the abstractions for destructors is a partial equivalence relation, at relations
of the recursive destructors that are. -/
theorem DesRel.isPer {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality}
    {rs : Nat → Option TermRel} (hrs : ∀ i x, rs i = some x → IsPer x) {Γ : Scope}
    {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S) : IsPer S where
  symm h' := DesRel.symm_of hd ih h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .none
    | some x => exact .some fun _ _ => (hrs i x hi).symm) _ _ h'
  trans h₁ h₂ := DesRel.trans_of hd ih h _ _ _ h _ _ _ h (fun i => by
    match hi : rs i with
    | none => exact .inl ⟨rfl, rfl, rfl⟩
    | some x => exact .inr ⟨x, x, x, rfl, rfl, rfl, fun _ _ _ => (hrs i x hi).trans⟩) _ _ _ h₁ h₂

/-- Destructors have a unique equality of the abstractions for them, at given relations of their
recursive destructors. -/
theorem DesRel.unique {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S) (s' : Quality) (S' : ObsRel)
    (h' : DesRel sig ι n (fun m _ => levelRel sig ι m) s' rs ds @θ S') :
    ∀ o₁ o₂, S o₁ o₂ ↔ S' o₁ o₂ :=
  DesRel.congr hd ih h _ _ _ h' fun _ => Option.rel_refl (fun _ _ _ => .rfl) _

/-- The equality of the abstractions for destructors relates the abstractions that the equality of
the same destructors relates, at relations of the recursive destructors that relate more terms. -/
theorem DesRel.mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {s₁ : Quality} {rs₁ : Nat → Option TermRel}
    {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns} {θ : Subst 0 [] Γ} {S₁ : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun x y => ∀ t u, x t u → y t u) (rs₁ i) (rs₂ i)) →
        ∀ o₁ o₂, S₁ o₁ o₂ → S₂ o₁ o₂
  | .nil, _, _, _, h', _ => by cases h'; exact fun _ _ _ => trivial
  | .cons (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR => by
    have hSΘp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hEp := AbstractionRel.isPer hSΘp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd ih (hF ts hts _ hv)) hBresp
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' _ _ =>
      have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd ih (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSΘp hSS hFF
      exact fun o₁ o₂ ⟨h₁, h₂⟩ =>
        have hf := hEp.trans h₁ (hEp.symm h₁)
        ⟨(hEE _ _).1 h₁, DesRel.mono hd ih (hG _ hf) _ _ _ (hG' _ ((hEE _ _).1 hf))
          (fun i => hR (i + 1)) _ _ h₂⟩
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs hΘ _ hG, _, _, _, h', hR => by
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.unique hd ih hΘ _ _ hΘ'
        exact fun o₁ o₂ ⟨h₁, h₂⟩ => ⟨fun ts us hts => hr _ _ (h₁ ts us ((hSS _ _).2 hts)),
          DesRel.mono hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩))
            (fun i => hR (i + 1)) _ _ h₂⟩

/-- The equality of the terms of the fields of the constructors of a block, at relations `F X D` of
its recursive fields of the type `D`, grows with `X` when they do: the premise of the properties of
`(eq_μ)` and `(true_μ)`. -/
theorem TelRel.block_mono {sig : Signature} {ι : Interpretation} {n : Nat} (hd : sig.Distinct)
    (ih : ∀ m, m < n → (levelRel sig ι m).IsPer) {j g k : Nat} {Δ : Scope} {α : Type}
    {Ts : List (DataType j g k Δ)} {s : Quality}
    {rec : Constructor j g k Δ → Nat → Option Name}
    {Θ : Constructor j g k Δ → (ps : List Parameter) × Telescope 0 [] ps}
    {F : α → Name → TermRel} {S : α → Constructor j g k Δ → FieldsRel}
    (hS : ∀ X, ∀ T ∈ Ts, ∀ c ∈ T.constructors, TelRel sig ι n (fun m _ => levelRel sig ι m) s
      (fun i => (rec c i).map (F X)) (Θ c).2 (S X c))
    (X Y : α) (hXY : ∀ D t u, F X D t u → F Y D t u) (T : DataType j g k Δ)
    (hT : T ∈ Ts) (c : Constructor j g k Δ) (hc : c ∈ T.constructors) (ts us : Terms 0 []) :
    S X c ts us → S Y c ts us :=
  TelRel.mono hd ih (hS X T hT c hc) _ _ _ (hS Y T hT c hc)
    (fun _ => Option.rel_map (fun D => hXY D) _) ts us

/-- A type of a universe is not a proposition, in a signature whose names are distinct. -/
theorem HasEq.univ_not_prop {sig : Signature} {ι : Interpretation} {v : Term 0 []} {n k : Nat}
    {R : TermRel} {b : Prop} (hd : sig.Distinct) (h : (levelRel sig ι n).univ v R)
    (h' : (levelRel sig ι k).prop v b) : False :=
  UnivRel.not_prop hd (levelRel_univ_iff.1 h) (levelRel_prop_iff.1 h')

/-- The level of a type of a universe is unique, in a signature whose names are distinct. -/
theorem HasEq.univ_level {sig : Signature} {ι : Interpretation} {v : Term 0 []} {n n' : Nat}
    {R R' : TermRel} (hd : sig.Distinct) (h : (levelRel sig ι n).univ v R)
    (h' : (levelRel sig ι n').univ v R') : n = n' :=
  UnivRel.level hd (levelRel_univ_iff.1 h) (levelRel_univ_iff.1 h')


end Sic.Core
