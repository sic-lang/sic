module

public import Sic.Core.Meaning

/-!
# Levels by Their Values

The meaning reads the levels of a closed term by their values, while the reduction copies them as
they are written: an instance `f.{0 ⊔ 0}` of a definition unfolds to its body at `0 ⊔ 0`, which is
not the body at the value `0` that the meaning of the signature makes meaningful, and the rule
`(f_≡)` relates two instances of a constant whose levels are written differently.
Two terms that differ only by levels of the same values compute alike, to canonical terms that differ
in the same way, and the equality `eq(v)` relates the sorts by the values of their levels, so that
no closed judgment tells them apart.

The core reduces by `(δ_⟶)` alone, which copies the levels of the constant into its body, and its
equality `eq(v)` relates sorts only; the kinds of declarations add the cases of their reductions
and of their clauses.

ADE have levels as terms, which their rules of equality and their logical relation compare as terms;
the levels of Sic are not terms, and no counterpart is needed there.
-/

@[expose] public section

namespace Sic.Core

/-! ## Terms Equal up to the Values of Their Levels -/

/-- Two lists of levels whose levels are equal one by one. -/
inductive Level.ListEquiv {k : Nat} : List (Level k) → List (Level k) → Prop where
  /-- No level. -/
  | nil : ListEquiv [] []
  /-- Two equal levels, then equal lists. -/
  | cons {l₁ l₂ : Level k} {ls₁ ls₂ : List (Level k)} (h : l₁ ≈ l₂) (hs : ListEquiv ls₁ ls₂) :
      ListEquiv (l₁ :: ls₁) (l₂ :: ls₂)

mutual

-- ADE: none.
/-- `t` and `t'` are the same term, but for their levels, which are equal one by one. -/
inductive Term.LevelEquiv {k : Nat} : {Γ : Scope} → Term k Γ → Term k Γ → Prop where
  /-- A variable, applied to arguments equal up to their levels. -/
  | var {Γ : Scope} {e : Scope.Entry} (x : Var Γ e) {ts₁ ts₂ : Args k Γ e.params}
      (h : Args.LevelEquiv ts₁ ts₂) : Term.LevelEquiv (.var x ts₁) (.var x ts₂)
  /-- Two sorts of the same quality at equal levels. -/
  | sort {Γ : Scope} (s : Quality) {l₁ l₂ : Level k} (h : l₁ ≈ l₂) :
      Term.LevelEquiv (Γ := Γ) (.sort ⟨s, l₁⟩) (.sort ⟨s, l₂⟩)
  /-- A constant, at equal levels. -/
  | const {Γ : Scope} (f : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
      (h : Level.ListEquiv ls₁ ls₂) : Term.LevelEquiv (Γ := Γ) (.const f qs ls₁ ps) (.const f qs ls₂ ps)
  /-- An instance of a declared type, at equal levels, with arguments equal up to their levels. -/
  | inst {Γ Δ : Scope} (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
      {as₁ as₂ : InstanceArgs k Γ Δ} (h : Level.ListEquiv ls₁ ls₂)
      (has : InstanceArgs.LevelEquiv as₁ as₂) :
      Term.LevelEquiv (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)

/-- The arguments of a telescope, equal up to their levels one by one. -/
inductive Args.LevelEquiv {k : Nat} : {Γ : Scope} → {ps : List Parameter} → Args k Γ ps →
    Args k Γ ps → Prop where
  /-- No argument. -/
  | nil {Γ : Scope} : Args.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two arguments equal up to their levels, then the others. -/
  | cons {Γ : Scope} {p : Parameter} {ps : List Parameter} {t₁ t₂ : Term k Γ} {ts₁ ts₂ : Args k Γ ps}
      (h : Term.LevelEquiv t₁ t₂) (hs : Args.LevelEquiv ts₁ ts₂) :
      Args.LevelEquiv (Args.cons (p := p) t₁ ts₁) (.cons t₂ ts₂)

/-- The arguments of an instance, equal up to their levels one by one. -/
inductive InstanceArgs.LevelEquiv {k : Nat} : {Γ Δ : Scope} → InstanceArgs k Γ Δ →
    InstanceArgs k Γ Δ → Prop where
  /-- No argument. -/
  | nil {Γ : Scope} : InstanceArgs.LevelEquiv (Γ := Γ) .nil .nil
  /-- The arguments before the last one, then two last ones equal up to their levels. -/
  | snoc {Γ Δ : Scope} {e : Scope.Entry} {as₁ as₂ : InstanceArgs k Γ Δ}
      {B₁ B₂ : Term k (Γ.extend e.params.length)} (has : InstanceArgs.LevelEquiv as₁ as₂)
      (h : Term.LevelEquiv B₁ B₂) : InstanceArgs.LevelEquiv (InstanceArgs.snoc (e := e) as₁ B₁) (.snoc as₂ B₂)

end

/-! ## Equivalence -/

theorem Level.ListEquiv.refl {k : Nat} : (ls : List (Level k)) → ListEquiv ls ls
  | [] => .nil
  | l :: ls => .cons (Level.equivalence.refl l) (ListEquiv.refl ls)

theorem Level.ListEquiv.symm {k : Nat} {ls₁ ls₂ : List (Level k)} :
    ListEquiv ls₁ ls₂ → ListEquiv ls₂ ls₁
  | .nil => .nil
  | .cons h hs => .cons (Level.equivalence.symm h) hs.symm

mutual

theorem Term.LevelEquiv.refl {k : Nat} {Γ : Scope} : (t : Term k Γ) → Term.LevelEquiv t t
  | .var x ts => .var x (Args.LevelEquiv.refl ts)
  | .sort ⟨s, l⟩ => .sort s (Level.equivalence.refl l)
  | .const f qs ls ps => .const f qs ps (Level.ListEquiv.refl ls)
  | .inst D qs ls ps as => .inst D qs ps (Level.ListEquiv.refl ls) (InstanceArgs.LevelEquiv.refl as)

theorem Args.LevelEquiv.refl {k : Nat} {Γ : Scope} {ps : List Parameter} :
    (ts : Args k Γ ps) → Args.LevelEquiv ts ts
  | .nil => .nil
  | .cons t ts => .cons (Term.LevelEquiv.refl t) (Args.LevelEquiv.refl ts)

theorem InstanceArgs.LevelEquiv.refl {k : Nat} {Γ Δ : Scope} :
    (as : InstanceArgs k Γ Δ) → InstanceArgs.LevelEquiv as as
  | .nil => .nil
  | .snoc as B => .snoc (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl B)

end

mutual

theorem Term.LevelEquiv.symm {k : Nat} {Γ : Scope} {t₁ t₂ : Term k Γ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv t₂ t₁
  | .var x h => .var x h.symm
  | .sort s h => .sort s (Level.equivalence.symm h)
  | .const f qs ps h => .const f qs ps h.symm
  | .inst D qs ps h has => .inst D qs ps h.symm has.symm

theorem Args.LevelEquiv.symm {k : Nat} {Γ : Scope} {ps : List Parameter} {ts₁ ts₂ : Args k Γ ps} :
    Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv ts₂ ts₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm

theorem InstanceArgs.LevelEquiv.symm {k : Nat} {Γ Δ : Scope} {as₁ as₂ : InstanceArgs k Γ Δ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv as₂ as₁
  | .nil => .nil
  | .snoc has h => .snoc has.symm h.symm

end

/-! ## Renaming and Instantiation of the Level Variables -/

mutual

/-- A renaming keeps two terms equal up to their levels. -/
theorem Term.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (ξ : Ren Γ Δ) {t₁ t₂ : Term k Δ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv (t₁.rename ξ) (t₂.rename ξ)
  | .var x h => .var (ξ x) (h.rename ξ)
  | .sort s h => .sort s h
  | .const f qs ps h => .const f qs ps h
  | .inst D qs ps h has => .inst D qs ps h (has.rename ξ)

theorem Args.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ)
    {ts₁ ts₂ : Args k Δ ps} : Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv (ts₁.rename ξ) (ts₂.rename ξ)
  | .nil => .nil
  | .cons h hs => .cons (h.rename ξ) (hs.rename ξ)

theorem InstanceArgs.LevelEquiv.rename {k : Nat} {Γ Δ Ξ : Scope} (ξ : Ren Γ Δ)
    {as₁ as₂ : InstanceArgs k Δ Ξ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv (as₁.rename ξ) (as₂.rename ξ)
  | .nil => .nil
  | .snoc has h => .snoc (has.rename ξ) (h.rename (Ren.liftN _ ξ))

end

/-- Equal levels replace the level variables by equal levels. -/
theorem Level.subst_equiv {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'} (h : ∀ i, ls₁ i ≈ ls₂ i)
    (l : Level k) : l.subst ls₁ ≈ l.subst ls₂ := fun ρ => by
  rw [Level.value_subst, Level.value_subst]
  exact congrArg (l.value ·) (funext fun i => h i ρ)

theorem Level.ListEquiv.map_subst {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) :
    (ls : List (Level k)) → ListEquiv (ls.map (Level.subst ls₁)) (ls.map (Level.subst ls₂))
  | [] => .nil
  | l :: ls => .cons (Level.subst_equiv h l) (ListEquiv.map_subst h ls)

mutual

/-- Equal levels that replace the level variables give terms equal up to their levels. -/
theorem Term.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (t : Term k Γ) →
    Term.LevelEquiv (t.substLevels ls₁) (t.substLevels ls₂)
  | .var x ts => .var x (Args.substLevels_levelEquiv h ts)
  | .sort ⟨s, l⟩ => .sort s (Level.subst_equiv h l)
  | .const f qs ls ps => .const f qs ps (Level.ListEquiv.map_subst h ls)
  | .inst D qs ls ps as =>
    .inst D qs ps (Level.ListEquiv.map_subst h ls) (InstanceArgs.substLevels_levelEquiv h as)

theorem Args.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ps : List Parameter}
    {ls₁ ls₂ : Fin k → Level k'} (h : ∀ i, ls₁ i ≈ ls₂ i) : (ts : Args k Γ ps) →
    Args.LevelEquiv (ts.substLevels ls₁) (ts.substLevels ls₂)
  | .nil => .nil
  | .cons t ts => .cons (Term.substLevels_levelEquiv h t) (Args.substLevels_levelEquiv h ts)

theorem InstanceArgs.substLevels_levelEquiv {k k' : Nat} {Γ Δ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (as : InstanceArgs k Γ Δ) →
    InstanceArgs.LevelEquiv (as.substLevels ls₁) (as.substLevels ls₂)
  | .nil => .nil
  | .snoc as B =>
    .snoc (InstanceArgs.substLevels_levelEquiv h as) (Term.substLevels_levelEquiv h B)

end

/-- Two lists of equal levels have the same length. -/
theorem Level.ListEquiv.length_eq {k : Nat} {ls₁ ls₂ : List (Level k)} :
    ListEquiv ls₁ ls₂ → ls₁.length = ls₂.length
  | .nil => rfl
  | .cons _ hs => congrArg (· + 1) hs.length_eq

/-- Two lists of equal levels give equal levels to the variables they replace. -/
theorem Level.ListEquiv.getFin {k : Nat} : {ls₁ ls₂ : List (Level k)} → ListEquiv ls₁ ls₂ →
    {n : Nat} → (h₁ : ls₁.length = n) → (h₂ : ls₂.length = n) → (i : Fin n) →
    ls₁.getFin h₁ i ≈ ls₂.getFin h₂ i
  | _, _, .nil, _, h₁, _, i => by subst h₁; exact i.elim0
  | _, _, .cons h hs, _, h₁, h₂, i => by
    subst h₁
    match i with
    | ⟨0, _⟩ => exact h
    | ⟨j + 1, hj⟩ => exact hs.getFin rfl (Nat.succ.inj h₂) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- Two lists of levels equal one by one are equal lists of levels. -/
theorem Level.ListEquiv.of_getFin {k : Nat} : {ls₁ ls₂ : List (Level k)} → {n : Nat} →
    (h₁ : ls₁.length = n) → (h₂ : ls₂.length = n) → (∀ i, ls₁.getFin h₁ i ≈ ls₂.getFin h₂ i) →
    ListEquiv ls₁ ls₂
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, h₁, h₂, _ => by subst h₁; cases h₂
  | _ :: _, [], _, h₁, h₂, _ => by subst h₂; cases h₁
  | _ :: _, _ :: _, _, h₁, h₂, h => by
    subst h₁
    exact .cons (h ⟨0, Nat.zero_lt_succ _⟩)
      (ListEquiv.of_getFin rfl (Nat.succ.inj h₂) fun ⟨j, hj⟩ => h ⟨j + 1, Nat.succ_lt_succ hj⟩)

/-! ## Levels Without Variables -/

/-- Two levels without variables are equal when their values are. -/
theorem Level.equal_closed_iff {l₁ l₂ : Level 0} : l₁ ≈ l₂ ↔ l₁.closedValue = l₂.closedValue :=
  ⟨fun h => h Fin.elim0, fun h ρ => by
    rw [show ρ = Fin.elim0 from funext fun i => i.elim0]
    exact h⟩

/-- The numeral of a level is a level of the same value. -/
theorem Level.value_ofNat {k : Nat} (ρ : Fin k → Nat) : (n : Nat) → (Level.ofNat n).value ρ = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (Level.value_ofNat ρ n)

/-- A level without variables equals the numeral of its value. -/
theorem Level.ofNat_closedValue (l : Level 0) : Level.ofNat l.closedValue ≈ l :=
  Level.equal_closed_iff.2 (Level.value_ofNat _ _)

/-- A term whose level variables are replaced by levels without variables equals it at the values of
these levels, up to its levels: the meaning of the signature gives the entries at these values, and
the reduction unfolds the definitions at the levels of their instances. -/
theorem Term.substLevels_levelEquiv_atLevels {k : Nat} {Γ : Scope} (ls : Fin k → Level 0)
    (t : Term k Γ) : Term.LevelEquiv (t.substLevels ls) (t.atLevels fun i => (ls i).closedValue) :=
  Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (Level.ofNat_closedValue (ls i))) t

/-! ## Reduction -/

/-- A head normal form stays one when its levels change for equal ones. -/
theorem Whnf.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' : Term k Γ}
    (hw : Whnf sig t) (h : Term.LevelEquiv t t') : Whnf sig t' := by
  cases hw with
  | sort => cases h; exact .sort _
  | inst => cases h; exact .inst _ _ _ _ _
  | ne hn =>
    cases hn with
    | var => cases h; exact .ne (.var _ _)
    | const hc => cases h; exact .ne (.const hc)

/-- A term whose levels change for equal ones reduces to the term its reduct becomes so. -/
theorem Red.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' u : Term k Γ}
    (hr : Red sig t u) (h : Term.LevelEquiv t t') :
    ∃ u', Red sig t' u' ∧ Term.LevelEquiv u u' := by
  cases hr with
  | delta hd hq hl hp =>
    cases h with
    | const _ _ _ hls =>
      have hl' := hls.length_eq.symm.trans hl
      exact ⟨_, .delta hd hq hl' hp,
        (Term.substLevels_levelEquiv (hls.getFin hl hl') _).rename _⟩

/-- A term whose levels change for equal ones reduces to the term its reducts become so. -/
theorem RedStar.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' u : Term k Γ}
    (hr : RedStar sig t u) (h : Term.LevelEquiv t t') :
    ∃ u', RedStar sig t' u' ∧ Term.LevelEquiv u u' := by
  induction hr generalizing t' with
  | refl => exact ⟨t', .refl _, h⟩
  | step hr _ ih =>
    obtain ⟨u₁', hr', h₁⟩ := hr.levelEquiv h
    obtain ⟨u', hs', h'⟩ := ih h₁
    exact ⟨u', .step hr' hs', h'⟩

/-- A closed term whose levels change for equal ones computes to the canonical term its canonical
term becomes so. -/
theorem Computes.levelEquiv {sig : Signature} {t t' v : Term 0 []} (hc : Computes sig t v)
    (h : Term.LevelEquiv t t') : ∃ v', Computes sig t' v' ∧ Term.LevelEquiv v v' := by
  obtain ⟨v', hs, hv⟩ := hc.1.levelEquiv h
  exact ⟨v', ⟨hs, hc.2.levelEquiv hv⟩, hv⟩

/-! ## Equality of the Canonical Terms
The relations of the sorts read the levels of the sorts by their values, so that they relate the
terms whose levels change for equal ones, with the same equality of their terms.
This is proved level by level, as the partial equivalence relations are, by cases on the clauses,
so that each kind of declaration adds the cases of its clauses. -/

/-- The relations of the sorts of a level relate the terms whose levels change for equal ones. -/
structure LevelRel.LevelInvariant (L : LevelRel) : Prop where
  /-- `eq(U_n)` relates them, with the same equality of their terms. -/
  univ {A B A' B' : Term 0 []} {R : TermRel} :
    L.univ A B R → Term.LevelEquiv A A' → Term.LevelEquiv B B' → L.univ A' B' R
  /-- The equality of the terms of a type of `U_n` relates them. -/
  univ_rel {A B : Term 0 []} {R : TermRel} {t u t' u' : Term 0 []} :
    L.univ A B R → R t u → Term.LevelEquiv t t' → Term.LevelEquiv u u' → R t' u'
  /-- `eq(Ω_n)` relates them, with the same truth. -/
  prop {P Q P' Q' : Term 0 []} {b : Prop} :
    L.prop P Q b → Term.LevelEquiv P P' → Term.LevelEquiv Q Q' → L.prop P' Q' b

/-- No sort is below the level `0`. -/
theorem LevelRel.empty_levelInvariant : LevelRel.empty.LevelInvariant where
  univ h := h.elim
  univ_rel h := h.elim
  prop h := h.elim

/-- `eq(Ω_n)` relates the propositions whose levels change for equal ones: it has no clause in the
core. -/
theorem PropRel.levelEquiv {P Q P' Q' : Term 0 []} {b : Prop} (h : PropRel P Q b)
    (_hP : Term.LevelEquiv P P') (_hQ : Term.LevelEquiv Q Q') : PropRel P' Q' b := nomatch h

/-- Two sorts at levels of the same value `n` stay so when their levels change for equal ones. -/
theorem Term.LevelEquiv.sort_value {s : Quality} {l : Level 0} {A' : Term 0 []} {n : Nat}
    (h : Term.LevelEquiv (.sort ⟨s, l⟩) A') (hl : l.closedValue + 1 = n) :
    ∃ l', A' = .sort ⟨s, l'⟩ ∧ l'.closedValue + 1 = n := by
  cases h with
  | sort _ h => exact ⟨_, rfl, (Level.equal_closed_iff.1 h) ▸ hl⟩

/-- The relations of the level `n` relate the terms whose levels change for equal ones, if those of
the level below it do. -/
theorem UnivRel.levelInvariant {n : Nat} {below : LevelRel} (hb : below.LevelInvariant) :
    LevelRel.LevelInvariant ⟨UnivRel n below, PropRel⟩ where
  univ
    | .univ h₁ h₂, hA, hB => by
      obtain ⟨_, rfl, h₁'⟩ := hA.sort_value h₁
      obtain ⟨_, rfl, h₂'⟩ := hB.sort_value h₂
      exact .univ h₁' h₂'
    | .prop h₁ h₂, hA, hB => by
      obtain ⟨_, rfl, h₁'⟩ := hA.sort_value h₁
      obtain ⟨_, rfl, h₂'⟩ := hB.sort_value h₂
      exact .prop h₁' h₂'
  univ_rel
    | .univ _ _, ⟨R, h⟩, ht, hu => ⟨R, hb.univ h ht hu⟩
    | .prop _ _, ⟨b, h⟩, ht, hu => ⟨b, hb.prop h ht hu⟩
  prop := PropRel.levelEquiv

/-- The relations of every level relate the terms whose levels change for equal ones. -/
theorem levelRel_levelInvariant : (n : Nat) → (levelRel n).LevelInvariant
  | 0 => UnivRel.levelInvariant LevelRel.empty_levelInvariant
  | n + 1 => UnivRel.levelInvariant (levelRel_levelInvariant n)

/-- A canonical type whose levels change for equal ones has the same equality of its terms. -/
theorem HasEq.levelEquiv {v v' : Term 0 []} {R : TermRel} (hA : HasEq v R)
    (h : Term.LevelEquiv v v') : HasEq v' R :=
  match hA with
  | .univ n hn => .univ n ((levelRel_levelInvariant n).univ hn h h)
  | .prop n b hn hR => .prop n b ((levelRel_levelInvariant n).prop hn h h) hR

/-- The equality of the terms of a canonical type relates the terms whose levels change for equal
ones. -/
theorem HasEq.rel_levelEquiv {v : Term 0 []} {R : TermRel} {t u t' u' : Term 0 []}
    (hA : HasEq v R) (htu : R t u) (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u') :
    R t' u' :=
  match hA with
  | .univ n hn => (levelRel_levelInvariant n).univ_rel hn htu ht hu
  | .prop _ _ _ hR => (hR t' u').2 ((hR t u).1 htu)

/-- A proposition whose levels change for equal ones stays a proposition. -/
theorem IsProp.levelEquiv {v v' : Term 0 []} (hA : IsProp v) (h : Term.LevelEquiv v v') :
    IsProp v' :=
  let ⟨n, b, hn⟩ := hA
  ⟨n, b, (levelRel_levelInvariant n).prop hn h h⟩

/-! ## Closed Judgments
No closed judgment tells apart two terms whose levels change for equal ones. -/

/-- A closed type that computes to a proposition still does when its levels change for equal
ones. -/
theorem ComputesToProp.levelEquiv {sig : Signature} {ι : Interpretation} {A A' : Term 0 []}
    (hA : ComputesToProp sig ι A) (h : Term.LevelEquiv A A') : ComputesToProp sig ι A' :=
  let ⟨_, hc, hp⟩ := hA
  let ⟨_, hc', h₀⟩ := hc.levelEquiv h
  ⟨_, hc', hp.levelEquiv h₀⟩

/-- The clause of `(⊨_type≡)` still holds when the levels of the types change for equal ones. -/
theorem EqTypeClause.levelEquiv {sig : Signature} {ι : Interpretation} {A B A' B' : Term 0 []}
    (hAB : EqTypeClause sig ι A B) (hA : Term.LevelEquiv A A') (hB : Term.LevelEquiv B B') :
    EqTypeClause sig ι A' B' :=
  let ⟨_, _, R, hcA, hcB, hRA, hRB⟩ := hAB
  let ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
  let ⟨_, hcB', hB₀⟩ := hcB.levelEquiv hB
  ⟨_, _, R, hcA', hcB', hRA.levelEquiv hA₀, hRB.levelEquiv hB₀⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` still hold when the levels of the terms and of the type
change for equal ones. -/
theorem EqTermClause.levelEquiv {sig : Signature} {ι : Interpretation} {t u A t' u' A' : Term 0 []}
    (htu : EqTermClause sig ι t u A) (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u')
    (hA : Term.LevelEquiv A A') : EqTermClause sig ι t' u' A' := by
  refine ⟨fun hP' => ?_, fun hP' => ?_⟩
  · obtain ⟨_, _, _, R, hcA, hct, hcu, hR, hvw⟩ :=
      htu.1 fun hP => hP' (hP.levelEquiv hA)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
    obtain ⟨_, hct', hv⟩ := hct.levelEquiv ht
    obtain ⟨_, hcu', hw⟩ := hcu.levelEquiv hu
    exact ⟨_, _, _, R, hcA', hct', hcu', hR.levelEquiv hA₀, hR.rel_levelEquiv hvw hv hw⟩
  · obtain ⟨_, R, hcA, hR, htu'⟩ := htu.2 (hP'.levelEquiv hA.symm)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
    exact ⟨_, R, hcA', hR.levelEquiv hA₀, hR.rel_levelEquiv htu' ht hu⟩

/-- `(⊨_type≡)` still holds when the levels of the types change for equal ones. -/
theorem ValidEqType₀.levelEquiv {sig : Signature} {ι : Interpretation} {A B A' B' : Term 0 []}
    (hAB : ValidEqType₀ sig ι A B) (hA : Term.LevelEquiv A A') (hB : Term.LevelEquiv B B') :
    ValidEqType₀ sig ι A' B' :=
  ⟨hAB.1, hAB.2.levelEquiv hA hB⟩

/-- `(⊨_≡)` and `(⊨_≡Ω)` still hold when the levels of the terms and of the type change for equal
ones. -/
theorem ValidEqTerm₀.levelEquiv {sig : Signature} {ι : Interpretation} {t u A t' u' A' : Term 0 []}
    (htu : ValidEqTerm₀ sig ι t u A) (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u')
    (hA : Term.LevelEquiv A A') : ValidEqTerm₀ sig ι t' u' A' :=
  ⟨htu.1.levelEquiv hA hA, htu.2.levelEquiv ht hu hA⟩

end Sic.Core
