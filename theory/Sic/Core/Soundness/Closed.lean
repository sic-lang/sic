module

public import Sic.Core.Meaning

/-!
# Closed Judgments

The properties of the closed judgments of the meaning that the soundness of the rules uses: they are
partial equivalence relations, as the rules `(sym)` and `(trans)` say, the equality of terms holds
at every type equal to its own, as `(conv_≡)` says, and a step of reduction of a term or of a type
changes no judgment, as `(δ)` needs; equal terms of a sort are also equal types, as `(U_type≡)` and
`(Ω_type≡)` say, and two sorts at levels of the same value are equal terms of the universe above
them, as `(U_≡)` and `(Ω_≡)` say.

The equality `eq(v)` of a closed canonical type that is not a proposition relates canonical terms,
as the meaning of the judgments says, while the equality of the proofs of a proposition relates all
the closed terms when it is true; a type that has the equality of a proposition, and relates some
terms, is then a proposition too, which the conversion needs, since the clauses of the equality of
terms depend on whether the type computes to a proposition.
These proofs hold in every signature whose names are distinct, so that a closed term computes to one
canonical term at most, and each type has a unique equality of its terms.

ADE prove these properties on their logical relation, at two derivations of the reducibility of the
types, which their relation does not identify; the meaning of Sic gives each type a unique
equality, `HasEq.unique`, from which they follow at once.
-/

@[expose] public section

namespace Sic.Core

/-! ## Canonical Terms -/

/-- `ty(U_n)` gives canonical types: sorts and instances of declared types. -/
theorem UnivRel.whnf {sig sig' : Signature} {ι : Interpretation} {n : Nat}
    {below : LevelRel.Below n} {v : Term 0 []} {R : TermRel} (h : UnivRel sig ι n below v R) :
    Whnf sig' v := by
  cases h with
  | univ => exact .sort _
  | prop => exact .sort _
  | data _ _ _ _ hv => subst hv; exact .inst _ _ _ _ _
  | codata _ _ _ _ hv => subst hv; exact .inst _ _ _ _ _

/-- `ty(Ω_n)` gives canonical propositions: instances of declared types. -/
theorem PropRel.whnf {sig sig' : Signature} {ι : Interpretation} {n : Nat}
    {below : LevelRel.Below n} {v : Term 0 []} {b : Prop} (h : PropRel sig ι n below v b) :
    Whnf sig' v := by
  cases h with
  | data _ _ _ _ hv => subst hv; exact .inst _ _ _ _ _
  | codata _ _ _ _ hv => subst hv; exact .inst _ _ _ _ _

/-- `(eq_c)` relates canonical terms: constructors. -/
theorem DataType.ctorRel_whnf {sig' : Signature} {j g k : Nat} {Δ : Scope} {D : Name}
    {T : DataType j g k Δ} {S : Constructor j g k Δ → FieldsRel} {v w : Term 0 []}
    (h : T.ctorRel D S v w) : Whnf sig' v ∧ Whnf sig' w := by
  obtain ⟨_, _, _, _, ⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, rfl⟩, _⟩ := h
  exact ⟨.ctor _ _ _ _ _ _ _, .ctor _ _ _ _ _ _ _⟩

/-- `(eq_d)` relates canonical terms: corecursors. -/
theorem corecRel_whnf {sig' : Signature} {D : Name} {S : ObsRel} {v w : Term 0 []}
    (h : corecRel D S v w) : Whnf sig' v ∧ Whnf sig' w := by
  obtain ⟨_, _, ⟨_, _, _, _, _, _, _, _, _, rfl, -⟩, ⟨_, _, _, _, _, _, _, _, _, rfl, -⟩, _⟩ := h
  exact ⟨.corec _ _ _ _ _ _ _ _ _, .corec _ _ _ _ _ _ _ _ _⟩

/-- `eq(v)` relates closed canonical terms, of any signature, when `v` is not a proposition. -/
theorem HasEq.canonical {sig : Signature} {ι : Interpretation} {v w₁ w₂ : Term 0 []} {R : TermRel}
    (sig' : Signature) : HasEq sig ι v R → ¬ IsProp sig ι v → R w₁ w₂ → Whnf sig' w₁ ∧ Whnf sig' w₂
  | .univ _ h, _, hvw => by
    cases levelRel_univ_iff.1 h with
    | univ =>
      obtain ⟨_, h₁, h₂⟩ := hvw
      exact ⟨(levelRel_univ_iff.1 h₁).whnf, (levelRel_univ_iff.1 h₂).whnf⟩
    | prop =>
      obtain ⟨_, _, h₁, h₂, -⟩ := hvw
      exact ⟨(levelRel_prop_iff.1 h₁).whnf, (levelRel_prop_iff.1 h₂).whnf⟩
    | data => exact DataType.ctorRel_whnf hvw
    | codata => exact corecRel_whnf hvw
  | .prop k b h _, hn, _ => absurd ⟨k, b, h⟩ hn

/-- A closed term that is no head normal form of the empty signature: a constant, which it does not
declare. -/
def Term.unknown : Term 0 [] := .const "" [] [] []

/-- `Term.unknown` is no head normal form of the empty signature. -/
theorem Term.unknown_not_whnf : ¬ Whnf [] Term.unknown := by
  have : ∀ {t : Term 0 []}, Whnf [] t → t ≠ Term.unknown := by
    intro t h ht
    cases h with
    | sort => cases ht
    | inst => cases ht
    | ctor => cases ht
    | corec => cases ht
    | ne hn =>
      cases hn with
      | var => cases ht
      | const hc => nomatch hc
      | recursor => cases ht
  exact fun h => this h rfl

/-- The equality of the proofs of a proposition relates all the closed terms, or none, in a signature
whose names are distinct. -/
theorem HasEq.prop_any {sig : Signature} {ι : Interpretation} {v t u t' u' : Term 0 []}
    {R : TermRel} (hd : sig.Distinct) (hA : HasEq sig ι v R) (hp : IsProp sig ι v) (htu : R t u) :
    R t' u' := by
  obtain ⟨k, b, hk⟩ := hp
  have hR : ∀ t u, R t u ↔ b := hA.unique hd (.prop k b hk fun _ _ => .rfl)
  exact (hR _ _).2 ((hR t u).1 htu)

/-- The canonical form of a type that computes to a proposition is a proposition, in a signature
whose names are distinct. -/
theorem ComputesToProp.isProp {sig : Signature} {ι : Interpretation} {A v : Term 0 []}
    (hp : ComputesToProp sig ι A) (hd : sig.Distinct) (hA : Computesι sig ι A v) :
    IsProp sig ι v := by
  obtain ⟨A₁, hA₁, hp⟩ := hp
  cases Computesι.det hd hA hA₁
  exact hp

/-- A type of a sort is a proposition or not, as its equality says, in a signature whose names are
distinct. -/
theorem HasEq.isProp_or {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R : TermRel}
    (hd : sig.Distinct) : HasEq sig ι v R → IsProp sig ι v ∨ ¬ IsProp sig ι v
  | .univ _ h => .inr fun ⟨_, _, h'⟩ => HasEq.univ_not_prop hd h h'
  | .prop k b h _ => .inl ⟨k, b, h⟩

/-- A type whose equality is that of a proposition, and relates two terms, is a proposition, in a
signature whose names are distinct. -/
theorem HasEq.isProp_of_prop {sig : Signature} {ι : Interpretation} {v w t u : Term 0 []}
    {R : TermRel} (hd : sig.Distinct) (hA : HasEq sig ι v R) (hB : HasEq sig ι w R)
    (hp : IsProp sig ι v) (htu : R t u) : IsProp sig ι w :=
  (hB.isProp_or hd).elim id fun hn =>
    (Term.unknown_not_whnf (hB.canonical [] hn (hA.prop_any hd hp htu (u' := Term.unknown))).1).elim

/-- Two types with the same equality, which relates two terms, are both propositions or neither, in
a signature whose names are distinct. -/
theorem HasEq.isProp_iff {sig : Signature} {ι : Interpretation} {v w t u : Term 0 []}
    {R : TermRel} (hd : sig.Distinct) (hA : HasEq sig ι v R) (hB : HasEq sig ι w R) (htu : R t u) :
    IsProp sig ι v ↔ IsProp sig ι w :=
  ⟨fun hp => hA.isProp_of_prop hd hB hp htu, fun hp => hB.isProp_of_prop hd hA hp htu⟩

/-! ## Partial Equivalence Relations -/

/-- The clause of `(⊨_type≡)` is symmetric. -/
theorem EqTypeClause.symm {sig : Signature} {ι : Interpretation} {A B : Term 0 []} :
    EqTypeClause sig ι A B → EqTypeClause sig ι B A
  | ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩ => ⟨B₀, A₀, R, hB, hA, hB₀, hA₀⟩

-- ADE: `symEq`, in `Definition/LogicalRelation/Properties/Symmetry.agda`.
/-- `Σ ⊨ A ≡ B` is symmetric. -/
theorem ValidEqType₀.symm {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    (h : ValidEqType₀ sig ι A B) : ValidEqType₀ sig ι B A :=
  ⟨h.1, h.2.symm⟩

/-- The clause of `(⊨_type≡)` is transitive, in a signature whose names are distinct. -/
theorem EqTypeClause.trans {sig : Signature} {ι : Interpretation} {A B C : Term 0 []}
    (hd : sig.Distinct) :
    EqTypeClause sig ι A B → EqTypeClause sig ι B C → EqTypeClause sig ι A C
  | ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩, ⟨B₁, C₀, R', hB', hC, hB₁, hC₀⟩ => by
    cases Computesι.det hd hB hB'
    have hRR' : R = R' := funext fun t => funext fun u => propext (hB₀.unique hd hB₁ t u)
    subst hRR'
    exact ⟨A₀, C₀, R, hA, hC, hA₀, hC₀⟩

-- ADE: `transEq`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
/-- `Σ ⊨ A ≡ B` is transitive. -/
theorem ValidEqType₀.trans {sig : Signature} {ι : Interpretation} {A B C : Term 0 []}
    (h : ValidEqType₀ sig ι A B) (h' : ValidEqType₀ sig ι B C) : ValidEqType₀ sig ι A C :=
  ⟨h.1, h.2.trans h.1 h'.2⟩

/-- `Σ ⊨ A ≡ B` gives `Σ ⊨ A`. -/
theorem ValidEqType₀.left {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    (h : ValidEqType₀ sig ι A B) : ValidType₀ sig ι A :=
  h.trans h.symm

/-- `Σ ⊨ A ≡ B` gives `Σ ⊨ B`. -/
theorem ValidEqType₀.right {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    (h : ValidEqType₀ sig ι A B) : ValidType₀ sig ι B :=
  h.symm.trans h

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` are symmetric, in a signature whose names are distinct. -/
theorem EqTermClause.symm {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (hd : sig.Distinct) (h : EqTermClause sig ι t u A) : EqTermClause sig ι u t A := by
  refine ⟨fun hn => ?_, fun hp => ?_⟩
  · obtain ⟨A₀, v, w, R, hA, ht, hu, hR, hvw⟩ := h.1 hn
    exact ⟨A₀, w, v, R, hA, hu, ht, hR, (hR.isPer hd).symm hvw⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h.2 hp
    exact ⟨A₀, R, hA, hR, (hR.isPer hd).symm htu⟩

-- ADE: `symEqTerm`, in `Definition/LogicalRelation/Properties/Symmetry.agda`.
/-- `Σ ⊨ t ≡ u : A` is symmetric. -/
theorem ValidEqTerm₀.symm {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) : ValidEqTerm₀ sig ι u t A :=
  ⟨h.1, h.2.symm h.1.1⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` are transitive, in a signature whose names are distinct. -/
theorem EqTermClause.trans {sig : Signature} {ι : Interpretation} {t u w A : Term 0 []}
    (hd : sig.Distinct) (h : EqTermClause sig ι t u A) (h' : EqTermClause sig ι u w A) :
    EqTermClause sig ι t w A := by
  refine ⟨fun hn => ?_, fun hp => ?_⟩
  · obtain ⟨A₀, v₁, v₂, R, hA, ht, hu, hR, hv⟩ := h.1 hn
    obtain ⟨A₁, v₃, v₄, R', hA', hu', hw, hR', hv'⟩ := h'.1 hn
    cases Computesι.det hd hA hA'
    cases Computesι.det hd hu hu'
    exact ⟨A₀, v₁, v₄, R, hA, ht, hw, hR, (hR.isPer hd).trans hv ((hR'.unique hd hR _ _).1 hv')⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h.2 hp
    obtain ⟨A₁, R', hA', hR', huw⟩ := h'.2 hp
    cases Computesι.det hd hA hA'
    exact ⟨A₀, R, hA, hR, (hR.isPer hd).trans htu ((hR'.unique hd hR _ _).1 huw)⟩

-- ADE: `transEqTerm`, in `Definition/LogicalRelation/Properties/Transitivity.agda`.
/-- `Σ ⊨ t ≡ u : A` is transitive. -/
theorem ValidEqTerm₀.trans {sig : Signature} {ι : Interpretation} {t u w A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) (h' : ValidEqTerm₀ sig ι u w A) : ValidEqTerm₀ sig ι t w A :=
  ⟨h.1, h.2.trans h.1.1 h'.2⟩

/-- `Σ ⊨ t ≡ u : A` gives `Σ ⊨ t : A`. -/
theorem ValidEqTerm₀.left {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) : ValidTerm₀ sig ι t A :=
  h.trans h.symm

/-- `Σ ⊨ t ≡ u : A` gives `Σ ⊨ u : A`. -/
theorem ValidEqTerm₀.right {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) : ValidTerm₀ sig ι u A :=
  h.symm.trans h

/-! ## Conversion -/

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` hold at every type equal to `A`. -/
theorem EqTermClause.conv {sig : Signature} {ι : Interpretation} {t u A B : Term 0 []}
    (hd : sig.Distinct) (h : EqTermClause sig ι t u A) (hAB : EqTypeClause sig ι A B) :
    EqTermClause sig ι t u B := by
  obtain ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩ := hAB
  rcases hA₀.isProp_or hd with hpA₀ | hnA₀
  · have hpA : ComputesToProp sig ι A := ⟨A₀, hA, hpA₀⟩
    obtain ⟨A₁, R', hA', hR', htu⟩ := h.2 hpA
    cases Computesι.det hd hA hA'
    have htu : R t u := (hR'.unique hd hA₀ t u).1 htu
    have hpB₀ : IsProp sig ι B₀ := (hA₀.isProp_iff hd hB₀ htu).1 hpA₀
    exact ⟨fun hn => absurd ⟨B₀, hB, hpB₀⟩ hn, fun _ => ⟨B₀, R, hB, hB₀, htu⟩⟩
  · obtain ⟨A₁, v, w, R', hA', ht, hu, hR', hvw⟩ := h.1 fun hpA => hnA₀ (hpA.isProp hd hA)
    cases Computesι.det hd hA hA'
    have hvw : R v w := (hR'.unique hd hA₀ v w).1 hvw
    refine ⟨fun _ => ⟨B₀, v, w, R, hB, ht, hu, hB₀, hvw⟩, fun hpB => ?_⟩
    exact ⟨B₀, R, hB, hB₀, hB₀.prop_any hd (hpB.isProp hd hB) hvw⟩

-- ADE: `convEqTerm₁`, in `Definition/LogicalRelation/Properties/Conversion.agda`.
/-- `Σ ⊨ t ≡ u : A` and `Σ ⊨ A ≡ B` give `Σ ⊨ t ≡ u : B`. -/
theorem ValidEqTerm₀.conv {sig : Signature} {ι : Interpretation} {t u A B : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) (hAB : ValidEqType₀ sig ι A B) : ValidEqTerm₀ sig ι t u B :=
  ⟨hAB.right, h.2.conv hAB.1 hAB.2⟩

/-! ## Reduction

The steps of reduction are those of the signature whose constants are interpreted, where the meaning
computes, so that a declared constant steps to its interpretation; `Red.interpret` gives the steps
of the signature itself.
-/

/-- A step of reduction of `Σ` is a step of reduction once its constants are interpreted. -/
theorem Red.interpret {sig : Signature} {ι : Interpretation} {k : Nat} {Γ : Scope}
    {t u : Term k Γ} : Red sig t u → Red (sig.interpret ι) t u
  | .delta h hq hl hp => .delta (List.mem_map_of_mem (f := Entry.interpret ι) h) hq hl hp
  | .iota h hi hD hc hu hv =>
    .iota (List.mem_map_of_mem (f := Entry.interpret ι) h) hi hD hc hu hv
  | .recursor h => .recursor h.interpret

/-- A term computes to the canonical terms of the term it reduces to, in a signature whose names are
distinct. -/
theorem Computesι.red_iff {sig : Signature} {ι : Interpretation} {t t' v : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) t t') :
    Computesι sig ι t v ↔ Computesι sig ι t' v := by
  have hd := hd.interpret (ι := ι)
  constructor
  · rintro ⟨hs, hw⟩
    cases hs with
    | refl => exact (hw.not_red hd h).elim
    | step h' hs => cases h.det hd h'; exact ⟨hs, hw⟩
  · rintro ⟨hs, hw⟩
    exact ⟨.step h hs, hw⟩

/-- A type computes to a proposition exactly when the type it reduces to does, in a signature whose
names are distinct. -/
theorem ComputesToProp.red_iff {sig : Signature} {ι : Interpretation} {A A' : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) A A') :
    ComputesToProp sig ι A ↔ ComputesToProp sig ι A' := by
  simp only [ComputesToProp, Computesι.red_iff hd h]

/-- The clause of `(⊨_type≡)` holds of a type exactly when it holds of the type it reduces to, in a
signature whose names are distinct. -/
theorem EqTypeClause.red_iff {sig : Signature} {ι : Interpretation} {A A' B : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) A A') :
    EqTypeClause sig ι A B ↔ EqTypeClause sig ι A' B := by
  simp only [EqTypeClause, Computesι.red_iff hd h]

-- ADE: `redSubst*`, in `Definition/LogicalRelation/Properties/Reduction.agda`.
/-- `Σ ⊨ A ≡ B` holds exactly when `Σ ⊨ A' ≡ B` does, for a step `A ⟶ A'`. -/
theorem ValidEqType₀.red_iff {sig : Signature} {ι : Interpretation} {A A' B : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) A A') :
    ValidEqType₀ sig ι A B ↔ ValidEqType₀ sig ι A' B := by
  simp only [ValidEqType₀, EqTypeClause.red_iff hd h]

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` hold of a term exactly when they hold of the term it reduces
to, in a signature whose names are distinct. -/
theorem EqTermClause.red_iff {sig : Signature} {ι : Interpretation} {t t' u A : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) t t') :
    EqTermClause sig ι t u A ↔ EqTermClause sig ι t' u A := by
  refine and_congr (by simp only [Computesι.red_iff hd h]) ⟨fun h' hp => ?_, fun h' hp => ?_⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h' hp
    exact ⟨A₀, R, hA, hR, hR.prop_any hd (hp.isProp hd hA) htu⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h' hp
    exact ⟨A₀, R, hA, hR, hR.prop_any hd (hp.isProp hd hA) htu⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` hold at a type exactly when they hold at the type it reduces
to, in a signature whose names are distinct. -/
theorem EqTermClause.red_type_iff {sig : Signature} {ι : Interpretation} {t u A A' : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) A A') :
    EqTermClause sig ι t u A ↔ EqTermClause sig ι t u A' := by
  simp only [EqTermClause, ComputesToProp.red_iff hd h, Computesι.red_iff hd h]

-- ADE: `redSubst*Term`, in `Definition/LogicalRelation/Properties/Reduction.agda`.
/-- `Σ ⊨ t ≡ u : A` holds exactly when `Σ ⊨ t' ≡ u : A` does, for a step `t ⟶ t'`. -/
theorem ValidEqTerm₀.red_iff {sig : Signature} {ι : Interpretation} {t t' u A : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) t t') :
    ValidEqTerm₀ sig ι t u A ↔ ValidEqTerm₀ sig ι t' u A := by
  simp only [ValidEqTerm₀, EqTermClause.red_iff hd h]

/-- `Σ ⊨ t ≡ u : A` holds exactly when `Σ ⊨ t ≡ u : A'` does, for a step `A ⟶ A'`. -/
theorem ValidEqTerm₀.red_type_iff {sig : Signature} {ι : Interpretation} {t u A A' : Term 0 []}
    (hd : sig.Distinct) (h : Red (sig.interpret ι) A A') :
    ValidEqTerm₀ sig ι t u A ↔ ValidEqTerm₀ sig ι t u A' := by
  simp only [ValidEqTerm₀, ValidType₀, ValidEqType₀.red_iff hd h, EqTermClause.red_type_iff hd h]
  constructor
  · rintro ⟨⟨hs, hc⟩, h'⟩
    exact ⟨⟨hs, ((EqTypeClause.red_iff hd h).1 hc.symm).symm⟩, h'⟩
  · rintro ⟨⟨hs, hc⟩, h'⟩
    exact ⟨⟨hs, ((EqTypeClause.red_iff hd h).2 hc.symm).symm⟩, h'⟩


/-! ## Sorts -/

-- ADE: `⊩≡∷U→⊩≡`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/-- `(U_type≡)`, closed: equal terms of a universe are equal types. -/
theorem ValidEqTerm₀.univType {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    {l : Level 0} (h : ValidEqTerm₀ sig ι A B (.sort ⟨.type, l⟩)) : ValidEqType₀ sig ι A B := by
  obtain ⟨⟨hd, -⟩, hcl, -⟩ := h
  obtain ⟨A₀, v, w, R, hc, hv, hw, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | univ n hn =>
    cases levelRel_univ_iff.1 hn with
    | univ =>
      obtain ⟨R', h₁, h₂⟩ := hvw
      exact ⟨hd, v, w, R', hv, hw, .univ _ h₁, .univ _ h₂⟩
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort

-- ADE: none.
/-- `(Ω_type≡)`, closed: equal propositions are equal types. -/
theorem ValidEqTerm₀.propType {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    {l : Level 0} (h : ValidEqTerm₀ sig ι A B (.sort ⟨.prop, l⟩)) : ValidEqType₀ sig ι A B := by
  obtain ⟨⟨hd, -⟩, hcl, -⟩ := h
  obtain ⟨A₀, v, w, R, hc, hv, hw, hR, hvw⟩ := hcl not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | univ n hn =>
    cases levelRel_univ_iff.1 hn with
    | prop =>
      obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := hvw
      exact ⟨hd, v, w, fun _ _ => b₁, hv, hw, .prop _ b₁ h₁ fun _ _ => .rfl,
        .prop _ b₂ h₂ fun _ _ => hb⟩
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort

-- ADE: `⊩U≡U∷U`, in `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`.
/-- `(U_≡)` and `(Ω_≡)`, closed: two sorts of the same quality at levels of the same value are equal
terms of the universe above the level of the first, in a signature whose names are distinct. -/
theorem ValidEqTerm₀.sort {sig : Signature} {ι : Interpretation} (hd : sig.Distinct)
    {q : Quality} {l₁ l₂ : Level 0} (hl : l₁ ≈ l₂) :
    ValidEqTerm₀ sig ι (.sort ⟨q, l₁⟩) (.sort ⟨q, l₂⟩) (.sort ⟨.type, .succ l₁⟩) := by
  have hU : HasEq sig ι (.sort ⟨.type, .succ l₁⟩)
      (fun A B => ∃ R, (levelRel sig ι (l₁.closedValue + 1)).univ A R ∧
        (levelRel sig ι (l₁.closedValue + 1)).univ B R) :=
    .univ (l₁.closedValue + 2) (levelRel_univ_iff.2 (.univ (k := l₁.closedValue + 1) rfl rfl))
  have h₂ : l₂.closedValue = l₁.closedValue := (hl Fin.elim0).symm
  refine ⟨⟨hd, _, _, _, Computes.sort _ _, Computes.sort _ _, hU, hU⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, Computes.sort _ _, Computes.sort _ _, hU, ?_⟩,
    fun hP => absurd hP not_computesToProp_sort⟩
  cases q
  · exact ⟨_, levelRel_univ_iff.2 (.univ rfl rfl), levelRel_univ_iff.2 (.univ h₂ rfl)⟩
  · exact ⟨_, levelRel_univ_iff.2 (.prop rfl rfl), levelRel_univ_iff.2 (.prop h₂ rfl)⟩

end Sic.Core
