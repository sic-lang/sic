module

public import Sic.Core.Meaning

/-!
# Closed Judgments

The properties of the closed judgments of the meaning that the soundness of the rules uses: they are
partial equivalence relations, as the rules `(sym)` and `(trans)` say, the equality of terms holds
at every type equal to its own, as `(conv_≡)` says, and a step of reduction of a term or of a type
changes no judgment, as `(δ)` needs.

The equality `eq(A₀)` of a closed canonical type that is not a proposition relates canonical terms,
as the meaning of the judgments says, while the equality of the proofs of a proposition relates all
the closed terms when it is true; a type that has the equality of a proposition, and relates some
terms, is then a proposition too, which the conversion needs, since the clauses of the equality of
terms depend on whether the type computes to a proposition.
These proofs hold for every clause of `eq(Ω_n)` that relates canonical terms, and do not use that
the core has no proposition.

ADE prove these properties on their logical relation, at two derivations of the reducibility of the
types, which their relation does not identify; the meaning of Sic gives each type a unique
equality, `HasEq.unique`, from which they follow at once.
-/

@[expose] public section

namespace Sic.Core

/-! ## Canonical Terms -/

/-- `eq(U_n)` relates sorts. -/
theorem UnivRel.sort {n : Nat} {below : LevelRel} {A B : Term 0 []} {R : TermRel} :
    UnivRel n below A B R → (∃ κ, A = .sort κ) ∧ ∃ κ, B = .sort κ
  | .univ _ _ => ⟨⟨_, rfl⟩, _, rfl⟩
  | .prop _ _ => ⟨⟨_, rfl⟩, _, rfl⟩

/-- `eq(Ω_n)` relates canonical terms: it has no clause in the core. -/
theorem PropRel.canonical {P Q : Term 0 []} {b : Prop} (sig : Signature) (h : PropRel P Q b) :
    Whnf sig P ∧ Whnf sig Q :=
  nomatch h

/-- `eq(U_n)` relates canonical terms. -/
theorem LevelRel.univ_canonical {n : Nat} {A B : Term 0 []} {R : TermRel} (sig : Signature)
    (h : (levelRel n).univ A B R) : Whnf sig A ∧ Whnf sig B := by
  have hs : (∃ κ, A = .sort κ) ∧ ∃ κ, B = .sort κ := by cases n <;> exact UnivRel.sort h
  obtain ⟨⟨_, rfl⟩, _, rfl⟩ := hs
  exact ⟨.sort _, .sort _⟩

/-- `eq(A₀)` relates closed canonical terms, when `A₀` is not a proposition. -/
theorem HasEq.canonical {A₀ v w : Term 0 []} {R : TermRel} (sig : Signature) :
    HasEq A₀ R → ¬ IsProp A₀ → R v w → Whnf sig v ∧ Whnf sig w
  | .univ 0 h, _, _ => by
    cases h with
    | univ h₁ => exact absurd h₁ (Nat.succ_ne_zero _)
    | prop h₁ => exact absurd h₁ (Nat.succ_ne_zero _)
  | .univ (m + 1) h, _, hvw => by
    cases h with
    | univ =>
      obtain ⟨_, hR'⟩ := hvw
      exact LevelRel.univ_canonical sig hR'
    | prop =>
      obtain ⟨_, hb⟩ := hvw
      rw [levelRel_prop] at hb
      exact hb.canonical sig
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
    | ne hn =>
      cases hn with
      | var => cases ht
      | const hc => nomatch hc
  exact fun h => this h rfl

/-- The equality of the proofs of a proposition relates all the closed terms, or none. -/
theorem HasEq.prop_any {A₀ t u t' u' : Term 0 []} {R : TermRel} (hA : HasEq A₀ R)
    (hp : IsProp A₀) (htu : R t u) : R t' u' := by
  obtain ⟨k, b, hk⟩ := hp
  have hR : ∀ t u, R t u ↔ b := hA.unique (.prop k b hk fun _ _ => .rfl)
  exact (hR _ _).2 ((hR t u).1 htu)

/-- The canonical form of a type that computes to a proposition is a proposition, in a meaningful
signature. -/
theorem ComputesToProp.isProp {sig : Signature} {ι : Interpretation} {A A₀ : Term 0 []}
    (hp : ComputesToProp sig ι A) (hsig : ValidSig ι sig) (hA : Computesι sig ι A A₀) :
    IsProp A₀ := by
  obtain ⟨A₁, hA₁, hp⟩ := hp
  cases Computesι.det hsig hA hA₁
  exact hp

/-- A type of a sort is a proposition or not, as its equality says. -/
theorem HasEq.isProp_or {A₀ : Term 0 []} {R : TermRel} : HasEq A₀ R → IsProp A₀ ∨ ¬ IsProp A₀
  | .univ _ h => .inr fun ⟨_, _, h'⟩ => HasEq.univ_not_prop h h'
  | .prop k b h _ => .inl ⟨k, b, h⟩

/-- A type whose equality is that of a proposition, and relates two terms, is a proposition. -/
theorem HasEq.isProp_of_prop {A₀ B₀ t u : Term 0 []} {R : TermRel} (hA : HasEq A₀ R)
    (hB : HasEq B₀ R) (hp : IsProp A₀) (htu : R t u) : IsProp B₀ :=
  hB.isProp_or.elim id fun hn =>
    (Term.unknown_not_whnf (hB.canonical [] hn (hA.prop_any hp htu (u' := Term.unknown))).1).elim

/-- Two types with the same equality, which relates two terms, are both propositions or neither. -/
theorem HasEq.isProp_iff {A₀ B₀ t u : Term 0 []} {R : TermRel} (hA : HasEq A₀ R)
    (hB : HasEq B₀ R) (htu : R t u) : IsProp A₀ ↔ IsProp B₀ :=
  ⟨fun hp => hA.isProp_of_prop hB hp htu, fun hp => hB.isProp_of_prop hA hp htu⟩

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

/-- The clause of `(⊨_type≡)` is transitive, in a meaningful signature. -/
theorem EqTypeClause.trans {sig : Signature} {ι : Interpretation} {A B C : Term 0 []}
    (hsig : ValidSig ι sig) :
    EqTypeClause sig ι A B → EqTypeClause sig ι B C → EqTypeClause sig ι A C
  | ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩, ⟨B₁, C₀, R', hB', hC, hB₁, hC₀⟩ => by
    cases Computesι.det hsig hB hB'
    have hRR' : R = R' := funext fun t => funext fun u => propext (hB₀.unique hB₁ t u)
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

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` are symmetric. -/
theorem EqTermClause.symm {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (h : EqTermClause sig ι t u A) : EqTermClause sig ι u t A := by
  refine ⟨fun hn => ?_, fun hp => ?_⟩
  · obtain ⟨A₀, v, w, R, hA, ht, hu, hR, hvw⟩ := h.1 hn
    exact ⟨A₀, w, v, R, hA, hu, ht, hR, hR.isPer.symm hvw⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h.2 hp
    exact ⟨A₀, R, hA, hR, hR.isPer.symm htu⟩

-- ADE: `symEqTerm`, in `Definition/LogicalRelation/Properties/Symmetry.agda`.
/-- `Σ ⊨ t ≡ u : A` is symmetric. -/
theorem ValidEqTerm₀.symm {sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) : ValidEqTerm₀ sig ι u t A :=
  ⟨h.1, h.2.symm⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` are transitive, in a meaningful signature. -/
theorem EqTermClause.trans {sig : Signature} {ι : Interpretation} {t u w A : Term 0 []}
    (hsig : ValidSig ι sig) (h : EqTermClause sig ι t u A) (h' : EqTermClause sig ι u w A) :
    EqTermClause sig ι t w A := by
  refine ⟨fun hn => ?_, fun hp => ?_⟩
  · obtain ⟨A₀, v₁, v₂, R, hA, ht, hu, hR, hv⟩ := h.1 hn
    obtain ⟨A₁, v₃, v₄, R', hA', hu', hw, hR', hv'⟩ := h'.1 hn
    cases Computesι.det hsig hA hA'
    cases Computesι.det hsig hu hu'
    exact ⟨A₀, v₁, v₄, R, hA, ht, hw, hR, hR.isPer.trans hv ((hR'.unique hR _ _).1 hv')⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h.2 hp
    obtain ⟨A₁, R', hA', hR', huw⟩ := h'.2 hp
    cases Computesι.det hsig hA hA'
    exact ⟨A₀, R, hA, hR, hR.isPer.trans htu ((hR'.unique hR _ _).1 huw)⟩

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
    (hsig : ValidSig ι sig) (h : EqTermClause sig ι t u A) (hAB : EqTypeClause sig ι A B) :
    EqTermClause sig ι t u B := by
  obtain ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩ := hAB
  rcases hA₀.isProp_or with hpA₀ | hnA₀
  · have hpA : ComputesToProp sig ι A := ⟨A₀, hA, hpA₀⟩
    obtain ⟨A₁, R', hA', hR', htu⟩ := h.2 hpA
    cases Computesι.det hsig hA hA'
    have htu : R t u := (hR'.unique hA₀ t u).1 htu
    have hpB₀ : IsProp B₀ := (hA₀.isProp_iff hB₀ htu).1 hpA₀
    exact ⟨fun hn => absurd ⟨B₀, hB, hpB₀⟩ hn, fun _ => ⟨B₀, R, hB, hB₀, htu⟩⟩
  · obtain ⟨A₁, v, w, R', hA', ht, hu, hR', hvw⟩ := h.1 fun hpA => hnA₀ (hpA.isProp hsig hA)
    cases Computesι.det hsig hA hA'
    have hvw : R v w := (hR'.unique hA₀ v w).1 hvw
    refine ⟨fun _ => ⟨B₀, v, w, R, hB, ht, hu, hB₀, hvw⟩, fun hpB => ?_⟩
    exact ⟨B₀, R, hB, hB₀, hB₀.prop_any (hpB.isProp hsig hB) hvw⟩

-- ADE: `convEqTerm₁`, in `Definition/LogicalRelation/Properties/Conversion.agda`.
/-- `Σ ⊨ t ≡ u : A` and `Σ ⊨ A ≡ B` give `Σ ⊨ t ≡ u : B`. -/
theorem ValidEqTerm₀.conv {sig : Signature} {ι : Interpretation} {t u A B : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) (hAB : ValidEqType₀ sig ι A B) : ValidEqTerm₀ sig ι t u B :=
  ⟨hAB.right, h.2.conv hAB.1 hAB.2⟩

/-! ## Reduction -/

/-- A step of reduction of `Σ` is a step of reduction once its constants are interpreted. -/
theorem Red.interpret {sig : Signature} {ι : Interpretation} {k : Nat} {Γ : Scope}
    {t u : Term k Γ} : Red sig t u → Red (sig.interpret ι) t u
  | .delta h hq hl hp => .delta (List.mem_map_of_mem (f := Entry.interpret ι) h) hq hl hp

/-- A term computes to the canonical terms of the term it reduces to, in a meaningful signature. -/
theorem Computesι.red_iff {sig : Signature} {ι : Interpretation} {t t' v : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig t t') : Computesι sig ι t v ↔ Computesι sig ι t' v := by
  have hd := hsig.distinct.interpret (ι := ι)
  have h := h.interpret (ι := ι)
  constructor
  · rintro ⟨hs, hw⟩
    cases hs with
    | refl => exact (hw.not_red hd h).elim
    | step h' hs => cases h.det hd h'; exact ⟨hs, hw⟩
  · rintro ⟨hs, hw⟩
    exact ⟨.step h hs, hw⟩

/-- A type computes to a proposition exactly when the type it reduces to does, in a meaningful
signature. -/
theorem ComputesToProp.red_iff {sig : Signature} {ι : Interpretation} {A A' : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig A A') :
    ComputesToProp sig ι A ↔ ComputesToProp sig ι A' := by
  simp only [ComputesToProp, Computesι.red_iff hsig h]

/-- The clause of `(⊨_type≡)` holds of a type exactly when it holds of the type it reduces to, in a
meaningful signature. -/
theorem EqTypeClause.red_iff {sig : Signature} {ι : Interpretation} {A A' B : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig A A') :
    EqTypeClause sig ι A B ↔ EqTypeClause sig ι A' B := by
  simp only [EqTypeClause, Computesι.red_iff hsig h]

-- ADE: `redSubst*`, in `Definition/LogicalRelation/Properties/Reduction.agda`.
/-- `Σ ⊨ A ≡ B` holds exactly when `Σ ⊨ A' ≡ B` does, for `Σ ⊢ A ⟶ A'`. -/
theorem ValidEqType₀.red_iff {sig : Signature} {ι : Interpretation} {A A' B : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig A A') :
    ValidEqType₀ sig ι A B ↔ ValidEqType₀ sig ι A' B := by
  simp only [ValidEqType₀, EqTypeClause.red_iff hsig h]

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` hold of a term exactly when they hold of the term it reduces
to, in a meaningful signature. -/
theorem EqTermClause.red_iff {sig : Signature} {ι : Interpretation} {t t' u A : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig t t') :
    EqTermClause sig ι t u A ↔ EqTermClause sig ι t' u A := by
  refine and_congr (by simp only [Computesι.red_iff hsig h]) ⟨fun h' hp => ?_, fun h' hp => ?_⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h' hp
    exact ⟨A₀, R, hA, hR, hR.prop_any (hp.isProp hsig hA) htu⟩
  · obtain ⟨A₀, R, hA, hR, htu⟩ := h' hp
    exact ⟨A₀, R, hA, hR, hR.prop_any (hp.isProp hsig hA) htu⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` hold at a type exactly when they hold at the type it reduces
to, in a meaningful signature. -/
theorem EqTermClause.red_type_iff {sig : Signature} {ι : Interpretation} {t u A A' : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig A A') :
    EqTermClause sig ι t u A ↔ EqTermClause sig ι t u A' := by
  simp only [EqTermClause, ComputesToProp.red_iff hsig h, Computesι.red_iff hsig h]

-- ADE: `redSubst*Term`, in `Definition/LogicalRelation/Properties/Reduction.agda`.
/-- `Σ ⊨ t ≡ u : A` holds exactly when `Σ ⊨ t' ≡ u : A` does, for `Σ ⊢ t ⟶ t'`. -/
theorem ValidEqTerm₀.red_iff {sig : Signature} {ι : Interpretation} {t t' u A : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig t t') :
    ValidEqTerm₀ sig ι t u A ↔ ValidEqTerm₀ sig ι t' u A := by
  simp only [ValidEqTerm₀, EqTermClause.red_iff hsig h]

/-- `Σ ⊨ t ≡ u : A` holds exactly when `Σ ⊨ t ≡ u : A'` does, for `Σ ⊢ A ⟶ A'`. -/
theorem ValidEqTerm₀.red_type_iff {sig : Signature} {ι : Interpretation} {t u A A' : Term 0 []}
    (hsig : ValidSig ι sig) (h : Red sig A A') :
    ValidEqTerm₀ sig ι t u A ↔ ValidEqTerm₀ sig ι t u A' := by
  simp only [ValidEqTerm₀, ValidType₀, ValidEqType₀.red_iff hsig h, EqTermClause.red_type_iff hsig h]
  constructor
  · rintro ⟨⟨hs, hc⟩, h'⟩
    exact ⟨⟨hs, ((EqTypeClause.red_iff hsig h).1 hc.symm).symm⟩, h'⟩
  · rintro ⟨⟨hs, hc⟩, h'⟩
    exact ⟨⟨hs, ((EqTypeClause.red_iff hsig h).2 hc.symm).symm⟩, h'⟩

end Sic.Core
