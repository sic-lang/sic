module

public import Sic.Core.Syntax

/-!
# Terms Equal up to the Values of Their Levels

Two levels of annex 06 of RFC 36 are equal when their values are, so that two terms of annex 08 are
the same term when they differ only by levels of the same values; the levels of the Lean are
written, and two terms written with different levels of the same values are two terms, which this
relation relates.
It is an equivalence relation.

ADE have levels as terms, which their rules of equality and their logical relation compare as terms;
the levels of Sic are not terms, and no counterpart is needed there.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Definition -/

/-- Two lists of levels whose levels are equal one by one. -/
inductive Level.ListEquiv {k : Nat} : List (Level k) → List (Level k) → Prop where
  /-- No level. -/
  | nil : ListEquiv [] []
  /-- Two equal levels, then equal lists. -/
  | cons {l₁ l₂ : Level k} {ls₁ ls₂ : List (Level k)} (h : l₁ ≈ l₂) (hs : ListEquiv ls₁ ls₂) :
      ListEquiv (l₁ :: ls₁) (l₂ :: ls₂)

/-- Lists of sorts with the same qualities, at levels equal one by one. -/
inductive Universe.ListEquiv {k : Nat} : List (Universe k) → List (Universe k) → Prop where
  /-- No sort. -/
  | nil : ListEquiv [] []
  /-- Two sorts of the same quality at equal levels, then the others. -/
  | cons (s : Quality) {l₁ l₂ : Level k} {κs₁ κs₂ : List (Universe k)} (h : l₁ ≈ l₂)
      (hs : ListEquiv κs₁ κs₂) : ListEquiv (⟨s, l₁⟩ :: κs₁) (⟨s, l₂⟩ :: κs₂)

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
  /-- A constructor of an instance at equal levels, with arguments and fields equal up to their
  levels. -/
  | ctor {Γ Δ : Scope} (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
      {as₁ as₂ : InstanceArgs k Γ Δ} (c : Name) {ts₁ ts₂ : Terms k Γ} (h : Level.ListEquiv ls₁ ls₂)
      (has : InstanceArgs.LevelEquiv as₁ as₂) (hts : Terms.LevelEquiv ts₁ ts₂) :
      Term.LevelEquiv (.ctor D qs ls₁ ps as₁ c ts₁) (.ctor D qs ls₂ ps as₂ c ts₂)
  /-- A recursor of an instance at equal levels, with arguments, a term, motives and branches
  equal up to their levels, the sorts of their motives having the same quality at equal levels. -/
  | recursor {Γ Δ : Scope} (r ς χ : Grade) (D : Name) (qs : List Quality)
      {ls₁ ls₂ : List (Level k)} (ps : List Grade) {as₁ as₂ : InstanceArgs k Γ Δ}
      {t₁ t₂ : Term k Γ} (s : Quality) {l₁ l₂ : Level k} {Cs₁ Cs₂ : Motives k Γ}
      {us₁ us₂ : Branches k Γ} (hl : Level.ListEquiv ls₁ ls₂)
      (has : InstanceArgs.LevelEquiv as₁ as₂) (h : Term.LevelEquiv t₁ t₂) (hκ : l₁ ≈ l₂)
      (hCs : Motives.LevelEquiv Cs₁ Cs₂) (hus : Branches.LevelEquiv us₁ us₂) :
      Term.LevelEquiv (.recursor r ς χ D qs ls₁ ps as₁ t₁ ⟨s, l₁⟩ Cs₁ us₁)
        (.recursor r ς χ D qs ls₂ ps as₂ t₂ ⟨s, l₂⟩ Cs₂ us₂)
  /-- An observation of a term of an instance at equal levels, with arguments of the instance, a
  term and arguments of the destructor equal up to their levels. -/
  | obs {Γ Δ : Scope} (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
      {as₁ as₂ : InstanceArgs k Γ Δ} {t₁ t₂ : Term k Γ} (d : Name) {bs₁ bs₂ : Terms k Γ}
      (hl : Level.ListEquiv ls₁ ls₂) (has : InstanceArgs.LevelEquiv as₁ as₂)
      (h : Term.LevelEquiv t₁ t₂) (hbs : Terms.LevelEquiv bs₁ bs₂) :
      Term.LevelEquiv (.obs D qs ls₁ ps as₁ t₁ d bs₁) (.obs D qs ls₂ ps as₂ t₂ d bs₂)
  /-- A corecursor of an instance at equal levels, with arguments, a state, states and branches
  equal up to their levels. -/
  | corec {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)}
      (ps : List Grade) {as₁ as₂ : InstanceArgs k Γ Δ} {ss₁ ss₂ : Terms k Γ}
      {Ss₁ Ss₂ : States k Γ} {vs₁ vs₂ : CorecBranches k Γ} (hl : Level.ListEquiv ls₁ ls₂)
      (has : InstanceArgs.LevelEquiv as₁ as₂) (hss : Terms.LevelEquiv ss₁ ss₂)
      (hSs : States.LevelEquiv Ss₁ Ss₂) (hvs : CorecBranches.LevelEquiv vs₁ vs₂) :
      Term.LevelEquiv (.corec r D qs ls₁ ps as₁ ss₁ Ss₁ vs₁) (.corec r D qs ls₂ ps as₂ ss₂ Ss₂ vs₂)
  /-- An equality at the same quality and at equal levels, with a type and terms equal up to their
  levels. -/
  | equality {Γ : Scope} (s : Quality) {l₁ l₂ : Level k} {A₁ A₂ t₁ t₂ u₁ u₂ : Term k Γ}
      (hl : l₁ ≈ l₂) (hA : Term.LevelEquiv A₁ A₂) (ht : Term.LevelEquiv t₁ t₂)
      (hu : Term.LevelEquiv u₁ u₂) :
      Term.LevelEquiv (.equality s l₁ A₁ t₁ u₁) (.equality s l₂ A₂ t₂ u₂)
  /-- A proof by reflexivity at the same quality and at equal levels, with a type and a term equal
  up to their levels; the case is not named `refl`, which names the reflexivity of the relation. -/
  | reflProof {Γ : Scope} (s : Quality) {l₁ l₂ : Level k} {A₁ A₂ t₁ t₂ : Term k Γ}
      (hl : l₁ ≈ l₂) (hA : Term.LevelEquiv A₁ A₂) (ht : Term.LevelEquiv t₁ t₂) :
      Term.LevelEquiv (.refl s l₁ A₁ t₁) (.refl s l₂ A₂ t₂)
  /-- A transport, with a type, terms, a motive, a proof and a transported term equal up to their
  levels. -/
  | transp {Γ : Scope} {A₁ A₂ t₁ t₂ u₁ u₂ : Term k Γ} {C₁ C₂ : Term k (Γ.extend 1)}
      {e₁ e₂ v₁ v₂ : Term k Γ} (hA : Term.LevelEquiv A₁ A₂) (ht : Term.LevelEquiv t₁ t₂)
      (hu : Term.LevelEquiv u₁ u₂) (hC : Term.LevelEquiv C₁ C₂) (he : Term.LevelEquiv e₁ e₂)
      (hv : Term.LevelEquiv v₁ v₂) :
      Term.LevelEquiv (.transp A₁ t₁ u₁ C₁ e₁ v₁) (.transp A₂ t₂ u₂ C₂ e₂ v₂)
  /-- A proof by extensionality at equal levels, with propositions and implications equal up to
  their levels. -/
  | propExt {Γ : Scope} {l₁ l₂ : Level k} {P₁ P₂ Q₁ Q₂ : Term k Γ}
      {f₁ f₂ g₁ g₂ : Term k (Γ.extend 1)} (hl : l₁ ≈ l₂) (hP : Term.LevelEquiv P₁ P₂)
      (hQ : Term.LevelEquiv Q₁ Q₂) (hf : Term.LevelEquiv f₁ f₂) (hg : Term.LevelEquiv g₁ g₂) :
      Term.LevelEquiv (.propExt l₁ P₁ Q₁ f₁ g₁) (.propExt l₂ P₂ Q₂ f₂ g₂)

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

/-- The fields of a constructor, equal up to their levels one by one. -/
inductive Terms.LevelEquiv {k : Nat} : {Γ : Scope} → Terms k Γ → Terms k Γ → Prop where
  /-- No field. -/
  | nil {Γ : Scope} : Terms.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two fields equal up to their levels, then the others. -/
  | cons {Γ : Scope} {t₁ t₂ : Term k Γ} {ts₁ ts₂ : Terms k Γ} (h : Term.LevelEquiv t₁ t₂)
      (hs : Terms.LevelEquiv ts₁ ts₂) : Terms.LevelEquiv (.cons t₁ ts₁) (.cons t₂ ts₂)

/-- The motives of a recursor, equal up to their levels one by one. -/
inductive Motives.LevelEquiv {k : Nat} : {Γ : Scope} → Motives k Γ → Motives k Γ → Prop where
  /-- No motive. -/
  | nil {Γ : Scope} : Motives.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two motives equal up to their levels, then the others. -/
  | cons {Γ : Scope} {n : Nat} {C₁ C₂ : Term k (Γ.extend (n + 1))} {Cs₁ Cs₂ : Motives k Γ}
      (h : Term.LevelEquiv C₁ C₂) (hs : Motives.LevelEquiv Cs₁ Cs₂) :
      Motives.LevelEquiv (.cons n C₁ Cs₁) (.cons n C₂ Cs₂)

/-- The branches of a recursor, equal up to their levels one by one. -/
inductive Branches.LevelEquiv {k : Nat} : {Γ : Scope} → Branches k Γ → Branches k Γ → Prop where
  /-- No branch. -/
  | nil {Γ : Scope} : Branches.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two branches equal up to their levels, then the others. -/
  | cons {Γ : Scope} {n m : Nat} {es : Vector Grade m} {u₁ u₂ : Term k ((Γ.extend n).extend m)} {us₁ us₂ : Branches k Γ}
      (h : Term.LevelEquiv u₁ u₂) (hs : Branches.LevelEquiv us₁ us₂) :
      Branches.LevelEquiv (.cons n m es u₁ us₁) (.cons n m es u₂ us₂)

/-- Two telescopes whose types are equal up to their levels. -/
inductive Telescope.LevelEquiv {k : Nat} :
    {Γ : Scope} → {ps : List Parameter} → Telescope k Γ ps → Telescope k Γ ps → Prop where
  /-- `ε`. -/
  | nil {Γ : Scope} : Telescope.LevelEquiv (Γ := Γ) .nil .nil
  /-- `(x : A ▶ p; q ◀ r, Θ)`. -/
  | cons {Γ : Scope} {ps : List Parameter} (q : Grade) (p : Parameter) {A₁ A₂ : Term k Γ}
      {Θ₁ Θ₂ : Telescope k (.var :: Γ) ps} (h : Term.LevelEquiv A₁ A₂)
      (hΘ : Telescope.LevelEquiv Θ₁ Θ₂) : Telescope.LevelEquiv (.cons q p A₁ Θ₁) (.cons q p A₂ Θ₂)

/-- The states of a corecursor, equal up to their levels one by one. -/
inductive States.LevelEquiv {k : Nat} : {Γ : Scope} → States k Γ → States k Γ → Prop where
  /-- No state. -/
  | nil {Γ : Scope} : States.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two states equal up to their levels, then the others. -/
  | cons {Γ : Scope} {n : Nat} {ps : List Parameter} {S₁ S₂ : Telescope k (Γ.extend n) ps}
      {κs₁ κs₂ : List (Universe k)} {Ss₁ Ss₂ : States k Γ} (h : Telescope.LevelEquiv S₁ S₂)
      (hκ : Universe.ListEquiv κs₁ κs₂) (hs : States.LevelEquiv Ss₁ Ss₂) :
      States.LevelEquiv (.cons n S₁ κs₁ Ss₁) (.cons n S₂ κs₂ Ss₂)

/-- The branches of a corecursor, equal up to their levels one by one. -/
inductive CorecBranches.LevelEquiv {k : Nat} :
    {Γ : Scope} → CorecBranches k Γ → CorecBranches k Γ → Prop where
  /-- No branch. -/
  | nil {Γ : Scope} : CorecBranches.LevelEquiv (Γ := Γ) .nil .nil
  /-- Two branches equal up to their levels, then the others. -/
  | cons {Γ : Scope} {n m a : Nat} {v₁ v₂ : Term k (((Γ.extend n).extend m).extend a)}
      {vs₁ vs₂ : CorecBranches k Γ} (h : Term.LevelEquiv v₁ v₂)
      (hs : CorecBranches.LevelEquiv vs₁ vs₂) :
      CorecBranches.LevelEquiv (.cons n m a v₁ vs₁) (.cons n m a v₂ vs₂)

end

-- ADE: none.
/-- The destructors of a codata type, equal up to their levels one by one. -/
inductive Destructors.LevelEquiv {k : Nat} :
    {Γ : Scope} → {ns : List Name} → Destructors k Γ ns → Destructors k Γ ns → Prop where
  /-- No destructor. -/
  | nil {Γ : Scope} : Destructors.LevelEquiv (Γ := Γ) .nil .nil
  /-- `d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς`, then the destructors after it. -/
  | cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} (p q ς : Grade)
      {Θ₁ Θ₂ : Telescope k Γ ps} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (ψ : ResultOwnership Grade ps.length) {ds₁ ds₂ : Destructors k (.secondOrder ps ψ :: Γ) ns}
      (hΘ : Telescope.LevelEquiv Θ₁ Θ₂) (hB : Term.LevelEquiv B₁ B₂)
      (hds : Destructors.LevelEquiv ds₁ ds₂) :
      Destructors.LevelEquiv (.cons (d := d) p q ς Θ₁ B₁ ψ ds₁) (.cons p q ς Θ₂ B₂ ψ ds₂)

/-! ## Equivalence -/

theorem Level.ListEquiv.refl {k : Nat} : (ls : List (Level k)) → ListEquiv ls ls
  | [] => .nil
  | l :: ls => .cons (Level.equivalence.refl l) (ListEquiv.refl ls)

theorem Level.ListEquiv.symm {k : Nat} {ls₁ ls₂ : List (Level k)} :
    ListEquiv ls₁ ls₂ → ListEquiv ls₂ ls₁
  | .nil => .nil
  | .cons h hs => .cons (Level.equivalence.symm h) hs.symm

theorem Universe.ListEquiv.refl {k : Nat} : (κs : List (Universe k)) → ListEquiv κs κs
  | [] => .nil
  | ⟨s, l⟩ :: κs => .cons s (Level.equivalence.refl l) (ListEquiv.refl κs)

theorem Universe.ListEquiv.symm {k : Nat} {κs₁ κs₂ : List (Universe k)} :
    ListEquiv κs₁ κs₂ → ListEquiv κs₂ κs₁
  | .nil => .nil
  | .cons s h hs => .cons s (Level.equivalence.symm h) hs.symm

mutual

theorem Term.LevelEquiv.refl {k : Nat} {Γ : Scope} : (t : Term k Γ) → Term.LevelEquiv t t
  | .var x ts => .var x (Args.LevelEquiv.refl ts)
  | .sort ⟨s, l⟩ => .sort s (Level.equivalence.refl l)
  | .const f qs ls ps => .const f qs ps (Level.ListEquiv.refl ls)
  | .inst D qs ls ps as => .inst D qs ps (Level.ListEquiv.refl ls) (InstanceArgs.LevelEquiv.refl as)
  | .ctor D qs ls ps as c ts => .ctor D qs ps c (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Terms.LevelEquiv.refl ts)
  | .recursor r ς χ D qs ls ps as t ⟨s, l⟩ Cs us => .recursor r ς χ D qs ps s
      (Level.ListEquiv.refl ls) (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl t)
      (Level.equivalence.refl l) (Motives.LevelEquiv.refl Cs) (Branches.LevelEquiv.refl us)
  | .obs D qs ls ps as t d bs => .obs D qs ps d (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl t) (Terms.LevelEquiv.refl bs)
  | .corec r D qs ls ps as ss Ss vs => .corec r D qs ps (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Terms.LevelEquiv.refl ss) (States.LevelEquiv.refl Ss)
      (CorecBranches.LevelEquiv.refl vs)
  | .equality s l A t u => .equality s (Level.equivalence.refl l) (Term.LevelEquiv.refl A)
      (Term.LevelEquiv.refl t) (Term.LevelEquiv.refl u)
  | .refl s l A t => .reflProof s (Level.equivalence.refl l) (Term.LevelEquiv.refl A)
      (Term.LevelEquiv.refl t)
  | .transp A t₁ t₂ C t u => .transp (Term.LevelEquiv.refl A) (Term.LevelEquiv.refl t₁)
      (Term.LevelEquiv.refl t₂) (Term.LevelEquiv.refl C) (Term.LevelEquiv.refl t)
      (Term.LevelEquiv.refl u)
  | .propExt l A B t u => .propExt (Level.equivalence.refl l) (Term.LevelEquiv.refl A)
      (Term.LevelEquiv.refl B) (Term.LevelEquiv.refl t) (Term.LevelEquiv.refl u)

theorem Args.LevelEquiv.refl {k : Nat} {Γ : Scope} {ps : List Parameter} :
    (ts : Args k Γ ps) → Args.LevelEquiv ts ts
  | .nil => .nil
  | .cons t ts => .cons (Term.LevelEquiv.refl t) (Args.LevelEquiv.refl ts)

theorem InstanceArgs.LevelEquiv.refl {k : Nat} {Γ Δ : Scope} :
    (as : InstanceArgs k Γ Δ) → InstanceArgs.LevelEquiv as as
  | .nil => .nil
  | .snoc as B => .snoc (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl B)

theorem Terms.LevelEquiv.refl {k : Nat} {Γ : Scope} : (ts : Terms k Γ) → Terms.LevelEquiv ts ts
  | .nil => .nil
  | .cons t ts => .cons (Term.LevelEquiv.refl t) (Terms.LevelEquiv.refl ts)

theorem Motives.LevelEquiv.refl {k : Nat} {Γ : Scope} :
    (Cs : Motives k Γ) → Motives.LevelEquiv Cs Cs
  | .nil => .nil
  | .cons _ C Cs => .cons (Term.LevelEquiv.refl C) (Motives.LevelEquiv.refl Cs)

theorem Branches.LevelEquiv.refl {k : Nat} {Γ : Scope} :
    (us : Branches k Γ) → Branches.LevelEquiv us us
  | .nil => .nil
  | .cons _ _ _ u us => .cons (Term.LevelEquiv.refl u) (Branches.LevelEquiv.refl us)


theorem Telescope.LevelEquiv.refl {k : Nat} {Γ : Scope} {ps : List Parameter} :
    (Θ : Telescope k Γ ps) → Telescope.LevelEquiv Θ Θ
  | .nil => .nil
  | .cons q p A Θ => .cons q p (Term.LevelEquiv.refl A) (Telescope.LevelEquiv.refl Θ)

theorem States.LevelEquiv.refl {k : Nat} {Γ : Scope} :
    (Ss : States k Γ) → States.LevelEquiv Ss Ss
  | .nil => .nil
  | .cons _ S κs Ss =>
    .cons (Telescope.LevelEquiv.refl S) (Universe.ListEquiv.refl κs) (States.LevelEquiv.refl Ss)

theorem CorecBranches.LevelEquiv.refl {k : Nat} {Γ : Scope} :
    (vs : CorecBranches k Γ) → CorecBranches.LevelEquiv vs vs
  | .nil => .nil
  | .cons _ _ _ v vs => .cons (Term.LevelEquiv.refl v) (CorecBranches.LevelEquiv.refl vs)

end

theorem Destructors.LevelEquiv.refl {k : Nat} {Γ : Scope} {ns : List Name} :
    (ds : Destructors k Γ ns) → Destructors.LevelEquiv ds ds
  | .nil => .nil
  | .cons p q ς Θ B ψ ds =>
    .cons p q ς ψ (Telescope.LevelEquiv.refl Θ) (Term.LevelEquiv.refl B) (Destructors.LevelEquiv.refl ds)

mutual

theorem Term.LevelEquiv.symm {k : Nat} {Γ : Scope} {t₁ t₂ : Term k Γ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv t₂ t₁
  | .var x h => .var x h.symm
  | .sort s h => .sort s (Level.equivalence.symm h)
  | .const f qs ps h => .const f qs ps h.symm
  | .inst D qs ps h has => .inst D qs ps h.symm has.symm
  | .ctor D qs ps c h has hts => .ctor D qs ps c h.symm has.symm hts.symm
  | .recursor r ς χ D qs ps s hl has h hκ hCs hus =>
    .recursor r ς χ D qs ps s hl.symm has.symm h.symm (Level.equivalence.symm hκ) hCs.symm hus.symm
  | .obs D qs ps d hl has h hbs => .obs D qs ps d hl.symm has.symm h.symm hbs.symm
  | .corec r D qs ps hl has hss hSs hvs =>
    .corec r D qs ps hl.symm has.symm hss.symm hSs.symm hvs.symm
  | .equality s hl hA ht hu => .equality s (Level.equivalence.symm hl) hA.symm ht.symm hu.symm
  | .reflProof s hl hA ht => .reflProof s (Level.equivalence.symm hl) hA.symm ht.symm
  | .transp hA ht hu hC he hv => .transp hA.symm ht.symm hu.symm hC.symm he.symm hv.symm
  | .propExt hl hP hQ hf hg => .propExt (Level.equivalence.symm hl) hP.symm hQ.symm hf.symm hg.symm

theorem Args.LevelEquiv.symm {k : Nat} {Γ : Scope} {ps : List Parameter} {ts₁ ts₂ : Args k Γ ps} :
    Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv ts₂ ts₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm

theorem InstanceArgs.LevelEquiv.symm {k : Nat} {Γ Δ : Scope} {as₁ as₂ : InstanceArgs k Γ Δ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv as₂ as₁
  | .nil => .nil
  | .snoc has h => .snoc has.symm h.symm

theorem Terms.LevelEquiv.symm {k : Nat} {Γ : Scope} {ts₁ ts₂ : Terms k Γ} :
    Terms.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv ts₂ ts₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm

theorem Motives.LevelEquiv.symm {k : Nat} {Γ : Scope} {Cs₁ Cs₂ : Motives k Γ} :
    Motives.LevelEquiv Cs₁ Cs₂ → Motives.LevelEquiv Cs₂ Cs₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm

theorem Branches.LevelEquiv.symm {k : Nat} {Γ : Scope} {us₁ us₂ : Branches k Γ} :
    Branches.LevelEquiv us₁ us₂ → Branches.LevelEquiv us₂ us₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm


/-- Two telescopes equal up to their levels in the other order. -/
theorem Telescope.LevelEquiv.symm {k : Nat} {Γ : Scope} {ps : List Parameter}
    {Θ₁ Θ₂ : Telescope k Γ ps} : Telescope.LevelEquiv Θ₁ Θ₂ → Telescope.LevelEquiv Θ₂ Θ₁
  | .nil => .nil
  | .cons q p h hΘ => .cons q p h.symm hΘ.symm

theorem States.LevelEquiv.symm {k : Nat} {Γ : Scope} {Ss₁ Ss₂ : States k Γ} :
    States.LevelEquiv Ss₁ Ss₂ → States.LevelEquiv Ss₂ Ss₁
  | .nil => .nil
  | .cons h hκ hs => .cons h.symm hκ.symm hs.symm

theorem CorecBranches.LevelEquiv.symm {k : Nat} {Γ : Scope} {vs₁ vs₂ : CorecBranches k Γ} :
    CorecBranches.LevelEquiv vs₁ vs₂ → CorecBranches.LevelEquiv vs₂ vs₁
  | .nil => .nil
  | .cons h hs => .cons h.symm hs.symm

end

theorem Level.ListEquiv.trans {k : Nat} {ls₁ ls₂ ls₃ : List (Level k)} :
    ListEquiv ls₁ ls₂ → ListEquiv ls₂ ls₃ → ListEquiv ls₁ ls₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (Level.equivalence.trans h h') (hs.trans hs')

theorem Universe.ListEquiv.trans {k : Nat} {κs₁ κs₂ κs₃ : List (Universe k)} :
    ListEquiv κs₁ κs₂ → ListEquiv κs₂ κs₃ → ListEquiv κs₁ κs₃
  | .nil, .nil => .nil
  | .cons s h hs, .cons _ h' hs' => .cons s (Level.equivalence.trans h h') (hs.trans hs')

mutual

theorem Term.LevelEquiv.trans {k : Nat} {Γ : Scope} {t₁ t₂ t₃ : Term k Γ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv t₂ t₃ → Term.LevelEquiv t₁ t₃
  | .var x h, .var _ h' => .var x (h.trans h')
  | .sort s h, .sort _ h' => .sort s (Level.equivalence.trans h h')
  | .const f qs ps h, .const _ _ _ h' => .const f qs ps (h.trans h')
  | .inst D qs ps h has, .inst _ _ _ h' has' => .inst D qs ps (h.trans h') (has.trans has')
  | .ctor D qs ps c h has hts, .ctor _ _ _ _ h' has' hts' =>
    .ctor D qs ps c (h.trans h') (has.trans has') (hts.trans hts')
  | .recursor r ς χ D qs ps s hl has h hκ hCs hus,
    .recursor _ _ _ _ _ _ _ hl' has' h' hκ' hCs' hus' =>
    .recursor r ς χ D qs ps s (hl.trans hl') (has.trans has') (h.trans h')
      (Level.equivalence.trans hκ hκ') (hCs.trans hCs') (hus.trans hus')
  | .obs D qs ps d hl has h hbs, .obs _ _ _ _ hl' has' h' hbs' =>
    .obs D qs ps d (hl.trans hl') (has.trans has') (h.trans h') (hbs.trans hbs')
  | .corec r D qs ps hl has hss hSs hvs, .corec _ _ _ _ hl' has' hss' hSs' hvs' =>
    .corec r D qs ps (hl.trans hl') (has.trans has') (hss.trans hss') (hSs.trans hSs')
      (hvs.trans hvs')
  | .equality s hl hA ht hu, .equality _ hl' hA' ht' hu' =>
    .equality s (Level.equivalence.trans hl hl') (hA.trans hA') (ht.trans ht') (hu.trans hu')
  | .reflProof s hl hA ht, .reflProof _ hl' hA' ht' =>
    .reflProof s (Level.equivalence.trans hl hl') (hA.trans hA') (ht.trans ht')
  | .transp hA ht hu hC he hv, .transp hA' ht' hu' hC' he' hv' =>
    .transp (hA.trans hA') (ht.trans ht') (hu.trans hu') (hC.trans hC') (he.trans he')
      (hv.trans hv')
  | .propExt hl hP hQ hf hg, .propExt hl' hP' hQ' hf' hg' =>
    .propExt (Level.equivalence.trans hl hl') (hP.trans hP') (hQ.trans hQ') (hf.trans hf')
      (hg.trans hg')
termination_by structural h _ => h

theorem Args.LevelEquiv.trans {k : Nat} {Γ : Scope} {ps : List Parameter}
    {ts₁ ts₂ ts₃ : Args k Γ ps} :
    Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv ts₂ ts₃ → Args.LevelEquiv ts₁ ts₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')
termination_by structural h _ => h

theorem InstanceArgs.LevelEquiv.trans {k : Nat} {Γ Δ : Scope} {as₁ as₂ as₃ : InstanceArgs k Γ Δ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv as₂ as₃ →
      InstanceArgs.LevelEquiv as₁ as₃
  | .nil, .nil => .nil
  | .snoc has h, .snoc has' h' => .snoc (has.trans has') (h.trans h')
termination_by structural h _ => h

theorem Terms.LevelEquiv.trans {k : Nat} {Γ : Scope} {ts₁ ts₂ ts₃ : Terms k Γ} :
    Terms.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv ts₂ ts₃ → Terms.LevelEquiv ts₁ ts₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')
termination_by structural h _ => h

theorem Motives.LevelEquiv.trans {k : Nat} {Γ : Scope} {Cs₁ Cs₂ Cs₃ : Motives k Γ} :
    Motives.LevelEquiv Cs₁ Cs₂ → Motives.LevelEquiv Cs₂ Cs₃ → Motives.LevelEquiv Cs₁ Cs₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')
termination_by structural h _ => h

theorem Branches.LevelEquiv.trans {k : Nat} {Γ : Scope} {us₁ us₂ us₃ : Branches k Γ} :
    Branches.LevelEquiv us₁ us₂ → Branches.LevelEquiv us₂ us₃ → Branches.LevelEquiv us₁ us₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')
termination_by structural h _ => h

theorem Telescope.LevelEquiv.trans {k : Nat} {Γ : Scope} {ps : List Parameter}
    {Θ₁ Θ₂ Θ₃ : Telescope k Γ ps} :
    Telescope.LevelEquiv Θ₁ Θ₂ → Telescope.LevelEquiv Θ₂ Θ₃ → Telescope.LevelEquiv Θ₁ Θ₃
  | .nil, .nil => .nil
  | .cons q p h hΘ, .cons _ _ h' hΘ' => .cons q p (h.trans h') (hΘ.trans hΘ')
termination_by structural h _ => h

theorem States.LevelEquiv.trans {k : Nat} {Γ : Scope} {Ss₁ Ss₂ Ss₃ : States k Γ} :
    States.LevelEquiv Ss₁ Ss₂ → States.LevelEquiv Ss₂ Ss₃ → States.LevelEquiv Ss₁ Ss₃
  | .nil, .nil => .nil
  | .cons h hκ hs, .cons h' hκ' hs' => .cons (h.trans h') (hκ.trans hκ') (hs.trans hs')
termination_by structural h _ => h

theorem CorecBranches.LevelEquiv.trans {k : Nat} {Γ : Scope} {vs₁ vs₂ vs₃ : CorecBranches k Γ} :
    CorecBranches.LevelEquiv vs₁ vs₂ → CorecBranches.LevelEquiv vs₂ vs₃ →
      CorecBranches.LevelEquiv vs₁ vs₃
  | .nil, .nil => .nil
  | .cons h hs, .cons h' hs' => .cons (h.trans h') (hs.trans hs')
termination_by structural h _ => h

end

end Sic.Core
