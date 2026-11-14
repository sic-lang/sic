module

public import Sic.Core.Meaning
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Substitution

/-!
# Levels by Their Values

The meaning reads the levels of a closed term by their values, while the reduction copies them as
they are written: an instance `f.{0 ⊔ 0}` of a definition unfolds to its body at `0 ⊔ 0`, which is
not the body at the value `0` that the meaning of the signature makes meaningful, and the rule
`(f_≡)` relates two instances of a constant whose levels are written differently.
Two terms that differ only by levels of the same values compute alike, to canonical terms that differ
in the same way, and the graph of the sorts reads the levels of the sorts and of the instances of
the data types by their values, so that no closed judgment tells them apart.
The fields of an instance are the fields of its declaration at its levels and its arguments, so that
a substitution that gives each variable terms equal up to their levels keeps two terms equal up to
their levels.

The core reduces by `(δ_⟶)` alone, which copies the levels of the constant into its body; the kinds
of declarations add the cases of their reductions.

ADE have levels as terms, which their rules of equality and their logical relation compare as terms;
the levels of Sic are not terms, and no counterpart is needed there.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Terms Equal up to the Values of Their Levels -/

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
  equal up to their levels. -/
  | recursor {Γ Δ : Scope} (r : Grade) (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)}
      (ps : List Grade) {as₁ as₂ : InstanceArgs k Γ Δ} {t₁ t₂ : Term k Γ} {Cs₁ Cs₂ : Motives k Γ}
      {us₁ us₂ : Branches k Γ} (hl : Level.ListEquiv ls₁ ls₂)
      (has : InstanceArgs.LevelEquiv as₁ as₂) (h : Term.LevelEquiv t₁ t₂)
      (hCs : Motives.LevelEquiv Cs₁ Cs₂) (hus : Branches.LevelEquiv us₁ us₂) :
      Term.LevelEquiv (.recursor r D qs ls₁ ps as₁ t₁ Cs₁ us₁)
        (.recursor r D qs ls₂ ps as₂ t₂ Cs₂ us₂)
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
  /-- `d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ χ`, then the destructors after it. -/
  | cons {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} (p q χ : Grade)
      {Θ₁ Θ₂ : Telescope k Γ ps} {B₁ B₂ : Term k (Γ.extend ps.length)}
      (ψ : ResultOwnership Grade ps.length) {ds₁ ds₂ : Destructors k (.secondOrder ps ψ :: Γ) ns}
      (hΘ : Telescope.LevelEquiv Θ₁ Θ₂) (hB : Term.LevelEquiv B₁ B₂)
      (hds : Destructors.LevelEquiv ds₁ ds₂) :
      Destructors.LevelEquiv (.cons (d := d) p q χ Θ₁ B₁ ψ ds₁) (.cons p q χ Θ₂ B₂ ψ ds₂)

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
  | .recursor r D qs ls ps as t Cs us => .recursor r D qs ps (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl t) (Motives.LevelEquiv.refl Cs)
      (Branches.LevelEquiv.refl us)
  | .obs D qs ls ps as t d bs => .obs D qs ps d (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Term.LevelEquiv.refl t) (Terms.LevelEquiv.refl bs)
  | .corec r D qs ls ps as ss Ss vs => .corec r D qs ps (Level.ListEquiv.refl ls)
      (InstanceArgs.LevelEquiv.refl as) (Terms.LevelEquiv.refl ss) (States.LevelEquiv.refl Ss)
      (CorecBranches.LevelEquiv.refl vs)

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
  | .cons p q χ Θ B ψ ds =>
    .cons p q χ ψ (Telescope.LevelEquiv.refl Θ) (Term.LevelEquiv.refl B) (Destructors.LevelEquiv.refl ds)

mutual

theorem Term.LevelEquiv.symm {k : Nat} {Γ : Scope} {t₁ t₂ : Term k Γ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv t₂ t₁
  | .var x h => .var x h.symm
  | .sort s h => .sort s (Level.equivalence.symm h)
  | .const f qs ps h => .const f qs ps h.symm
  | .inst D qs ps h has => .inst D qs ps h.symm has.symm
  | .ctor D qs ps c h has hts => .ctor D qs ps c h.symm has.symm hts.symm
  | .recursor r D qs ps hl has h hCs hus =>
    .recursor r D qs ps hl.symm has.symm h.symm hCs.symm hus.symm
  | .obs D qs ps d hl has h hbs => .obs D qs ps d hl.symm has.symm h.symm hbs.symm
  | .corec r D qs ps hl has hss hSs hvs =>
    .corec r D qs ps hl.symm has.symm hss.symm hSs.symm hvs.symm

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

/-! ## Renaming and Instantiation of the Level Variables -/

mutual

/-- A renaming keeps two terms equal up to their levels. -/
theorem Term.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ) {t₁ t₂ : Term k Δ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv (t₁.rename α) (t₂.rename α)
  | .var x h => .var (α x) (h.rename α)
  | .sort s h => .sort s h
  | .const f qs ps h => .const f qs ps h
  | .inst D qs ps h has => .inst D qs ps h (has.rename α)
  | .ctor D qs ps c h has hts => .ctor D qs ps c h (has.rename α) (hts.rename α)
  | .recursor r D qs ps hl has h hCs hus =>
    .recursor r D qs ps hl (has.rename α) (h.rename α) (hCs.rename α) (hus.rename α)
  | .obs D qs ps d hl has h hbs => .obs D qs ps d hl (has.rename α) (h.rename α) (hbs.rename α)
  | .corec r D qs ps hl has hss hSs hvs =>
    .corec r D qs ps hl (has.rename α) (hss.rename α) (hSs.rename α) (hvs.rename α)

theorem Args.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} {ps : List Parameter} (α : Ren Γ Δ)
    {ts₁ ts₂ : Args k Δ ps} : Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv (ts₁.rename α) (ts₂.rename α)
  | .nil => .nil
  | .cons h hs => .cons (h.rename α) (hs.rename α)

theorem InstanceArgs.LevelEquiv.rename {k : Nat} {Γ Δ Ξ : Scope} (α : Ren Γ Δ)
    {as₁ as₂ : InstanceArgs k Δ Ξ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv (as₁.rename α) (as₂.rename α)
  | .nil => .nil
  | .snoc has h => .snoc (has.rename α) (h.rename (Ren.liftN _ α))

theorem Terms.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ) {ts₁ ts₂ : Terms k Δ} :
    Terms.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv (ts₁.rename α) (ts₂.rename α)
  | .nil => .nil
  | .cons h hs => .cons (h.rename α) (hs.rename α)

theorem Motives.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ) {Cs₁ Cs₂ : Motives k Δ} :
    Motives.LevelEquiv Cs₁ Cs₂ → Motives.LevelEquiv (Cs₁.rename α) (Cs₂.rename α)
  | .nil => .nil
  | .cons h hs => .cons (h.rename (Ren.liftN _ α)) (hs.rename α)

theorem Branches.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ) {us₁ us₂ : Branches k Δ} :
    Branches.LevelEquiv us₁ us₂ → Branches.LevelEquiv (us₁.rename α) (us₂.rename α)
  | .nil => .nil
  | .cons (n := n) (m := m) h hs => .cons (h.rename (Ren.liftN m (Ren.liftN n α))) (hs.rename α)


theorem Telescope.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} {ps : List Parameter} (α : Ren Γ Δ)
    {Θ₁ Θ₂ : Telescope k Δ ps} :
    Telescope.LevelEquiv Θ₁ Θ₂ → Telescope.LevelEquiv (Θ₁.rename α) (Θ₂.rename α)
  | .nil => .nil
  | .cons q p h hΘ => .cons q p (h.rename α) (hΘ.rename (Ren.lift α))

theorem States.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ) {Ss₁ Ss₂ : States k Δ} :
    States.LevelEquiv Ss₁ Ss₂ → States.LevelEquiv (Ss₁.rename α) (Ss₂.rename α)
  | .nil => .nil
  | .cons h hκ hs => .cons (h.rename (Ren.liftN _ α)) hκ (hs.rename α)

theorem CorecBranches.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} (α : Ren Γ Δ)
    {vs₁ vs₂ : CorecBranches k Δ} :
    CorecBranches.LevelEquiv vs₁ vs₂ → CorecBranches.LevelEquiv (vs₁.rename α) (vs₂.rename α)
  | .nil => .nil
  | .cons (n := n) (m := m) (a := a) h hs =>
    .cons (h.rename (Ren.liftN a (Ren.liftN m (Ren.liftN n α)))) (hs.rename α)

end

/-- Equal levels replace the level variables by equal levels. -/
theorem Level.subst_equiv {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'} (h : ∀ i, ls₁ i ≈ ls₂ i)
    (l : Level k) : l.subst ls₁ ≈ l.subst ls₂ := fun ρ => by
  rw [Level.value_subst, Level.value_subst]
  exact congrArg (l.value ·) (funext fun i => h i ρ)

theorem Universe.ListEquiv.map_subst {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (κs : List (Universe k)) →
      ListEquiv (κs.map (Universe.substLevels ls₁)) (κs.map (Universe.substLevels ls₂))
  | [] => .nil
  | ⟨s, l⟩ :: κs => .cons s (Level.subst_equiv h l) (ListEquiv.map_subst h κs)

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
  | .ctor D qs ls ps as c ts =>
    .ctor D qs ps c (Level.ListEquiv.map_subst h ls) (InstanceArgs.substLevels_levelEquiv h as)
      (Terms.substLevels_levelEquiv h ts)
  | .recursor r D qs ls ps as t Cs us =>
    .recursor r D qs ps (Level.ListEquiv.map_subst h ls) (InstanceArgs.substLevels_levelEquiv h as)
      (Term.substLevels_levelEquiv h t) (Motives.substLevels_levelEquiv h Cs)
      (Branches.substLevels_levelEquiv h us)
  | .obs D qs ls ps as t d bs =>
    .obs D qs ps d (Level.ListEquiv.map_subst h ls) (InstanceArgs.substLevels_levelEquiv h as)
      (Term.substLevels_levelEquiv h t) (Terms.substLevels_levelEquiv h bs)
  | .corec r D qs ls ps as ss Ss vs =>
    .corec r D qs ps (Level.ListEquiv.map_subst h ls) (InstanceArgs.substLevels_levelEquiv h as)
      (Terms.substLevels_levelEquiv h ss) (States.substLevels_levelEquiv h Ss)
      (CorecBranches.substLevels_levelEquiv h vs)

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

theorem Terms.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (ts : Terms k Γ) →
    Terms.LevelEquiv (ts.substLevels ls₁) (ts.substLevels ls₂)
  | .nil => .nil
  | .cons t ts => .cons (Term.substLevels_levelEquiv h t) (Terms.substLevels_levelEquiv h ts)

theorem Motives.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (Cs : Motives k Γ) →
    Motives.LevelEquiv (Cs.substLevels ls₁) (Cs.substLevels ls₂)
  | .nil => .nil
  | .cons _ C Cs => .cons (Term.substLevels_levelEquiv h C) (Motives.substLevels_levelEquiv h Cs)

theorem Branches.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (us : Branches k Γ) →
    Branches.LevelEquiv (us.substLevels ls₁) (us.substLevels ls₂)
  | .nil => .nil
  | .cons _ _ _ u us => .cons (Term.substLevels_levelEquiv h u) (Branches.substLevels_levelEquiv h us)


/-- Equal levels that replace the level variables give telescopes equal up to their levels. -/
theorem Telescope.substLevels_levelEquiv {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      Telescope.LevelEquiv (Θ.substLevels ls₁) (Θ.substLevels ls₂)
  | _, _, .nil => .nil
  | _, _, .cons q p A Θ =>
    .cons q p (Term.substLevels_levelEquiv h A) (Telescope.substLevels_levelEquiv h Θ)

theorem States.substLevels_levelEquiv {k k' : Nat} {Γ : Scope} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : (Ss : States k Γ) →
    States.LevelEquiv (Ss.substLevels ls₁) (Ss.substLevels ls₂)
  | .nil => .nil
  | .cons _ S κs Ss =>
    .cons (Telescope.substLevels_levelEquiv h S) (Universe.ListEquiv.map_subst h κs)
      (States.substLevels_levelEquiv h Ss)

theorem CorecBranches.substLevels_levelEquiv {k k' : Nat} {Γ : Scope}
    {ls₁ ls₂ : Fin k → Level k'} (h : ∀ i, ls₁ i ≈ ls₂ i) : (vs : CorecBranches k Γ) →
    CorecBranches.LevelEquiv (vs.substLevels ls₁) (vs.substLevels ls₂)
  | .nil => .nil
  | .cons _ _ _ v vs =>
    .cons (Term.substLevels_levelEquiv h v) (CorecBranches.substLevels_levelEquiv h vs)

end

/-- Equal levels that replace the level variables give destructors equal up to their levels. -/
theorem Destructors.substLevels_levelEquiv {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) →
      Destructors.LevelEquiv (ds.substLevels ls₁) (ds.substLevels ls₂)
  | _, _, .nil => .nil
  | _, _, .cons p q χ Θ B ψ ds =>
    .cons p q χ ψ (Telescope.substLevels_levelEquiv h Θ) (Term.substLevels_levelEquiv h B)
      (Destructors.substLevels_levelEquiv h ds)

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

/-! ## Substitution

A substitution that gives each variable terms equal up to their levels keeps two terms equal up to
their levels, as the fields of an instance of a declared type, which its arguments substitute,
need. -/

/-- Two values of a substitution of the first order equal up to their levels. -/
inductive Val.LevelEquiv {k : Nat} {Γ : Scope} : {e : Scope.Entry} → Val k Γ e → Val k Γ e → Prop where
  /-- The same variable. -/
  | var {e : Scope.Entry} (x : Var Γ e) : Val.LevelEquiv (.var x) (.var x)
  /-- Two terms equal up to their levels. -/
  | term {t₁ t₂ : Term k Γ} (h : Term.LevelEquiv t₁ t₂) : Val.LevelEquiv (.term t₁) (.term t₂)

/-- A renaming keeps two values equal up to their levels. -/
theorem Val.LevelEquiv.rename {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} (α : Ren Γ Δ)
    {v₁ v₂ : Val k Δ e} : Val.LevelEquiv v₁ v₂ → Val.LevelEquiv (v₁.rename α) (v₂.rename α)
  | .var x => .var (α x)
  | .term h => .term (h.rename α)

/-- Two values equal up to their levels applied to arguments equal up to their levels give terms
equal up to their levels. -/
theorem Val.LevelEquiv.apply {k : Nat} {Γ : Scope} {e : Scope.Entry} {v₁ v₂ : Val k Γ e}
    {us₁ us₂ : Args k Γ e.params} :
    Val.LevelEquiv v₁ v₂ → Args.LevelEquiv us₁ us₂ → Term.LevelEquiv (v₁.apply us₁) (v₂.apply us₂)
  | .var y, hs => .var y hs
  | .term h, _ => h

/-- Two substitutions of the first order that give each variable values equal up to their
levels. -/
def Subst₀.LevelEquiv {k : Nat} {Γ Δ : Scope} (σ₁ σ₂ : Subst₀ k Γ Δ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Δ e), Val.LevelEquiv (σ₁ x) (σ₂ x)

/-- Two substitutions equal up to their levels stay so under a new entry. -/
theorem Subst₀.LevelEquiv.lift {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (h : Subst₀.LevelEquiv σ₁ σ₂) : Subst₀.LevelEquiv (Subst₀.lift (e := e) σ₁) (Subst₀.lift σ₂) := by
  intro _ x
  cases x with
  | zero => exact .var _
  | succ x => exact (h x).rename _

/-- Two substitutions equal up to their levels stay so under new variables. -/
theorem Subst₀.LevelEquiv.liftN {k : Nat} :
    {Γ Δ : Scope} → (n : Nat) → {σ₁ σ₂ : Subst₀ k Γ Δ} → Subst₀.LevelEquiv σ₁ σ₂ →
      Subst₀.LevelEquiv (Subst₀.liftN n σ₁) (Subst₀.liftN n σ₂)
  | _, _, 0, _, _, h => h
  | _, _, n + 1, _, _, h => Subst₀.LevelEquiv.liftN n (Subst₀.LevelEquiv.lift h)

/-- Two terms equal up to their levels substituted for the last variable. -/
theorem Subst₀.LevelEquiv.single {k : Nat} {Γ : Scope} {t₁ t₂ : Term k Γ}
    (h : Term.LevelEquiv t₁ t₂) : Subst₀.LevelEquiv (Subst₀.single t₁) (Subst₀.single t₂) := by
  intro _ x
  cases x with
  | zero => exact .term h
  | succ x => exact .var _

mutual

/-- A substitution of the first order equal up to the levels keeps two terms equal up to their
levels. -/
theorem Term.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {t₁ t₂ : Term k Δ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv (t₁.subst₀ σ₁) (t₂.subst₀ σ₂)
  | .var x h => by
    rw [Term.subst₀_var, Term.subst₀_var]
    exact (hσ x).apply (h.subst₀ hσ)
  | .sort s h => .sort s h
  | .const f qs ps h => .const f qs ps h
  | .inst D qs ps h has => .inst D qs ps h (has.subst₀ hσ)
  | .ctor D qs ps c h has hts => .ctor D qs ps c h (has.subst₀ hσ) (hts.subst₀ hσ)
  | .recursor r D qs ps hl has h hCs hus =>
    .recursor r D qs ps hl (has.subst₀ hσ) (h.subst₀ hσ) (hCs.subst₀ hσ) (hus.subst₀ hσ)
  | .obs D qs ps d hl has h hbs => .obs D qs ps d hl (has.subst₀ hσ) (h.subst₀ hσ) (hbs.subst₀ hσ)
  | .corec r D qs ps hl has hss hSs hvs =>
    .corec r D qs ps hl (has.subst₀ hσ) (hss.subst₀ hσ) (hSs.subst₀ hσ) (hvs.subst₀ hσ)

theorem Args.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {σ₁ σ₂ : Subst₀ k Γ Δ} (hσ : Subst₀.LevelEquiv σ₁ σ₂) {ts₁ ts₂ : Args k Δ ps} :
    Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv (ts₁.subst₀ σ₁) (ts₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst₀ hσ) (hs.subst₀ hσ)

theorem InstanceArgs.LevelEquiv.subst₀ {k : Nat} {Γ Δ Ξ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {as₁ as₂ : InstanceArgs k Δ Ξ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv (as₁.subst₀ σ₁) (as₂.subst₀ σ₂)
  | .nil => .nil
  | .snoc has h => .snoc (has.subst₀ hσ) (h.subst₀ (Subst₀.LevelEquiv.liftN _ hσ))

theorem Terms.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {ts₁ ts₂ : Terms k Δ} :
    Terms.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv (ts₁.subst₀ σ₁) (ts₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst₀ hσ) (hs.subst₀ hσ)

theorem Motives.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {Cs₁ Cs₂ : Motives k Δ} :
    Motives.LevelEquiv Cs₁ Cs₂ → Motives.LevelEquiv (Cs₁.subst₀ σ₁) (Cs₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst₀ (Subst₀.LevelEquiv.liftN _ hσ)) (hs.subst₀ hσ)

theorem Branches.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {us₁ us₂ : Branches k Δ} :
    Branches.LevelEquiv us₁ us₂ → Branches.LevelEquiv (us₁.subst₀ σ₁) (us₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hs =>
    .cons (h.subst₀ (Subst₀.LevelEquiv.liftN _ (Subst₀.LevelEquiv.liftN _ hσ))) (hs.subst₀ hσ)


/-- A substitution of the first order equal up to the levels keeps two telescopes equal up to their
levels. -/
theorem Telescope.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {σ₁ σ₂ : Subst₀ k Γ Δ} (hσ : Subst₀.LevelEquiv σ₁ σ₂) {Θ₁ Θ₂ : Telescope k Δ ps} :
    Telescope.LevelEquiv Θ₁ Θ₂ → Telescope.LevelEquiv (Θ₁.subst₀ σ₁) (Θ₂.subst₀ σ₂)
  | .nil => .nil
  | .cons q p h hΘ => .cons q p (h.subst₀ hσ) (hΘ.subst₀ (Subst₀.LevelEquiv.lift hσ))

theorem States.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {Ss₁ Ss₂ : States k Δ} :
    States.LevelEquiv Ss₁ Ss₂ → States.LevelEquiv (Ss₁.subst₀ σ₁) (Ss₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hκ hs => .cons (h.subst₀ (Subst₀.LevelEquiv.liftN _ hσ)) hκ (hs.subst₀ hσ)

theorem CorecBranches.LevelEquiv.subst₀ {k : Nat} {Γ Δ : Scope} {σ₁ σ₂ : Subst₀ k Γ Δ}
    (hσ : Subst₀.LevelEquiv σ₁ σ₂) {vs₁ vs₂ : CorecBranches k Δ} :
    CorecBranches.LevelEquiv vs₁ vs₂ → CorecBranches.LevelEquiv (vs₁.subst₀ σ₁) (vs₂.subst₀ σ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst₀ (Subst₀.LevelEquiv.liftN _ (Subst₀.LevelEquiv.liftN _
      (Subst₀.LevelEquiv.liftN _ hσ)))) (hs.subst₀ hσ)

end

/-- Arguments equal up to their levels instantiate terms equal up to their levels to terms equal up
to their levels. -/
theorem Term.LevelEquiv.instantiate {k : Nat} {Γ : Scope} :
    {ps : List Parameter} → {B₁ B₂ : Term k (Γ.extend ps.length)} → {ts₁ ts₂ : Args k Γ ps} →
      Term.LevelEquiv B₁ B₂ → Args.LevelEquiv ts₁ ts₂ →
        Term.LevelEquiv (B₁.instantiate ts₁) (B₂.instantiate ts₂)
  | [], _, _, .nil, .nil, hB, .nil => hB
  | _ :: ps, B₁, B₂, .cons t₁ ts₁, .cons t₂ ts₂, hB, .cons h hs => by
    show Term.LevelEquiv
      (Term.instantiate (B₁.subst₀ (Subst₀.liftN ps.length (Subst₀.single t₁))) ts₁)
      (Term.instantiate (B₂.subst₀ (Subst₀.liftN ps.length (Subst₀.single t₂))) ts₂)
    exact Term.LevelEquiv.instantiate
      (hB.subst₀ (Subst₀.LevelEquiv.liftN ps.length (Subst₀.LevelEquiv.single h))) hs

/-- Two substitutions of the second order that give each variable abstractions equal up to their
levels. -/
def Subst.LevelEquiv {k : Nat} {Γ Δ : Scope} (θ₁ θ₂ : Subst k Γ Δ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Δ e), Term.LevelEquiv (θ₁ x) (θ₂ x)

/-- Two substitutions equal up to their levels stay so under a new entry. -/
theorem Subst.LevelEquiv.lift {k : Nat} {Γ Δ : Scope} {e : Scope.Entry} {θ₁ θ₂ : Subst k Γ Δ}
    (h : Subst.LevelEquiv θ₁ θ₂) : Subst.LevelEquiv (Subst.lift (e := e) θ₁) (Subst.lift θ₂) := by
  intro _ x
  cases x with
  | zero => exact Term.LevelEquiv.refl _
  | succ x => exact (h x).rename _

/-- Two substitutions equal up to their levels stay so under new variables. -/
theorem Subst.LevelEquiv.liftN {k : Nat} :
    {Γ Δ : Scope} → (n : Nat) → {θ₁ θ₂ : Subst k Γ Δ} → Subst.LevelEquiv θ₁ θ₂ →
      Subst.LevelEquiv (Subst.liftN n θ₁) (Subst.liftN n θ₂)
  | _, _, 0, _, _, h => h
  | _, _, n + 1, _, _, h => Subst.LevelEquiv.liftN n (Subst.LevelEquiv.lift h)

/-- Arguments of an instance equal up to their levels are substitutions equal up to their levels. -/
theorem InstanceArgs.LevelEquiv.toSubst {k : Nat} {Γ : Scope} :
    {Δ : Scope} → {as₁ as₂ : InstanceArgs k Γ Δ} → InstanceArgs.LevelEquiv as₁ as₂ →
      Subst.LevelEquiv as₁.toSubst as₂.toSubst
  | _, _, _, .snoc _ h, _, .zero => h
  | _, _, _, .snoc has _, _, .succ x => has.toSubst x

/-- A substitution is equal to itself up to its levels. -/
theorem Subst.LevelEquiv.refl {k : Nat} {Γ Δ : Scope} (θ : Subst k Γ Δ) : Subst.LevelEquiv θ θ :=
  fun x => Term.LevelEquiv.refl (θ x)

/-- Substitutions equal up to their levels stay so when each is followed by an abstraction, the two
equal up to their levels. -/
theorem Subst.LevelEquiv.snoc {k : Nat} {Γ : Scope} {e : Scope.Entry} {θ₁ θ₂ : Subst k [] Γ}
    (h : Subst.LevelEquiv θ₁ θ₂) {f₁ f₂ : Term k (Scope.extend [] e.params.length)}
    (hf : Term.LevelEquiv f₁ f₂) : Subst.LevelEquiv (Subst.snoc (e := e) θ₁ f₁) (Subst.snoc θ₂ f₂)
  | _, .zero => hf
  | _, .succ x => h x

/-- Pairs of closed substitutions equal up to their levels are equal up to their levels. -/
theorem Subst.LevelEquiv.append {k : Nat} {Γ : Scope} {n : Nat} {θ₁ θ₂ : Subst k [] Γ}
    {τ₁ τ₂ : Subst k [] (Scope.extend [] n)} (h : Subst.LevelEquiv θ₁ θ₂)
    (h' : Subst.LevelEquiv τ₁ τ₂) : Subst.LevelEquiv (Subst.append θ₁ τ₁) (Subst.append θ₂ τ₂) := by
  intro _ x
  rcases Var.cases_extend n x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · show Term.LevelEquiv (Subst.append θ₁ τ₁ (y.weakenN n)) (Subst.append θ₂ τ₂ (y.weakenN n))
    rw [Subst.append_weakenN, Subst.append_weakenN]; exact h y
  · show Term.LevelEquiv (Subst.append θ₁ τ₁ (Ren.liftN n Ren.empty z))
      (Subst.append θ₂ τ₂ (Ren.liftN n Ren.empty z))
    rw [Subst.append_liftN_empty, Subst.append_liftN_empty]; exact h' z

/-- Substitutions equal up to their levels, the other way. -/
theorem Subst.LevelEquiv.symm {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (h : Subst.LevelEquiv θ₁ θ₂) : Subst.LevelEquiv θ₂ θ₁ :=
  fun x => (h x).symm

mutual

/-- A substitution of the second order equal up to the levels keeps two terms equal up to their
levels. -/
theorem Term.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {t₁ t₂ : Term k Δ} :
    Term.LevelEquiv t₁ t₂ → Term.LevelEquiv (t₁.subst θ₁) (t₂.subst θ₂)
  | .var x h => (hθ x).instantiate (h.subst hθ)
  | .sort s h => .sort s h
  | .const f qs ps h => .const f qs ps h
  | .inst D qs ps h has => .inst D qs ps h (has.subst hθ)
  | .ctor D qs ps c h has hts => .ctor D qs ps c h (has.subst hθ) (hts.subst hθ)
  | .recursor r D qs ps hl has h hCs hus =>
    .recursor r D qs ps hl (has.subst hθ) (h.subst hθ) (hCs.subst hθ) (hus.subst hθ)
  | .obs D qs ps d hl has h hbs => .obs D qs ps d hl (has.subst hθ) (h.subst hθ) (hbs.subst hθ)
  | .corec r D qs ps hl has hss hSs hvs =>
    .corec r D qs ps hl (has.subst hθ) (hss.subst hθ) (hSs.subst hθ) (hvs.subst hθ)

theorem Args.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {ps : List Parameter} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {ts₁ ts₂ : Args k Δ ps} :
    Args.LevelEquiv ts₁ ts₂ → Args.LevelEquiv (ts₁.subst θ₁) (ts₂.subst θ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst hθ) (hs.subst hθ)

theorem InstanceArgs.LevelEquiv.subst {k : Nat} {Γ Δ Ξ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {as₁ as₂ : InstanceArgs k Δ Ξ} :
    InstanceArgs.LevelEquiv as₁ as₂ → InstanceArgs.LevelEquiv (as₁.subst θ₁) (as₂.subst θ₂)
  | .nil => .nil
  | .snoc has h => .snoc (has.subst hθ) (h.subst (Subst.LevelEquiv.liftN _ hθ))

theorem Terms.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {ts₁ ts₂ : Terms k Δ} :
    Terms.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv (ts₁.subst θ₁) (ts₂.subst θ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst hθ) (hs.subst hθ)

theorem Motives.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {Cs₁ Cs₂ : Motives k Δ} :
    Motives.LevelEquiv Cs₁ Cs₂ → Motives.LevelEquiv (Cs₁.subst θ₁) (Cs₂.subst θ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst (Subst.LevelEquiv.liftN _ hθ)) (hs.subst hθ)

theorem Branches.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {us₁ us₂ : Branches k Δ} :
    Branches.LevelEquiv us₁ us₂ → Branches.LevelEquiv (us₁.subst θ₁) (us₂.subst θ₂)
  | .nil => .nil
  | .cons h hs =>
    .cons (h.subst (Subst.LevelEquiv.liftN _ (Subst.LevelEquiv.liftN _ hθ))) (hs.subst hθ)


/-- A substitution of the second order equal up to the levels keeps two telescopes equal up to their
levels. -/
theorem Telescope.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {θ₁ θ₂ : Subst k Γ Δ} (hθ : Subst.LevelEquiv θ₁ θ₂) {Θ₁ Θ₂ : Telescope k Δ ps} :
    Telescope.LevelEquiv Θ₁ Θ₂ → Telescope.LevelEquiv (Θ₁.subst θ₁) (Θ₂.subst θ₂)
  | .nil => .nil
  | .cons q p h hΘ => .cons q p (h.subst hθ) (hΘ.subst (Subst.LevelEquiv.lift hθ))

theorem States.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {Ss₁ Ss₂ : States k Δ} :
    States.LevelEquiv Ss₁ Ss₂ → States.LevelEquiv (Ss₁.subst θ₁) (Ss₂.subst θ₂)
  | .nil => .nil
  | .cons h hκ hs => .cons (h.subst (Subst.LevelEquiv.liftN _ hθ)) hκ (hs.subst hθ)

theorem CorecBranches.LevelEquiv.subst {k : Nat} {Γ Δ : Scope} {θ₁ θ₂ : Subst k Γ Δ}
    (hθ : Subst.LevelEquiv θ₁ θ₂) {vs₁ vs₂ : CorecBranches k Δ} :
    CorecBranches.LevelEquiv vs₁ vs₂ → CorecBranches.LevelEquiv (vs₁.subst θ₁) (vs₂.subst θ₂)
  | .nil => .nil
  | .cons h hs => .cons (h.subst (Subst.LevelEquiv.liftN _ (Subst.LevelEquiv.liftN _
      (Subst.LevelEquiv.liftN _ hθ)))) (hs.subst hθ)

end

/-- The fields of a constructor at levels of the same values and at arguments equal up to their
levels are equal up to their levels. -/
theorem Constructor.fieldsAt_levelEquiv {j g k : Nat} {Δ : Scope} (c : Constructor j g k Δ)
    (I : Instance j g) {ls₁ ls₂ : Fin k → Level 0} {as₁ as₂ : InstanceArgs 0 [] Δ}
    (hls : ∀ i, ls₁ i ≈ ls₂ i) (has : InstanceArgs.LevelEquiv as₁ as₂) :
    Telescope.LevelEquiv (c.fieldsAt I ls₁ as₁) (c.fieldsAt I ls₂ as₂) :=
  (Telescope.substLevels_levelEquiv hls _).subst has.toSubst

/-! ## Reduction -/

/-- The branches of two branches equal up to their levels are equal up to their levels. -/
theorem Branches.LevelEquiv.get {k : Nat} {Γ : Scope} :
    {us₁ us₂ : Branches k Γ} → Branches.LevelEquiv us₁ us₂ → {i n m : Nat} →
      {u₁ : Term k ((Γ.extend n).extend m)} → us₁.get i = some ⟨n, m, u₁⟩ →
        ∃ u₂, us₂.get i = some ⟨n, m, u₂⟩ ∧ Term.LevelEquiv u₁ u₂
  | _, _, .nil, _, _, _, _, he => nomatch he
  | _, _, .cons h _, 0, _, _, _, he => by
    cases he
    exact ⟨_, rfl, h⟩
  | _, _, .cons _ hs, _ + 1, _, _, _, he => hs.get he

/-- Terms equal up to their levels, instantiated by fields equal up to their levels, are equal up to
their levels. -/
theorem Term.LevelEquiv.instantiateTerms {k : Nat} {Γ : Scope} :
    {n : Nat} → {u₁ u₂ : Term k (Γ.extend n)} → Term.LevelEquiv u₁ u₂ → {ts₁ ts₂ : Terms k Γ} →
      Terms.LevelEquiv ts₁ ts₂ → {v₁ : Term k Γ} → u₁.instantiateTerms ts₁ = some v₁ →
        ∃ v₂, u₂.instantiateTerms ts₂ = some v₂ ∧ Term.LevelEquiv v₁ v₂
  | 0, _, _, h, _, _, .nil, _, hv => by
    cases hv
    exact ⟨_, rfl, h⟩
  | _ + 1, _, _, h, _, _, .cons ht hts, _, hv =>
    Term.LevelEquiv.instantiateTerms
      (h.subst₀ (Subst₀.LevelEquiv.liftN _ (Subst₀.LevelEquiv.single ht))) hts hv
  | 0, _, _, _, _, _, .cons .., _, hv => nomatch hv
  | _ + 1, _, _, _, _, _, .nil, _, hv => nomatch hv

/-- A branch of a corecursor and one equal up to its levels, instantiated by states and arguments
equal up to their levels, are equal up to their levels. -/
theorem Term.LevelEquiv.instantiateTerms₂ {k : Nat} {Γ : Scope} {m a : Nat}
    {g₁ g₂ : Term k ((Γ.extend m).extend a)} (h : Term.LevelEquiv g₁ g₂)
    {ts₁ ts₂ us₁ us₂ : Terms k Γ}
    (hts : Terms.LevelEquiv ts₁ ts₂) (hus : Terms.LevelEquiv us₁ us₂) {v₁ : Term k Γ}
    (hv : g₁.instantiateTerms₂ ts₁ us₁ = some v₁) :
    ∃ v₂, g₂.instantiateTerms₂ ts₂ us₂ = some v₂ ∧ Term.LevelEquiv v₁ v₂ := by
  unfold Term.instantiateTerms₂ at hv ⊢
  cases hg₁ : g₁.instantiateTerms (us₁.rename (Ren.weakenN m)) with
  | none => rw [hg₁] at hv; cases hv
  | some w₁ =>
    rw [hg₁] at hv
    obtain ⟨w₂, hg₂, hw⟩ := h.instantiateTerms (hus.rename _) hg₁
    obtain ⟨v₂, hv₂, hvv⟩ := hw.instantiateTerms hts hv
    exact ⟨v₂, by rw [hg₂]; exact hv₂, hvv⟩

/-- The recursive results of terms equal up to their levels, by functions that give terms equal up to
their levels, are equal up to their levels. -/
theorem Terms.LevelEquiv.results {k : Nat} {Γ : Scope} {f₁ f₂ : Name → Term k Γ → Term k Γ}
    (hf : ∀ D t₁ t₂, Term.LevelEquiv t₁ t₂ → Term.LevelEquiv (f₁ D t₁) (f₂ D t₂)) :
    {ts₁ ts₂ : Terms k Γ} → Terms.LevelEquiv ts₁ ts₂ → (rs : List (Option Name)) →
      Terms.LevelEquiv (ts₁.results f₁ rs) (ts₂.results f₂ rs)
  | _, _, _, [] => .nil
  | _, _, .nil, some _ :: _ | _, _, .nil, none :: _ => .nil
  | _, _, .cons ht hts, some D :: rs => .cons (hf D _ _ ht) (Terms.LevelEquiv.results hf hts rs)
  | _, _, .cons _ hts, none :: rs => Terms.LevelEquiv.results hf hts rs

/-- The branches of corecursors equal up to their levels have, at a position, branches equal up to
their levels. -/
theorem CorecBranches.LevelEquiv.get {k : Nat} {Γ : Scope} :
    {vs₁ vs₂ : CorecBranches k Γ} → CorecBranches.LevelEquiv vs₁ vs₂ → {i n m a : Nat} →
      {v₁ : Term k (((Γ.extend n).extend m).extend a)} → vs₁.get i = some ⟨n, m, a, v₁⟩ →
        ∃ v₂, vs₂.get i = some ⟨n, m, a, v₂⟩ ∧ Term.LevelEquiv v₁ v₂
  | _, _, .nil, _, _, _, _, _, he => nomatch he
  | _, _, .cons h _, 0, _, _, _, _, he => by
    cases he
    exact ⟨_, rfl, h⟩
  | _, _, .cons _ hs, _ + 1, _, _, _, _, he => hs.get he

/-- A neutral term stays one when its levels change for equal ones. -/
theorem Neutral.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' : Term k Γ}
    (hn : Neutral sig t) (h : Term.LevelEquiv t t') : Neutral sig t' := by
  induction hn generalizing t' with
  | var => cases h; exact .var _ _
  | const hc => cases h; exact .const hc
  | recursor _ ih =>
    cases h with
    | recursor _ _ _ _ _ _ ht => exact .recursor (ih ht)
  | obs _ ih =>
    cases h with
    | obs _ _ _ _ _ _ ht => exact .obs (ih ht)

/-- A head normal form stays one when its levels change for equal ones. -/
theorem Whnf.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' : Term k Γ}
    (hw : Whnf sig t) (h : Term.LevelEquiv t t') : Whnf sig t' := by
  cases hw with
  | sort => cases h; exact .sort _
  | inst => cases h; exact .inst _ _ _ _ _
  | ctor => cases h; exact .ctor _ _ _ _ _ _ _
  | corec => cases h; exact .corec _ _ _ _ _ _ _ _ _
  | ne hn => exact .ne (hn.levelEquiv h)

/-! ## Positions -/

theorem Universe.ListEquiv.tail {k : Nat} {κs₁ κs₂ : List (Universe k)} :
    Universe.ListEquiv κs₁ κs₂ → Universe.ListEquiv κs₁.tail κs₂.tail
  | .nil => .nil
  | .cons _ _ hs => hs

/-- The levels of packings of sorts equal one by one, below equal levels, are equal. -/
theorem Telescope.packLevel_equiv {k : Nat} : {κs₁ κs₂ : List (Universe k)} →
    Universe.ListEquiv κs₁ κs₂ → {l₁ l₂ : Level k} → l₁ ≈ l₂ →
      Telescope.packLevel κs₁ l₁ ≈ Telescope.packLevel κs₂ l₂
  | _, _, .nil, _, _, h => h
  | _, _, .cons _ h hs, _, _, hl => fun ρ => by
    show Level.value ρ (.max _ (Telescope.packLevel _ _)) =
      Level.value ρ (.max _ (Telescope.packLevel _ _))
    simp only [Level.value]
    rw [h ρ, Telescope.packLevel_equiv hs hl ρ]

/-- The packings of telescopes equal up to their levels, at sorts equal one by one and at equal
levels, are equal up to their levels. -/
theorem Telescope.LevelEquiv.pack {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    {Θ₁ Θ₂ : Telescope k Γ ps} → Telescope.LevelEquiv Θ₁ Θ₂ →
    {κs₁ κs₂ : List (Universe k)} → Universe.ListEquiv κs₁ κs₂ → {l₁ l₂ : Level k} → l₁ ≈ l₂ →
      Term.LevelEquiv (Θ₁.pack κs₁ l₁) (Θ₂.pack κs₂ l₂)
  | _, [], _, _, .nil, _, _, _, _, _, hl =>
    .inst _ _ _ (.cons hl .nil) .nil
  | _, _ :: _, _, _, .cons _ _ hA hΘ, _, _, .nil, _, _, hl =>
    .inst _ _ _ (.cons hl (.cons (Telescope.packLevel_equiv .nil hl) .nil))
      (.snoc (.snoc .nil hA) (hΘ.pack .nil hl))
  | _, _ :: _, _, _, .cons _ _ hA hΘ, _, _, .cons _ h hs, _, _, hl =>
    .inst _ _ _ (.cons h (.cons (Telescope.packLevel_equiv hs hl) .nil))
      (.snoc (.snoc .nil hA) (hΘ.pack hs hl))

/-- Unpackings of terms, telescopes, motives and terms equal up to their levels, at sorts equal one
by one and at equal levels, are equal up to their levels. -/
theorem Term.LevelEquiv.unpack {k : Nat} (r : Grade) : {Γ : Scope} → {ps : List Parameter} →
    {u₁ u₂ : Term k Γ} → Term.LevelEquiv u₁ u₂ → {Θ₁ Θ₂ : Telescope k Γ ps} →
    Telescope.LevelEquiv Θ₁ Θ₂ → {κs₁ κs₂ : List (Universe k)} → Universe.ListEquiv κs₁ κs₂ →
    {l₁ l₂ : Level k} → l₁ ≈ l₂ → {C₁ C₂ : Term k Γ} → Term.LevelEquiv C₁ C₂ →
    {b₁ b₂ : Term k (Γ.extend ps.length)} → Term.LevelEquiv b₁ b₂ →
      Term.LevelEquiv (Term.unpack r u₁ Θ₁ κs₁ l₁ C₁ b₁) (Term.unpack r u₂ Θ₂ κs₂ l₂ C₂ b₂)
  | _, [], _, _, hu, _, _, .nil, _, _, _, _, _, hl, _, _, hC, _, _, hb =>
    .recursor _ _ _ _ (.cons hl .nil) .nil hu (.cons (hC.rename _) .nil) (.cons hb .nil)
  | _, _ :: _, _, _, hu, _, _, .cons _ _ hA hΘ, _, _, hκ, _, _, hl, _, _, hC, _, _, hb => by
    cases hκ with
    | nil =>
      exact .recursor _ _ _ _ (.cons hl (.cons (Telescope.packLevel_equiv .nil hl) .nil))
        (.snoc (.snoc .nil hA) (hΘ.pack .nil hl)) hu (.cons (hC.rename _) .nil)
        (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hΘ.rename _) .nil hl
          (hC.rename _) (hb.rename _)) .nil)
    | cons _ h hs =>
      exact .recursor _ _ _ _ (.cons h (.cons (Telescope.packLevel_equiv hs hl) .nil))
        (.snoc (.snoc .nil hA) (hΘ.pack hs hl)) hu (.cons (hC.rename _) .nil)
        (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hΘ.rename _) hs hl
          (hC.rename _) (hb.rename _)) .nil)

/-- The states at a position of states equal up to their levels are equal up to their levels, and
so are their sorts. -/
theorem States.LevelEquiv.getAt {k : Nat} {Γ : Scope} : {Ss₁ Ss₂ : States k Γ} →
    States.LevelEquiv Ss₁ Ss₂ → (j : Nat) →
      (Ss₁.get j = none ∧ Ss₂.get j = none) ∨
        ∃ (n : Nat) (ps : List Parameter) (S₁ S₂ : Telescope k (Γ.extend n) ps),
          Ss₁.get j = some ⟨n, ps, S₁⟩ ∧ Ss₂.get j = some ⟨n, ps, S₂⟩ ∧
          Telescope.LevelEquiv S₁ S₂ ∧ Universe.ListEquiv (Ss₁.sorts j) (Ss₂.sorts j)
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hS hκ _, 0 => .inr ⟨_, _, _, _, rfl, rfl, hS, hκ⟩
  | _, _, .cons _ _ hs, j + 1 => hs.getAt j

/-- The states of a type in states equal up to their levels, and their sorts, are equal up to
their levels. -/
theorem States.LevelEquiv.stateOf {k : Nat} {Γ : Scope} (names : List Name) (D : Name)
    {Ss₁ Ss₂ : States k Γ} (h : States.LevelEquiv Ss₁ Ss₂) :
    (Ss₁.stateOf names D = none ∧ Ss₂.stateOf names D = none) ∨
      ∃ (ps : List Parameter) (S₁ S₂ : Telescope k Γ ps) (κs₁ κs₂ : List (Universe k)),
        Ss₁.stateOf names D = some ⟨ps, S₁, κs₁⟩ ∧ Ss₂.stateOf names D = some ⟨ps, S₂, κs₂⟩ ∧
        Telescope.LevelEquiv S₁ S₂ ∧ Universe.ListEquiv κs₁ κs₂ := by
  unfold States.stateOf
  cases names.idxOf? D with
  | none => exact .inl ⟨rfl, rfl⟩
  | some j =>
    simp only
    rcases h.getAt j with ⟨h₁, h₂⟩ | ⟨n, ps, S₁, S₂, h₁, h₂, hS, hκ⟩
    · rw [h₁, h₂]; exact .inl ⟨rfl, rfl⟩
    · rw [h₁, h₂]
      cases n with
      | zero => exact .inr ⟨_, S₁, S₂, _, _, rfl, rfl, hS, hκ⟩
      | succ => exact .inl ⟨rfl, rfl⟩

/-- `resume` of positions equal up to their levels, for corecursors equal up to their levels, of
sorts of the same quality at equal levels, is equal up to its levels. -/
theorem Term.LevelEquiv.resume {k : Nat} {Γ Δ : Scope} {ps' : List Parameter} (r : Grade)
    (D : Name) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
    {as₁ as₂ : InstanceArgs k Γ Δ} {Ss₁ Ss₂ : States k Γ} {gs₁ gs₂ : CorecBranches k Γ}
    (s : Quality) {l₁ l₂ : Level k} (χ : Grade) {S₁ S₂ : Telescope k Γ ps'}
    {κs₁ κs₂ : List (Universe k)} {v₁ v₂ : Term k Γ} (hl : Level.ListEquiv ls₁ ls₂)
    (has : InstanceArgs.LevelEquiv as₁ as₂) (hSs : States.LevelEquiv Ss₁ Ss₂)
    (hgs : CorecBranches.LevelEquiv gs₁ gs₂) (hκ : l₁ ≈ l₂) (hS : Telescope.LevelEquiv S₁ S₂)
    (hκs : Universe.ListEquiv κs₁ κs₂) (hv : Term.LevelEquiv v₁ v₂) :
    Term.LevelEquiv (Term.resume r D qs ls₁ ps as₁ Ss₁ gs₁ ⟨s, l₁⟩ χ S₁ κs₁ v₁)
      (Term.resume r D qs ls₂ ps as₂ Ss₂ gs₂ ⟨s, l₂⟩ χ S₂ κs₂ v₂) := by
  have h0 := Telescope.packLevel_equiv hκs (Level.equivalence.refl .zero)
  have hT : Term.LevelEquiv (Term.inst D qs ls₁ ps as₁) (Term.inst D qs ls₂ ps as₂) :=
    .inst _ _ _ hl has
  exact .recursor _ _ _ _ (.cons (Telescope.packLevel_equiv hκs h0) (.cons hκ .nil))
    (.snoc (.snoc .nil (hS.pack hκs h0)) hT) hv (.cons (hT.rename _) .nil)
    (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hS.rename _) hκs h0 (hT.rename _)
        (.corec _ _ _ _ hl ((has.rename _).rename _) (Terms.LevelEquiv.refl _)
          ((hSs.rename _).rename _) ((hgs.rename _).rename _)))
      (.cons (Term.LevelEquiv.refl _) .nil))

/-- The observed terms of corecursors equal up to their levels, of sorts of the same quality at
equal levels, at branches equal up to their levels, are equal up to their levels. -/
theorem Term.LevelEquiv.observed {k : Nat} {Γ Δ : Scope} (names : List Name) (rec : Option Name)
    (r : Grade) (qs : List Quality) {ls₁ ls₂ : List (Level k)} (ps : List Grade)
    {as₁ as₂ : InstanceArgs k Γ Δ} {Ss₁ Ss₂ : States k Γ} {gs₁ gs₂ : CorecBranches k Γ}
    (s : Quality) {l₁ l₂ : Level k} (χ : Grade) {v₁ v₂ : Term k Γ} (hl : Level.ListEquiv ls₁ ls₂)
    (has : InstanceArgs.LevelEquiv as₁ as₂) (hSs : States.LevelEquiv Ss₁ Ss₂)
    (hgs : CorecBranches.LevelEquiv gs₁ gs₂) (hκ : l₁ ≈ l₂) (hv : Term.LevelEquiv v₁ v₂) :
    Term.LevelEquiv (Term.observed names rec r qs ls₁ ps as₁ Ss₁ gs₁ ⟨s, l₁⟩ χ v₁)
      (Term.observed names rec r qs ls₂ ps as₂ Ss₂ gs₂ ⟨s, l₂⟩ χ v₂) := by
  unfold Term.observed
  cases rec with
  | none => exact hv
  | some D =>
    simp only
    rcases hSs.stateOf names D with ⟨h₁, h₂⟩ | ⟨ps', S₁, S₂, κs₁, κs₂, h₁, h₂, hS, hκs⟩
    · rw [h₁, h₂]; exact hv
    · rw [h₁, h₂]
      exact Term.LevelEquiv.resume r D qs ps s χ hl has hSs hgs hκ hS hκs hv

/-- A term whose levels change for equal ones reduces to the term its reduct becomes so. -/
theorem Red.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' u : Term k Γ}
    (hr : Red sig t u) (h : Term.LevelEquiv t t') :
    ∃ u', Red sig t' u' ∧ Term.LevelEquiv u u' := by
  induction hr generalizing t' with
  | delta hd hq hl hp =>
    cases h with
    | const _ _ _ hls =>
      have hl' := hls.length_eq.symm.trans hl
      exact ⟨_, .delta hd hq hl' hp,
        (Term.substLevels_levelEquiv (hls.getFin hl hl') _).rename _⟩
  | iota hdecl hi hD hc hq hp hu hv =>
    cases h with
    | recursor _ _ _ _ hl has ht hCs hus =>
      cases ht with
      | ctor _ _ _ _ _ _ hts =>
        obtain ⟨u', hu', huu⟩ := hus.get hu
        obtain ⟨v', hv', hvv⟩ := huu.instantiateTerms₂ hts
          (Terms.LevelEquiv.results (fun D _ _ h => .recursor _ D _ _ hl has h hCs hus) hts _) hv
        exact ⟨v', .iota hdecl hi hD hc hq hp hu' hv', hvv⟩
  | recursor _ ih =>
    cases h with
    | recursor _ _ _ _ hl has ht hCs hus =>
      obtain ⟨u', hr', hu⟩ := ih ht
      exact ⟨_, .recursor hr', .recursor _ _ _ _ hl has hu hCs hus⟩
  | beta hdecl hi hD hq hl hp hg hv =>
    cases h with
    | obs _ _ _ _ _ _ ht hbs =>
      cases ht with
      | corec _ _ _ _ hls has hss hSs hgs =>
        obtain ⟨g', hg', hgg⟩ := hgs.get hg
        obtain ⟨v', hv', hvv⟩ := hgg.instantiateTerms₂ hss hbs hv
        have hl' := hls.length_eq.symm.trans hl
        exact ⟨_, .beta hdecl hi hD hq hl' hp hg' hv',
          Term.LevelEquiv.observed _ _ _ _ _ _ _ hls has hSs hgs
            (Level.subst_equiv (hls.getFin hl hl') _) hvv⟩
  | obs _ ih =>
    cases h with
    | obs _ _ _ _ hl has ht hbs =>
      obtain ⟨u', hr', hu⟩ := ih ht
      exact ⟨_, .obs hr', .obs _ _ _ _ hl has hu hbs⟩

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
The relations of the sorts read the levels of the sorts and of the instances by their values, so
that they give the types whose levels change for equal ones, with the same equality of their terms,
which relates the terms whose levels change for equal ones, and with the same relation of run time.
This is proved level by level, as the partial equivalence relations are, by induction on the clauses
that give a type of the level, together with the telescopes of the fields of its constructors, so
that each kind of declaration adds the cases of its clauses. -/

/-- The relations of the sorts of a level give the types whose levels change for equal ones, with the
same equality of their terms or the same truth, and the same relation of run time. -/
structure LevelRel.LevelInvariant (L : LevelRel) : Prop where
  /-- `ty(U_n)` gives them, with the same equality of their terms. -/
  univ {A A' : Term 0 []} {R : TermRel} : L.univ A R → Term.LevelEquiv A A' → L.univ A' R
  /-- `ty(Ω_n)` gives them, with the same truth. -/
  prop {P P' : Term 0 []} {b : Prop} : L.prop P b → Term.LevelEquiv P P' → L.prop P' b
  /-- `rt(U_n)` gives them, with the same relation of run time. -/
  run {P : Program} {A A' : Term 0 []} {R : RunRel} : L.run P A R → Term.LevelEquiv A A' →
    L.run P A' R

/-- The equality of the terms of the types of a level relates the terms whose levels change for equal
ones. -/
def LevelRel.RelInvariant (L : LevelRel) : Prop :=
  ∀ {A : Term 0 []} {R : TermRel} {t u t' u' : Term 0 []}, L.univ A R → R t u →
    Term.LevelEquiv t t' → Term.LevelEquiv u u' → R t' u'

/-- A sort whose level changes for one of the same value. -/
theorem Term.LevelEquiv.sort_value {s : Quality} {l : Level 0} {A' : Term 0 []} {k : Nat}
    (h : Term.LevelEquiv (.sort ⟨s, l⟩) A') (hl : l.closedValue = k) :
    ∃ l', A' = .sort ⟨s, l'⟩ ∧ l'.closedValue = k := by
  cases h with
  | sort _ h => exact ⟨_, rfl, (Level.equal_closed_iff.1 h) ▸ hl⟩

/-- The closed levels `ls₁` and `ls₂` equal one by one give the level `l` the same value. -/
theorem Level.closedValue_subst_equiv {k : Nat} {ls₁ ls₂ : Fin k → Level 0}
    (h : ∀ i, ls₁ i ≈ ls₂ i) (l : Level k) :
    (l.subst ls₁).closedValue = (l.subst ls₂).closedValue :=
  Level.equal_closed_iff.1 (Level.subst_equiv h l)

mutual

/-- `ty(U_n)` gives the types whose levels change for equal ones. -/
theorem UnivRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : TermRel} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R → Term.LevelEquiv v v' →
      UnivRel sig ι n (fun m _ => levelRel sig ι m) v' R
  | .univ hl hk, h => by
    obtain ⟨_, rfl, hl'⟩ := h.sort_value hl
    exact .univ hl' hk
  | .prop hl hk, h => by
    obtain ⟨_, rfl, hl'⟩ := h.sort_value hl
    exact .prop hl' hk
  | .data hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .data hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT c hcm => TelRel.levelEquiv ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => DesRel.levelEquiv ih (hS X _ hT) (Destructors.substLevels_levelEquiv hls' _)
          has.toSubst

/-- `ty(Ω_n)` gives the propositions whose levels change for equal ones. -/
theorem PropRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {b : Prop} :
    PropRel sig ι n (fun m _ => levelRel sig ι m) v b → Term.LevelEquiv v v' →
      PropRel sig ι n (fun m _ => levelRel sig ι m) v' b
  | .data hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .data hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT c hcm => TelRel.levelEquiv ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => DesRel.levelEquiv ih (hS X _ hT) (Destructors.substLevels_levelEquiv hls' _)
          has.toSubst

/-- A telescope whose levels change for equal ones has the same equality of the terms of its
fields. -/
theorem TelRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality}
    {rs : Nat → Option TermRel} {ps : List Parameter} {Θ Θ' : Telescope 0 [] ps} {S : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S → Telescope.LevelEquiv Θ Θ' →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ' S
  | .nil, .nil => .nil
  | .cons hA hF G hG hresp hrs, .cons _ _ h hΘ =>
    have ⟨_, hA', hv⟩ := Computes.levelEquiv hA h
    .cons hA' (FieldRel.levelEquiv ih hF hv) G
      (fun a ha => TelRel.levelEquiv ih (hG a ha)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a))))
      hresp hrs
  | .recursive hrs G hG, .cons _ _ _ hΘ =>
    .recursive hrs G fun a => TelRel.levelEquiv ih (hG a)
      (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have the same equality of the abstractions for them. -/
theorem DesRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality} {Γ : Scope}
    {rs : Nat → Option TermRel} {ns : List Name} {ds ds' : Destructors 0 Γ ns} {θ θ' : Subst 0 [] Γ}
    {S : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S → Destructors.LevelEquiv ds ds' →
      Subst.LevelEquiv θ θ' → DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds' @θ' S
  | .nil, .nil, _ => .nil
  | .recursive hrs hΘ G hG, .cons _ _ _ _ hΘe _ hds, hθ =>
    .recursive hrs (TelRel.levelEquiv ih hΘ (hΘe.subst hθ)) G
      fun f => DesRel.levelEquiv ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
  | .cons hΘ F hB hF hBresp G hG hresp hrs, .cons _ _ _ _ hΘe hBe hds, hθ =>
    .cons (TelRel.levelEquiv ih hΘ (hΘe.subst hθ)) F
      (fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        have ⟨v', hv', _⟩ :=
          Computes.levelEquiv hv (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        ⟨v', hv'⟩)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        FieldRel.levelEquiv ih (hF ts hts v hv) hvv.symm)
      hBresp G (fun f hf => DesRel.levelEquiv ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))) hresp hrs

/-- The type of a field whose levels change for equal ones has the same equality of its terms. -/
theorem FieldRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality} {v v' : Term 0 []}
    {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → Term.LevelEquiv v v' →
      FieldRel sig ι n (fun m _ => levelRel sig ι m) s v' F
  | .univ hs h, hv => .univ hs (UnivRel.levelEquiv ih h hv)
  | .univBelow hs m hm h, hv => .univBelow hs m hm ((ih m hm).univ h hv)
  | .prop h, hv => .prop (PropRel.levelEquiv ih h hv)
  | .propBelow m hm h, hv => .propBelow m hm ((ih m hm).prop h hv)

end

mutual

/-- `rt(U_n)` gives the types whose levels change for equal ones, with the same relation of run
time. -/
theorem RunUnivRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : RunRel} :
    RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v R → Term.LevelEquiv v v' →
      RunUnivRel sig ι P n (fun m _ => levelRel sig ι m) v' R
  | .univ hl hk, h => by
    obtain ⟨_, rfl, hl'⟩ := h.sort_value hl
    exact .univ hl' hk
  | .prop hl hk, h => by
    obtain ⟨_, rfl, hl'⟩ := h.sort_value hl
    exact .prop hl' hk
  | .data hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .data hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT c hcm =>
          RunTelRel.levelEquiv ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => RunDesRel.levelEquiv ih (hS X _ hT)
          (Destructors.substLevels_levelEquiv hls' _) has.toSubst

/-- A telescope whose levels change for equal ones has the same relation of run time of the terms
of its fields. -/
theorem RunTelRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {rs : Nat → Option RunRel}
    {ps : List Parameter} {Θ Θ' : Telescope 0 [] ps} {S : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S → Telescope.LevelEquiv Θ Θ' →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ' S
  | .nil, .nil => .nil
  | .cons hA hF hR G hG hrs, .cons _ _ h hΘ =>
    have ⟨_, hA', hv⟩ := Computes.levelEquiv hA h
    .cons hA' (FieldRel.levelEquiv ih hF hv) (RunFieldRel.levelEquiv ih hR hv) G
      (fun a ha => RunTelRel.levelEquiv ih (hG a ha)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a))))
      hrs
  | .recursive hrs G hG, .cons _ _ _ hΘ =>
    .recursive hrs G fun a => RunTelRel.levelEquiv ih (hG a)
      (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have the same relation of run time of the observations by them. -/
theorem RunDesRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {D : Name} {Γ : Scope}
    {rs : Nat → Option RunRel} {ns : List Name} {ds ds' : Destructors 0 Γ ns} {θ θ' : Subst 0 [] Γ}
    {S : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs ds @θ S →
      Destructors.LevelEquiv ds ds' → Subst.LevelEquiv θ θ' →
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs ds' @θ' S
  | .nil, .nil, _ => .nil
  | .recursive hi hrs hRΘ G hG, .cons _ _ _ _ hΘe _ hds, hθ =>
    .recursive hi hrs (RunTelRel.levelEquiv ih hRΘ (hΘe.subst hθ)) G
      fun f => RunDesRel.levelEquiv ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
  | .cons hi hΘ hRΘ F R hB hF hR G hG hrs, .cons _ _ _ _ hΘe hBe hds, hθ =>
    .cons hi (TelRel.levelEquiv ih hΘ (hΘe.subst hθ)) (RunTelRel.levelEquiv ih hRΘ (hΘe.subst hθ))
      F R
      (fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        have ⟨v', hv', _⟩ :=
          Computes.levelEquiv hv (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        ⟨v', hv'⟩)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        FieldRel.levelEquiv ih (hF ts hts v hv) hvv.symm)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        RunFieldRel.levelEquiv ih (hR ts hts v hv) hvv.symm)
      G (fun f hf => RunDesRel.levelEquiv ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))) hrs

/-- The type of a field whose levels change for equal ones has the same relation of run time of its
terms. -/
theorem RunFieldRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : RunRel} :
    RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R → Term.LevelEquiv v v' →
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v' R
  | .univ h, hv => .univ (RunUnivRel.levelEquiv ih h hv)
  | .univBelow m hm h, hv => .univBelow m hm ((ih m hm).run h hv)
  | .prop h, hv => .prop (PropRel.levelEquiv ih h hv)
  | .propBelow m hm h, hv => .propBelow m hm ((ih m hm).prop h hv)

end

/-- The relations of every level give the types whose levels change for equal ones. -/
theorem levelRel_levelInvariant {sig : Signature} {ι : Interpretation} (n : Nat) :
    (levelRel sig ι n).LevelInvariant :=
  have ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant :=
    fun m _ => levelRel_levelInvariant m
  { univ := fun h hv => levelRel_univ_iff.2 (UnivRel.levelEquiv ih (levelRel_univ_iff.1 h) hv)
    prop := fun h hv => levelRel_prop_iff.2 (PropRel.levelEquiv ih (levelRel_prop_iff.1 h) hv)
    run := fun h hv => levelRel_run_iff.2 (RunUnivRel.levelEquiv ih (levelRel_run_iff.1 h) hv) }
termination_by n
decreasing_by all_goals assumption

mutual

/-- The equality of the terms of a type of `U_n` relates the terms whose levels change for equal
ones, in a signature whose names are distinct. -/
theorem UnivRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {v : Term 0 []}
    {R : TermRel} {t u t' u' : Term 0 []} :
    UnivRel sig ι n (fun m _ => levelRel sig ι m) v R → R t u → Term.LevelEquiv t t' →
      Term.LevelEquiv u u' → R t' u'
  | .univ (k := k) _ _, ⟨⟨R', h₁, h₂⟩, hr⟩, ht, hu =>
    ⟨⟨R', (levelRel_levelInvariant k).univ h₁ ht, (levelRel_levelInvariant k).univ h₂ hu⟩, fun P =>
      have ⟨Q, h₁, h₂⟩ := hr P
      ⟨Q, (levelRel_levelInvariant k).run h₁ ht, (levelRel_levelInvariant k).run h₂ hu⟩⟩
  | .prop (k := k) _ _, ⟨b₁, b₂, h₁, h₂, hb⟩, ht, hu =>
    ⟨b₁, b₂, (levelRel_levelInvariant k).prop h₁ ht, (levelRel_levelInvariant k).prop h₂ hu, hb⟩
  | .data h _ _ _ _ _ _ S hS, hR, ht, hu => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hmono := fun (X Y : Name → TermRel) (hXY : ∀ D v w, X D v w → Y D v w) =>
      TelRel.block_mono hd hp (Θ := fun c => ⟨_, c.fieldsAt _ _ _⟩)
        (F := fun X D => (X D).computed sig ι) hS X Y fun D _ _ => TermRel.computed_mono (hXY D)
    refine hR (fun D v w => ∀ v' w', Term.LevelEquiv v v' → Term.LevelEquiv w w' →
        DataType.blockRel _ S D v' w')
      (fun T hT v w ⟨c, hcm, ts, us, hv, hw, hcS⟩ v' w' hv' hw' => ?_) _ _ ht hu
    obtain ⟨_, _, _, _, _, rfl⟩ := hv
    obtain ⟨_, _, _, _, _, rfl⟩ := hw
    cases hv' with
    | ctor _ _ _ _ _ _ hts =>
      cases hw' with
      | ctor _ _ _ _ _ _ hus =>
        exact DataType.blockRel_closed hmono hT ⟨c, hcm, _, _, ⟨_, _, _, _, _, rfl⟩,
          ⟨_, _, _, _, _, rfl⟩, TelRel.rel_levelEquiv hd ih (hS _ T hT c hcm) _ _ _
            (hS _ T hT c hcm)
            (fun _ => Option.rel_map (fun D _ _ _ _ h ht hu => by
              obtain ⟨v₁, w₁, hc₁, hc₂, hX⟩ := h
              obtain ⟨v₂, hc₁', hv₂⟩ := Computes.levelEquiv hc₁ ht
              obtain ⟨w₂, hc₂', hw₂⟩ := Computes.levelEquiv hc₂ hu
              exact ⟨v₂, w₂, hc₁', hc₂', hX _ _ hv₂ hw₂⟩) _)
            hcS hts hus⟩
  | .codata _ _ _ _ _ _ _ _ hS, hR, ht, hu => by
    obtain ⟨X, hX, hx⟩ := hR
    refine ⟨fun D a b => ∃ a₀ b₀, X D a₀ b₀ ∧ Term.LevelEquiv a₀ a ∧ Term.LevelEquiv b₀ b,
      fun T hT a b ⟨a₀, b₀, hab, ha, hb⟩ => ?_, _, _, hx, ht, hu⟩
    obtain ⟨o₁, o₂, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
      hS'⟩ := hX T hT a₀ b₀ hab
    cases ha with
    | corec _ _ _ _ hl₁ has₁ _ _ _ =>
      cases hb with
      | corec _ _ _ _ hl₂ has₂ _ _ _ =>
        refine ⟨_, _, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
          DesRel.rel_levelEquiv hd ih (hS X T hT) _ _ _ (hS _ T hT)
            (fun _ => Option.rel_map (fun D _ _ _ _ h ht hu => by
              obtain ⟨v₁, w₁, hc₁, hc₂, hX⟩ := h
              obtain ⟨v₂, hc₁', hv₂⟩ := Computes.levelEquiv hc₁ ht
              obtain ⟨w₂, hc₂', hw₂⟩ := Computes.levelEquiv hc₂ hu
              exact ⟨v₂, w₂, hc₁', hc₂', v₁, w₁, hX, hv₂, hw₂⟩) _)
            hS' (fun d xs => ?_) (fun d xs => ?_)⟩
        · exact .obs _ _ _ d hl₁ (has₁.rename _) (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl₁ has₁
            ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)
        · exact .obs _ _ _ d hl₂ (has₂.rename _) (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl₂ has₂
            ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)

/-- The equality of the terms of the fields of a telescope relates the terms whose levels change
for equal ones, at relations of the recursive fields that do. -/
theorem TelRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {ps : List Parameter} {Θ : Telescope 0 [] ps} {S₁ : FieldsRel}
    {ts us ts' us' : Terms 0 []} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Option.Rel (fun R₁ R₂ => ∀ t u t' u', R₁ t u → Term.LevelEquiv t t' →
          Term.LevelEquiv u u' → R₂ t' u') (rs₁ i) (rs₂ i)) →
        S₁ ts us → Terms.LevelEquiv ts ts' → Terms.LevelEquiv us us' → S₂ ts' us'
  | .nil, _, _, _, h', _, h, .nil, .nil => by cases h'; exact h
  | .cons hA hF _ hG _ hrs, _, _, _, h', hR, h, .cons ht hts, .cons hu hus => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    cases h' with
    | cons hA' hF' _ hG' hresp' _ =>
      cases Computesι.det hd hA hA'
      obtain ⟨h₁, h₂⟩ := h
      have hFF := FieldRel.unique hd hp hF _ _ hF'
      have hFp := FieldRel.isPer hd hp hF
      have htt := hFp.trans h₁ (hFp.symm h₁)
      have htt' := FieldRel.rel_levelEquiv hd ih hF htt (Term.LevelEquiv.refl _) ht
      exact ⟨(hFF _ _).1 (FieldRel.rel_levelEquiv hd ih hF h₁ ht hu),
        (hresp' _ _ ((hFF _ _).1 htt') _ _).1
          (TelRel.rel_levelEquiv hd ih (hG _ htt) _ _ _ (hG' _ ((hFF _ _).1 htt))
            (fun i => hR (i + 1)) h₂ hts hus)⟩
    | recursive hrs' _ _ => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive hrs _ hG, _, _, _, h', hR, h, .cons ht hts, .cons hu hus => by
    cases h' with
    | cons _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        obtain ⟨h₁, h₂⟩ := h
        exact ⟨hr _ _ _ _ h₁ ht hu,
          TelRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _ (hG' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1)) h₂
            hts hus⟩

/-- The equality of the abstractions for destructors relates the observations whose levels change
for equal ones, at relations of the recursive destructors that do. -/
theorem DesRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {s₁ : Quality}
    {rs₁ : Nat → Option TermRel} {Γ : Scope} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S₁ : ObsRel} {o₁ o₂ o₁' o₂' : Observations} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Option TermRel) (S₂ : ObsRel),
        DesRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ ds @θ S₂ →
        (∀ i, Option.Rel (fun R₁ R₂ => ∀ t u t' u', R₁ t u → Term.LevelEquiv t t' →
          Term.LevelEquiv u u' → R₂ t' u') (rs₁ i) (rs₂ i)) →
        S₁ o₁ o₂ → (∀ d ps, Term.LevelEquiv (o₁ d ps) (o₁' d ps)) →
        (∀ d ps, Term.LevelEquiv (o₂ d ps) (o₂' d ps)) → S₂ o₁' o₂'
  | .nil, _, _, _, h', _, _, _, _ => by cases h'; trivial
  | .cons (d := d) (ps := ps) (SΘ := SΘ) hΘ F hB hF hBresp _ hG _ hrs, _, _, _, h', hR, ⟨h₁, h₂⟩,
      e₁, e₂ => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd hp (fun _ _ h => by cases h) hΘ
    have hEp := AbstractionRel.isPer hSp
      (fun ts hts => have ⟨_, hv⟩ := hB ts hts; FieldRel.isPer hd hp (hF ts hts _ hv)) hBresp
    have hE : ∀ f₁ f₂ f₁' f₂', AbstractionRel (ps := ps) SΘ F f₁ f₂ → Term.LevelEquiv f₁ f₁' →
        Term.LevelEquiv f₂ f₂' → AbstractionRel (ps := ps) SΘ F f₁' f₂' :=
      fun _ _ _ _ h ef₁ ef₂ ts us hts =>
        have ⟨_, hv⟩ := hB ts (hSp.trans hts (hSp.symm hts))
        FieldRel.rel_levelEquiv hd ih (hF ts (hSp.trans hts (hSp.symm hts)) _ hv) (h ts us hts)
          (ef₁.subst (Subst.LevelEquiv.refl _)) (ef₂.subst (Subst.LevelEquiv.refl _))
    have hff := hEp.trans h₁ (hEp.symm h₁)
    have hff' := hE _ _ _ _ hff (Term.LevelEquiv.refl _) (e₁ d ps)
    cases h' with
    | cons hΘ' F' _ hF' _ _ hG' hresp' _ =>
      have hSS := TelRel.unique hd hp hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        FieldRel.unique hd hp (hF ts hts _ hv) _ _ (hF' ts ((hSS _ _).1 hts) _ hv)
      have hEE := AbstractionRel.congr hSp hSS hFF
      exact ⟨(hEE _ _).1 (hE _ _ _ _ h₁ (e₁ d ps) (e₂ d ps)),
        (hresp' _ _ ((hEE _ _).1 hff') _ _).1
          (DesRel.rel_levelEquiv hd ih (hG _ hff) _ _ _ (hG' _ ((hEE _ _).1 hff))
            (fun i => hR (i + 1)) h₂ e₁ e₂)⟩
    | recursive hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
  | .recursive (d := d) (ps := ps) hrs hΘ _ hG, _, _, _, h', hR, ⟨h₁, h₂⟩, e₁, e₂ => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    cases h' with
    | cons _ _ _ _ _ _ _ _ hrs' => have h0 := hR 0; rw [hrs, hrs'] at h0; cases h0
    | recursive hrs' hΘ' _ hG' =>
      have h0 := hR 0
      rw [hrs, hrs'] at h0
      cases h0 with
      | some hr =>
        have hSS := TelRel.unique hd hp hΘ _ _ hΘ'
        exact ⟨fun ts us hts => hr _ _ _ _ (h₁ ts us ((hSS _ _).2 hts))
            ((e₁ d ps).subst (Subst.LevelEquiv.refl _)) ((e₂ d ps).subst (Subst.LevelEquiv.refl _)),
          DesRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _
            (hG' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1)) h₂ e₁ e₂⟩

/-- The equality of the terms of the type of a field relates the terms whose levels change for equal
ones. -/
theorem FieldRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {s : Quality}
    {v : Term 0 []} {F : TermRel} {t u t' u' : Term 0 []} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → F t u → Term.LevelEquiv t t' →
      Term.LevelEquiv u u' → F t' u'
  | .univ _ h, ⟨_, _, hct, hcu, hvw⟩, ht, hu =>
    have ⟨_, hct', hv⟩ := Computes.levelEquiv hct ht
    have ⟨_, hcu', hw⟩ := Computes.levelEquiv hcu hu
    ⟨_, _, hct', hcu', UnivRel.rel_levelEquiv hd ih h hvw hv hw⟩
  | .univBelow _ m hm h, ⟨_, _, hct, hcu, hvw⟩, ht, hu =>
    have ⟨_, hct', hv⟩ := Computes.levelEquiv hct ht
    have ⟨_, hcu', hw⟩ := Computes.levelEquiv hcu hu
    ⟨_, _, hct', hcu', ih m hm h hvw hv hw⟩
  | .prop _, h, _, _ => h
  | .propBelow _ _ _, h, _, _ => h

end

/-- The equality of the terms of the types of every level relates the terms whose levels change for
equal ones, in a signature whose names are distinct. -/
theorem levelRel_relInvariant {sig : Signature} {ι : Interpretation} (hd : sig.Distinct)
    (n : Nat) : (levelRel sig ι n).RelInvariant :=
  have ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant :=
    fun m _ => levelRel_relInvariant hd m
  fun h => UnivRel.rel_levelEquiv hd ih (levelRel_univ_iff.1 h)
termination_by n
decreasing_by all_goals assumption

/-- A canonical type whose levels change for equal ones has the same equality of its terms. -/
theorem HasEq.levelEquiv {sig : Signature} {ι : Interpretation} {v v' : Term 0 []} {R : TermRel}
    (hA : HasEq sig ι v R) (h : Term.LevelEquiv v v') : HasEq sig ι v' R :=
  match hA with
  | .univ n hn => .univ n ((levelRel_levelInvariant n).univ hn h)
  | .prop n b hn hR => .prop n b ((levelRel_levelInvariant n).prop hn h) hR

/-- A canonical type whose levels change for equal ones has the same relation of run time. -/
theorem HasRun.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {v v' : Term 0 []}
    {R : RunRel} (hA : HasRun sig ι P v R) (h : Term.LevelEquiv v v') : HasRun sig ι P v' R :=
  match hA with
  | .univ n hn => .univ n ((levelRel_levelInvariant n).run hn h)
  | .prop n b hn hR => .prop n b ((levelRel_levelInvariant n).prop hn h) hR

/-- The equality of the terms of a canonical type relates the terms whose levels change for equal
ones, in a signature whose names are distinct. -/
theorem HasEq.rel_levelEquiv {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R : TermRel}
    {t u t' u' : Term 0 []} (hd : sig.Distinct) (hA : HasEq sig ι v R) (htu : R t u)
    (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u') : R t' u' :=
  match hA with
  | .univ n hn => levelRel_relInvariant hd n hn htu ht hu
  | .prop _ _ _ hR => (hR t' u').2 ((hR t u).1 htu)

/-- A proposition whose levels change for equal ones stays a proposition. -/
theorem IsProp.levelEquiv {sig : Signature} {ι : Interpretation} {v v' : Term 0 []}
    (hA : IsProp sig ι v) (h : Term.LevelEquiv v v') : IsProp sig ι v' :=
  let ⟨n, b, hn⟩ := hA
  ⟨n, b, (levelRel_levelInvariant n).prop hn h⟩

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
  let ⟨_, _, R, hcA, hcB, hRA, hRB, hr⟩ := hAB
  let ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
  let ⟨_, hcB', hB₀⟩ := hcB.levelEquiv hB
  ⟨_, _, R, hcA', hcB', hRA.levelEquiv hA₀, hRB.levelEquiv hB₀, fun P Q =>
    ⟨fun h => ((hr P Q).1 (h.levelEquiv hA₀.symm)).levelEquiv hB₀,
      fun h => ((hr P Q).2 (h.levelEquiv hB₀.symm)).levelEquiv hA₀⟩⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` still hold when the levels of the terms and of the type
change for equal ones, in a signature whose names are distinct. -/
theorem EqTermClause.levelEquiv {sig : Signature} {ι : Interpretation} {t u A t' u' A' : Term 0 []}
    (hd : sig.Distinct) (htu : EqTermClause sig ι t u A) (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u')
    (hA : Term.LevelEquiv A A') : EqTermClause sig ι t' u' A' := by
  refine ⟨fun hP' => ?_, fun hP' => ?_⟩
  · obtain ⟨_, _, _, R, hcA, hct, hcu, hR, hvw⟩ :=
      htu.1 fun hP => hP' (hP.levelEquiv hA)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
    obtain ⟨_, hct', hv⟩ := hct.levelEquiv ht
    obtain ⟨_, hcu', hw⟩ := hcu.levelEquiv hu
    exact ⟨_, _, _, R, hcA', hct', hcu', hR.levelEquiv hA₀, hR.rel_levelEquiv hd hvw hv hw⟩
  · obtain ⟨_, R, hcA, hR, htu'⟩ := htu.2 (hP'.levelEquiv hA.symm)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hA
    exact ⟨_, R, hcA', hR.levelEquiv hA₀, hR.rel_levelEquiv hd htu' ht hu⟩

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
  ⟨htu.1.levelEquiv hA hA, htu.2.levelEquiv htu.1.1 ht hu hA⟩

/-! ## Contexts and Telescopes

The meaning of a type declaration gives the fields of its constructors in the context of its
parameters at the values of its levels, while an instance gives them at its own levels: two equal
substitutions of a context are equal substitutions of the context at levels of the same values, and
two closed telescopes equal in a sort stay so when their levels and that of the sort change for
equal ones. -/

/-- Two contexts whose types are equal up to their levels. -/
inductive Context.LevelEquiv {k : Nat} : {Γ : Scope} → Context k Γ → Context k Γ → Prop where
  /-- `ε`. -/
  | empty : Context.LevelEquiv .empty .empty
  /-- `Γ, x : A`. -/
  | var {Γ : Scope} {ctx₁ ctx₂ : Context k Γ} {A₁ A₂ : Term k Γ} (h : Context.LevelEquiv ctx₁ ctx₂)
      (hA : Term.LevelEquiv A₁ A₂) : Context.LevelEquiv (ctx₁.var A₁) (ctx₂.var A₂)
  /-- `Γ, X : (Θ ⊢ A ◀ ψ)`. -/
  | secondOrder {Γ : Scope} {ps : List Parameter} {ctx₁ ctx₂ : Context k Γ}
      {Θ₁ Θ₂ : Telescope k Γ ps} {A₁ A₂ : Term k (Γ.extend ps.length)} (ψ : ResultOwnership Grade ps.length)
      (h : Context.LevelEquiv ctx₁ ctx₂) (hΘ : Telescope.LevelEquiv Θ₁ Θ₂)
      (hA : Term.LevelEquiv A₁ A₂) :
      Context.LevelEquiv (ctx₁.secondOrder Θ₁ A₁ ψ) (ctx₂.secondOrder Θ₂ A₂ ψ)

/-- Equal levels that replace the level variables give contexts equal up to their levels. -/
theorem Context.substLevels_levelEquiv {k k' : Nat} {ls₁ ls₂ : Fin k → Level k'}
    (h : ∀ i, ls₁ i ≈ ls₂ i) : {Γ : Scope} → (ctx : Context k Γ) →
      Context.LevelEquiv (ctx.substLevels ls₁) (ctx.substLevels ls₂)
  | _, .empty => .empty
  | _, .var ctx A => .var (Context.substLevels_levelEquiv h ctx) (Term.substLevels_levelEquiv h A)
  | _, .secondOrder ctx Θ A ψ => .secondOrder ψ (Context.substLevels_levelEquiv h ctx)
      (Telescope.substLevels_levelEquiv h Θ) (Term.substLevels_levelEquiv h A)

/-- Two contexts equal up to their levels in the other order. -/
theorem Context.LevelEquiv.symm {k : Nat} {Γ : Scope} {ctx₁ ctx₂ : Context k Γ} :
    Context.LevelEquiv ctx₁ ctx₂ → Context.LevelEquiv ctx₂ ctx₁
  | .empty => .empty
  | .var h hA => .var h.symm hA.symm
  | .secondOrder ψ h hΘ hA => .secondOrder ψ h.symm hΘ.symm hA.symm

/-- Contexts and telescopes equal up to their levels give appended contexts equal up to their
levels. -/
theorem Context.LevelEquiv.append {k : Nat} : {Γ : Scope} → {ps : List Parameter} →
    {ctx₁ ctx₂ : Context k Γ} → {Θ₁ Θ₂ : Telescope k Γ ps} → Context.LevelEquiv ctx₁ ctx₂ →
      Telescope.LevelEquiv Θ₁ Θ₂ → Context.LevelEquiv (ctx₁.append Θ₁) (ctx₂.append Θ₂)
  | _, _, _, _, _, _, h, .nil => h
  | _, _, _, _, _, _, h, .cons _ _ hA hΘ => Context.LevelEquiv.append (Γ := .var :: _) (h.var hA) hΘ

/-- Two equal substitutions of a context are equal substitutions of a context equal to it up to its
levels: each type of the context changes for one equal to it up to its levels, which the meaning of
the closed judgments does not tell apart. -/
theorem EqSubst.levelEquiv {sig : Signature} {ι : Interpretation} : {Γ : Scope} →
    {ctx₁ ctx₂ : Context 0 Γ} → Context.LevelEquiv ctx₁ ctx₂ → {σ₁ σ₂ : Subst 0 [] Γ} →
      EqSubst sig ι ctx₁ σ₁ σ₂ → EqSubst sig ι ctx₂ σ₁ σ₂
  | _, _, _, .empty, _, _, hσ => hσ
  | _, _, _, .var h hA, _, _, hσ => by
    obtain ⟨hσ, ht⟩ := (EqSubst.var_iff _ _ _ _).1 hσ
    exact (EqSubst.var_iff _ _ _ _).2 ⟨EqSubst.levelEquiv h hσ,
      ht.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _)
        (hA.subst (Subst.LevelEquiv.refl _))⟩
  | _, _, _, .secondOrder ψ h hΘ hA, _, _, hσ => by
    obtain ⟨hσ, ht⟩ := (EqSubst.secondOrder_iff _ _ _ _ _ _).1 hσ
    refine (EqSubst.secondOrder_iff _ _ _ _ _ _).2 ⟨EqSubst.levelEquiv h hσ, fun τ₁ τ₂ hτ => ?_⟩
    have hτ' := EqSubst.levelEquiv
      (Context.LevelEquiv.empty.append (hΘ.symm.subst (Subst.LevelEquiv.refl _))) hτ
    exact (ht τ₁ τ₂ hτ').levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _)
      ((hA.subst (Subst.LevelEquiv.refl _)).subst (Subst.LevelEquiv.refl _))
termination_by _ ctx₁ => ctx₁.size
decreasing_by
  all_goals first
    | (simp only [Context.size]; omega)
    | (rw [Context.size_append]; simp only [Context.size]; omega)

/-- Two closed telescopes equal in a sort stay so when their levels, and that of the sort, change for
equal ones, which the meaning of the closed judgments does not tell apart. -/
theorem ValidEqTelescope₀.levelEquiv {sig : Signature} {ι : Interpretation} {κ κ' : Universe 0}
    (hq : κ.quality = κ'.quality) (hl : κ.level ≈ κ'.level) :
    {ps : List Parameter} → {Θ₁ Θ₂ Θ₁' Θ₂' : Telescope 0 [] ps} →
      ValidEqTelescope₀ sig ι κ Θ₁ Θ₂ → Telescope.LevelEquiv Θ₁ Θ₁' →
        Telescope.LevelEquiv Θ₂ Θ₂' → ValidEqTelescope₀ sig ι κ' Θ₁' Θ₂'
  | [], .nil, .nil, .nil, .nil, h, _, _ => by rw [ValidEqTelescope₀] at h ⊢; exact h
  | _ :: _, .cons .., .cons .., .cons .., .cons .., h, .cons _ _ hA₁ hΘ₁, .cons _ _ hA₂ hΘ₂ => by
    rw [ValidEqTelescope₀] at h ⊢
    obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
    refine ⟨⟨κ₁, ⟨hq ▸ hκ.1, fun ρ => (hl ρ) ▸ hκ.2 ρ⟩,
      hA.levelEquiv hA₁ hA₂ (Term.LevelEquiv.refl _)⟩, fun v₁ v₂ hv => ?_⟩
    exact ValidEqTelescope₀.levelEquiv hq hl
      (hΘ v₁ v₂ (hv.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) hA₁.symm))
      (hΘ₁.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl _)))
      (hΘ₂.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl _)))

end Sic.Core
