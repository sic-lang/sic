module

public import Sic.Core.Meaning
public import Sic.Core.Nesting.Relation
import Sic.Core.Lifting.Functionality
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

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
  | .recursor r ς χ D qs ps s hl has h hκ hCs hus =>
    .recursor r ς χ D qs ps s hl (has.rename α) (h.rename α) hκ (hCs.rename α) (hus.rename α)
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
  | .recursor r ς χ D qs ls ps as t ⟨s, l⟩ Cs us =>
    .recursor r ς χ D qs ps s (Level.ListEquiv.map_subst h ls)
      (InstanceArgs.substLevels_levelEquiv h as) (Term.substLevels_levelEquiv h t)
      (Level.subst_equiv h l) (Motives.substLevels_levelEquiv h Cs)
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
  | _, _, .cons p q ς Θ B ψ ds =>
    .cons p q ς ψ (Telescope.substLevels_levelEquiv h Θ) (Term.substLevels_levelEquiv h B)
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
  | .recursor r ς χ D qs ps s hl has h hκ hCs hus =>
    .recursor r ς χ D qs ps s hl (has.subst₀ hσ) (h.subst₀ hσ) hκ (hCs.subst₀ hσ) (hus.subst₀ hσ)
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
theorem Subst.LevelEquiv.snoc {k : Nat} {Γ' Γ : Scope} {e : Scope.Entry} {θ₁ θ₂ : Subst k Γ' Γ}
    (h : Subst.LevelEquiv θ₁ θ₂) {f₁ f₂ : Term k (Γ'.extend e.params.length)}
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
  | .recursor r ς χ D qs ps s hl has h hκ hCs hus =>
    .recursor r ς χ D qs ps s hl (has.subst hθ) (h.subst hθ) hκ (hCs.subst hθ) (hus.subst hθ)
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
theorem Constructor.fieldsAt_levelEquiv {j g k k' : Nat} {Γ Δ : Scope} (c : Constructor j g k Δ)
    (I : Instance j g) {ls₁ ls₂ : Fin k → Level k'} {as₁ as₂ : InstanceArgs k' Γ Δ}
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
    | recursor _ _ _ _ _ _ _ _ _ ht => exact .recursor (ih ht)
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
    {l₁ l₂ : Level k} → l₁ ≈ l₂ → (s : Quality) → {l₁' l₂' : Level k} → l₁' ≈ l₂' →
    {C₁ C₂ : Term k Γ} → Term.LevelEquiv C₁ C₂ →
    {b₁ b₂ : Term k (Γ.extend ps.length)} → Term.LevelEquiv b₁ b₂ →
      Term.LevelEquiv (Term.unpack r u₁ Θ₁ κs₁ l₁ ⟨s, l₁'⟩ C₁ b₁)
        (Term.unpack r u₂ Θ₂ κs₂ l₂ ⟨s, l₂'⟩ C₂ b₂)
  | _, [], _, _, hu, _, _, .nil, _, _, _, _, _, hl, s, _, _, hs, _, _, hC, _, _, hb =>
    .recursor _ _ _ _ _ _ s (.cons hl .nil) .nil hu hs (.cons (hC.rename _) .nil) (.cons hb .nil)
  | _, _ :: _, _, _, hu, _, _, .cons _ _ hA hΘ, _, _, hκ, _, _, hl, s, _, _, hs', _, _, hC, _, _,
      hb => by
    cases hκ with
    | nil =>
      exact .recursor _ _ _ _ _ _ s (.cons hl (.cons (Telescope.packLevel_equiv .nil hl) .nil))
        (.snoc (.snoc .nil hA) (hΘ.pack .nil hl)) hu hs' (.cons (hC.rename _) .nil)
        (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hΘ.rename _) .nil hl s hs'
          (hC.rename _) (hb.rename _)) .nil)
    | cons _ h hs =>
      exact .recursor _ _ _ _ _ _ s (.cons h (.cons (Telescope.packLevel_equiv hs hl) .nil))
        (.snoc (.snoc .nil hA) (hΘ.pack hs hl)) hu hs' (.cons (hC.rename _) .nil)
        (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hΘ.rename _) hs hl s hs'
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
  exact .recursor _ _ _ _ _ _ s (.cons (Telescope.packLevel_equiv hκs h0) (.cons hκ .nil))
    (.snoc (.snoc .nil (hS.pack hκs h0)) hT) hv hκ (.cons (hT.rename _) .nil)
    (.cons (Term.LevelEquiv.unpack r (Term.LevelEquiv.refl _) (hS.rename _) hκs h0 s hκ
        (hT.rename _)
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

/-! ## Liftings and Recursive Results

The reduction of a recursor builds the results of the nested fields from the types of the fields,
by the liftings of their instances: the levels of these results are those of the types, of the
motives and of the instance of the recursor, so that the results of terms, at types, motives and
an instance equal up to their levels, are equal up to their levels.
The result of a nested field reads each destructor of its type by its name, which names one
destructor in a signature whose names are distinct. -/

/-- A level joined to levels, and a level equal to it joined to equal levels, are equal. -/
theorem Level.joins_equiv {k : Nat} : {ls₁ ls₂ : List (Level k)} → Level.ListEquiv ls₁ ls₂ →
    {l₁ l₂ : Level k} → l₁ ≈ l₂ → l₁.joins ls₁ ≈ l₂.joins ls₂
  | _, _, .nil, _, _, h => h
  | _, _, .cons h hs, _, _, hl =>
    Level.joins_equiv hs fun ρ => by
      show Max.max _ _ = Max.max _ _
      rw [hl ρ, h ρ]

/-- Lists of equal levels, followed by lists of equal levels, are lists of equal levels. -/
theorem Level.ListEquiv.append {k : Nat} : {ls₁ ls₂ ls₁' ls₂' : List (Level k)} →
    Level.ListEquiv ls₁ ls₂ → Level.ListEquiv ls₁' ls₂' →
      Level.ListEquiv (ls₁ ++ ls₁') (ls₂ ++ ls₂')
  | _, _, _, _, .nil, h' => h'
  | _, _, _, _, .cons h hs, h' => .cons h (hs.append h')

/-- Two terms equal up to their levels stay so in a scope equal to theirs. -/
theorem Term.LevelEquiv.cast {k : Nat} {Γ Γ' : Scope} (h : Γ = Γ') {t₁ t₂ : Term k Γ}
    (ht : Term.LevelEquiv t₁ t₂) : Term.LevelEquiv (h ▸ t₁) (h ▸ t₂) := by
  subst h
  exact ht

/-- The terms of arguments equal up to their levels are equal up to their levels. -/
theorem Args.LevelEquiv.terms {k : Nat} {Γ : Scope} : {ps : List Parameter} →
    {ts₁ ts₂ : Args k Γ ps} → Args.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv ts₁.terms ts₂.terms
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons h hs.terms

/-- Terms equal up to their levels to the terms of arguments of a telescope are the terms of
arguments of this telescope. -/
theorem Args.exists_of_terms_levelEquiv {k : Nat} {Γ : Scope} : {ps : List Parameter} →
    (ts : Args k Γ ps) → {fs : Terms k Γ} → Terms.LevelEquiv ts.terms fs →
      ∃ ts₂ : Args k Γ ps, ts₂.terms = fs ∧ Args.LevelEquiv ts ts₂
  | [], .nil, _, h => by
    cases h with
    | nil => exact ⟨.nil, rfl, .nil⟩
  | _ :: _, .cons _ ts, _, h => by
    cases h with
    | cons h hs =>
      obtain ⟨ts₂, rfl, hts⟩ := Args.exists_of_terms_levelEquiv ts hs
      exact ⟨.cons _ ts₂, rfl, .cons h hts⟩

/-- The types of the entries of telescopes equal up to their levels, at arguments equal up to their
levels, are equal up to their levels. -/
theorem Telescope.LevelEquiv.typesAt {k : Nat} {Γ : Scope} : {ps : List Parameter} →
    {Θ₁ Θ₂ : Telescope k Γ ps} → {ts₁ ts₂ : Args k Γ ps} → Telescope.LevelEquiv Θ₁ Θ₂ →
      Args.LevelEquiv ts₁ ts₂ → Terms.LevelEquiv (Θ₁.typesAt ts₁) (Θ₂.typesAt ts₂)
  | _, _, _, _, _, .nil, .nil => .nil
  | _, _, _, _, _, .cons _ _ hA hΘ, .cons ht hts =>
    .cons hA (Telescope.LevelEquiv.typesAt (hΘ.subst₀ (Subst₀.LevelEquiv.single ht)) hts)

/-- The motives of motives equal up to their levels, at a position, are equal up to their
levels. -/
theorem Motives.LevelEquiv.get {k : Nat} {Γ : Scope} : {Cs₁ Cs₂ : Motives k Γ} →
    Motives.LevelEquiv Cs₁ Cs₂ → (i : Nat) →
      (Cs₁.get i = none ∧ Cs₂.get i = none) ∨
        ∃ (n : Nat) (C₁ C₂ : Term k (Γ.extend (n + 1))),
          Cs₁.get i = some ⟨n, C₁⟩ ∧ Cs₂.get i = some ⟨n, C₂⟩ ∧ Term.LevelEquiv C₁ C₂
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => .inr ⟨_, _, _, rfl, rfl, h⟩
  | _, _, .cons _ hs, i + 1 => hs.get i

/-- Branches of corecursors equal up to their levels are as many. -/
theorem CorecBranches.LevelEquiv.length_eq {k : Nat} {Γ : Scope} : {gs₁ gs₂ : CorecBranches k Γ} →
    CorecBranches.LevelEquiv gs₁ gs₂ → gs₁.length = gs₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg (· + 1) hs.length_eq

/-- Branches of a corecursor, each of which is equal up to its levels to a branch that has a
property of its position, are equal up to their levels to branches that have this property. -/
theorem CorecBranches.LevelEquiv.exists_of_forall {k : Nat} {Γ : Scope} :
    (gs₁ : CorecBranches k Γ) →
      (Q : Nat → (Σ n m a, Term k (((Γ.extend n).extend m).extend a)) → Prop) →
      (∀ i n m a (g₁ : Term k (((Γ.extend n).extend m).extend a)),
        gs₁.get i = some ⟨n, m, a, g₁⟩ → ∃ g₂, Term.LevelEquiv g₁ g₂ ∧ Q i ⟨n, m, a, g₂⟩) →
      ∃ gs₂, CorecBranches.LevelEquiv gs₁ gs₂ ∧ ∀ i b, gs₂.get i = some b → Q i b
  | .nil, _, _ => ⟨.nil, .nil, fun _ _ h => nomatch h⟩
  | .cons n m a g gs, Q, h => by
    obtain ⟨g₂, hg, hq⟩ := h 0 n m a g rfl
    obtain ⟨gs₂, hgs, hqs⟩ := CorecBranches.LevelEquiv.exists_of_forall gs (fun i => Q (i + 1))
      (fun i n m a g₁ hi => h (i + 1) n m a g₁ hi)
    refine ⟨.cons n m a g₂ gs₂, .cons hg hgs, fun i b hb => ?_⟩
    cases i with
    | zero =>
      cases hb
      exact hq
    | succ i => exact hqs i b hb

/-- The substitutions of the observations of terms equal up to their levels, after substitutions
equal up to their levels, are equal up to their levels. -/
theorem Destructors.Pos.obsSubst_levelEquiv {k k' : Nat} {Γ' : Scope} {d : Name} {p q ς : Grade}
    {ps : List Parameter} {o₁ o₂ : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)}
    (ho : ∀ d ps', Term.LevelEquiv (o₁ d ps') (o₂ d ps')) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (h : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {θ₁ θ₂ : Subst k Γ' Γ} → Subst.LevelEquiv θ₁ θ₂ →
        Subst.LevelEquiv (h.obsSubst o₁ θ₁) (h.obsSubst o₂ θ₂)
  | _, _, _, _, _, _, _, .here, _, _, hθ => hθ
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') h, _, _, hθ =>
    h.obsSubst_levelEquiv ho (hθ.snoc (ho d' ps'))

/-- Two motives of a type of a block equal up to their levels: instances and motives equal up to
their levels, at equal levels. -/
structure Lifting.BlockMotive.LevelEquiv {k : Nat} {Γ' Γ : Scope}
    (b₁ b₂ : Lifting.BlockMotive k Γ' Γ) : Prop where
  /-- The instances are equal up to their levels. -/
  type : Term.LevelEquiv b₁.type b₂.type
  /-- The motives are equal up to their levels. -/
  motive : Term.LevelEquiv b₁.motive b₂.motive
  /-- The levels are equal. -/
  level : b₁.level ≈ b₂.level

/-- Two liftings equal up to their levels: the same renaming, the same variables lifted, with the
same motives at equal levels, and the same types of a block, with motives equal up to their
levels. -/
structure Lifting.LevelEquiv {k : Nat} {Γ' Γ : Scope} (ρ₁ ρ₂ : Lifting k Γ' Γ) : Prop where
  /-- The renamings are equal. -/
  ren : @Lifting.ren k Γ' Γ ρ₁ = @Lifting.ren k Γ' Γ ρ₂
  /-- A variable is lifted by both or by none, with the same motive at equal levels. -/
  motive : ∀ {e : Scope.Entry} (x : Var Γ e),
    (ρ₁.motive x = none ∧ ρ₂.motive x = none) ∨
      ∃ y l₁ l₂, ρ₁.motive x = some (y, l₁) ∧ ρ₂.motive x = some (y, l₂) ∧ l₁ ≈ l₂
  /-- A type is lifted by both or by none, with motives equal up to their levels. -/
  block : ∀ D : Name,
    (ρ₁.block D = none ∧ ρ₂.block D = none) ∨
      ∃ b₁ b₂, ρ₁.block D = some b₁ ∧ ρ₂.block D = some b₂ ∧ b₁.LevelEquiv b₂

namespace Lifting.LevelEquiv

variable {k : Nat} {Γ' Γ : Scope} {ρ₁ ρ₂ : Lifting k Γ' Γ}

/-- Two liftings equal up to their levels stay so under a new entry of both scopes. -/
theorem lift {e : Scope.Entry} (h : Lifting.LevelEquiv ρ₁ ρ₂) :
    Lifting.LevelEquiv (ρ₁.lift (e := e)) ρ₂.lift where
  ren := by
    funext a x
    show Ren.lift ρ₁.ren x = Ren.lift ρ₂.ren x
    rw [h.ren]
  motive := fun x => by
    cases x with
    | zero => exact .inl ⟨rfl, rfl⟩
    | succ x =>
      rcases h.motive x with ⟨h₁, h₂⟩ | ⟨y, l₁, l₂, h₁, h₂, hl⟩
      · exact .inl ⟨by show (ρ₁.motive x).map _ = none; rw [h₁]; rfl,
          by show (ρ₂.motive x).map _ = none; rw [h₂]; rfl⟩
      · exact .inr ⟨.succ y, l₁, l₂, by show (ρ₁.motive x).map _ = _; rw [h₁]; rfl,
          by show (ρ₂.motive x).map _ = _; rw [h₂]; rfl, hl⟩
  block := fun D => by
    rcases h.block D with ⟨h₁, h₂⟩ | ⟨b₁, b₂, h₁, h₂, hb⟩
    · exact .inl ⟨by show (ρ₁.block D).map _ = none; rw [h₁]; rfl,
        by show (ρ₂.block D).map _ = none; rw [h₂]; rfl⟩
    · exact .inr ⟨b₁.lift, b₂.lift, by show (ρ₁.block D).map _ = _; rw [h₁]; rfl,
        by show (ρ₂.block D).map _ = _; rw [h₂]; rfl,
        ⟨hb.type.rename _, hb.motive.rename _, hb.level⟩⟩

/-- Two liftings equal up to their levels stay so in a scope extended by a new entry. -/
theorem weaken {e : Scope.Entry} (h : Lifting.LevelEquiv ρ₁ ρ₂) :
    Lifting.LevelEquiv (ρ₁.weaken (e := e)) ρ₂.weaken where
  ren := by
    funext a x
    show Var.succ (ρ₁.ren x) = Var.succ (ρ₂.ren x)
    rw [h.ren]
  motive := fun x => by
    rcases h.motive x with ⟨h₁, h₂⟩ | ⟨y, l₁, l₂, h₁, h₂, hl⟩
    · exact .inl ⟨by show (ρ₁.motive x).map _ = none; rw [h₁]; rfl,
        by show (ρ₂.motive x).map _ = none; rw [h₂]; rfl⟩
    · exact .inr ⟨.succ y, l₁, l₂, by show (ρ₁.motive x).map _ = _; rw [h₁]; rfl,
        by show (ρ₂.motive x).map _ = _; rw [h₂]; rfl, hl⟩
  block := fun D => by
    rcases h.block D with ⟨h₁, h₂⟩ | ⟨b₁, b₂, h₁, h₂, hb⟩
    · exact .inl ⟨by show (ρ₁.block D).map _ = none; rw [h₁]; rfl,
        by show (ρ₂.block D).map _ = none; rw [h₂]; rfl⟩
    · exact .inr ⟨b₁.weaken, b₂.weaken, by show (ρ₁.block D).map _ = _; rw [h₁]; rfl,
        by show (ρ₂.block D).map _ = _; rw [h₂]; rfl, ⟨hb.type, hb.motive.rename _, hb.level⟩⟩

/-- Two liftings equal up to their levels stay so under new variables. -/
theorem liftN : (n : Nat) → {Γ' Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ' Γ} →
    Lifting.LevelEquiv ρ₁ ρ₂ → Lifting.LevelEquiv (ρ₁.liftN n) (ρ₂.liftN n)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => liftN n h.lift

/-- A lifting equal up to its levels to one that lifts no variable lifts none. -/
theorem motive_eq_none (h : Lifting.LevelEquiv ρ₁ ρ₂)
    (hρ : ∀ {a} (x : Var Γ a), ρ₁.motive x = none) : ∀ {a} (x : Var Γ a), ρ₂.motive x = none :=
  fun x => by
    rcases h.motive x with ⟨_, h₂⟩ | ⟨y, l₁, l₂, h₁, _, _⟩
    · exact h₂
    · exact nomatch (hρ x).symm.trans h₁

/-- Two terms equal up to their levels, renamed under variables by liftings equal up to their
levels, are equal up to their levels. -/
theorem rename_liftN (h : Lifting.LevelEquiv ρ₁ ρ₂) (n : Nat) {B₁ B₂ : Term k (Γ.extend n)}
    (hB : Term.LevelEquiv B₁ B₂) :
    Term.LevelEquiv (B₁.rename (Ren.liftN n ρ₁.ren)) (B₂.rename (Ren.liftN n ρ₂.ren)) := by
  have e : B₂.rename (Ren.liftN n ρ₂.ren) = B₂.rename (Ren.liftN n ρ₁.ren) := by rw [h.ren]
  rw [e]
  exact hB.rename _

/-- The liftings of the scopes of two recursors of instances at equal levels, with arguments and
motives equal up to their levels, in sorts of equal levels, are equal up to their levels. -/
theorem ofMotives {Γ Δ : Scope} (names : List Name) (qs : List Quality)
    {ls₁ ls₂ : List (Level k)} (ps : List Grade) {as₁ as₂ : InstanceArgs k Γ Δ}
    {l₁ l₂ : Level k} {Cs₁ Cs₂ : Motives k Γ} (hls : Level.ListEquiv ls₁ ls₂)
    (has : InstanceArgs.LevelEquiv as₁ as₂) (hl : l₁ ≈ l₂) (hCs : Motives.LevelEquiv Cs₁ Cs₂) :
    Lifting.LevelEquiv (Lifting.ofMotives names qs ls₁ ps as₁ l₁ Cs₁)
      (Lifting.ofMotives names qs ls₂ ps as₂ l₂ Cs₂) where
  ren := rfl
  motive := fun _ => .inl ⟨rfl, rfl⟩
  block := fun D => by
    unfold Lifting.ofMotives
    by_cases hD : D ∈ names
    · simp only [hD, ↓reduceIte]
      rcases hCs.get (names.idxOf D) with ⟨h₁, h₂⟩ | ⟨n, C₁, C₂, h₁, h₂, hC⟩
      · rw [h₁, h₂]
        exact .inl ⟨rfl, rfl⟩
      · rw [h₁, h₂]
        cases n with
        | zero => exact .inr ⟨_, _, rfl, rfl, ⟨.inst _ _ _ hls has, hC, hl⟩⟩
        | succ => exact .inl ⟨rfl, rfl⟩
    · simp only [hD, ↓reduceIte]
      exact .inl ⟨trivial, trivial⟩

end Lifting.LevelEquiv

/-- A lifting that lifts no variable lifts none under new variables. -/
theorem Lifting.liftN_motive_eq_none {k : Nat} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (n : Nat) :
    ∀ {a} (y : Var (Γ.extend n) a), (ρ.liftN n).motive y = none := fun y => by
  cases h : (ρ.liftN n).motive y with
  | none => rfl
  | some p =>
    obtain ⟨x, -, hx⟩ := Lifting.isSome_of_liftN n ρ y (by rw [h]; rfl)
    rw [hρ x] at hx
    exact nomatch hx

/-- A lifting that lifts no variable lifts none in a scope extended by a new entry. -/
theorem Lifting.weaken_motive_eq_none {k : Nat} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry} :
    ∀ {a} (x : Var Γ a), (ρ.weaken (e := e)).motive x = none := fun x => by
  show (ρ.motive x).map _ = none
  rw [hρ x]
  rfl

mutual

/-- A type lifted by a lifting that lifts no variable, at a term, and a type equal to it up to its
levels: the second one is lifted by a lifting equal to the first one up to its levels, at a term
equal up to its levels, to a type equal up to its levels, of an equal level. -/
theorem Term.Lifts.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables} :
    {Γ' Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ' Γ} → {n : Nest Name} → {e₁ e₂ : Term k Γ'} →
      {A₁ A₂ : Term k Γ} → {A₁' : Term k Γ'} → {l₁ : Level k} →
      Term.Lifts sig v ρ₁ n e₁ A₁ A₁' l₁ → Lifting.LevelEquiv ρ₁ ρ₂ →
      (∀ {a} (x : Var Γ a), ρ₁.motive x = none) → Term.LevelEquiv e₁ e₂ →
      Term.LevelEquiv A₁ A₂ →
        ∃ A₂' l₂, Term.Lifts sig v ρ₂ n e₂ A₂ A₂' l₂ ∧ Term.LevelEquiv A₁' A₂' ∧ l₁ ≈ l₂
  | _, _, _, _, _, _, _, _, _, _, _, .var (x := x) hx _, _, hρ₁, _, _ =>
    nomatch (hρ₁ x).symm.trans hx
  | _, _, _, _, _, _, _, _, _, _, _, .block (D := D) hD, hρ, _, he, hA => by
    cases hA with
    | inst _ _ _ _ _ =>
      rcases hρ.block D with ⟨h₁, _⟩ | ⟨b₁, b₂, h₁, h₂, hb⟩
      · exact nomatch h₁.symm.trans hD
      · cases Option.some.inj (h₁.symm.trans hD)
        exact ⟨_, _, .block h₂, hb.motive.subst₀ (Subst₀.LevelEquiv.single he), hb.level⟩
  | _, _, _, _, _, _, _, _, _, _, _, .inst h hD hn hq hl hp has hS hL, hρ, hρ₁, he, hA => by
    cases hA with
    | inst _ _ _ hls hase =>
      obtain ⟨ls₂', as₂', has₂, hls', has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      have hl₂ := hls.length_eq.symm.trans hl
      exact ⟨_, _, .inst h hD hn hq hl₂ hp has₂ hS hL,
        .inst _ _ _ (hls.append hls') (.snoc has' he),
        Level.joins_equiv hls' (Level.subst_equiv (hls.getFin hl hl₂) _)⟩

/-- The arguments of an instance lifted by a lifting that lifts no variable, and arguments equal
to them up to their levels: the second ones are lifted by a lifting equal to the first one up to
its levels, at the same positions, to arguments equal up to their levels, at equal levels. -/
theorem InstanceArgs.Lifts.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables} :
    {Γ' Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as₁ as₂ : InstanceArgs k Γ Δ} → {S : List Nat} → {ls₁ : List (Level k)} → {Δ' : Scope} →
      {as₁' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ₁ ns as₁ S ls₁ as₁' →
      Lifting.LevelEquiv ρ₁ ρ₂ → (∀ {a} (x : Var Γ a), ρ₁.motive x = none) →
      InstanceArgs.LevelEquiv as₁ as₂ →
        ∃ (ls₂ : List (Level k)) (as₂' : InstanceArgs k Γ' Δ'),
          InstanceArgs.Lifts sig v ρ₂ ns as₂ S ls₂ as₂' ∧ Level.ListEquiv ls₁ ls₂ ∧
            InstanceArgs.LevelEquiv as₁' as₂'
  | _, _, _, _, _, _, _, _, _, _, _, _, .nil, _, _, hA => by
    cases hA with
    | nil => exact ⟨[], .nil, .nil, .nil, .nil⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, .lifted (a := a) has hB, hρ, hρ₁, hA => by
    cases hA with
    | snoc hase hBe =>
      obtain ⟨ls₂, as₂', has₂, hls, has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      obtain ⟨B₂', l₂, hB₂, hB', hl⟩ := Term.Lifts.levelEquiv hB (hρ.liftN _).weaken
        (Lifting.weaken_motive_eq_none (Lifting.liftN_motive_eq_none hρ₁ _))
        (Term.LevelEquiv.refl _) hBe
      exact ⟨_, _, .lifted has₂ hB₂, hls.append (.cons hl .nil),
        .snoc (.snoc has' (hρ.rename_liftN _ hBe)) (hB'.cast _)⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, .absent (a := a) has hB hn, hρ, hρ₁, hA => by
    cases hA with
    | snoc hase hBe =>
      obtain ⟨ls₂, as₂', has₂, hls, has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      refine ⟨_, _, .absent has₂ (fun y hy => ?_) hn, hls, .snoc has' (hρ.rename_liftN _ hBe)⟩
      rw [Lifting.liftN_motive_eq_none (hρ.motive_eq_none hρ₁) _ y] at hy
      exact nomatch hy

end

/-- The recursive result of a term, by a lifting that lifts no variable, in a signature whose names
are distinct, and a term equal to it up to its levels: the second one has a recursive result equal
up to its levels, at a type, by a lifting and with results of the types of the block equal up to
their levels. -/
theorem Term.NestedResult.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables}
    (hsig : sig.Distinct) :
    {Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ Γ} → {φ₁ φ₂ : Name → Term k (.var :: Γ)} →
      {n : Nest Name} → {A₁ A₂ t₁ t₂ e₁ : Term k Γ} →
      Term.NestedResult sig v ρ₁ φ₁ n A₁ t₁ e₁ → Lifting.LevelEquiv ρ₁ ρ₂ →
      (∀ {a} (x : Var Γ a), ρ₁.motive x = none) → (∀ E, Term.LevelEquiv (φ₁ E) (φ₂ E)) →
      Term.LevelEquiv A₁ A₂ → Term.LevelEquiv t₁ t₂ →
        ∃ e₂, Term.NestedResult sig v ρ₂ φ₂ n A₂ t₂ e₂ ∧ Term.LevelEquiv e₁ e₂
  | _, _, _, _, _, _, _, _, _, _, _, .block (D := D) hD, hρ, _, hφ, hA, ht => by
    cases hA with
    | inst _ _ _ _ _ =>
      rcases hρ.block D with ⟨h₁, _⟩ | ⟨b₁, b₂, h₁, h₂, hb⟩
      · exact nomatch h₁.symm.trans hD
      · exact ⟨_, .block h₂, (hφ D).subst₀ (Subst₀.LevelEquiv.single ht)⟩
  | Γ, _, ρ₂, _, φ₂, n, _, _, t₁, t₂, _,
      .inst (decl := decl) (T := T) (D := D) (qs := qs) (ls := ls₁) (ps := ps) (as := as₁)
        (ns := ns) (gs := gs₁) h hn hq hl hp has hS hL hgl hgs hgt,
      hρ, hρ₁, hφ, hA, ht => by
    cases hA with
    | @inst _ _ _ _ _ ls₂ _ _ as₂ hls hase =>
      obtain ⟨ls₂', as₂', has₂, hls', has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      have hl₂ := hls.length_eq.symm.trans hl
      have ho : ∀ d ps', Term.LevelEquiv (t₁.observation D qs ls₁ ps as₁ d ps')
          (t₂.observation D qs ls₂ ps as₂ d ps') := fun d ps' =>
        .obs _ _ _ _ hls (hase.rename _) (ht.rename _) (Terms.LevelEquiv.refl _)
      obtain ⟨gs₂, hgse, hQ⟩ := CorecBranches.LevelEquiv.exists_of_forall gs₁
        (fun i b => ∀ d, ns[i]? = some d → ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length)
          (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ)
          (g : Term k (Γ.extend ps₁.length)), b = ⟨0, 0, ps₁.length, g⟩ →
          Term.NestedResult sig v (ρ₂.liftN ps₁.length)
            (fun E => (φ₂ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
            (B.nest (fun _ => none)
              (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs n.args))))
            ((B.substLevels (ls₂.getFin hl₂)).subst
              (Subst.liftN _ (hd.obsSubst (t₂.observation D qs ls₂ ps as₂) as₂.toSubst)))
            (t₂.observation D qs ls₂ ps as₂ d ps₁) g)
        (fun i n' m' a' g₁ hi => by
          rcases hnd : ns[i]? with _ | d
          · exact ⟨g₁, .refl _, fun d h' => nomatch h'⟩
          · obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, g, hg⟩ := hgs i d hnd
            cases Option.some.inj (hi.symm.trans hg)
            obtain ⟨g₂, hres, hgg⟩ := Term.NestedResult.levelEquiv hsig
              (hgt i d p q ς ps₁ Ξ Θ B ψ g hnd hd hg) (hρ.liftN _)
              (Lifting.liftN_motive_eq_none hρ₁ _) (fun E => (hφ E).rename _)
              ((Term.substLevels_levelEquiv (hls.getFin hl hl₂) B).subst
                (Subst.LevelEquiv.liftN _ (hd.obsSubst_levelEquiv ho hase.toSubst)))
              (ho d ps₁)
            refine ⟨g₂, hgg, fun d' hd' => ?_⟩
            cases hd'
            intro p' q' ς' ps₁' Ξ' Θ' B' ψ' hd₂
            exact Destructors.Pos.forall_of (hsig.destructors_nodup h)
              (motive := fun {p q ς ps₁' Ξ Θ B ψ} hd =>
                ∀ g : Term k (Γ.extend ps₁'.length),
                  (⟨0, 0, ps₁.length, g₂⟩ :
                    Σ n m a, Term k (((Γ.extend n).extend m).extend a)) =
                      ⟨0, 0, ps₁'.length, g⟩ →
                  Term.NestedResult sig v (ρ₂.liftN ps₁'.length)
                    (fun E => (φ₂ E).rename (Ren.lift (Ren.weakenN ps₁'.length)))
                    (B.nest (fun _ => none)
                      (Nesting.liftN ps₁'.length (hd.nesting (Nesting.ofArgs n.args))))
                    ((B.substLevels (ls₂.getFin hl₂)).subst
                      (Subst.liftN _
                        (hd.obsSubst (t₂.observation D qs ls₂ ps as₂) as₂.toSubst)))
                    (t₂.observation D qs ls₂ ps as₂ d ps₁') g)
              hd (fun g hg' => by cases hg'; exact hres) hd₂)
      refine ⟨_, .inst h hn hq hl₂ hp has₂ hS hL (hgse.length_eq.symm.trans hgl)
          (fun i d hnd => ?_)
          (fun i d p q ς ps₁ Ξ Θ B ψ g hnd hd hg => hQ i _ hg d hnd p q ς ps₁ Ξ Θ B ψ hd g rfl),
        .corec _ _ _ _ (hls.append hls') (.snoc has' ht) .nil (States.LevelEquiv.refl _) hgse⟩
      obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, g, hg⟩ := hgs i d hnd
      obtain ⟨g₂, hg₂, -⟩ := hgse.get hg
      exact ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hd, g₂, hg₂⟩

/-- The recursive results of the terms of fields, by a lifting that lifts no variable, in a
signature whose names are distinct, and terms equal to them up to their levels: the second ones
have recursive results equal up to their levels, at types, by a lifting and with results of the
types of the block equal up to their levels. -/
theorem Terms.ResultTerms.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables}
    (hsig : sig.Distinct) {Γ : Scope} {ρ₁ ρ₂ : Lifting k Γ Γ}
    {φ₁ φ₂ : Name → Term k (.var :: Γ)} (hρ : Lifting.LevelEquiv ρ₁ ρ₂)
    (hρ₁ : ∀ {a} (x : Var Γ a), ρ₁.motive x = none)
    (hφ : ∀ E, Term.LevelEquiv (φ₁ E) (φ₂ E)) :
    {ns : List (Nest Name)} → {ps : List Parameter} → {As₁ As₂ ts₁ ts₂ : Terms k Γ} →
      {ps' : List Parameter} → {rs₁ : Args k Γ ps'} →
      Terms.ResultTerms sig v ρ₁ φ₁ ns ps As₁ ts₁ rs₁ → Terms.LevelEquiv As₁ As₂ →
      Terms.LevelEquiv ts₁ ts₂ →
        ∃ rs₂ : Args k Γ ps', Terms.ResultTerms sig v ρ₂ φ₂ ns ps As₂ ts₂ rs₂ ∧
          Args.LevelEquiv rs₁ rs₂
  | _, _, _, _, _, _, _, _, .nil, .nil, .nil => ⟨.nil, .nil, .nil⟩
  | _, _, _, _, _, _, _, _, .plain h, .cons _ hAs, .cons _ hts => by
    obtain ⟨rs₂, hr, hrs⟩ := Terms.ResultTerms.levelEquiv hsig hρ hρ₁ hφ h hAs hts
    exact ⟨rs₂, .plain hr, hrs⟩
  | _, _, _, _, _, _, _, _, .recursive (D := D) h, .cons _ hAs, .cons ht hts => by
    obtain ⟨rs₂, hr, hrs⟩ := Terms.ResultTerms.levelEquiv hsig hρ hρ₁ hφ h hAs hts
    exact ⟨.cons _ rs₂, .recursive hr, .cons ((hφ D).subst₀ (Subst₀.LevelEquiv.single ht)) hrs⟩
  | _, _, _, _, _, _, _, _, .nested he h, .cons hA hAs, .cons ht hts => by
    obtain ⟨e₂, he₂, hee⟩ := he.levelEquiv hsig hρ hρ₁ hφ hA ht
    obtain ⟨rs₂, hr, hrs⟩ := Terms.ResultTerms.levelEquiv hsig hρ hρ₁ hφ h hAs hts
    exact ⟨.cons e₂ rs₂, .nested he₂ hr, .cons hee hrs⟩

/-- A term whose levels change for equal ones reduces to the term its reduct becomes so, in a
signature whose names are distinct. -/
theorem Red.levelEquiv {sig : Signature} {k : Nat} {Γ : Scope} {t t' u : Term k Γ}
    (hsig : sig.Distinct) (hr : Red sig t u) (h : Term.LevelEquiv t t') :
    ∃ u', Red sig t' u' ∧ Term.LevelEquiv u u' := by
  induction hr generalizing t' with
  | delta hd hq hl hp =>
    cases h with
    | const _ _ _ hls =>
      have hl' := hls.length_eq.symm.trans hl
      exact ⟨_, .delta hd hq hl' hp,
        (Term.substLevels_levelEquiv (hls.getFin hl hl') _).rename _⟩
  | iota hdecl hi hD hc hq hl hp hu hrs hv =>
    cases h with
    | recursor _ _ _ _ _ _ s hls has ht hκ hCs hus =>
      cases ht with
      | ctor _ _ _ _ _ _ hts =>
        obtain ⟨ts₂, rfl, htse⟩ := Args.exists_of_terms_levelEquiv _ hts
        have hl₂ := hls.length_eq.symm.trans hl
        obtain ⟨u', hu', huu⟩ := hus.get hu
        obtain ⟨rs₂, hrs₂, hrse⟩ := Terms.ResultTerms.levelEquiv hsig
          (Lifting.LevelEquiv.ofMotives _ _ _ hls has hκ hCs) (fun _ => rfl)
          (fun D => .recursor _ _ _ D _ _ s hls (has.rename _) (Term.LevelEquiv.refl _) hκ
            (hCs.rename _) (hus.rename _))
          hrs ((Constructor.fieldsAt_levelEquiv _ _ (hls.getFin hl hl₂) has).typesAt htse)
          htse.terms
        obtain ⟨v', hv', hvv⟩ := huu.instantiateTerms₂ htse.terms hrse.terms hv
        exact ⟨v', .iota hdecl hi hD hc hq hl₂ hp hu' hrs₂ hv', hvv⟩
  | recursor _ ih =>
    cases h with
    | recursor _ _ _ _ _ _ _ hl has ht hκ hCs hus =>
      obtain ⟨u', hr', hu⟩ := ih ht
      exact ⟨_, .recursor hr', .recursor _ _ _ _ _ _ _ hl has hu hκ hCs hus⟩
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
    (hsig : sig.Distinct) (hr : RedStar sig t u) (h : Term.LevelEquiv t t') :
    ∃ u', RedStar sig t' u' ∧ Term.LevelEquiv u u' := by
  induction hr generalizing t' with
  | refl => exact ⟨t', .refl _, h⟩
  | step hr _ ih =>
    obtain ⟨u₁', hr', h₁⟩ := hr.levelEquiv hsig h
    obtain ⟨u', hs', h'⟩ := ih h₁
    exact ⟨u', .step hr' hs', h'⟩

/-- A closed term whose levels change for equal ones computes to the canonical term its canonical
term becomes so. -/
theorem Computes.levelEquiv {sig : Signature} {t t' v : Term 0 []} (hsig : sig.Distinct)
    (hc : Computes sig t v) (h : Term.LevelEquiv t t') :
    ∃ v', Computes sig t' v' ∧ Term.LevelEquiv v v' := by
  obtain ⟨v', hs, hv⟩ := hc.1.levelEquiv hsig h
  exact ⟨v', ⟨hs, hc.2.levelEquiv hv⟩, hv⟩

/-! ## Equality of the Canonical Terms
The relations of the sorts read the levels of the sorts and of the instances by their values, so
that they give the types whose levels change for equal ones, with the same equality of their terms,
which relates the terms whose levels change for equal ones, and with the same relation of run time.
This is proved level by level, as the partial equivalence relations are, by induction on the clauses
that give a type of the level, together with the telescopes of the fields of its constructors, so
that each kind of declaration adds the cases of its clauses. -/

mutual

/-- Two types equal up to their levels have the same nesting, which reads no level. -/
theorem Term.LevelEquiv.nest {k : Nat} {α : Type} (mark : Name → Option α) {Γ : Scope}
    {ν : Nesting α Γ} {t₁ t₂ : Term k Γ} :
    Term.LevelEquiv t₁ t₂ → t₁.nest mark @ν = t₂.nest mark @ν
  | .var _ _ => rfl
  | .sort _ _ => rfl
  | .const _ _ _ _ => rfl
  | .inst D _ _ _ has => by
    simp only [Term.nest]
    rw [InstanceArgs.LevelEquiv.nest mark has]
  | .ctor _ _ _ _ _ _ _ => rfl
  | .recursor _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | .obs _ _ _ _ _ _ _ _ => rfl
  | .corec _ _ _ _ _ _ _ _ _ => rfl

/-- The arguments of two instances equal up to their levels have the same nestings. -/
theorem InstanceArgs.LevelEquiv.nest {k : Nat} {α : Type} (mark : Name → Option α) {Γ Δ : Scope}
    {ν : Nesting α Γ} {as₁ as₂ : InstanceArgs k Γ Δ} :
    InstanceArgs.LevelEquiv as₁ as₂ → as₁.nest mark @ν = as₂.nest mark @ν
  | .nil => rfl
  | .snoc has h => by
    simp only [InstanceArgs.nest]
    rw [Term.LevelEquiv.nest mark h, InstanceArgs.LevelEquiv.nest mark has]

end

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
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : TermRel} :
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
        fun X _ hT c hcm => TelRel.levelEquiv hd ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
          (fun _ => Nest.map_rel₃
            (r := fun (x y _ : NestLeaf) => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2)
            (fun D' => by exact ⟨.inst D' _ _ hls has, rfl⟩) _)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => DesRel.levelEquiv hd ih (hS X _ hT) (Destructors.substLevels_levelEquiv hls' _)
          has.toSubst

/-- `ty(Ω_n)` gives the propositions whose levels change for equal ones. -/
theorem PropRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {b : Prop} :
    PropRel sig ι n (fun m _ => levelRel sig ι m) v b → Term.LevelEquiv v v' →
      PropRel sig ι n (fun m _ => levelRel sig ι m) v' b
  | .data hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .data hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT c hcm => TelRel.levelEquiv hd ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
          (fun _ => Nest.map_rel₃
            (r := fun (x y _ : NestLeaf) => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2)
            (fun D' => by exact ⟨.inst D' _ _ hls has, rfl⟩) _)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => DesRel.levelEquiv hd ih (hS X _ hT) (Destructors.substLevels_levelEquiv hls' _)
          has.toSubst

/-- A telescope whose levels change for equal ones has the same equality of the terms of its
fields, at positions that hold the same relations and types whose levels change for equal ones. -/
theorem TelRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality}
    {rs rs' : Nat → Nest NestLeaf} {ps : List Parameter} {Θ Θ' : Telescope 0 [] ps}
    {S : FieldsRel} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S → Telescope.LevelEquiv Θ Θ' →
      (∀ i, Nest.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) (rs i) (rs' i)) →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ' S
  | .nil, .nil, _ => .nil
  | .cons hA hF G hG hresp hrs, .cons _ _ h hΘ, hR =>
    have ⟨_, hA', hv⟩ := Computes.levelEquiv hd.interpret hA h
    .cons hA' (FieldRel.levelEquiv hd ih hF hv) G
      (fun a ha => TelRel.levelEquiv hd ih (hG a ha)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))
        (fun i => hR (i + 1)))
      hresp ((hR 0).eq_plain.1.2 hrs)
  | .nested hrs hF G hG, .cons _ _ hA hΘ, hR =>
    .nested (fun h => hrs ((hR 0).eq_plain.1.1 h)) (NestRel.levelEquiv hd ih hF hA (hR 0)) G
      fun a => TelRel.levelEquiv hd ih (hG a)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))
        (fun i => hR (i + 1))

/-- A type whose levels change for equal ones has, at a nesting, the same equality of its terms, at
positions that hold the same relations and types whose levels change for equal ones. -/
theorem NestRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {sT s : Quality} {τ τ' : Nest NestLeaf}
    {A A' : Term 0 []} {F : TermRel} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F → Term.LevelEquiv A A' →
      Nest.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) τ τ' →
      NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ' A' F
  | .plain hA hF, h, hτ => by
    cases hτ
    obtain ⟨_, hA', hv⟩ := Computes.levelEquiv hd.interpret hA h
    exact .plain hA' (FieldRel.levelEquiv hd ih hF hv)
  | .direct hs hT, h, hτ => by
    cases hτ with
    | direct hr =>
      obtain ⟨hTT', rfl⟩ := hr
      exact .direct hs ((hTT'.symm.trans hT).trans h)
  | .codata hD hq hl hp hA hs hκ hn hrec S hS, h, hτ => by
    subst hA
    cases hτ with
    | inst hνs =>
      cases h with
      | inst _ _ _ hls has =>
        have hl' := hls.length_eq.symm.trans hl
        have hls' := hls.getFin hl hl'
        exact .codata hD hq hl' hp rfl hs hκ
          ((Level.closedValue_subst_equiv hls' _) ▸ hn) hrec S
          (NestDesRel.levelEquiv hd ih hS (Destructors.substLevels_levelEquiv hls' _) has.toSubst
            (Nesting.ofArgs_rel₃ hνs))
  | .codataProp hD hq hl hp hA hκ hn hrec S hS, h, hτ => by
    subst hA
    cases hτ with
    | inst hνs =>
      cases h with
      | inst _ _ _ hls has =>
        have hl' := hls.length_eq.symm.trans hl
        have hls' := hls.getFin hl hl'
        exact .codataProp hD hq hl' hp rfl hκ
          ((Level.closedValue_subst_equiv hls' _) ▸ hn) hrec S
          (NestDesRel.levelEquiv hd ih hS (Destructors.substLevels_levelEquiv hls' _) has.toSubst
            (Nesting.ofArgs_rel₃ hνs))

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have, at nestings, the same equality of the abstractions for them, at positions that
hold the same relations and types whose levels change for equal ones. -/
theorem NestDesRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {sT s : Quality} {Γ : Scope}
    {ν ν' : Nesting NestLeaf Γ} {ns : List Name} {ds ds' : Destructors 0 Γ ns}
    {θ θ' : Subst 0 [] Γ} {S : ObsRel} :
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν ds @θ S →
      Destructors.LevelEquiv ds ds' → Subst.LevelEquiv θ θ' →
      Nesting.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) @ν @ν' →
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν' ds' @θ' S
  | .nil, .nil, _, _ => .nil
  | .cons (ps := ps) hν hΘ F hF hBresp G hG hresp, .cons (B₂ := B') _ _ _ _ hΘe hBe hds, hθ,
      hνν =>
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hνν) B'
    .cons (hB.eq_plain.1.2 (Term.LevelEquiv.nest _ hBe ▸ hν))
      (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain)) F
      (fun ts hts => NestRel.levelEquiv hd ih (hF ts hts)
        (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _))) .plain)
      hBresp G
      (fun f hf => NestDesRel.levelEquiv hd ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))
        (Nesting.lift_rel₃ hνν))
      hresp
  | .nested (ps := ps) hν hΘ F hF hBresp G hG, .cons (B₂ := B') _ _ _ _ hΘe hBe hds, hθ, hνν =>
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hνν) B'
    .nested (fun h => hν (Term.LevelEquiv.nest _ hBe ▸ hB.eq_plain.1.1 h))
      (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain)) F
      (fun ts hts => NestRel.levelEquiv hd ih (hF ts hts)
        (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        (by rw [Term.LevelEquiv.nest _ hBe]; exact hB))
      hBresp G
      fun f => NestDesRel.levelEquiv hd ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
        (Nesting.lift_rel₃ hνν)

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have the same equality of the abstractions for them. -/
theorem DesRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality} {Γ : Scope}
    {rs : Nat → Option TermRel} {ns : List Name} {ds ds' : Destructors 0 Γ ns} {θ θ' : Subst 0 [] Γ}
    {S : ObsRel} :
    DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S → Destructors.LevelEquiv ds ds' →
      Subst.LevelEquiv θ θ' → DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds' @θ' S
  | .nil, .nil, _ => .nil
  | .recursive hrs hΘ G hG, .cons _ _ _ _ hΘe _ hds, hθ =>
    .recursive hrs (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain)) G
      fun f => DesRel.levelEquiv hd ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
  | .cons hΘ F hB hF hBresp G hG hresp hrs, .cons _ _ _ _ hΘe hBe hds, hθ =>
    .cons (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain)) F
      (fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        have ⟨v', hv', _⟩ :=
          Computes.levelEquiv hd.interpret hv (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        ⟨v', hv'⟩)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hd.interpret hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        FieldRel.levelEquiv hd ih (hF ts hts v hv) hvv.symm)
      hBresp G (fun f hf => DesRel.levelEquiv hd ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))) hresp hrs

/-- The type of a field whose levels change for equal ones has the same equality of its terms. -/
theorem FieldRel.levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {s : Quality} {v v' : Term 0 []}
    {F : TermRel} :
    FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F → Term.LevelEquiv v v' →
      FieldRel sig ι n (fun m _ => levelRel sig ι m) s v' F
  | .univ hs h, hv => .univ hs (UnivRel.levelEquiv hd ih h hv)
  | .univBelow hs m hm h, hv => .univBelow hs m hm ((ih m hm).univ h hv)
  | .prop h, hv => .prop (PropRel.levelEquiv hd ih h hv)
  | .propBelow m hm h, hv => .propBelow m hm ((ih m hm).prop h hv)

end

mutual

/-- `rt(U_n)` gives the types whose levels change for equal ones, with the same relation of run
time. -/
theorem RunUnivRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : RunRel} :
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
          RunTelRel.levelEquiv hd ih (hS X _ hT c hcm) (c.fieldsAt_levelEquiv _ hls' has)
            (fun _ => Nest.map_rel₃
              (r := fun (x y _ : RunNestLeaf) => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2)
              (fun D' => by exact ⟨.inst D' _ _ hls has, rfl⟩) _)
  | .codata hD hq hl hp hv hs hn S hS, h => by
    subst hv
    cases h with
    | inst _ _ _ hls has =>
      have hl' := hls.length_eq.symm.trans hl
      have hls' := hls.getFin hl hl'
      exact .codata hD hq hl' hp rfl hs ((Level.closedValue_subst_equiv hls' _).symm.trans hn) S
        fun X _ hT => RunDesRel.levelEquiv hd ih (hS X _ hT)
          (Destructors.substLevels_levelEquiv hls' _) has.toSubst

/-- A telescope whose levels change for equal ones has the same relation of run time of the terms
of its fields, at positions that hold the same relations and types whose levels change for equal
ones. -/
theorem RunTelRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {rs rs' : Nat → Nest RunNestLeaf}
    {ps : List Parameter} {Θ Θ' : Telescope 0 [] ps} {S : RunFieldsRel} :
    RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs Θ S → Telescope.LevelEquiv Θ Θ' →
      (∀ i, Nest.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) (rs i) (rs' i)) →
      RunTelRel sig ι P n (fun m _ => levelRel sig ι m) rs' Θ' S
  | .nil, .nil, _ => .nil
  | .cons hA hF hR G hG hrs, .cons _ _ h hΘ, hRs =>
    have ⟨_, hA', hv⟩ := Computes.levelEquiv hd.interpret hA h
    .cons hA' (FieldRel.levelEquiv hd ih hF hv) (RunFieldRel.levelEquiv hd ih hR hv) G
      (fun a ha => RunTelRel.levelEquiv hd ih (hG a ha)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))
        (fun i => hRs (i + 1)))
      ((hRs 0).eq_plain.1.2 hrs)
  | .nested hrs hR G hG, .cons _ _ hA hΘ, hRs =>
    .nested (fun h => hrs ((hRs 0).eq_plain.1.1 h)) (RunNestRel.levelEquiv hd ih hR hA (hRs 0)) G
      fun a => RunTelRel.levelEquiv hd ih (hG a)
        (hΘ.subst₀ (Subst₀.LevelEquiv.single (Term.LevelEquiv.refl a)))
        (fun i => hRs (i + 1))

/-- A type whose levels change for equal ones has, at a nesting, the same relation of run time of
its terms, at positions that hold the same relations and types whose levels change for equal
ones. -/
theorem RunNestRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {τ τ' : Nest RunNestLeaf}
    {A A' : Term 0 []} {R : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R → Term.LevelEquiv A A' →
      Nest.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) τ τ' →
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ' A' R
  | .plain hA hR, h, hτ => by
    cases hτ
    obtain ⟨_, hA', hv⟩ := Computes.levelEquiv hd.interpret hA h
    exact .plain hA' (RunFieldRel.levelEquiv hd ih hR hv)
  | .direct hT, h, hτ => by
    cases hτ with
    | direct hr =>
      obtain ⟨hTT', rfl⟩ := hr
      exact .direct ((hTT'.symm.trans hT).trans h)
  | .codata hD hq hl hp hA hκ hn hrec S hS, h, hτ => by
    subst hA
    cases hτ with
    | inst hνs =>
      cases h with
      | inst _ _ _ hls has =>
        have hl' := hls.length_eq.symm.trans hl
        have hls' := hls.getFin hl hl'
        exact .codata hD hq hl' hp rfl hκ
          ((Level.closedValue_subst_equiv hls' _) ▸ hn) hrec S
          (RunNestDesRel.levelEquiv hd ih hS (Destructors.substLevels_levelEquiv hls' _) has.toSubst
            (Nesting.ofArgs_rel₃ hνs))
  | .codataProp hD hq hl hp hA hκ hn, h, hτ => by
    subst hA
    cases hτ with
    | inst hνs =>
      cases h with
      | inst _ _ _ hls has =>
        have hl' := hls.length_eq.symm.trans hl
        have hls' := hls.getFin hl hl'
        exact .codataProp hD hq hl' hp rfl hκ
          ((Level.closedValue_subst_equiv hls' _) ▸ hn)

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have, at nestings, the same relation of run time of the observations by them, at
positions that hold the same relations and types whose levels change for equal ones. -/
theorem RunNestDesRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {D : Name} {Γ : Scope}
    {ν ν' : Nesting RunNestLeaf Γ} {ns : List Name} {ds ds' : Destructors 0 Γ ns}
    {θ θ' : Subst 0 [] Γ} {S : RunObsRel} :
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν ds @θ S →
      Destructors.LevelEquiv ds ds' → Subst.LevelEquiv θ θ' →
      Nesting.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) @ν @ν' →
      RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν' ds' @θ' S
  | .nil, .nil, _, _ => .nil
  | .cons (ps := ps) hi hν hΘ hRΘ F R hF hR G hG, .cons (B₂ := B') _ _ _ _ hΘe hBe hds, hθ,
      hνν =>
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hνν) B'
    .cons hi (hB.eq_plain.1.2 (Term.LevelEquiv.nest _ hBe ▸ hν))
      (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain))
      (RunTelRel.levelEquiv hd ih hRΘ (hΘe.subst hθ) (fun _ => .plain)) F R
      (fun ts hts => NestRel.levelEquiv hd ih (hF ts hts)
        (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _))) .plain)
      (fun ts hts => RunNestRel.levelEquiv hd ih (hR ts hts)
        (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _))) .plain)
      G
      fun f hf => RunNestDesRel.levelEquiv hd ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))
        (Nesting.lift_rel₃ hνν)
  | .nested (ps := ps) hi hν hΘ hRΘ R hR G hG, .cons (B₂ := B') _ _ _ _ hΘe hBe hds, hθ, hνν =>
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hνν) B'
    .nested hi (fun h => hν (Term.LevelEquiv.nest _ hBe ▸ hB.eq_plain.1.1 h))
      (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain))
      (RunTelRel.levelEquiv hd ih hRΘ (hΘe.subst hθ) (fun _ => .plain)) R
      (fun ts hts => RunNestRel.levelEquiv hd ih (hR ts hts)
        (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        (by rw [Term.LevelEquiv.nest _ hBe]; exact hB))
      G
      fun f => RunNestDesRel.levelEquiv hd ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
        (Nesting.lift_rel₃ hνν)

/-- Destructors whose levels change for equal ones, at a closed substitution whose levels change for
equal ones, have the same relation of run time of the observations by them. -/
theorem RunDesRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {D : Name} {Γ : Scope}
    {rs : Nat → Option RunRel} {ns : List Name} {ds ds' : Destructors 0 Γ ns} {θ θ' : Subst 0 [] Γ}
    {S : RunObsRel} :
    RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs ds @θ S →
      Destructors.LevelEquiv ds ds' → Subst.LevelEquiv θ θ' →
        RunDesRel sig ι P n (fun m _ => levelRel sig ι m) D rs ds' @θ' S
  | .nil, .nil, _ => .nil
  | .recursive hi hrs hRΘ G hG, .cons _ _ _ _ hΘe _ hds, hθ =>
    .recursive hi hrs
      (RunTelRel.levelEquiv hd ih hRΘ (hΘe.subst hθ) (fun _ => .plain)) G
      fun f => RunDesRel.levelEquiv hd ih (hG f) hds (hθ.snoc (Term.LevelEquiv.refl f))
  | .cons hi hΘ hRΘ F R hB hF hR G hG hrs, .cons _ _ _ _ hΘe hBe hds, hθ =>
    .cons hi (TelRel.levelEquiv hd ih hΘ (hΘe.subst hθ) (fun _ => .plain))
      (RunTelRel.levelEquiv hd ih hRΘ (hΘe.subst hθ) (fun _ => .plain))
      F R
      (fun ts hts =>
        have ⟨_, hv⟩ := hB ts hts
        have ⟨v', hv', _⟩ :=
          Computes.levelEquiv hd.interpret hv (hBe.subst (Subst.LevelEquiv.append hθ (Subst.LevelEquiv.refl _)))
        ⟨v', hv'⟩)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hd.interpret hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        FieldRel.levelEquiv hd ih (hF ts hts v hv) hvv.symm)
      (fun ts hts _ hv' =>
        have ⟨v, hv, hvv⟩ := Computes.levelEquiv hd.interpret hv'
          (hBe.symm.subst (Subst.LevelEquiv.append (Subst.LevelEquiv.symm hθ)
            (Subst.LevelEquiv.refl _)))
        RunFieldRel.levelEquiv hd ih (hR ts hts v hv) hvv.symm)
      G (fun f hf => RunDesRel.levelEquiv hd ih (hG f hf) hds (hθ.snoc (Term.LevelEquiv.refl f))) hrs

/-- The type of a field whose levels change for equal ones has the same relation of run time of its
terms. -/
theorem RunFieldRel.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant) {v v' : Term 0 []} {R : RunRel} :
    RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v R → Term.LevelEquiv v v' →
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v' R
  | .univ h, hv => .univ (RunUnivRel.levelEquiv hd ih h hv)
  | .univBelow m hm h, hv => .univBelow m hm ((ih m hm).run h hv)
  | .prop h, hv => .prop (PropRel.levelEquiv hd ih h hv)
  | .propBelow m hm h, hv => .propBelow m hm ((ih m hm).prop h hv)

end

/-- The relations of every level give the types whose levels change for equal ones. -/
theorem levelRel_levelInvariant {sig : Signature} {ι : Interpretation} (hd : sig.Distinct)
    (n : Nat) :
    (levelRel sig ι n).LevelInvariant :=
  have ih : ∀ m, m < n → (levelRel sig ι m).LevelInvariant :=
    fun m _ => levelRel_levelInvariant hd m
  { univ := fun h hv => levelRel_univ_iff.2 (UnivRel.levelEquiv hd ih (levelRel_univ_iff.1 h) hv)
    prop := fun h hv => levelRel_prop_iff.2 (PropRel.levelEquiv hd ih (levelRel_prop_iff.1 h) hv)
    run := fun h hv => levelRel_run_iff.2 (RunUnivRel.levelEquiv hd ih (levelRel_run_iff.1 h) hv) }
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
    ⟨⟨R', (levelRel_levelInvariant hd k).univ h₁ ht, (levelRel_levelInvariant hd k).univ h₂ hu⟩, fun P =>
      have ⟨Q, h₁, h₂⟩ := hr P
      ⟨Q, (levelRel_levelInvariant hd k).run h₁ ht, (levelRel_levelInvariant hd k).run h₂ hu⟩⟩
  | .prop (k := k) _ _, ⟨b₁, b₂, h₁, h₂, hb⟩, ht, hu =>
    ⟨b₁, b₂, (levelRel_levelInvariant hd k).prop h₁ ht, (levelRel_levelInvariant hd k).prop h₂ hu, hb⟩
  | .data h _ _ _ _ _ _ S hS, hR, ht, hu => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hmono := fun (X Y : Name → TermRel) (hXY : ∀ D v w, X D v w → Y D v w) =>
      TelRel.block_mono hd hp (Θ := fun c => ⟨_, c.fieldsAt _ _ _⟩)
        (F := fun X D => (.inst D _ _ _ _, (X D).computed sig ι)) hS X Y
        fun D _ _ => TermRel.computed_mono (hXY D)
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
            (fun _ => Nest.map_rel₃
              (r := fun (x y _ : NestLeaf) => ∀ t u t' u', x.2 t u → Term.LevelEquiv t t' →
                Term.LevelEquiv u u' → y.2 t' u')
              (fun D _ _ _ _ h ht hu => by
              obtain ⟨v₁, w₁, hc₁, hc₂, hX⟩ := h
              obtain ⟨v₂, hc₁', hv₂⟩ := Computes.levelEquiv hd.interpret hc₁ ht
              obtain ⟨w₂, hc₂', hw₂⟩ := Computes.levelEquiv hd.interpret hc₂ hu
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
              obtain ⟨v₂, hc₁', hv₂⟩ := Computes.levelEquiv hd.interpret hc₁ ht
              obtain ⟨w₂, hc₂', hw₂⟩ := Computes.levelEquiv hd.interpret hc₂ hu
              exact ⟨v₂, w₂, hc₁', hc₂', v₁, w₁, hX, hv₂, hw₂⟩) _)
            hS' (fun d xs => ?_) (fun d xs => ?_)⟩
        · exact .obs _ _ _ d hl₁ (has₁.rename _) (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl₁ has₁
            ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)
        · exact .obs _ _ _ d hl₂ (has₂.rename _) (Term.LevelEquiv.rename _ (.corec _ _ _ _ hl₂ has₂
            ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)

/-- The equality of the terms of the fields of a telescope relates the terms whose levels change
for equal ones, at positions whose relations do. -/
theorem TelRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {s₁ : Quality}
    {rs₁ : Nat → Nest NestLeaf} {ps : List Parameter} {Θ : Telescope 0 [] ps} {S₁ : FieldsRel}
    {ts us ts' us' : Terms 0 []} :
    TelRel sig ι n (fun m _ => levelRel sig ι m) s₁ rs₁ Θ S₁ →
      ∀ (s₂ : Quality) (rs₂ : Nat → Nest NestLeaf) (S₂ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) s₂ rs₂ Θ S₂ →
        (∀ i, Nest.Rel (fun x y => ∀ t u t' u', x.2 t u → Term.LevelEquiv t t' →
          Term.LevelEquiv u u' → y.2 t' u') (rs₁ i) (rs₂ i)) →
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
    | nested hrs' _ _ _ => exact absurd ((hR 0).eq_plain.1.2 hrs) hrs'
  | .nested hrs hF _ hG, _, _, _, h', hR, h, .cons ht hts, .cons hu hus => by
    cases h' with
    | cons _ _ _ _ _ hrs' => exact absurd ((hR 0).eq_plain.1.1 hrs') hrs
    | nested hrs' hF' _ hG' =>
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨NestRel.rel_levelEquiv hd ih hF _ _ _ hF' (hR 0) h₁ ht hu,
        TelRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _
          (hG' (.sort ⟨.type, .zero⟩)) (fun i => hR (i + 1)) h₂ hts hus⟩
termination_by structural h _ _ _ _ _ _ _ _ => h

/-- The equality that the graph of the nestings gives the terms of a type relates the terms whose
levels change for equal ones, at positions whose relations do. -/
theorem NestRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {sT₁ sT₂ s₁ : Quality}
    {τ₁ : Nest NestLeaf} {A : Term 0 []} {F₁ : TermRel} {t u t' u' : Term 0 []} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT₁ s₁ τ₁ A F₁ →
      ∀ (s₂ : Quality) (τ₂ : Nest NestLeaf) (F₂ : TermRel),
        NestRel sig ι n (fun m _ => levelRel sig ι m) sT₂ s₂ τ₂ A F₂ →
        Nest.Rel (fun x y => ∀ t u t' u', x.2 t u → Term.LevelEquiv t t' →
          Term.LevelEquiv u u' → y.2 t' u') τ₁ τ₂ →
        F₁ t u → Term.LevelEquiv t t' → Term.LevelEquiv u u' → F₂ t' u'
  | .plain hA hF, _, _, _, h', hR, h, ht, hu => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    cases hR
    cases h' with
    | plain hA' hF' =>
      cases Computesι.det hd hA hA'
      exact (FieldRel.unique hd hp hF _ _ hF' _ _).1 (FieldRel.rel_levelEquiv hd ih hF h ht hu)
  | .direct _ _, _, _, _, h', hR, h, ht, hu => by
    cases hR with
    | direct hr =>
      cases h' with
      | direct _ _ => exact hr _ _ _ _ h ht hu
  | .codata hD _ _ _ hA _ hκ _ _ _ hS, _, _, _, h', hR, h, ht, hu => by
    cases hR with
    | inst hνs =>
      cases h' with
      | codata hD' _ _ _ hA' _ _ _ _ _ hS' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        cases hT
        cases has
        obtain ⟨v₁, w₁, hc₁, hc₂, o₁, o₂, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
          ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩, hoo⟩ := h
        obtain ⟨v₂, hc₁', hv₂⟩ := Computes.levelEquiv hd.interpret hc₁ ht
        obtain ⟨w₂, hc₂', hw₂⟩ := Computes.levelEquiv hd.interpret hc₂ hu
        cases hv₂ with
        | corec _ _ _ _ hl₁ has₁ _ _ _ =>
          cases hw₂ with
          | corec _ _ _ _ hl₂ has₂ _ _ _ =>
            refine ⟨_, _, hc₁', hc₂', _, _, ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
              ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩,
              NestDesRel.rel_levelEquiv hd ih hS _ _ _ hS' (Nesting.ofArgs_rel₃ hνs) hoo
                (fun d xs => ?_) (fun d xs => ?_)⟩
            · exact .obs _ _ _ d hl₁ (has₁.rename _) (Term.LevelEquiv.rename _
                (.corec _ _ _ _ hl₁ has₁ ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)
            · exact .obs _ _ _ d hl₂ (has₂.rename _) (Term.LevelEquiv.rename _
                (.corec _ _ _ _ hl₂ has₂ ‹_› ‹_› ‹_›)) (Terms.LevelEquiv.refl _)
      | codataProp hD' _ _ _ hA' hκ' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        exact nomatch hκ.symm.trans hκ'
  | .codataProp hD _ _ _ hA hκ _ _ _ hS, _, _, _, h', hR, h, ht, hu => by
    cases hR with
    | inst hνs =>
      cases h' with
      | codata hD' _ _ _ hA' _ hκ' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        exact nomatch hκ.symm.trans hκ'
      | codataProp hD' _ _ _ hA' _ _ _ _ hS' =>
        subst hA
        obtain ⟨-, hDD, hqs, hls, hps, has⟩ := Term.inst.inj hA'
        subst hDD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique hD hD'
        cases hT
        cases has
        obtain ⟨o, ho⟩ := h
        exact ⟨o, NestDesRel.rel_levelEquiv hd ih hS _ _ _ hS' (Nesting.ofArgs_rel₃ hνs) ho
          (fun _ _ => Term.LevelEquiv.refl _) (fun _ _ => Term.LevelEquiv.refl _)⟩
termination_by structural h _ _ _ _ _ _ _ _ => h

/-- The equality of the abstractions for destructors read at nestings relates the observations whose
levels change for equal ones, at positions whose relations do. -/
theorem NestDesRel.rel_levelEquiv {sig : Signature} {ι : Interpretation} {n : Nat}
    (hd : sig.Distinct) (ih : ∀ m, m < n → (levelRel sig ι m).RelInvariant) {sT₁ sT₂ s₁ : Quality}
    {Γ : Scope} {ν₁ : Nesting NestLeaf Γ} {ns : List Name} {ds : Destructors 0 Γ ns}
    {θ : Subst 0 [] Γ} {S₁ : ObsRel} {o₁ o₂ o₁' o₂' : Observations} :
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT₁ s₁ @ν₁ ds @θ S₁ →
      ∀ (s₂ : Quality) (ν₂ : Nesting NestLeaf Γ) (S₂ : ObsRel),
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT₂ s₂ @ν₂ ds @θ S₂ →
        Nesting.Rel (fun x y => ∀ t u t' u', x.2 t u → Term.LevelEquiv t t' →
          Term.LevelEquiv u u' → y.2 t' u') @ν₁ @ν₂ →
        S₁ o₁ o₂ → (∀ d ps, Term.LevelEquiv (o₁ d ps) (o₁' d ps)) →
        (∀ d ps, Term.LevelEquiv (o₂ d ps) (o₂' d ps)) → S₂ o₁' o₂'
  | .nil, _, _, _, h', _, _, _, _ => by cases h'; trivial
  | .cons (d := d) (ps := ps) (B := B) (SΘ := SΘ) hν hΘ F hF hBresp _ hG _, _, _, _, h', hR,
      ⟨h₁, h₂⟩, e₁, e₂ => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd hp (fun _ => .plain) hΘ
    have hEp := AbstractionRel.isPer hSp
      (fun ts hts => NestRel.isPer hd hp .plain (hF ts hts)) hBresp
    have hE : ∀ f₁ f₂ f₁' f₂', AbstractionRel (ps := ps) SΘ F f₁ f₂ → Term.LevelEquiv f₁ f₁' →
        Term.LevelEquiv f₂ f₂' → AbstractionRel (ps := ps) SΘ F f₁' f₂' :=
      fun _ _ _ _ h ef₁ ef₂ ts us hts =>
        have htt := hSp.trans hts (hSp.symm hts)
        NestRel.rel_levelEquiv hd ih (hF ts htt) _ _ _ (hF ts htt) .plain (h ts us hts)
          (ef₁.subst (Subst.LevelEquiv.refl _)) (ef₂.subst (Subst.LevelEquiv.refl _))
    have hff := hEp.trans h₁ (hEp.symm h₁)
    have hff' := hE _ _ _ _ hff (Term.LevelEquiv.refl _) (e₁ d ps)
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hR) B
    cases h' with
    | cons _ hΘ' F' hF' _ _ hG' hresp' =>
      have hSS := TelRel.unique hd hp hΘ _ _ hΘ'
      have hFF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ t u,
          F ts.terms t u ↔ F' ts.terms t u := fun ts hts =>
        NestRel.unique hd hp (hF ts hts) _ _ (hF' ts ((hSS _ _).1 hts))
      have hEE := AbstractionRel.congr hSp hSS hFF
      exact ⟨(hEE _ _).1 (hE _ _ _ _ h₁ (e₁ d ps) (e₂ d ps)),
        (hresp' _ _ ((hEE _ _).1 hff') _ _).1
          (NestDesRel.rel_levelEquiv hd ih (hG _ hff) _ _ _ (hG' _ ((hEE _ _).1 hff))
            (Nesting.lift_rel₃ hR) h₂ e₁ e₂)⟩
    | nested hν' => exact absurd (hB.eq_plain.1.2 hν) hν'
  | .nested (d := d) (ps := ps) (B := B) (SΘ := SΘ) hν hΘ F hF _ _ hG, _, _, _, h', hR,
      ⟨h₁, h₂⟩, e₁, e₂ => by
    have hp : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd hp (fun _ => .plain) hΘ
    have hB := Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hR) B
    cases h' with
    | cons hν' => exact absurd (hB.eq_plain.1.1 hν') hν
    | nested _ hΘ' F' hF' _ _ hG' =>
      have hSS := TelRel.unique hd hp hΘ _ _ hΘ'
      exact ⟨fun ts us hts =>
          have hts' := (hSS _ _).2 hts
          have htt := hSp.trans hts' (hSp.symm hts')
          NestRel.rel_levelEquiv hd ih (hF ts htt) _ _ _ (hF' ts ((hSS _ _).1 htt)) hB
            (h₁ ts us hts') ((e₁ d ps).subst (Subst.LevelEquiv.refl _))
            ((e₂ d ps).subst (Subst.LevelEquiv.refl _)),
        NestDesRel.rel_levelEquiv hd ih (hG (.sort ⟨.type, .zero⟩)) _ _ _
          (hG' (.sort ⟨.type, .zero⟩)) (Nesting.lift_rel₃ hR) h₂ e₁ e₂⟩
termination_by structural h _ _ _ _ _ _ _ _ => h

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
    have hSp := TelRel.isPer hd hp (fun _ => .plain) hΘ
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
    have ⟨_, hct', hv⟩ := Computes.levelEquiv hd.interpret hct ht
    have ⟨_, hcu', hw⟩ := Computes.levelEquiv hd.interpret hcu hu
    ⟨_, _, hct', hcu', UnivRel.rel_levelEquiv hd ih h hvw hv hw⟩
  | .univBelow _ m hm h, ⟨_, _, hct, hcu, hvw⟩, ht, hu =>
    have ⟨_, hct', hv⟩ := Computes.levelEquiv hd.interpret hct ht
    have ⟨_, hcu', hw⟩ := Computes.levelEquiv hd.interpret hcu hu
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

/-- A canonical type whose levels change for equal ones has the same equality of its terms, in a
signature whose names are distinct. -/
theorem HasEq.levelEquiv {sig : Signature} {ι : Interpretation} {v v' : Term 0 []} {R : TermRel}
    (hd : sig.Distinct) (hA : HasEq sig ι v R) (h : Term.LevelEquiv v v') : HasEq sig ι v' R :=
  match hA with
  | .univ n hn => .univ n ((levelRel_levelInvariant hd n).univ hn h)
  | .prop n b hn hR => .prop n b ((levelRel_levelInvariant hd n).prop hn h) hR

/-- A canonical type whose levels change for equal ones has the same relation of run time, in a
signature whose names are distinct. -/
theorem HasRun.levelEquiv {sig : Signature} {ι : Interpretation} {P : Program} {v v' : Term 0 []}
    {R : RunRel} (hd : sig.Distinct) (hA : HasRun sig ι P v R) (h : Term.LevelEquiv v v') :
    HasRun sig ι P v' R :=
  match hA with
  | .univ n hn => .univ n ((levelRel_levelInvariant hd n).run hn h)
  | .prop n b hn hR => .prop n b ((levelRel_levelInvariant hd n).prop hn h) hR

/-- The equality of the terms of a canonical type relates the terms whose levels change for equal
ones, in a signature whose names are distinct. -/
theorem HasEq.rel_levelEquiv {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R : TermRel}
    {t u t' u' : Term 0 []} (hd : sig.Distinct) (hA : HasEq sig ι v R) (htu : R t u)
    (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u') : R t' u' :=
  match hA with
  | .univ n hn => levelRel_relInvariant hd n hn htu ht hu
  | .prop _ _ _ hR => (hR t' u').2 ((hR t u).1 htu)

/-- A proposition whose levels change for equal ones stays a proposition, in a signature whose
names are distinct. -/
theorem IsProp.levelEquiv {sig : Signature} {ι : Interpretation} {v v' : Term 0 []}
    (hd : sig.Distinct) (hA : IsProp sig ι v) (h : Term.LevelEquiv v v') : IsProp sig ι v' :=
  let ⟨n, b, hn⟩ := hA
  ⟨n, b, (levelRel_levelInvariant hd n).prop hn h⟩

/-! ## Closed Judgments
No closed judgment tells apart two terms whose levels change for equal ones. -/

/-- A closed type that computes to a proposition still does when its levels change for equal
ones, in a signature whose names are distinct. -/
theorem ComputesToProp.levelEquiv {sig : Signature} {ι : Interpretation} {A A' : Term 0 []}
    (hd : sig.Distinct) (hA : ComputesToProp sig ι A) (h : Term.LevelEquiv A A') :
    ComputesToProp sig ι A' :=
  let ⟨_, hc, hp⟩ := hA
  let ⟨_, hc', h₀⟩ := hc.levelEquiv hd.interpret h
  ⟨_, hc', hp.levelEquiv hd h₀⟩

/-- The clause of `(⊨_type≡)` still holds when the levels of the types change for equal ones, in a
signature whose names are distinct. -/
theorem EqTypeClause.levelEquiv {sig : Signature} {ι : Interpretation} {A B A' B' : Term 0 []}
    (hd : sig.Distinct) (hAB : EqTypeClause sig ι A B) (hA : Term.LevelEquiv A A')
    (hB : Term.LevelEquiv B B') : EqTypeClause sig ι A' B' :=
  let ⟨_, _, R, hcA, hcB, hRA, hRB, hr⟩ := hAB
  let ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hd.interpret hA
  let ⟨_, hcB', hB₀⟩ := hcB.levelEquiv hd.interpret hB
  ⟨_, _, R, hcA', hcB', hRA.levelEquiv hd hA₀, hRB.levelEquiv hd hB₀, fun P Q =>
    ⟨fun h => ((hr P Q).1 (h.levelEquiv hd hA₀.symm)).levelEquiv hd hB₀,
      fun h => ((hr P Q).2 (h.levelEquiv hd hB₀.symm)).levelEquiv hd hA₀⟩⟩

/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` still hold when the levels of the terms and of the type
change for equal ones, in a signature whose names are distinct. -/
theorem EqTermClause.levelEquiv {sig : Signature} {ι : Interpretation} {t u A t' u' A' : Term 0 []}
    (hd : sig.Distinct) (htu : EqTermClause sig ι t u A) (ht : Term.LevelEquiv t t') (hu : Term.LevelEquiv u u')
    (hA : Term.LevelEquiv A A') : EqTermClause sig ι t' u' A' := by
  refine ⟨fun hP' => ?_, fun hP' => ?_⟩
  · obtain ⟨_, _, _, R, hcA, hct, hcu, hR, hvw⟩ :=
      htu.1 fun hP => hP' (hP.levelEquiv hd hA)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hd.interpret hA
    obtain ⟨_, hct', hv⟩ := hct.levelEquiv hd.interpret ht
    obtain ⟨_, hcu', hw⟩ := hcu.levelEquiv hd.interpret hu
    exact ⟨_, _, _, R, hcA', hct', hcu', hR.levelEquiv hd hA₀, hR.rel_levelEquiv hd hvw hv hw⟩
  · obtain ⟨_, R, hcA, hR, htu'⟩ := htu.2 (hP'.levelEquiv hd hA.symm)
    obtain ⟨_, hcA', hA₀⟩ := hcA.levelEquiv hd.interpret hA
    exact ⟨_, R, hcA', hR.levelEquiv hd hA₀, hR.rel_levelEquiv hd htu' ht hu⟩

/-- `(⊨_type≡)` still holds when the levels of the types change for equal ones. -/
theorem ValidEqType₀.levelEquiv {sig : Signature} {ι : Interpretation} {A B A' B' : Term 0 []}
    (hAB : ValidEqType₀ sig ι A B) (hA : Term.LevelEquiv A A') (hB : Term.LevelEquiv B B') :
    ValidEqType₀ sig ι A' B' :=
  ⟨hAB.1, hAB.2.levelEquiv hAB.1 hA hB⟩

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
