module

public import Sic.Core.Meaning.Interpretation
public import Sic.Core.Substitution.Closed
public import Sic.Core.Syntax.LevelEquiv

/-!
# Terms Equal up to Their Levels Under the Substitutions

Two terms that differ only by levels of the same values stay so when their variables are renamed,
when their level variables are instantiated by equal levels, and when a substitution gives each
variable terms equal up to their levels.
The reduction substitutes the terms that it copies, and the fields of an instance are the fields of
its declaration at its levels and its arguments: both keep two terms equal up to their levels by
these properties.

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
  | .equality s hl hA ht hu => .equality s hl (hA.rename α) (ht.rename α) (hu.rename α)
  | .reflProof s hl hA ht => .reflProof s hl (hA.rename α) (ht.rename α)
  | .transp hA ht hu hC he hv =>
    .transp (hA.rename α) (ht.rename α) (hu.rename α) (hC.rename (Ren.liftN 1 α))
      (he.rename α) (hv.rename α)
  | .propExt hl hP hQ hf hg =>
    .propExt hl (hP.rename α) (hQ.rename α) (hf.rename (Ren.liftN 1 α))
      (hg.rename (Ren.liftN 1 α))

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
  | .equality s l A t u =>
    .equality s (Level.subst_equiv h l) (Term.substLevels_levelEquiv h A)
      (Term.substLevels_levelEquiv h t) (Term.substLevels_levelEquiv h u)
  | .refl s l A t =>
    .reflProof s (Level.subst_equiv h l) (Term.substLevels_levelEquiv h A)
      (Term.substLevels_levelEquiv h t)
  | .transp A t u C e v =>
    .transp (Term.substLevels_levelEquiv h A) (Term.substLevels_levelEquiv h t)
      (Term.substLevels_levelEquiv h u) (Term.substLevels_levelEquiv h C)
      (Term.substLevels_levelEquiv h e) (Term.substLevels_levelEquiv h v)
  | .propExt l P Q f g =>
    .propExt (Level.subst_equiv h l) (Term.substLevels_levelEquiv h P)
      (Term.substLevels_levelEquiv h Q) (Term.substLevels_levelEquiv h f)
      (Term.substLevels_levelEquiv h g)

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
  | .equality s hl hA ht hu => .equality s hl (hA.subst₀ hσ) (ht.subst₀ hσ) (hu.subst₀ hσ)
  | .reflProof s hl hA ht => .reflProof s hl (hA.subst₀ hσ) (ht.subst₀ hσ)
  | .transp hA ht hu hC he hv =>
    .transp (hA.subst₀ hσ) (ht.subst₀ hσ) (hu.subst₀ hσ) (hC.subst₀ (Subst₀.LevelEquiv.liftN _ hσ))
      (he.subst₀ hσ) (hv.subst₀ hσ)
  | .propExt hl hP hQ hf hg =>
    .propExt hl (hP.subst₀ hσ) (hQ.subst₀ hσ) (hf.subst₀ (Subst₀.LevelEquiv.liftN _ hσ))
      (hg.subst₀ (Subst₀.LevelEquiv.liftN _ hσ))

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
  | .equality s hl hA ht hu => .equality s hl (hA.subst hθ) (ht.subst hθ) (hu.subst hθ)
  | .reflProof s hl hA ht => .reflProof s hl (hA.subst hθ) (ht.subst hθ)
  | .transp hA ht hu hC he hv =>
    .transp (hA.subst hθ) (ht.subst hθ) (hu.subst hθ) (hC.subst (Subst.LevelEquiv.liftN _ hθ))
      (he.subst hθ) (hv.subst hθ)
  | .propExt hl hP hQ hf hg =>
    .propExt hl (hP.subst hθ) (hQ.subst hθ) (hf.subst (Subst.LevelEquiv.liftN _ hθ))
      (hg.subst (Subst.LevelEquiv.liftN _ hθ))

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
end Sic.Core
