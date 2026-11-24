module

public import Sic.Core.Meaning.Levels.Substitution
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Substitution
import Sic.Core.Syntax.Signature

/-!
# Recursive Results Equal up to Their Levels

The reduction of a recursor builds the results of the nested fields from the types of the fields,
by the liftings of their instances: the levels of these results are those of the types, of the
motives and of the instance of the recursor, so that the results of terms, at types, motives and
an instance equal up to their levels, are equal up to their levels.
The result of a nested field reads each destructor of its type by its name, which names one
destructor in a signature whose names are distinct.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

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

/-- Branches of the destructors equal up to their levels have, at a position, branches equal up to
their levels. -/
theorem DestructorBranches.LevelEquiv.get {k : Nat} {Γ : Scope} :
    {vs₁ vs₂ : DestructorBranches k Γ} → DestructorBranches.LevelEquiv vs₁ vs₂ → {i n m a : Nat} →
      {v₁ : Term k (((Γ.extend n).extend m).extend a)} → vs₁.get i = some ⟨n, m, a, v₁⟩ →
        ∃ v₂, vs₂.get i = some ⟨n, m, a, v₂⟩ ∧ Term.LevelEquiv v₁ v₂
  | _, _, .nil, _, _, _, _, _, he => nomatch he
  | _, _, .cons h _, 0, _, _, _, _, he => by
    cases he
    exact ⟨_, rfl, h⟩
  | _, _, .cons _ hs, _ + 1, _, _, _, _, he => hs.get he

/-- Branches of the destructors equal up to their levels are as many. -/
theorem DestructorBranches.LevelEquiv.length_eq {k : Nat} {Γ : Scope} :
    {gs₁ gs₂ : DestructorBranches k Γ} →
    DestructorBranches.LevelEquiv gs₁ gs₂ → gs₁.length = gs₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg (· + 1) hs.length_eq

/-- Branches of the destructors, each of which is equal up to its levels to a branch that has a
property of its position, are equal up to their levels to branches that have this property. -/
theorem DestructorBranches.LevelEquiv.exists_of_forall {k : Nat} {Γ : Scope} :
    (gs₁ : DestructorBranches k Γ) →
      (Q : Nat → (Σ n m a, Term k (((Γ.extend n).extend m).extend a)) → Prop) →
      (∀ i n m a (g₁ : Term k (((Γ.extend n).extend m).extend a)),
        gs₁.get i = some ⟨n, m, a, g₁⟩ → ∃ g₂, Term.LevelEquiv g₁ g₂ ∧ Q i ⟨n, m, a, g₂⟩) →
      ∃ gs₂, DestructorBranches.LevelEquiv gs₁ gs₂ ∧ ∀ i b, gs₂.get i = some b → Q i b
  | .nil, _, _ => ⟨.nil, .nil, fun _ _ h => nomatch h⟩
  | .cons n m a g gs, Q, h => by
    obtain ⟨g₂, hg, hq⟩ := h 0 n m a g rfl
    obtain ⟨gs₂, hgs, hqs⟩ := DestructorBranches.LevelEquiv.exists_of_forall gs (fun i => Q (i + 1))
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

/-- What two types lifted give the results, equal up to their levels: equal levels, the same factor
and the same ownership. -/
structure Lifting.Result.LevelEquiv {k : Nat} (m₁ m₂ : Lifting.Result k) : Prop where
  /-- The levels are equal. -/
  level : m₁.level ≈ m₂.level
  /-- The factors are the same. -/
  factor : m₁.factor = m₂.factor
  /-- The ownerships are the same. -/
  ownership : m₁.ownership = m₂.ownership

/-- Lists of what types lifted give the results, equal one by one up to their levels. -/
inductive Lifting.Result.ListEquiv {k : Nat} :
    List (Lifting.Result k) → List (Lifting.Result k) → Prop where
  /-- No result. -/
  | nil : ListEquiv [] []
  /-- Two results equal up to their levels, then equal lists. -/
  | cons {m₁ m₂ : Lifting.Result k} {ms₁ ms₂ : List (Lifting.Result k)} (h : m₁.LevelEquiv m₂)
      (hs : ListEquiv ms₁ ms₂) : ListEquiv (m₁ :: ms₁) (m₂ :: ms₂)

/-- The levels of results equal up to their levels are equal. -/
theorem Lifting.Result.ListEquiv.levels {k : Nat} : {ms₁ ms₂ : List (Lifting.Result k)} →
    Lifting.Result.ListEquiv ms₁ ms₂ → Level.ListEquiv (ms₁.map (·.level)) (ms₂.map (·.level))
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.level hs.levels

/-- The grades of results equal up to their levels are the same. -/
theorem Lifting.Result.ListEquiv.grades {k : Nat} : {ms₁ ms₂ : List (Lifting.Result k)} →
    Lifting.Result.ListEquiv ms₁ ms₂ → Lifting.Result.grades ms₁ = Lifting.Result.grades ms₂
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    have ih := hs.grades
    simp only [Lifting.Result.grades, List.flatMap_cons] at ih ⊢
    rw [h.factor, h.ownership, ih]

/-- Lists of results equal up to their levels, followed by such lists, are such lists. -/
theorem Lifting.Result.ListEquiv.append {k : Nat} : {ms₁ ms₂ ms₁' ms₂' : List (Lifting.Result k)} →
    Lifting.Result.ListEquiv ms₁ ms₂ → Lifting.Result.ListEquiv ms₁' ms₂' →
      Lifting.Result.ListEquiv (ms₁ ++ ms₁') (ms₂ ++ ms₂')
  | _, _, _, _, .nil, h' => h'
  | _, _, _, _, .cons h hs, h' => .cons h (hs.append h')

/-- Two motives of a type of a block equal up to their levels: instances and motives equal up to
their levels, at equal levels, of the same ownership. -/
structure Lifting.BlockMotive.LevelEquiv {k : Nat} {Γ' Γ : Scope}
    (b₁ b₂ : Lifting.BlockMotive k Γ' Γ) : Prop where
  /-- The instances are equal up to their levels. -/
  type : Term.LevelEquiv b₁.type b₂.type
  /-- The motives are equal up to their levels. -/
  motive : Term.LevelEquiv b₁.motive b₂.motive
  /-- The levels are equal. -/
  level : b₁.level ≈ b₂.level
  /-- The ownerships are the same. -/
  ownership : b₁.ownership = b₂.ownership

/-- Two liftings equal up to their levels: the same renaming, the same variables lifted, with the
same motives at equal levels, and the same types of a block, with motives equal up to their
levels. -/
structure Lifting.LevelEquiv {k : Nat} {Γ' Γ : Scope} (ρ₁ ρ₂ : Lifting k Γ' Γ) : Prop where
  /-- The renamings are equal. -/
  ren : @Lifting.ren k Γ' Γ ρ₁ = @Lifting.ren k Γ' Γ ρ₂
  /-- A variable is lifted by both or by none, with the same motive at equal levels. -/
  motive : ∀ {e : Scope.Entry} (x : Var Γ e),
    (ρ₁.motive x = none ∧ ρ₂.motive x = none) ∨
      ∃ y m₁ m₂, ρ₁.motive x = some (y, m₁) ∧ ρ₂.motive x = some (y, m₂) ∧ m₁.LevelEquiv m₂
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
        ⟨hb.type.rename _, hb.motive.rename _, hb.level, hb.ownership⟩⟩

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
        by show (ρ₂.block D).map _ = _; rw [h₂]; rfl, ⟨hb.type, hb.motive.rename _, hb.level,
          hb.ownership⟩⟩

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
    {l₁ l₂ : Level k} (χ : Grade) {Cs₁ Cs₂ : Motives k Γ} (hls : Level.ListEquiv ls₁ ls₂)
    (has : InstanceArgs.LevelEquiv as₁ as₂) (hl : l₁ ≈ l₂) (hCs : Motives.LevelEquiv Cs₁ Cs₂) :
    Lifting.LevelEquiv (Lifting.ofMotives names qs ls₁ ps as₁ l₁ χ Cs₁)
      (Lifting.ofMotives names qs ls₂ ps as₂ l₂ χ Cs₂) where
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
        | zero => exact .inr ⟨_, _, rfl, rfl, ⟨.inst _ _ _ hls has, hC, hl, rfl⟩⟩
        | succ => exact .inl ⟨rfl, rfl⟩
    · simp only [hD, ↓reduceIte]
      exact .inl ⟨trivial, trivial⟩

end Lifting.LevelEquiv

mutual

/-- A type lifted by a lifting that lifts no variable, at a term, and a type equal to it up to its
levels: the second one is lifted by a lifting equal to the first one up to its levels, at a term
equal up to its levels, to a type equal up to its levels, of a result equal up to its levels. -/
theorem Term.Lifts.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables} :
    {Γ' Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ' Γ} → {n : Nest Name} → {e₁ e₂ : Term k Γ'} →
      {A₁ A₂ : Term k Γ} → {A₁' : Term k Γ'} → {m₁ : Lifting.Result k} →
      Term.Lifts sig v ρ₁ n e₁ A₁ A₁' m₁ → Lifting.LevelEquiv ρ₁ ρ₂ →
      (∀ {a} (x : Var Γ a), ρ₁.motive x = none) → Term.LevelEquiv e₁ e₂ →
      Term.LevelEquiv A₁ A₂ →
        ∃ A₂' m₂, Term.Lifts sig v ρ₂ n e₂ A₂ A₂' m₂ ∧ Term.LevelEquiv A₁' A₂' ∧
          m₁.LevelEquiv m₂
  | _, _, _, _, _, _, _, _, _, _, _, .var (x := x) hx _, _, hρ₁, _, _ =>
    nomatch (hρ₁ x).symm.trans hx
  | _, _, _, _, _, _, _, _, _, _, _, .block (D := D) hD, hρ, _, he, hA => by
    cases hA with
    | inst _ _ _ _ _ =>
      rcases hρ.block D with ⟨h₁, _⟩ | ⟨b₁, b₂, h₁, h₂, hb⟩
      · exact nomatch h₁.symm.trans hD
      · cases Option.some.inj (h₁.symm.trans hD)
        exact ⟨_, _, .block h₂, hb.motive.subst₀ (Subst₀.LevelEquiv.single he),
          ⟨hb.level, rfl, hb.ownership⟩⟩
  | _, _, _, _, _, _, _, _, _, _, _, .inst (ps := ps) (ms := ms₁) h hD hn hqp hl has hS hL hπ, hρ,
      hρ₁, he,
      hA => by
    cases hA with
    | inst _ _ _ hls hase =>
      obtain ⟨ms₂, as₂', has₂, hms, has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      have hl₂ := hls.length_eq.symm.trans hl
      have hg : v.grades ps ms₁ = v.grades ps ms₂ := by
        rw [Lifting.Variables.grades, Lifting.Variables.grades, hms.grades]
      rw [hg] at hπ
      rw [hg]
      exact ⟨_, _, .inst h hD hn hqp hl₂ has₂ hS hL (hπ.inst_congr _ _ _),
        .inst _ _ _ (hls.append hms.levels) (.snoc has' he),
        ⟨Level.joins_equiv hms.levels (Level.subst_equiv (hls.getFin hl hl₂) _), rfl, rfl⟩⟩

/-- The arguments of an instance lifted by a lifting that lifts no variable, and arguments equal
to them up to their levels: the second ones are lifted by a lifting equal to the first one up to
its levels, at the same positions, to arguments equal up to their levels, of results equal up to
their levels. -/
theorem InstanceArgs.Lifts.levelEquiv {sig : Signature} {k : Nat} {v : Lifting.Variables} :
    {Γ' Γ : Scope} → {ρ₁ ρ₂ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as₁ as₂ : InstanceArgs k Γ Δ} → {S : List Nat} → {ms₁ : List (Lifting.Result k)} →
      {Δ' : Scope} → {as₁' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ₁ ns as₁ S ms₁ as₁' →
      Lifting.LevelEquiv ρ₁ ρ₂ → (∀ {a} (x : Var Γ a), ρ₁.motive x = none) →
      InstanceArgs.LevelEquiv as₁ as₂ →
        ∃ (ms₂ : List (Lifting.Result k)) (as₂' : InstanceArgs k Γ' Δ'),
          InstanceArgs.Lifts sig v ρ₂ ns as₂ S ms₂ as₂' ∧ Lifting.Result.ListEquiv ms₁ ms₂ ∧
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
      .inst (decl := decl) (T := T) (D := D) (qs := qs) (ls := ls₁) (ms := ms₁) (ps := ps)
        (as := as₁) (ns := ns) (gs := gs₁) h hn hqp hl has hS hL hgl hgs hgt,
      hρ, hρ₁, hφ, hA, ht => by
    cases hA with
    | @inst _ _ _ _ _ ls₂ _ _ as₂ hls hase =>
      obtain ⟨ms₂, as₂', has₂, hms, has'⟩ := InstanceArgs.Lifts.levelEquiv has hρ hρ₁ hase
      have hl₂ := hls.length_eq.symm.trans hl
      have hg : v.grades ps ms₁ = v.grades ps ms₂ := by
        rw [Lifting.Variables.grades, Lifting.Variables.grades, hms.grades]
      rw [hg]
      have ho : ∀ d ps', Term.LevelEquiv (t₁.observation D qs ls₁ ps as₁ d ps')
          (t₂.observation D qs ls₂ ps as₂ d ps') := fun d ps' =>
        .obs _ _ _ _ hls (hase.rename _) (ht.rename _) (Terms.LevelEquiv.refl _)
      obtain ⟨gs₂, hgse, hQ⟩ := DestructorBranches.LevelEquiv.exists_of_forall gs₁
        (fun i b => ∀ d, ns[i]? = some d → ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length)
          (hd : (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ)
          (g : Term k (Γ.extend ps₁.length)), b = ⟨0, 0, ps₁.length, g⟩ →
          Term.NestedResult sig v (ρ₂.liftN ps₁.length)
            (fun E => (φ₂ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
            (B.nest (fun _ => none)
              (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs n.args))))
            ((B.substLevels (ls₂.getFin hl₂)).subst
              (Subst.liftN _ (hd.obsSubstOf D qs ls₂ ps as₂ t₂)))
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
                        (hd.obsSubstOf D qs ls₂ ps as₂ t₂)))
                    (t₂.observation D qs ls₂ ps as₂ d ps₁') g)
              hd (fun g hg' => by cases hg'; exact hres) hd₂)
      refine ⟨_, .inst h hn hqp hl₂ has₂ hS hL (hgse.length_eq.symm.trans hgl)
          (fun i d hnd => ?_)
          (fun i d p q ς ps₁ Ξ Θ B ψ g hnd hd hg => hQ i _ hg d hnd p q ς ps₁ Ξ Θ B ψ hd g rfl),
        .corec _ _ _ _ (hls.append hms.levels) (.snoc has' ht) .nil (States.LevelEquiv.refl _) hgse⟩
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
end Sic.Core
