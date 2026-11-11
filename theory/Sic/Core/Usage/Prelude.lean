module

public import Sic.Core.Prelude
public import Sic.Core.Usage
import Sic.Core.Usage.Renaming

/-!
# Usage of the Prelude

The usage of the prelude of annex 18 of RFC 36: the constructors of its types use their parameters
as the grades of the types allow, and the packing of arguments, the recursors on the pair, on the
unit and on the type of positions, the unpacking of a term of a packing and the resumption of a
position, which an observation of a recursive destructor computes, use the variables as their rules
show.

The rules of the recursors on the pair, on the unit and on the type of positions are the rules of
the data types at the instances of the prelude, whose premises on the block hold by computation; the
resumption shows what the rules of the corecursors require of the branches of their recursive
destructors.

ADE have no prelude and no codata types, hence no positions: their pairs and their unit are types of
the theory, and a program of their theory nests the eliminations of their pairs and of their unit
itself.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Formation -/

/-- The constructors of the types of the prelude use their parameters as the grades of the types
allow.
RFC: `\mathsf{prelude}_{▶}` -/
theorem UsageSig.prelude : UsageSig Signature.prelude :=
  .data (.data (.data .empty rfl
    (fun ι _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      exact ⟨_, .cons .nil .nil, fun x => x.elim0⟩))
    rfl
    (fun (ι : Instance 1 2) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.pairMk) (.cons (δ := (𝟘ᶜ ∙ Grade.zero) ∙ Grade.one)
        (Usage.var .nil) (.sub (.cons (δ := 𝟘ᶜ) (Usage.var (.cons (Usage.var .nil) .nil))
          (.sub .nil ?_)) ?_)) .nil, ?_⟩
      all_goals
        intro x
        try simp only [Prelude.pairType]
        generalize ι.grades 0 = p
        generalize ι.grades 1 = ρ
        revert x p ρ
        decide))
    rfl
    (fun (ι : Instance 1 3) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.stepNext) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_))
        (.cons (c := Prelude.stepDone) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_)) .nil), ?_⟩
      all_goals
        intro x
        try simp only [Prelude.stepType]
        generalize ι.grades 0 = r
        generalize ι.grades 1 = p
        revert x r p
        decide)

/-! ## Packing -/

-- ADE: none.
/-- The packing of arguments uses the variables as the arguments do: each pair uses its first term
with the grade of its entry and the rest once, and the unit uses none.
RFC: `\mathsf{pack}_{\bar t▶}` -/
theorem Usage.pack {sig : Signature} (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} :
    {ps : List Parameter} → {γ : GradeVector Γ.length} → {ts : Args k Γ ps} →
      (Θ : Telescope k Γ ps) → (κs : List (Universe k)) → (l : Level k) →
      UsageArgs sig γ m ts → Usage sig γ m (ts.pack Θ κs l)
  | [], _, .nil, .nil, _, l, .nil =>
    Usage.ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl
      .nil
  | p :: _, _, .cons t ts, .cons _ _ A Θ, κs, l, .cons (γ := γ) (δ := δ) ht hts => by
    have hr := Usage.pack hpre (Θ.subst₀ (Subst₀.single t)) κs.tail l hts
    have hm : m ⊙ Grade.one = m := by cases m <;> decide
    refine .sub (Usage.ctor (con := Prelude.pairMk)
      (ts := .cons t (.cons (ts.pack (Θ.subst₀ (Subst₀.single t)) κs.tail l) .nil))
      (qs := [(κs.headD ⟨.type, l⟩).quality]) (ps := [p.usage, p.requirement])
      hpre.pair (List.mem_singleton_self _) rfl rfl (.cons ht (.cons (hm ▸ hr) .nil))) ?_
    intro x
    show p.usage * γ x + δ x ≤ p.usage * γ x + (Grade.one * δ x + Grade.zero)
    generalize p.usage * γ x = a
    generalize δ x = b
    revert a b
    decide

/-! ## Recursors of the Pair, of the Unit and of the Type of Positions -/

-- ADE: `prodrecₘ`, in `Graded/Usage.agda`.
/-- The recursor on a term of the pair uses the variables of its term `r` times and those of its
branch, whose uses of the two fields cover `⌜m⌝ · r` times their grades. -/
theorem Usage.pairRecursor (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} {q : Quality}
    {ls : List (Level k)} {p ρ r g₀ g₁ : Grade} {as : InstanceArgs k Γ Prelude.pairScope}
    {t : Term k Γ} {C : Term k (.var :: Γ)} {u : Term k (.var :: .var :: Γ)}
    {γ δ : GradeVector Γ.length}
    (hC : Usage sig 𝟘ᶜ .zeroZero C) (ht : Usage sig γ (m ⊙ r) t)
    (hu : Usage (Γ := .var :: .var :: Γ) sig ((δ ∙ g₀) ∙ g₁) m u)
    (hg₀ : m.grade * r * p ≤ g₀) (hg₁ : m.grade * r * Grade.one ≤ g₁) :
    Usage sig ((r ·ᶜ γ) +ᶜ δ) m
      (.recursor r "Pair" [q] ls [p, ρ] as t (.cons 0 C .nil) (.cons 2 0 #v[] u .nil)) := by
  have hz : ∀ a b c : Grade, a ≤ b → a ≤ b + Grade.zero * c := by decide
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) (δs := fun _ => δ)
    (gs := fun _ l => if l = 0 then g₀ else g₁) hpre.pair rfl rfl
    ?_ ht rfl ?_ ?_ ?_ ?_ ?_
  · intro j n C' hj
    match j, hj with
    | 0, hj => cases hj; exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu
  · intro i j T' con l p' hi hl
    match i, hi with
    | 0, rfl =>
      match l, hl with
      | 0, rfl => exact hz _ _ _ hg₀
      | 1, rfl => exact hz _ _ _ hg₁
  · intro i j T' con hi
    match i, hi with
    | 0, rfl =>
      intro x
      show δ x ≤ δ x + Grade.zero * δ x
      generalize δ x = a
      revert a
      decide
  · intro _ ⟨T', hT', h2⟩
    rcases hT' with _ | ⟨_, ⟨⟩⟩
    exact absurd h2 (by decide)

-- ADE: `unitrecₘ`, in `Graded/Usage.agda`.
/-- The recursor on a term of the unit uses the variables of its term `r` times and those of its
branch. -/
theorem Usage.unitRecursor (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} {l : Level k}
    {r : Grade} {t u : Term k Γ} {C : Term k (.var :: Γ)} {γ δ : GradeVector Γ.length}
    (hC : Usage sig 𝟘ᶜ .zeroZero C) (ht : Usage sig γ (m ⊙ r) t) (hu : Usage sig δ m u) :
    Usage sig ((r ·ᶜ γ) +ᶜ δ) m
      (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 #v[] u .nil)) := by
  refine .recursor (decl := Prelude.unit) (T := Prelude.unitType) (δs := fun _ => δ)
    (gs := fun _ _ => Grade.zero) hpre.unit rfl rfl
    ?_ ht rfl ?_ ?_ ?_ ?_ ?_
  · intro j n C' hj
    match j, hj with
    | 0, hj => cases hj; exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu
  · intro i j T' con l p' hi hl
    match i, hi with
    | 0, rfl => exact nomatch hl
  · intro i j T' con hi
    match i, hi with
    | 0, rfl =>
      intro x
      show δ x ≤ δ x + Grade.zero * δ x
      generalize δ x = a
      revert a
      decide
  · intro _ ⟨T', hT', h2⟩
    rcases hT' with _ | ⟨_, ⟨⟩⟩
    exact absurd h2 (by decide)

-- ADE: none.
/-- The recursor on a term of the type of positions uses the variables of its term `r` times and
those of its branches as a lower bound `χ` of their uses allows, each using the variable of its
field as `⌜m⌝ · r` times the grade of the field allows; in the mode `11ᵐ`, it uses its term at run
time, whose constructor chooses the branch. -/
theorem Usage.stepRecursor (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} {q : Quality}
    {ls : List (Level k)} {p q' ρ r g₀ g₁ : Grade} {as : InstanceArgs k Γ Prelude.stepScope}
    {t : Term k Γ} {C : Term k (.var :: Γ)} {u₀ u₁ : Term k (.var :: Γ)}
    {γ δ₀ δ₁ χ : GradeVector Γ.length}
    (hC : Usage sig 𝟘ᶜ .zeroZero C) (ht : Usage sig γ (m ⊙ r) t)
    (hu₀ : Usage (Γ := .var :: Γ) sig (δ₀ ∙ g₀) m u₀) (hu₁ : Usage (Γ := .var :: Γ) sig (δ₁ ∙ g₁) m u₁)
    (hg₀ : m.grade * r * p ≤ g₀) (hg₁ : m.grade * r * q' ≤ g₁) (hχ₀ : χ ≤ᶜ δ₀) (hχ₁ : χ ≤ᶜ δ₁)
    (hr : m = .oneOne → r.mode = .oneOne) :
    Usage sig ((r ·ᶜ γ) +ᶜ χ) m
      (.recursor r "Step" [q] ls [p, q', ρ] as t (.cons 0 C .nil)
        (.cons 1 0 #v[] u₀ (.cons 1 0 #v[] u₁ .nil))) := by
  have hz : ∀ a b c : Grade, a ≤ b → a ≤ b + Grade.zero * c := by decide
  have hl : ∀ a b : Grade, a ≤ b → a ≤ b + Grade.zero * a := by decide
  refine .recursor (decl := Prelude.step) (T := Prelude.stepType)
    (δs := fun i => if i = 0 then δ₀ else δ₁) (gs := fun i _ => if i = 0 then g₀ else g₁)
    hpre.step rfl rfl ?_ ht rfl ?_ ?_ ?_ ?_ ?_
  · intro j n C' hj
    match j, hj with
    | 0, hj => cases hj; exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u₀, rfl⟩
    | 1, rfl => exact ⟨u₁, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu₀
    | 1, rfl, rfl => exact hu₁
  · intro i j T' con l p' hi hl'
    match i, hi with
    | 0, rfl =>
      match l, hl' with
      | 0, rfl => exact hz _ _ _ hg₀
    | 1, rfl =>
      match l, hl' with
      | 0, rfl => exact hz _ _ _ hg₁
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact fun x => hl _ _ (hχ₀ x)
    | 1, rfl => exact fun x => hl _ _ (hχ₁ x)
  · intro hm _
    exact hr hm

/-! ## Unpacking -/

-- ADE: `prodrecₘ` and `unitrecₘ`, in `Graded/Usage.agda`, nested.
/-- The unpacking uses the variables of its term `r` times and those of its branch, which uses the
variable of each entry of the telescope `⌜m⌝ · r` times its grade; its motive, a type, uses no
variable.
RFC: `\mathsf{unpack}_{▶}` -/
theorem Usage.unpack (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} → {ps : List Parameter} →
    {m : Mode} → {γ δ : GradeVector Γ.length} → {u : Term k Γ} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → {C : Term k Γ} →
    {b : Term k (Γ.extend ps.length)} →
    Usage sig 𝟘ᶜ .zeroZero C → Usage sig γ (m ⊙ r) u →
    Usage sig (δ.extendParams (m.grade * r) ps) m b →
      Usage sig ((r ·ᶜ γ) +ᶜ δ) m (Term.unpack r u Θ κs l C b)
  | _, [], _, _, _, _, .nil, _, _, _, _, hC, hu, hb => by
    have hC' := usageStableUnderRenaming.usage (Ren.weaken (e := .var)) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC'
    exact Usage.unitRecursor hpre hC' hu hb
  | Γ, p :: ps, m, γ, δ, u, .cons _ _ A Θ, κs, l, C, b, hC, hu, hb => by
    have hC₁ := usageStableUnderRenaming.usage (Ren.weaken (e := .var)) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC₁
    have hC₂ := usageStableUnderRenaming.usage (Ren.weakenN (Γ := Γ) 2) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC₂
    have hb' := usageStableUnderRenaming.usage (Ren.liftN ps.length (Ren.weaken (e := .var))) hb
    erw [GradeVector.rename_extendParams (Γ := .var :: .var :: Γ) (Δ := .var :: Γ) (δ ∙ (m.grade * r * p.usage))
      (m.grade * r) ps (Ren.weaken (e := .var)), GradeVector.rename_weaken] at hb'
    have hy : Usage sig (GradeVector.update 𝟘ᶜ (Var.toFin .zero) (m ⊙ r).grade +ᶜ 𝟘ᶜ) (m ⊙ r)
        (Term.var₀ (Γ := .var :: .var :: Γ) (k := k) .zero) := .var .nil
    have ih := Usage.unpack hpre r (Θ := Θ.rename Ren.weaken) (κs := κs.tail) (l := l) hC₂ hy hb'
    have hz : ∀ r a : Grade, r * a ≤ r * (a + Grade.zero) + Grade.zero := by decide
    have hs : ∀ r c : Grade, c ≤ r * (Grade.zero + Grade.zero) + c := by decide
    have hm : ∀ (m : Mode) (r : Grade), m.grade * r * Grade.one ≤ r * (m ⊙ r).grade := by decide
    refine Usage.pairRecursor (g₁ := r * (m ⊙ r).grade) hpre hC₁ hu (.sub ih ?_) (Grade.le_refl _)
      (hm m r)
    intro y
    cases y using Fin.cases with
    | zero =>
      exact (congrArg (fun c => r * (m ⊙ r).grade ≤ r * (c + Grade.zero) + Grade.zero)
        (ite_eq_left rfl)).mpr (hz r _)
    | succ y =>
      exact (congrArg (fun c => (δ ∙ (m.grade * r * p.usage)) y ≤ r * (c + Grade.zero) +
        (δ ∙ (m.grade * r * p.usage)) y) (ite_eq_right (Fin.succ_ne_zero y))).mpr (hs r _)

/-! ## Resumption -/

-- ADE: none.
/-- The resumption of a position `v`, in a mode `m` that allows the grade `q_s` of a term already
built, uses the variables of `v` and those of the corecursor resumed as a lower bound `η` of its
uses `δ` and of no use allows, since a position resumes the corecursor or gives a term already
built: the corecursor from the variables of the state, which uses them as `⌜m⌝ · r` times their
grades allow, uses the others as `δ` allows.
RFC: `\mathsf{resume}_{▶}` -/
theorem Usage.resume (hpre : sig.HasPrelude) {Γ Δ : Scope} {ps' : List Parameter} {r : Grade}
    {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ Δ} {Ss : States k Γ} {gs : CorecBranches k Γ} {κ : Universe k}
    {χ : Grade} {S : Telescope k Γ ps'} {κs : List (Universe k)} {v : Term k Γ} {m : Mode}
    {γ δ η : GradeVector Γ.length}
    (hT : Usage sig 𝟘ᶜ .zeroZero (Term.inst D qs ls ps as)) (hv : Usage sig γ m v)
    (hc : Usage sig (δ.extendParams (m.grade * r) ps') m (Term.corecAt r D qs ls ps as Ss gs ps'))
    (hm : m ·ᵐ (Prelude.doneGrade κ.quality).mode = m) (hηδ : η ≤ᶜ δ) (hη : η ≤ᶜ 𝟘ᶜ) :
    Usage sig (γ +ᶜ η) m (Term.resume r D qs ls ps as Ss gs κ χ S κs v) := by
  have hT' := usageStableUnderRenaming.usage (Ren.weaken (e := .var)) hT
  rw [GradeVector.rename_commutes.rename_zero] at hT'
  have hc' := usageStableUnderRenaming.usage (Ren.liftN ps'.length (Ren.weaken (e := .var))) hc
  erw [GradeVector.rename_extendParams (Γ := .var :: Γ) (Δ := Γ) δ (m.grade * r) ps'
    (Ren.weaken (e := .var)), GradeVector.rename_weaken, Term.corecAt_rename] at hc'
  have hy : Usage sig (GradeVector.update 𝟘ᶜ (Var.toFin .zero) (m ⊙ r).grade +ᶜ 𝟘ᶜ) (m ⊙ r)
      (Term.var₀ (Γ := .var :: Γ) (k := k) .zero) := .var .nil
  have hn := Usage.unpack hpre r (Θ := S.rename Ren.weaken) (κs := κs)
    (l := Telescope.packLevel κs .zero) hT' hy hc'
  have hx : Usage sig (GradeVector.update 𝟘ᶜ (Var.toFin .zero) m.grade +ᶜ 𝟘ᶜ) m
      (Term.var₀ (Γ := .var :: Γ) (k := k) .zero) := .var .nil
  have hv' : Usage sig γ (m ⊙ Grade.one) v := by
    have : ∀ m : Mode, m ⊙ Grade.one = m := by decide
    rw [this]; exact hv
  have hd : ∀ (m : Mode) (q : Grade), m ·ᵐ q.mode = m → m.grade * Grade.one * q ≤ m.grade := by
    decide
  have hn' : ∀ (m : Mode) (r : Grade), m.grade * Grade.one * r ≤ r * (m ⊙ r).grade := by decide
  have hz : ∀ r a : Grade, r * a ≤ r * (a + Grade.zero) + Grade.zero := by decide
  have hs : ∀ r c : Grade, c ≤ r * (Grade.zero + Grade.zero) + c := by decide
  have h0 : ∀ a : Grade, a ≤ a + Grade.zero := by decide
  have h00 : Grade.zero ≤ Grade.zero + Grade.zero := by decide
  have h1 := Usage.stepRecursor (q := κ.quality)
    (ls := [Telescope.packLevel κs (Telescope.packLevel κs .zero), κ.level]) (p := r) (ρ := χ)
    (as := Prelude.stepArgs (S.pack κs (Telescope.packLevel κs .zero)) (.inst D qs ls ps as))
    (g₀ := r * (m ⊙ r).grade) (g₁ := m.grade) (δ₁ := 𝟘ᶜ) (χ := η)
    hpre hT' hv' (.sub hn ?_) (.sub hx ?_) (hn' m r) (hd m _ hm) hηδ hη (fun _ => by decide)
  · have hγ : ∀ x, (Grade.one ·ᶜ γ) x = γ x := fun x => by
      show Grade.one * γ x = γ x
      generalize γ x = a; revert a; decide
    exact .sub h1 (fun x => by
      show (γ +ᶜ η) x ≤ (Grade.one ·ᶜ γ +ᶜ η) x
      simp only [GradeVector.add, hγ]
      exact Grade.le_refl _)
  · intro y
    cases y using Fin.cases with
    | zero =>
      exact (congrArg (fun c => r * (m ⊙ r).grade ≤ r * (c + Grade.zero) + Grade.zero)
        (ite_eq_left rfl)).mpr (hz r _)
    | succ y =>
      exact (congrArg (fun c => (δ ∙ (r * (m ⊙ r).grade)) y.succ ≤ r * (c + Grade.zero) +
        (δ ∙ (r * (m ⊙ r).grade)) y.succ) (ite_eq_right (Fin.succ_ne_zero y))).mpr (hs r _)
  · intro y
    cases y using Fin.cases with
    | zero =>
      exact (congrArg (fun c => m.grade ≤ c + Grade.zero) (ite_eq_left rfl)).mpr (h0 _)
    | succ y =>
      exact (congrArg (fun c => Grade.zero ≤ c + Grade.zero)
        (ite_eq_right (Fin.succ_ne_zero y))).mpr h00

end Sic.Core
