module

public import Sic.Core.Ownership
public import Sic.Core.Prelude
public import Sic.Core.Usage
import Sic.Core.Ownership.Renaming
import Sic.Core.Prelude.Unpacking
import Sic.Core.Usage.Renaming

/-!
# Positions

The positions of annex 17 of RFC 36: the resumption of a position, which an observation of a
recursive destructor computes, a recursor on the type of positions that unpacks a new state into the
corecursor from it, or gives a term already built; its usage and its ownership, derived from the
rules of the recursor of the type of positions and of the unpacking, which show what the rules of
the corecursors require of the branches of their recursive destructors.

The rules of the recursor on the type of positions are the rules of the data types at the instances
of the prelude, whose premises on the block hold by computation.

ADE have no codata types, hence no positions.
-/

@[expose] public section

namespace Sic.Core

variable {sig : Signature} {k : Nat}

/-! ## Rules of the Type of Positions -/

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

-- ADE: none.
/-- The recursor on a term of the type of positions has the ownership of its branches, each checked
with the ownership `o` of the term times the requirement of its field, times the grade `⌜m⌝ · r`
of the recursor times the grade of the field, for its variable. -/
theorem Ownership.stepRecursor (hpre : sig.HasPrelude) {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {q : Quality} {ls : List (Level k)} {p q' ρ r o p' : Grade}
    {as : InstanceArgs k Γ Prelude.stepScope} {t : Term k Γ} {C : Term k (.var :: Γ)}
    {u₀ u₁ : Term k (.var :: Γ)} (ht : Ownership sig φ (m ⊙ r) o t)
    (hu₀ : Ownership sig (Ownership.extendFields φ o (m.grade * r) [⟨p, Grade.one⟩]) m p' u₀)
    (hu₁ : Ownership sig (Ownership.extendFields φ o (m.grade * r) [⟨q', ρ⟩]) m p' u₁) :
    Ownership sig φ m p'
      (.recursor r "Step" [q] ls [p, q', ρ] as t (.cons 0 C .nil)
        (.cons 1 0 #v[] u₀ (.cons 1 0 #v[] u₁ .nil))) := by
  refine .recursor (decl := Prelude.step) (T := Prelude.stepType) hpre.step rfl rfl ht rfl ?_ ?_
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u₀, rfl⟩
    | 1, rfl => exact ⟨u₁, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu₀
    | 1, rfl, rfl => exact hu₁

/-! ## Resumption -/

-- ADE: none.
/-- The corecursor from the variables of a state, renamed under the variables of the state, is the
corecursor from these variables of its instance, states and branches renamed. -/
theorem Term.corecAt_rename {Γ Δ Ξ : Scope} (ξ : Ren Γ Δ) (r : Grade) (D : Name)
    (qs : List Quality) (ls : List (Level k)) (ps : List Grade) (as : InstanceArgs k Δ Ξ)
    (Ss : States k Δ) (gs : CorecBranches k Δ) (ps' : List Parameter) :
    (Term.corecAt r D qs ls ps as Ss gs ps').rename (Ren.liftN ps'.length ξ) =
      Term.corecAt r D qs ls ps (as.rename ξ) (Ss.rename ξ) (gs.rename ξ) ps' := by
  rw [Term.rename_eq_subst_of (θ := Subst.liftN ps'.length (Ren.toSubst ξ))
      (Subst.liftN_eta_of ps'.length (fun _ => rfl)),
    Term.corecAt_subst, ← InstanceArgs.rename_eq_subst,
    (States.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (Ss.rename ξ)).symm.trans
      (States.subst_rename_of (fun _ => rfl) Ss),
    (CorecBranches.subst_id_of (θ := fun x => Var.eta x) (fun _ => rfl) (gs.rename ξ)).symm.trans
      (CorecBranches.subst_rename_of (fun _ => rfl) gs)]
  rfl

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

-- ADE: none.
/-- The resumption of a position `v` of the ownership `o` has every ownership `p'` below the
ownership `11ᵖ` of the corecursor resumed, a new value, and below the ownership of the term already
built, which the recursor gives the ownership `o` times its requirement `χ`, times the grade
`⌜m⌝ · q_s` with which the branch uses it, since a position resumes the corecursor or gives a term
already built: the corecursor from the variables of the state, each of the ownership `o` times the
grade `⌜m⌝ · r` of the new state, times its requirement, times the grade with which the corecursor
uses it, has the ownership `11ᵖ` of a new value.
RFC: `\mathsf{resume}_{◀}` -/
theorem Ownership.resume (hpre : sig.HasPrelude) {Γ Δ : Scope} {ps' : List Parameter} {r : Grade}
    {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ Δ} {Ss : States k Γ} {gs : CorecBranches k Γ} {κ : Universe k}
    {χ : Grade} {S : Telescope k Γ ps'} {κs : List (Universe k)} {v : Term k Γ} {m : Mode}
    {φ : Var Γ .var → Grade} {o p' : Grade} (hv : Ownership sig φ m o v)
    (hc : Ownership sig (Ownership.extendFields φ (o * (m.grade * r)) (m.grade * r) ps') m
      .linearLinear (Term.corecAt r D qs ls ps as Ss gs ps'))
    (hp₁ : p' ≤ .linearLinear) (hp₂ : p' ≤ (o * χ) * (m.grade * Prelude.doneGrade κ.quality)) :
    Ownership sig φ m p' (Term.resume r D qs ls ps as Ss gs κ χ S κs v) := by
  have hv' : Ownership sig φ (m ⊙ Grade.one) o v := by
    have : ∀ m : Mode, m ⊙ Grade.one = m := by decide
    rw [this]; exact hv
  let φ' : Var (.var :: Γ) .var → Grade :=
    Ownership.extendFields φ o (m.grade * Grade.one) [⟨r, Grade.one⟩]
  have hx : φ' .zero = o * (m.grade * r) := by
    show (o * Grade.one) * ((m.grade * Grade.one) * r) = o * (m.grade * r)
    generalize o = a; generalize m = b; generalize r = c; revert a b c; decide
  have hy : Ownership sig φ' (m ⊙ r) (o * (m.grade * r)) (Term.var₀ (k := k) .zero) :=
    hx ▸ Ownership.var (φ := φ') (x := .zero)
  have hc' := ownershipStableUnderRenaming.ownership (Ren.liftN ps'.length (Ren.weaken (e := .var)))
    (Ownership.extendFields_liftN (φ' := φ') (ξ := Ren.weaken)
      (fun _ => rfl) (o * (m.grade * r)) (m.grade * r) ps') hc
  erw [Term.corecAt_rename] at hc'
  have hn := Ownership.unpack hpre r (Θ := S.rename Ren.weaken) (κs := κs)
    (l := Telescope.packLevel κs .zero)
    (C := (Term.inst D qs ls ps as).rename Ren.weaken) hy (.sub hc' hp₁)
  have hd : Ownership sig
      (Ownership.extendFields φ o (m.grade * Grade.one) [⟨Prelude.doneGrade κ.quality, χ⟩]) m p'
      (Term.var₀ (k := k) .zero) := by
    refine .sub (Ownership.var (x := .zero)) ?_
    show p' ≤ (o * χ) * ((m.grade * Grade.one) * Prelude.doneGrade κ.quality)
    have : ∀ (m : Mode) (q : Grade), (m.grade * Grade.one) * q = m.grade * q := by decide
    rw [this]; exact hp₂
  exact Ownership.stepRecursor hpre hv' hn hd
