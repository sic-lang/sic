module

public import Sic.Core.Soundness.Nesting.Reading
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Equality of the Nested Types

The graph of the nestings of the equality of annex 18 of RFC 36 is a reading of the nested types:
it reads two closed types, each at its nesting, with the same equality of their terms.
A position is read in a sort of the quality of the sort of the type it holds: the types given for
the variables with a position are read where the types of a universe that stand for them are, and a
type of a universe is not read as a proposition.
A type that is strictly positive in variables is then read by the graph at any closed types given
for these variables, when the graph reads them at their nestings: the equality of its terms is the
same at two substitutions, as the meaning of a nested field of a block asks, whatever the relations
given at its positions.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Types Read by the Graph of the Nestings -/

-- ADE: none.
/-- The graph of the nestings of the sort of the quality `s` at the level `n` reads two closed
types, each at its nesting, with the same equality of their terms, where the positions hold types
of sorts of the quality `sT`. -/
def NestReads (sig : Signature) (ι : Interpretation) (n : Nat) (sT s : Quality)
    (τ₁ τ₂ : Nest NestLeaf) (A₁ A₂ : Term 0 []) : Prop :=
  ∃ F, NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ₁ A₁ F ∧
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ₂ A₂ F

/-- Two equal closed types of a universe that the graph of the nestings reads without position in
the sort of the quality `s` are read in a sort of types: a type of a universe is not a
proposition. -/
theorem NestReads.quality_of_univ {A₁ A₂ : Term 0 []} {κ : Universe 0} {n : Nat}
    {sT s : Quality} (hκ : κ.quality = .type) (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ))
    (hr : NestReads sig ι n sT s .plain .plain A₁ A₂) : s = .type := by
  obtain ⟨F, hF, -⟩ := hr
  obtain ⟨q, l⟩ := κ
  obtain rfl : q = .type := hκ
  have hd := h.1.1
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ k hk =>
    cases levelRel_univ_iff.1 hk with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      obtain ⟨⟨R', h₁, -⟩, -⟩ := hvw
      cases hF with
      | plain hA hF' =>
        cases Computesι.det hd hw₁ hA
        cases hF' with
        | univ hs _ => exact hs
        | univBelow hs _ _ _ => exact hs
        | prop hP => exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h₁) hP).elim
        | propBelow m _ hP =>
          exact (UnivRel.not_prop hd (levelRel_univ_iff.1 h₁) (levelRel_prop_iff.1 hP)).elim

/-! ## Destructors Read by the Graph of the Nestings -/

/-- A destructor whose arguments are equal telescopes and whose results are equal types at two
equal closed substitutions, and are the same at two other substitutions, followed by destructors
that the graph of the nestings reads with one equality at these, for each pair of equal
abstractions for it, is read with them by the graph of the nestings with one equality, as a
destructor whose result has no position: the equality of its results and that of the destructors
after it are defined from the graph at the first substitution, which gives one at most. -/
theorem NestDesRel.of_plain_head (hd : sig.Distinct) {n : Nat} {sT : Quality} {κ κ₁ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting NestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
    (hν₁ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) = .plain)
    (hν₂ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) = .plain)
    (hΘ : ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂))
    (hΘ₁ : Θ.subst θ₁' = Θ.subst θ₁) (hΘ₂ : Θ.subst θ₂' = Θ.subst θ₂) (hκ : κ₁ ≼ κ)
    (hB : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
        (.sort κ₁))
    (hB₁ : ∀ τ, B.subst (Subst.append θ₁' τ) = B.subst (Subst.append θ₁ τ))
    (hB₂ : ∀ τ, B.subst (Subst.append θ₂' τ) = B.subst (Subst.append θ₂ τ))
    (hds : ∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
      ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁) S ∧
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) S) :
    ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality @ν₁
        (.cons (d := d) p q ς Θ B ψ ds) @θ₁' S ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality @ν₂
        (.cons (d := d) p q ς Θ B ψ ds) @θ₂' S := by
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have ihκ : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  have hSp := TelRel.isPer hd ihκ (fun _ => .plain) hT₁
  have hκn : κ₁.level.closedValue ≤ n := Nat.le_trans (hκ.2 Fin.elim0) hn
  -- The results at the first substitution and equal arguments are equal types.
  have hBB : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst))
        (B.subst (Subst.append θ₁ us.toSubst)) (.sort κ₁) := fun ts us hts =>
    have huu := hSp.trans (hSp.symm hts) hts
    (hB _ _ ((hT ts us).1 hts)).trans (hB _ _ ((hT us us).1 huu)).symm
  let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ w F', Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
      FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w F' ∧ F' t u
  have hFeq : ∀ (ts : Args 0 [] ps) w F₀,
      Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w →
      FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w F₀ →
      F ts.terms = F₀ := fun ts w F₀ hw hF₀ =>
    funext fun t => funext fun u => propext
      ⟨fun ⟨ts', hts', w', F', hw', hF', h'⟩ => by
        cases Args.terms_inj hts'
        cases Computesι.det hd hw hw'
        exact (FieldRel.unique hd ih hF' _ _ hF₀ t u).1 h',
      fun h' => ⟨ts, rfl, w, F₀, hw, hF₀, h'⟩⟩
  -- A type equal to the result at the first substitution and the arguments `ts` has the
  -- equality `F ts`.
  have hres : ∀ (ts : Args 0 [] ps) (A : Term 0 []),
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst)) A (.sort κ₁) →
      (∃ w, Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality w (F ts.terms)) ∧
      ∃ v, Computesι sig ι A v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) κ.quality v (F ts.terms) :=
    fun ts A hA => by
      obtain ⟨w₁, w₂, F₀, hw₁, hw₂, hF₁, hF₂, -⟩ := hA.fieldRel hκ.1 hκn
      rw [hFeq ts w₁ F₀ hw₁ hF₁]
      exact ⟨⟨w₁, hw₁, hF₁⟩, w₂, hw₂, hF₂⟩
  have hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u := fun ts us hts t u => by
    obtain ⟨ts', us', rfl, rfl, -⟩ := hT₁.to_eqSubst hd
      (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) _ _ hts
    have huu := hSp.trans (hSp.symm hts) hts
    obtain ⟨⟨w', hw', -⟩, -⟩ := hres us' _ (hBB us' us' huu)
    obtain ⟨-, v, hv, hFv⟩ := hres ts' _ (hBB ts' us' hts)
    cases Computesι.det hd hw' hv
    rw [hFeq us' w' _ hw' hFv]
  -- Equal abstractions for the destructor have equal instances at equal arguments.
  have hcond : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ τ₁ τ₂,
      EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁)) :=
    fun f₁ f₂ hf τ₁ τ₂ hτ => by
      obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
          @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
        ⟨_, Subst.args_toSubst ps τ₁⟩
      obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
          @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
        ⟨_, Subst.args_toSubst ps τ₂⟩
      have hts := (hT ts us).2 hτ
      have htt := hSp.trans hts (hSp.symm hts)
      obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts htt)
      exact hF.validEqTerm hd hw (hf _ _ hts)
  let G : Term 0 (Scope.extend [] ps.length) → ObsRel := fun f o₁ o₂ => ∃ S',
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' ∧ S' o₁ o₂
  have hGeq : ∀ f S', NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' → G f = S' := fun f S' hS' =>
    funext fun o₁ => funext fun o₂ => propext
      ⟨fun ⟨_, h', hs⟩ => (NestDesRel.unique hd ih h' _ _ hS' o₁ o₂).1 hs,
        fun hs => ⟨S', hS', hs⟩⟩
  have hG : ∀ f, AbstractionRel SΘ F f f →
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
        (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) (G f) ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
        (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₂' f) (G f) := fun f hf => by
    obtain ⟨S', h₁, h₂⟩ := hds f f (hcond f f hf)
    rw [hGeq f S' h₁]
    exact ⟨h₁, h₂⟩
  have hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ o₁ o₂, G f₁ o₁ o₂ ↔ G f₂ o₁ o₂ :=
    fun f₁ f₂ hf o₁ o₂ => by
      have hEp := AbstractionRel.isPer hSp (fun ts hts =>
        have ⟨⟨_, _, hF⟩, _⟩ := hres ts _ (hBB ts ts hts)
        FieldRel.isPer hd ih hF) hBresp
      obtain ⟨S', h₁, h₂⟩ := hds f₁ f₂ (hcond f₁ f₂ hf)
      have hf₂ := hEp.trans (hEp.symm hf) hf
      obtain ⟨S'', h₁', h₂'⟩ := hds f₂ f₂ (hcond f₂ f₂ hf₂)
      rw [hGeq f₁ S' h₁, hGeq f₂ S'' h₁']
      exact NestDesRel.unique hd ih h₂ _ _ h₂' o₁ o₂
  refine ⟨_, .cons hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).1) hresp,
    .cons hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).2) hresp⟩
  · obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts hts)
    rw [hB₁]
    exact .plain hw hF
  · obtain ⟨-, v, hv, hF⟩ := hres ts _ (hB _ _ ((hT ts ts).1 hts))
    rw [hB₂]
    exact .plain hv hF

/-- A destructor whose arguments are equal telescopes at two equal closed substitutions, and are
the same at two other substitutions, at which the graph of the nestings reads its results at their
nestings with one equality, at equal arguments, followed by destructors that the graph reads with
one equality at these substitutions, for each pair of abstractions for it, is read with them by the
graph of the nestings with one equality, as a destructor whose result has a position. -/
theorem NestDesRel.of_nested_head (hd : sig.Distinct) {n : Nat} {sT : Quality} {κ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting NestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
    (hν₁ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) ≠ .plain)
    (hν₂ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) ≠ .plain)
    (hΘ : ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂))
    (hΘ₁ : Θ.subst θ₁' = Θ.subst θ₁) (hΘ₂ : Θ.subst θ₂' = Θ.subst θ₂)
    (hB : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      NestReads sig ι n sT κ.quality (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂))
        (B.subst (Subst.append θ₁' τ₁)) (B.subst (Subst.append θ₂' τ₂)))
    (hds : ∀ f₁ f₂, ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁) S ∧
        NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
          (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂) S) :
    ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality @ν₁
        (.cons (d := d) p q ς Θ B ψ ds) @θ₁' S ∧
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality @ν₂
        (.cons (d := d) p q ς Θ B ψ ds) @θ₂' S := by
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have ihκ : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  have hSp := TelRel.isPer hd ihκ (fun _ => .plain) hT₁
  let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ F', NestRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
      (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
      (B.subst (Subst.append θ₁' ts.toSubst)) F' ∧ F' t u
  have hFeq : ∀ (ts : Args 0 [] ps) F₀,
      NestRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.subst (Subst.append θ₁' ts.toSubst)) F₀ → F ts.terms = F₀ := fun ts F₀ hF₀ =>
    funext fun t => funext fun u => propext
      ⟨fun ⟨ts', hts', F', hF', h'⟩ => by
        cases Args.terms_inj hts'
        exact (NestRel.unique hd ih hF' _ _ hF₀ t u).1 h',
      fun h' => ⟨ts, rfl, F₀, hF₀, h'⟩⟩
  have hBresp : ∀ ts us, SΘ ts us → ∀ t u, F ts t u ↔ F us t u := fun ts us hts t u => by
    obtain ⟨ts', us', rfl, rfl, hE⟩ := hT₁.to_eqSubst hd
      (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) _ _ hts
    have huu := hSp.trans (hSp.symm hts) hts
    obtain ⟨F', h₁, h₂⟩ := hB _ _ hE
    obtain ⟨F'', h₁', h₂'⟩ := hB _ _ ((hT us' us').1 huu)
    rw [hFeq ts' F' h₁, hFeq us' F'' h₁']
    exact NestRel.unique hd ih h₂ _ _ h₂' t u
  -- The destructors after it have one equality, whatever the abstractions for it.
  let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
  obtain ⟨G, h₀₁, h₀₂⟩ := hds f₀ f₀
  refine ⟨_, .nested hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F (fun ts hts => ?_) hBresp G (fun f => ?_),
    .nested hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F (fun ts hts => ?_) hBresp G (fun f => ?_)⟩
  · obtain ⟨F', h₁, -⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hFeq ts F' h₁]
    exact h₁
  · obtain ⟨S, h₁, h₂⟩ := hds f f₀
    have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
      (NestDesRel.unique hd ih h₂ _ _ h₀₂ o₁ o₂)
    exact hSG ▸ h₁
  · obtain ⟨F', h₁, h₂⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hFeq ts F' h₁]
    exact h₂
  · obtain ⟨S, h₁, h₂⟩ := hds f₀ f
    have hSG : S = G := funext fun o₁ => funext fun o₂ => propext
      (NestDesRel.unique hd ih h₁ _ _ h₀₁ o₁ o₂)
    exact hSG ▸ h₂

/-- An instance of a codata type that is a type of a field of the sort of the quality `s` at the
level `n` lives at a level that `n` bounds, and `s` is the quality of the universes when it lives
in a universe. -/
theorem FieldRel.codata_inv (hd : sig.Distinct) {n : Nat} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue ≤ n ∧
      ((decl.sort (.ofLists qs ps hq hp)).quality = .type → s = .type) := by
  have hu : ∀ m R, UnivRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R →
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = m :=
    fun m R hu => by
      cases hu with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' _ hn' =>
        obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
        subst hD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
        exact hn'
  have hb : ∀ m b, PropRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) b →
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = m ∧
        (decl.sort (.ofLists qs ps hq hp)).quality = .prop :=
    fun m b hb => by
      cases hb with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' hs' hn' =>
        obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
        subst hD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
        exact ⟨hn', hs'⟩
  cases hF with
  | univ hs hu' => exact ⟨Nat.le_of_eq (hu n _ hu'), fun _ => hs⟩
  | univBelow hs m hm hu' =>
    exact ⟨Nat.le_trans (Nat.le_of_eq (hu m _ (levelRel_univ_iff.1 hu'))) (Nat.le_of_lt hm),
      fun _ => hs⟩
  | prop hb' =>
    obtain ⟨e, hκ'⟩ := hb n _ hb'
    exact ⟨Nat.le_of_eq e, fun hκ => nomatch hκ.symm.trans hκ'⟩
  | propBelow m hm hb' =>
    obtain ⟨e, hκ'⟩ := hb m _ (levelRel_prop_iff.1 hb')
    exact ⟨Nat.le_trans (Nat.le_of_eq e) (Nat.le_of_lt hm), fun hκ => nomatch hκ.symm.trans hκ'⟩

/-! ## Reading of the Equality -/

-- ADE: none.
/-- The reading of the graph of the nestings of the equality at the level `n`, of the sorts whose
level `n` bounds, at positions that hold types of sorts of the quality `sT`: two types, or the
destructors of a codata type at two substitutions, are read with one equality, in the sort of a
quality. -/
def nestReading (sig : Signature) (ι : Interpretation) (hd : sig.Distinct) (n : Nat)
    (sT : Quality) :
    Reading sig ι NestLeaf Quality where
  rd := NestReads sig ι n sT
  dr s _ _ ν₁ ν₂ ds θ₁ θ₂ := ∃ S,
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν₁ ds @θ₁ S ∧
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν₂ ds @θ₂ S
  ok s κ := κ.level.closedValue ≤ n ∧ s = κ.quality
  plain := fun ⟨hn, hs⟩ hκ h => by
    subst hs
    obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, -⟩ :=
      h.fieldRel hκ.1 (Nat.le_trans (hκ.2 Fin.elim0) hn)
    exact ⟨F, .plain hc₁ hF₁, .plain hc₂ hF₂⟩
  nil := ⟨fun _ _ => True, .nil, .nil⟩
  plain_head := fun ⟨hn, hs⟩ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁ hB₂
      hds => by
    subst hs
    exact NestDesRel.of_plain_head hd hn hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁ hB₂ hds
  nested_head := fun ⟨hn, hs⟩ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds => by
    subst hs
    exact NestDesRel.of_nested_head hd hn hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds
  inst := by
    intro s decl D T qs ls ps as₁ as₂ as₁' as₂' νs₁ νs₂ hT hq hl hp hrec hr
    obtain ⟨FE, hrE, -⟩ := hr
    cases hrE with
    | plain hc hF =>
      cases Computesι.det hd ⟨.refl _, .inst D qs _ ps _⟩ hc
      obtain ⟨hn, hs⟩ := FieldRel.codata_inv hd hT hq hl hp hF
      have hls : ∀ i, (Level.ofNat ((ls.getFin hl i).closedValue) : Level 0) ≈ ls.getFin hl i :=
        fun i => Level.ofNat_closedValue _
      refine ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        ⟨Nat.le_trans (Nat.le_of_eq (Level.closedValue_subst_equiv hls _)) hn, rfl⟩,
        fun ⟨S, hS₁, hS₂⟩ => ?_⟩
      have hinv : ∀ m, m < n → (levelRel sig ι m).LevelInvariant :=
        fun m _ => levelRel_levelInvariant hd m
      have hrel : ∀ ν : Nesting NestLeaf decl.scope,
          Nesting.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) @ν @ν :=
        fun ν _ x => Nest.rel₃_refl (fun _ => ⟨Term.LevelEquiv.refl _, rfl⟩) _
      have hS₁' := NestDesRel.levelEquiv hd hinv hS₁
        (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
      have hS₂' := NestDesRel.levelEquiv hd hinv hS₂
        (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
      cases hκ : (decl.sort (.ofLists qs ps hq hp)).quality with
      | type =>
        rw [hκ] at hS₁' hS₂'
        exact ⟨_, .codata hT hq hl hp rfl (hs hκ) hκ hn hrec S hS₁',
          .codata hT hq hl hp rfl (hs hκ) hκ hn hrec S hS₂'⟩
      | prop =>
        rw [hκ] at hS₁' hS₂'
        exact ⟨_, .codataProp hT hq hl hp rfl hκ hn hrec S hS₁',
          .codataProp hT hq hl hp rfl hκ hn hrec S hS₂'⟩

-- ADE: none.
/-- The types typed in a signature whose entries have their meaning, and strictly positive in the
variables with a position, are read by the graph of the nestings of the equality at their
nestings, with one equality of their terms, given the soundness of the typing. -/
theorem NestReads.readsNested (hS : TypingSound sig ι) (hd : sig.Distinct) (n : Nat) (sT : Quality)
    {sigT : Signature} (hent : sig.ValidEntries ι sigT) :
    ReadsNested sig ι (NestReads sig ι n sT) sigT :=
  ReadsInstances.readsNested hS hent ((nestReading sig ι hd n sT).readsInstances hS sigT hent)

end

end Sic.Core
