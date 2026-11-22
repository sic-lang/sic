module

public import Sic.Core.Meaning.Equality.Properties
public import Sic.Core.Soundness.Nesting.Reading
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Equality of the Nested Types

The graph of the nestings of the equality of annex 21 of RFC 36 is a reading of the nested types:
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

/-- The graph of the nestings of the sort of the quality `s` at the level `n` reads two closed
types, each at its nesting, with the same equality of their terms, where the positions hold types
of sorts of the quality `sT`. -/
def NestReads (sig : Signature) (ι : Interpretation) (n : Nat) (sT s : Quality)
    (τ₁ τ₂ : Nest NestLeaf) (A₁ A₂ : Term 0 []) : Prop :=
  ∃ F, NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ₁ A₁ F ∧
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ₂ A₂ F

/-- The graph of the nestings at the level `n` reads the destructors of a codata type at two
nestings of their scope and two closed substitutions, in the sort of the quality `s`, with the same
equality of the observations by them, where the positions hold types of sorts of the quality
`sT`. -/
def NestDesReads (sig : Signature) (ι : Interpretation) (n : Nat) (sT s : Quality) {Γ : Scope}
    {ns : List Name} (ν₁ ν₂ : Nesting NestLeaf Γ) (ds : Destructors 0 Γ ns)
    (θ₁ θ₂ : Subst 0 [] Γ) : Prop :=
  ∃ S, NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν₁ ds @θ₁ S ∧
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν₂ ds @θ₂ S

/-- The sorts in which the graph of the nestings at the level `n` reads in the sort of the quality
`s`: those of the quality `s` whose level `n` bounds. -/
def NestReadsOk (n : Nat) (s : Quality) (κ : Universe 0) : Prop :=
  κ.level.closedValue ≤ n ∧ s = κ.quality

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
    | data _ _ _ hv => cases hv
    | codata _ _ _ hv => cases hv
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

/-- The clause `Reading.PlainHead` of the graph of the nestings: a destructor whose arguments are
equal telescopes and whose results are equal types at two equal closed substitutions, and are the
same at two other substitutions, followed by destructors that the graph of the nestings reads with
one equality at these, for each pair of equal abstractions for it, is read with them by the graph of
the nestings with one equality, as a destructor whose result has no position: the equality of its
results and that of the destructors after it are defined from the graph at the first substitution,
which gives one at most. -/
theorem NestDesRel.of_plain_head (hd : sig.Distinct) {n : Nat} {sT : Quality} :
    Reading.PlainHead sig ι (NestDesReads sig ι n sT) (NestReadsOk n) := by
  intro s κ κ₁ ⟨hn, hs⟩ Γ d ns ps p q ς Θ B ψ ds ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁
    hB₂ hds
  subst hs
  unfold NestDesReads at hds ⊢
  have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) κ.level.closedValue)
    (fun _ => .plain) hT₁
  have hκn : κ₁.level.closedValue ≤ n := Nat.le_trans (hκ.2 Fin.elim0) hn
  obtain ⟨hF₁, hF₂, hBresp, hcond⟩ := FieldRel.atArgs_head hd hT₁ hκ.1 hκn hB
  let F : Terms 0 [] → TermRel := FieldRel.atArgs sig ι n κ.quality fun ts =>
    B.subst (Subst.append θ₁ ts.toSubst)
  let G : Term 0 (Scope.extend [] ps.length) → ObsRel := Math.Rel₂.ofGraph fun f S' =>
    NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT κ.quality
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S'
  have hGeq : ∀ f S', _ → G f = S' := fun _ _ hS' =>
    Math.Rel₂.ofGraph_eq hS' fun _ h' => NestDesRel.unique hd ih h' _ _ hS'
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
        have ⟨⟨w, hw⟩, hF⟩ := hF₁ ts hts
        FieldRel.isPer hd ih (hF w hw)) hBresp
      obtain ⟨S', h₁, h₂⟩ := hds f₁ f₂ (hcond f₁ f₂ hf)
      have hf₂ := hEp.trans (hEp.symm hf) hf
      obtain ⟨S'', h₁', h₂'⟩ := hds f₂ f₂ (hcond f₂ f₂ hf₂)
      rw [hGeq f₁ S' h₁, hGeq f₂ S'' h₁']
      exact NestDesRel.unique hd ih h₂ _ _ h₂' o₁ o₂
  refine ⟨_, .cons hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).1) hresp,
    .cons hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F (fun ts hts => ?_) hBresp G
      (fun f hf => (hG f hf).2) hresp⟩
  · obtain ⟨⟨w, hw⟩, hF⟩ := hF₁ ts hts
    rw [hB₁]
    exact .plain hw (hF w hw)
  · obtain ⟨⟨v, hv⟩, hF⟩ := hF₂ ts hts
    rw [hB₂]
    exact .plain hv (hF v hv)

/-- The head of a destructor whose result has a position, whose arguments are a closed telescope
`Θ` of the graph of a sort, with the equality `SΘ`, and whose results `B` the graph of the nestings
reads with one equality at equal arguments, at two substitutions `θ₁` and `θ₂` and at two nestings
`τ₁` and `τ₂`: the graph reads its results at arguments that `SΘ` relates to themselves, at both
substitutions, with the equality at these arguments that it gives at `θ₁`, which `SΘ` respects. -/
theorem NestRel.atArgs_head (hd : sig.Distinct) {m n : Nat} {sT s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {SΘ : FieldsRel}
    (hT₁ : TelRel sig ι m (fun k _ => levelRel sig ι k) .type (fun _ => .plain) Θ SΘ) {Γ : Scope}
    {B : Term 0 (Γ.extend ps.length)} {τ₁ τ₂ : Nest NestLeaf} {θ₁ θ₂ : Subst 0 [] Γ}
    (hB : ∀ σ₁ σ₂, EqSubst sig ι (Context.empty.append Θ) σ₁ σ₂ →
      NestReads sig ι n sT s τ₁ τ₂ (B.subst (Subst.append θ₁ σ₁)) (B.subst (Subst.append θ₂ σ₂))) :
    (∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      NestRel sig ι n (fun k _ => levelRel sig ι k) sT s τ₁ (B.subst (Subst.append θ₁ ts.toSubst))
        (NestRel.atArgs sig ι n sT s τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst))
          ts.terms)) ∧
    (∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      NestRel sig ι n (fun k _ => levelRel sig ι k) sT s τ₂ (B.subst (Subst.append θ₂ ts.toSubst))
        (NestRel.atArgs sig ι n sT s τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst))
          ts.terms)) ∧
    ∀ ts us, SΘ ts us → ∀ t u,
      NestRel.atArgs sig ι n sT s τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst)) ts t u ↔
        NestRel.atArgs sig ι n sT s τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst)) us t u := by
  have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have hT := TelRel.eqSubst_iff_plain hd hT₁
  have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) m) (fun _ => .plain) hT₁
  have heq := fun (ts : Args 0 [] ps) F' =>
    NestRel.atArgs_eq (A := fun ts => B.subst (Subst.append θ₁ ts.toSubst)) (ts := ts) (F := F')
      (sT := sT) (s := s) (τ := τ₁) hd ih
  refine ⟨fun ts hts => ?_, fun ts hts => ?_, fun ts us hts t u => ?_⟩
  · obtain ⟨F', h₁, -⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [heq ts F' h₁]
    exact h₁
  · obtain ⟨F', h₁, h₂⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [heq ts F' h₁]
    exact h₂
  · obtain ⟨ts', us', rfl, rfl, hE⟩ := hT₁.to_eqSubst_plain hd _ _ hts
    have huu := hSp.trans (hSp.symm hts) hts
    obtain ⟨F', h₁, h₂⟩ := hB _ _ hE
    obtain ⟨F'', h₁', h₂'⟩ := hB _ _ ((hT us' us').1 huu)
    rw [heq ts' F' h₁, heq us' F'' h₁']
    exact NestRel.unique hd ih h₂ _ _ h₂' t u

/-- The clause `Reading.NestedHead` of the graph of the nestings: a destructor whose arguments are
equal telescopes at two equal closed substitutions, and are the same at two other substitutions, at
which the graph of the nestings reads its results at their nestings with one equality, at equal
arguments, followed by destructors that the graph reads with one equality at these substitutions,
for each pair of abstractions for it, is read with them by the graph of the nestings with one
equality, as a destructor whose result has a position. -/
theorem NestDesRel.of_nested_head (hd : sig.Distinct) {n : Nat} {sT : Quality} :
    Reading.NestedHead sig ι (NestReads sig ι n sT) (NestDesReads sig ι n sT) (NestReadsOk n) := by
  intro s κ ⟨hn, hs⟩ Γ d ns ps p q ς Θ B ψ ds ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds
  subst hs
  unfold NestDesReads at hds ⊢
  have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  obtain ⟨hF₁, hF₂, hBresp⟩ := NestRel.atArgs_head hd hT₁ hB
  let F : Terms 0 [] → TermRel := NestRel.atArgs sig ι n sT κ.quality
    (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁)) fun ts =>
      B.subst (Subst.append θ₁' ts.toSubst)
  -- The destructors after it have one equality, whatever the abstractions for it.
  let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
  obtain ⟨G, h₀₁, h₀₂⟩ := hds f₀ f₀
  refine ⟨_, .nested hν₁ (hΘ₁ ▸ hT₁.levelLe hn) F hF₁ hBresp G (fun f => ?_),
    .nested hν₂ (hΘ₂ ▸ hT₂.levelLe hn) F hF₂ hBresp G (fun f => ?_)⟩
  · obtain ⟨S, h₁, h₂⟩ := hds f f₀
    have hSG : S = G := Math.Rel₂.ext_of_iff (NestDesRel.unique hd ih h₂ _ _ h₀₂)
    exact hSG ▸ h₁
  · obtain ⟨S, h₁, h₂⟩ := hds f₀ f
    have hSG : S = G := Math.Rel₂.ext_of_iff (NestDesRel.unique hd ih h₁ _ _ h₀₁)
    exact hSG ▸ h₂

/-- An instance of a codata type that is a type of a field of the sort of the quality `s` at the
level `n` lives at a level that `n` bounds, and `s` is the quality of the universes when it lives
in a universe. -/
theorem FieldRel.codata_inv (hd : sig.Distinct) {n : Nat} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels)
    {s : Quality} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s (.inst D qs ls ps as) F) :
    (decl.sortAt hqp.inst (ls.getFin hl)).level.closedValue ≤ n ∧
      ((decl.sort hqp.inst).quality = .type → s = .type) := by
  have hu : ∀ m R, UnivRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R →
      (decl.sortAt hqp.inst (ls.getFin hl)).level.closedValue = m :=
    fun m R hu => by
      cases hu with
      | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ hv' _ hn' =>
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
        exact hn'
  have hb : ∀ m b, PropRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) b →
      (decl.sortAt hqp.inst (ls.getFin hl)).level.closedValue = m ∧
        (decl.sort hqp.inst).quality = .prop :=
    fun m b hb => by
      cases hb with
      | data h' _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ hv' hs' hn' =>
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
        exact ⟨hn',
          hs'⟩
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

/-- The reading of the graph of the nestings of the equality at the level `n`, of the sorts whose
level `n` bounds, at positions that hold types of sorts of the quality `sT`: two types, or the
destructors of a codata type at two substitutions, are read with one equality, in the sort of a
quality. -/
def nestReading (sig : Signature) (ι : Interpretation) (hd : sig.Distinct) (n : Nat)
    (sT : Quality) :
    Reading sig ι NestLeaf Quality where
  rd := NestReads sig ι n sT
  dr := NestDesReads sig ι n sT
  ok := NestReadsOk n
  plain := fun ⟨hn, hs⟩ hκ h => by
    subst hs
    obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, -⟩ :=
      h.fieldRel hκ.1 (Nat.le_trans (hκ.2 Fin.elim0) hn)
    exact ⟨F, .plain hc₁ hF₁, .plain hc₂ hF₂⟩
  nil := ⟨fun _ _ => True, .nil, .nil⟩
  plain_head := NestDesRel.of_plain_head hd
  nested_head := NestDesRel.of_nested_head hd
  inst := by
    intro s decl D T qs ls ps as₁ as₂ as₁' as₂' νs₁ νs₂ hT hqp hl hrec _ hr
    obtain ⟨FE, hrE, -⟩ := hr
    cases hrE with
    | plain hc hF =>
      cases Computesι.det hd (Whnf.inst D qs _ ps _).computes hc
      obtain ⟨hn, hs⟩ := FieldRel.codata_inv hd hT hqp hl hF
      refine ⟨(decl.sort hqp.inst).quality,
        ⟨Nat.le_trans (Nat.le_of_eq (decl.sort_atLevels_closedValue hqp hl)) hn, rfl⟩,
        fun ⟨S, hS₁, hS₂⟩ => ?_⟩
      have hS₁' := NestDesRel.substLevels_of_atLevels hd hS₁
      have hS₂' := NestDesRel.substLevels_of_atLevels hd hS₂
      cases hκ : (decl.sort hqp.inst).quality with
      | type =>
        rw [hκ] at hS₁' hS₂'
        exact ⟨_, .codata hT hqp hl rfl (hs hκ) hκ hn hrec S hS₁',
          .codata hT hqp hl rfl (hs hκ) hκ hn hrec S hS₂'⟩
      | prop =>
        rw [hκ] at hS₁' hS₂'
        exact ⟨_, .codataProp hT hqp hl rfl hκ hn hrec S hS₁',
          .codataProp hT hqp hl rfl hκ hn hrec S hS₂'⟩

/-- The types typed in a signature whose entries have their meaning, and strictly positive in the
variables with a position, are read by the graph of the nestings of the equality at their
nestings, with one equality of their terms, given the soundness of the typing. -/
theorem NestReads.readsNested (hS : TypingSound sig ι) (hd : sig.Distinct) (n : Nat) (sT : Quality)
    {sigT : Signature} (hent : sig.ValidEntries ι sigT) :
    ReadsNested sig ι (NestReads sig ι n sT) sigT :=
  ReadsInstances.readsNested hS hent ((nestReading sig ι hd n sT).readsInstances hS sigT hent)

end

end Sic.Core
