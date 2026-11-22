module

public import Sic.Core.Meaning.RunTime.Properties
public import Sic.Core.Soundness.Nesting.Reading
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.RunTime.Nesting
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Run Time of the Nested Types

The graph of the nestings of run time of annex 21 of RFC 36 is a reading of the nested types: it
reads two closed types, each at its nesting, with the same relation of run time of their terms.
A type that is strictly positive in variables is then read by the graph at any closed types given
for these variables, when the graph reads them at their nestings: the relation of run time of its
terms is the same at two substitutions, as the meaning of a nested field of a block asks, for each
program and whatever the relations given at its positions.

The graph reads the equality of the arguments of a destructor, and that of its result when it has
no position, which the meaning of the destructor gives at the first pair of substitutions: it reads
no equality at a result that has a position.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Types Read by the Graph of the Nestings of Run Time -/

/-- The graph of the nestings of run time at the level `n` reads two closed types, each at its
nesting, with the same relation of run time of their terms, for the program `P`. -/
def RunNestReads (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (τ₁ τ₂ : Nest RunNestLeaf) (A₁ A₂ : Term 0 []) : Prop :=
  ∃ R, RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₁ A₁ R ∧
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₂ A₂ R

/-- The graph of the nestings of run time at the level `n` reads the destructors of a codata type
at two nestings of their scope and two closed substitutions, with the same relation of run time of
the observations by them, for the program `P`, whatever the name of the type, which gives them
their cases. -/
def RunNestDesReads (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat) {Γ : Scope}
    {ns : List Name} (ν₁ ν₂ : Nesting RunNestLeaf Γ) (ds : Destructors 0 Γ ns)
    (θ₁ θ₂ : Subst 0 [] Γ) : Prop :=
  ∀ D, (∀ d ∈ ns, ∃ i, sig.destructorCase D d = some i) →
    ∃ S, RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₁ ds @θ₁ S ∧
      RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν₂ ds @θ₂ S

/-- The sorts in which the graph of the nestings of run time at the level `n` reads: those whose
level `n` bounds. -/
def RunNestReadsOk (n : Nat) (_ : Unit) (κ : Universe 0) : Prop :=
  κ.level.closedValue ≤ n

/-! ## Destructors Read by the Graph of the Nestings of Run Time -/

/-- The clause `Reading.PlainHead` of the graph of the nestings of run time: a destructor whose
arguments are equal telescopes and whose results are equal types at two equal closed substitutions,
and are the same at two other substitutions, followed by destructors that the graph of the nestings
of run time reads with one relation at these, for each pair of equal abstractions for it, is read
with them by the graph with one relation, as a destructor whose result has no position: the relation
of its results and that of the destructors after it are defined from the graph at the first
substitution, which gives one at most. -/
theorem RunNestDesReads.of_plain_head (hd : sig.Distinct) {n : Nat} :
    Reading.PlainHead sig ι (fun _ => @RunNestDesReads sig ι P n) (RunNestReadsOk n) := by
  intro _ κ κ₁ hn Γ d ns ps p q ς Θ B ψ ds ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁ hB₂
    hds
  intro D hcase
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
    Nat.forall_lt (levelRel_run_unique hd) _
  obtain ⟨i, hi⟩ := hcase d List.mem_cons_self
  have hcase' := fun d' (hd' : d' ∈ ns) => hcase d' (List.mem_cons_of_mem _ hd')
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  obtain ⟨RΘ, hRT₁, hRT₂⟩ := hΘ.runTelRel hd P rfl
  have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) κ.level.closedValue)
    (fun _ => .plain) hT₁
  have hκn : κ₁.level.closedValue ≤ n := Nat.le_trans (hκ.2 Fin.elim0) hn
  have hκs : κ₁.quality ≤ Quality.type := fun h => nomatch h
  obtain ⟨hF₁, hF₂, -, hcond⟩ := FieldRel.atArgs_head hd hT₁ hκs hκn hB
  obtain ⟨hR₁, hR₂⟩ := RunFieldRel.atArgs_head hd P hT₁ hκn hB
  let F : Terms 0 [] → TermRel := FieldRel.atArgs sig ι n .type fun ts =>
    B.subst (Subst.append θ₁ ts.toSubst)
  let R : Terms 0 [] → RunRel := RunFieldRel.atArgs sig ι P n fun ts =>
    B.subst (Subst.append θ₁ ts.toSubst)
  let G : Term 0 (Scope.extend [] ps.length) → RunObsRel := Math.Rel₃.ofGraph fun f S' =>
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S'
  have hGeq : ∀ f S', _ → G f = S' := fun _ _ hS' =>
    Math.Rel₃.ofGraph_eq hS' fun _ h' => RunNestDesRel.unique hd ihm ih h' _ hS'
  have hG : ∀ f, AbstractionRel SΘ F f f →
      RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D
        (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) (G f) ∧
      RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D
        (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₂' f) (G f) := fun f hf => by
    obtain ⟨S', h₁, h₂⟩ := hds f f (hcond f f hf) D hcase'
    rw [hGeq f S' h₁]
    exact ⟨h₁, h₂⟩
  -- The destructors after it have the same relation at equal abstractions, which the destructors
  -- at the second substitution relate to the second one, with one relation for each pair.
  have hresp : ∀ f₁ f₂, AbstractionRel SΘ F f₁ f₂ → ∀ H o a, G f₁ H o a ↔ G f₂ H o a :=
    fun f₁ f₂ hf H o a => by
      have hf₂ : AbstractionRel SΘ F f₂ f₂ := fun ts us hts => by
        have htt := hSp.trans hts (hSp.symm hts)
        obtain ⟨⟨w, hw⟩, hF⟩ := hF₁ ts htt
        have hP := FieldRel.isPer hd ihm (hF w hw)
        exact hP.trans (hP.symm (hf ts ts htt)) (hf ts us hts)
      obtain ⟨S₁, h₁, h₂⟩ := hds f₁ f₂ (hcond f₁ f₂ hf) D hcase'
      obtain ⟨S₂, h₁', h₂'⟩ := hds f₂ f₂ (hcond f₂ f₂ hf₂) D hcase'
      rw [hGeq f₁ S₁ h₁, hGeq f₂ S₂ h₁']
      exact RunNestDesRel.unique hd ihm ih h₂ _ h₂' H o a
  refine ⟨_, .cons hi hν₁ (hΘ₁ ▸ hT₁.levelLe hn) (hΘ₁ ▸ hRT₁.levelLe hn) F R
      (fun ts hts => ?_) (fun ts hts => ?_) G (fun f hf => (hG f hf).1) hresp,
    .cons hi hν₂ (hΘ₂ ▸ hT₂.levelLe hn) (hΘ₂ ▸ hRT₂.levelLe hn) F R
      (fun ts hts => ?_) (fun ts hts => ?_) G (fun f hf => (hG f hf).2) hresp⟩
  · obtain ⟨⟨w, hw⟩, hF⟩ := hF₁ ts hts
    rw [hB₁]
    exact .plain hw (hF w hw)
  · obtain ⟨⟨w, hw⟩, -⟩ := hF₁ ts hts
    rw [hB₁]
    exact .plain hw (hR₁ ts hts w hw)
  · obtain ⟨⟨v, hv⟩, hF⟩ := hF₂ ts hts
    rw [hB₂]
    exact .plain hv (hF v hv)
  · obtain ⟨⟨v, hv⟩, -⟩ := hF₂ ts hts
    rw [hB₂]
    exact .plain hv (hR₂ ts hts v hv)

/-- The head of a destructor whose result has a position, whose arguments are a closed telescope
`Θ` of the graph of a sort, with the equality `SΘ`, and whose results `B` the graph of the nestings
of run time reads with one relation at equal arguments, at two substitutions `θ₁` and `θ₂` and at
two nestings `τ₁` and `τ₂`: the graph reads its results at arguments that `SΘ` relates to
themselves, at both substitutions, with the relation at these arguments that it gives at `θ₁`. -/
theorem RunNestRel.atArgs_head (hd : sig.Distinct) (P : Program) {m n : Nat} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {SΘ : FieldsRel}
    (hT₁ : TelRel sig ι m (fun k _ => levelRel sig ι k) .type (fun _ => .plain) Θ SΘ) {Γ : Scope}
    {B : Term 0 (Γ.extend ps.length)} {τ₁ τ₂ : Nest RunNestLeaf} {θ₁ θ₂ : Subst 0 [] Γ}
    (hB : ∀ σ₁ σ₂, EqSubst sig ι (Context.empty.append Θ) σ₁ σ₂ →
      RunNestReads sig ι P n τ₁ τ₂ (B.subst (Subst.append θ₁ σ₁))
        (B.subst (Subst.append θ₂ σ₂))) :
    (∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      RunNestRel sig ι P n (fun k _ => levelRel sig ι k) τ₁ (B.subst (Subst.append θ₁ ts.toSubst))
        (RunNestRel.atArgs sig ι P n τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst))
          ts.terms)) ∧
    ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      RunNestRel sig ι P n (fun k _ => levelRel sig ι k) τ₂ (B.subst (Subst.append θ₂ ts.toSubst))
        (RunNestRel.atArgs sig ι P n τ₁ (fun ts => B.subst (Subst.append θ₁ ts.toSubst))
          ts.terms) := by
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
    Nat.forall_lt (levelRel_run_unique hd) _
  have hT := TelRel.eqSubst_iff_plain hd hT₁
  have heq := fun (ts : Args 0 [] ps) R' =>
    RunNestRel.atArgs_eq (A := fun ts => B.subst (Subst.append θ₁ ts.toSubst)) (ts := ts) (R := R')
      (τ := τ₁) hd ihm ih
  refine ⟨fun ts hts => ?_, fun ts hts => ?_⟩
  · obtain ⟨R', h₁, -⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [heq ts R' h₁]
    exact h₁
  · obtain ⟨R', h₁, h₂⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [heq ts R' h₁]
    exact h₂

/-- The clause `Reading.NestedHead` of the graph of the nestings of run time: a destructor whose
arguments are equal telescopes at two equal closed substitutions, and are the same at two other
substitutions, at which the graph of the nestings of run time reads its results at their nestings
with one relation, at equal arguments, followed by destructors that the graph reads with one
relation at these substitutions, for each pair of abstractions for it, is read with them by the
graph with one relation, as a destructor whose result has a position. -/
theorem RunNestDesReads.of_nested_head (hd : sig.Distinct) {n : Nat} :
    Reading.NestedHead sig ι (fun _ => RunNestReads sig ι P n) (fun _ => @RunNestDesReads sig ι P n)
      (RunNestReadsOk n) := by
  intro _ κ hn Γ d ns ps p q ς Θ B ψ ds ν₁ ν₂ θ₁ θ₂ θ₁' θ₂' hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds
  intro D hcase
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
    Nat.forall_lt (levelRel_run_unique hd) _
  obtain ⟨i, hi⟩ := hcase d List.mem_cons_self
  have hcase' := fun d' (hd' : d' ∈ ns) => hcase d' (List.mem_cons_of_mem _ hd')
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  obtain ⟨RΘ, hRT₁, hRT₂⟩ := hΘ.runTelRel hd P rfl
  obtain ⟨hR₁, hR₂⟩ := RunNestRel.atArgs_head hd P hT₁ hB
  let R : Terms 0 [] → RunRel := RunNestRel.atArgs sig ι P n
    (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁)) fun ts =>
      B.subst (Subst.append θ₁' ts.toSubst)
  -- The destructors after it have one relation, whatever the abstractions for it.
  let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
  obtain ⟨G, h₀₁, h₀₂⟩ := hds f₀ f₀ D hcase'
  refine ⟨_, .nested hi hν₁ (hΘ₁ ▸ hT₁.levelLe hn) (hΘ₁ ▸ hRT₁.levelLe hn) R hR₁ G (fun f => ?_),
    .nested hi hν₂ (hΘ₂ ▸ hT₂.levelLe hn) (hΘ₂ ▸ hRT₂.levelLe hn) R hR₂ G (fun f => ?_)⟩
  · obtain ⟨S, h₁, h₂⟩ := hds f f₀ D hcase'
    have hSG : S = G := Math.Rel₃.ext_of_iff fun H o a =>
      (RunNestDesRel.unique hd ihm ih h₂ _ h₀₂ H o a)
    exact hSG ▸ h₁
  · obtain ⟨S, h₁, h₂⟩ := hds f₀ f D hcase'
    have hSG : S = G := Math.Rel₃.ext_of_iff fun H o a =>
      (RunNestDesRel.unique hd ihm ih h₁ _ h₀₁ H o a)
    exact hSG ▸ h₂

/-! ## Instances of Codata Types -/

/-- An instance of a codata type that has a relation of run time of the types of the fields at the
level `n` lives at a level that `n` bounds. -/
theorem RunFieldRel.codata_inv (hd : sig.Distinct) {n : Nat} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] decl.scope}
    (h : sig.HasCodataType D decl T) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) {R : RunRel}
    (hR : RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) (.inst D qs ls ps as) R) :
    (decl.sortAt (.ofLists qs ps hq hp) (ls.getFin hl)).level.closedValue ≤ n := by
  have hu : ∀ m R, RunUnivRel sig ι P m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R →
      (decl.sortAt (.ofLists qs ps hq hp) (ls.getFin hl)).level.closedValue = m :=
    fun m R hu => by
      cases hu with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' _ hn' =>
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
        exact hn'
  have hb : ∀ m b, PropRel sig ι m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) b →
      (decl.sortAt (.ofLists qs ps hq hp) (ls.getFin hl)).level.closedValue = m :=
    fun m b hb => by
      cases hb with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' _ hn' =>
        obtain ⟨rfl, rfl, -, rfl, rfl, rfl, -⟩ := hd.codataInst_unique h h' hv'
        exact hn'
  cases hR with
  | univ hu' => exact Nat.le_of_eq (hu n _ hu')
  | univBelow m hm hu' =>
    exact Nat.le_trans (Nat.le_of_eq (hu m _ (levelRel_run_iff.1 hu'))) (Nat.le_of_lt hm)
  | prop hb' => exact Nat.le_of_eq (hb n _ hb')
  | propBelow m hm hb' =>
    exact Nat.le_trans (Nat.le_of_eq (hb m _ (levelRel_prop_iff.1 hb'))) (Nat.le_of_lt hm)

/-! ## Reading of Run Time -/

/-- The reading of the graph of the nestings of run time at the level `n`, for the program `P`, of
the sorts whose level `n` bounds: two types, or the destructors of a codata type at two
substitutions, are read with one relation of run time. -/
def runNestReading (sig : Signature) (ι : Interpretation) (hd : sig.Distinct) (P : Program)
    (n : Nat) : Reading sig ι RunNestLeaf Unit where
  rd _ := RunNestReads sig ι P n
  dr _ := @RunNestDesReads sig ι P n
  ok := RunNestReadsOk n
  plain := fun hn hκ h => by
    obtain ⟨w₁, w₂, R, hc₁, hc₂, hR₁, hR₂⟩ :=
      h.runFieldRel P (Nat.le_trans (hκ.2 Fin.elim0) hn)
    exact ⟨R, .plain hc₁ hR₁, .plain hc₂ hR₂⟩
  nil := fun _ _ => ⟨fun _ _ _ => True, .nil, .nil⟩
  plain_head := RunNestDesReads.of_plain_head hd
  nested_head := RunNestDesReads.of_nested_head hd
  inst := by
    intro _ decl D T qs ls ps as₁ as₂ as₁' as₂' νs₁ νs₂ hT hq hl hp hrec hadm hr
    obtain ⟨RE, hrE, -⟩ := hr
    cases hrE with
    | plain hc hR =>
      cases Computesι.det hd (Whnf.inst D qs _ ps _).computes hc
      have hn := RunFieldRel.codata_inv hd hT hq hl hp hR
      refine ⟨(), Nat.le_trans (Nat.le_of_eq (decl.sort_atLevels_closedValue hq hl hp)) hn,
        fun hdr => ?_⟩
      obtain ⟨S, hS₁, hS₂⟩ := hdr D fun d hdm =>
        hT.2.2 ▸ Signature.destructorCase_of_mem hT.1 hT.2.1 hdm
      have hS₁' := RunNestDesRel.substLevels_of_atLevels hd hS₁
      have hS₂' := RunNestDesRel.substLevels_of_atLevels hd hS₂
      cases hκ : (decl.sort (.ofLists qs ps hq hp)).quality with
      | type =>
        exact ⟨_, .codata hT hq hl hp rfl hκ hn hrec S hS₁',
          .codata hT hq hl hp rfl hκ hn hrec S hS₂'⟩
      | prop =>
        exact ⟨_, .codataProp hT hq hl hp rfl hadm hκ hn hrec,
          .codataProp hT hq hl hp rfl hadm hκ hn hrec⟩

/-- The types typed in a signature whose entries have their meaning, and strictly positive in the
variables with a position, are read by the graph of the nestings of run time at their nestings,
with one relation of run time of their terms, for each program, given the soundness of the
typing. -/
theorem RunNestReads.readsNested (hS : TypingSound sig ι) (hd : sig.Distinct) (P : Program)
    (n : Nat) {sigT : Signature} (hent : sig.ValidEntries ι sigT) :
    ReadsNested sig ι (fun _ : Unit => RunNestReads sig ι P n) sigT :=
  ReadsInstances.readsNested hS hent ((runNestReading sig ι hd P n).readsInstances hS sigT hent)

end

end Sic.Core
