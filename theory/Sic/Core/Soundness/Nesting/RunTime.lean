module

public import Sic.Core.Soundness.Nesting.Reading
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.RunTime.Nesting
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

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

-- ADE: none.
/-- The graph of the nestings of run time at the level `n` reads two closed types, each at its
nesting, with the same relation of run time of their terms, for the program `P`. -/
def RunNestReads (sig : Signature) (ι : Interpretation) (P : Program) (n : Nat)
    (τ₁ τ₂ : Nest RunNestLeaf) (A₁ A₂ : Term 0 []) : Prop :=
  ∃ R, RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₁ A₁ R ∧
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ₂ A₂ R

-- ADE: none.
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

/-! ## Destructors Read by the Graph of the Nestings of Run Time -/

/-- A destructor whose arguments are equal telescopes and whose results are equal types at two
equal closed substitutions, and are the same at two other substitutions, followed by destructors
that the graph of the nestings of run time reads with one relation at these, for each pair of equal
abstractions for it, is read with them by the graph with one relation, as a destructor whose result
has no position: the relation of its results and that of the destructors after it are defined from
the graph at the first substitution, which gives one at most. -/
theorem RunNestDesReads.of_plain_head (hd : sig.Distinct) {n : Nat} {κ κ₁ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting RunNestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
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
      RunNestDesReads sig ι P n (Nesting.lift (e := .secondOrder ps ψ) @ν₁)
        (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁)
        (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂)) :
    RunNestDesReads sig ι P n @ν₁ @ν₂ (.cons (d := d) p q ς Θ B ψ ds) @θ₁' @θ₂' := by
  intro D hcase
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
    Nat.forall_lt (levelRel_run_unique hd) _
  obtain ⟨i, hi⟩ := hcase d List.mem_cons_self
  have hcase' := fun d' (hd' : d' ∈ ns) => hcase d' (List.mem_cons_of_mem _ hd')
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  obtain ⟨RΘ, hRT₁, hRT₂⟩ := hΘ.runTelRel hd P rfl
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) κ.level.closedValue)
    (fun _ => .plain) hT₁
  have hκn : κ₁.level.closedValue ≤ n := Nat.le_trans (hκ.2 Fin.elim0) hn
  have hκs : κ₁.quality ≤ Quality.type := fun h => nomatch h
  -- The results at the first substitution and equal arguments are equal types.
  have hBB : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst))
        (B.subst (Subst.append θ₁ us.toSubst)) (.sort κ₁) := fun ts us hts =>
    have huu := hSp.trans (hSp.symm hts) hts
    (hB _ _ ((hT ts us).1 hts)).trans (hB _ _ ((hT us us).1 huu)).symm
  let F : Terms 0 [] → TermRel := fun tms t u => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ w F', Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
      FieldRel sig ι n (fun m _ => levelRel sig ι m) .type w F' ∧ F' t u
  have hFeq : ∀ (ts : Args 0 [] ps) w F₀,
      Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w →
      FieldRel sig ι n (fun m _ => levelRel sig ι m) .type w F₀ →
      F ts.terms = F₀ := fun ts w F₀ hw hF₀ =>
    funext fun t => funext fun u => propext
      ⟨fun ⟨ts', hts', w', F', hw', hF', h'⟩ => by
        cases Args.terms_inj hts'
        cases Computesι.det hd hw hw'
        exact (FieldRel.unique hd ihm hF' _ _ hF₀ t u).1 h',
      fun h' => ⟨ts, rfl, w, F₀, hw, hF₀, h'⟩⟩
  -- A type equal to the result at the first substitution and the arguments `ts` has the
  -- equality `F ts`.
  have hres : ∀ (ts : Args 0 [] ps) (A : Term 0 []),
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst)) A (.sort κ₁) →
      (∃ w, Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) .type w (F ts.terms)) ∧
      ∃ v, Computesι sig ι A v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) .type v (F ts.terms) :=
    fun ts A hA => by
      obtain ⟨w₁, w₂, F₀, hw₁, hw₂, hF₁, hF₂, -⟩ := hA.fieldRel hκs hκn
      rw [hFeq ts w₁ F₀ hw₁ hF₁]
      exact ⟨⟨w₁, hw₁, hF₁⟩, w₂, hw₂, hF₂⟩
  let R : Terms 0 [] → RunRel := fun tms H t a => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ w R', Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w R' ∧ R' H t a
  have hReq : ∀ (ts : Args 0 [] ps) w R₀,
      Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w →
      RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w R₀ →
      R ts.terms = R₀ := fun ts w R₀ hw hR₀ =>
    funext fun H => funext fun t => funext fun a => propext
      ⟨fun ⟨ts', hts', w', R', hw', hR', h'⟩ => by
        cases Args.terms_inj hts'
        cases Computesι.det hd hw hw'
        exact (RunFieldRel.congr hd ihm ih hR' _ hR₀ H t a).1 h',
      fun h' => ⟨ts, rfl, w, R₀, hw, hR₀, h'⟩⟩
  -- A type equal to the result at the first substitution and the arguments `ts` has the
  -- relation of run time `R ts`.
  have hrun : ∀ (ts : Args 0 [] ps) (A : Term 0 []),
      ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ ts.toSubst)) A (.sort κ₁) →
      (∃ w, Computesι sig ι (B.subst (Subst.append θ₁ ts.toSubst)) w ∧
        RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) w (R ts.terms)) ∧
      ∃ v, Computesι sig ι A v ∧
        RunFieldRel sig ι P n (fun m _ => levelRel sig ι m) v (R ts.terms) :=
    fun ts A hA => by
      obtain ⟨w₁, w₂, R₀, hw₁, hw₂, hR₁, hR₂⟩ := hA.runFieldRel P hκn
      rw [hReq ts w₁ R₀ hw₁ hR₁]
      exact ⟨⟨w₁, hw₁, hR₁⟩, w₂, hw₂, hR₂⟩
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
  let G : Term 0 (Scope.extend [] ps.length) → RunObsRel := fun f H o a => ∃ S',
    RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' ∧ S' H o a
  have hGeq : ∀ f S', RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D
      (Nesting.lift (e := .secondOrder ps ψ) @ν₁) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f) S' → G f = S' := fun f S' hS' =>
    funext fun H => funext fun o => funext fun a => propext
      ⟨fun ⟨_, h', hs⟩ => (RunNestDesRel.unique hd ihm ih h' _ hS' H o a).1 hs,
        fun hs => ⟨S', hS', hs⟩⟩
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
        obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts htt)
        have hP := FieldRel.isPer hd ihm hF
        exact hP.trans (hP.symm (hf ts ts htt)) (hf ts us hts)
      obtain ⟨S₁, h₁, h₂⟩ := hds f₁ f₂ (hcond f₁ f₂ hf) D hcase'
      obtain ⟨S₂, h₁', h₂'⟩ := hds f₂ f₂ (hcond f₂ f₂ hf₂) D hcase'
      rw [hGeq f₁ S₁ h₁, hGeq f₂ S₂ h₁']
      exact RunNestDesRel.unique hd ihm ih h₂ _ h₂' H o a
  refine ⟨_, .cons hi hν₁ (hΘ₁ ▸ hT₁.levelLe hn) (hΘ₁ ▸ hRT₁.levelLe hn) F R
      (fun ts hts => ?_) (fun ts hts => ?_) G (fun f hf => (hG f hf).1) hresp,
    .cons hi hν₂ (hΘ₂ ▸ hT₂.levelLe hn) (hΘ₂ ▸ hRT₂.levelLe hn) F R
      (fun ts hts => ?_) (fun ts hts => ?_) G (fun f hf => (hG f hf).2) hresp⟩
  · obtain ⟨⟨w, hw, hF⟩, -⟩ := hres ts _ (hBB ts ts hts)
    rw [hB₁]
    exact .plain hw hF
  · obtain ⟨⟨w, hw, hR⟩, -⟩ := hrun ts _ (hBB ts ts hts)
    rw [hB₁]
    exact .plain hw hR
  · obtain ⟨-, v, hv, hF⟩ := hres ts _ (hB _ _ ((hT ts ts).1 hts))
    rw [hB₂]
    exact .plain hv hF
  · obtain ⟨-, v, hv, hR⟩ := hrun ts _ (hB _ _ ((hT ts ts).1 hts))
    rw [hB₂]
    exact .plain hv hR

/-- A destructor whose arguments are equal telescopes at two equal closed substitutions, and are
the same at two other substitutions, at which the graph of the nestings of run time reads its
results at their nestings with one relation, at equal arguments, followed by destructors that the
graph reads with one relation at these substitutions, for each pair of abstractions for it, is read
with them by the graph with one relation, as a destructor whose result has a position. -/
theorem RunNestDesReads.of_nested_head (hd : sig.Distinct) {n : Nat} {κ : Universe 0}
    (hn : κ.level.closedValue ≤ n) {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter}
    {p q ς : Grade} {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)}
    {ψ : ResultOwnership Grade ps.length} {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns}
    {ν₁ ν₂ : Nesting RunNestLeaf Γ} {θ₁ θ₂ θ₁' θ₂' : Subst 0 [] Γ}
    (hν₁ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁) ≠ .plain)
    (hν₂ : B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂) ≠ .plain)
    (hΘ : ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂))
    (hΘ₁ : Θ.subst θ₁' = Θ.subst θ₁) (hΘ₂ : Θ.subst θ₂' = Θ.subst θ₂)
    (hB : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
      RunNestReads sig ι P n (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₂))
        (B.subst (Subst.append θ₁' τ₁)) (B.subst (Subst.append θ₂' τ₂)))
    (hds : ∀ f₁ f₂, RunNestDesReads sig ι P n (Nesting.lift (e := .secondOrder ps ψ) @ν₁)
      (Nesting.lift (e := .secondOrder ps ψ) @ν₂) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ₁' f₁)
      (Subst.snoc (e := .secondOrder ps ψ) θ₂' f₂)) :
    RunNestDesReads sig ι P n @ν₁ @ν₂ (.cons (d := d) p q ς Θ B ψ ds) @θ₁' @θ₂' := by
  intro D hcase
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
  have ih : ∀ m, m < n → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
    Nat.forall_lt (levelRel_run_unique hd) _
  obtain ⟨i, hi⟩ := hcase d List.mem_cons_self
  have hcase' := fun d' (hd' : d' ∈ ns) => hcase d' (List.mem_cons_of_mem _ hd')
  obtain ⟨SΘ, hT₁, hT₂⟩ := hΘ.telRel hd
  obtain ⟨RΘ, hRT₁, hRT₂⟩ := hΘ.runTelRel hd P rfl
  have hT := TelRel.eqSubst_iff hd hT₁ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain)
  let R : Terms 0 [] → RunRel := fun tms H t a => ∃ ts : Args 0 [] ps, ts.terms = tms ∧
    ∃ R', RunNestRel sig ι P n (fun m _ => levelRel sig ι m)
      (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
      (B.subst (Subst.append θ₁' ts.toSubst)) R' ∧ R' H t a
  have hReq : ∀ (ts : Args 0 [] ps) R₀,
      RunNestRel sig ι P n (fun m _ => levelRel sig ι m)
        (B.nest (fun _ => none) (Nesting.liftN ps.length @ν₁))
        (B.subst (Subst.append θ₁' ts.toSubst)) R₀ → R ts.terms = R₀ := fun ts R₀ hR₀ =>
    funext fun H => funext fun t => funext fun a => propext
      ⟨fun ⟨ts', hts', R', hR', h'⟩ => by
        cases Args.terms_inj hts'
        exact (RunNestRel.unique hd ihm ih hR' _ hR₀ H t a).1 h',
      fun h' => ⟨ts, rfl, R₀, hR₀, h'⟩⟩
  -- The destructors after it have one relation, whatever the abstractions for it.
  let f₀ : Term 0 (Scope.extend [] ps.length) := .sort ⟨.type, .zero⟩
  obtain ⟨G, h₀₁, h₀₂⟩ := hds f₀ f₀ D hcase'
  refine ⟨_, .nested hi hν₁ (hΘ₁ ▸ hT₁.levelLe hn) (hΘ₁ ▸ hRT₁.levelLe hn) R
      (fun ts hts => ?_) G (fun f => ?_),
    .nested hi hν₂ (hΘ₂ ▸ hT₂.levelLe hn) (hΘ₂ ▸ hRT₂.levelLe hn) R
      (fun ts hts => ?_) G (fun f => ?_)⟩
  · obtain ⟨R', h₁, -⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hReq ts R' h₁]
    exact h₁
  · obtain ⟨S, h₁, h₂⟩ := hds f f₀ D hcase'
    have hSG : S = G := funext fun H => funext fun o => funext fun a => propext
      (RunNestDesRel.unique hd ihm ih h₂ _ h₀₂ H o a)
    exact hSG ▸ h₁
  · obtain ⟨R', h₁, h₂⟩ := hB _ _ ((hT ts ts).1 hts)
    rw [hReq ts R' h₁]
    exact h₂
  · obtain ⟨S, h₁, h₂⟩ := hds f₀ f D hcase'
    have hSG : S = G := funext fun H => funext fun o => funext fun a => propext
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
    ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue ≤ n := by
  have hu : ∀ m R, RunUnivRel sig ι P m (fun k _ => levelRel sig ι k) (.inst D qs ls ps as) R →
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
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue = m :=
    fun m b hb => by
      cases hb with
      | data h' _ _ _ hv' => exact (hd.inst_data_codata h' h hv'.symm).elim
      | codata h' _ _ _ hv' _ hn' =>
        obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv'
        subst hD hqs hls hps
        obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h'
        exact hn'
  cases hR with
  | univ hu' => exact Nat.le_of_eq (hu n _ hu')
  | univBelow m hm hu' =>
    exact Nat.le_trans (Nat.le_of_eq (hu m _ (levelRel_run_iff.1 hu'))) (Nat.le_of_lt hm)
  | prop hb' => exact Nat.le_of_eq (hb n _ hb')
  | propBelow m hm hb' =>
    exact Nat.le_trans (Nat.le_of_eq (hb m _ (levelRel_prop_iff.1 hb'))) (Nat.le_of_lt hm)

/-! ## Reading of Run Time -/

-- ADE: none.
/-- The reading of the graph of the nestings of run time at the level `n`, for the program `P`, of
the sorts whose level `n` bounds: two types, or the destructors of a codata type at two
substitutions, are read with one relation of run time. -/
def runNestReading (sig : Signature) (ι : Interpretation) (hd : sig.Distinct) (P : Program)
    (n : Nat) : Reading sig ι RunNestLeaf Unit where
  rd _ := RunNestReads sig ι P n
  dr _ _ _ ν₁ ν₂ ds θ₁ θ₂ := RunNestDesReads sig ι P n @ν₁ @ν₂ ds @θ₁ @θ₂
  ok _ κ := κ.level.closedValue ≤ n
  plain := fun hn hκ h => by
    obtain ⟨w₁, w₂, R, hc₁, hc₂, hR₁, hR₂⟩ :=
      h.runFieldRel P (Nat.le_trans (hκ.2 Fin.elim0) hn)
    exact ⟨R, .plain hc₁ hR₁, .plain hc₂ hR₂⟩
  nil := fun _ _ => ⟨fun _ _ _ => True, .nil, .nil⟩
  plain_head := fun hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁ hB₂ hds =>
    RunNestDesReads.of_plain_head hd hn hν₁ hν₂ hΘ hΘ₁ hΘ₂ hκ hB hB₁ hB₂ hds
  nested_head := fun hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds =>
    RunNestDesReads.of_nested_head hd hn hν₁ hν₂ hΘ hΘ₁ hΘ₂ hB hds
  inst := by
    intro _ decl D T qs ls ps as₁ as₂ as₁' as₂' νs₁ νs₂ hT hq hl hp hrec hadm hr
    obtain ⟨RE, hrE, -⟩ := hr
    cases hrE with
    | plain hc hR =>
      cases Computesι.det hd (Whnf.inst D qs _ ps _).computes hc
      have hn := RunFieldRel.codata_inv hd hT hq hl hp hR
      have hls : ∀ i, (Level.ofNat ((ls.getFin hl i).closedValue) : Level 0) ≈ ls.getFin hl i :=
        fun i => Level.ofNat_closedValue _
      refine ⟨(), Nat.le_trans (Nat.le_of_eq (Level.closedValue_subst_equiv hls _)) hn,
        fun hdr => ?_⟩
      obtain ⟨S, hS₁, hS₂⟩ := hdr D fun d hdm =>
        hT.2.2 ▸ Signature.destructorCase_of_mem hT.1 hT.2.1 hdm
      have hinv : ∀ m, m < n → (levelRel sig ι m).LevelInvariant :=
        Nat.forall_lt (levelRel_levelInvariant hd) _
      have hrel : ∀ ν : Nesting RunNestLeaf decl.scope,
          Nesting.Rel (fun x y => Term.LevelEquiv x.1 y.1 ∧ x.2 = y.2) @ν @ν :=
        fun ν _ x => Nest.rel₃_refl (fun _ => ⟨Term.LevelEquiv.refl _, rfl⟩) _
      have hS₁' := RunNestDesRel.levelEquiv hd hinv hS₁
        (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
      have hS₂' := RunNestDesRel.levelEquiv hd hinv hS₂
        (Destructors.substLevels_levelEquiv hls (T.body _)) (Subst.LevelEquiv.refl _) (hrel _)
      cases hκ : (decl.sort (.ofLists qs ps hq hp)).quality with
      | type =>
        exact ⟨_, .codata hT hq hl hp rfl hκ hn hrec S hS₁',
          .codata hT hq hl hp rfl hκ hn hrec S hS₂'⟩
      | prop =>
        exact ⟨_, .codataProp hT hq hl hp rfl hadm hκ hn hrec,
          .codataProp hT hq hl hp rfl hadm hκ hn hrec⟩

-- ADE: none.
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
