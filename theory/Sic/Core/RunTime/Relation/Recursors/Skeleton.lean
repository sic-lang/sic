module

public import Sic.Core.RunTime.Relation.Recursors.Nested
public import Sic.Core.Soundness.Recursors.Nested
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Syntax.Signature
import Sic.Math.Nat

/-!
# Run Time of the Nested Results of an Erased Recursor

The recursive result of a nested field at run time, `n.Ξ`, when the recursor is of the multiplicity
`0`: the recursor then runs on the term of the skeleton of its type, whose nested fields are `↯`,
and the corecursor of the shape observes no field, since the result of each of its branches is the
recursor on the term of the skeleton of its motive, or the corecursor of the next lifting.
The fields of the term of the skeleton are related by the equality of the block rather than by its
relation of run time, so that the proof is an induction on the graph of the nestings of the
equality, beside the one on the graph of run time when the recursor is used.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable (sig : Signature) (ι : Interpretation) (P : Program) (ρ₁ : Lifting 0 [] [])
  (φ : Name → Term 0 [.var]) (block : Name → Option Shape.Motive) (ϱ : Multiplicity) {m₀ : Nat}
  (Ns₀ : TargetBranches m₀) (E₀ : List Nat) (Hb : Heap)

-- ADE: none.
/-- The leaf `x` given at a position that holds the type `D` of the block, for the recursor of the
multiplicity `0`: the recursor `rec_0 · ◀ ϱ with N̄₀` of the shape of `D`, on any path, which it
does not evaluate, gives a value related to the result of a term that `x.2` relates, at the motive
of `D` at this term, in any environment that binds the variables of the branches renamed as `E₀`
binds them, from any heap that extends the heap `Hb` in which the cells of `E₀` live. -/
def SkeletonResultLeaf (D : Name) (x : NestLeaf) : Prop :=
  ∀ b ms, ρ₁.block D = some b → block D = some ms → ∀ t t', x.2 t t' → ∀ {m : Nat}
    (g : TargetRen m m₀) (E : List Nat), (∀ x : Fin m₀, E[(g x : Nat)]? = E₀[(x : Nat)]?) →
    ∀ (H : Heap) (O : Target m), Hb.Extends H → ∀ ϖ H₁, H.Extends H₁ →
      ∃ w H₂ tr, Eval P ϖ H₁ E (ms.next.body .zero ϱ O (Ns₀.rename g)) w H₂ tr ∧
        H₁.Extends H₂ ∧
        RunsAs sig ι P H₂ ((φ D).subst₀ (Subst₀.single t)) w (b.motive.subst₀ (Subst₀.single t))

end

section

variable {sig : Signature} {ι : Interpretation} {P : Program} {v : Lifting.Variables}
  {ρ₁ : Lifting 0 [] []} {φ : Name → Term 0 [.var]} {block : Name → Option Shape.Motive}
  {ϱ : Multiplicity} {m₀ : Nat} {Ns₀ : TargetBranches m₀} {E₀ : List Nat} {Hb : Heap}

/-- The recursive result of the multiplicity `0` of a closed term at a position that holds a type of
the block runs as the leaf of the position says, for any relation of the path, which the body does
not evaluate. -/
theorem NestedRunsAt.skeleton_direct {D : Name} {x : NestLeaf}
    (hx : SkeletonResultLeaf sig ι P ρ₁ φ block ϱ Ns₀ E₀ Hb D x) (A : Term 0 []) {t t' : Term 0 []}
    (ht : x.2 t t') (R : RunRel) :
    NestedRunsAt sig ι P v ρ₁ φ block .zero ϱ Ns₀ E₀ Hb (.direct D) A t R := by
  intro e A' mr ms hres hL hsh _ _ m g E hE H O hHb _ ϖ H₁ hH₁
  cases hres with
  | block hD =>
    cases hL with
    | block hD' =>
      cases Option.some.inj (hD.symm.trans hD')
      exact hx _ ms hD hsh t t' ht g E hE H O hHb ϖ H₁ hH₁
    | inst _ _ hn => exact absurd rfl (hn _)
  | inst _ hn => exact absurd rfl (hn _)

mutual

-- ADE: none.
/-- The recursive result of the multiplicity `0` of a closed term that the equality of a type, by
the graph of the nestings, relates to a term, runs, for any relation of the path: its shape, on any
path, gives a value related to the result at the type lifted, in a signature whose names are
distinct and whose liftings are those of its types, in their order, when the shapes of the types of
the block follow `ρ₁`, and the relation at each position runs as the leaf of the position says and
does not read the computation. -/
theorem NestRel.skeletonRuns (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    {n : Nat} {sT s : Quality} {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F →
      Nest.All (fun x => LeafCongr sig ι sT x.2) τ →
      ∀ {ν : Nest Name}, Nest.Rel (SkeletonResultLeaf sig ι P ρ₁ φ block ϱ Ns₀ E₀ Hb) ν τ →
      ∀ t t', F t t' → ∀ R, NestedRunsAt sig ι P v ρ₁ φ block .zero ϱ Ns₀ E₀ Hb ν A t R
  | .plain _ _, _, _, hν, _, _, _, _ => by
    cases hν with
    | plain => exact NestedRunsAt.plain _ _ _
  | .direct _ _, _, _, hν, _, _, ht, _ => by
    cases hν with
    | direct hx => exact NestedRunsAt.skeleton_direct hx _ ht _
  | .codata (ls := ls) h hq hl hp hA _ _ _ hrec _ hS, hτ, _, hν, t, t', ht, R => by
    subst hA
    cases hν with
    | inst hνs =>
      cases hτ with
      | inst hτs =>
        obtain ⟨w₁, w₂, hc₁, -, o₁, o₂, hw₁, -, hSo⟩ := ht
        exact NestedRunsAt.inst (n := n) hd hord hlifts (fun h0 => (h0 rfl).elim) hb h hq hl hp hrec
          fun d p q ς ps₁ Ξ Θ B ψ hpos _ => by
            obtain ⟨SΘ, hΘ, hN⟩ := NestDesRel.skeletonRuns hd hord hlifts hb
              (hpos.substLevels (ls.getFin hl)) hS (Nesting.ofArgs_rel₃ hτs)
              (Nesting.ofArgs_rel₃ hνs) hSo (ObsEquiv.of_computes hd hc₁ hw₁)
              (funext fun _ => funext fun x => (hpos.obsSubst_posSubstLevels _ _ _ x).symm)
              (hpos.nest_substLevels _ _)
            obtain ⟨i, hi⟩ := h.2.2 ▸ Signature.destructorCase_of_mem h.1 h.2.1
              (List.mem_of_getElem? hpos.getElem?_index)
            exact ⟨SΘ, fun _ _ _ _ => False, i, hi, hΘ, fun h0 => (h0 rfl).elim,
              fun ts hts => hN ts hts _⟩
  | .codataProp (ls := ls) h hq hl hp hA _ _ hrec _ hS, hτ, _, hν, t, _, ht, R => by
    subst hA
    cases hν with
    | inst hνs =>
      cases hτ with
      | inst hτs =>
        obtain ⟨o, hSo⟩ := ht
        exact NestedRunsAt.inst (n := n) hd hord hlifts (fun h0 => (h0 rfl).elim) hb h hq hl hp hrec
          fun d p q ς ps₁ Ξ Θ B ψ hpos _ => by
            obtain ⟨SΘ, hΘ, hN⟩ := NestDesRel.skeletonRuns hd hord hlifts hb
              (hpos.substLevels (ls.getFin hl)) hS (Nesting.ofArgs_rel₃ hτs)
              (Nesting.ofArgs_rel₃ hνs) hSo (f₁ := t.observation _ _ _ _ _) (.inl rfl)
              (funext fun _ => funext fun x => (hpos.obsSubst_posSubstLevels _ _ _ x).symm)
              (hpos.nest_substLevels _ _)
            obtain ⟨i, hi⟩ := h.2.2 ▸ Signature.destructorCase_of_mem h.1 h.2.1
              (List.mem_of_getElem? hpos.getElem?_index)
            exact ⟨SΘ, fun _ _ _ _ => False, i, hi, hΘ, fun h0 => (h0 rfl).elim,
              fun ts hts => hN ts hts _⟩
termination_by structural h _ _ _ _ _ _ _ => h

-- ADE: none.
/-- At a position of a destructor in destructors that the graph of the nestings reads, at
instantiated levels, an observation `f₁` that computes as an observation that the equality of the
destructors relates to an observation, gives, at arguments of the destructor that the equality of
its telescope relates to themselves, a term whose recursive result of the multiplicity `0` runs at
its result: the destructors before it are equal abstractions, or have a result with a position, on
which the destructors after them do not depend. -/
theorem NestDesRel.skeletonRuns (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    {n : Nat} {sT s : Quality} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {nms : List Name} → {ds : Destructors 0 Γ nms} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : ds.Pos d p q ς Ξ Θ B ψ) →
      {ν' : Nesting NestLeaf Γ} → {θ : Subst 0 [] Γ} → {S : ObsRel} →
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν' ds @θ S →
      Nesting.All (fun x => LeafCongr sig ι sT x.2) @ν' → {ν : Nesting Name Γ} →
      Nesting.Rel (SkeletonResultLeaf sig ι P ρ₁ φ block ϱ Ns₀ E₀ Hb) @ν @ν' →
      {o₁ o₂ f₁ : Observations} → S o₁ o₂ → ObsEquiv sig ι s f₁ o₁ →
      ∀ {σ : (e : Scope.Entry) → Var Ξ e → Term 0 (Scope.extend [] e.params.length)},
      (σ = fun _ x => hpos.obsSubst f₁ θ x) → ∀ {νB : Nest Name},
      νB = B.nest (fun _ => none) (Nesting.liftN ps.length (hpos.nesting @ν)) →
      ∃ SΘ, TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          (Θ.subst fun {e} x => σ e x) SΘ ∧
        ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms → ∀ R,
          NestedRunsAt sig ι P v ρ₁ φ block .zero ϱ Ns₀ E₀ Hb νB
            (B.subst (Subst.append (fun {e} x => σ e x) ts.toSubst)) ((f₁ d ps).subst ts.toSubst) R
  | _, _, _, _, _, B, _, .here, _, _, _, .cons (SΘ := SΘ) hν hΘ F hF _ _ _ _, _, _, hRel, _, _, _,
      hSo, hf₁, _, hσ, _, hνB => by
    subst hσ hνB
    refine ⟨SΘ, hΘ, fun ts hts => ?_⟩
    exact NestRel.skeletonRuns hd hord hlifts hb (hF ts hts) .plain
      ((Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B).cast hν hν) _ _
      ((NestRel.congr_computes (hF ts hts) .plain (hf₁.at (.inr fun _ _ _ _ => .rfl) d ps _ _)).2
        (hSo.1 ts ts hts))
  | _, _, _, _, _, B, _, .here, _, _, _, .nested (SΘ := SΘ) _ hΘ F hF _ _ _, hAll, _, hRel, _, _, _,
      hSo, hf₁, _, hσ, _, hνB => by
    subst hσ hνB
    refine ⟨SΘ, hΘ, fun ts hts => ?_⟩
    have hAllB := Term.nest_all (p := fun x : NestLeaf => LeafCongr sig ι sT x.2)
      (mark := fun _ => none) (fun _ _ h => nomatch h) (Nesting.liftN_rel₃ ps.length hAll) B
    exact NestRel.skeletonRuns hd hord hlifts hb (hF ts hts) hAllB
      (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B) _ _
      ((NestRel.congr_computes (hF ts hts) hAllB (hf₁.at (.inr fun _ _ _ _ => .rfl) d ps _ _)).2
        (hSo.1 ts ts hts))
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _,
      .cons (SΘ := SΘ) _ hΘ F hF hBresp G hG hresp, hAll, _, hRel, o₁, o₂, f₁, hSo, hf₁, _, hσ,
      _, hνB => by
    have ih := Nat.forall_lt (levelRel_isPer (ι := ι) hd) n
    have hSp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    have hFv : ∀ ts : Args 0 [] ps', SΘ ts.terms ts.terms →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts => by
      cases hF ts hts with
      | plain _ hF' => exact ⟨_, hF'⟩
    have hEp := AbstractionRel.isPer hSp
      (fun ts hts => NestRel.isPer hd ih .plain (hF ts hts)) hBresp
    have ho₁ := hEp.trans hSo.1 (hEp.symm hSo.1)
    have hfo : AbstractionRel SΘ F (f₁ d' ps') (o₁ d' ps') :=
      (AbstractionRel.congr_computes hSp hFv
        (hf₁.imp_right fun h => ⟨fun τ w => h d' ps' τ w, fun _ _ => .rfl⟩)).2 ho₁
    exact NestDesRel.skeletonRuns hd hord hlifts hb hp (hG _ (hEp.trans hfo (hEp.symm hfo)))
      (Nesting.lift_rel₃ hAll) (Nesting.lift_rel₃ hRel) ((hresp _ _ hfo o₁ o₂).2 hSo.2) hf₁ hσ
      hνB
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _, .nested _ _ _ _ _ _ hG, hAll,
      _, hRel, _, _, f₁, hSo, hf₁, _, hσ, _, hνB =>
    NestDesRel.skeletonRuns hd hord hlifts hb hp (hG (f₁ d' ps')) (Nesting.lift_rel₃ hAll)
      (Nesting.lift_rel₃ hRel) hSo.2 hf₁ hσ hνB
termination_by structural _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ => h

end

-- ADE: none.
/-- `n.Ξ` at run time for the recursor of the multiplicity `0`: the corecursor without state of the
shape of the type of a nested field, whose field is bound to any cell, in a heap that extends the
heap `Hb` of the cells of `E₀`, evaluates to a value related to the recursive result of the field at
the type lifted, when the hypotheses of `NestRel.skeletonRuns` hold and the equality of the type
relates the field to a term: the field is never read. -/
theorem RunsAs.nestedSkeleton (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    {n : Nat} {sT s : Quality} {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel}
    (hF : NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F)
    (hτ : Nest.All (fun x => LeafCongr sig ι sT x.2) τ)
    {ν : Nest Name} (hν : Nest.Rel (SkeletonResultLeaf sig ι P ρ₁ φ block ϱ Ns₀ E₀ Hb) ν τ)
    {t t' e A' : Term 0 []} (ht : F t t') {mr : Lifting.Result 0}
    (hres : Term.NestedResult sig v ρ₁ φ ν A t e) (hL : Term.Lifts sig v ρ₁ ν t A A' mr)
    {σ : Shape} {π χ : Grade}
    (hsh : A.shape v (Signature.shapes v .oneOne Grade.run sig) block Nesting.plain ν =
      some ⟨.lifting σ, π, χ⟩)
    (hrun : ∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') (hval : ValidTerm₀ sig ι e A')
    (c : Nat) (H : Heap) (hHb : Hb.Extends H) (ϖ : Multiplicity) (H₁ : Heap)
    (hH₁ : H.Extends H₁) :
    ∃ w H₂ tr, Eval P ϖ H₁ (c :: E₀) (Target.nested .zero ϱ σ Ns₀) w H₂ tr ∧ H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ e w A' :=
  NestRel.skeletonRuns hd hord hlifts hb hF hτ hν t t' ht (fun _ _ _ => False) e A' mr _ hres hL
    hsh hrun hval (TargetRen.shift m₀ 1) (c :: E₀) (fun _ => List.getElem?_cons_succ) H (.var 0)
    hHb (fun h0 => (h0 rfl).elim) ϖ H₁ hH₁

end

end Sic.Core
