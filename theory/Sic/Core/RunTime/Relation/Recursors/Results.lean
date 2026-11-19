module

public import Sic.Core.Lifting.Substitution
public import Sic.Core.RunTime.Relation
public import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Rules
import Sic.Core.Soundness.Substitution

/-!
# Evaluation of the Recursive Results

The recursive results of a branch at run time, one for each field whose nesting has a position, in
order, at the types of the recursive results that the typing gives: the recursor on the term of a
recursive field and the corecursor of the shape of the type of a nested field, which a relation of
run time, or the equality for the term of a skeleton, gives the terms of the fields, evaluate to
addresses related to the results, at each result whose grade is used at run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Recursive Results -/

/-- `Qd` holds of the terms `ts` of the fields, at their addresses `bs`, at each recursive field of a
type `D` of the block whose result, at its grade in `es`, is used at run time, and `Qn` at each
such nested field, of its nesting and of its type in `As`; the nestings of the fields are `ns`. -/
def Terms.RecAt (Qd : Name → Term 0 [] → Nat → Prop)
    (Qn : Nest Name → Term 0 [] → Term 0 [] → Nat → Prop) :
    List (Nest Name) → Terms 0 [] → List Grade → Terms 0 [] → List Nat → Prop
  | .plain :: ns, .cons _ As, es, .cons _ ts, _ :: bs => Terms.RecAt Qd Qn ns As es ts bs
  | .direct D :: ns, .cons _ As, e :: es, .cons t ts, b :: bs =>
    (e ∉ Mode.oneOne.erased → Qd D t b) ∧ Terms.RecAt Qd Qn ns As es ts bs
  | .inst ms :: ns, .cons A As, e :: es, .cons t ts, b :: bs =>
    (e ∉ Mode.oneOne.erased → Qn (.inst ms) A t b) ∧ Terms.RecAt Qd Qn ns As es ts bs
  | _, _, _, _, _ => True

-- ADE: none.
/-- The types of the entries of a closed telescope are terms of universes, each at every term of the
types of the entries before it. -/
def Telescope.ValidSorts₀ (sig : Signature) (ι : Interpretation) :
    {ps : List Parameter} → Telescope 0 [] ps → Prop
  | [], .nil => True
  | _ :: _, .cons _ _ A Θ => (∃ κ, ValidTerm₀ sig ι A (.sort κ)) ∧
      ∀ v, ValidTerm₀ sig ι v A → Telescope.ValidSorts₀ sig ι (Θ.subst₀ (Subst₀.single v))

/-- Each type of a closed telescope whose types are terms of universes, at arguments that the
meaning relates to themselves, has a relation of run time: the way the walk of the recursive
results reads `Telescope.ValidSorts₀`. -/
theorem Telescope.ValidSorts₀.hasRun (P : Program) :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → Telescope.ValidSorts₀ sig ι Θ →
      (ts : Args 0 [] ps) → EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
        ∀ (i : Nat) (A : Term 0 []), (Θ.typesAt ts).get i = some A →
          ∃ vA R, Computesι sig ι A vA ∧ HasRun sig ι P vA R
  | [], .nil, _, .nil, _, _, _, h => nomatch h
  | _ :: _, .cons _ _ _ _, hV, .cons _ _, _, 0, _, h => by
    obtain ⟨⟨_, hκ⟩, _⟩ := hV
    cases h
    exact ValidTerm₀.hasRun P hκ
  | _ :: _, .cons _ _ _ _, hV, .cons _ ts, hts, i + 1, A, h => by
    obtain ⟨_, hΘ⟩ := hV
    obtain ⟨ht, hts'⟩ := EqSubst.args_cons_iff.1 hts
    exact Telescope.ValidSorts₀.hasRun P (hΘ _ ht) ts hts' i A h

/-- `Θ[σ⇑][v / x] = Θ[σ, v]`, with the substitution followed by `v` that the arguments of a
telescope read. -/
theorem Telescope.subst_lift_single_snoc {Γ : Scope} {ps : List Parameter} (σ : Subst 0 [] Γ)
    (v : Term 0 []) (Θ : Telescope 0 (.var :: Γ) ps) :
    (Θ.subst (Subst.lift σ)).subst₀ (Subst₀.single v) = Θ.subst (Subst.snoc (e := .var) σ v) := by
  rw [Telescope.subst_lift_single]
  congr 1
  apply Subst.ext
  intro a x
  cases x <;> rfl

/-- The fields that the relation of run time of a telescope relates to their addresses in the heap
`H₀`, whose nestings are `ns`, satisfy `Qd` at each recursive field whose result is used at run
time, and `Qn` at each such nested field: at the position of a recursive field of the type `D`, the
relation of the position implies `Qd` on the terms that `V D` holds of, and the field of a result
used at run time is used too; at the position of a nested field, its relation of run time read at
its nesting, of a term of its type, at the grade of the field, implies `Qn` when the result is used
at run time. -/
theorem RunTelRel.recAt {n : Nat} {below : LevelRel.Below n} {Qd : Name → Term 0 [] → Nat → Prop}
    {Qn : Nest Name → Term 0 [] → Term 0 [] → Nat → Prop} {V : Name → Term 0 [] → Prop}
    {H₀ : Heap} :
    {rs' : Nat → Nest RunNestLeaf} → {ps : List Parameter} → {Θ : Telescope 0 [] ps} →
    {S : RunFieldsRel} → RunTelRel sig ι P n below rs' Θ S → (ns : List (Nest Name)) →
    ns.length = ps.length → (es : List Grade) → (ts : Args 0 [] ps) →
    (∀ i D, ns[i]? = some (.direct D) → ∃ x, rs' i = .direct x ∧
      ∀ t b, x.2 H₀ t b → V D t → Qd D t b) →
    (∀ i ms, ns[i]? = some (.inst ms) → rs' i ≠ .plain ∧
      ∀ (p : Parameter) (A t : Term 0 []) (R : RunRel) (b : Nat), ps[i]? = some p →
        (Θ.typesAt ts).get i = some A →
        ValidTerm₀ sig ι t A → RunNestRel sig ι P n below (rs' i) A R →
        RunRel.atGrade p.usage R H₀ t b →
        Telescope.resultGrades ns es i ∉ Mode.oneOne.erased → Qn (.inst ms) A t b) →
    (∀ l D (p : Parameter), ns[l]? = some (.direct D) → ps[l]? = some p →
      Telescope.resultGrades ns es l ∉ Mode.oneOne.erased → p.usage ∉ Mode.oneOne.erased) →
    (bs : List Nat) → S H₀ ts.terms bs →
    EqSubst sig ι (Context.empty.append Θ) ts.toSubst ts.toSubst →
    Terms.RecRel (fun D t _ => V D t) (ns.map Nest.blockName) ts.terms ts.terms →
    Terms.RecAt Qd Qn ns (Θ.typesAt ts) es ts.terms bs
  | _, [], .nil, _, .nil, ns, hlen, _, .nil, _, _, _, _, _, _, _ => by
    cases ns with
    | nil => trivial
    | cons => cases hlen
  | _, p :: ps, .cons _ _ A Θ, _, .cons _ _ _ G hG hrs0, ns, hlen, es, .cons t ts, hd', hN, hg,
      bs, hS, hts, hV => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨⟨hFt, -⟩, hGt⟩ := hS
    obtain ⟨-, hts'⟩ := EqSubst.args_cons_iff.1 hts
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    cases x with
    | direct D =>
      obtain ⟨_, h, -⟩ := hd' 0 D rfl
      exact nomatch h.symm.trans hrs0
    | inst ms => exact absurd hrs0 (hN 0 ms rfl).1
    | plain =>
    exact RunTelRel.recAt (hG t hFt) ns (Nat.succ.inj hlen) es ts (fun i => hd' (i + 1))
      (fun i => hN (i + 1)) (fun l => hg (l + 1)) bs hGt hts' hV
  | _, p :: ps, .cons _ _ A Θ, _, .nested hrs0 hRn G hG, ns, hlen, es, .cons t ts, hd', hN, hg,
      bs, hS, hts, hV => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨hb, hGt⟩ := hS
    obtain ⟨htv, hts'⟩ := EqSubst.args_cons_iff.1 hts
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    cases x with
    | plain =>
      exact RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) es ts (fun i => hd' (i + 1))
        (fun i => hN (i + 1)) (fun l => hg (l + 1)) bs hGt hts' hV
    | inst ms =>
      cases es with
      | nil => trivial
      | cons e es =>
      exact ⟨fun he => (hN 0 ms rfl).2 p A t _ b rfl rfl htv hRn hb he,
        RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) es ts (fun i => hd' (i + 1))
          (fun i => hN (i + 1)) (fun l => hg (l + 1)) bs hGt hts' hV⟩
    | direct D =>
    obtain ⟨⟨_, _⟩, hτ, hQ⟩ := hd' 0 D rfl
    rw [hτ] at hRn
    cases hRn with
    | direct _ =>
    cases es with
    | nil => trivial
    | cons e es =>
    obtain ⟨hVt, hV'⟩ := hV
    exact ⟨fun he => hQ t b (hb (hg 0 D p rfl rfl he)) hVt,
      RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) es ts (fun i => hd' (i + 1))
        (fun i => hN (i + 1)) (fun l => hg (l + 1)) bs hGt hts' hV'⟩

/-- The fields of arguments related at their positions by the graph of the nestings, at the
addresses to which the terms `G (some D)` of the types `D` of their recursive fields, and `G none`
of the others, evaluate, satisfy `Qd` at each recursive field, when `Qd D` holds of each term of a
recursive field that `V D` relates, at each address to which `G (some D)` evaluates, at some
weight, in a heap that extends `H₀`, to a heap that `Hf` extends, and `Qn` at each nested field,
when the relation that the graph of the nestings gives its type relates its term to a term. -/
theorem EvalAll.recAt {n nE : Nat} {sE : Quality} {L : Name → NestLeaf} {ϖ : Multiplicity}
    {E : List Nat} {G : Option Name → Multiplicity × Target n}
    {V : Name → TermRel} {Qd : Name → Term 0 [] → Nat → Prop}
    {Qn : Nest Name → Term 0 [] → Term 0 [] → Nat → Prop} {H₀ Hf : Heap} :
    {ps : List Parameter} → (ns : List (Nest Name)) →
    (∀ D, some D ∈ ns.map Nest.blockName → ∀ t u, V D t u → ∀ ϖ' Ha b Hb R, H₀.Extends Ha →
      Eval P ϖ' Ha E (G (some D)).2 b Hb R → Hb.Extends Hf → Qd D t b) →
    (∀ ms (A t u : Term 0 []) (F : TermRel) b, .inst ms ∈ ns →
      NestRel sig ι nE (fun m _ => levelRel sig ι m) sE sE ((Nest.inst ms).map L) A F → F t u →
      Qn (.inst ms) A t b) →
    ns.length = ps.length → (es : List Grade) → (Θ : Telescope 0 [] ps) → (ts us : Args 0 [] ps) →
    {H₁ : Heap} → {as : List Nat} → {R : List Nat} → H₀.Extends H₁ →
    EvalAll P ϖ H₁ E (Targets.ofList ((ns.map Nest.blockName).map G)) as Hf R →
    Terms.RecRel V (ns.map Nest.blockName) ts.terms us.terms →
    Terms.NestedRel sig ι nE sE L ns Θ ts.terms us.terms →
    Terms.RecAt Qd Qn ns (Θ.typesAt ts) es ts.terms as
  | [], [], _, _, _, _, .nil, .nil, .nil, _, _, _, _, .nil, _, _ => trivial
  | _ :: _, .direct D :: ns, hG, hN, hl, e :: es, .cons _ _ _ Θ, .cons t ts, .cons u us, _, _, _,
      hH, .cons h hs, hV, hN' =>
    ⟨fun _ => hG D (List.mem_cons_self ..) t u hV.1 _ _ _ _ _ hH h hs.extends,
      EvalAll.recAt ns (fun D hD => hG D (List.mem_cons_of_mem _ hD))
        (fun ms A t u F b hm => hN ms A t u F b (List.mem_cons_of_mem _ hm)) (Nat.succ.inj hl) es
        _ ts us (hH.trans h.extends) hs hV.2 hN'.2⟩
  | _ :: _, .direct _ :: _, _, _, _, [], .cons _ _ _ _, .cons _ _, .cons _ _, _, _, _, _, _, _,
      _ => trivial
  | _ :: _, .inst ms :: ns, hG, hN, hl, e :: es, .cons _ _ A Θ, .cons t ts, .cons u us, _, _, _,
      hH, .cons h hs, hV, hN' => by
    obtain ⟨F, hF, hFt⟩ := hN'.1 (fun h => nomatch h)
    exact ⟨fun _ => hN ms A t u F _ List.mem_cons_self hF hFt,
      EvalAll.recAt ns (fun D hD => hG D (List.mem_cons_of_mem _ hD))
        (fun ms A t u F b hm => hN ms A t u F b (List.mem_cons_of_mem _ hm)) (Nat.succ.inj hl) es
        _ ts us (hH.trans h.extends) hs hV hN'.2⟩
  | _ :: _, .inst _ :: _, _, _, _, [], .cons _ _ _ _, .cons _ _, .cons _ _, _, _, _, _, _, _,
      _ => trivial
  | _ :: _, .plain :: ns, hG, hN, hl, es, .cons _ _ _ Θ, .cons t ts, .cons u us, _, _, _, hH,
      .cons h hs, hV, hN' =>
    EvalAll.recAt ns (fun D hD => hG D (List.mem_cons_of_mem _ hD))
      (fun ms A t u F b hm => hN ms A t u F b (List.mem_cons_of_mem _ hm)) (Nat.succ.inj hl) es _
      ts us (hH.trans h.extends) hs hV hN'.2
  | [], _ :: _, _, _, hl, _, _, _, _, _, _, _, _, _, _, _ => nomatch hl
  | _ :: _, [], _, _, hl, _, _, _, _, _, _, _, _, _, _, _ => nomatch hl

/-- The recursive results of a branch at run time, by induction on the types `R` of the recursive
results of the fields, whose nestings are `ns`, the types of the fields being `As` and their
variables `xs`, which `θ` substitutes by the terms of the fields and `θ'` the results before:
from the addresses `bs` of the fields, the last of the addresses `bsAll` from the position `o`,
the recursive results evaluate, at each weight, in each heap that extends `H₀` and with the
branches renamed by any `g` in any environment `E'` that binds each variable `g x` as `E` binds
`x`, to addresses related to the results `rs` at their types, each at its grade in `es`, when the
results are terms of their types, these types terms of universes, and what the recursor or the
corecursor of each result whose grade is used at run time computes is related to it: `Qd` for the
recursor on a recursive field of the type `D`, at the motive of `D`, and `Qn` for the corecursor of
the shape `σ` that `s` gives a nested field, at the type of the field lifted, from a cell that holds
the address of the field. -/
theorem Args.evalResults (hd : sig.Distinct) {v : Lifting.Variables} {ρr ϱ : Multiplicity}
    {m : Nat} {Ns : TargetBranches m} {E : List Nat} {ρ₁ : Lifting 0 [] []}
    {φ : Name → Term 0 [.var]} {lookup : Shape.Lookup} {block : Name → Option Shape.Motive}
    {H₀ : Heap} {bsAll : List Nat} {f : Nat → Option Name} {s : Nat → Option Shape}
    {Δ' Δ : Scope} {ρ : Lifting 0 Δ' Δ} {ns : List (Nest Name)} {ps : List Parameter}
    {As xs : Terms 0 Δ} {ps' : List Parameter} {R : Telescope 0 Δ' ps'} {πs : List Grade}
    (h : Terms.ResultTypes sig v ρ ns ps As xs R πs) :
    ∀ {θ : Subst 0 [] Δ} {θ' : Subst 0 [] Δ'}, Lifting.Substitutes θ θ' ρ ρ₁ →
    ∀ (o : Nat) (bs : List Nat), bsAll.drop o = bs → bs.length = ps.length →
    ∀ (es : List Grade), es.length = ps'.length →
    (∀ i D, ns[i]? = some (.direct D) → (f (o + i)).isSome) →
    (∀ i ms, ns[i]? = some (.inst ms) → f (o + i) = none) →
    (∀ i ms A, ns[i]? = some (.inst ms) → (As.subst θ).get i = some A →
      ∃ σ π χ, s (o + i) = some σ ∧
        A.shape v lookup block Nesting.plain (.inst ms) = some ⟨.lifting σ, π, χ⟩) →
    ∀ {rs : Args 0 [] ps'}, Terms.ResultTerms sig v ρ₁ φ ns ps (As.subst θ) (xs.subst θ) rs →
    EqSubst sig ι (Context.empty.append (R.subst θ')) rs.toSubst rs.toSubst →
    Telescope.ValidSorts₀ sig ι (R.subst θ') →
    Terms.RecAt
      (fun D t b => ∀ ϖ H', H₀.Extends H' → ∀ {m' : Nat} (g : TargetRen m' m) (E' : List Nat),
        (∀ x : Fin m, E'[(g x : Nat)]? = E[(x : Nat)]?) →
        ∃ v H₂ tr, EvalRec P ϖ H' E' ρr ϱ (Ns.rename g) b v H₂ tr ∧ H'.Extends H₂ ∧
          ∀ b₁, ρ₁.block D = some b₁ →
            RunsAs sig ι P H₂ ((φ D).subst₀ (Subst₀.single t)) v
              (b₁.motive.subst₀ (Subst₀.single t)))
      (fun ν A t b => ∀ (σ : Shape) (π χ : Grade) (e A' : Term 0 []) (mr : Lifting.Result 0),
        A.shape v lookup block Nesting.plain ν = some ⟨.lifting σ, π, χ⟩ →
        Term.NestedResult sig v ρ₁ φ ν A t e → Term.Lifts sig v ρ₁ ν t A A' mr →
        (∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') → ValidTerm₀ sig ι e A' →
        ∀ ϖ H' (c : Nat) (π' : Multiplicity), H₀.Extends H' → H'[c]? = some (.cell π' b) →
        ∀ {m' : Nat} (g : TargetRen m' m) (E' : List Nat),
        (∀ x : Fin m, E'[(g x : Nat)]? = E[(x : Nat)]?) →
        ∃ w H₂ tr, Eval P ϖ H' (c :: E') (Target.nested ρr ϱ σ (Ns.rename g)) w H₂ tr ∧
          H'.Extends H₂ ∧ RunsAs sig ι P H₂ e w A')
      ns (As.subst θ) es (xs.subst θ) bs →
    ∀ ϖ H', H₀.Extends H' → ∀ {m' : Nat} (g : TargetRen m' m) (E' : List Nat),
      (∀ x : Fin m, E'[(g x : Nat)]? = E[(x : Nat)]?) →
      ∃ vs H₂ tr, EvalResults P ϖ H' E' ρr ϱ (Ns.rename g) bsAll
        (List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else w) es
          ((Telescope.nestPositions ns o).map fun l => RecursiveResult.ofField (f l) (s l) l))
        (es.map Grade.run) vs H₂ tr ∧
      H'.Extends H₂ ∧
      RunsAsArgs sig ι P H₂ (fun j => es.getD j Grade.zero) rs vs (R.subst θ') := by
  have hid : ∀ {a} (y : Var [] a), ρ₁.ren y = y := fun y => nomatch y
  induction h with
  | nil =>
    intro θ θ' _ o bs _ _ es hes _ _ _ rs hr _ _ _ ϖ H' _ _ _ _ _
    cases rs
    obtain rfl : es = [] := List.eq_nil_of_length_eq_zero hes
    exact ⟨[], H', [], .nil, List.prefix_refl H', trivial⟩
  | @plain _ _ ρ ns p ps ps' A x As xs R πs h ih =>
    intro θ θ' hs o bs hdrop hbl es hes hf hfn hsn rs hr hEq hV hQ ϖ H' hH' _ g E' hg
    cases bs with
    | nil => cases hbl
    | cons b bs =>
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    rw [Terms.subst, Terms.subst] at hr
    cases hr with
    | plain hr =>
    rw [Telescope.nestPositions_plain]
    exact ih hs (o + 1) bs hdrop' (Nat.succ.inj hbl) es hes
      (fun i D hi => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D hi)
      (fun i ms hi => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hfn (i + 1) ms hi)
      (fun i ms A hi hA => by
        rw [show o + 1 + i = o + (i + 1) by omega]
        exact hsn (i + 1) ms A hi hA)
      hr hEq hV hQ ϖ H' hH' g E' hg
  | @recursive _ _ ρ D ns p ps ps' A x As xs b R πs hD h ih =>
    intro θ θ' hs o bs hdrop hbl es hes hf hfn hsn rs hr hEq hV hQ ϖ H' hH' _ g E' hg
    cases bs with
    | nil => cases hbl
    | cons a bs =>
    cases es with
    | nil => cases hes
    | cons e es =>
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    have hao : bsAll[o]? = some a := by
      have h0 := congrArg (·[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero] at h0
      exact h0
    rw [Terms.subst, Terms.subst] at hr hQ
    cases hr with
    | recursive hr =>
    rename_i rs
    obtain ⟨hQt, hQ'⟩ := hQ
    -- The type of the result is the motive of `D` at the term of the field.
    have hty : (b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))).subst θ' =
        (b.subst θ θ').motive.subst₀ (Subst₀.single (x.subst θ)) := by
      rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ θ') b.motive, hs.subst_rename₀ x,
        Term.rename_id_of hid]
      rfl
    have hb₁ : ρ₁.block D = some (b.subst θ θ') := by rw [hs.block, hD]; rfl
    obtain ⟨hvr, hEq'⟩ := (EqSubst.args_cons_subst_iff θ').1 hEq
    obtain ⟨-, hV'⟩ := hV
    have hV'' := hV' _ hvr
    rw [Telescope.subst_lift_single_snoc] at hV''
    have hf' : ∀ i D', ns[i]? = some (.direct D') → (f (o + 1 + i)).isSome := fun i D' hi => by
      rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D' hi
    have hfn' : ∀ i ms, ns[i]? = some (.inst ms) → f (o + 1 + i) = none := fun i ms hi => by
      rw [show o + 1 + i = o + (i + 1) by omega]; exact hfn (i + 1) ms hi
    have hsn' : ∀ i ms A, ns[i]? = some (.inst ms) → (As.subst θ).get i = some A →
        ∃ σ π χ, s (o + 1 + i) = some σ ∧
          A.shape v lookup block Nesting.plain (.inst ms) = some ⟨.lifting σ, π, χ⟩ :=
      fun i ms A hi hA => by
        rw [show o + 1 + i = o + (i + 1) by omega]; exact hsn (i + 1) ms A hi hA
    have hks : List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased
          else w) (e :: es) ((Telescope.nestPositions (.direct D :: ns) o).map fun l =>
            RecursiveResult.ofField (f l) (s l) l) =
        (if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field o) ::
          List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else w) es
            ((Telescope.nestPositions ns (o + 1)).map fun l =>
              RecursiveResult.ofField (f l) (s l) l) := by
      obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.1 (hf 0 D rfl)
      rw [Nat.add_zero] at hD'
      rw [Telescope.nestPositions_cons rfl, List.map_cons, List.zipWith_cons_cons]
      simp only [RecursiveResult.ofField, hD']
    rw [hks]
    by_cases he : e ∈ Mode.oneOne.erased
    · have hH'' : H'.Extends (H' ++ [.erased]) := List.prefix_append _ _
      obtain ⟨vs, H₂, R₂, hevs, hH₂, hruns⟩ := ih (hs.ofSnoc _) (o + 1) bs hdrop'
        (Nat.succ.inj hbl) es (Nat.succ.inj hes) hf' hfn' hsn' hr hEq' hV'' hQ' ϖ _
        (hH'.trans hH'') g E' hg
      refine ⟨H'.length :: vs, H₂, R₂, ?_, hH''.trans hH₂, fun h => (h he).elim, ?_⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
        exact .erased hevs
      · rw [Telescope.subst_lift_single_snoc]
        exact hruns
    · obtain ⟨w, H₂, R₁, hev, hH₂, hrun⟩ := hQt he (ϖ * e.run) H' hH' g E' hg
      obtain ⟨vs, H₃, R₂, hevs, hH₃, hruns⟩ := ih (hs.ofSnoc _) (o + 1) bs hdrop'
        (Nat.succ.inj hbl) es (Nat.succ.inj hes) hf' hfn' hsn' hr hEq' hV'' hQ' ϖ _
        (hH'.trans hH₂) g E' hg
      refine ⟨w :: vs, H₃, R₁ ++ R₂, ?_, hH₂.trans hH₃,
        fun _ => ?_, ?_⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
        exact .recursor hao hev hevs
      · show RunsAs sig ι P H₃ _ w ((b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))).subst θ')
        rw [hty]
        exact (hrun _ hb₁).mono hd hH₃
      · rw [Telescope.subst_lift_single_snoc]
        exact hruns
  | @nested _ _ ρ ms ns p ps ps' A x As xs A' mr R πs hA h ih =>
    intro θ θ' hs o bs hdrop hbl es hes hf hfn hsn rs hr hEq hV hQ ϖ H' hH' _ g E' hg
    cases bs with
    | nil => cases hbl
    | cons a bs =>
    cases es with
    | nil => cases hes
    | cons e es =>
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    have hao : bsAll[o]? = some a := by
      have h0 := congrArg (·[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero] at h0
      exact h0
    rw [Terms.subst, Terms.subst] at hr hQ
    cases hr with
    | nested hres hr =>
    rename_i eR rs
    obtain ⟨hQt, hQ'⟩ := hQ
    have hL := hA.subst hs
    rw [hs.subst_rename₀ x, Term.rename_id_of hid] at hL
    obtain ⟨hvr, hEq'⟩ := (EqSubst.args_cons_subst_iff θ').1 hEq
    obtain ⟨⟨κ, hκ⟩, hV'⟩ := hV
    have hV'' := hV' _ hvr
    rw [Telescope.subst_lift_single_snoc] at hV''
    obtain ⟨σ, π, χ, hsσ, hsh⟩ := hsn 0 ms _ rfl rfl
    have hf' : ∀ i D', ns[i]? = some (.direct D') → (f (o + 1 + i)).isSome := fun i D' hi => by
      rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D' hi
    have hfn' : ∀ i ms, ns[i]? = some (.inst ms) → f (o + 1 + i) = none := fun i ms hi => by
      rw [show o + 1 + i = o + (i + 1) by omega]; exact hfn (i + 1) ms hi
    have hsn' : ∀ i ms A, ns[i]? = some (.inst ms) → (As.subst θ).get i = some A →
        ∃ σ π χ, s (o + 1 + i) = some σ ∧
          A.shape v lookup block Nesting.plain (.inst ms) = some ⟨.lifting σ, π, χ⟩ :=
      fun i ms A hi hA => by
        rw [show o + 1 + i = o + (i + 1) by omega]; exact hsn (i + 1) ms A hi hA
    have hks : List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased
          else w) (e :: es) ((Telescope.nestPositions (.inst ms :: ns) o).map fun l =>
            RecursiveResult.ofField (f l) (s l) l) =
        (if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .nested o σ) ::
          List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else w) es
            ((Telescope.nestPositions ns (o + 1)).map fun l =>
              RecursiveResult.ofField (f l) (s l) l) := by
      have hfo : f o = none := hfn 0 ms rfl
      have hso : s o = some σ := hsσ
      rw [Telescope.nestPositions_cons rfl, List.map_cons, List.zipWith_cons_cons]
      simp only [RecursiveResult.ofField, hfo, hso]
    rw [hks]
    by_cases he : e ∈ Mode.oneOne.erased
    · have hH'' : H'.Extends (H' ++ [.erased]) := List.prefix_append _ _
      obtain ⟨vs, H₂, R₂, hevs, hH₂, hruns⟩ := ih (hs.ofSnoc _) (o + 1) bs hdrop'
        (Nat.succ.inj hbl) es (Nat.succ.inj hes) hf' hfn' hsn' hr hEq' hV'' hQ' ϖ _
        (hH'.trans hH'') g E' hg
      refine ⟨H'.length :: vs, H₂, R₂, ?_, hH''.trans hH₂, fun h => (h he).elim, ?_⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
        exact .erased hevs
      · rw [Telescope.subst_lift_single_snoc]
        exact hruns
    · -- The corecursor of the shape, from a new cell that holds the address of the field.
      let Hc := H' ++ [.cell ((ϖ * e.run) * (σ.factor * ρr)) a]
      have hHc : H'.Extends Hc := List.prefix_append _ _
      obtain ⟨w, H₂, R₁, hev, hH₂, hrun⟩ := hQt he σ π χ eR (A'.subst θ') mr hsh hres hL
        (ValidTerm₀.hasRun P hκ) hvr (ϖ * e.run) Hc H'.length _ (hH'.trans hHc)
        List.getElem?_concat_length g E' hg
      obtain ⟨vs, H₃, R₂, hevs, hH₃, hruns⟩ := ih (hs.ofSnoc _) (o + 1) bs hdrop'
        (Nat.succ.inj hbl) es (Nat.succ.inj hes) hf' hfn' hsn' hr hEq' hV'' hQ' ϖ _
        ((hH'.trans hHc).trans hH₂) g E' hg
      refine ⟨w :: vs, H₃, R₁ ++ R₂, ?_, hHc.trans (hH₂.trans hH₃),
        fun _ => hrun.mono hd hH₃, ?_⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
        exact .nested hao hev hevs
      · rw [Telescope.subst_lift_single_snoc]
        exact hruns

/-- Terms of a list evaluate to as many addresses. -/
theorem EvalAll.length_ofList {n : Nat} {ϖ : Multiplicity} {H H' : Heap} {E : List Nat} :
    (Ms : List (Multiplicity × Target n)) → {as : List Nat} → {R : List Nat} →
      EvalAll P ϖ H E (Targets.ofList Ms) as H' R → as.length = Ms.length
  | [], _, _, .nil => rfl
  | _ :: Ms, _, _, .cons _ hs => congrArg (· + 1) (EvalAll.length_ofList Ms hs)

end Sic.Core
