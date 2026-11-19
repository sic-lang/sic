module

public import Sic.Core.RunTime.Relation
public import Sic.Core.RunTime.Relation.Recursors.Results
import Sic.Core.RunTime.Monotonicity

/-!
# Evaluation of the Recursive Results

The recursive results of a branch at run time: the terms of the recursive fields that a relation of
run time holds of are evaluated, and their results satisfy a relation at each recursive field whose
result is used at run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-! ## Recursive Results -/

/-- `Q` holds of the terms `ts` of the fields of the types `rs` of a block, at their addresses `bs`,
at each recursive field whose result, at its grade in `es`, is used at run time. -/
def Terms.RecAt (Q : Name → Term 0 [] → Nat → Prop) :
    List (Option Name) → List Grade → Terms 0 [] → List Nat → Prop
  | some D :: rs, e :: es, .cons t ts, b :: bs =>
    (e ∉ Mode.oneOne.erased → Q D t b) ∧ Terms.RecAt Q rs es ts bs
  | none :: rs, es, .cons _ ts, _ :: bs => Terms.RecAt Q rs es ts bs
  | _, _, _, _ => True

/-- The fields that the relation of run time of a telescope relates to their addresses in the heap
`H₀` satisfy `Q` at each recursive field whose result is used at run time, among fields none of
which is nested, whose nestings are `ns`, when the relation that the position of each recursive
field holds, at its type `D`, implies `Q` on the terms that `V D` holds of, and when the field of
each result used at run time is used too. -/
theorem RunTelRel.recAt {n : Nat} {below : LevelRel.Below n} {Q : Name → Term 0 [] → Nat → Prop}
    {V : Name → Term 0 [] → Prop} {H₀ : Heap} :
    {rs' : Nat → Nest RunNestLeaf} → {ps : List Parameter} → {Θ : Telescope 0 [] ps} →
    {S : RunFieldsRel} → RunTelRel sig ι P n below rs' Θ S → (ns : List (Nest Name)) →
    ns.length = ps.length → (∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms) →
    (∀ i D, ns[i]? = some (.direct D) → ∃ x, rs' i = .direct x ∧
      ∀ t b, x.2 H₀ t b → V D t → Q D t b) →
    (ts : Args 0 [] ps) → (bs : List Nat) → S H₀ ts.terms bs →
    Terms.RecRel (fun D t _ => V D t) (ns.map Nest.blockName) ts.terms ts.terms →
    (es : List Grade) →
    (∀ l (p : Parameter), ps[l]? = some p → Telescope.resultGrades ns es l ∉ Mode.oneOne.erased →
      p.usage ∉ Mode.oneOne.erased) →
    Terms.RecAt Q (ns.map Nest.blockName) es ts.terms bs
  | _, [], .nil, _, .nil, ns, hlen, _, _, .nil, _, _, _, _, _ => by
    cases ns with
    | nil => trivial
    | cons => cases hlen
  | _, p :: ps, .cons _ _ _ Θ, _, .cons _ _ _ G hG hrs0, ns, hlen, hn, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨⟨hFt, -⟩, hGt⟩ := hS
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    have hn' : ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms := fun ν hν => hn ν (List.mem_cons_of_mem _ hν)
    cases x with
    | direct D =>
      obtain ⟨_, h, -⟩ := hrs 0 D rfl
      exact nomatch h.symm.trans hrs0
    | inst ms => exact absurd rfl (hn _ List.mem_cons_self ms)
    | plain =>
    exact RunTelRel.recAt (hG t hFt) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt
      hV es (fun l => hg (l + 1))
  | _, p :: ps, .cons _ _ _ Θ, _, .nested hrs0 hRn G hG, ns, hlen, hn, hrs,
      .cons t ts, bs, hS, hV, es, hg => by
    cases bs with
    | nil => exact (hS : False).elim
    | cons b bs =>
    obtain ⟨hb, hGt⟩ := hS
    cases ns with
    | nil => cases hlen
    | cons x ns =>
    have hn' : ∀ ν ∈ ns, ∀ ms, ν ≠ .inst ms := fun ν hν => hn ν (List.mem_cons_of_mem _ hν)
    cases x with
    | plain =>
      exact RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt
        hV es (fun l => hg (l + 1))
    | inst ms => exact absurd rfl (hn _ List.mem_cons_self ms)
    | direct D =>
    obtain ⟨⟨_, _⟩, hτ, hQ⟩ := hrs 0 D rfl
    rw [hτ] at hRn
    cases hRn with
    | direct _ =>
    cases es with
    | nil => trivial
    | cons e es =>
    obtain ⟨hVt, hV'⟩ := hV
    exact ⟨fun he => hQ t b (hb (hg 0 p rfl he)) hVt,
      RunTelRel.recAt (hG t) ns (Nat.succ.inj hlen) hn' (fun i => hrs (i + 1)) ts bs hGt hV' es
        (fun l => hg (l + 1))⟩

/-- The recursive results of a branch at run time, by induction on the fields, whose nestings are
`ns`: from the addresses `bs` of the fields, the last of the addresses `bsAll` from the position
`o`, the recursive results evaluate, at each weight and in each heap that extends `H₀`, to addresses
related to the results `f D t` at the motives at their fields, each at its grade in `es`, when the
recursor on each recursive field `t` of the type `D` whose result is used evaluates, at each weight
and in each such heap, to such an address. -/
theorem Args.evalResults (hd : sig.Distinct) {m : Nat} {ρ ϱ : Multiplicity} {Ns : TargetBranches m}
    {E : List Nat}
    {f : Name → Term 0 [] → Term 0 []} {names : List Name} {Cs : Motives 0 []} {H₀ : Heap}
    {bsAll : List Nat} :
    {ps : List Parameter} → (ns : List (Nest Name)) → ns.length = ps.length →
    (ts : Args 0 [] ps) → (o : Nat) → (bs : List Nat) → bsAll.drop o = bs →
    bs.length = ps.length → (es : List Grade) →
    es.length = (Telescope.nestResultParams ns ps).length →
    Terms.RecAt (fun D t b => ∀ ϖ H', H₀.Extends H' → ∃ v H₂ tr, EvalRec P ϖ H' E ρ ϱ Ns b v H₂ tr ∧
      H'.Extends H₂ ∧ ∀ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ →
        RunsAs sig ι P H₂ (f D t) v (C.subst₀ (Subst₀.single t))) (ns.map Nest.blockName) es
      ts.terms bs →
    {R : Telescope 0 [] (Telescope.nestResultParams ns ps)} →
    Motives.results names Cs ns ts.terms = some R →
    {rs : Args 0 [] (Telescope.nestResultParams ns ps)} → ts.results f ns = some rs →
    ∀ ϖ H', H₀.Extends H' → ∃ vs H₂ tr, EvalResults P ϖ H' E ρ ϱ Ns bsAll
      (List.zipWith (fun e l => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field l)
        es
        (((ns.map Nest.blockName).zipIdx o).filterMap fun y => y.1.map fun _ => y.2))
        (es.map Grade.run) vs H₂ tr ∧
      H'.Extends H₂ ∧
      RunsAsArgs sig ι P H₂ (fun j => es.getD j Grade.zero) rs vs R
  | [], ns, hlen, .nil, _, _, _, _, es, hes, _, R, hR, rs, hrs, ϖ, H', _ => by
    cases ns with
    | cons _ _ => cases hlen
    | nil =>
      unfold Motives.results at hR
      cases hR
      unfold Args.results at hrs
      cases hrs
      refine ⟨[], H', [], ?_, List.prefix_refl H', trivial⟩
      have hes' : es = [] := List.eq_nil_of_length_eq_zero hes
      subst hes'
      exact .nil
  | _ :: _, [], hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases hlen
  | _ :: _, _ :: _, _, .cons _ _, _, [], _, hbl, _, _, _, _, _, _, _, _, _, _ => by cases hbl
  | _ :: _, .inst _ :: _, _, .cons _ _, _, _ :: _, _, _, _, _, _, _, hR, _, _, _, _, _ => by
    unfold Motives.results at hR
    cases hR
  | p :: ps, .plain :: ns, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, rs, hrs,
      ϖ, H', hH' => by
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    unfold Motives.results at hR
    unfold Args.results at hrs
    exact Args.evalResults hd ns (Nat.succ.inj hlen) ts (o + 1) bs hdrop' (Nat.succ.inj hbl) es
      hes hQ hR hrs ϖ H' hH'
  | p :: ps, .direct D :: ns, hlen, .cons t ts, o, b :: bs, hdrop, hbl, es, hes, hQ, R, hR, rs,
      hrs, ϖ, H', hH' => by
    cases es with
    | nil => cases hes
    | cons e es =>
    obtain ⟨hQt, hQ'⟩ := hQ
    have hdrop' : bsAll.drop (o + 1) = bs := by
      rw [List.drop_add_one_eq_tail_drop, hdrop]
      rfl
    have hbo : bsAll[o]? = some b := by
      have h0 := congrArg (·[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero] at h0
      exact h0
    obtain ⟨rs', hrs', rfl⟩ := Option.map_eq_some_iff.1 hrs
    simp only [Args.terms] at hR
    unfold Motives.results at hR
    cases hC : Cs.get (names.idxOf D) with
    | none => simp only [hC] at hR; cases hR
    | some a =>
    obtain ⟨k, C⟩ := a
    cases k with
    | succ => simp only [hC] at hR; cases hR
    | zero =>
    simp only [hC] at hR
    obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.1 hR
    -- The rest of the results, at the result `f D t`, are the results of the rest of the fields.
    have hR'' : Motives.results names Cs ns (ps := ps) ts.terms =
        some (R'.subst₀ (Subst₀.single (f D t))) := by
      let σ₀ : Subst 0 [] [] := fun x => nomatch x
      have h := Motives.results_subst names (Subst₀.toSubst (Subst₀.single (f D t))) ns hR'
      rw [Motives.subst_rename_of (θ' := σ₀) (fun x => by cases x),
        Motives.subst_id_of (fun x => by cases x), Terms.subst_rename_of (θ' := σ₀)
          (fun x => by cases x), Terms.subst_id_of (fun x => by cases x),
        ← Telescope.subst₀_eq_subst] at h
      exact h
    have hlen' : ns.length = ps.length := Nat.succ.inj hlen
    have hbl' : bs.length = ps.length := Nat.succ.inj hbl
    have hes' : es.length = (Telescope.nestResultParams ns ps).length := Nat.succ.inj hes
    by_cases he : e ∈ Mode.oneOne.erased
    · have hH'' : H'.Extends (H' ++ [.erased]) := List.prefix_append _ _
      obtain ⟨vs, H₂, R₂, hevs, hH₂, hruns⟩ := Args.evalResults hd ns hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' hrs' ϖ _ (hH'.trans hH'')
      refine ⟨H'.length :: vs, H₂, R₂, ?_, hH''.trans hH₂, fun h => (h he).elim, hruns⟩
      show EvalResults P ϖ H' E ρ ϱ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field o) :: _) (e.run :: _) _
        H₂ _
      rw [ite_eq_left_of_eq_true _ _ (eq_true he)]
      exact .erased hevs
    · obtain ⟨v, H₂, R₁, hev, hH₂, hrun⟩ := hQt he (ϖ * e.run) H' hH'
      obtain ⟨vs, H₃, R₂, hevs, hH₃, hruns⟩ := Args.evalResults hd ns hlen' ts (o + 1) bs hdrop'
        hbl' es hes' hQ' hR'' hrs' ϖ _ (hH'.trans hH₂)
      refine ⟨v :: vs, H₃, R₁ ++ R₂, ?_, hH₂.trans hH₃, fun _ => (hrun C hC).mono hd hH₃, hruns⟩
      show EvalResults P ϖ H' E ρ ϱ Ns bsAll
        ((if e ∈ Mode.oneOne.erased then RecursiveResult.erased else .field o) :: _) (e.run :: _) _
        H₃ _
      rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
      exact .recursor hbo hev hevs

/-- Terms of a list evaluate to as many addresses. -/
theorem EvalAll.length_ofList {n : Nat} {ϖ : Multiplicity} {H H' : Heap} {E : List Nat} :
    (Ms : List (Multiplicity × Target n)) → {as : List Nat} → {R : List Nat} →
      EvalAll P ϖ H E (Targets.ofList Ms) as H' R → as.length = Ms.length
  | [], _, _, .nil => rfl
  | _ :: Ms, _, _, .cons _ hs => congrArg (· + 1) (EvalAll.length_ofList Ms hs)

/-- The fields of arguments related at the recursive fields by `V`, at the addresses to which the
terms `G (some D)` of their types `D` evaluate, satisfy `Q`, when `Q D` holds of each term of a
recursive field that `V D` relates, at each address to which `G (some D)` evaluates, at some weight,
in a heap that extends `H₀`, to a heap that `Hf` extends. -/
theorem EvalAll.recAt {n : Nat} {ϖ : Multiplicity} {E : List Nat}
    {G : Option Name → Multiplicity × Target n}
    {V : Name → TermRel} {Q : Name → Term 0 [] → Nat → Prop} {H₀ Hf : Heap} :
    {ps : List Parameter} → (rs : List (Option Name)) →
    (∀ D, some D ∈ rs → ∀ t u, V D t u → ∀ ϖ' Ha b Hb R, H₀.Extends Ha →
      Eval P ϖ' Ha E (G (some D)).2 b Hb R → Hb.Extends Hf → Q D t b) →
    rs.length = ps.length → (es : List Grade) → (ts us : Args 0 [] ps) → {H₁ : Heap} →
    {as : List Nat} → {R : List Nat} → H₀.Extends H₁ →
    EvalAll P ϖ H₁ E (Targets.ofList (rs.map G)) as Hf R →
    Terms.RecRel V rs ts.terms us.terms → Terms.RecAt Q rs es ts.terms as
  | [], [], _, _, _, .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, some D :: rs, hG, hl, _ :: es, .cons t ts, .cons u us, _, _, _, hH, .cons h hs, hV =>
    ⟨fun _ => hG D (List.mem_cons_self ..) t u hV.1 _ _ _ _ _ hH h hs.extends,
      EvalAll.recAt rs (fun D hD => hG D (List.mem_cons_of_mem _ hD)) (Nat.succ.inj hl) es ts us
        (hH.trans h.extends) hs hV.2⟩
  | _ :: _, some _ :: _, _, _, [], .cons _ _, .cons _ _, _, _, _, _, _, _ => trivial
  | _ :: _, none :: rs, hG, hl, es, .cons _ ts, .cons _ us, _, _, _, hH, .cons h hs, hV =>
    EvalAll.recAt rs (fun D hD => hG D (List.mem_cons_of_mem _ hD)) (Nat.succ.inj hl) es ts us
      (hH.trans h.extends) hs hV
  | [], _ :: _, _, hl, _, _, _, _, _, _, _, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _, _, _, _, _, _, _, _ => nomatch hl

end Sic.Core
