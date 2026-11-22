module

public import Sic.Core.Lifting.Extension
public import Sic.Core.RunTime.Monotonicity
public import Sic.Core.Soundness.Corecursors
public import Sic.Core.Syntax.Signature
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Recursion
import Sic.Core.Lifting.Shape
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Results.Substitution
import Sic.Core.RunTime.Relation.Recursors.Nested.Branches
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Observations
import Sic.Core.RunTime.Subsumption
import Sic.Core.Shape.Results.Lifting
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Recursors.Nested
import Sic.Core.Soundness.Substitution
import Sic.Math.Nat

/-!
# Run Time of the Nested Results

The recursive result of a nested field at run time, `n.Ξ`: the corecursor without state whose
branches the evaluation builds from the shape `Ξ` and the branches of the recursor, one for each
destructor that the lifting keeps, each observing the field by the destructor that it lifts and
giving the recursor on this observation, or the corecursor of the next lifting.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Paths, Leaves and Nested Results at Run Time -/

section

variable (sig : Signature) (ι : Interpretation) (P : Program)

-- ADE: none.
/-- The path `O` from a field, in the environment `E` and from the heap `H`, runs to an address that
`R` relates to `t`: renamed by any renaming `f`, in any environment `E'` that binds each variable
`f x` as `E` binds `x`, it evaluates, at every weight and in every heap that extends `H`, to an
address that `R` relates to `t` in the heap after its evaluation, which extends the heap before;
the built branches evaluate the path under their arguments, whose environment extends `E`. -/
def Target.RunsTo (R : RunRel) (t : Term 0 []) {m : Nat} (E : List Nat) (H : Heap)
    (O : Target m) : Prop :=
  ∀ {m' : Nat} (f : TargetRen m' m) (E' : List Nat),
    (∀ x : Fin m, E'[(f x : Nat)]? = E[(x : Nat)]?) → ∀ ϖ H₁, H.Extends H₁ →
      ∃ a H₂ tr, Eval P ϖ H₁ E' (O.rename f) a H₂ tr ∧ H₁.Extends H₂ ∧ R H₂ t a

variable (v : Lifting.Variables) (ρ₁ : Lifting 0 [] []) (φ : Name → Term 0 [.var])
  (block : Name → Option Shape.Motive) (ρ ϱ : Multiplicity) {m₀ : Nat}
  (Ns₀ : TargetBranches m₀) (E₀ : List Nat) (Hb : Heap)

-- ADE: none.
/-- The leaf `x` given at a position that holds the type `D` of the block: the recursor
`rec_ρ · ◀ ϱ with N̄₀` of the shape of `D`, on a path that runs to an address that the relation `x.2`
relates to a term `t` of the type `x.1` of the position, when the recursor and the factor of the
shape are used at run time, gives a value related to the result of `t` at the motive of `D` at `t`,
in any environment that binds the variables of the branches renamed as `E₀` binds them, from any
heap that extends the heap `Hb` in which the cells of `E₀` live. -/
def RunResultLeaf (D : Name) (x : RunNestLeaf) : Prop :=
  ∀ b ms, ρ₁.block D = some b → block D = some ms → ∀ (t : Term 0 []), ValidTerm₀ sig ι t x.1 →
    ∀ {m : Nat} (g : TargetRen m m₀) (E : List Nat),
    (∀ x : Fin m₀, E[(g x : Nat)]? = E₀[(x : Nat)]?) → ∀ (H : Heap) (O : Target m),
    Hb.Extends H → (ρ ≠ .zero → ms.factor.run ≠ .zero → O.RunsTo P x.2 t E H) →
    ∀ ϖ H₁, H.Extends H₁ → ∃ w H₂ tr, Eval P ϖ H₁ E (ms.next.body ρ ϱ O (Ns₀.rename g)) w H₂ tr ∧
      H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ ((φ D).subst₀ (Subst₀.single t)) w (b.motive.subst₀ (Subst₀.single t))

-- ADE: none.
/-- The recursive result `e` of the closed term `t` of the type `A`, whose nesting is `ν`, at run
time: when `A` lifted at `t` is a type with a relation of run time, of which `e` is a term, the body
of the shape of `A`, on a path that runs to an address that `R` relates to `t` when the recursor and
the factor of the shape are used at run time, gives a value related to `e` at `A` lifted, in any
environment that binds the variables of the branches renamed as `E₀` binds them, from any heap that
extends the heap `Hb` in which the cells of `E₀` live. -/
def NestedRunsAt (ν : Nest Name) (A t : Term 0 []) (R : RunRel) : Prop :=
  ∀ (e A' : Term 0 []) (mr : Lifting.Result 0) (ms : Shape.Motive),
    Term.NestedResult sig v ρ₁ φ ν A t e → Term.Lifts sig v ρ₁ ν t A A' mr →
    A.shape v (Signature.shapes v .oneOne Grade.run sig) block Nesting.plain ν = some ms →
    (∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') → ValidTerm₀ sig ι e A' →
    ∀ {m : Nat} (g : TargetRen m m₀) (E : List Nat),
      (∀ x : Fin m₀, E[(g x : Nat)]? = E₀[(x : Nat)]?) →
      ∀ (H : Heap) (O : Target m), Hb.Extends H →
      (ρ ≠ .zero → ms.factor.run ≠ .zero → O.RunsTo P R t E H) → ∀ ϖ H₁, H.Extends H₁ →
        ∃ w H₂ tr, Eval P ϖ H₁ E (ms.next.body ρ ϱ O (Ns₀.rename g)) w H₂ tr ∧ H₁.Extends H₂ ∧
          RunsAs sig ι P H₂ e w A'

end

/-! ## Relations That Do Not Read the Computation -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

-- ADE: none.
/-- The relation of run time `R` relates the terms that compute as terms that it relates. -/
def RunLeafCongr (sig : Signature) (ι : Interpretation) (R : RunRel) : Prop :=
  ∀ H a a' w, (∀ u, Computesι sig ι a u ↔ Computesι sig ι a' u) → (R H a w ↔ R H a' w)

/-- A relation computed relates the terms that compute as terms that it relates. -/
theorem RunRel.computed_leafCongr (R : RunRel) : RunLeafCongr sig ι (R.computed sig ι) :=
  fun _ _ _ _ h => ⟨fun ⟨u, hu, hR⟩ => ⟨u, (h u).1 hu, hR⟩, fun ⟨u, hu, hR⟩ => ⟨u, (h u).2 hu, hR⟩⟩

/-- The relation of run time that the graph of the nestings gives a type relates the terms that
compute as terms that it relates, when the relations at its positions do. -/
theorem RunNestRel.congr_computes {n : Nat} {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel}
    (hR : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (hτ : Nest.All (fun x => RunLeafCongr sig ι x.2) τ) : RunLeafCongr sig ι R := by
  cases hR with
  | plain _ hF =>
    cases hF with
    | univ _ | univBelow _ _ _ => exact RunRel.computed_leafCongr _
    | prop _ | propBelow _ _ _ => exact fun _ _ _ _ _ => .rfl
  | direct _ =>
    cases hτ with
    | direct h => exact h
  | codata => exact RunRel.computed_leafCongr _
  | codataProp => exact fun _ _ _ _ _ => .rfl

end

/-! ## Nested Results of an Instance -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program} {v : Lifting.Variables}
  {ρ₁ : Lifting 0 [] []} {φ : Name → Term 0 [.var]} {block : Name → Option Shape.Motive}
  {ρ ϱ : Multiplicity} {m₀ : Nat} {Ns₀ : TargetBranches m₀} {E₀ : List Nat} {Hb : Heap}

/-- Arguments of a telescope whose entries are used `r` times more, which its relation of run time
relates to addresses, are arguments of the telescope that its equality relates to themselves, as
many as the addresses, and its relation of run time relates them, in each heap that extends the
first one, to addresses that are the same at each position used at run time, when the entries used
at run time are used at run time `r` times more too. -/
theorem RunTelRel.of_scale (hd : sig.Distinct) {n n' : Nat} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {r : Grade} {SΘ SΘ' : FieldsRel} {RΘ' : RunFieldsRel}
    (hΘ : TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain) Θ SΘ)
    (hΘ' : TelRel sig ι n' (fun m _ => levelRel sig ι m) .type (fun _ => .plain) (Θ.scale r) SΘ')
    (hRΘ' : RunTelRel sig ι P n' (fun m _ => levelRel sig ι m) (fun _ => .plain) (Θ.scale r) RΘ')
    (ts : Args 0 [] ps) (ts' : Args 0 [] (ps.map (Parameter.scale r))) (hts : ts.terms = ts'.terms)
    {H : Heap} {bs : List Nat} (hbs : RΘ' H ts'.terms bs) :
    SΘ ts.terms ts.terms ∧ bs.length = ps.length ∧
      ∀ RΘ, RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain) Θ RΘ →
        (∀ p ∈ ps, p.usage ∉ Mode.oneOne.erased → (p.scale r).usage ∉ Mode.oneOne.erased) →
        ∀ H', H.Extends H' → ∀ as : List Nat, as.length = ps.length →
          (∀ l (h : l < ps.length), ps[l].usage.run ≠ .zero → as[l]? = bs[l]?) →
          RΘ H' ts.terms as := by
  have ihm := Nat.forall_lt (levelRel_isPer (ι := ι) hd)
  have hSΘ' : SΘ' ts'.terms ts'.terms :=
    RunTelRel.fieldsRel hd (ihm _) hRΘ' (fun _ => rfl) _ _ hΘ' (fun _ => rfl) H ts'.terms bs hbs
  have hSS := TelRel.unique hd (ihm _) (TelRel.levelLe (Nat.le_max_left n' n) hΘ') _ _
    (TelRel.levelLe (Nat.le_max_right n' n) (hΘ.scale r))
  have hSΘ : SΘ ts.terms ts.terms := (hSS _ _).1 (hts ▸ hSΘ')
  have heq' := (TelRel.eqSubst_iff hd hΘ'
    (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) ts' ts').1 hSΘ'
  have hargs' := RunsAsArgs.of_runTelRel hRΘ'
    (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain)
    (Parameter.grades (ps.map (Parameter.scale r)))
    (fun _ _ h hu => by rw [Parameter.grades_of_getElem? h] at hu; exact hu) ts' heq' bs hbs
  have hlen : bs.length = ps.length := (RunsAsArgs.length hargs').trans (List.length_map _)
  refine ⟨hSΘ, hlen, fun RΘ hRΘ hus H' hH as hl hag => ?_⟩
  have heqΘ := (TelRel.eqSubst_iff hd hΘ
    (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h) (fun _ => .plain) ts ts).1 hSΘ
  refine RunTelRel.of_runsAsArgs hd hRΘ (Telescope.nestHeads_of_not _ fun _ ⟨_, h⟩ => nomatch h)
    (fun _ => .plain) (Parameter.grades ps)
    (fun _ _ h hu => by rw [Parameter.grades_of_getElem? h]; exact hu) ts heqΘ as ?_
  -- A position whose grade is used at run time is a position of the telescope.
  have hpos : ∀ l, Parameter.grades ps l ∉ Mode.oneOne.erased →
      ∃ h : l < ps.length, ps[l].usage ∉ Mode.oneOne.erased := fun l hg => by
    by_cases hlc : l < ps.length
    · exact ⟨hlc, by rwa [Parameter.grades_of_getElem? (List.getElem?_eq_getElem hlc)] at hg⟩
    · have hz : Parameter.grades ps l = Grade.zero := by
        simp [Parameter.grades, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (Nat.le_of_not_lt hlc)]
      exact absurd ((hz ▸ (by decide : Grade.zero ∈ Mode.oneOne.erased))) hg
  refine RunsAsArgs.of_scale r ts ts' hts (RunsAsArgs.of_addrs (by rw [hl, hlen])
    (fun l hg => ?_) (RunsAsArgs.of_counted (g' := Parameter.grades ps) (fun l hg => ?_)
      (RunsAsArgs.mono hd hH hargs')))
  · obtain ⟨hlc, hu⟩ := hpos l hg
    exact hag l hlc fun h0 => hu ((Mode.erased_values.1 _).2 h0)
  · obtain ⟨hlc, hu⟩ := hpos l hg
    rw [Parameter.grades_of_getElem?
      (by rw [List.getElem?_map, List.getElem?_eq_getElem hlc]; rfl)]
    exact hus _ (List.getElem_mem hlc) hu

/-- The observation that a built branch makes of a path that runs to an address related to `t` by
`R`, by the destructor of the case `i`, at the variables of its arguments, whose cells bind the
addresses `b̄`, runs to an address that `Rb` relates to the observation of `t`, when `R` relates `t`
only to observations that run so, at the arguments related to addresses that are those of `b̄` at
each position used at run time. -/
theorem Target.RunsTo.obs_args {R : RunRel} {t : Term 0 []} {m : Nat} {E : List Nat} {H : Heap}
    {O : Target m} (hO : O.RunsTo P R t E H) {ps : List Parameter} {i : Nat}
    {ψ : ResultOwnership Grade ps.length} {ς : Grade} {RΘ : RunFieldsRel}
    {Rb : Terms 0 [] → RunRel} {f : Term 0 (Scope.extend [] ps.length)}
    (hAbs : ∀ H a, R H t a → RunAbstractionRel P i ψ ς RΘ Rb f H a) (ts : Args 0 [] ps)
    {H' : Heap} (hH : H.Extends H') {πs : List Multiplicity} {bs : List Nat}
    (hlen : bs.length = ps.length) (hπs : πs.length = bs.length)
    (hrel : ∀ H'', H'.Extends H'' → ∀ as : List Nat, as.length = ps.length →
      (∀ l (h : l < ps.length), ps[l].usage.run ≠ .zero → as[l]? = bs[l]?) →
      RΘ H'' ts.terms as) :
    Target.RunsTo P (Rb ts.terms) (f.subst ts.toSubst)
      ((List.range' H'.length bs.length).reverse ++ E) (H'.bind πs bs)
      (.obs (O.rename (TargetRen.shift m (0 + ps.length))) i (ψ.map Grade.run) ς.run
        (Targets.ofVars (fun j => ps[j].usage.run) (fun j => ps[j].requirement.run)
          (Shape.argVar m ps.length))) := by
  intro m'' f' E'' hE'' ϖ₂ H₄ hH₄
  -- The path runs to an address related to `t`.
  obtain ⟨a₀, H₅, tr₁, hev₁, hext₁, hR₀⟩ := hO (f' ∘ TargetRen.shift m (0 + ps.length)) E''
    (fun x => by
      show E''[(f' (TargetRen.shift m (0 + ps.length) x) : Nat)]? = E[(x : Nat)]?
      rw [hE'']
      have e : ((TargetRen.shift m (0 + ps.length) x : Fin _) : Nat) = (x : Nat) + bs.length := by
        rw [hlen]
        show (x : Nat) + (0 + ps.length) = _
        rw [Nat.zero_add]
      rw [e, List.getElem?_reverse_range'_append_right])
    ϖ₂ H₄ ((hH.trans (List.prefix_append _ _)).trans hH₄)
  -- The arguments of the observation are the cells of the arguments of the branch.
  have hcells : ∀ k : Fin ps.length, ps[k].usage.run ≠ .zero → ∃ c' π',
      E''[(f' (Shape.argVar m ps.length k) : Nat)]? = some c' ∧
        H₅[c']? = some (.cell π' (bs[(k : Nat)]'(by rw [hlen]; exact k.isLt))) := fun k _ => by
    have hk : (k : Nat) < bs.length := by rw [hlen]; exact k.isLt
    have hi : bs.reverse[ps.length - 1 - (k : Nat)]? = some bs[(k : Nat)] := by
      rw [List.getElem?_reverse (by rw [hlen]; omega),
        show bs.length - 1 - (ps.length - 1 - (k : Nat)) = k by omega,
        List.getElem?_eq_getElem hk]
    obtain ⟨c', π', hc', hc⟩ := (Heap.binds_bind H' hπs).reverse.getElem? hi
    refine ⟨c', π', ?_, Heap.Extends.getElem? (hH₄.trans hext₁) hc⟩
    rw [hE'']
    show ((List.range' H'.length bs.length).reverse ++ E)[ps.length - 1 - (k : Nat)]? = _
    rw [List.getElem?_append_left (by simp; omega)]
    exact hc'
  obtain ⟨as₂, H₆, tr₂, hev₂, hext₂, hl₂, hk₂⟩ := Targets.evalAll_ofVars P ϖ₂ E''
    (fun j => ps[j].usage.run) (fun j => ps[j].requirement.run) (f' ∘ Shape.argVar m ps.length) H₅
    (fun k => bs[(k : Nat)]'(by rw [hlen]; exact k.isLt)) hcells
  have hRΘ₂ : RΘ H₆ ts.terms as₂ :=
    hrel H₆ ((List.prefix_append _ _).trans (hH₄.trans (hext₁.trans hext₂))) as₂ hl₂
      fun l hlc hu => by
        rw [hk₂ ⟨l, hlc⟩ hu, List.getElem?_eq_getElem (by rw [hlen]; exact hlc)]
  -- The observation of the value of the path at them runs to an address related to its result.
  obtain ⟨w₃, H₇, tr₃, hobs, hRb⟩ := hAbs H₅ a₀ hR₀ H₆ hext₂ ts as₂ hRΘ₂ ϖ₂
  have hmul : List.ofFn (fun j : Fin ps.length => ps[j].usage.run) = ps.map (·.usage.run) :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  have hreq : List.ofFn (fun j : Fin ps.length => ps[j].requirement.run) =
      ps.map (·.requirement.run) :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  let Ms : Targets m'' := Targets.ofVars (fun j : Fin ps.length => ps[j].usage.run)
    (fun j : Fin ps.length => ps[j].requirement.run) (f' ∘ Shape.argVar m ps.length)
  have hobs' : EvalObs P ϖ₂ H₆ a₀ i (ψ.map Grade.run) ς.run Ms.multiplicities Ms.requirements as₂
      w₃ H₇ tr₃ := by
    rw [Targets.multiplicities_ofVars, Targets.requirements_ofVars, hmul, hreq]
    exact hobs
  have hev := Eval.obs hev₁ hev₂ hobs'
  refine ⟨w₃, H₇, tr₁ ++ (tr₂ ++ tr₃), ?_, Eval.extends hev, hRb⟩
  rw [Target.rename, Target.rename_rename, Targets.rename_ofVars]
  exact hev

-- ADE: none.
/-- The recursive result of a closed term `t` of an instance of a codata type of `Σ` without
recursive destructor, at the nesting of an instance, at run time: the body of its shape, the
corecursor without state of the shape of the lifting, evaluates to a closure that is related to the
result, a corecursor of the lifting, at the instance lifted, when the recursive results of the
observations of `t` by the destructors used at run time are, and when these observations run, from
an address that `R` relates to `t`, to addresses related to them, when `ρ` is not `0`: the closure
observed by a destructor of the lifting used at run time runs its branch, which observes the path by
the destructor that it lifts, at the arguments of the observation, and gives the body of the shape
of the result on this observation, a path from the field again; when `ρ` is `0`, the body of the
recursor runs on the term of the skeleton of its motive, and the observation of the path is never
evaluated.
The recursor is used at run time when `ρ` is not `0`, `hr`, since the lifting scales the arguments of the destructors
that it lifts by its grade, while the branches built read them through the destructors lifted; and
the shapes of the types of the block carry the factor `11ᵖ` and the ownerships of the motives that
`ρ₁` gives them, `hb`, so that the arguments lifted have the shapes of their motives, at which the
shape of the instance is that of the lifting of the result. -/
theorem NestedRunsAt.inst (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hr : ρ ≠ .zero → v.recursion ∉ Mode.oneOne.erased)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    {n : Nat} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope}
    (hrec : ∀ r ∈ (T.body (.ofLists qs ps hq hp)).recursion decl.names, r = none)
    {ns : List (Nest Name)} {t : Term 0 []} {R : RunRel}
    (horacle : ∀ (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership Grade ps₁.length)
      (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ), p ∉ Mode.oneOne.erased →
      ∃ SΘ Rb i, sig.destructorCase D d = some i ∧
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)) SΘ ∧
        (ρ ≠ .zero → ∃ RΘ, RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain)
          ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)) RΘ ∧
          ∀ H a, R H t a →
            RunAbstractionRel P i ψ ς RΘ Rb (t.observation D qs ls ps as d ps₁) H a) ∧
        ∀ ts : Args 0 [] ps₁, SΘ ts.terms ts.terms →
          NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb
            (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hpos.nesting (Nesting.ofArgs ns))))
            ((B.substLevels (ls.getFin hl)).subst
              (Subst.append (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst))
            ((t.observation D qs ls ps as d ps₁).subst ts.toSubst) (Rb ts.terms)) :
    NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb (.inst ns) (.inst D qs ls ps as) t R := by
  intro e A' mA msO hres hL hsh hrun hval m g E hE H O hHb hO ϖ H₁ hH₁
  have hρ₁ : ∀ {a} (x : Var [] a), ρ₁.motive x = none := fun x => nomatch x
  have hid₁ : ∀ {a} (x : Var [] a), ρ₁.ren x = x := fun x => nomatch x
  obtain ⟨_, _, _, S, ms₁, Δ', as', nms, body, gs₁, rfl, has₁, hLm, hgs₁, hgt₁⟩ :=
    hres.inst_inv hd h
  have hDn : D ∈ decl.names := h.2.2 ▸ TypeDeclaration.codata_name_mem_names h.2.1
  obtain ⟨S', ms'', Δ'', as'', rfl, has'⟩ := hL.inst_inv hd h.1 hDn
  obtain ⟨rfl, rfl, hsg⟩ := InstanceArgs.Lifts.unique hd has₁ has'
  cases hsg
  have hq' : (qs ++ [v.quality]).length = decl.sorts + 1 := by
    rw [List.length_append, hq]
    rfl
  have hp' : (v.grades ps ms₁).length = decl.liftingGrades S := v.length_grades hp has₁.length_eq
  have hl' : (ls ++ ms₁.map (·.level)).length = decl.levels + S.length := by
    rw [List.length_append, hl, List.length_map, has₁.length_eq]
  obtain ⟨hΔ, -⟩ := has₁.instantiates hρ₁ S
    (fun i => (decl.liftingMotive S (.ofLists (qs ++ [v.quality]) (v.grades ps ms₁) hq' hp')
      i).substLevels ((ls ++ ms₁.map (·.level)).getFin hl'))
    (fun _ _ => Iff.rfl)
    (fun j h₁ h₂ => TypeDeclaration.liftingMotive_ofLists has₁.nodup hq' hl has₁.length_eq hl' hp
      hp' j h₁ h₂)
  subst hΔ
  -- The lifting, its type and its destructors.
  let declL := decl.lifting D S nms body
  let TL : CodataType declL.sorts declL.grades declL.levels declL.scope :=
    { name := Lifting.name D S
      usage := fun _ _ => .unrestrictedUnrestricted
      positive := fun _ => false
      destructors := nms
      body := body }
  have hTLmem : TL ∈ declL.codataTypes := List.mem_cons_self
  have hTL : sig.HasCodataType (Lifting.name D S) declL TL := ⟨hLm, hTLmem, rfl⟩
  have hLf := hord.lifts h.1 hDn hLm
  let I' : Instance (decl.sorts + 1) (decl.liftingGrades S) :=
    .ofLists (qs ++ [v.quality]) (v.grades ps ms₁) hq' hp'
  have hFrec : ∀ T' ∈ decl.codataTypes, T'.name = D →
      ∀ r ∈ (T'.body I'.lifted).recursion decl.names, r = none := fun T' hT' hn' => by
    cases eq_of_heq (hd.hasCodataType_unique ⟨h.1, hT', hn'⟩ h).2
    rw [Instance.lifted_ofLists qs ps v.quality _ hq hp]
    exact hrec
  have hrecL : ∀ r ∈ (TL.body I').recursion declL.names, r = none := hLf.recursion I' hFrec
  have hrs : ∀ {α : Type} (f : Name → α) (i : Nat),
      ((TL.body I').recursionAt declL.names i).map f = none := fun f i => by
    rw [Destructors.recursionAt_eq_none hrecL i]
    rfl
  -- The shape of the instance is the shape of the lifting at the shapes of the arguments lifted.
  obtain ⟨ms', hms', hmsA⟩ := has₁.shapes (fun _ h => h)
    (hord.liftingsHaveShapes (md := .oneOne) (ax := Grade.run) hd sig [] rfl)
    (ν := Nesting.plain) (fun x => nomatch x) hb
  have hne : S.zip ms' ≠ [] := fun h0 => by
    simp only [Term.shape, Nest.args, hms', h0] at hsh
    exact nomatch hsh
  rw [Term.shape_inst (fun _ h => by cases h) hms' hne] at hsh
  obtain ⟨⟨σ, π⟩, hσ, rfl⟩ := Option.map_eq_some_iff.1 hsh
  -- The body evaluates to a closure of the branches built from the shape.
  let Ps := σ.branches ρ ϱ O (Ns₀.rename g)
  let H₂ : Heap := H₁ ++ [.corec m E Ps [] [] []]
  have hwH : H₂[H₁.length]? = some (.corec m E Ps [] [] []) := by simp [H₂]
  refine ⟨H₁.length, H₂, [], .corec .nil, List.prefix_append _ _, ?_⟩
  -- The observations of the result, a corecursor of the lifting.
  let L' := (ls ++ ms₁.map (·.level)).getFin hl'
  let θ' : Subst 0 [] (.var :: decl.scope.lifted S) := (InstanceArgs.snoc (e := .var) as' t).toSubst
  generalize he : Term.corec v.recursion (Lifting.name D S) (qs ++ [v.quality])
    (ls ++ ms₁.map (·.level)) (v.grades ps ms₁) (.snoc (e := .var) as' t) .nil
    (.cons 0 .nil [] .nil) gs₁ = e at hval ⊢
  let o' : Observations := e.observation (Lifting.name D S) (qs ++ [v.quality])
    (ls ++ ms₁.map (·.level)) (v.grades ps ms₁) (.snoc (e := .var) as' t)
  have hc' : e.CorecObservations (Lifting.name D S) o' :=
    ⟨_, _, _, _, _, _, _, _, _, he.symm, by subst he; rfl⟩
  have hwe : Computesι sig ι e e := Whnf.computes (he ▸ .corec ..)
  -- The instance lifted, a type or a proposition with a relation of run time.
  have hIA : Computesι sig ι
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t))
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t)) :=
    (Whnf.inst ..).computes
  obtain ⟨vA, R', hcA, hR'⟩ := hrun
  cases Computesι.det hd hIA hcA
  refine ⟨_, hIA, ?_⟩
  cases hR' with
  | prop k b hk _ => exact .inl ⟨k, b, hk⟩
  | univ nR hU =>
    have hs : (declL.sort I').quality = .type := by
      cases levelRel_run_iff.1 hU with
      | data hc _ _ _ hv' => exact (hd.inst_data_codata hc hTL hv'.symm).elim
      | codata h' _ _ _ hv' hs' =>
        obtain ⟨-, hD', hqs, hls, hps, -⟩ := Term.inst.inj hv'
        subst hD' hqs hls hps
        obtain ⟨rfl, -⟩ := hd.hasCodataType_unique hTL h'
        exact hs'
    have hnp : ¬ ComputesToProp sig ι
        (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
          (v.grades ps ms₁) (.snoc (e := .var) as' t)) := fun ⟨v', hv', k, b, hk⟩ => by
      cases Computesι.det hd hIA hv'
      exact RunUnivRel.not_prop hd (levelRel_run_iff.1 hU) (levelRel_prop_iff.1 hk)
    obtain ⟨nR', Sr, hnR, hSr, rfl⟩ := HasRun.codata hd hTL hq' hl' hp' (.univ nR hU) hs
    subst hnR
    -- The equality of the destructors of the lifting relates the observations of the result.
    obtain ⟨vE, w₁, w₂, RE, hvE, hw₁, hw₂, hRE, hRw⟩ := hval.2.1 hnp
    cases Computesι.det hd hIA hvE
    cases Computesι.det hd hwe hw₁
    cases Computesι.det hd hwe hw₂
    obtain ⟨-, SE, hSE, rfl⟩ := (HasEq.instCodata_inv hd hTL hq' hl' hp' hRE).resolve_right
      fun ⟨hsp, _⟩ => absurd (hs.symm.trans hsp) (by decide)
    obtain ⟨XE, hXE, hXe⟩ := hRw
    obtain ⟨o₁, o₂, hc₁, hc₂, hSo⟩ := hXE TL hTLmem e e hXe
    obtain ⟨_, _, _, _, _, _, _, _, _, he₁, rfl⟩ := hc₁
    obtain ⟨_, _, _, _, _, _, _, _, _, he₂, rfl⟩ := hc₂
    let X : Name → RunRel := fun N Hx vx ax =>
      N = Lifting.name D S ∧ vx = e ∧ ax = H₁.length ∧ H₂.Extends Hx
    subst he
    cases he₁
    cases he₂
    have hPos := DesRel.positions hd L' (TL.body I') (hrs _) (hSE XE TL hTLmem) hSo
    -- The closure and the result are related by `(®_ν)`, for the relations `X` that relate the
    -- result to the closure in every heap that extends the one of the closure.
    refine .inr ⟨_, .univ nR hU, _, hwe, X, fun T' hT' Hx vx ax hX => ?_, rfl, rfl, rfl,
      List.prefix_refl _⟩
    cases List.mem_singleton.1 hT'
    obtain ⟨-, rfl, rfl, hHx⟩ := hX
    refine ⟨o', hc', RunDesRel.of_positions hd L' (TL.body I') (hrs _) (hSr X TL hTLmem) hPos ?_⟩
    intro d' p' q' ς' ps₁' Ξ' Θ' B' ψ' hpos' i' SΘ' RΘ' hp'u hi' hΘ' hRΘ' H' hH' ts' bs hts'
      hfield ϖ'
    -- The destructor of the type that the destructor of the lifting lifts.
    have hidx := hpos'.getElem?_index
    obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hpos, g₁, hg₁⟩ := hgs₁ _ d' hidx
    obtain ⟨mr, hps, hΘeq, hBL⟩ := TypeDeclaration.Lifts.observation (v := v) hd h hLf
      (ρ := ρ₁) hρ₁ hq hl hp hq' hl' hp' has₁ t hpos hpos' o'
    subst hps
    have ht₁ : t.rename ρ₁.ren = t := Term.rename_id_of hid₁ t
    rw (transparency := .default) [ht₁] at hΘeq hBL
    obtain ⟨σ₂, π₂, mS, rest, hσ₂, hmS, hp'g, hς', hps', hψ', hdrop, hfac⟩ :=
      hord.shapes_get hd h hLm has₁.nodup hq hp has₁.length_eq hq' hp' hmsA hpos hpos'
    rw [hσ] at hσ₂
    cases hσ₂
    have hiL : declL.codataCases[hpos'.index]? = some (0, TL, d') := by
      show (List.map (fun c => (0, TL, c)) nms ++ [])[hpos'.index]? = _
      rw [List.append_nil, List.getElem?_map, hidx]
      rfl
    obtain rfl : i' = hpos'.index :=
      Option.some.inj (hi'.symm.trans (hd.destructorCase_of_codataCases hLm hiL))
    have hpu : p ∉ Mode.oneOne.erased := fun hp₀ => hp'u ((Mode.erased_values.1 _).2
      (hp'g ▸ Lifting.resultGrade_run_eq_zero _ _ ((Mode.erased_values.1 _).1 hp₀)))
    have hprun : p'.run ≠ .zero := fun h0 => hp'u ((Mode.erased_values.1 p').2 h0)
    obtain ⟨SΘ, Rb, i, hi, hΘ, hRun, hNest⟩ := horacle d' p q ς ps₁ Ξ Θ B ψ hpos hpu
    -- The arguments of the destructor of the lifting are those of the destructor of the type.
    rw [Telescope.rename_id_of hid₁] at hΘeq
    have hΘ'' : TelRel sig ι ((declL.sort I').level.subst L').closedValue
        (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
        (((Θ.substLevels (ls.getFin hl)).subst
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)).scale
            (v.recursion * mr.factor)) SΘ' := hΘeq ▸ hΘ'
    have hRΘ'' : RunTelRel sig ι P ((declL.sort I').level.subst L').closedValue
        (fun m _ => levelRel sig ι m) (fun _ => .plain)
        (((Θ.substLevels (ls.getFin hl)).subst
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)).scale
            (v.recursion * mr.factor)) RΘ' := hΘeq ▸ hRΘ'
    obtain ⟨ts, hts⟩ := Args.exists_terms_map (Parameter.scale (v.recursion * mr.factor)) ps₁ ts'
    obtain ⟨hSΘ, hlen, hrel⟩ := RunTelRel.of_scale hd hΘ hΘ'' hRΘ'' ts ts' hts hts'
    have hSΘ' : SΘ' ts'.terms ts'.terms := RunTelRel.fieldsRel hd
      (Nat.forall_lt (levelRel_isPer hd) _)
      hRΘ' (fun _ => rfl) _ _ hΘ' (fun _ => rfl) H' ts'.terms bs hts'
    -- The recursive result of the observation, a term of the result of the destructor lifted.
    have hφ : (fun E => ((φ E).rename (Ren.lift (Ren.weakenN ps₁.length))).subst
        (Subst.lift ts.toSubst)) = φ := funext fun E => Term.subst_lift_toSubst_rename ts (φ E)
    have hN := (hgt₁ _ d' p q ς ps₁ Ξ Θ B ψ g₁ hidx hpos hg₁).subst
      (Lifting.Substitutes.closedArgs ρ₁ ts)
    rw [hφ, Term.subst_append] at hN
    have hL'' := hBL.subst (Lifting.Substitutes.closedArgs ρ₁ ts)
    rw [Term.rename_id_of (Ren.liftN_id_of _ hid₁), Term.subst_append,
      Term.subst_toSubst_cast _ _ ts ts' hts, Term.subst_append] at hL''
    have hshape := TypeDeclaration.Lifts.shape_result hd h hLf (ρ := ρ₁) hq hl hp hq' hl' hp' has₁
      t hms' hpos hpos' ts (fun hA _ hν hbA =>
        (hA.shape_eq hd hord (md := .oneOne) (ax := Grade.run) hν hbA).imp fun _ h => h.1) hb
    rw [Term.subst_append] at hshape
    obtain ⟨vB, FB, RB, hvB, hFB, hRB⟩ := hfield
    have hrecN : (TL.body I').resultName declL.names d' = none :=
      (hpos'.resultName declL.names (hd.destructors_nodup hTL)).trans
        (hLf.blockName_pos I' hFrec hpos')
    have hred : ∀ w, Computesι sig ι ((o' d' _).subst ts'.toSubst) w ↔
        Computesι sig ι (g₁.subst ts.toSubst) w := fun w => by
      rw [Term.observation_subst_args, ← hts]
      exact Computesι.red_iff hd (Red.beta_stateless hTL hq' hl' hp' hiL hrecN hg₁ ts)
    have hvalI := FieldRel.validEqTerm hd hFB hvB ((hFB.congr_computes (.inr ⟨hred, hred⟩)).1
      (hPos d' p' q' ς' _ Ξ' Θ' B' ψ' hpos' SΘ' hΘ' ts' ts' hSΘ' vB FB hvB hFB))
    obtain ⟨R'', hR''⟩ := hRB.hasRun
    -- The branch of the destructor, which observes the path by the destructor that it lifts, at
    -- its arguments, and gives the body of the shape of the result on this observation.
    have hP := Shape.branches_get ρ ϱ O (Ns₀.rename g) hpos'.index σ hdrop
    let c := ps₁.length
    let O' : Target (m + (0 + c)) :=
      .obs (O.rename (TargetRen.shift m (0 + c))) ((sig.destructorCase D d').getD 0)
        (ψ.map Grade.run) ς.run
        (Targets.ofVars (fun j => ps₁[j].usage.run) (fun j => ps₁[j].requirement.run)
          (Shape.argVar m c))
    let g' : TargetRen (m + (0 + c)) m₀ := TargetRen.shift m (0 + c) ∘ g
    let πs' : Fin c → Multiplicity := fun j =>
      ((Mode.oneOne ⊙ p').grade * (ps₁[j].scale (v.recursion * mS.factor)).usage).run
    let Hd := H'.bind ((List.ofFn (Fin.elim0 : Fin 0 → Multiplicity) ++ List.ofFn πs').map
      (ϖ' * ·)) ([] ++ bs)
    let E' := (List.range' H'.length ([] ++ bs).length).reverse ++ E
    have hlen' : ([] ++ bs).length = c := hlen
    have hE' : ∀ x : Fin m₀, E'[(g' x : Nat)]? = E₀[(x : Nat)]? := fun x => by
      have e : ((g' x : Fin _) : Nat) = (g x : Nat) + ([] ++ bs).length := by
        rw [hlen']
        show (g x : Nat) + (0 + c) = _
        rw [Nat.zero_add]
      rw [e, List.getElem?_reverse_range'_append_right]
      exact hE x
    have hO' : ρ ≠ .zero → mS.factor.run ≠ .zero →
        O'.RunsTo P (Rb ts.terms) ((t.observation D qs ls ps as d' ps₁).subst ts.toSubst) E' Hd := by
      intro hρ hmf
      obtain ⟨RΘ, hRΘ, hAbs⟩ := hRun hρ
      -- The factor of the shape of the instance is used at run time, so that the path runs.
      have hπ : π.run ≠ .zero := fun h0 => by
        rcases Multiplicity.modality.zero.mul_eq_zero _ _ (hfac h0) with h1 | h1
        · exact hprun h1
        · exact hmf h1
      have hr' : v.recursion * mS.factor ∉ Mode.oneOne.erased :=
        fun h => hmf ((Mode.erased_values.1 _).1 ((Mode.erasesUncounted .oneOne).mul _ _ (hr hρ) h))
      have hus : ∀ p ∈ ps₁, p.usage ∉ Mode.oneOne.erased →
          (p.scale (v.recursion * mr.factor)).usage ∉ Mode.oneOne.erased := fun p hp hu => by
        rw [List.map_inj_left.1 hps' p hp]
        exact fun h => hu ((Mode.erasesUncounted .oneOne).mul _ _ hr' h)
      have hcase : (sig.destructorCase D d').getD 0 = i := by rw [hi]; rfl
      intro m'' f' E'' hE''
      exact Target.RunsTo.obs_args (i := (sig.destructorCase D d').getD 0)
        (πs := (List.ofFn (Fin.elim0 : Fin 0 → Multiplicity) ++ List.ofFn πs').map (ϖ' * ·))
        (hO hρ hπ) (by rw [hcase]; exact hAbs) ts
        (hH₁.trans ((List.prefix_append _ _).trans (hHx.trans hH'))) hlen (by simp [hlen]; rfl)
        (hrel RΘ hRΘ hus) f' E'' hE''
    obtain ⟨w'', H₃, tr, hev, hext, hrunI⟩ := hNest ts hSΘ (g₁.subst ts.toSubst) _ mr mS hN hL''
      (hshape.trans hmS) ⟨vB, R'', hvB, hR''⟩ hvalI g' E' hE' Hd O'
      (hHb.trans (hH₁.trans ((List.prefix_append _ _).trans ((hHx.trans hH').trans
        (List.prefix_append _ _))))) hO' ϖ' Hd (List.prefix_refl _)
    have hbody : (if p'.run = .zero then (.erased : Target (m + (0 + c))) else
        mS.next.body ρ ϱ O' ((Ns₀.rename g).rename (TargetRen.shift m (0 + c)))) =
        mS.next.body ρ ϱ O' (Ns₀.rename g') := by
      simp only [hprun, ↓reduceIte]
      rw [TargetBranches.rename_rename]
    refine ⟨w'', H₃, tr, .beta (Heap.Extends.getElem? (hHx.trans hH') hwH) hP rfl hlen (fun j => j.elim0)
      (fun j => ?_) (fun j => j.elim0) (fun j => ?_)
      (congrArg (fun x : Σ c, ResultOwnership Grade c =>
        (⟨x.1, x.2.map Grade.run⟩ : Σ c, ResultOwnership Multiplicity c)) hψ')
      (hς' ▸ Multiplicity.le_refl' _) (hbody ▸ hev) .none, (RunsAs.congr_computes hred).2 hrunI⟩
    · refine ⟨_, ?_, Multiplicity.le_refl' _⟩
      simp only [hps', List.map_map, List.getElem?_map, Mode.grade_odot_of_not_erased p' hp'u,
        Grade.modality.semiring.one_mul, List.getElem?_eq_getElem j.isLt]
      rfl
    · refine ⟨_, ?_, Multiplicity.le_refl' _⟩
      simp only [hps', List.map_map, List.getElem?_map, List.getElem?_eq_getElem j.isLt]
      rfl

/-- The recursive result of a closed term at a nesting without position, which no type lifts,
vacuously runs. -/
theorem NestedRunsAt.plain (A t : Term 0 []) (R : RunRel) :
    NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb .plain A t R :=
  fun _ _ _ _ _ hL => (hL.not_avoidsLifted rfl fun x _ => nomatch x).elim

/-- The recursive result of a closed term of a type at a position that holds a type of the block,
which has the levels of the type of the leaf up to their values, runs as the leaf of the position
says. -/
theorem NestedRunsAt.direct {D : Name} {x : RunNestLeaf}
    (hx : RunResultLeaf sig ι P ρ₁ φ block ρ ϱ Ns₀ E₀ Hb D x) {A t : Term 0 []}
    (hA : Term.LevelEquiv x.1 A) (ht : ValidTerm₀ sig ι t A) :
    NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb (.direct D) A t x.2 := by
  intro e A' mr ms hres hL hsh _ _ m g E hE H O hHb hO ϖ H₁ hH₁
  cases hres with
  | block hD =>
    cases hL with
    | block hD' =>
      cases Option.some.inj (hD.symm.trans hD')
      exact hx _ ms hD hsh t
        (ValidEqTerm₀.levelEquiv ht (.refl t) (.refl t) hA.symm) g E hE H O hHb hO ϖ H₁ hH₁
    | inst _ _ hn => exact absurd rfl (hn _)
  | inst _ hn => exact absurd rfl (hn _)

/-- An abstraction related at run time to an address is related to it when it computes as an
abstraction that is, at a relation of its result that does not read the computation. -/
theorem RunAbstractionRel.congr_computes {ps : List Parameter} {i : Nat}
    {ψ : ResultOwnership Grade ps.length} {ς : Grade} {RΘ : RunFieldsRel}
    {Rb : Terms 0 [] → RunRel} {f g : Term 0 (Scope.extend [] ps.length)} {H : Heap} {a : Nat}
    (hRb : ∀ H' (ts : Args 0 [] ps) bs, RΘ H' ts.terms bs → RunLeafCongr sig ι (Rb ts.terms))
    (hfg : ∀ τ w, Computesι sig ι (f.subst τ) w ↔ Computesι sig ι (g.subst τ) w)
    (h : RunAbstractionRel P i ψ ς RΘ Rb g H a) : RunAbstractionRel P i ψ ς RΘ Rb f H a :=
  fun H' hH ts bs hts ϖ =>
    let ⟨w, H'', tr, hev, hR⟩ := h H' hH ts bs hts ϖ
    ⟨w, H'', tr, hev, (hRb H' ts bs hts H'' _ _ w fun u => hfg ts.toSubst u).2 hR⟩

end

/-! ## Observations of a Term of an Instance -/

section

variable {sig : Signature} {ι : Interpretation}

/-- The observations of a closed term of an instance of a codata type of `Σ`, in a universe of
types, none of whose destructors is recursive, are related to themselves by the equality of the
destructors of the type: the term computes to a corecursor whose observations the equality
relates, and its observations compute as them. -/
theorem ValidTerm₀.desRel (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope}
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hrec : ∀ r ∈ (T.body (.ofLists qs ps hq hp)).recursion decl.names, r = none)
    {t : Term 0 []} (ht : ValidTerm₀ sig ι t (.inst D qs ls ps as)) :
    ∃ (rs : Nat → Option TermRel) (SE : ObsRel), (∀ i, rs i = none) ∧
      DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) .type rs
        ((T.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst SE ∧
      SE (t.observation D qs ls ps as) (t.observation D qs ls ps as) := by
  have hI : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    (Whnf.inst ..).computes
  obtain ⟨-, v₀, -, R₀, hv₀, -, hR₀, -, -⟩ := ht.1
  cases Computesι.det hd hI hv₀
  obtain ⟨-, Se, hSe, rfl⟩ := (HasEq.instCodata_inv hd h hq hl hp hR₀).resolve_right
    fun ⟨hs', _⟩ => nomatch hκ.symm.trans hs'
  have hU₀ : (levelRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue).univ
      (.inst D qs ls ps as) (CodataType.blockRel decl.codataTypes Se D) :=
    levelRel_univ_iff.2 (.codata h hq hl hp rfl hκ rfl Se hSe)
  have hnp := Computesι.not_computesToProp hd hI hU₀
  obtain ⟨v₁, w₁, w₂, R', hv₁, hw₁, hw₂, hR', hrel⟩ := ht.2.1 hnp
  cases Computesι.det hd hI hv₁
  cases Computesι.det hd hw₁ hw₂
  have hmono := DesRel.blockMono hd hSe
  have hrel' := (HasEq.unique hd hR' hR₀ w₁ w₁).1 hrel
  rw [← h.2.2] at hrel'
  obtain ⟨o₁, o₂, hc₁, hc₂, ho⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel'
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := hc₁
  obtain ⟨_, _, _, _, _, _, _, _, _, he, rfl⟩ := hc₂
  cases he
  have hrs : ∀ i, ((T.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
      (fun D' => (CodataType.blockRel decl.codataTypes Se D').computed sig ι) = none := fun i => by
    rw [Destructors.recursionAt_eq_none hrec i]
    rfl
  have hDes := hSe (CodataType.blockRel decl.codataTypes Se) T h.2.1
  -- The observations of the term compute as those of the corecursor, and conversely.
  rcases ObsEquiv.of_computes (s := .type) hd (qs := qs) (ls := ls) (ps := ps) (as := as) hw₁
    ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ with hf | hf
  · exact nomatch hf
  refine ⟨_, _, hrs, hDes, DesRel.obsEquiv hd (fun i R hi => by rw [hrs i] at hi; cases hi) hDes
    ho (.inr fun d ps τ w => (hf d ps τ w).symm) (.inr fun d ps τ w => (hf d ps τ w).symm)⟩

end

/-! ## Nested Results at Run Time -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program} {v : Lifting.Variables}
  {ρ₁ : Lifting 0 [] []} {φ : Name → Term 0 [.var]} {block : Name → Option Shape.Motive}
  {ρ ϱ : Multiplicity} {m₀ : Nat} {Ns₀ : TargetBranches m₀} {E₀ : List Nat} {Hb : Heap}

mutual

-- ADE: none.
/-- The recursive result of a closed term of a type, which the graph of the nestings of run time
reads at the relation `R`, runs: its shape, on a path that runs to an address that `R` relates to
the term, gives a value related to the result at the type lifted, in a signature whose names are
distinct, whose liftings are those of its types, in their order, and whose destructors of a codata
proposition, at an instance that the constraint of its block admits, are erased, when the recursor
is used at run time, the shapes of the types of the block follow `ρ₁`, and the relation at each
position runs as the leaf of the position says and does not read the computation. -/
theorem RunNestRel.nestedRuns (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hr : v.recursion ∉ Mode.oneOne.erased)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    (hprop : sig.ErasesPropDestructors)
    {n : Nat} {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel} :
    RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R →
      Nest.All (fun x => RunLeafCongr sig ι x.2) τ →
      ∀ {ν : Nest Name}, Nest.Rel (RunResultLeaf sig ι P ρ₁ φ block ρ ϱ Ns₀ E₀ Hb) ν τ →
      ∀ t, ValidTerm₀ sig ι t A → NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb ν A t R
  | .plain _ _, _, _, hν, _, _ => by
    cases hν with
    | plain => exact NestedRunsAt.plain _ _ _
  | .direct hA, _, _, hν, _, ht => by
    cases hν with
    | direct hx => exact NestedRunsAt.direct hx hA ht
  | .codata (ls := ls) h hq hl hp hA hκ _ hrec _ hS, hτ, _, hν, _, ht => by
    subst hA
    cases hν with
    | inst hνs =>
      cases hτ with
      | inst hτs =>
        obtain ⟨_, _, hrs, hDes, hSf⟩ := ValidTerm₀.desRel hd h hq hl hp hκ hrec ht
        refine NestedRunsAt.inst (n := n) hd hord (fun _ => hr) hb h hq hl hp hrec
          fun d p q ς ps₁ Ξ Θ B ψ hpos hpu => ?_
        obtain ⟨SΘ, RΘ, Rb, i, hi, hΘ, hRΘ, hAbs, hN⟩ := RunNestDesRel.nestedRuns hd hord hr
          hb hprop (hpos.substLevels (ls.getFin hl)) hS (Nesting.ofArgs_rel₃ hτs)
          (Nesting.ofArgs_rel₃ hνs) hrs hDes hSf hpu
          (funext fun _ => funext fun x => (hpos.obsSubst_posSubstLevels _ _ _ x).symm)
          (hpos.nest_substLevels _ _)
        exact ⟨SΘ, Rb, i, hi, hΘ, fun _ => ⟨RΘ, hRΘ,
          fun H a ⟨_, hu, o, hco, hSo⟩ => hAbs H o a (ObsEquiv.of_computes hd hu hco) hSo⟩, hN⟩
  | .codataProp h hq hl hp hA hadm hκ _ hrec, _, _, hν, _, _ => by
    subst hA
    cases hν with
    | inst _ =>
      exact NestedRunsAt.inst (n := n) hd hord (fun _ => hr) hb h hq hl hp hrec
        fun _ _ _ _ _ _ _ _ _ hpos hpu => absurd (hprop h hq hp hadm hκ hpos) hpu
termination_by structural h _ _ _ _ _ => h

-- ADE: none.
/-- At a position of a destructor, whose grade is used at run time, in destructors that the graph
of the nestings of run time reads, and that the equality of the destructors reads too, the
observations `f`, which this equality relates to themselves, give the telescope of the destructor,
with its equality and its relation of run time, and a relation of run time of its result: the
observation of an address related to observations that `f` computes as runs to addresses related
to the observations by `f`, and the recursive results of these observations run. -/
theorem RunNestDesRel.nestedRuns (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hr : v.recursion ∉ Mode.oneOne.erased)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    (hprop : sig.ErasesPropDestructors)
    {n : Nat} {D : Name} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {nms : List Name} → {ds : Destructors 0 Γ nms} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : ds.Pos d p q ς Ξ Θ B ψ) →
      {ν' : Nesting RunNestLeaf Γ} → {θ : Subst 0 [] Γ} → {S : RunObsRel} →
      RunNestDesRel sig ι P n (fun m _ => levelRel sig ι m) D @ν' ds @θ S →
      Nesting.All (fun x => RunLeafCongr sig ι x.2) @ν' → {ν : Nesting Name Γ} →
      Nesting.Rel (RunResultLeaf sig ι P ρ₁ φ block ρ ϱ Ns₀ E₀ Hb) @ν @ν' →
      {nE : Nat} → {rs : Nat → Option TermRel} → (∀ i, rs i = none) → {SE : ObsRel} →
      DesRel sig ι nE (fun m _ => levelRel sig ι m) .type rs ds @θ SE →
      {f : Observations} → SE f f → p ∉ Mode.oneOne.erased →
      ∀ {σ : (e : Scope.Entry) → Var Ξ e → Term 0 (Scope.extend [] e.params.length)},
      (σ = fun _ x => hpos.obsSubst f θ x) → ∀ {νB : Nest Name},
      νB = B.nest (fun _ => none) (Nesting.liftN ps.length (hpos.nesting @ν)) →
      ∃ SΘ RΘ Rb i, sig.destructorCase D d = some i ∧
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          (Θ.subst fun {e} x => σ e x) SΘ ∧
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain)
          (Θ.subst fun {e} x => σ e x) RΘ ∧
        (∀ H o a, ObsEquiv sig ι .type f o → S H o a →
          RunAbstractionRel P i ψ ς RΘ Rb (f d ps) H a) ∧
        ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
          NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ Hb νB
            (B.subst (Subst.append (fun {e} x => σ e x) ts.toSubst)) ((f d ps).subst ts.toSubst)
            (Rb ts.terms)
  | _, _, _, _, _, B, _, .here, _, _, _,
      .cons (SΘ := SΘ) (RΘ := RΘ) (i := i) hi hν hΘ hRΘ _ R _ hR _ _ _, _, _, hRel, _, _, _, _,
      _, f, _, _, _, hσ, _, hνB => by
    subst hσ hνB
    refine ⟨SΘ, RΘ, R, i, hi, hΘ, hRΘ, fun H o a ho hSo => ?_, fun ts _ => ?_⟩
    · -- The observation by `o` runs, and the observation by `f` computes as it.
      refine RunAbstractionRel.congr_computes (fun H' ts bs hts =>
        RunNestRel.congr_computes
          (hR ts (RunTelRel.fieldsRel hd (Nat.forall_lt (levelRel_isPer hd) _) hRΘ
          (fun _ => rfl) _ _ hΘ
          (fun _ => rfl) H' ts.terms bs hts)) .plain) (fun τ w => ?_) (hSo.2.1 ‹_›)
      rcases ho with ho | ho
      · exact nomatch ho
      · exact ho d ps τ w
    · -- The result has no position.
      simp only [Destructors.Pos.nesting]
      rw [((Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B).eq_plain.1.1 hν)]
      exact NestedRunsAt.plain _ _ _
  | _, _, _, _, _, B, _, .here, _, _, _,
      .nested (SΘ := SΘ) (RΘ := RΘ) (i := i) hi _ hΘ hRΘ R hR _ _, hAll, _, hRel, nE, _, hrs, _,
      hE, f, hSf, hpu, _, hσ, _, hνB => by
    subst hσ hνB
    have hAllB := Term.nest_all (p := fun x : RunNestLeaf => RunLeafCongr sig ι x.2)
      (mark := fun _ => none) (fun _ _ h => nomatch h) (Nesting.liftN_rel₃ ps.length hAll) B
    refine ⟨SΘ, RΘ, R, i, hi, hΘ, hRΘ, fun H o a ho hSo => ?_, fun ts hts => ?_⟩
    · -- The observation by `o` runs, and the observation by `f` computes as it.
      refine RunAbstractionRel.congr_computes (fun H' ts bs hts =>
        RunNestRel.congr_computes
          (hR ts (RunTelRel.fieldsRel hd (Nat.forall_lt (levelRel_isPer hd) _) hRΘ
          (fun _ => rfl) _ _ hΘ
          (fun _ => rfl) H' ts.terms bs hts)) hAllB) (fun τ w => ?_) (hSo.1 hpu)
      rcases ho with ho | ho
      · exact nomatch ho
      · exact ho d ps τ w
    · -- The observation is a term of the result, which the equality of the destructors gives.
      cases hE with
      | recursive hrs' => rw [hrs 0] at hrs'; cases hrs'
      | cons hΘE _ hBE hFE _ _ _ _ _ =>
        have htE := (TelRel.unique hd (Nat.forall_lt (levelRel_isPer hd) _)
          (TelRel.levelLe (Nat.le_max_left n nE) hΘ) _ _
          (TelRel.levelLe (Nat.le_max_right n nE) hΘE) _ _).1 hts
        obtain ⟨vB, hvB⟩ := hBE ts htE
        exact RunNestRel.nestedRuns hd hord hr hb hprop (hR ts hts) hAllB
          (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B) _
          (FieldRel.validEqTerm hd (hFE ts htE vB hvB) hvB (hSf.1 ts ts htE))
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _,
      .cons (SΘ := SΘ) _ _ hΘ _ F _ hF _ G hG hresp, hAll, _, hRel, nE, _, hrs, _, hE, f, hSf, hpu,
      _, hσ, _, hνB => by
    cases hE with
    | recursive hrs' => rw [hrs 0] at hrs'; cases hrs'
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ SΘE hΘE FE _ hFE _ _ hGE _ _ =>
      have ihE := Nat.forall_lt (levelRel_isPer (ι := ι) hd) (max n nE)
      have hSp := TelRel.isPer hd (Nat.forall_lt (levelRel_isPer hd) _) (fun _ => .plain) hΘ
      have hFv : ∀ ts : Args 0 [] ps', SΘ ts.terms ts.terms → ∃ v,
          Computesι sig ι _ v ∧ FieldRel sig ι n (fun m _ => levelRel sig ι m) .type v (F ts.terms) :=
        fun ts hts => by
          cases hF ts hts with
          | plain hA hF' => exact ⟨_, hA, hF'⟩
      -- The observations by `f` at `d'` are related to themselves by the clause of `d'`.
      have hAf : AbstractionRel SΘ F (f d' ps') (f d' ps') := fun ts us hts => by
        have htt := hSp.trans hts (hSp.symm hts)
        obtain ⟨vB, hvB, hFB⟩ := hFv ts htt
        have htsE := (TelRel.unique hd ihE (TelRel.levelLe (Nat.le_max_left n nE) hΘ) _ _
          (TelRel.levelLe (Nat.le_max_right n nE) hΘE) _ _).1 hts
        have httE := (TelRel.unique hd ihE (TelRel.levelLe (Nat.le_max_left n nE) hΘ) _ _
          (TelRel.levelLe (Nat.le_max_right n nE) hΘE) _ _).1 htt
        exact (FieldRel.unique hd ihE ((hFE ts httE vB hvB).levelLe (Nat.le_max_right n nE)) _ _
          (hFB.levelLe (Nat.le_max_left n nE)) _ _).1 (hSf.1 ts us htsE)
      obtain ⟨SΘ₁, RΘ₁, Rb, i, hi, hΘ₁, hRΘ₁, hAbs, hN⟩ := RunNestDesRel.nestedRuns hd hord
        hr hb hprop hp (hG _ hAf) (Nesting.lift_rel₃ hAll) (Nesting.lift_rel₃ hRel)
        (fun i => hrs (i + 1)) (hGE _ hSf.1) hSf.2 hpu hσ hνB
      refine ⟨SΘ₁, RΘ₁, Rb, i, hi, hΘ₁, hRΘ₁, fun H o a ho hSo => hAbs H o a ho ?_, hN⟩
      -- The destructors after `d'` are the same for the observations by `f` and by `o` at `d'`.
      have hfo : AbstractionRel SΘ F (f d' ps') (o d' ps') :=
        (AbstractionRel.congr_computes (s := .type) hSp
          (fun ts hts => (hFv ts hts).imp fun _ h => h.2)
          (ho.imp_right fun h => ⟨fun _ _ => .rfl, fun τ w => h d' ps' τ w⟩)).1 hAf
      exact (hresp _ _ hfo H o a).2 hSo.2.2
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _, .nested _ _ _ _ _ _ _ hG,
      hAll, _, hRel, _, _, hrs, _, hE, f, hSf, hpu, _, hσ, _, hνB => by
    cases hE with
    | recursive hrs' => rw [hrs 0] at hrs'; cases hrs'
    | cons _ _ _ _ _ _ hGE _ _ =>
      obtain ⟨SΘ₁, RΘ₁, Rb, i, hi, hΘ₁, hRΘ₁, hAbs, hN⟩ := RunNestDesRel.nestedRuns hd hord
        hr hb hprop hp (hG (f d' ps')) (Nesting.lift_rel₃ hAll) (Nesting.lift_rel₃ hRel)
        (fun i => hrs (i + 1)) (hGE _ hSf.1) hSf.2 hpu hσ hνB
      exact ⟨SΘ₁, RΘ₁, Rb, i, hi, hΘ₁, hRΘ₁, fun H o a ho hSo => hAbs H o a ho hSo.2, hN⟩
termination_by structural _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => h

end

-- ADE: none.
/-- `n.Ξ` at run time: the corecursor without state of the shape of the type of a nested field,
whose field is bound to a cell, in a heap that extends the heap `Hb` of the cells of `E₀`, that
holds an address that the relation of run time of the type relates to the field, evaluates to a
value related to the recursive result of the field at the type lifted, when the hypotheses of
`RunNestRel.nestedRuns` hold and the relations of the positions are monotone in the heap: the path
from the field is the field itself. -/
theorem RunsAs.nested (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hr : v.recursion ∉ Mode.oneOne.erased)
    (hb : ∀ D b, ρ₁.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩)
    (hprop : sig.ErasesPropDestructors)
    {n : Nat} {τ : Nest RunNestLeaf} {A : Term 0 []} {R : RunRel}
    (hR : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (hτ : Nest.All (fun x => RunLeafCongr sig ι x.2) τ) (hτm : Nest.All (fun x => RunRel.Monotone x.2) τ)
    {ν : Nest Name} (hν : Nest.Rel (RunResultLeaf sig ι P ρ₁ φ block ρ ϱ Ns₀ E₀ Hb) ν τ)
    {t e A' : Term 0 []} (ht : ValidTerm₀ sig ι t A) {mr : Lifting.Result 0}
    (hres : Term.NestedResult sig v ρ₁ φ ν A t e) (hL : Term.Lifts sig v ρ₁ ν t A A' mr)
    {σ : Shape} {π χ : Grade}
    (hsh : A.shape v (Signature.shapes v .oneOne Grade.run sig) block Nesting.plain ν =
      some ⟨.lifting σ, π, χ⟩)
    (hrun : ∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') (hval : ValidTerm₀ sig ι e A')
    {c : Nat} {H : Heap} (hHb : Hb.Extends H)
    (hc : π.run ≠ .zero → ∃ π' a, H[c]? = some (.cell π' a) ∧ R H t a) (ϖ : Multiplicity)
    (H₁ : Heap) (hH₁ : H.Extends H₁) :
    ∃ w H₂ tr, Eval P ϖ H₁ (c :: E₀) (Target.nested ρ ϱ σ Ns₀) w H₂ tr ∧ H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ e w A' := by
  have hmono : R.Monotone := levelRel_runNest_mono hd hR hτm
  refine RunNestRel.nestedRuns hd hord hr hb hprop hR hτ hν t ht e A' mr _ hres hL hsh hrun
    hval (TargetRen.shift m₀ 1) (c :: E₀) (fun x => List.getElem?_cons_succ) H (.var 0) hHb
    (fun _ hπ m' f E' hE' ϖ' H' hH' => ?_) ϖ H₁ hH₁
  -- The path from the field is the field, whose cell holds an address related to it.
  obtain ⟨π', a, hca, hRa⟩ := hc hπ
  have hE0 : E'[(f 0 : Nat)]? = some c := hE' 0
  exact ⟨a, H', [c], .var hE0 (Heap.Extends.getElem? hH' hca), List.prefix_refl _, hmono hH' hRa⟩

end

end Sic.Core
