module

public import Sic.Core.Erasure.Results
public import Sic.Core.Lifting.Extension
public import Sic.Core.Nesting.Relation
public import Sic.Core.RunTime.Relation
import Sic.Core.Erasure.Results.Lifting
import Sic.Core.Erasure.Results.Substitution
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Recursion
import Sic.Core.Lifting.Shape
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Results.Substitution
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Observations
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors.Nested
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

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

/-! ## Branches Built From a Shape -/

/-- The branch built at the index `k` from a shape is the branch of the element of the shape at this
index: without state, it binds the arguments of the lifted destructor and observes the term by the
destructor that it lifts, then gives the result of this observation, or `↯` when the destructor is
never observed at run time. -/
theorem Shape.branches_get {m : Nat} (ρ ϱ : Multiplicity) (M : Target m) (Ns : TargetBranches m) :
    (k : Nat) → (σ : Shape) → {i c : Nat} → {ρᵢ : Multiplicity} →
      {πs ϱs πs' ϱs' : Fin c → Multiplicity} → {ψ : ResultOwnership Multiplicity c} →
      {ς : Multiplicity} → {ψ₀ : ResultOwnership Multiplicity c} → {ς₀ : Multiplicity} →
      {next : Shape.Next} → {rest : Shape} →
      σ.drop k = .cons i c ρᵢ πs ϱs πs' ϱs' ψ ς ψ₀ ς₀ next rest →
      (σ.branches ρ ϱ M Ns).get k = some (.none, ⟨0, c, Fin.elim0, Fin.elim0, πs', ϱs', ψ, ς,
        if ρᵢ = .zero then .erased else
          next.body ρ ϱ
            (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
              (Targets.ofVars πs ϱs (Shape.argVar m c)))
            (Ns.rename (TargetRen.shift m (0 + c)))⟩)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by
    cases h
    rfl
  | _ + 1, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, h => nomatch h
  | k + 1, .cons .., _, _, _, _, _, _, _, _, _, _, _, _, _, h =>
    Shape.branches_get ρ ϱ M Ns k _ h

/-! ## Arguments of a Built Branch -/

/-- The variables as terms, renamed, are the variables renamed, as terms. -/
theorem Targets.rename_ofVars {n n' : Nat} (α : TargetRen n' n) :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).rename α = Targets.ofVars πs ϱs (α ∘ xs)
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.rename, Targets.rename_ofVars α]
    split <;> rfl

/-- The variables as terms are stored at their multiplicities. -/
theorem Targets.multiplicities_ofVars {n : Nat} :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).multiplicities = List.ofFn πs
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.multiplicities, List.ofFn_succ,
      Targets.multiplicities_ofVars]

/-- The variables as terms are stored at their requirements. -/
theorem Targets.requirements_ofVars {n : Nat} :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).requirements = List.ofFn ϱs
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.requirements, List.ofFn_succ,
      Targets.requirements_ofVars]

/-- The variables as terms evaluate, in an environment whose cells bind the variables at a position
of a multiplicity other than `0` to addresses, to these addresses at these positions, and to new
addresses of `↯` at the others, in a heap that extends the first. -/
theorem Targets.evalAll_ofVars (P : Program) (ϖ : Multiplicity) {n : Nat} (E : List Nat) :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) → (H : Heap) →
      (bs : Fin c → Nat) →
      (∀ k, πs k ≠ .zero → ∃ c' π, E[(xs k : Nat)]? = some c' ∧ H[c']? = some (.cell π (bs k))) →
      ∃ as H' R, EvalAll P ϖ H E (Targets.ofVars πs ϱs xs) as H' R ∧ H.Extends H' ∧
        as.length = c ∧ ∀ k : Fin c, πs k ≠ .zero → as[(k : Nat)]? = some (bs k)
  | 0, _, _, _, H, _, _ => ⟨[], H, [], .nil, List.prefix_refl _, rfl, fun k => k.elim0⟩
  | c + 1, πs, ϱs, xs, H, bs, hE => by
    by_cases h0 : πs 0 = .zero
    · obtain ⟨as, H', R, hev, hH', hl, hk'⟩ := Targets.evalAll_ofVars P ϖ E
        (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ) (H ++ [.erased])
        (fun k => bs k.succ) (fun k hk => by
          obtain ⟨c', π, h₁, h₂⟩ := hE k.succ hk
          exact ⟨c', π, h₁, Heap.Extends.getElem? (List.prefix_append _ _) h₂⟩)
      refine ⟨H.length :: as, H', [] ++ R, ?_, (List.prefix_append _ _).trans hH',
        by simp [hl], fun k hk => ?_⟩
      · simp only [Targets.ofVars, h0, ↓reduceIte]
        exact .cons .erased hev
      · cases k using Fin.cases with
        | zero => exact absurd h0 hk
        | succ k => exact hk' k hk
    · obtain ⟨c', π, h₁, h₂⟩ := hE 0 h0
      obtain ⟨as, H', R, hev, hH', hl, hk'⟩ := Targets.evalAll_ofVars P ϖ E
        (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ) H
        (fun k => bs k.succ) (fun k hk => hE k.succ hk)
      refine ⟨bs 0 :: as, H', [c'] ++ R, ?_, hH', by simp [hl], fun k hk => ?_⟩
      · simp only [Targets.ofVars, h0, ↓reduceIte]
        exact .cons (.var h₁ h₂) hev
      · cases k using Fin.cases with
        | zero => rfl
        | succ k => exact hk' k hk

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
  (Ns₀ : TargetBranches m₀) (E₀ : List Nat)

-- ADE: none.
/-- The leaf `x` given at a position that holds the type `D` of the block: the recursor
`rec_ρ · ◀ ϱ with N̄₀` of the shape of `D`, on a path that runs to an address that the relation `x.2`
relates to the term `t`, when the factor of the shape is used at run time, gives a value related to
the result of `t` at the motive of `D` at `t`, in any environment that binds the variables of the
branches renamed as `E₀` binds them. -/
def RunResultLeaf (D : Name) (x : RunNestLeaf) : Prop :=
  ∀ b ms, ρ₁.block D = some b → block D = some ms → ∀ (t : Term 0 []) {m : Nat}
    (g : TargetRen m m₀) (E : List Nat), (∀ x : Fin m₀, E[(g x : Nat)]? = E₀[(x : Nat)]?) →
    ∀ (H : Heap) (O : Target m), (ms.factor.run ≠ .zero → O.RunsTo P x.2 t E H) →
    ∀ ϖ H₁, H.Extends H₁ → ∃ w H₂ tr, Eval P ϖ H₁ E (ms.next.body ρ ϱ O (Ns₀.rename g)) w H₂ tr ∧
      H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ ((φ D).subst₀ (Subst₀.single t)) w (b.motive.subst₀ (Subst₀.single t))

-- ADE: none.
/-- The recursive result `e` of the closed term `t` of the type `A`, whose nesting is `ν`, at run
time: when `A` lifted at `t` is a type with a relation of run time, of which `e` is a term, the body
of the shape of `A`, on a path that runs to an address that `R` relates to `t` when the factor of the
shape is used at run time, gives a value related to `e` at `A` lifted, in any environment that binds
the variables of the branches renamed as `E₀` binds them. -/
def NestedRunsAt (ν : Nest Name) (A t : Term 0 []) (R : RunRel) : Prop :=
  ∀ (e A' : Term 0 []) (mr : Lifting.Result 0) (ms : Shape.Motive),
    Term.NestedResult sig v ρ₁ φ ν A t e → Term.Lifts sig v ρ₁ ν t A A' mr →
    A.shape v (sig.shapes v sig) block Nesting.plain ν = some ms →
    (∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') → ValidTerm₀ sig ι e A' →
    ∀ {m : Nat} (g : TargetRen m m₀) (E : List Nat),
      (∀ x : Fin m₀, E[(g x : Nat)]? = E₀[(x : Nat)]?) →
      ∀ (H : Heap) (O : Target m), (ms.factor.run ≠ .zero → O.RunsTo P R t E H) →
      ∀ ϖ H₁, H.Extends H₁ →
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

/-! ## Arguments of a Lifted Destructor -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- Arguments related to addresses at a telescope whose entries are used more are related to them at
the telescope: the relation reads the types of the entries only, which are the same. -/
theorem RunsAsArgs.of_scale {H : Heap} (r : Grade) :
    {ps : List Parameter} → {g : Nat → Grade} → {Θ : Telescope 0 [] ps} → (ts : Args 0 [] ps) →
      (ts' : Args 0 [] (ps.map (Parameter.scale r))) → ts.terms = ts'.terms → {bs : List Nat} →
      RunsAsArgs sig ι P H g ts' bs (Θ.scale r) → RunsAsArgs sig ι P H g ts bs Θ
  | [], _, .nil, .nil, .nil, _, [], _ => trivial
  | _ :: _, _, .cons _ _ _ _, .cons t ts, .cons t' ts', h, b :: bs, hb => by
    injection h with _ h₁ h₂
    subst h₁
    obtain ⟨hb₁, hb₂⟩ := hb
    refine ⟨hb₁, RunsAsArgs.of_scale r ts ts' h₂ ?_⟩
    rw [← Telescope.scale_subst₀]
    exact hb₂
  | [], _, .nil, .nil, .nil, _, _ :: _, hb => (hb : False).elim
  | _ :: _, _, .cons _ _ _ _, .cons _ _, .cons _ _, _, [], hb => (hb : False).elim

/-- Arguments related to addresses are related to addresses that are the same at each position whose
grade is used at run time. -/
theorem RunsAsArgs.of_addrs {H : Heap} :
    {ps : List Parameter} → {g : Nat → Grade} → {ts : Args 0 [] ps} →
      {Θ : Telescope 0 [] ps} → {bs as : List Nat} → as.length = bs.length →
      (∀ l, g l ∉ Mode.oneOne.erased → as[l]? = bs[l]?) →
      RunsAsArgs sig ι P H g ts bs Θ → RunsAsArgs sig ι P H g ts as Θ
  | [], _, .nil, .nil, [], [], _, _, h => h
  | _ :: _, _, .cons _ _, .cons _ _ _ _, b :: bs, a :: as, hl, heq, h =>
    ⟨fun hg => by
      cases Option.some.inj (heq 0 hg)
      exact h.1 hg,
    RunsAsArgs.of_addrs (Nat.succ.inj hl) (fun l hg => heq (l + 1) hg) h.2⟩
  | [], _, .nil, .nil, _ :: _, _, _, _, h => (h : False).elim
  | _ :: _, _, .cons _ _, .cons _ _ _ _, [], _, _, _, h => (h : False).elim
  | [], _, .nil, .nil, [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, _, .cons _ _, .cons _ _ _ _, _ :: _, [], hl, _, _ => nomatch hl

end

/-! ## Nested Results of an Instance -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program} {v : Lifting.Variables}
  {ρ₁ : Lifting 0 [] []} {φ : Name → Term 0 [.var]} {block : Name → Option Shape.Motive}
  {ρ ϱ : Multiplicity} {m₀ : Nat} {Ns₀ : TargetBranches m₀} {E₀ : List Nat}

/-- Arguments of a telescope whose entries are used `r` times more, which its relation of run time
relates to addresses, are arguments of the telescope that its equality relates to themselves, as
many as the addresses, and its relation of run time relates them, in each heap that extends the
first one, to addresses that are the same at each position used at run time, when the entries used
at run time are used at run time `r` times more too. -/
theorem RunTelRel.of_scale (hd : sig.Distinct) {n n' : Nat} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {r : Grade} {SΘ SΘ' : FieldsRel} {RΘ RΘ' : RunFieldsRel}
    (hΘ : TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain) Θ SΘ)
    (hRΘ : RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain) Θ RΘ)
    (hΘ' : TelRel sig ι n' (fun m _ => levelRel sig ι m) .type (fun _ => .plain) (Θ.scale r) SΘ')
    (hRΘ' : RunTelRel sig ι P n' (fun m _ => levelRel sig ι m) (fun _ => .plain) (Θ.scale r) RΘ')
    (ts : Args 0 [] ps) (ts' : Args 0 [] (ps.map (Parameter.scale r))) (hts : ts.terms = ts'.terms)
    {H : Heap} {bs : List Nat} (hbs : RΘ' H ts'.terms bs) :
    SΘ ts.terms ts.terms ∧ bs.length = ps.length ∧
      ((∀ p ∈ ps, p.usage ∉ Mode.oneOne.erased → (p.scale r).usage ∉ Mode.oneOne.erased) →
        ∀ H', H.Extends H' → ∀ as : List Nat, as.length = ps.length →
          (∀ l (h : l < ps.length), ps[l].usage.run ≠ .zero → as[l]? = bs[l]?) →
          RΘ H' ts.terms as) := by
  have ihm : ∀ k m, m < k → (levelRel sig ι m).IsPer := fun _ m _ => levelRel_isPer hd m
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
  refine ⟨hSΘ, hlen, fun hus H' hH as hl hag => ?_⟩
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
an address that `R` relates to `t`, to addresses related to them: the closure observed by a
destructor of the lifting used at run time runs its branch, which observes the path by the
destructor that it lifts, at the arguments of the observation, and gives the body of the shape of
the result on this observation, a path from the field again.
The recursor is used at run time, `hr`, since the lifting scales the arguments of the destructors
that it lifts by its grade, while the branches built read them through the destructors lifted; and
the shapes of the types of the block carry the factor `11ᵖ` and the ownerships of the motives that
`ρ₁` gives them, `hb`, so that the arguments lifted have the shapes of their motives, at which the
shape of the instance is that of the lifting of the result. -/
theorem NestedRunsAt.inst (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    (hr : v.recursion ∉ Mode.oneOne.erased)
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
      ∃ SΘ RΘ Rb i, sig.destructorCase D d = some i ∧
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)) SΘ ∧
        RunTelRel sig ι P n (fun m _ => levelRel sig ι m) (fun _ => .plain)
          ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)) RΘ ∧
        (∀ H a, R H t a → RunAbstractionRel P i ψ ς RΘ Rb (t.observation D qs ls ps as d ps₁) H a) ∧
        ∀ ts : Args 0 [] ps₁, SΘ ts.terms ts.terms →
          NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀
            (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hpos.nesting (Nesting.ofArgs ns))))
            ((B.substLevels (ls.getFin hl)).subst
              (Subst.append (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst))
            ((t.observation D qs ls ps as d ps₁).subst ts.toSubst) (Rb ts.terms)) :
    NestedRunsAt sig ι P v ρ₁ φ block ρ ϱ Ns₀ E₀ (.inst ns) (.inst D qs ls ps as) t R := by
  intro e A' mA msO hres hL hsh hrun hval m g E hE H O hO ϖ H₁ hH₁
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
  have hLf := hlifts h.1 hDn hLm
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
  obtain ⟨ms', hms', hmsA⟩ := has₁.shapes (fun _ h => h) (hord.liftingsHaveShapes hd sig [] rfl)
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
  have hwe : Computesι sig ι e e := ⟨.refl _, he ▸ .corec ..⟩
  -- The instance lifted, a type or a proposition with a relation of run time.
  have hIA : Computesι sig ι
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t))
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t)) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
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
    have hpu : p ∉ Mode.oneOne.erased := fun hpe => hp'u ((Mode.erased_values.1 _).2
      (hp'g ▸ Lifting.resultGrade_run_eq_zero _ _ ((Mode.erased_values.1 _).1 hpe)))
    have hprun : p'.run ≠ .zero := fun h0 => hp'u ((Mode.erased_values.1 p').2 h0)
    obtain ⟨SΘ, RΘ, Rb, i, hi, hΘ, hRΘ, hAbs, hNest⟩ := horacle d' p q ς ps₁ Ξ Θ B ψ hpos hpu
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
    obtain ⟨hSΘ, hlen, hrel⟩ := RunTelRel.of_scale hd hΘ hRΘ hΘ'' hRΘ'' ts ts' hts hts'
    have hSΘ' : SΘ' ts'.terms ts'.terms := RunTelRel.fieldsRel hd (fun m _ => levelRel_isPer hd m)
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
      t hms' hpos hpos' ts
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
    let Hb := H'.bind ((List.ofFn (Fin.elim0 : Fin 0 → Multiplicity) ++ List.ofFn πs').map
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
    have hO' : mS.factor.run ≠ .zero →
        O'.RunsTo P (Rb ts.terms) ((t.observation D qs ls ps as d' ps₁).subst ts.toSubst) E' Hb := by
      intro hmf
      -- The factor of the shape of the instance is used at run time, so that the path runs.
      have hπ : π.run ≠ .zero := fun h0 => by
        rcases Multiplicity.modality.zero.mul_eq_zero _ _ (hfac h0) with h1 | h1
        · exact hprun h1
        · exact hmf h1
      have hr' : v.recursion * mS.factor ∉ Mode.oneOne.erased :=
        fun h => hmf ((Mode.erased_values.1 _).1 ((Mode.erasesUncounted .oneOne).mul _ _ hr h))
      have hus : ∀ p ∈ ps₁, p.usage ∉ Mode.oneOne.erased →
          (p.scale (v.recursion * mr.factor)).usage ∉ Mode.oneOne.erased := fun p hp hu => by
        rw [List.map_inj_left.1 hps' p hp]
        exact fun h => hu ((Mode.erasesUncounted .oneOne).mul _ _ hr' h)
      have hcase : (sig.destructorCase D d').getD 0 = i := by rw [hi]; rfl
      intro m'' f' E'' hE''
      exact Target.RunsTo.obs_args (i := (sig.destructorCase D d').getD 0)
        (πs := (List.ofFn (Fin.elim0 : Fin 0 → Multiplicity) ++ List.ofFn πs').map (ϖ' * ·))
        (hO hπ) (by rw [hcase]; exact hAbs) ts
        (hH₁.trans ((List.prefix_append _ _).trans (hHx.trans hH'))) hlen (by simp [hlen]; rfl)
        (hrel hus) f' E'' hE''
    obtain ⟨w'', H₃, tr, hev, hext, hrunI⟩ := hNest ts hSΘ (g₁.subst ts.toSubst) _ mr mS hN hL''
      (hshape.trans hmS) ⟨vB, R'', hvB, hR''⟩ hvalI g' E' hE' Hb O' hO' ϖ' Hb (List.prefix_refl _)
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

end

end Sic.Core
