module

public import Sic.Core.Evaluation
public import Sic.Core.Evaluation.Heap
public import Sic.Core.Erasure.Results
public import Sic.Core.Meaning.RunTime
public import Sic.Core.Nesting.Relation
public import Sic.Core.Results
public import Sic.Core.RunTime.Relation

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

end Sic.Core
