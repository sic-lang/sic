module

public import Sic.Core.Shape.Ownership
public import Sic.Core.Shape.Results

/-!
# Factors, Fits and Ownerships of the Shapes of the Types Lifted

The shape of annex 14 of RFC 36 that a type lifted has, on the axis of the uses at run time, keeps
what the lifting declares: its factor is the run-time multiplicity of the factor that it carries,
it fits the recursor in the mode `11ᵐ`, and it has the ownerships `ς` and `χ` of the recursor, `ς`
the requirement of the lifted destructors and `χ` the ownership of the results that are motives.

Each of these is a property of the shapes that every shape keeps: the shape of a variable lifted
has it when the shapes of the variables have it, the shape of a type of the block, the recursor
itself, has it, and the shape of a lifting has it when the shapes of the arguments lifted have it,
since the destructors of the lifting are built from the results of the destructors that it lifts,
whose shapes have it in turn.
One walk of the terms carries any such property, and the signature, entry by entry, gives it to the
shapes of the liftings, as the shape follows the signature.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Properties That the Shapes Keep -/

/-- A property of the shapes of the variables holds under a new variable, which has none. -/
theorem Nesting.motives_lift {P : Shape.Motive → Prop} {Γ : Scope} {e : Scope.Entry}
    {ν : Nesting Shape.Motive Γ}
    (h : ∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m → P m) :
    ∀ {a : Scope.Entry} (x : Var (e :: Γ) a) (m : Shape.Motive),
      (Nesting.lift (e := e) ν x).motive = some m → P m := by
  intro a x m hm
  cases x with
  | zero => simp [Nesting.lift, Nest.motive] at hm
  | succ x => exact h x m hm

/-- A property of the shapes of the variables holds under new variables, which have none. -/
theorem Nesting.motives_liftN {P : Shape.Motive → Prop} : (n : Nat) → {Γ : Scope} →
    {ν : Nesting Shape.Motive Γ} →
    (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m → P m) →
    ∀ {a : Scope.Entry} (x : Var (Γ.extend n) a) (m : Shape.Motive),
      (Nesting.liftN n ν x).motive = some m → P m
  | 0, _, _, h => h
  | n + 1, _, _, h => Nesting.motives_liftN n (Nesting.motives_lift h)

/-- The variables without position have no shape, of which any property holds. -/
theorem Nesting.motives_plain {P : Shape.Motive → Prop} {Γ : Scope} :
    ∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive),
      (Nesting.plain (α := Shape.Motive) x).motive = some m → P m := by
  intro a x m hm
  simp [Nesting.plain, Nest.motive] at hm

/-- The parameters lifted with shapes that have a property have shapes that have it. -/
theorem Nesting.motives_of_shapes {P : Shape.Motive → Prop} {Δ : Scope}
    (ms : List (Nat × Shape.Motive)) (h : ∀ x ∈ ms, P x.2) :
    ∀ {a : Scope.Entry} (x : Var Δ a) (m : Shape.Motive),
      (Shape.motives (Δ := Δ) ms x).motive = some m → P m := by
  intro a x m hm
  simp only [Shape.motives] at hm
  split at hm
  · rename_i m' hl
    simp only [Nest.motive, Option.some.injEq] at hm
    subst hm
    obtain ⟨_, _, rfl, -⟩ := List.lookup_eq_some_iff.1 hl
    exact h (x.level, _) (by simp)
  · simp [Nest.motive] at hm

mutual

-- ADE: none.
/-- The shape of a type has a property that the shapes of the variables, those of the types of the
block and the shapes of the liftings at arguments that have it have: the shape of a variable is
its own, that of a type of the block is given, and that of an instance is a lifting at the shapes
of its arguments lifted. -/
theorem Term.shape_of_motives {P : Shape.Motive → Prop} {v : Lifting.Variables}
    {lookup : Shape.Lookup} {block : Name → Option Shape.Motive}
    (hl : ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π, (∀ x ∈ ms, P x.2) →
      lookup D qs ps ms = some (σ, π) → P ⟨.lifting σ, π, .linearLinear⟩)
    (hb : ∀ D m, block D = some m → P m) :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} →
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m → P m) →
      (n : Nest Name) → (A : Term k Γ) → ∀ m, A.shape v lookup block @ν n = some m → P m
  | _, _, hν, _, .var x _, m, h => hν x m h
  | _, ν, hν, n, .inst D qs _ ps as, m, h => by
    cases n with
    | direct _ => exact hb D m h
    | plain | inst _ =>
      simp only [Term.shape] at h
      split at h
      · rename_i m₀ ms hs
        obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hl D qs ps _ σ.1 σ.2 (InstanceArgs.shapes_of_motives hl hb hν _ as _ hs) hσ
      · cases h
  | _, _, _, _, .sort _, _, h => by simp [Term.shape] at h
  | _, _, _, _, .const _ _ _ _, _, h => by simp [Term.shape] at h
  | _, _, _, _, .ctor _ _ _ _ _ _ _, _, h => by simp [Term.shape] at h
  | _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _, _, h => by simp [Term.shape] at h
  | _, _, _, _, .obs _ _ _ _ _ _ _ _, _, h => by simp [Term.shape] at h
  | _, _, _, _, .corec _ _ _ _ _ _ _ _ _, _, h => by simp [Term.shape] at h

-- ADE: none.
/-- The shapes of the arguments of an instance that are lifted have a property that the shapes of
the variables, those of the types of the block and the shapes of the liftings at arguments that
have it have. -/
theorem InstanceArgs.shapes_of_motives {P : Shape.Motive → Prop} {v : Lifting.Variables}
    {lookup : Shape.Lookup} {block : Name → Option Shape.Motive}
    (hl : ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π, (∀ x ∈ ms, P x.2) →
      lookup D qs ps ms = some (σ, π) → P ⟨.lifting σ, π, .linearLinear⟩)
    (hb : ∀ D m, block D = some m → P m) :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} →
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m → P m) →
      (ns : List (Nest Name)) → {Δ : Scope} → (as : InstanceArgs k Γ Δ) → ∀ l,
        as.shapes v lookup block @ν ns = some l → ∀ x ∈ l, P x.2
  | _, _, _, _, _, .nil, l, h => by
    simp only [InstanceArgs.shapes, Option.some.injEq] at h
    subst h
    intro x hx
    cases hx
  | _, ν, hν, ns, _, .snoc as B, l, h => by
    simp only [InstanceArgs.shapes] at h
    split at h
    · rename_i l₀ m hs hm
      cases h
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact InstanceArgs.shapes_of_motives hl hb hν _ as _ hs x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact Term.shape_of_motives hl hb (Nesting.motives_liftN _ hν) _ B m hm
    · rename_i l₀ hs hm
      split at h
      · cases h
        exact InstanceArgs.shapes_of_motives hl hb hν _ as _ hs
      · cases h
    · cases h

end

-- ADE: none.
/-- The shapes of the liftings that the entries of a signature declare have a property, as the
shapes of the liftings at arguments that have it, when the shape of the destructors of a type, at
parameters whose shapes have it and where the liftings of the entries before have it, has it: the
shape of a lifting is that of the destructors of the type lifted, along the entries before it. -/
theorem Signature.shapes_of_motives {P : Shape.Motive → Prop} (v : Lifting.Variables) (md : Mode)
    (ax : Grade → Multiplicity)
    (hds : ∀ (sig' : Signature) {k' : Nat} {Γ : Scope} {ns : List Name}
      (ds : Destructors k' Γ ns) (D : Name) (ν : Nesting Shape.Motive Γ),
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m → P m) →
      (∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π, (∀ x ∈ ms, P x.2) →
        Signature.shapes v md ax sig' D qs ps ms = some (σ, π) →
          P ⟨.lifting σ, π, .linearLinear⟩) →
      P ⟨.lifting (ds.shape sig' v md ax (Signature.shapes v md ax sig') D ν).1,
        (ds.shape sig' v md ax (Signature.shapes v md ax sig') D ν).2.getD .noneNone,
        .linearLinear⟩) :
    (sig : Signature) → ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π, (∀ x ∈ ms, P x.2) →
      Signature.shapes v md ax sig D qs ps ms = some (σ, π) → P ⟨.lifting σ, π, .linearLinear⟩
  | [], _, _, _, _, _, _, _, h => by simp [Signature.shapes] at h
  | .typeDeclaration L :: sig', D, qs, ps, ms, σ, π, hms, h => by
    have ih := Signature.shapes_of_motives v md ax hds sig'
    simp only [Signature.shapes] at h
    split at h
    · obtain ⟨e, -, he⟩ := List.exists_of_findSome?_eq_some h
      split at he
      · rename_i decl
        split at he
        · split at he
          · obtain ⟨T, -, hT⟩ := Option.map_eq_some_iff.1 he
            cases hT
            exact hds sig' _ D _ (Nesting.motives_of_shapes ms hms) ih
          · cases he
        · cases he
      · cases he
    · exact ih D qs ps ms σ π hms h
  | .constantDefinition _ :: sig', D, qs, ps, ms, σ, π, hms, h => by
    simp only [Signature.shapes] at h
    exact Signature.shapes_of_motives v md ax hds sig' D qs ps ms σ π hms h
  | .constantDeclaration _ :: sig', D, qs, ps, ms, σ, π, hms, h => by
    simp only [Signature.shapes] at h
    exact Signature.shapes_of_motives v md ax hds sig' D qs ps ms σ π hms h

/-! ## Factors -/

-- ADE: none.
/-- The shape of the destructors of a type, on the axis of the uses at run time, has the factor that
it gives as a grade, its run-time multiplicity, and gives one exactly when it has a destructor, when
the shapes of the variables and those of the liftings have the factors that they carry. -/
theorem Destructors.shape_factor (sig : Signature) (v : Lifting.Variables) (md : Mode)
    {lookup : Shape.Lookup} (D : Name)
    (hl : ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π,
      (∀ x ∈ ms, x.2.next.factor = x.2.factor.run) →
      lookup D qs ps ms = some (σ, π) → σ.factor = π.run) :
    {Γ : Scope} → (ν : Nesting Shape.Motive Γ) →
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m →
        m.next.factor = m.factor.run) →
      {ns : List Name} → (ds : Destructors k Γ ns) →
        (ds.shape sig v md Grade.run lookup D ν).1.factor =
            ((ds.shape sig v md Grade.run lookup D ν).2.getD .noneNone).run ∧
          ((ds.shape sig v md Grade.run lookup D ν).2 = none ↔
            (ds.shape sig v md Grade.run lookup D ν).1 = .nil)
  | _, _, _, [], .nil => by simp [Destructors.shape, Shape.factor]; rfl
  | _, ν, hν, _ :: _, .cons (ps := ps) p _ _ _ B _ ds => by
    have ih := Destructors.shape_factor sig v md D hl (Nesting.lift ν) (Nesting.motives_lift hν) ds
    simp only [Destructors.shape]
    split
    · exact ih
    · rename_i μ hμ
      have hi : μ.next.factor = μ.factor.run :=
        Term.shape_of_motives hl (fun _ _ h => by cases h) (Nesting.motives_liftN _ hν) _ B μ hμ
      obtain ⟨ih₁, ih₂⟩ := ih
      refine ⟨?_, by simp⟩
      simp only [Option.getD_some]
      revert ih₁ ih₂
      generalize Destructors.shape sig v md Grade.run lookup D (Nesting.lift ν) ds = r
      obtain ⟨σ, o⟩ := r
      intro ih₁ ih₂
      cases σ with
      | nil =>
        have : o = none := ih₂.2 rfl
        subst this
        simp only [Shape.factor, Grade.meetWith, (Grade.run_op _ _).2.1] at hi ⊢
        rw [hi]
      | cons =>
        cases o with
        | none => exact absurd (ih₂.1 rfl) (by simp)
        | some q =>
          simp only [Shape.factor, Grade.meetWith, (Grade.run_op _ _).2.1,
            (Grade.run_op _ _).2.2.1, Option.getD_some] at hi ih₁ ⊢
          rw [hi, ← ih₁]

/-- The shapes of the liftings that a signature declares, on the axis of the uses at run time, have
the factors that they give as grades, at their run-time multiplicities, at arguments whose shapes
have the factors that they carry. -/
theorem Signature.shapes_factor (v : Lifting.Variables) (md : Mode) (sig : Signature) :
    ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π,
      (∀ x ∈ ms, x.2.next.factor = x.2.factor.run) →
      Signature.shapes v md Grade.run sig D qs ps ms = some (σ, π) → σ.factor = π.run :=
  Signature.shapes_of_motives (P := fun m => m.next.factor = m.factor.run) v md Grade.run
    (fun sig' _ _ _ ds D ν hν hl => (Destructors.shape_factor sig' v md D hl ν hν ds).1) sig

-- ADE: none.
/-- The factor of the shape of the lifting of the type of a nested field, read in the mode `md` on
the axis of the uses at run time, is the run-time multiplicity of the grade factor that the shape
carries: the factor of each destructor of a lifting is its multiplicity times the factor of its
result, whose shape carries it in turn, and the recursor itself has the factor `1`. -/
theorem Shape.factor_eq_run {sig : Signature} {v : Lifting.Variables} {md : Mode}
    {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade} {Γ : Scope}
    {A : Term k Γ} {n : Nest Name} {σ : Shape} {π χ' : Grade}
    (h : A.shape v (sig.shapes v md Grade.run) (sig.blockShapes names qs ps χ) Nesting.plain n =
      some ⟨.lifting σ, π, χ'⟩) : σ.factor = π.run :=
  Term.shape_of_motives (P := fun m => m.next.factor = m.factor.run)
    (Signature.shapes_factor v md sig)
    (fun D m hm => by
      simp only [Signature.blockShapes] at hm
      split at hm
      · cases hm
        rfl
      · cases hm)
    Nesting.motives_plain n A _ h

/-! ## Fits -/

/-- The grade of the mode `11ᵐ` times the grade of the result of a lifted destructor is that grade,
the grade of a mode. -/
theorem Lifting.oneOne_odot_resultGrade :
    ∀ (s : Quality) (p : Grade),
      (Mode.oneOne ⊙ Lifting.resultGrade s p).grade = Lifting.resultGrade s p := by
  decide

/-- The uses at run time of an argument of a lifted destructor, its grade times the grade of the
recursor times the factor of the result, are within the grade of the recursor times the grade of the
destructor times the factor times the grade of the argument. -/
theorem _root_.Sic.Grading.Multiplicity.mul_fits :
    ∀ g r f u : Multiplicity, g * ((r * f) * u) ≤ r * (g * f) * u := by
  decide

-- ADE: none.
/-- The shape of the destructors of a type, in the mode `11ᵐ` on the axis of the uses at run time,
fits the recursor of the grade `r` of the lifting, when the shapes of the variables and those of
the liftings carry their factors and fit it: each argument of a lifted destructor is used `r` times
the factor of its result more, within `r` times the multiplicity of the destructor times this
factor times its own multiplicity. -/
theorem Destructors.shape_fits (sig : Signature) (v : Lifting.Variables) {lookup : Shape.Lookup}
    (D : Name)
    (hl : ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π,
      (∀ x ∈ ms, x.2.next.factor = x.2.factor.run ∧ x.2.next.Fits v.recursion.run) →
      lookup D qs ps ms = some (σ, π) → σ.factor = π.run ∧ σ.Fits v.recursion.run) :
    {Γ : Scope} → (ν : Nesting Shape.Motive Γ) →
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m →
        m.next.factor = m.factor.run ∧ m.next.Fits v.recursion.run) →
      {ns : List Name} → (ds : Destructors k Γ ns) →
        (ds.shape sig v .oneOne Grade.run lookup D ν).1.Fits v.recursion.run
  | _, _, _, [], .nil => trivial
  | _, ν, hν, _ :: _, .cons (ps := ps) p _ _ _ B _ ds => by
    have ih := Destructors.shape_fits sig v D hl (Nesting.lift ν) (Nesting.motives_lift hν) ds
    simp only [Destructors.shape]
    split
    · exact ih
    · rename_i μ hμ
      obtain ⟨hf, hfits⟩ :=
        Term.shape_of_motives (P := fun m => m.next.factor = m.factor.run ∧
          m.next.Fits v.recursion.run) hl (fun _ _ h => by cases h)
          (Nesting.motives_liftN _ hν) _ B μ hμ
      refine ⟨fun j => ?_, hfits, ih⟩
      simp only [Parameter.scale, Lifting.oneOne_odot_resultGrade, hf, (Grade.run_op _ _).2.1]
      exact Multiplicity.mul_fits _ _ _ _

-- ADE: none.
/-- The shape of the lifting of the type of a nested field, read in the mode `11ᵐ` on the axis of
the uses at run time, fits the recursor of the grade `r` of the lifting: the lifting scales the
arguments of its destructors by `r` times the factors of their results, whose shapes fit it in
turn, and the recursor itself fits it. -/
theorem Shape.fits_of_shapes {sig : Signature} {v : Lifting.Variables} {names : List Name}
    {qs : List Quality} {ps : List Grade} {χ : Grade} {Γ : Scope} {A : Term k Γ} {n : Nest Name}
    {σ : Shape} {π χ' : Grade}
    (h : A.shape v (sig.shapes v .oneOne Grade.run) (sig.blockShapes names qs ps χ) Nesting.plain
      n = some ⟨.lifting σ, π, χ'⟩) : σ.Fits v.recursion.run :=
  (Term.shape_of_motives (P := fun m => m.next.factor = m.factor.run ∧ m.next.Fits v.recursion.run)
    (Signature.shapes_of_motives (P := fun m => m.next.factor = m.factor.run ∧
        m.next.Fits v.recursion.run) v .oneOne Grade.run
      (fun sig' _ _ _ ds D ν hν hl =>
        ⟨(Destructors.shape_factor sig' v .oneOne D (Signature.shapes_factor v .oneOne sig') ν
            (fun x m hm => (hν x m hm).1) ds).1,
          Destructors.shape_fits sig' v D hl ν hν ds⟩) sig)
    (fun D m hm => by
      simp only [Signature.blockShapes] at hm
      split at hm
      · cases hm
        exact ⟨rfl, trivial⟩
      · cases hm)
    Nesting.motives_plain n A _ h).2

/-! ## Ownerships -/

-- ADE: none.
/-- The shape of the destructors of a type, on the axis of the uses at run time, has the ownerships
`ς` and `χ`, `ς` the requirement of the lifting, when the shapes of the variables and those of the
liftings have them and the ownership that each carries is the run-time multiplicity of the ownership
of its shape: each lifted destructor requires `ς`, and its result has the ownership that the shape
of its result carries, as a constant. -/
theorem Destructors.shape_uniform (sig : Signature) (v : Lifting.Variables) (md : Mode)
    {lookup : Shape.Lookup} (D : Name) (χ : Multiplicity)
    (hl : ∀ D qs ps (ms : List (Nat × Shape.Motive)) σ π,
      (∀ x ∈ ms, x.2.next.Uniform v.requirement.run χ ∧
        x.2.ownership.run = x.2.next.ownership χ) →
      lookup D qs ps ms = some (σ, π) → σ.Uniform v.requirement.run χ) :
    {Γ : Scope} → (ν : Nesting Shape.Motive Γ) →
      (∀ {a : Scope.Entry} (x : Var Γ a) (m : Shape.Motive), (ν x).motive = some m →
        m.next.Uniform v.requirement.run χ ∧ m.ownership.run = m.next.ownership χ) →
      {ns : List Name} → (ds : Destructors k Γ ns) →
        (ds.shape sig v md Grade.run lookup D ν).1.Uniform v.requirement.run χ
  | _, _, _, [], .nil => trivial
  | _, ν, hν, _ :: _, .cons (ps := ps) p _ _ _ B _ ds => by
    have ih := Destructors.shape_uniform sig v md D χ hl (Nesting.lift ν) (Nesting.motives_lift hν)
      ds
    simp only [Destructors.shape]
    split
    · exact ih
    · rename_i μ hμ
      obtain ⟨hu, ho⟩ :=
        Term.shape_of_motives (P := fun m => m.next.Uniform v.requirement.run χ ∧
          m.ownership.run = m.next.ownership χ)
          (fun D qs ps ms σ π hms h => ⟨hl D qs ps ms σ π hms h, rfl⟩) (fun _ _ h => by cases h)
          (Nesting.motives_liftN _ hν) _ B μ hμ
      refine ⟨rfl, ?_, hu, ih⟩
      rw [← ho]
      rfl

-- ADE: none.
/-- The shape of the lifting of the type of a nested field, read on the axis of the uses at run
time, has the ownerships `ς` and `χ` of the recursor, at their run-time multiplicities: each
lifted destructor requires the requirement `ς` of the lifting, and its result has the ownership
`χ` of the results that are motives when it is the recursor itself, and `1` when it is the
corecursor of the next lifting, a new value, whose shape has them in turn. -/
theorem Shape.uniform_of_shapes {sig : Signature} {v : Lifting.Variables} {md : Mode}
    {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade} {Γ : Scope}
    {A : Term k Γ} {n : Nest Name} {σ : Shape} {π χ' : Grade}
    (h : A.shape v (sig.shapes v md Grade.run) (sig.blockShapes names qs ps χ) Nesting.plain n =
      some ⟨.lifting σ, π, χ'⟩) : σ.Uniform v.requirement.run χ.run :=
  (Term.shape_of_motives (P := fun m => m.next.Uniform v.requirement.run χ.run ∧
      m.ownership.run = m.next.ownership χ.run)
    (Signature.shapes_of_motives (P := fun m => m.next.Uniform v.requirement.run χ.run ∧
        m.ownership.run = m.next.ownership χ.run) v md Grade.run
      (fun sig' _ _ _ ds D ν hν hl =>
        ⟨Destructors.shape_uniform sig' v md D χ.run (fun D qs ps ms σ π hms h =>
            (hl D qs ps ms σ π hms h).1) ν hν ds, rfl⟩) sig)
    (fun D m hm => by
      simp only [Signature.blockShapes] at hm
      split at hm
      · cases hm
        exact ⟨trivial, rfl⟩
      · cases hm)
    Nesting.motives_plain n A _ h).1

end Sic.Core
