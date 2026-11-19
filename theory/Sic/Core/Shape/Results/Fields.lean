module

public import Sic.Core.Lifting.Extension
public import Sic.Core.Results
public import Sic.Core.Shape.Ownership
public import Sic.Core.Shape.Results.Substitution
import Sic.Core.Shape.Results.Factor
import Sic.Core.Shape.Results.Lifting
import Sic.Core.Substitution.Nesting

/-!
# Shapes of the Types of the Fields at an Instance

The shape of annex 14 of RFC 36 that the erasure of a recursor gives a nested field is computed on
the type of the field in its declaration, at its nesting in the block, while the relation of run
time reads the shape of the type of the field at the instance of the recursor and at the terms of
the fields before it, at the same nesting: the two agree.
A substitution only replaces variables, which have no position in the nesting of a field, and the
shape of a type at no position is none whatever its variables are, so that the shape of a type at
its nesting does not depend on the terms that a substitution gives its variables, nor on its
levels.
The shapes that the erasure gives the types of the block are also those that the lifting of the
block of a recursor asks: the recursor itself, of the factor `11ᵖ` and of the ownership of its
results.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {v : Lifting.Variables} {lookup : Shape.Lookup}
  {block : Name → Option Shape.Motive}

/-! ## Substitutions at a Nesting Without Variables -/

mutual

/-- A type substituted by any substitution has the shape of the type at the nesting of the type,
where no variable has a position, the variables having no shapes: each variable is at no position,
where any term has no shape. -/
theorem Term.shape_subst_nest (mark : Name → Option Name) :
    {Γ Δ : Scope} → (θ : Subst k Γ Δ) → {ν : Nesting Shape.Motive Δ} →
      {ν' : Nesting Shape.Motive Γ} → {μ : Nesting Name Δ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν x = .plain) →
      (∀ (e : Scope.Entry) (x : Var Γ e), ν' x = .plain) →
      (∀ (e : Scope.Entry) (x : Var Δ e), μ x = .plain) → (A : Term k Δ) →
        (A.subst θ).shape v lookup block @ν' (A.nest mark @μ) =
          A.shape v lookup block @ν (A.nest mark @μ)
  | _, _, θ, ν, ν', μ, hν, hν', hμ, .var x ts => by
    show ((θ x).instantiate (ts.subst θ)).shape v lookup block @ν' (μ x) = (ν x).motive
    rw [hμ _ x, hν _ x, Term.shape_eq_none_of_nest _ (Term.nest_plain hν' _)]
    rfl
  | _, _, θ, ν, ν', μ, hν, hν', hμ, .inst D _ _ _ as => by
    have ih := InstanceArgs.shapes_subst_nest mark θ hν hν' hμ as
    simp only [Term.subst, Term.nest]
    cases mark D with
    | some _ => rfl
    | none =>
      by_cases hall : (as.nest mark @μ).all Nest.isPlain = true
      · have hp : Nest.ofArgs (as.nest mark @μ) = .plain := by
          rw [Nest.ofArgs, ite_eq_left hall]
        rw [InstanceArgs.shapes_of_all_isPlain as hall,
          InstanceArgs.shapes_of_all_isPlain (as.subst θ) hall] at ih
        simp only [hp, Term.shape, Nest.args, ih]
      · have hp : Nest.ofArgs (as.nest mark @μ) = .inst (as.nest mark @μ) := by
          rw [Nest.ofArgs, ite_eq_right hall]
        simp only [hp, Term.shape, Nest.args, ih]
  | _, _, _, _, _, _, _, _, _, .sort _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, _, _, .const _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl

/-- The arguments of an instance substituted by any substitution have the shapes of the arguments
at their nestings, where no variable has a position, the variables having no shapes. -/
theorem InstanceArgs.shapes_subst_nest (mark : Name → Option Name) :
    {Γ Δ Ξ : Scope} → (θ : Subst k Γ Δ) → {ν : Nesting Shape.Motive Δ} →
      {ν' : Nesting Shape.Motive Γ} → {μ : Nesting Name Δ} →
      (∀ (e : Scope.Entry) (x : Var Δ e), ν x = .plain) →
      (∀ (e : Scope.Entry) (x : Var Γ e), ν' x = .plain) →
      (∀ (e : Scope.Entry) (x : Var Δ e), μ x = .plain) → (as : InstanceArgs k Δ Ξ) →
        (as.subst θ).shapes v lookup block @ν' (as.nest mark @μ) =
          as.shapes v lookup block @ν (as.nest mark @μ)
  | _, _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, θ, _, _, _, hν, hν', hμ, .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.nest, InstanceArgs.shapes, InstanceArgs.shapes,
      List.tail_cons, List.headD_cons, InstanceArgs.shapes_subst_nest mark θ hν hν' hμ as,
      Term.shape_subst_nest mark (Subst.liftN _ θ) (Nesting.liftN_plain _ hν)
        (Nesting.liftN_plain _ hν') (Nesting.liftN_plain _ hμ) B]

end

/-- A type at other levels, substituted by any substitution, has the shape of the type at the
nesting of a field of a block, where the variables have no position and no shape. -/
theorem Term.shape_subst_blockNest (names : List Name) {k' : Nat} (ls : Fin k' → Level k)
    {Γ Δ : Scope} (θ : Subst k Γ Δ) (A : Term k' Δ) :
    ((A.substLevels ls).subst θ).shape v lookup block Nesting.plain (A.blockNest names) =
      A.shape v lookup block Nesting.plain (A.blockNest names) := by
  have h := Term.shape_subst_nest (v := v) (lookup := lookup) (block := block)
    (fun D => if D ∈ names then some D else none) θ (ν := Nesting.plain) (ν' := Nesting.plain)
    (μ := Nesting.plain) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (A.substLevels ls)
  rw [Term.nest_substLevels, Term.shape_substLevels] at h
  exact h

/-! ## Fields at an Instance -/

/-- The shape of the nested result of each field of a telescope, at its nesting in the block, is
that of the type of the field at other levels, at a substitution of the variables of its scope
and at the terms of the fields before it, at the same nesting. -/
theorem Telescope.nestedShapes_typesAt (names : List Name) {k' : Nat} (ls : Fin k' → Level k) :
    {Δ : Scope} → {ps : List Parameter} → (Θ : Telescope k' Δ ps) → {Γ : Scope} →
      (θ : Subst k Γ Δ) → (ts : Args k Γ ps) → (l : Nat) → {A : Term k Γ} → {n : Nest Name} →
      (((Θ.substLevels ls).subst θ).typesAt ts).get l = some A → (Θ.nest names)[l]? = some n →
        (Θ.nestedShapes v lookup block names)[l]? =
          some (Shape.Motive.nested (A.shape v lookup block Nesting.plain n))
  | _, [], .nil, _, _, .nil, _, _, _, hA, _ => nomatch hA
  | _, _ :: _, .cons _ _ B Θ, _, θ, .cons _ ts, 0, A, n, hA, hn => by
    cases hA
    cases hn
    show some (Shape.Motive.nested (B.shape v lookup block Nesting.plain (B.blockNest names))) = _
    rw [Term.shape_subst_blockNest names ls θ B]
  | _, _ :: _, .cons _ _ B Θ, _, θ, .cons t ts, l + 1, A, n, hA, hn => by
    have hΘ : (((Θ.substLevels ls).subst (Subst.lift θ)).subst₀ (Subst₀.single t)) =
        (Θ.substLevels ls).subst
          (fun x => (Subst.lift θ x).subst (Subst.liftN _ (Subst₀.toSubst (Subst₀.single t)))) := by
      rw [Telescope.subst₀_eq_subst]
      exact Telescope.subst_subst_of (fun _ => rfl) _
    have hA' : ((((Θ.substLevels ls).subst (Subst.lift θ)).subst₀ (Subst₀.single t)).typesAt
        ts).get l = some A := hA
    rw [hΘ] at hA'
    exact Telescope.nestedShapes_typesAt names ls Θ _ ts l hA' hn

/-- The shape of the nested result of each field of a telescope, at its nesting in the block, is
that of the type of the field at other levels and at a substitution of the variables of its scope,
in the scope of all the fields, at the same nesting. -/
theorem Telescope.nestedShapes_types (names : List Name) {k' : Nat} (ls : Fin k' → Level k) :
    {Δ : Scope} → {ps : List Parameter} → (Θ : Telescope k' Δ ps) → {Γ : Scope} →
      (θ : Subst k Γ Δ) → (l : Nat) → {A : Term k (Γ.extend ps.length)} → {n : Nest Name} →
      ((Θ.substLevels ls).subst θ).types.get l = some A → (Θ.nest names)[l]? = some n →
        (Θ.nestedShapes v lookup block names)[l]? =
          some (Shape.Motive.nested (A.shape v lookup block Nesting.plain n))
  | _, [], .nil, _, _, _, _, _, hA, _ => nomatch hA
  | _, _ :: ps, .cons _ _ B _, _, θ, 0, _, _, hA, hn => by
    cases hA
    cases hn
    have h := Term.shape_rename (v := v) (lookup := lookup) (block := block)
      (Ren.weakenN (ps.length + 1))
      (ν := Nesting.plain) (ν' := Nesting.plain) (fun _ _ => rfl) (n := B.blockNest names)
      ((B.substLevels ls).subst θ)
    rw [Term.shape_subst_blockNest names ls θ B] at h
    exact congrArg (fun x => some (Shape.Motive.nested x)) h.symm
  | _, _ :: _, .cons _ _ _ Θ, _, θ, l + 1, _, _, hA, hn =>
    Telescope.nestedShapes_types names ls Θ (Subst.lift θ) l hA hn

/-- The shape of a nested result is the shape of the lifting of the type of its field, whatever its
factor and its ownership. -/
theorem Shape.Motive.nested_eq_some {m : Option Shape.Motive} {σ : Shape} :
    Shape.Motive.nested m = some σ ↔ ∃ π χ', m = some ⟨.lifting σ, π, χ'⟩ := by
  constructor
  · intro h
    match m, h with
    | some ⟨.lifting _, π, χ'⟩, rfl => exact ⟨π, χ', rfl⟩
  · rintro ⟨π, χ', rfl⟩
    rfl

-- ADE: none.
/-- The shape that the erasure of a recursor gives the nested result of the field `l` of the
constructor `con`, `Constructor.nestedShapes` in the mode `11ᵐ` on the axis of the uses at run time,
is the shape of the lifting that the type `A` of the field at the instance, at the levels `ls`, at
the arguments `as` and at the terms `ts` of the fields, has at the nesting `n` of the field in the
block, the shape that the relation of run time reads of the result. -/
theorem Constructor.nestedShapes_shape {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g} {Γ : Scope} (ls : Fin k' → Level k)
    (as : InstanceArgs k Γ Δ) (ts : Args k Γ (con.params I)) {l : Nat} {A : Term k Γ}
    {n : Nest Name} (hA : ((con.fieldsAt I ls as).typesAt ts).get l = some A)
    (hn : ((con.fields I).nest names)[l]? = some n) (σ : Shape) :
    (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]? = some (some σ) ↔
      ∃ π χ', A.shape v (sig.shapes v .oneOne Grade.run) (sig.blockShapes names qs ps χ)
        Nesting.plain n = some ⟨.lifting σ, π, χ'⟩ := by
  rw [Constructor.nestedShapes, Telescope.nestedShapes_typesAt names ls (con.fields I)
    as.toSubst ts l hA hn, Option.some.injEq, Shape.Motive.nested_eq_some]

/-- The shape that the declaration of a nested field gives its result is the shape of the lifting
of the type of a field. -/
theorem Telescope.exists_shape_of_nestedShapes {v : Lifting.Variables} {lookup : Shape.Lookup}
    {block : Name → Option Shape.Motive} {names : List Name} {σ : Shape} :
    {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) → (l : Nat) →
      (Θ.nestedShapes v lookup block names)[l]? = some (some σ) →
        ∃ (Δ : Scope) (A : Term k Δ) (n : Nest Name) (π χ' : Grade),
          A.shape v lookup block Nesting.plain n = some ⟨.lifting σ, π, χ'⟩
  | _, [], .nil, _, h => nomatch h
  | _, _ :: _, .cons _ _ A _, 0, h => by
    simp only [Telescope.nestedShapes, List.getElem?_cons_zero, Option.some.injEq] at h
    match hA : A.shape v lookup block Nesting.plain (A.blockNest names), h with
    | some ⟨.lifting _, π, χ'⟩, rfl => exact ⟨_, A, _, π, χ', hA⟩
  | _, _ :: _, .cons _ _ _ Θ, l + 1, h => Telescope.exists_shape_of_nestedShapes Θ l h

-- ADE: none.
/-- The shape that the erasure gives the nested result of a field, in the mode `11ᵐ` on the axis of
the uses at run time, fits the recursor of the grade `r`. -/
theorem Constructor.nestedShapes_fits {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {v : Lifting.Variables} {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g} {l : Nat} {σ : Shape}
    (h : (con.nestedShapes sig v .oneOne Grade.run names qs ps χ I)[l]? = some (some σ)) :
    σ.Fits v.recursion.run := by
  obtain ⟨_, _, _, _, _, hA⟩ := Telescope.exists_shape_of_nestedShapes _ l h
  exact Shape.fits_of_shapes hA

-- ADE: none.
/-- The shape of the nested result of a field, in the mode `md` on the axis of the uses at run time,
has the ownerships `ς` and `χ` of the recursor, at their run-time multiplicities. -/
theorem Constructor.nestedShapes_uniform {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {v : Lifting.Variables} {md : Mode} {names : List Name} {qs : List Quality} {ps : List Grade}
    {χ : Grade} {con : Constructor j g k' Δ} {I : Instance j g} {l : Nat} {σ : Shape}
    (h : (con.nestedShapes sig v md Grade.run names qs ps χ I)[l]? = some (some σ)) :
    σ.Uniform v.requirement.run χ.run := by
  obtain ⟨_, _, _, _, _, hA⟩ := Telescope.exists_shape_of_nestedShapes _ l h
  exact Shape.uniform_of_shapes hA

/-! ## Shapes of the Block -/

-- ADE: none.
/-- Each type of the block that the lifting of the scope of a recursor gives a motive has a shape,
the recursor itself, of the factor `11ᵖ` and of the ownership of the results of the recursor. -/
theorem Signature.blockShapes_of_block {sig : Signature} {Γ Δ : Scope}
    {names : List Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ Δ} {l : Level k} {χ : Grade} {Cs : Motives k Γ} :
    ∀ D b, (Lifting.ofMotives names qs ls ps as l χ Cs).block D = some b →
      ∃ Υ, sig.blockShapes names qs ps χ D = some ⟨Υ, .linearLinear, b.ownership⟩ := by
  intro D b h
  obtain ⟨hD, _, _, rfl⟩ := Lifting.ofMotives_block_inv h
  exact ⟨.recursor (sig.skeleton D qs ps), ite_eq_left hD⟩

/-! ## Factors of the Recursive Results -/

/-- The lifting of the scope of a recursor, under new variables, lifts no variable, so that the
variables have no shapes. -/
theorem Lifting.ofMotives_shapes {Γ Δ : Scope} {names : List Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {l : Level k} {χ : Grade}
    {Cs : Motives k Γ} (n : Nat) :
    ((Lifting.ofMotives names qs ls ps as l χ Cs).liftN n).Shapes Nesting.plain := by
  have h : ∀ (n : Nat) {Γ' Γ : Scope} (ρ : Lifting k Γ' Γ),
      (∀ {a : Scope.Entry} (x : Var Γ a), ρ.motive x = none) →
        ∀ {a : Scope.Entry} (x : Var (Γ.extend n) a), (ρ.liftN n).motive x = none := by
    intro n
    induction n with
    | zero => exact fun ρ h => h
    | succ n ih =>
      refine fun ρ h => ih ρ.lift fun x => ?_
      cases x with
      | zero => rfl
      | succ x => show (ρ.motive x).map _ = none; rw [h x]; rfl
  intro _ x
  exact Or.inl ⟨h n _ (fun _ => rfl) x, rfl⟩

/-- Each type of the block that the lifting of the scope of a recursor, under new variables, gives
a motive has a shape, of the factor `11ᵖ` and of the ownership of the results of the recursor. -/
theorem Signature.blockShapes_of_block_liftN {sig : Signature} {Γ Δ : Scope}
    {names : List Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ Δ} {l : Level k} {χ : Grade} {Cs : Motives k Γ} (n : Nat) :
    ∀ D b, ((Lifting.ofMotives names qs ls ps as l χ Cs).liftN n).block D = some b →
      ∃ Υ, sig.blockShapes names qs ps χ D = some ⟨Υ, .linearLinear, b.ownership⟩ := by
  intro D b h
  obtain ⟨b₀, h₀, he⟩ := Lifting.liftN_block_ownership n h
  obtain ⟨Υ, hΥ⟩ := Signature.blockShapes_of_block D b₀ h₀
  exact ⟨Υ, he ▸ hΥ⟩

-- ADE: none.
/-- The recursive result of each field whose nesting has a position, the `j`-th of them, has the
factor of the shape of its type: `11ᵖ` for a recursive field, and, for a nested field, the factor
of the shape of the lifting of its type, which it has, in a signature whose names are distinct and
that declares each lifting after the destructors that it lifts, where the shapes of the variables
follow the lifting and those of the types of the block carry their ownerships. -/
theorem Terms.ResultTypes.factor_shape {sig : Signature} {md : Mode} {ax : Grade → Multiplicity}
    (hsig : sig.Distinct) (hord : sig.LiftsInOrder) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} →
      {πs : List Grade} → Terms.ResultTypes sig v ρ ns ps As xs R πs →
      {ν : Nesting Shape.Motive Δ} → ρ.Shapes @ν →
      (∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
      ∀ (o j l : Nat) (n : Nest Name) (A : Term k Δ),
        (Telescope.nestPositions ns o)[j]? = some (o + l) → ns[l]? = some n →
          As.get l = some A →
        (∀ D, n = .direct D → πs[j]? = some .linearLinear) ∧
          (∀ ms, n = .inst ms → ∃ m', A.shape v (sig.shapes v md ax) block @ν (.inst ms) =
            some m' ∧ πs[j]? = some m'.factor)
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, hj, _, _ => nomatch hj
  | _, _, _, _, _, _, _, _, _, _, .plain h, ν, hν, hb, o, j, l, n, A, hj, hn, hA => by
    rw [Telescope.nestPositions_plain] at hj
    cases l with
    | zero =>
      exact absurd (Telescope.le_of_mem_nestPositions (List.mem_of_getElem? hj)) (by omega)
    | succ l =>
      rw [show o + (l + 1) = o + 1 + l by omega] at hj
      exact h.factor_shape hsig hord hν hb (o + 1) j l n A hj hn hA
  | _, _, _, _, _, _, _, _, _, _, .recursive _ h, ν, hν, hb, o, j, l, n, A, hj, hn, hA => by
    rw [Telescope.nestPositions_cons rfl] at hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      have hl : l = 0 := by omega
      subst hl
      cases hn
      refine ⟨fun _ _ => rfl, fun _ h => nomatch h⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      cases l with
      | zero =>
        exact absurd (Telescope.le_of_mem_nestPositions (List.mem_of_getElem? hj)) (by omega)
      | succ l =>
        rw [show o + (l + 1) = o + 1 + l by omega] at hj
        exact h.factor_shape hsig hord hν.weaken (Lifting.blockShapes_liftN_weaken 0 hb) (o + 1)
          j l n A hj hn hA
  | _, _, _, _, _, _, _, _, _, _, .nested hA' h, ν, hν, hb, o, j, l, n, A, hj, hn, hA => by
    rw [Telescope.nestPositions_cons rfl] at hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      have hl : l = 0 := by omega
      subst hl
      cases hn
      cases hA
      refine ⟨fun _ h => (nomatch h), fun ms h => ?_⟩
      cases h
      obtain ⟨m', hm', hof⟩ := Term.Lifts.shape_eq (md := md) (ax := ax) hsig hord hA' hν hb
      exact ⟨m', hm', by rw [hof.1]; rfl⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      cases l with
      | zero =>
        exact absurd (Telescope.le_of_mem_nestPositions (List.mem_of_getElem? hj)) (by omega)
      | succ l =>
        rw [show o + (l + 1) = o + 1 + l by omega] at hj
        exact h.factor_shape hsig hord hν.weaken (Lifting.blockShapes_liftN_weaken 0 hb) (o + 1)
          j l n A hj hn hA

/-- A type at a nesting that is a position has no shape of a lifting: the recursor itself, or no
shape. -/
theorem Term.nested_shape_direct {sig : Signature} {md : Mode} {ax : Grade → Multiplicity}
    {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade} {Γ : Scope}
    (D : Name) : (A : Term k Γ) →
      Shape.Motive.nested (A.shape v (sig.shapes v md ax) (sig.blockShapes names qs ps χ)
        Nesting.plain (.direct D)) = none
  | .var _ _ => rfl
  | .inst D' _ _ _ _ => by
    simp only [Term.shape, Signature.blockShapes]
    split <;> rfl
  | .sort _ | .const _ _ _ _ | .ctor _ _ _ _ _ _ _ | .recursor _ _ _ _ _ _ _ _ _ _ _ _
  | .obs _ _ _ _ _ _ _ _ | .corec _ _ _ _ _ _ _ _ _ => rfl

/-- A type at the nesting of an instance whose shape is given is the corecursor of a lifting. -/
theorem Term.shape_inst_lifting {lookup : Shape.Lookup} {block : Name → Option Shape.Motive}
    {Γ : Scope} {ms : List (Nest Name)} {m : Shape.Motive} :
    (A : Term k Γ) → A.shape v lookup block Nesting.plain (.inst ms) = some m →
      ∃ σ, m.next = .lifting σ
  | .var _ _, h => by simp [Term.shape, Nesting.plain, Nest.motive] at h
  | .inst _ _ _ _ _, h => by
    simp only [Term.shape] at h
    split at h
    · obtain ⟨σ, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨σ.1, rfl⟩
    · cases h
  | .sort _, h | .const _ _ _ _, h | .ctor _ _ _ _ _ _ _, h | .recursor _ _ _ _ _ _ _ _ _ _ _ _, h
  | .obs _ _ _ _ _ _ _ _, h | .corec _ _ _ _ _ _ _ _ _, h => by simp [Term.shape] at h

/-- The `i`-th field of the constructor `con` whose nesting has a position, the field `l`, has a
nesting other than none, and a type in the scope of all the fields. -/
theorem Constructor.exists_nest_of_nestPositions {j g k' : Nat} {Δ Γ : Scope}
    {con : Constructor j g k' Δ} {I : Instance j g} {names : List Name} (ls : Fin k' → Level k)
    (as : InstanceArgs k Γ Δ) {i l : Nat}
    (hl : (Telescope.nestPositions ((con.fields I).nest names) 0)[i]? = some l) :
    ∃ n A, ((con.fields I).nest names)[l]? = some n ∧ n.isPlain = false ∧
      (con.fieldsAt I ls as).types.get l = some A := by
  obtain ⟨n, hn, hp⟩ := Telescope.mem_nestPositions.1
    ((Nat.zero_add l).symm ▸ List.mem_of_getElem? hl : 0 + l ∈ _)
  have hlt : l < (con.params I).length := by
    rw [← Telescope.length_nest names (con.fields I)]
    exact (List.getElem?_eq_some_iff.1 hn).1
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1
    ((Telescope.get_types_isSome (con.fieldsAt I ls as) l).2 hlt)
  exact ⟨n, A, hn, hp, hA⟩

-- ADE: none.
/-- The `i`-th recursive result of the constructor `con`, at the field `l`, has the factor `π` of
the typing, whose run-time multiplicity is the factor of the shape of the field that the erasure
reads, when the field is nested, in a signature whose names are distinct and that declares each
lifting after the destructors that it lifts: both read the shape of the lifting of the type of the
field. -/
theorem Constructor.ResultTypes.factor_nested {sig : Signature} {md : Mode}
    (hsig : sig.Distinct) (hord : sig.LiftsInOrder) {j g k' : Nat} {Δ Γ : Scope}
    {con : Constructor j g k' Δ} {I : Instance j g} {names : List Name} {ls : Fin k' → Level k}
    {as : InstanceArgs k Γ Δ} {qs : List Quality} {ls' : List (Level k)} {ps : List Grade}
    {lC : Level k} {χ : Grade} {Cs : Motives k Γ} {ps' : List Parameter}
    {R : Telescope k (Γ.extend (con.params I).length) ps'} {πs : List Grade}
    (h : Constructor.ResultTypes sig v con I names ls as
      (Lifting.ofMotives names qs ls' ps as lC χ Cs) R πs) {i l : Nat}
    (hl : (Telescope.nestPositions ((con.fields I).nest names) 0)[i]? = some l) {σ : Shape}
    (hσ : (con.nestedShapes sig v md Grade.run names qs ps χ I)[l]? = some (some σ)) :
    ∃ π, πs[i]? = some π ∧ σ.factor = π.run := by
  obtain ⟨n, A, hn, hp, hA⟩ := Constructor.exists_nest_of_nestPositions ls as hl
  rw [Constructor.nestedShapes, Telescope.nestedShapes_types names ls (con.fields I) as.toSubst l
    hA hn, Option.some.injEq] at hσ
  obtain ⟨π, χ', hm⟩ := Shape.Motive.nested_eq_some.1 hσ
  cases n with
  | plain => cases hp
  | direct D => rw [Term.nested_shape_direct D A] at hσ; cases hσ
  | inst ms =>
    obtain ⟨-, hi⟩ := h.factor_shape (md := md) (ax := Grade.run) hsig hord
      (Lifting.ofMotives_shapes _) (Signature.blockShapes_of_block_liftN _) 0 i l _ A
      (by rw [Nat.zero_add]; exact hl) hn hA
    obtain ⟨m', hm', hπ⟩ := hi ms rfl
    rw [hm] at hm'
    cases hm'
    exact ⟨π, hπ, Shape.factor_eq_run hm⟩

-- ADE: none.
/-- The nested field that is the `i`-th field of the constructor `con` whose nesting has a position
has a shape, in a signature whose names are distinct and that declares each lifting after the
destructors that it lifts, when the typing gives it a recursive result: the type of the field
lifted has a shape. -/
theorem Constructor.ResultTypes.nestedShapes_isSome {sig : Signature} {md : Mode}
    {ax : Grade → Multiplicity} (hsig : sig.Distinct) (hord : sig.LiftsInOrder) {j g k' : Nat}
    {Δ Γ : Scope} {con : Constructor j g k' Δ} {I : Instance j g} {names : List Name}
    {ls : Fin k' → Level k} {as : InstanceArgs k Γ Δ} {qs : List Quality} {ls' : List (Level k)}
    {ps : List Grade} {lC : Level k} {χ : Grade} {Cs : Motives k Γ} {ps' : List Parameter}
    {R : Telescope k (Γ.extend (con.params I).length) ps'} {πs : List Grade}
    (h : Constructor.ResultTypes sig v con I names ls as
      (Lifting.ofMotives names qs ls' ps as lC χ Cs) R πs) {i l : Nat}
    (hl : (Telescope.nestPositions ((con.fields I).nest names) 0)[i]? = some l)
    {ms : List (Nest Name)}
    (hn : ((con.fields I).nest names)[l]? = some (.inst ms)) :
    ∃ σ, (con.nestedShapes sig v md ax names qs ps χ I)[l]? = some (some σ) := by
  obtain ⟨n, A, hn', -, hA⟩ := Constructor.exists_nest_of_nestPositions ls as hl
  rw [hn] at hn'
  cases hn'
  obtain ⟨-, hi⟩ := h.factor_shape (md := md) (ax := ax) hsig hord (Lifting.ofMotives_shapes _)
    (Signature.blockShapes_of_block_liftN _) 0 i l _ A (by rw [Nat.zero_add]; exact hl) hn hA
  obtain ⟨m', hm', -⟩ := hi ms rfl
  obtain ⟨σ, hσ⟩ := Term.shape_inst_lifting A hm'
  refine ⟨σ, ?_⟩
  rw [Constructor.nestedShapes, Telescope.nestedShapes_types names ls (con.fields I) as.toSubst l
    hA hn, hm']
  obtain ⟨next, π, χ'⟩ := m'
  cases hσ
  rfl

end Sic.Core
