module

public import Sic.Core.Results
public import Sic.Core.Shape.Results
import Sic.Core.Shape.Results.Substitution
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

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {v : Lifting.Variables} {lookup : Shape.Lookup}
  {block : Name → Option Shape.Motive}

/-- The term at the position `j` of the terms `t̄`, the first one at `0`. -/
def Terms.get {Γ : Scope} : Terms k Γ → Nat → Option (Term k Γ)
  | .nil, _ => none
  | .cons t _, 0 => some t
  | .cons _ ts, j + 1 => ts.get j

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

end Sic.Core
