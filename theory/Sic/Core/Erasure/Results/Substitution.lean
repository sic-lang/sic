module

public import Sic.Core.Erasure.Results
public import Sic.Core.Lifting.Observations
import Sic.Core.Positivity.Nesting

/-!
# Shapes of the Substituted Types

The shape of a type of the recursive results of annex 16 of RFC 36 does not read the levels, and a
substitution that keeps the nestings of the variables keeps it: such a substitution gives each
variable a variable with its shape, or, to a variable that has none, an observation, which has
none either.
A type without position, at nestings of its variables none of which has a position where it
occurs, has no shape.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {v : Lifting.Variables} {lookup : Shape.Lookup}
  {block : Name → Option Shape.Motive}

/-! ## Levels -/

mutual

/-- A type keeps its shape when levels replace its level variables. -/
theorem Term.shape_substLevels {k' : Nat} (ls' : Fin k → Level k') :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} → {n : Nest Name} → (A : Term k Γ) →
      (A.substLevels ls').shape v lookup block @ν n = A.shape v lookup block @ν n
  | _, _, _, .var _ _ => rfl
  | _, _, n, .inst _ _ _ _ as => by
    cases n <;> simp only [Term.substLevels, Term.shape, InstanceArgs.shapes_substLevels ls' as]
  | _, _, _, .sort _ => by rw [Term.substLevels]; rfl
  | _, _, _, .const _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl
  | _, _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.substLevels]; rfl

/-- The arguments of an instance keep their shapes when levels replace their level variables. -/
theorem InstanceArgs.shapes_substLevels {k' : Nat} (ls' : Fin k → Level k') :
    {Γ Δ : Scope} → {ν : Nesting Shape.Motive Γ} → {ns : List (Nest Name)} →
      (as : InstanceArgs k Γ Δ) →
        (as.substLevels ls').shapes v lookup block @ν ns = as.shapes v lookup block @ν ns
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .snoc as B => by
    rw [InstanceArgs.substLevels, InstanceArgs.shapes, InstanceArgs.shapes,
      Term.shape_substLevels ls' B, InstanceArgs.shapes_substLevels ls' as]

end

/-- Destructors keep their shape when levels replace their level variables. -/
theorem Destructors.shape_substLevels {k' : Nat} (sig : Signature) (D : Name)
    (ls' : Fin k → Level k') :
    {Γ : Scope} → (ν : Nesting Shape.Motive Γ) → {ns : List Name} → (ds : Destructors k Γ ns) →
      (ds.substLevels ls').shape sig v lookup D @ν = ds.shape sig v lookup D @ν
  | _, _, _, .nil => rfl
  | _, ν, _, .cons _ _ _ _ B _ ds => by
    rw [Destructors.substLevels, Destructors.shape, Destructors.shape, Term.shape_substLevels ls' B,
      Destructors.shape_substLevels sig D ls' (Nesting.lift @ν) ds]

/-! ## Substitutions That Keep the Nestings -/

mutual

/-- A type substituted by a substitution that keeps the nestings has the shape of the type. -/
theorem Term.shape_subst_of :
    {Γ Δ : Scope} → {θ : Subst k Γ Δ} → {ν : Nesting Shape.Motive Δ} →
      {ν' : Nesting Shape.Motive Γ} → Subst.Nests θ @ν @ν' → {n : Nest Name} → (A : Term k Δ) →
        (A.subst θ).shape v lookup block @ν' n = A.shape v lookup block @ν n
  | _, _, θ, ν, ν', h, n, .var x ts => by
    show ((θ x).instantiate (ts.subst θ)).shape v lookup block @ν' n = (ν x).motive
    rcases h x with ⟨hν, Ξ, D, qs, ls, ps, as, t, d, bs, hθ⟩ | ⟨y, us, hθ, hν⟩
    · rw [show θ x = _ from hθ, Term.instantiate_eq_subst₀, Term.subst₀, hν]
      rfl
    · rw [show θ x = _ from hθ, Term.instantiate_eq_subst₀, Term.subst₀_var,
        Args.toSubst₀_weakenN, ← hν]
      rfl
  | _, _, _, _, _, h, n, .inst _ _ _ _ as => by
    cases n <;> simp only [Term.subst, Term.shape, InstanceArgs.shapes_subst_of h as]
  | _, _, _, _, _, _, _, .sort _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, .const _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl
  | _, _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => by rw [Term.subst]; rfl

/-- The arguments of an instance substituted by a substitution that keeps the nestings have the
shapes of the arguments. -/
theorem InstanceArgs.shapes_subst_of :
    {Γ Δ Ξ : Scope} → {θ : Subst k Γ Δ} → {ν : Nesting Shape.Motive Δ} →
      {ν' : Nesting Shape.Motive Γ} → Subst.Nests θ @ν @ν' → {ns : List (Nest Name)} →
        (as : InstanceArgs k Δ Ξ) →
          (as.subst θ).shapes v lookup block @ν' ns = as.shapes v lookup block @ν ns
  | _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, h, _, .snoc as B => by
    rw [InstanceArgs.subst, InstanceArgs.shapes, InstanceArgs.shapes,
      Term.shape_subst_of (h.liftN _) B, InstanceArgs.shapes_subst_of h as]

end

/-! ## Types Without Shape -/

mutual

/-- A type without position, where no declared type holds one, has no shape at no position. -/
theorem Term.shape_eq_none_of_nest :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} → (A : Term k Γ) →
      A.nest (fun _ => none) @ν = .plain → A.shape v lookup block @ν .plain = none
  | _, ν, .var x _, h => by
    show (ν x).motive = none
    rw [show ν x = _ from h]
    rfl
  | _, ν, .inst _ _ _ _ as, h => by
    have hall : (as.nest (α := Shape.Motive) (fun _ => none) @ν).all Nest.isPlain = true := by
      rw [← Nest.isPlain_ofArgs, show Nest.ofArgs _ = _ from h]
      rfl
    simp only [Term.shape, Nest.args, InstanceArgs.shapes_eq_nil_of_nest as hall]
  | _, _, .sort _, _ => rfl
  | _, _, .const _ _ _ _, _ => rfl
  | _, _, .ctor _ _ _ _ _ _ _, _ => rfl
  | _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, .obs _ _ _ _ _ _ _ _, _ => rfl
  | _, _, .corec _ _ _ _ _ _ _ _ _, _ => rfl

/-- Arguments of an instance without position, where no declared type holds one, have no shape at
no position. -/
theorem InstanceArgs.shapes_eq_nil_of_nest :
    {Γ Δ : Scope} → {ν : Nesting Shape.Motive Γ} → (as : InstanceArgs k Γ Δ) →
      (as.nest (fun _ => none) @ν).all Nest.isPlain = true →
        as.shapes v lookup block @ν [] = []
  | _, _, _, .nil, _ => rfl
  | _, _, _, .snoc as B, h => by
    rw [InstanceArgs.nest, List.all_cons, Bool.and_eq_true] at h
    rw [InstanceArgs.shapes, List.tail_nil, List.headD_nil,
      InstanceArgs.shapes_eq_nil_of_nest as h.2,
      Term.shape_eq_none_of_nest B (Nest.eq_plain_of_isPlain h.1)]
    rfl

end

/-- A type in which no variable with a position occurs has no shape at no position. -/
theorem Term.shape_eq_none_of_avoids {Γ : Scope} {ν : Nesting Shape.Motive Γ} {A : Term k Γ}
    (h : ∀ {e : Scope.Entry} (x : Var Γ e), ν x ≠ .plain → A.Avoids x) :
    A.shape v lookup block @ν .plain = none :=
  Term.shape_eq_none_of_nest A (Term.nest_eq_plain_of_avoids h)

end Sic.Core
