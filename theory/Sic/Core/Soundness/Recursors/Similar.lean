module

public import Sic.Core.Nesting
public import Sic.Core.Substitution
import Sic.Core.Substitution.Composition

/-!
# Types of the Same Shape at a Nesting

The recursive results of two terms of a field nested below a codata type, at two instances of the
type of the field, are corecursors of the same lifting when the two instances have the same
declared types, at the same sorts and grades, along the nesting of the field: the arguments of
these types and their levels may differ, and what the positions hold is not read.

The meaning of the types does not tell it: a proposition declared as a codata type has the truth
of its destructors as its only meaning, which does not determine its name.
The two instances of the type of a field are the same type at two substitutions, and so are the
results of the destructors of an instance: a type at two substitutions that give the variables
types of the same shape, at the nestings of these variables, has the same shape at its nesting.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Shape -/

mutual

-- ADE: none.
/-- Two types have the same shape at the nesting `n`: at the nesting of an instance, they are
instances of the same declared type, at the same sorts and grades, whose arguments have the same
shape at their nestings; nothing is asked without position, nor at a position. -/
inductive Term.Similar : {Γ : Scope} → Nest Name → Term k Γ → Term k Γ → Prop where
  /-- No position. -/
  | plain {Γ : Scope} {A₁ A₂ : Term k Γ} : Term.Similar .plain A₁ A₂
  /-- A position. -/
  | direct {Γ : Scope} {D : Name} {A₁ A₂ : Term k Γ} : Term.Similar (.direct D) A₁ A₂
  /-- Two instances of a declared type, at the same sorts and grades. -/
  | inst {Γ Δ : Scope} {ns : List (Nest Name)} {D : Name} {qs : List Quality}
      {ls₁ ls₂ : List (Level k)} {ps : List Grade} {as₁ as₂ : InstanceArgs k Γ Δ}
      (h : InstanceArgs.Similar ns as₁ as₂) :
      Term.Similar (.inst ns) (.inst D qs ls₁ ps as₁) (.inst D qs ls₂ ps as₂)

-- ADE: none.
/-- The arguments of two instances have the same shape at the nestings `ns`, the last one first,
and without position after those of `ns`. -/
inductive InstanceArgs.Similar :
    {Γ Δ : Scope} → List (Nest Name) → InstanceArgs k Γ Δ → InstanceArgs k Γ Δ → Prop where
  /-- No argument. -/
  | nil {Γ : Scope} {ns : List (Nest Name)} : InstanceArgs.Similar (Γ := Γ) ns .nil .nil
  /-- A last argument, at the first nesting, and the others. -/
  | snoc {Γ Δ : Scope} {ns : List (Nest Name)} {a : Scope.Entry} {as₁ as₂ : InstanceArgs k Γ Δ}
      {B₁ B₂ : Term k (Γ.extend a.params.length)} (has : InstanceArgs.Similar ns.tail as₁ as₂)
      (hB : Term.Similar (ns.headD .plain) B₁ B₂) :
      InstanceArgs.Similar ns (.snoc (e := a) as₁ B₁) (.snoc as₂ B₂)

end

-- ADE: none.
/-- The types `Ā₁` and `Ā₂` of fields have the same shape, one by one, at the nestings `ns` of the
fields. -/
def Terms.Similar {Γ : Scope} : List (Nest Name) → Terms k Γ → Terms k Γ → Prop
  | ν :: ns, .cons A₁ As₁, .cons A₂ As₂ => Term.Similar ν A₁ A₂ ∧ Terms.Similar ns As₁ As₂
  | _, _, _ => True

/-! ## Stability -/

mutual

/-- Two types of the same shape, renamed, have the same shape. -/
theorem Term.Similar.rename {Γ' : Scope} :
    {Γ : Scope} → {n : Nest Name} → {A₁ A₂ : Term k Γ} → Term.Similar n A₁ A₂ →
      ∀ (α₁ α₂ : Ren Γ' Γ), Term.Similar n (A₁.rename α₁) (A₂.rename α₂)
  | _, _, _, _, .plain, _, _ => .plain
  | _, _, _, _, .direct, _, _ => .direct
  | _, _, _, _, .inst h, α₁, α₂ => by
    rw [Term.rename, Term.rename]
    exact .inst (h.rename α₁ α₂)

/-- The arguments of two instances of the same shape, renamed, have the same shape. -/
theorem InstanceArgs.Similar.rename {Γ' : Scope} :
    {Γ Δ : Scope} → {ns : List (Nest Name)} → {as₁ as₂ : InstanceArgs k Γ Δ} →
      InstanceArgs.Similar ns as₁ as₂ →
      ∀ (α₁ α₂ : Ren Γ' Γ), InstanceArgs.Similar ns (as₁.rename α₁) (as₂.rename α₂)
  | _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, .snoc has hB, α₁, α₂ => by
    rw [InstanceArgs.rename, InstanceArgs.rename]
    exact .snoc (has.rename α₁ α₂) (hB.rename _ _)

end

mutual

/-- Two types of the same shape, each substituted, have the same shape. -/
theorem Term.Similar.subst {Γ' : Scope} :
    {Γ : Scope} → {n : Nest Name} → {A₁ A₂ : Term k Γ} → Term.Similar n A₁ A₂ →
      ∀ (θ₁ θ₂ : Subst k Γ' Γ), Term.Similar n (A₁.subst θ₁) (A₂.subst θ₂)
  | _, _, _, _, .plain, _, _ => .plain
  | _, _, _, _, .direct, _, _ => .direct
  | _, _, _, _, .inst h, θ₁, θ₂ => by
    rw [Term.subst, Term.subst]
    exact .inst (h.subst θ₁ θ₂)

/-- The arguments of two instances of the same shape, each substituted, have the same shape. -/
theorem InstanceArgs.Similar.subst {Γ' : Scope} :
    {Γ Δ : Scope} → {ns : List (Nest Name)} → {as₁ as₂ : InstanceArgs k Γ Δ} →
      InstanceArgs.Similar ns as₁ as₂ →
      ∀ (θ₁ θ₂ : Subst k Γ' Γ), InstanceArgs.Similar ns (as₁.subst θ₁) (as₂.subst θ₂)
  | _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, .snoc has hB, θ₁, θ₂ => by
    rw [InstanceArgs.subst, InstanceArgs.subst]
    exact .snoc (has.subst θ₁ θ₂) (hB.subst _ _)

end

mutual

/-- Two types of the same shape, each substituted by a substitution of the first order, have the
same shape. -/
theorem Term.Similar.subst₀ {Γ' : Scope} :
    {Γ : Scope} → {n : Nest Name} → {A₁ A₂ : Term k Γ} → Term.Similar n A₁ A₂ →
      ∀ (σ₁ σ₂ : Subst₀ k Γ' Γ), Term.Similar n (A₁.subst₀ σ₁) (A₂.subst₀ σ₂)
  | _, _, _, _, .plain, _, _ => .plain
  | _, _, _, _, .direct, _, _ => .direct
  | _, _, _, _, .inst h, σ₁, σ₂ => by
    rw [Term.subst₀, Term.subst₀]
    exact .inst (h.subst₀ σ₁ σ₂)

/-- The arguments of two instances of the same shape, each substituted by a substitution of the
first order, have the same shape. -/
theorem InstanceArgs.Similar.subst₀ {Γ' : Scope} :
    {Γ Δ : Scope} → {ns : List (Nest Name)} → {as₁ as₂ : InstanceArgs k Γ Δ} →
      InstanceArgs.Similar ns as₁ as₂ →
      ∀ (σ₁ σ₂ : Subst₀ k Γ' Γ), InstanceArgs.Similar ns (as₁.subst₀ σ₁) (as₂.subst₀ σ₂)
  | _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, .snoc has hB, σ₁, σ₂ => by
    rw [InstanceArgs.subst₀, InstanceArgs.subst₀]
    exact .snoc (has.subst₀ σ₁ σ₂) (hB.subst₀ _ _)

end

/-- The types of fields of the same shape, each substituted by a substitution of the first order,
have the same shape. -/
theorem Terms.Similar.subst₀ {Γ' Γ : Scope} :
    {ns : List (Nest Name)} → {As₁ As₂ : Terms k Γ} → Terms.Similar ns As₁ As₂ →
      ∀ (σ₁ σ₂ : Subst₀ k Γ' Γ), Terms.Similar ns (As₁.subst₀ σ₁) (As₂.subst₀ σ₂)
  | _ :: _, .cons _ _, .cons _ _, h, σ₁, σ₂ => ⟨h.1.subst₀ σ₁ σ₂, h.2.subst₀ σ₁ σ₂⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, .nil, _, _, _, _ => trivial
  | _ :: _, .cons _ _, .nil, _, _, _ => trivial

/-! ## A Type at Two Substitutions -/

-- ADE: none.
/-- Two substitutions give each variable abstractions of the same shape, at the nesting `ν` of the
variable. -/
def Subst.Similar {Γ Δ : Scope} (θ₁ θ₂ : Subst k Γ Δ) (ν : Nesting Name Δ) : Prop :=
  ∀ {e : Scope.Entry} (x : Var Δ e), Term.Similar (ν x) (θ₁ x) (θ₂ x)

/-- Two substitutions that give the variables abstractions of the same shape do so under a new
entry, which has no position. -/
theorem Subst.Similar.lift {Γ Δ : Scope} {e₀ : Scope.Entry} {θ₁ θ₂ : Subst k Γ Δ}
    {ν : Nesting Name Δ} (h : Subst.Similar θ₁ θ₂ @ν) :
    Subst.Similar (Subst.lift (e := e₀) θ₁) (Subst.lift θ₂) (Nesting.lift @ν) := by
  intro e x
  cases x with
  | zero => exact .plain
  | succ x => exact (h x).rename _ _

/-- Two substitutions that give the variables abstractions of the same shape do so under new
variables. -/
theorem Subst.Similar.liftN :
    (n : Nat) → {Γ Δ : Scope} → {θ₁ θ₂ : Subst k Γ Δ} → {ν : Nesting Name Δ} →
      Subst.Similar θ₁ θ₂ @ν →
        Subst.Similar (Subst.liftN n θ₁) (Subst.liftN n θ₂) (Nesting.liftN n @ν)
  | 0, _, _, _, _, _, h => h
  | n + 1, Γ, Δ, _, _, _, h => Subst.Similar.liftN n (Γ := .var :: Γ) (Δ := .var :: Δ) h.lift

/-- Two substitutions that give the variables abstractions of the same shape, each followed by an
abstraction for a new entry, without position, do so. -/
theorem Subst.Similar.snoc {Γ Δ : Scope} {e : Scope.Entry} {θ₁ θ₂ : Subst k Γ Δ}
    {ν : Nesting Name Δ} (h : Subst.Similar θ₁ θ₂ @ν)
    (B₁ B₂ : Term k (Γ.extend e.params.length)) :
    Subst.Similar (Subst.snoc (e := e) θ₁ B₁) (Subst.snoc θ₂ B₂) (Nesting.lift @ν) := by
  intro a x
  cases x with
  | zero => exact .plain
  | succ x => exact h x

mutual

-- ADE: none.
/-- A type at two instantiations of its levels and at two substitutions that give the variables
abstractions of the same shape, at their nestings, has the same shape at its nesting, whatever
the declared types hold. -/
theorem Term.similar_subst {k' : Nat} (mark : Name → Option Name) (ls₁ ls₂ : Fin k → Level k') :
    {Γ Δ : Scope} → {θ₁ θ₂ : Subst k' Γ Δ} → {ν : Nesting Name Δ} → Subst.Similar θ₁ θ₂ @ν →
      (A : Term k Δ) →
        Term.Similar (A.nest mark @ν) ((A.substLevels ls₁).subst θ₁) ((A.substLevels ls₂).subst θ₂)
  | _, _, θ₁, θ₂, _, h, .var x ts => by
    rw [Term.substLevels, Term.substLevels, Term.subst, Term.subst, Term.instantiate_eq_subst₀,
      Term.instantiate_eq_subst₀]
    exact (h x).subst₀ _ _
  | _, _, _, _, _, h, .inst D _ _ _ as => by
    rw [Term.substLevels, Term.substLevels, Term.subst, Term.subst, Term.nest]
    split
    · exact .direct
    · unfold Nest.ofArgs
      split
      · exact .plain
      · exact .inst (InstanceArgs.similar_subst mark ls₁ ls₂ h as)
  | _, _, _, _, _, _, .sort _ => .plain
  | _, _, _, _, _, _, .const _ _ _ _ => .plain
  | _, _, _, _, _, _, .ctor _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, _, .equality .. | _, _, _, _, _, _, .refl ..
  | _, _, _, _, _, _, .transp .. | _, _, _, _, _, _, .propExt .. => .plain

/-- The arguments of an instance at two instantiations of their levels and at two substitutions
that give the variables abstractions of the same shape have the same shape at their nestings. -/
theorem InstanceArgs.similar_subst {k' : Nat} (mark : Name → Option Name)
    (ls₁ ls₂ : Fin k → Level k') :
    {Γ Δ Ξ : Scope} → {θ₁ θ₂ : Subst k' Γ Δ} → {ν : Nesting Name Δ} → Subst.Similar θ₁ θ₂ @ν →
      (as : InstanceArgs k Δ Ξ) →
        InstanceArgs.Similar (as.nest mark @ν) ((as.substLevels ls₁).subst θ₁)
          ((as.substLevels ls₂).subst θ₂)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, h, .snoc as B => by
    rw [InstanceArgs.substLevels, InstanceArgs.substLevels, InstanceArgs.subst, InstanceArgs.subst,
      InstanceArgs.nest]
    exact .snoc (InstanceArgs.similar_subst mark ls₁ ls₂ h as)
      (Term.similar_subst mark ls₁ ls₂ (h.liftN _) B)

end

/-! ## Arguments of an Instance and Observations -/

/-- The arguments of two instances of the same shape give the parameters abstractions of the same
shape, at the nestings of the arguments. -/
theorem InstanceArgs.Similar.toSubst {Γ : Scope} :
    {Δ : Scope} → {ns : List (Nest Name)} → {as₁ as₂ : InstanceArgs k Γ Δ} →
      InstanceArgs.Similar ns as₁ as₂ →
        Subst.Similar as₁.toSubst as₂.toSubst (Nesting.ofArgs ns)
  | _, _, _, _, .nil, _, x => nomatch x
  | _, ns, _, _, .snoc has hB, _, .zero => by
    cases ns <;> exact hB
  | _, ns, _, _, .snoc has hB, _, .succ x => by
    cases ns with
    | nil =>
      have h := has.toSubst x
      cases x <;> exact h
    | cons _ _ => exact has.toSubst x

/-- Two substitutions that give the variables of the scope of destructors abstractions of the same
shape, each followed by abstractions for the destructors before a position, which have no position,
do so in the scope of this position. -/
theorem Destructors.Pos.similar {k' : Nat} {Γ' : Scope}
    (o₁ o₂ : Name → (ps' : List Parameter) → Term k (Γ'.extend ps'.length)) {d : Name}
    {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k' Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k' Ξ ps} → {B : Term k' (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hd : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
      {θ₁ θ₂ : Subst k Γ' Γ} → {ν : Nesting Name Γ} → Subst.Similar θ₁ θ₂ @ν →
        Subst.Similar (hd.obsSubst o₁ θ₁) (hd.obsSubst o₂ θ₂) (hd.nesting @ν)
  | _, _, _, _, _, _, _, .here, _, _, _, h => h
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (ψ' := ψ') hd, _, _, _, h =>
    hd.similar o₁ o₂ (h.snoc (e := .secondOrder ps' ψ') (o₁ d' ps') (o₂ d' ps'))

end Sic.Core
