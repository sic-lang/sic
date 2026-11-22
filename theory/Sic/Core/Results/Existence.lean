module

public import Sic.Core.Lifting.Extension
public import Sic.Core.Lifting.Instantiation
public import Sic.Core.Results
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Observations
import Sic.Core.Lifting.Shape
import Sic.Core.Results.Substitution
import Sic.Core.Syntax.Signature
import Sic.Core.Syntax.Terms

/-!
# Existence of the Recursive Results

A term of a type that is lifted has a recursive result, in a signature whose names are distinct
and that declares each lifting after the destructors that it lifts: the recursive results of the
terms of fields exist when the types of these results do, and so do those of the terms of the
fields of a constructor.

The result of a term of an instance of a codata type is a corecursor whose branches are the
results of the observations of the term, at the variables of their arguments.
The type of an observation is not a part of the type of the term: it is the result of a
destructor, as the declaration of the type gives it, at the arguments of the instance, and the
declaration of the lifting lifts it, in the signature before the lifting.
The proof thus follows the signature, entry by entry: the result of a destructor is lifted by the
liftings declared before, which have results, and its parameters are given the arguments of the
instance, which have results since they are lifted where the instance is.

A branch is a term under the arguments of its destructor, and the result of a parameter applied to
arguments is that of its argument at these arguments: a type has results under every substitution
of its lifting, so that the property goes under the variables and to the arguments.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig sig₁ : Signature} {v : Lifting.Variables}

/-! ## Types Whose Terms Have Results -/

/-- Each term of the type `A`, whose nesting is `n`, substituted by a substitution of its lifting
`ρ`, has a recursive result, whatever the results of the terms of the types of the block are. -/
def Term.HasResult (sig : Signature) (v : Lifting.Variables) {Γ' Γ : Scope} (ρ : Lifting k Γ' Γ)
    (n : Nest Name) (A : Term k Γ) : Prop :=
  ∀ (Γ₂ : Scope) (θ : Subst k Γ₂ Γ) (θ' : Subst k Γ₂ Γ') (ρ₂ : Lifting k Γ₂ Γ₂),
    Lifting.Substitutes θ θ' ρ ρ₂ → ∀ (φ : Name → Term k (.var :: Γ₂)) (t : Term k Γ₂),
      ∃ e, Term.NestedResult sig v ρ₂ φ n (A.subst θ) t e

namespace Term.HasResult

variable {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n : Nest Name}

/-- A type whose terms have results, substituted. -/
theorem subst {A : Term k Γ} (h : Term.HasResult sig v ρ n A) {Δ' Δ : Scope} {θ : Subst k Δ Γ}
    {θ' : Subst k Δ' Γ'} {ρ' : Lifting k Δ' Δ} (hs : Lifting.Substitutes θ θ' ρ ρ') :
    Term.HasResult sig v ρ' n (A.subst θ) := by
  intro Γ₂ θ₂ θ₂' ρ₂ hs₂ φ t
  obtain ⟨e, he⟩ := h _ _ _ _ (hs.comp hs₂) φ t
  rw [← Term.subst_subst_of (fun _ => rfl) A] at he
  exact ⟨e, he⟩

/-- A type whose terms have results, by a lifting in a scope extended by a new entry, has them by
the lifting. -/
theorem of_weaken {e : Scope.Entry} {A : Term k Γ}
    (h : Term.HasResult sig v (ρ.weaken (e := e)) n A) : Term.HasResult sig v ρ n A := by
  intro Γ₂ θ θ' ρ₂ hs φ t
  exact h _ _ _ _ (hs.ofSnoc (.sort ⟨.prop, .zero⟩)) φ t

/-- A type whose terms have results, under new variables, renamed under them in a scope extended
by a new entry. -/
theorem lift (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry} (m : Nat)
    {A : Term k (Γ.extend m)} (h : Term.HasResult sig v (ρ.liftN m) n A) :
    Term.HasResult sig v ((ρ.lift (e := e)).liftN m) n (A.rename (Ren.liftN m Ren.weaken)) := by
  have h' := h.subst ((Lifting.Substitutes.ofLift (e := e) hρ).liftN m)
  have e₁ : A.subst (Subst.liftN m (Ren.toSubst (Ren.weaken (e := e)))) =
      A.rename (Ren.liftN m Ren.weaken) :=
    (Term.rename_eq_subst_of (Subst.liftN_eta_of m fun _ => rfl) A).symm
  rw [e₁] at h'
  exact h'

/-- A type whose terms have results, under new variables, has them by the lifting in a scope
extended by a new entry. -/
theorem weaken (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry} (m : Nat)
    {A : Term k (Γ.extend m)} (h : Term.HasResult sig v (ρ.liftN m) n A) :
    Term.HasResult sig v ((ρ.weaken (e := e)).liftN m) n A := by
  have h' := h.subst ((Lifting.Substitutes.ofWeaken (e := e) hρ).liftN m)
  have e₁ : A.subst (Subst.liftN m (Ren.toSubst fun x => x)) = A :=
    Term.subst_id_of (Subst.liftN_id_of m fun _ => rfl) A
  rw [e₁] at h'
  exact h'

/-- An abstraction whose terms have results, under the variables of its telescope, at arguments
for these variables. -/
theorem instantiate (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) :
    {ps : List Parameter} → {A : Term k (Γ.extend ps.length)} → (us : Args k Γ ps) →
      Term.HasResult sig v (ρ.liftN ps.length) n A → Term.HasResult sig v ρ n (A.instantiate us)
  | [], _, .nil, h => h
  | _ :: ps, A, .cons u us, h => by
    have h' : Term.HasResult sig v (ρ.liftN ps.length) n
        (A.subst (Subst.liftN ps.length (Subst₀.toSubst (Subst₀.single u)))) :=
      Term.HasResult.subst (ρ := ρ.lift.liftN ps.length) h
        ((Lifting.Substitutes.single hρ u).liftN ps.length)
    exact (congrArg (fun B : Term k (Γ.extend ps.length) =>
        Term.HasResult sig v ρ n (B.instantiate us))
      (Term.subst₀_liftN_eq_subst ps.length (Subst₀.single u) A)).mpr
      (Term.HasResult.instantiate hρ us h')

end Term.HasResult

/-! ## Substitutions Whose Abstractions Have Results -/

/-- The terms of the abstraction that the substitution `θ` gives each variable with a position,
where `ν` gives the nestings of the variables, have results at the nesting of the variable, by the
lifting `ρ` under the variables of the abstraction. -/
def Subst.HasResults (sig : Signature) (v : Lifting.Variables) {Γ' Γ Δ : Scope} (θ : Subst k Γ Δ)
    (ρ : Lifting k Γ' Γ) (ν : Nesting Name Δ) : Prop :=
  ∀ (a : Scope.Entry) (x : Var Δ a), ν x ≠ .plain →
    Term.HasResult sig v (ρ.liftN a.params.length) (ν x) (θ x)

/-- A lifting that lifts no variable lifts none under a new entry. -/
theorem Lifting.lift_motive_eq_none {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry} :
    ∀ {a} (x : Var (e :: Γ) a), (ρ.lift (e := e)).motive x = none
  | _, .zero => rfl
  | _, .succ x => by
    show (ρ.motive x).map _ = none
    rw [hρ x]
    rfl

namespace Subst.HasResults

variable {Γ' Γ Δ : Scope} {θ : Subst k Γ Δ} {ρ : Lifting k Γ' Γ} {ν : Nesting Name Δ}

/-- A substitution whose abstractions have results, under a new entry, which has no position. -/
theorem lift (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry}
    (h : Subst.HasResults sig v θ ρ @ν) :
    Subst.HasResults sig v (Subst.lift (e := e) θ) ρ.lift (Nesting.lift @ν) := fun _ x =>
  match x with
  | .zero => fun hx => absurd rfl hx
  | .succ x => fun hx => (h _ x hx).lift hρ _

/-- A substitution whose abstractions have results, under new variables. -/
theorem liftN : (m : Nat) → {Γ' Γ Δ : Scope} → {θ : Subst k Γ Δ} → {ρ : Lifting k Γ' Γ} →
    {ν : Nesting Name Δ} → (∀ {a} (x : Var Γ a), ρ.motive x = none) →
      Subst.HasResults sig v θ ρ @ν →
        Subst.HasResults sig v (Subst.liftN m θ) (ρ.liftN m) (Nesting.liftN m @ν)
  | 0, _, _, _, _, _, _, _, h => h
  | m + 1, Γ', Γ, Δ, _, _, _, hρ, h =>
    liftN (Γ' := .var :: Γ') (Γ := .var :: Γ) (Δ := .var :: Δ) m
      (Lifting.lift_motive_eq_none hρ) (h.lift hρ)

/-- A substitution whose abstractions have results has them by the lifting in a scope extended by
a new entry. -/
theorem weaken (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {e : Scope.Entry}
    (h : Subst.HasResults sig v θ ρ @ν) : Subst.HasResults sig v θ (ρ.weaken (e := e)) @ν :=
  fun _ x hx => (h _ x hx).weaken hρ _

/-- The substitution of arguments whose abstractions have results, followed by a term for a new
variable, which has no position. -/
theorem snocTerm {Δ : Scope} {as : InstanceArgs k Γ Δ} {ν : Nesting Name Δ}
    (h : Subst.HasResults sig v as.toSubst ρ @ν) (t : Term k Γ) :
    Subst.HasResults sig v (InstanceArgs.snoc (e := .var) as t).toSubst ρ (Nesting.lift @ν) :=
  fun _ x =>
    match x with
    | .zero => fun hx => absurd rfl hx
    | .succ x => fun hx => h _ x hx

/-- The substitution of arguments whose abstractions have results, substituted. -/
theorem substArgs {Δ : Scope} {as : InstanceArgs k Γ Δ} {ν : Nesting Name Δ}
    (h : Subst.HasResults sig v as.toSubst ρ @ν) {Ξ' Ξ : Scope} {w : Subst k Ξ Γ}
    {w' : Subst k Ξ' Γ'} {ρ₂ : Lifting k Ξ' Ξ} (hs : Lifting.Substitutes w w' ρ ρ₂) :
    Subst.HasResults sig v (as.subst w).toSubst ρ₂ @ν := fun a x hx => by
  show Term.HasResult sig v _ _ ((as.subst w).toSubst x)
  rw [← InstanceArgs.toSubst_subst w as x]
  exact (h _ x hx).subst (hs.liftN a.params.length)

/-- A substitution whose abstractions have results at the nestings of the arguments of an instance
has them at the nestings of the arguments of the nesting of this instance. -/
theorem ofArgs_args {ns : List (Nest Name)} (h : Subst.HasResults sig v θ ρ (Nesting.ofArgs ns)) :
    Subst.HasResults sig v θ ρ (Nesting.ofArgs (Nest.ofArgs ns).args) := by
  unfold Nest.ofArgs
  split
  · exact fun _ x hx => absurd (Nesting.ofArgs_nil x) hx
  · exact h

end Subst.HasResults

/-! ## Liftings Whose Instances Have Results -/

/-- Each term of an instance of a type lifted by a lifting that the signature `Σ₁` declares has a
recursive result in the signature `Σ`, when the terms of the arguments of the instance with a
position have. -/
def Signature.LiftingsHaveResults (sig₁ sig : Signature) : Prop :=
  ∀ (k : Nat) (v : Lifting.Variables) {decl : TypeDeclaration} {D : Name} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns},
    .typeDeclaration decl ∈ sig → D ∈ decl.names →
    .typeDeclaration (decl.lifting D S ns body) ∈ sig₁ →
    ∀ {Γ : Scope} {ρ : Lifting k Γ Γ}, (∀ {a} (x : Var Γ a), ρ.motive x = none) →
    ∀ {n : Nest Name} {qs : List Quality} {ls : List (Level k)} {ms : List (Lifting.Result k)}
      {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {Δ' : Scope} {as' : InstanceArgs k Γ Δ'},
      (∀ E, n ≠ .direct E) → Instance.AsMany decl.sorts decl.grades qs ps → ls.length =
      decl.levels → InstanceArgs.Lifts sig v
      ρ n.args as S ms as' → S ≠ [] →
      Subst.HasResults sig v as.toSubst ρ (Nesting.ofArgs n.args) →
      ∀ (φ : Name → Term k (.var :: Γ)) (t : Term k Γ),
        ∃ e, Term.NestedResult sig v ρ φ n (.inst D qs ls ps as) t e

/-! ## Results of a Type Lifted by a Declaration -/

mutual

/-- The terms of a type lifted at no position, in a signature `Σ₁` whose liftings have results in
`Σ`, substituted by an instantiation of its lifting whose abstractions have results, have
results. -/
theorem Term.Lifts.hasResult_instantiate
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveResults sig₁ sig) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {m : Lifting.Result k} → Term.Lifts sig₁ v ρ n e A A' m → n = .plain →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
          Subst.HasResults sig v θ ρ' @ν →
            Term.HasResult sig v ρ' (A.nest (fun _ => none) @ν) (A.subst θ)
  | _, _, _, _, _, _, _, _, .var (x := x) (y := y) (m := m) (ts := ts) hx _, _, _, _, θ, _, ρ',
      ν, hI, ho => by
    obtain ⟨B', -, hL⟩ := hI.lifted x y m hx
    have hν : ν x ≠ .plain := fun h =>
      hL.not_avoidsLifted h (Term.avoidsLifted_of_none hI.motive' _ (θ x))
    rw [Term.subst]
    exact (ho _ x hν).instantiate hI.motive' (ts.subst θ)
  | _, _, _, _, _, _, _, _, .block _, hn, _, _, _, _, _, _, _, _ => nomatch hn
  | _, _, _, _, _, _, _, _, .inst h hD _ hqp hl has hS hL _, hn, _, _, _, _, _, _, hI, ho => by
    subst hn
    intro Γ₂ w w' ρ₂ hs φ t
    have has' := ((has.ofTypeDeclarations hsub).instantiate rfl hI).ofArgs_args.subst hs
    have ho' := ((has.hasResults_instantiate hsub hM rfl hI ho).ofArgs_args).substArgs hs
    simp only [Term.subst]
    exact hM _ v (hsub _ h) hD hL hs.motive' (fun E => Nest.ofArgs_ne_direct _ E) hqp hl has' hS
      ho' φ t

/-- The terms of the arguments of an instance lifted at no position, in a signature `Σ₁` whose
liftings have results in `Σ`, substituted by an instantiation of their lifting whose abstractions
have results, have results at their nestings. -/
theorem InstanceArgs.Lifts.hasResults_instantiate
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveResults sig₁ sig) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig₁ v ρ ns as S ms as' → ns = [] →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
          Subst.HasResults sig v θ ρ' @ν →
            Subst.HasResults sig v (as.subst θ).toSubst ρ'
              (Nesting.ofArgs (as.nest (fun _ => none) @ν))
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, _ => fun _ x => nomatch x
  | _, _, _, _, _, _, _, _, _, _, .lifted (a := a) has hB, hns, _, _, _, _, _, _, hI, ho => by
    subst hns
    intro a' x
    cases x with
    | zero =>
      exact fun _ => (hB.hasResult_instantiate hsub hM rfl (hI.liftN a.params.length).weaken
        ((ho.liftN a.params.length hI.motive').weaken
          (hI.liftN a.params.length).motive')).of_weaken
    | succ x => exact fun hx => has.hasResults_instantiate hsub hM rfl hI ho _ x hx
  | _, _, _, _, _, _, _, _, _, _, .absent (a := a) has hB _, hns, _, _, _, _, _, _, hI, ho => by
    subst hns
    intro a' x
    cases x with
    | zero =>
      intro hx
      refine absurd (Term.nest_eq_plain_of_avoids fun z hz => hB z ?_) hx
      cases hm : (Lifting.liftN a.params.length _).motive z with
      | none => exact absurd ((hI.liftN a.params.length).plain z hm) hz
      | some _ => rfl
    | succ x => exact fun hx => has.hasResults_instantiate hsub hM rfl hI ho _ x hx

end

/-! ## Results of a Type Lifted -/

mutual

/-- The terms of a type lifted, in a signature whose liftings have results, have results. -/
theorem Term.Lifts.hasResult (hM : Signature.LiftingsHaveResults sig sig) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m →
        Term.HasResult sig v ρ n A
  | _, _, _, _, _, _, _, _, .var hx _ => by
    intro Γ₂ θ θ' ρ₂ hs
    exact nomatch (hs.motive _).symm.trans hx
  | _, _, _, _, _, _, _, _, .block (b := b) hD => by
    intro Γ₂ θ θ' ρ₂ hs φ t
    rw [Term.subst]
    refine ⟨_, Term.NestedResult.block (b := b.subst θ θ') ?_⟩
    rw [hs.block, hD]
    rfl
  | _, _, _, _, _, _, _, _, .inst h hD hn hqp hl has hS hL _ => by
    intro Γ₂ θ θ' ρ₂ hs φ t
    rw [Term.subst]
    exact hM _ v h hD hL hs.motive' hn hqp hl (has.subst hs) hS
      ((has.hasResults hM).substArgs hs) φ t

/-- The terms of the arguments of an instance lifted, in a signature whose liftings have results,
have results at their nestings. -/
theorem InstanceArgs.Lifts.hasResults (hM : Signature.LiftingsHaveResults sig sig) :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
        Subst.HasResults sig v as.toSubst ρ (Nesting.ofArgs ns)
  | _, _, _, _, _, _, _, _, _, _, .nil => fun _ x => nomatch x
  | _, _, _, ns, _, _, _, _, _, _, .lifted has hB => fun _ x =>
    match x with
    | .zero => fun _ => by
      show Term.HasResult sig v _ (Nesting.ofArgs ns .zero) _
      rw [Nesting.ofArgs_zero]
      exact (hB.hasResult hM).of_weaken
    | .succ x => fun hx => by
      show Term.HasResult sig v _ (Nesting.ofArgs ns (.succ x)) _
      rw [Nesting.ofArgs_succ]
      exact has.hasResults hM _ x fun h => hx ((Nesting.ofArgs_succ ns x).trans h)
  | _, _, _, ns, _, _, _, _, _, _, .absent has _ hn => fun _ x =>
    match x with
    | .zero => fun hx => absurd ((Nesting.ofArgs_zero ns).trans hn) hx
    | .succ x => fun hx => by
      show Term.HasResult sig v _ (Nesting.ofArgs ns (.succ x)) _
      rw [Nesting.ofArgs_succ]
      exact has.hasResults hM _ x fun h => hx ((Nesting.ofArgs_succ ns x).trans h)

end

/-! ## Results of an Instance Lifted -/

/-- Each term of an instance of a codata type lifted, at a nesting that is not a position, has a
recursive result in a signature `Σ` whose names are distinct, when the terms of the arguments of
the instance with a position have, and when the destructors of the lifting are those of the type,
lifted in a signature `Σ₁` whose liftings have results in `Σ`: the result is the corecursor whose
branch of each destructor of the lifting is the result of the observation of the term by this
destructor, whose type is the result that the declaration lifts, instantiated by the arguments. -/
theorem TypeDeclaration.Lifts.hasResult (hsig : sig.Distinct)
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveResults sig₁ sig) {decl : TypeDeclaration} {D : Name}
    {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hdecl : .typeDeclaration decl ∈ sig) (hLd : decl.Lifts sig₁ D S body)
    (hL : .typeDeclaration (decl.lifting D S ns body) ∈ sig) {Γ : Scope} {ρ : Lifting k Γ Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {n : Nest Name} {qs : List Quality}
    {ls : List (Level k)} {ms : List (Lifting.Result k)} {ps : List Grade}
    {as : InstanceArgs k Γ decl.scope} {Δ' : Scope}
    {as' : InstanceArgs k Γ Δ'} (hn : ∀ E, n ≠ .direct E)
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels)
    (has : InstanceArgs.Lifts sig v ρ n.args as S ms as') (hS : S ≠ [])
    (ho : Subst.HasResults sig v as.toSubst ρ (Nesting.ofArgs n.args))
    (φ : Name → Term k (.var :: Γ)) (t : Term k Γ) :
    ∃ e, Term.NestedResult sig v ρ φ n (.inst D qs ls ps as) t e := by
  obtain ⟨T, hT, hn', hb⟩ := id hLd
  have hTs : sig.HasCodataType D decl T := ⟨hdecl, hT, hn'⟩
  have hqp' := hqp.lifting v has.length_eq
  have hl' : (ls ++ ms.map (·.level)).length = decl.levels + S.length := by
    rw [List.length_append, hl, List.length_map, has.length_eq]
  obtain ⟨hΔ, -⟩ := has.instantiates hρ S
    (fun i => (decl.liftingMotive S hqp'.inst
      i).substLevels ((ls ++ ms.map (·.level)).getFin hl'))
    (fun _ _ => Iff.rfl)
    (fun j h₁ h₂ => TypeDeclaration.liftingMotive_inst has.nodup hqp hl has.length_eq hl' j h₁ h₂)
  subst hΔ
  -- A branch for each destructor of the lifting: the result of the observation by it.
  have key : ∀ i, i < ns.length →
      ∃ b : (Σ n m a, Term k (((Γ.extend n).extend m).extend a)), ∀ d, ns[i]? = some d →
        ∃ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
          (hd : (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ)
          (g : Term k (Γ.extend ps₁.length)),
          b = ⟨0, 0, ps₁.length, g⟩ ∧
          Term.NestedResult sig v (ρ.liftN ps₁.length)
            (fun E => (φ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
            (B.nest (fun _ => none)
              (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs n.args))))
            ((B.substLevels (ls.getFin hl)).subst
              (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
            (t.observation D qs ls ps as d ps₁) g := by
    intro i hi
    have hmem : ns[i] ∈ ns := List.getElem_mem hi
    obtain ⟨p', q', ς', ps₁', Ξ', Θ', B', ψ', ⟨hd'⟩⟩ := Destructors.exists_pos
      (body hqp'.inst) hmem
    obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos
      (T.body hqp.inst)
      ((Destructors.Lifts.sublist (hb hqp'.inst)).subset hmem)
    obtain ⟨_, -, ρ₁, e₀, A₀, A₀', hL₁, hI, -, hnest, -, -, hA, -⟩ :=
      hLd.result hsig hTs hρ hqp hl hl' has t hpos hd'
        (fun _ _ => .sort ⟨.prop, .zero⟩)
    have hres := hL₁.hasResult_instantiate hsub hM rfl (hI.liftN ps₁.length)
      ((ho.snocTerm t).liftN ps₁.length hρ)
    rw [hnest, hA] at hres
    obtain ⟨g, hg⟩ := hres _ _ _ _ (Lifting.Substitutes.refl (hI.liftN ps₁.length).motive')
      (fun E => (φ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
      (t.observation D qs ls ps as ns[i] ps₁)
    rw [Term.subst_id_of (fun _ => rfl)] at hg
    refine ⟨⟨0, 0, ps₁.length, g⟩, fun d hd'' => ?_⟩
    cases (List.getElem?_eq_getElem hi).symm.trans hd''
    exact ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hpos, g, rfl, hg⟩
  obtain ⟨gs, hgl, hgs⟩ := DestructorBranches.exists_of_forall ns.length _ key
  refine ⟨_, .inst hTs hn hqp hl has hS hL hgl ?_ ?_⟩
  · intro i d hi
    obtain ⟨b, hb', hP⟩ := hgs i (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hpos, g, rfl, -⟩ := hP d hi
    exact ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hpos, g, hb'⟩
  · intro i d p q ς ps₁ Ξ Θ B ψ g hi hpos hg
    obtain ⟨b, hb', hP⟩ := hgs i (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨p₀, q₀, ς₀, ps₀, Ξ₀, Θ₀, B₀, ψ₀, hpos₀, g₀, rfl, hN⟩ := hP d hi
    -- The position of a destructor is one, since the names of the destructors are distinct.
    exact Destructors.Pos.forall_of (hsig.destructors_nodup hTs)
      (motive := fun {_ _ _ ps₂ _ _ B₂ _} h => ∀ g' : Term k (Γ.extend ps₂.length),
        gs.get i = some ⟨0, 0, ps₂.length, g'⟩ →
          Term.NestedResult sig v (ρ.liftN ps₂.length)
            (fun E => (φ E).rename (Ren.lift (Ren.weakenN ps₂.length)))
            (B₂.nest (fun _ => none)
              (Nesting.liftN ps₂.length (h.nesting (Nesting.ofArgs n.args))))
            ((B₂.substLevels (ls.getFin hl)).subst
              (Subst.liftN _ (h.obsSubst (t.observation D qs ls ps as) as.toSubst)))
            (t.observation D qs ls ps as d ps₂) g')
      hpos₀ (fun g' hg' => DestructorBranches.get_inj hb' hg' ▸ hN) hpos g hg

/-! ## Signatures Whose Liftings Have Results -/

/-- The liftings that a signature whose names are distinct declares, each after the destructors
that it lifts, have results: those of the entries after a prefix of the signature, by induction on
these entries, since the destructors of a lifting are lifted by the liftings before it. -/
theorem Signature.LiftsInOrder.liftingsHaveResults (hsig : sig.Distinct)
    (hord : sig.LiftsInOrder) :
    ∀ (sig₁ pre : Signature), sig = pre ++ sig₁ → Signature.LiftingsHaveResults sig₁ sig
  | [], _, _ => by
    intro k v decl D S ns body _ _ hL
    exact nomatch hL
  | e :: sig₁, pre, he => by
    have ih := Signature.LiftsInOrder.liftingsHaveResults hsig hord sig₁ (pre ++ [e])
      (by rw [List.append_assoc]; exact he)
    intro k v decl D S ns body hdecl hD hL Γ ρ hρ n qs ls ls' ps as Δ' as' hn hqp hl has hS ho
      φ t
    rcases List.mem_cons.1 hL with heq | hL'
    · subst heq
      exact (hord pre sig₁ decl D S ns body he hdecl hD).2.hasResult hsig
        (fun _ h => he ▸ List.mem_append_right pre (List.mem_cons_of_mem _ h)) ih hdecl
        (he ▸ List.mem_append_right pre List.mem_cons_self) hρ hn hqp hl has hS ho φ t
    · exact ih _ v hdecl hD hL' hρ hn hqp hl has hS ho φ t

/-! ## Existence -/

/-- A term of a type that is lifted, by a lifting that lifts no variable, has a recursive result,
in a signature whose names are distinct and that declares each lifting after the destructors that
it lifts, whatever the results of the terms of the types of the block are. -/
theorem Term.Lifts.exists_nestedResult (hsig : sig.Distinct) (hord : sig.LiftsInOrder)
    {Γ : Scope} {ρ : Lifting k Γ Γ} (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {n : Nest Name}
    {u A A' : Term k Γ} {m : Lifting.Result k} (h : Term.Lifts sig v ρ n u A A' m)
    (φ : Name → Term k (.var :: Γ)) (t : Term k Γ) :
    ∃ e, Term.NestedResult sig v ρ φ n A t e := by
  obtain ⟨e, he⟩ := h.hasResult (hord.liftingsHaveResults hsig sig [] rfl) _ _ _ _
    (Lifting.Substitutes.refl hρ) φ t
  rw [Term.subst_id_of (fun _ => rfl)] at he
  exact ⟨e, he⟩

/-- The terms of fields whose recursive results have types, substituted by a substitution of the
lifting of these types, have recursive results, in a signature whose liftings have results: a
recursive field has the result of its term, and a nested field, whose type is lifted, has one
since the terms of a type lifted have. -/
theorem Terms.ResultTypes.exists_resultTerms (hM : Signature.LiftingsHaveResults sig sig) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} → {πs : List Grade} →
      Terms.ResultTypes sig v ρ ns ps As xs R πs →
      ∀ {Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ Δ'} {ρ₂ : Lifting k Γ Γ},
        Lifting.Substitutes θ θ' ρ ρ₂ → ∀ φ : Name → Term k (.var :: Γ),
          ∃ (ps'' : List Parameter) (rs : Args k Γ ps''),
            Terms.ResultTerms sig v ρ₂ φ ns ps (As.subst θ) (xs.subst θ) rs
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _ => ⟨[], .nil, .nil⟩
  | _, _, _, _, _, _, _, _, _, _, .plain h, _, _, _, _, hs, φ => by
    obtain ⟨_, rs, hr⟩ := h.exists_resultTerms hM hs φ
    rw [Terms.subst, Terms.subst]
    exact ⟨_, rs, .plain hr⟩
  | _, _, _, _, _, _, _, _, _, _, .recursive _ h, _, _, _, _, hs, φ => by
    obtain ⟨_, rs, hr⟩ := h.exists_resultTerms hM (hs.ofSnoc (.sort ⟨.prop, .zero⟩)) φ
    rw [Terms.subst, Terms.subst]
    exact ⟨_, .cons _ rs, .recursive hr⟩
  | _, _, _, _, _, _, _, _, _, _, .nested (x := x) hA h, _, θ, _, _, hs, φ => by
    obtain ⟨_, rs, hr⟩ := h.exists_resultTerms hM (hs.ofSnoc (.sort ⟨.prop, .zero⟩)) φ
    obtain ⟨e, he⟩ := hA.hasResult hM _ _ _ _ hs φ (x.subst θ)
    rw [Terms.subst, Terms.subst]
    exact ⟨_, .cons e rs, .nested he hr⟩

/-- A lifting that lifts no variable and renames none, under the variables of a telescope,
substituted by arguments of the telescope. -/
theorem Lifting.Substitutes.args {Γ : Scope} {ρ : Lifting k Γ Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) (hid : ∀ {a} (x : Var Γ a), ρ.ren x = x)
    {ps : List Parameter} (ts : Args k Γ ps) :
    Lifting.Substitutes (Subst₀.toSubst ts.toSubst₀) (Subst₀.toSubst ts.toSubst₀)
      (ρ.liftN ps.length) ρ :=
  have hts : ∀ {a} (x : Var Γ a),
      Subst₀.toSubst ts.toSubst₀ (x.weakenN ps.length) = Var.eta x :=
    fun x => by
      show (ts.toSubst₀ (x.weakenN ps.length)).eta = _
      rw [Args.toSubst₀_weakenN]
      rfl
  Lifting.Substitutes.ofLiftN hρ ps.length hts hts fun x => by
    rw [Lifting.liftN_ren]
    show Subst₀.toSubst ts.toSubst₀ (Ren.liftN ps.length ρ.ren x) = _
    rw [Ren.liftN_id_of ps.length hid x, Term.rename_id_of (Ren.liftN_id_of _ hid)]

/-- The terms of the fields of a telescope whose recursive results have types have recursive
results, in a signature whose names are distinct and that declares each lifting after the
destructors that it lifts, where the lifting of the block lifts no variable and renames none,
whatever the results of the terms of the types of the block are. -/
theorem Telescope.exists_resultTerms (hsig : sig.Distinct) (hord : sig.LiftsInOrder) {Γ : Scope}
    {ρ : Lifting k Γ Γ} (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none)
    (hid : ∀ {a} (x : Var Γ a), ρ.ren x = x) {ns : List (Nest Name)} {ps ps' : List Parameter}
    {Θ : Telescope k Γ ps} {R : Telescope k (Γ.extend ps.length) ps'} {πs : List Grade}
    (h : Terms.ResultTypes sig v (ρ.liftN ps.length) ns ps Θ.types (Args.bound (Γ := Γ) ps).terms
      R πs)
    (φ : Name → Term k (.var :: Γ)) (ts : Args k Γ ps) :
    ∃ rs : Args k Γ ps', Terms.ResultTerms sig v ρ φ ns ps (Θ.typesAt ts) ts.terms rs := by
  obtain ⟨ps'', rs, hr⟩ := Terms.ResultTypes.exists_resultTerms
    (hord.liftingsHaveResults hsig sig [] rfl) h (Lifting.Substitutes.args hρ hid ts) φ
  rw [← Terms.subst₀_eq_subst, ← Terms.subst₀_eq_subst, Telescope.types_toSubst₀,
    ← Args.terms_subst₀, Args.bound_toSubst₀] at hr
  obtain rfl : ps'' = ps' := hr.params_eq.trans h.params_eq.symm
  exact ⟨rs, hr⟩

/-- The terms of the fields of a constructor whose recursive results have types have recursive
results, in a signature whose names are distinct and that declares each lifting after the
destructors that it lifts, where the lifting of the block lifts no variable and renames none,
whatever the results of the terms of the types of the block are. -/
theorem Constructor.ResultTypes.exists_resultTerms (hsig : sig.Distinct)
    (hord : sig.LiftsInOrder) {j g k' : Nat} {Δ Γ : Scope} {c : Constructor j g k' Δ}
    {I : Instance j g} {names : List Name} {ls : Fin k' → Level k} {as : InstanceArgs k Γ Δ}
    {ρ : Lifting k Γ Γ} (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none)
    (hid : ∀ {a} (x : Var Γ a), ρ.ren x = x) {ps' : List Parameter}
    {R : Telescope k (Γ.extend (c.params I).length) ps'} {πs : List Grade}
    (h : Constructor.ResultTypes sig v c I names ls as ρ R πs) (φ : Name → Term k (.var :: Γ))
    (ts : Args k Γ (c.params I)) :
    ∃ rs : Args k Γ ps', Constructor.ResultTerms sig v c I names ls as ρ φ ts rs :=
  Telescope.exists_resultTerms hsig hord hρ hid h φ ts

end Sic.Core
