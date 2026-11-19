module

public import Sic.Core.Lifting.Observations
public import Sic.Core.Shape.Results
public import Sic.Core.Substitution.Closed
import Sic.Core.Lifting.Functionality
import Sic.Core.Positivity.Substitution
import Sic.Core.Substitution.Nesting

/-!
# Shapes of the Substituted Types

The shape of a type of the recursive results of annex 16 of RFC 36 does not read the levels, and a
substitution that keeps the nestings of the variables keeps it: such a substitution gives each
variable a variable with its shape, or, to a variable that has none, an observation, which has
none either.
The shapes follow a lifting when each variable lifted has a shape that carries the factor and the
ownership of its motive, and the others none.
A type without position, at nestings of its variables none of which has a position where it
occurs, has no shape.

The run time of the nested results relates the closed types of the results of the destructors,
while the erasure computes the shapes on the types that their declarations give, where the
parameters have the shapes of the arguments: a type lifted at no position, substituted by an
instantiation of its lifting, has, at its nesting, the shape of the type where each variable lifted
has the shape of what the instantiation gives it, at its nesting, when no variable of the scope of
the instantiation has a position, and the types lifted have shapes where the variables have the
shapes of their liftings, as a signature whose liftings have shapes gives them: an argument whose
nesting has a position and has no shape would leave the instance without shape at its nesting,
while the type of the declaration, where the arguments have no nesting, keeps the others.
The instantiation gives a variable lifted an abstraction lifted by a lifting that lifts no variable,
which keeps its shape at the arguments of the variable, and a renaming keeps the shapes, under the
variables of the arguments of an instance.
So the result of a destructor of a codata type, at a closed instance lifted at a term, at the
observations of the term and at closed arguments, has the shape of the result of the destructor where
the parameters have the shapes of the arguments of the instance, the shape that the shape of the
lifting of the type gives the destructor of the lifting.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig : Signature} {v : Lifting.Variables} {md : Mode}
  {ax : Grade → Multiplicity} {lookup : Shape.Lookup}
  {block : Name → Option Shape.Motive}

/-! ## Shapes That Follow a Lifting -/

/-- The shape `m'` carries the factor and the ownership of the result `m`. -/
def Shape.Motive.Of (m' : Shape.Motive) (m : Lifting.Result k) : Prop :=
  m'.factor = m.factor ∧ m'.ownership = m.ownership

/-- The shapes `m̄'` carry the factors and the ownerships of the results `m̄`, one by one. -/
def Shape.Motive.AllOf (ms' : List Shape.Motive) (ms : List (Lifting.Result k)) : Prop :=
  ms'.map (fun m' => (m'.factor, m'.ownership)) = ms.map (fun m => (m.factor, m.ownership))

/-- Shapes that carry the factors and the ownerships of results are as many as these. -/
theorem Shape.Motive.AllOf.length_eq {ms' : List Shape.Motive} {ms : List (Lifting.Result k)}
    (h : Shape.Motive.AllOf ms' ms) : ms'.length = ms.length := by
  have := congrArg List.length h
  rwa [List.length_map, List.length_map] at this

/-- The shapes `ν` of the variables follow the lifting `ρ`: a variable lifted has a shape, which
carries the factor and the ownership of its motive, and the others have no position. -/
def Lifting.Shapes {Γ' Γ : Scope} (ρ : Lifting k Γ' Γ) (ν : Nesting Shape.Motive Γ) : Prop :=
  ∀ {a : Scope.Entry} (x : Var Γ a), (ρ.motive x = none ∧ ν x = .plain) ∨
    ∃ (y : Var Γ' a.motive) (m : Lifting.Result k) (m' : Shape.Motive),
      ρ.motive x = some (y, m) ∧ ν x = .direct m' ∧ m'.Of m

namespace Lifting.Shapes

variable {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {ν : Nesting Shape.Motive Γ}

/-- Shapes that follow a lifting follow it under a new entry of both scopes. -/
theorem lift {e : Scope.Entry} (h : ρ.Shapes @ν) : (ρ.lift (e := e)).Shapes (Nesting.lift @ν) := by
  intro a x
  cases x with
  | zero => exact .inl ⟨rfl, rfl⟩
  | succ x =>
    rcases h x with ⟨h₁, h₂⟩ | ⟨y, m, m', h₁, h₂, h₃⟩
    · exact .inl ⟨by show (ρ.motive x).map _ = none; rw [h₁]; rfl, h₂⟩
    · exact .inr ⟨.succ y, m, m', by show (ρ.motive x).map _ = _; rw [h₁]; rfl, h₂, h₃⟩

/-- Shapes that follow a lifting follow it under new variables of both scopes. -/
theorem liftN : (n : Nat) → {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ν : Nesting Shape.Motive Γ} →
    ρ.Shapes @ν → (ρ.liftN n).Shapes (Nesting.liftN n @ν)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => liftN n h.lift

/-- Shapes that follow a lifting follow it in a scope extended by a new entry. -/
theorem weaken {e : Scope.Entry} (h : ρ.Shapes @ν) : (ρ.weaken (e := e)).Shapes @ν := by
  intro a x
  rcases h x with ⟨h₁, h₂⟩ | ⟨y, m, m', h₁, h₂, h₃⟩
  · exact .inl ⟨by show (ρ.motive x).map _ = none; rw [h₁]; rfl, h₂⟩
  · exact .inr ⟨.succ y, m, m', by show (ρ.motive x).map _ = _; rw [h₁]; rfl, h₂, h₃⟩

/-- A variable whose shape has a position is lifted. -/
theorem isSome {a : Scope.Entry} (h : ρ.Shapes @ν) (x : Var Γ a) (hx : ν x ≠ .plain) :
    (ρ.motive x).isSome := by
  rcases h x with ⟨-, h₂⟩ | ⟨y, m, -, h₁, -, -⟩
  · exact absurd h₂ hx
  · rw [h₁]
    rfl

end Lifting.Shapes

/-- The motive of a type of a block in a lifting under new variables has the ownership of its motive
in the lifting. -/
theorem Lifting.liftN_block_ownership {D : Name} : (n : Nat) → {Γ' Γ : Scope} →
    {ρ : Lifting k Γ' Γ} → {b : Lifting.BlockMotive k (Γ'.extend n) (Γ.extend n)} →
    (ρ.liftN n).block D = some b → ∃ b₀, ρ.block D = some b₀ ∧ b₀.ownership = b.ownership
  | 0, _, _, _, _, h => ⟨_, h, rfl⟩
  | n + 1, _, _, ρ, _, h => by
    obtain ⟨b₁, h₁, he⟩ := Lifting.liftN_block_ownership n (ρ := ρ.lift) h
    obtain ⟨b₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h₁
    exact ⟨b₀, h₀, he⟩

/-- Shapes of the types of a block that carry the ownerships of their motives in a lifting still do
under new variables and in the scope extended by an entry. -/
theorem Lifting.blockShapes_liftN_weaken {block : Name → Option Shape.Motive} {Γ' Γ : Scope}
    {ρ : Lifting k Γ' Γ} (n : Nat) {e : Scope.Entry}
    (hb : ∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) :
    ∀ D b, ((ρ.liftN n).weaken (e := e)).block D = some b →
      ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩ := fun D _ hD => by
  obtain ⟨b₁, hb₁, rfl⟩ := Option.map_eq_some_iff.1 hD
  obtain ⟨b₀, hb₀, he⟩ := Lifting.liftN_block_ownership n hb₁
  obtain ⟨Υ, hΥ⟩ := hb D b₀ hb₀
  exact ⟨Υ, he ▸ hΥ⟩

/-- A lifting without type of a block has none under new variables. -/
theorem Lifting.liftN_block_none : (n : Nat) → {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} →
    (∀ D, ρ.block D = none) → ∀ D, (ρ.liftN n).block D = none
  | 0, _, _, _, h => h
  | n + 1, _, _, ρ, h => Lifting.liftN_block_none n (ρ := ρ.lift) fun D => by
    show (ρ.block D).map _ = none
    rw [h D]
    rfl

/-- A lifting without type of a block has none in a scope extended by a new entry. -/
theorem Lifting.weaken_block_none {Γ' Γ : Scope} {e : Scope.Entry} {ρ : Lifting k Γ' Γ}
    (h : ∀ D, ρ.block D = none) : ∀ D, (ρ.weaken (e := e)).block D = none := fun D => by
  show (ρ.block D).map _ = none
  rw [h D]
  rfl

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
      (ds.substLevels ls').shape sig v md ax lookup D @ν = ds.shape sig v md ax lookup D @ν
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
        as.shapes v lookup block @ν [] = some []
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

/-! ## Renamings -/

/-- A renamed type has the shape of the type, at the shapes of the variables renamed. -/
theorem Term.shape_rename {Γ Δ : Scope} (α : Ren Γ Δ) {ν : Nesting Shape.Motive Δ}
    {ν' : Nesting Shape.Motive Γ} (h : ∀ (a : Scope.Entry) (x : Var Δ a), ν' (α x) = ν x)
    {n : Nest Name} (A : Term k Δ) :
    (A.rename α).shape v lookup block @ν' n = A.shape v lookup block @ν n := by
  rw [Term.rename_eq_subst]
  exact Term.shape_subst_of (fun x => .inr ⟨α x, Args.bound _, rfl, h _ x⟩) A

/-! ## Nestings Without Position -/

/-- The arguments of an instance, at nestings none of which has a position, have the shapes that
they have at no nesting. -/
theorem InstanceArgs.shapes_of_all_isPlain {Γ : Scope} {ν : Nesting Shape.Motive Γ} :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → {ns : List (Nest Name)} →
      ns.all Nest.isPlain = true → as.shapes v lookup block @ν ns = as.shapes v lookup block @ν []
  | _, .nil, _, _ => rfl
  | _, .snoc _ _, [], _ => rfl
  | _, .snoc as B, n :: ns, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [InstanceArgs.shapes, InstanceArgs.shapes, List.tail_cons, List.headD_cons, List.tail_nil,
      List.headD_nil, Nest.eq_plain_of_isPlain h.1, InstanceArgs.shapes_of_all_isPlain as h.2]

/-- The arguments of an instance have the same shapes at their nestings and at the nestings of the
arguments of the nesting of the instance. -/
theorem InstanceArgs.shapes_ofArgs_args {Γ Δ : Scope} {ν : Nesting Shape.Motive Γ}
    (as : InstanceArgs k Γ Δ) (ns : List (Nest Name)) :
    as.shapes v lookup block @ν (Nest.ofArgs ns).args = as.shapes v lookup block @ν ns := by
  unfold Nest.ofArgs
  split
  · next hns => exact (InstanceArgs.shapes_of_all_isPlain as hns).symm
  · rfl

/-! ## Liftings That Lift No Variable -/

mutual

/-- A type lifted by a lifting that lifts no variable, substituted, has the shape of the type, at
the same nesting, where no variable has a position, on either side. -/
theorem Term.Lifts.shape_subst :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m →
      (∀ {a} (x : Var Δ a), ρ.motive x = none) →
      ∀ {Γ : Scope} (θ : Subst k Γ Δ) {νs : Nesting Shape.Motive Δ}
        {νs' : Nesting Shape.Motive Γ}, (∀ (a : Scope.Entry) (x : Var Δ a), νs x = .plain) →
        (∀ (a : Scope.Entry) (x : Var Γ a), νs' x = .plain) →
          (A.subst θ).shape v lookup block @νs' n = A.shape v lookup block @νs n
  | _, _, _, _, _, _, _, _, .var hx _, hρ, _, _, _, _, _, _ => by
    rw [hρ] at hx
    exact nomatch hx
  | _, _, _, _, _, _, _, _, .block _, _, _, _, _, _, _, _ => by
    simp only [Term.subst, Term.shape]
  | _, _, _, n, _, _, _, _, .inst _ _ hn _ _ _ has _ _ _, hρ, _, θ, _, _, h₁, h₂ => by
    cases n with
    | direct E => exact absurd rfl (hn E)
    | plain => simp only [Term.subst, Term.shape, InstanceArgs.Lifts.shapes_subst has hρ θ h₁ h₂]
    | inst _ => simp only [Term.subst, Term.shape, InstanceArgs.Lifts.shapes_subst has hρ θ h₁ h₂]

/-- The arguments of an instance lifted by a lifting that lifts no variable, substituted, have the
shapes of the arguments, at the same nestings, where no variable has a position, on either side. -/
theorem InstanceArgs.Lifts.shapes_subst :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' →
      (∀ {a} (x : Var Δ a), ρ.motive x = none) →
      ∀ {Γ : Scope} (θ : Subst k Γ Δ) {νs : Nesting Shape.Motive Δ}
        {νs' : Nesting Shape.Motive Γ}, (∀ (a : Scope.Entry) (x : Var Δ a), νs x = .plain) →
        (∀ (a : Scope.Entry) (x : Var Γ a), νs' x = .plain) →
          (as.subst θ).shapes v lookup block @νs' ns = as.shapes v lookup block @νs ns
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .lifted has hB, hρ, _, θ, _, _, h₁, h₂ => by
    rw [InstanceArgs.subst, InstanceArgs.shapes, InstanceArgs.shapes,
      InstanceArgs.Lifts.shapes_subst has hρ θ h₁ h₂,
      Term.Lifts.shape_subst hB
        (Lifting.weaken_motive_eq_none (Lifting.liftN_motive_eq_none hρ _)) _
        (Nesting.liftN_plain _ h₁) (Nesting.liftN_plain _ h₂)]
  | _, _, _, _, _, _, _, _, _, _, .absent (a := a) (B := B) has _ hn, hρ, _, θ, νs, νs', h₁,
      h₂ => by
    have e₁ : (B.subst (Subst.liftN a.params.length θ)).shape v lookup block
        (Nesting.liftN a.params.length @νs') .plain = none :=
      Term.shape_eq_none_of_avoids fun x hx => absurd (Nesting.liftN_plain _ h₂ _ x) hx
    have e₂ : B.shape v lookup block (Nesting.liftN a.params.length @νs) .plain = none :=
      Term.shape_eq_none_of_avoids fun x hx => absurd (Nesting.liftN_plain _ h₁ _ x) hx
    rw [InstanceArgs.subst, InstanceArgs.shapes, InstanceArgs.shapes,
      InstanceArgs.Lifts.shapes_subst has hρ θ h₁ h₂, hn, e₁, e₂]

end


/-! ## Liftings Instantiated -/

/-- An abstraction lifted by a lifting that lifts no variable, under the variables of its telescope,
instantiated at arguments, has the shape of the abstraction, at the same nesting, where no variable
has a position. -/
theorem Term.Lifts.shape_instantiate_abstraction {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    (hρ : ∀ {a} (x : Var Γ a), ρ.motive x = none) {ps : List Parameter} {n : Nest Name}
    {e : Term k (.var :: Γ'.extend ps.length)} {A : Term k (Γ.extend ps.length)}
    {A' : Term k (.var :: Γ'.extend ps.length)} {m : Lifting.Result k}
    (h : Term.Lifts sig v (ρ.liftN ps.length).weaken n e A A' m) {νs : Nesting Shape.Motive Γ}
    (hνs : ∀ (a : Scope.Entry) (x : Var Γ a), νs x = .plain) (us : Args k Γ ps) :
    (A.instantiate us).shape v lookup block @νs n =
      A.shape v lookup block (Nesting.liftN ps.length @νs) n := by
  rw [Term.instantiate_eq_subst₀, Term.subst₀_eq_subst]
  exact h.shape_subst (Lifting.weaken_motive_eq_none (Lifting.liftN_motive_eq_none hρ _)) _
    (Nesting.liftN_plain _ hνs) hνs

namespace Lifting.Instantiates

variable {Γ' Γ Δ' Δ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ : Lifting k Δ' Δ}
  {ρ' : Lifting k Γ' Γ} {ν : Nesting Name Δ}

/-- The variables with a position of a lifting instantiated, under `n` new variables of the scopes
and in the scope extended by an entry, are lifted. -/
theorem isSome_liftN_weaken {νs : Nesting Shape.Motive Δ}
    (h : ∀ {a} (x : Var Δ a), νs x ≠ .plain → (ρ.motive x).isSome) (n : Nat) {e : Scope.Entry}
    {a : Scope.Entry} (z : Var (Δ.extend n) a) (hz : Nesting.liftN n @νs z ≠ .plain) :
    (((ρ.liftN n).weaken (e := e)).motive z).isSome := by
  obtain ⟨x, rfl, hx⟩ := Nesting.exists_of_liftN n z hz
  rw [show ((ρ.liftN n).weaken (e := e)).motive (x.weakenN n) =
    ((ρ.liftN n).motive (x.weakenN n)).map (Prod.map .succ id) from rfl, Option.isSome_map]
  exact Lifting.isSome_liftN_weakenN n ρ x (h x hx)

/-- What a substitution gives the variables lifted keeps its shape, at the nesting of the variable,
under `n` new variables of the scopes and in the scope extended by an entry, where no variable of
the scope of the substitution has a position. -/
theorem shape_liftN_weaken {νs : Nesting Shape.Motive Δ} {νs' : Nesting Shape.Motive Γ}
    (hνs' : ∀ (a : Scope.Entry) (x : Var Γ a), νs' x = .plain)
    (h : ∀ {a} (x : Var Δ a), (ρ.motive x).isSome →
      (θ x).shape v lookup block (Nesting.liftN a.params.length @νs') (ν x) = (νs x).motive)
    (n : Nat) {e : Scope.Entry} {a : Scope.Entry} (z : Var (Δ.extend n) a)
    (hz : (((ρ.liftN n).weaken (e := e)).motive z).isSome) :
    (Subst.liftN n θ z).shape v lookup block
        (Nesting.liftN a.params.length (Nesting.liftN n @νs')) (Nesting.liftN n @ν z) =
      (Nesting.liftN n @νs z).motive := by
  obtain ⟨x, rfl, hx⟩ := Lifting.isSome_of_liftN n ρ z (Lifting.isSome_of_weaken _ z hz)
  have hp : ∀ (b : Scope.Entry) (y : Var (Γ.extend a.params.length) b),
      Nesting.liftN a.params.length (Nesting.liftN n @νs') (Ren.liftN a.params.length
        (Ren.weakenN n) y) = Nesting.liftN a.params.length @νs' y := fun _ y =>
    (Nesting.liftN_plain _ (Nesting.liftN_plain _ hνs') _ _).trans
      (Nesting.liftN_plain _ hνs' _ y).symm
  rw [Subst.liftN_weakenN, Nesting.liftN_weakenN n ν x, Nesting.liftN_weakenN n νs x,
    Term.shape_rename _ hp]
  exact h x hx

end Lifting.Instantiates

mutual

-- ADE: none.
/-- A type lifted at no position, substituted by an instantiation of its lifting, has, at its
nesting, where the variables have the nestings of the instantiation, the shape of the type where
each variable lifted has the shape of what the instantiation gives it, at its nesting, and the
others none, when no variable of the scope of the instantiation has a position: the shape of a
variable lifted, applied to arguments, is that of the abstraction that the instantiation gives it,
which is lifted by a lifting that lifts no variable; the types lifted have shapes where the
variables have the shapes of their liftings, `hex`, so that the arguments with a position at the
nesting of the instance have shapes. -/
theorem Term.Lifts.shape_instantiate {block₀ : Name → Option Shape.Motive}
    (hex : ∀ {Ξ' Ξ : Scope} {ρ₀ : Lifting k Ξ' Ξ} {n₀ : Nest Name} {e₀ : Term k Ξ'}
          {B₀ : Term k Ξ} {B₀' : Term k Ξ'} {m₀ : Lifting.Result k},
          Term.Lifts sig v ρ₀ n₀ e₀ B₀ B₀' m₀ → ∀ {ν₀ : Nesting Shape.Motive Ξ}, ρ₀.Shapes @ν₀ →
            (∀ D b, ρ₀.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
              ∃ m₁, B₀.shape v lookup block @ν₀ n₀ = some m₁) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {n : Nest Name} → {e : Term k Δ'} → {A : Term k Δ} →
      {A' : Term k Δ'} → {m : Lifting.Result k} → Term.Lifts sig v ρ n e A A' m → n = .plain →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
      ∀ {νs : Nesting Shape.Motive Δ} {νs' : Nesting Shape.Motive Γ},
        (∀ {a} (x : Var Δ a), νs x ≠ .plain → (ρ.motive x).isSome) →
        (∀ (a : Scope.Entry) (x : Var Γ a), νs' x = .plain) →
        (∀ {a} (x : Var Δ a), (ρ.motive x).isSome →
          (θ x).shape v lookup block (Nesting.liftN a.params.length @νs') (ν x) = (νs x).motive) →
        (∀ D b, ρ'.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
          (A.subst θ).shape v lookup block @νs' (A.nest (fun _ => none) @ν) =
            A.shape v lookup block₀ @νs .plain
  | _, _, _, _, _, _, _, _, .var (x := x) (y := y) (m := m) (ts := ts) hx _, _, _, _, θ, _, _,
      ν, hI, νs, νs', _, hνs', hθ, _ => by
    obtain ⟨_, -, hL⟩ := hI.lifted x y m hx
    show ((θ x).instantiate (ts.subst θ)).shape v lookup block @νs' (ν x) = (νs x).motive
    rw [hL.shape_instantiate_abstraction hI.motive' hνs']
    exact hθ x (by rw [hx]; rfl)
  | _, _, _, _, _, _, _, _, .block _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hn
  | _, _, _, _, _, _, _, _, .inst (as := as) _ _ _ _ _ _ has _ _ _, hn, _, _, θ, _, _, ν, hI, νs,
      νs', hνs, hνs', hθ, hb => by
    subst hn
    have h := InstanceArgs.Lifts.shapes_instantiate (block₀ := block₀) hex has rfl hI hνs hνs' hθ
      hb
    rw [← InstanceArgs.shapes_ofArgs_args] at h
    simp only [Term.subst, Term.nest]
    have hne := Nest.ofArgs_ne_direct (as.nest (fun _ => none) @ν)
    generalize Nest.ofArgs _ = N at h hne ⊢
    cases N with
    | direct E => exact absurd rfl (hne E)
    | plain => simp only [Term.shape, Nest.args] at h ⊢; rw [h]
    | inst _ => simp only [Term.shape, Nest.args] at h ⊢; rw [h]

-- ADE: none.
/-- The arguments of an instance lifted at no position, substituted by an instantiation of their
lifting, have, at their nestings, the shapes of the arguments where each variable lifted has the
shape of what the instantiation gives it, at its nesting, and the others none, when no variable of
the scope of the instantiation has a position, and the types lifted have shapes, `hex`. -/
theorem InstanceArgs.Lifts.shapes_instantiate {block₀ : Name → Option Shape.Motive}
    (hex : ∀ {Ξ' Ξ : Scope} {ρ₀ : Lifting k Ξ' Ξ} {n₀ : Nest Name} {e₀ : Term k Ξ'}
          {B₀ : Term k Ξ} {B₀' : Term k Ξ'} {m₀ : Lifting.Result k},
          Term.Lifts sig v ρ₀ n₀ e₀ B₀ B₀' m₀ → ∀ {ν₀ : Nesting Shape.Motive Ξ}, ρ₀.Shapes @ν₀ →
            (∀ D b, ρ₀.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
              ∃ m₁, B₀.shape v lookup block @ν₀ n₀ = some m₁) :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {Ξ : Scope} →
      {as : InstanceArgs k Δ Ξ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Ξ' : Scope} →
      {as' : InstanceArgs k Δ' Ξ'} → InstanceArgs.Lifts sig v ρ ns as S ms as' → ns = [] →
      ∀ {Γ' Γ : Scope} {θ : Subst k Γ Δ} {θ' : Subst k Γ' Δ'} {ρ' : Lifting k Γ' Γ}
        {ν : Nesting Name Δ}, Lifting.Instantiates sig v θ θ' ρ ρ' @ν →
      ∀ {νs : Nesting Shape.Motive Δ} {νs' : Nesting Shape.Motive Γ},
        (∀ {a} (x : Var Δ a), νs x ≠ .plain → (ρ.motive x).isSome) →
        (∀ (a : Scope.Entry) (x : Var Γ a), νs' x = .plain) →
        (∀ {a} (x : Var Δ a), (ρ.motive x).isSome →
          (θ x).shape v lookup block (Nesting.liftN a.params.length @νs') (ν x) = (νs x).motive) →
        (∀ D b, ρ'.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
          (as.subst θ).shapes v lookup block @νs' (as.nest (fun _ => none) @ν) =
            as.shapes v lookup block₀ @νs []
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .lifted (a := a) (B := B) has hB, hns, _, _, θ, _, _, ν, hI, νs,
      νs', hνs, hνs', hθ, hb => by
    subst hns
    have hI' := (hI.liftN a.params.length).weaken (e := .var)
    have hb' := Lifting.blockShapes_liftN_weaken (block := block) a.params.length (e := .var) hb
    -- The argument instantiated is lifted at its nesting by a lifting that lifts no variable, so
    -- that it has a shape there, and so does the argument where the variables carry their shapes.
    obtain ⟨m₁, hm₁⟩ := hex (Term.Lifts.instantiate hB rfl hI')
      (ν₀ := Nesting.liftN a.params.length @νs')
      (fun x => .inl ⟨hI'.motive' x, Nesting.liftN_plain _ hνs' _ x⟩) hb'
    have he := Term.Lifts.shape_instantiate (block₀ := block₀) hex hB rfl hI'
      (Lifting.Instantiates.isSome_liftN_weaken hνs _) (Nesting.liftN_plain _ hνs')
      (Lifting.Instantiates.shape_liftN_weaken hνs' hθ _) hb'
    have he' : B.shape v lookup block₀ (Nesting.liftN a.params.length @νs) .plain = some m₁ :=
      he.symm.trans hm₁
    rw [InstanceArgs.subst, InstanceArgs.nest, InstanceArgs.shapes, InstanceArgs.shapes]
    simp only [List.tail_cons, List.headD_cons, List.tail_nil, List.headD_nil]
    rw [InstanceArgs.Lifts.shapes_instantiate (block₀ := block₀) hex has rfl hI hνs hνs' hθ hb]
    erw [hm₁, he']
    cases InstanceArgs.shapes v lookup block₀ @νs [] _ <;> rfl
  | _, _, _, _, _, _, _, _, _, _, .absent (a := a) (B := B) has hB _, hns, _, _, θ, _, _, ν, hI,
      νs, νs', hνs, hνs', hθ, hb => by
    subst hns
    have hN := hI.liftN a.params.length
    have hp : B.nest (fun _ => none) (Nesting.liftN a.params.length @ν) = .plain :=
      Term.nest_eq_plain_of_avoids fun z hz => hB z (by
        cases hm : (Lifting.liftN a.params.length _).motive z with
        | none => exact absurd (hN.plain z hm) hz
        | some _ => rfl)
    have e₁ : (B.subst (Subst.liftN a.params.length θ)).shape v lookup block
        (Nesting.liftN a.params.length @νs') .plain = none :=
      Term.shape_eq_none_of_avoids fun x hx => absurd (Nesting.liftN_plain _ hνs' _ x) hx
    have e₂ : B.shape v lookup block₀ (Nesting.liftN a.params.length @νs) .plain = none :=
      Term.shape_eq_none_of_avoids fun x hx =>
        hB x (Lifting.isSome_of_weaken _ x
          (Lifting.Instantiates.isSome_liftN_weaken (e := .var) hνs _ x hx))
    rw [InstanceArgs.subst, InstanceArgs.nest, InstanceArgs.shapes, InstanceArgs.shapes,
      List.tail_cons, List.headD_cons, List.tail_nil, List.headD_nil, hp,
      InstanceArgs.Lifts.shapes_instantiate (block₀ := block₀) hex has rfl hI hνs hνs' hθ hb, e₁, e₂]

end

/-! ## Shapes of the Arguments of an Instance -/

-- ADE: none.
/-- The shapes of the arguments of an instance followed by an argument, when they are given, are
those of the arguments before it, followed by the shape of the argument at its position when it
has one. -/
theorem InstanceArgs.shapes_snoc_eq_some {Γ Δ : Scope} {ν : Nesting Shape.Motive Γ}
    {e : Scope.Entry} {as : InstanceArgs k Γ Δ} {B : Term k (Γ.extend e.params.length)}
    {ns : List (Nest Name)} {l : List (Nat × Shape.Motive)}
    (h : (InstanceArgs.snoc (e := e) as B).shapes v lookup block @ν ns = some l) :
    ∃ l₀, as.shapes v lookup block @ν ns.tail = some l₀ ∧
      l = l₀ ++ ((B.shape v lookup block (Nesting.liftN _ @ν) (ns.headD .plain)).map
        fun m => (Δ.length, m)).toList := by
  rw [InstanceArgs.shapes] at h
  cases ha : as.shapes v lookup block @ν ns.tail with
  | none => rw [ha] at h; exact nomatch h
  | some l₀ =>
    refine ⟨l₀, rfl, ?_⟩
    rw [ha] at h
    cases hB : B.shape v lookup block (Nesting.liftN _ @ν) (ns.headD .plain) with
    | some m =>
      rw [hB] at h
      exact (Option.some.inj h).symm
    | none =>
      rw [hB] at h
      simp only at h
      split at h
      · simpa using (Option.some.inj h).symm
      · exact nomatch h

/-- The shapes of the arguments of an instance are at positions of its parameters. -/
theorem InstanceArgs.lt_of_mem_shapes {Γ : Scope} {ν : Nesting Shape.Motive Γ} :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → (ns : List (Nest Name)) →
      {l : List (Nat × Shape.Motive)} → as.shapes v lookup block @ν ns = some l →
        {y : Nat × Shape.Motive} → y ∈ l → y.1 < Δ.length
  | _, .nil, _, _, h, _, hy => by
    cases Option.some.inj h
    exact nomatch hy
  | _, .snoc (Δ := Δ) as B, ns, _, h, y, hy => by
    obtain ⟨l₀, h₀, rfl⟩ := InstanceArgs.shapes_snoc_eq_some h
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact Nat.lt_succ_of_lt (InstanceArgs.lt_of_mem_shapes as ns.tail h₀ hy)
    · cases hB : B.shape v lookup block (Nesting.liftN _ @ν) (ns.headD .plain) with
      | none => rw [hB] at hy; exact nomatch hy
      | some m =>
        rw [hB] at hy
        cases List.mem_singleton.1 hy
        exact Nat.lt_succ_self Δ.length

/-- A key other than all the keys of a list of pairs has no value in it. -/
theorem List.lookup_eq_none_of_ne {β : Type} {n : Nat} :
    (l : List (Nat × β)) → (∀ y ∈ l, y.1 ≠ n) → l.lookup n = none
  | [], _ => rfl
  | (a, b) :: l, h => by
    rw [List.lookup_cons, beq_eq_false_iff_ne.2 (h (a, b) (List.mem_cons_self ..)).symm]
    exact List.lookup_eq_none_of_ne l fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- The shape that the arguments of an instance give the parameter at the level of a variable,
when they have shapes, is the shape of the argument of this variable, at its nesting. -/
theorem InstanceArgs.lookup_shapes {Γ : Scope} {ν : Nesting Shape.Motive Γ} :
    {Δ : Scope} → (as : InstanceArgs k Γ Δ) → (ns : List (Nest Name)) →
      {l : List (Nat × Shape.Motive)} → as.shapes v lookup block @ν ns = some l →
      {a : Scope.Entry} → (x : Var Δ a) → l.lookup x.level =
        (as.toSubst x).shape v lookup block (Nesting.liftN a.params.length @ν)
          (Nesting.ofArgs ns x)
  | _, .snoc (Δ := Δ) (e := e) as B, ns, _, h, _, .zero => by
    obtain ⟨l₀, h₀, rfl⟩ := InstanceArgs.shapes_snoc_eq_some h
    have hn : Nesting.ofArgs (Δ := e :: Δ) ns (.zero (Γ := Δ) (e := e)) = ns.headD .plain := by
      cases ns <;> rfl
    show (l₀ ++ _).lookup Δ.length = B.shape v lookup block _ _
    rw [List.lookup_append, List.lookup_eq_none_of_ne _
      fun y hy => Nat.ne_of_lt (InstanceArgs.lt_of_mem_shapes as ns.tail h₀ hy), Option.none_or, hn]
    cases B.shape v lookup block (Nesting.liftN _ @ν) (ns.headD .plain) with
    | none => rfl
    | some m =>
      show List.lookup Δ.length [(Δ.length, m)] = some m
      rw [List.lookup_cons, beq_iff_eq.2 rfl]
  | _, .snoc (Δ := Δ) (e := e) as B, ns, _, h, _, .succ y => by
    obtain ⟨l₀, h₀, rfl⟩ := InstanceArgs.shapes_snoc_eq_some h
    have h₀' : ∀ {Δ' : Scope} {a' : Scope.Entry} (z : Var Δ' a'),
        Nesting.ofArgs (α := Name) [] z = .plain := fun z => by cases z <;> rfl
    have hn : Nesting.ofArgs (Δ := e :: Δ) ns (y.succ (e' := e)) = Nesting.ofArgs ns.tail y := by
      cases ns with
      | nil => exact (h₀' _).trans (h₀' y).symm
      | cons => rfl
    show (l₀ ++ _).lookup y.level = (as.toSubst y).shape v lookup block _ _
    rw [List.lookup_append, hn, ← InstanceArgs.lookup_shapes as ns.tail h₀ y]
    cases l₀.lookup y.level with
    | some _ => rfl
    | none =>
      rw [Option.none_or]
      exact List.lookup_eq_none_of_ne _ fun z hz => by
        cases hB : B.shape v lookup block (Nesting.liftN _ @ν) (ns.headD .plain) with
        | none => rw [hB] at hz; exact nomatch hz
        | some _ =>
          rw [hB] at hz
          cases List.mem_singleton.1 hz
          exact Nat.ne_of_gt (Var.level_lt y)

/-! ## Shapes of the Results of the Destructors at an Instance -/

-- ADE: none.
/-- The result of a destructor `d` of the codata type `D`, at a closed instance `D.{s̄; l̄; p̄} ā`
lifted at a term `t`, at the observations of `t` by the destructors before `d` and at closed
arguments of `d`, has, at its nesting, where no variable has a position, the shape of the result of
`d` where the parameters have the shapes of the arguments `ā`: the lifting of `D` lifts the result
of `d` at the parameters lifted, which the instance instantiates with the arguments lifted, whose
shapes are those of the parameters, and the substitution of the destructors before `d` by
observations keeps the nestings, when the types lifted have shapes, `hex`, and the types of the
block that the lifting of the instance gives have the shapes of their motives. -/
theorem TypeDeclaration.Lifts.shape_result {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hsig : sig.Distinct) (hT : sig.HasCodataType D decl T) (hL : decl.Lifts sig D S body)
    {ρ : Lifting 0 [] []} {qs : List Quality} {ls : List (Level 0)}
    {ms : List (Lifting.Result 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hq' : (qs ++ [v.quality]).length = decl.sorts + 1)
    (hl' : (ls ++ ms.map (·.level)).length = decl.levels + S.length)
    (hp' : (v.grades ps ms).length = decl.liftingGrades S) {nsA : List (Nest Name)}
    {as : InstanceArgs 0 [] decl.scope} {as' : InstanceArgs 0 [] (decl.scope.lifted S)}
    (has : InstanceArgs.Lifts sig v ρ nsA as S ms as') (t : Term 0 []) {ms' : List Shape.Motive}
    (hms : as.shapes v lookup block Nesting.plain nsA = some (S.zip ms')) {d : Name}
    {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps₁}
    {B : Term decl.levels (Ξ.extend ps₁.length)} {ψ : ResultOwnership Grade ps₁.length}
    (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) {p' q' ς' : Grade}
    {ps₁' : List Parameter} {Ξ' : Scope} {Θ' : Telescope (decl.levels + S.length) Ξ' ps₁'}
    {B' : Term (decl.levels + S.length) (Ξ'.extend ps₁'.length)}
    {ψ' : ResultOwnership Grade ps₁'.length}
    (hd' : (body (.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp')).Pos d p' q' ς' Ξ' Θ'
      B' ψ')
    (ts : Args 0 [] ps₁)
    (hex : ∀ {Ξ' Ξ : Scope} {ρ₀ : Lifting 0 Ξ' Ξ} {n₀ : Nest Name} {e₀ : Term 0 Ξ'}
      {B₀ : Term 0 Ξ} {B₀' : Term 0 Ξ'} {m₀ : Lifting.Result 0},
      Term.Lifts sig v ρ₀ n₀ e₀ B₀ B₀' m₀ → ∀ {ν₀ : Nesting Shape.Motive Ξ}, ρ₀.Shapes @ν₀ →
        (∀ D b, ρ₀.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
          ∃ m₁, B₀.shape v lookup block @ν₀ n₀ = some m₁)
    (hb : ∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) :
    (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN ps₁.length (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))).subst
        ts.toSubst).shape v lookup block Nesting.plain
        (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs nsA)))) =
      B.shape v lookup (fun _ => none)
        (Nesting.liftN ps₁.length (hd.nesting (Shape.motives (S.zip ms')))) .plain := by
  have hρ : ∀ {a} (x : Var [] a), ρ.motive x = none := fun x => nomatch x
  have h₀ : ∀ (a : Scope.Entry) (x : Var [] a), (Nesting.plain : Nesting Shape.Motive []) x =
      .plain := fun _ _ => rfl
  -- A term over the arguments of an entry, at a nesting none of whose variables has a position,
  -- has no shape there.
  have hnone : ∀ {n : Nat} (u : Term 0 (Scope.extend [] n)),
      u.shape v lookup block (Nesting.liftN n Nesting.plain) .plain = none := fun u =>
    Term.shape_eq_none_of_avoids fun x hx => (hx (Nesting.liftN_plain _ h₀ _ x)).elim
  obtain ⟨_, _, ρ₁, _, A₀, _, hL₁, hI, -, hnest, ⟨β, hA₀, hN⟩, -, hA, -⟩ :=
    hL.result hsig hT hρ hq hl hp hq' hl' hp' has t hd hd' (fun _ _ => .sort ⟨.prop, .zero⟩)
  obtain ⟨_, _, _, hLo⟩ :=
    hL.observation hsig hT hρ hq hl hp hq' hl' hp' has t hd hd' (fun _ _ => .sort ⟨.prop, .zero⟩)
  have hid : ∀ {a} (x : Var [] a), ρ.ren x = x := fun x => nomatch x
  rw [Term.rename_id_of (Ren.liftN_id_of _ hid)] at hLo
  -- The closed arguments do not change the shape, the lifting lifting no variable.
  rw [hLo.shape_subst (Lifting.liftN_motive_eq_none hρ _) ts.toSubst
    (νs := Nesting.liftN ps₁.length Nesting.plain) (Nesting.liftN_plain _ h₀) h₀,
    ← hA, ← hnest]
  -- The shape of a variable lifted is that of its argument lifted.
  have hθ : ∀ {a : Scope.Entry} (y : Var (.var :: decl.scope) a), (ρ₁.motive y).isSome →
      ((InstanceArgs.snoc (e := .var) as t).toSubst y).shape v lookup block
          (Nesting.liftN a.params.length Nesting.plain)
          (Nesting.lift (Nesting.ofArgs nsA) y) =
        (Nesting.lift (Shape.motives (S.zip ms')) y).motive := fun y _ => by
    cases y with
    | zero => exact hnone (n := 0) t
    | succ z =>
      show (as.toSubst z).shape v lookup block _ (Nesting.ofArgs nsA z) =
        (Shape.motives (S.zip ms') z).motive
      rw [← InstanceArgs.lookup_shapes as nsA hms z]
      unfold Shape.motives
      cases (S.zip ms').lookup z.level <;> rfl
  have hbN : ∀ D b, (ρ.liftN ps₁.length).block D = some b →
      ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩ := fun D _ hD => by
    obtain ⟨b₀, hb₀, he⟩ := Lifting.liftN_block_ownership ps₁.length hD
    obtain ⟨Υ, hΥ⟩ := hb D b₀ hb₀
    exact ⟨Υ, he ▸ hΥ⟩
  refine (hL₁.shape_instantiate (block₀ := fun _ => none) hex rfl (hI.liftN ps₁.length)
    (νs := Nesting.liftN ps₁.length (Nesting.lift (Shape.motives (S.zip ms')))) ?_
    (Nesting.liftN_plain _ h₀) ?_ hbN).trans ?_
  · intro a x hx
    obtain ⟨y, rfl, hy⟩ := Nesting.exists_of_liftN ps₁.length x hx
    refine Lifting.isSome_liftN_weakenN ps₁.length ρ₁ y ?_
    cases y with
    | zero => exact absurd rfl hy
    | succ z =>
      cases hm : ρ₁.motive (.succ z) with
      | some _ => rfl
      | none =>
        have hz : Nesting.ofArgs nsA z = .plain := hI.plain (.succ z) hm
        have hs : (S.zip ms').lookup z.level ≠ none := fun h => hy (by
          show Shape.motives (S.zip ms') z = .plain
          unfold Shape.motives
          rw [h])
        rw [InstanceArgs.lookup_shapes as nsA hms z, hz] at hs
        exact absurd (hnone _) hs
  · intro a x hx
    obtain ⟨y, rfl, hy⟩ := Lifting.isSome_of_liftN ps₁.length ρ₁ x hx
    have hp₀ : ∀ (b : Scope.Entry) (z : Var (Scope.extend [] a.params.length) b),
        Nesting.liftN a.params.length (Nesting.liftN ps₁.length Nesting.plain)
          (Ren.liftN a.params.length (Ren.weakenN ps₁.length) z) =
        Nesting.liftN a.params.length Nesting.plain z := fun _ z =>
      (Nesting.liftN_plain _ (Nesting.liftN_plain _ h₀) _ _).trans
        (Nesting.liftN_plain _ h₀ _ z).symm
    rw [Subst.liftN_weakenN, Nesting.liftN_weakenN, Nesting.liftN_weakenN, Term.shape_rename _ hp₀]
    exact hθ y hy
  · rw [hA₀, Term.shape_substLevels, Term.shape_subst_of (Subst.Nests.liftN ps₁.length (@hN _ _)),
      Term.shape_substLevels]

end Sic.Core
