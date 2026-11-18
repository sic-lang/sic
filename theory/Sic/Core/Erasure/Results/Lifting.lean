module

public import Sic.Core.Erasure.Results.Substitution
public import Sic.Core.Lifting.Extension
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Shape
import Sic.Core.Lifting.Substitution
import Sic.Core.Substitution.Closed
import Sic.Core.Syntax.Signature

/-!
# Shapes of the Types Lifted

The shape of annex 16 of RFC 36 follows the lifting of annex 20: a type lifted has a shape, which
gives the recursive result the factor and the ownership that the lifting gives it, in a signature
whose names are distinct and that declares each lifting after the destructors that it lifts.

The shape of an instance of a lifting is that of the destructors of the type lifted, whose results
are lifted by the liftings declared before, which have shapes: the proof follows the signature,
entry by entry, as the shape does.
The shape gives a lifting the meet of the grades of its destructors times the factors of their
results: the proof builds the factor of the destructors of the lifting from their shape, and the
factor of an instance of a lifting is one.
The declaration lifts the destructors at its parameters, where the parameters lifted have their
motives, and the shape reads them at the nestings of the parameters, whose positions hold the shapes
of the arguments lifted: the substitution of the parameters by those of the lifting, and of the
destructors before a destructor by the observations of the term lifted, keeps the shapes.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {sig sig₁ : Signature} {v : Lifting.Variables}

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

/-! ## Shapes of the Types Lifted -/

/-- The shapes of the liftings that the signature `Σ₁` declares follow their factors in the
signature `Σ`: an instance of such a lifting, whose motives have shapes that carry their factors and
their ownerships, has a shape, of its factor. -/
def Signature.LiftingsHaveShapes (sig₁ sig : Signature) : Prop :=
  ∀ (k : Nat) (v : Lifting.Variables) {decl : TypeDeclaration} {D : Name} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns},
    .typeDeclaration decl ∈ sig → D ∈ decl.names →
    .typeDeclaration (decl.lifting D S ns body) ∈ sig₁ →
    ∀ {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {qs : List Quality} {ls : List (Level k)}
      {ps : List Grade} {ms : List (Lifting.Result k)} {Δ : Scope} {as : InstanceArgs k Γ' Δ}
      {π : Grade} {ms' : List Shape.Motive},
      qs.length = decl.sorts → ps.length = decl.grades → S.Nodup → ms.length = S.length →
      Shape.Motive.AllOf ms' ms →
      Term.Factor sig ρ (.inst (Lifting.name D S) (qs ++ [v.quality]) ls (v.grades ps ms) as) π →
        ∃ σ, sig.shapes v sig₁ D qs ps (S.zip ms') = some (σ, π)

/-- The shape of an instance of a declared type, at a nesting that is not a position, whose
arguments lifted have shapes: that of the lifting at them. -/
theorem Term.shape_inst {lookup : Shape.Lookup} {block : Name → Option Shape.Motive} {Γ : Scope}
    {ν : Nesting Shape.Motive Γ} {n : Nest Name} (hn : ∀ E, n ≠ .direct E) {Δ : Scope} {D : Name}
    {qs : List Quality} {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ}
    {l : List (Nat × Shape.Motive)} (h : as.shapes v lookup block @ν n.args = l) (hl : l ≠ []) :
    (Term.inst D qs ls ps as).shape v lookup block @ν n =
      (lookup D qs ps l).map fun σ => ⟨.lifting σ.1, σ.2, .linearLinear⟩ := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases n with
  | direct E => exact absurd rfl (hn E)
  | plain => simp only [Term.shape, h]
  | inst ns => simp only [Term.shape, h]

mutual

-- ADE: none.
/-- A type lifted, in a signature `Σ₁` whose liftings have shapes in `Σ`, has a shape, which carries
the factor and the ownership of the recursive result that it is the type of, where the shapes of the
variables follow the lifting, and those of the types of the block carry their ownerships. -/
theorem Term.Lifts.shape
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveShapes sig₁ sig) {block : Name → Option Shape.Motive} :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {n : Nest Name} → {e : Term k Γ'} → {A : Term k Γ} →
      {A' : Term k Γ'} → {m : Lifting.Result k} → Term.Lifts sig₁ v ρ n e A A' m →
      ∀ {ν : Nesting Shape.Motive Γ}, ρ.Shapes @ν →
        (∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
          ∃ m', A.shape v (sig.shapes v sig₁) block @ν n = some m' ∧ m'.Of m
  | _, _, _, _, _, _, _, _, .var (x := x) hx _, ν, hν, _ => by
    rcases hν x with ⟨h₁, -⟩ | ⟨y, m, m', h₁, h₂, h₃⟩
    · cases h₁.symm.trans hx
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (h₁.symm.trans hx))
      exact ⟨m', by show (ν x).motive = _; rw [h₂]; rfl, h₃⟩
  | _, _, _, _, _, _, _, _, .block (D := D) hD, _, _, hb => by
    obtain ⟨Υ, hΥ⟩ := hb D _ hD
    exact ⟨_, hΥ, rfl, rfl⟩
  | _, _, _, n, _, _, _, _, .inst (S := S) h hD hn hq hl hp has hS hL hπ, ν, hν, hb => by
    obtain ⟨ms', hms', hms⟩ := has.shapes hsub hM hν hb
    have hl' : S.zip ms' ≠ [] := by
      intro he
      have := congrArg List.length he
      rw [List.length_zip, hms.length_eq, has.length_eq, Nat.min_self] at this
      exact hS (List.eq_nil_of_length_eq_zero this)
    obtain ⟨σ, hσ⟩ := hM _ v (hsub _ h) hD hL hq hp has.nodup
      has.length_eq hms (hπ.ofTypeDeclarations hsub)
    refine ⟨⟨.lifting σ, _, .linearLinear⟩, ?_, rfl, rfl⟩
    rw [Term.shape_inst hn hms' hl', hσ]
    rfl

-- ADE: none.
/-- The arguments of an instance lifted, in a signature `Σ₁` whose liftings have shapes in `Σ`,
have shapes at the positions of the arguments lifted, which carry the factors and the ownerships of
the recursive results that these are the types of. -/
theorem InstanceArgs.Lifts.shapes
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveShapes sig₁ sig) {block : Name → Option Shape.Motive} :
    {Γ' Γ : Scope} → {ρ : Lifting k Γ' Γ} → {ns : List (Nest Name)} → {Δ : Scope} →
      {as : InstanceArgs k Γ Δ} → {S : List Nat} → {ms : List (Lifting.Result k)} → {Δ' : Scope} →
      {as' : InstanceArgs k Γ' Δ'} → InstanceArgs.Lifts sig₁ v ρ ns as S ms as' →
      ∀ {ν : Nesting Shape.Motive Γ}, ρ.Shapes @ν →
        (∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) →
          ∃ ms', as.shapes v (sig.shapes v sig₁) block @ν ns = S.zip ms' ∧
            Shape.Motive.AllOf ms' ms
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _ => ⟨[], rfl, rfl⟩
  | _, _, ρ, _, _, _, _, _, _, _, .lifted (a := a) has hB, ν, hν, hb => by
    obtain ⟨ms', hms', hms⟩ := has.shapes hsub hM hν hb
    obtain ⟨m', hm', hm⟩ := hB.shape hsub hM
      (Lifting.Shapes.weaken (Lifting.Shapes.liftN a.params.length hν)) (fun D b hD => by
        obtain ⟨b₁, hb₁, rfl⟩ := Option.map_eq_some_iff.1 hD
        obtain ⟨b₀, hb₀, he⟩ := Lifting.liftN_block_ownership a.params.length hb₁
        obtain ⟨Υ, hΥ⟩ := hb D b₀ hb₀
        exact ⟨Υ, he ▸ hΥ⟩)
    refine ⟨ms' ++ [m'], ?_, by
      simp only [Shape.Motive.AllOf, List.map_append, List.map_cons, List.map_nil] at hms ⊢
      rw [hms, hm.1, hm.2]⟩
    rw [InstanceArgs.shapes, hms', hm', List.zip_append (by rw [hms.length_eq, has.length_eq])]
    rfl
  | _, _, ρ, _, _, _, _, _, _, _, .absent (a := a) has hB hn, ν, hν, hb => by
    obtain ⟨ms', hms', hms⟩ := has.shapes hsub hM hν hb
    refine ⟨ms', ?_, hms⟩
    rw [InstanceArgs.shapes, hms', hn, Term.shape_eq_none_of_avoids (fun x hx =>
      hB x (Lifting.Shapes.isSome (Lifting.Shapes.liftN a.params.length hν) x hx))]
    simp only [Option.map_none, Option.toList_none, List.append_nil]

end

/-! ## Shapes of the Destructors Lifted -/

/-- A result of a destructor of a lifting has its factor at the parameters of the lifting cast to an
equal number. -/
theorem Term.Factor.cast_liftN {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n₁ n₂ : Nat} (h : n₁ = n₂)
    {B : Term k (Γ'.extend n₁)} {π : Grade} (hB : Term.Factor sig (ρ.liftN n₁) B π) :
    Term.Factor sig (ρ.liftN n₂) (h ▸ B) π := by
  subst h
  exact hB

-- ADE: none.
/-- The destructors of a codata type lifted, in a signature `Σ₁` whose liftings have shapes in `Σ`,
have the factor that their shape gives, where the substitution of the destructors before each by
observations keeps the shapes, which follow the lifting. -/
theorem Destructors.Lifts.shape_factor
    (hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig)
    (hM : Signature.LiftingsHaveShapes sig₁ sig) (D : Name) {Γ₀ : Scope} {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)}
    (ho : ∀ d ps', ∃ (Ξ : Scope) (D' : Name) (qs : List Quality) (ls : List (Level k))
      (ps : List Grade) (as : InstanceArgs k (Γ₀.extend ps'.length) Ξ)
      (t : Term k (Γ₀.extend ps'.length)) (d' : Name) (bs : Terms k (Γ₀.extend ps'.length)),
      o d ps' = .obs D' qs ls ps as t d' bs) :
    {Γ' : Scope} → {ρ : Lifting k Γ' Γ₀} → {Ξ : Scope} → {θ : Subst k Γ₀ Ξ} → {ns : List Name} →
      {ds : Destructors k Ξ ns} → {ns' : List Name} → {ds' : Destructors k Γ' ns'} →
      Destructors.Lifts sig₁ v κ o ρ @θ ds ds' →
      ∀ {ν : Nesting Shape.Motive Ξ} {ν₀ : Nesting Shape.Motive Γ₀}, Subst.Nests θ @ν @ν₀ →
        ρ.Shapes @ν₀ → (∀ E, ρ.block E = none) →
          Destructors.Factor sig ρ ds' (ds.shape sig v (sig.shapes v sig₁) D @ν).2
  | _, _, _, _, _, _, _, _, .nil, _, _, _, _, _ => .nil
  | _, ρ, _, θ, _, _, _, _, .lifted (d := d) (ps := ps) (ψ := ψ) hB _ hds, ν, ν₀, hθ, hρ, hb => by
    obtain ⟨m', hm', hm⟩ := hB.shape hsub hM (block := fun _ => none)
      (Lifting.Shapes.liftN ps.length hρ) (fun E b h => by
        rw [Lifting.liftN_block_none ps.length hb E] at h
        cases h)
    rw [Term.shape_subst_of (hθ.liftN ps.length)] at hm'
    obtain ⟨Ξ', D', qs, ls, ps', as, t, d', bs, he⟩ := ho d ps
    have hθ' : Subst.Nests (θ.snoc (e := .secondOrder ps ψ) (o d ps)) (Nesting.lift @ν) @ν₀ := by
      rw [he]
      exact hθ.snocObs (e := .secondOrder ps ψ) D' qs ls ps' as t d' bs
    simp only [Destructors.shape, hm']
    rw [hm.1]
    exact .cons (Term.Factor.cast_liftN _
        ((Term.Lifts.factor (Lifting.liftN_block_none ps.length hb) hB).ofTypeDeclarations hsub))
      (hds.shape_factor hsub hM D ho hθ' (Lifting.Shapes.weaken hρ)
        (Lifting.weaken_block_none hb))
  | _, ρ, _, θ, _, _, _, _, .absent (d := d) (ps := ps) (ψ := ψ) (B := B) hB hds, ν, ν₀, hθ, hρ, hb => by
    have hn : B.shape v (sig.shapes v sig₁) (fun _ => none)
        (Nesting.liftN ps.length @ν) .plain = none := by
      rw [← Term.shape_subst_of (hθ.liftN ps.length)]
      exact Term.shape_eq_none_of_avoids fun x hx =>
        hB x (Lifting.Shapes.isSome (Lifting.Shapes.liftN ps.length hρ) x hx)
    obtain ⟨Ξ', D', qs, ls, ps', as, t, d', bs, he⟩ := ho d ps
    have hθ' : Subst.Nests (θ.snoc (e := .secondOrder ps ψ) (o d ps)) (Nesting.lift @ν) @ν₀ := by
      rw [he]
      exact hθ.snocObs (e := .secondOrder ps ψ) D' qs ls ps' as t d' bs
    simp only [Destructors.shape, hn]
    exact hds.shape_factor hsub hM D ho hθ' hρ hb

/-! ## Shapes of the Parameters of a Lifting -/

/-- The lifting of parameters lifts the parameters at the positions of `S`, each with the result of
its position. -/
theorem Lifting.base_motive_map (S : List Nat) (mv : Nat → Lifting.Result k) :
    (Δ : Scope) → ∀ {a : Scope.Entry} (x : Var Δ a),
      ((Lifting.base S mv Δ).motive x).map (·.2) = if x.level ∈ S then some (mv x.level) else none
  | e :: Δ, _, x => by
    show ((Lifting.cons (e := e) (mv Δ.length) (decide (Δ.length ∈ S))
      (Lifting.base S mv Δ)).motive x).map (·.2) = _
    cases hb : decide (Δ.length ∈ S) with
    | true =>
      cases x with
      | zero =>
        have hi : Δ.length ∈ S := of_decide_eq_true hb
        show some (mv Δ.length) = if Δ.length ∈ S then some (mv Δ.length) else none
        simp only [hi, ↓reduceIte]
      | succ x =>
        refine Eq.trans ?_ (Lifting.base_motive_map S mv Δ x)
        show Option.map _ (Option.map _ ((Lifting.base S mv Δ).motive x)) = _
        cases (Lifting.base S mv Δ).motive x <;> rfl
    | false =>
      cases x with
      | zero =>
        have hi : Δ.length ∉ S := of_decide_eq_false hb
        show none = if Δ.length ∈ S then _ else _
        simp only [hi, ↓reduceIte]
      | succ x =>
        refine Eq.trans ?_ (Lifting.base_motive_map S mv Δ x)
        show Option.map _ (Option.map _ ((Lifting.base S mv Δ).motive x)) = _
        cases (Lifting.base S mv Δ).motive x <;> rfl

/-- The shape of the position `S[j]` among positions and shapes paired is the shape at `j`, the
positions being distinct. -/
theorem _root_.List.lookup_zip_getElem {β : Type} :
    {S : List Nat} → {ms : List β} → S.Nodup → (j : Nat) → (h₁ : j < S.length) →
      (h₂ : j < ms.length) → (S.zip ms).lookup S[j] = some ms[j]
  | i :: S, m :: ms, _, 0, _, _ => by
    rw [List.zip_cons_cons, List.getElem_cons_zero, List.getElem_cons_zero, List.lookup,
      show (i == i) = true from decide_eq_true rfl]
  | i :: S, m :: ms, hS, j + 1, h₁, h₂ => by
    have hi : (S[j]'(Nat.lt_of_succ_lt_succ h₁) == i) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      exact (List.nodup_cons.1 hS).1 (he ▸ List.getElem_mem _)
    rw [List.zip_cons_cons, List.getElem_cons_succ, List.getElem_cons_succ, List.lookup, hi]
    exact List.lookup_zip_getElem (List.nodup_cons.1 hS).2 j _ _

/-- A position that is not among positions paired with shapes has no shape. -/
theorem _root_.List.lookup_zip_eq_none {β : Type} {i : Nat} :
    {S : List Nat} → {ms : List β} → i ∉ S → (S.zip ms).lookup i = none
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | i' :: S, _ :: ms, h => by
    have hi : (i == i') = false := beq_eq_false_iff_ne.2 fun he => h (he ▸ List.mem_cons_self)
    rw [List.zip_cons_cons, List.lookup, hi]
    exact List.lookup_zip_eq_none fun h' => h (List.mem_cons_of_mem _ h')

/-- The shapes of the parameters of a type declaration, whose parameters at distinct positions are
lifted with shapes that carry the factors and the ownerships of their motives, follow the lifting
of these parameters. -/
theorem Lifting.base_shapes {S : List Nat} (hS : S.Nodup) {mv : Nat → Lifting.Result k}
    {ms' : List Shape.Motive} (hl : ms'.length = S.length)
    (hmv : ∀ j (h₁ : j < S.length) (h₂ : j < ms'.length), (ms'[j]).Of (mv S[j])) (Δ : Scope) :
    (Lifting.base S mv Δ).Shapes (Shape.motives (S.zip ms')) := by
  intro a x
  have hx := Lifting.base_motive_map S mv Δ x
  by_cases hi : x.level ∈ S
  · simp only [hi, ↓reduceIte] at hx
    obtain ⟨⟨y, m⟩, hy, he⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hi
    refine .inr ⟨y, m, ms'[j]'(hl ▸ hj), hy, ?_, ?_⟩
    · show (match (S.zip ms').lookup x.level with
        | some m => Nest.direct m
        | none => .plain) = _
      rw [← hjx, List.lookup_zip_getElem hS j hj (hl ▸ hj)]
    · have hm : m = mv S[j] := by rw [hjx]; exact he
      rw [hm]
      exact hmv j hj (hl ▸ hj)
  · simp only [hi, ↓reduceIte] at hx
    refine .inl ⟨Option.map_eq_none_iff.1 hx, ?_⟩
    show (match (S.zip ms').lookup x.level with
      | some m => Nest.direct m
      | none => .plain) = _
    rw [List.lookup_zip_eq_none hi]

/-! ## Signatures Whose Liftings Have Shapes -/

/-- The entries of a suffix of a signature whose names are distinct have distinct names. -/
theorem Signature.Distinct.suffix {sig₂ : Signature} :
    (pre : Signature) → (pre ++ sig₂).Distinct → sig₂.Distinct
  | [], h => h
  | _ :: pre, h => Signature.Distinct.suffix pre h.1

/-- In a signature whose names are distinct, the first value that `f` gives an entry is the value
that it gives the entry that has the name `n`, when `f` gives none to the entries without it. -/
theorem Signature.Distinct.findSome?_eq {β : Type} {f : Entry → Option β} {n : Name} :
    {sig : Signature} → sig.Distinct → {e₀ : Entry} → e₀ ∈ sig → n ∈ e₀.names →
      (∀ e ∈ sig, (f e).isSome → n ∈ e.names) → sig.findSome? f = f e₀
  | [], _, _, h, _, _ => nomatch h
  | e :: sig, ⟨hd, _, hfresh, _⟩, e₀, he₀, hn₀, hf => by
    rcases List.mem_cons.1 he₀ with rfl | he₀'
    · cases hfe : f e₀ with
      | some b => exact List.findSome?_cons_of_isSome (by rw [hfe]; rfl) |>.trans hfe
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hfe]; rfl), List.findSome?_eq_none_iff]
        intro e' he'
        cases hfe' : f e' with
        | none => rfl
        | some _ =>
          exact absurd (hf e' (List.mem_cons_of_mem _ he') (by rw [hfe']; rfl))
            (hfresh e' he' n hn₀)
    · have hfe : f e = none := by
        cases hfe : f e with
        | none => rfl
        | some _ =>
          exact absurd hn₀ (hfresh e₀ he₀' n (hf e List.mem_cons_self (by rw [hfe]; rfl)))
      rw [List.findSome?_cons_of_isNone (by rw [hfe]; rfl)]
      exact hd.findSome?_eq he₀' hn₀ fun e' he' => hf e' (List.mem_cons_of_mem _ he')

/-- The names of the lifting of a type are its name. -/
theorem TypeDeclaration.lifting_names {decl : TypeDeclaration} {F : Name} {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns} :
    (decl.lifting F S ns body).names = [Lifting.name F S] := rfl

-- ADE: none.
/-- The liftings that a signature whose names are distinct declares, each after the destructors
that it lifts, have shapes: those of the entries after a prefix of the signature, by induction on
these entries, since the destructors of a lifting are lifted by the liftings before it, and the
shape of a lifting reads the shapes of the liftings before it. -/
theorem Signature.LiftsInOrder.liftingsHaveShapes (hsig : sig.Distinct) (hord : sig.LiftsInOrder) :
    ∀ (sig₁ pre : Signature), sig = pre ++ sig₁ → Signature.LiftingsHaveShapes sig₁ sig
  | [], _, _ => by
    intro k v decl D S ns body _ _ hL
    exact nomatch hL
  | e :: sig₁, pre, he => by
    have ih := Signature.LiftsInOrder.liftingsHaveShapes hsig hord sig₁ (pre ++ [e])
      (by rw [List.append_assoc]; exact he)
    have hsub : ∀ decl, Entry.typeDeclaration decl ∈ sig₁ → Entry.typeDeclaration decl ∈ sig :=
      fun _ h => he ▸ List.mem_append_right pre (List.mem_cons_of_mem _ h)
    intro k v decl D S ns body hdecl hD hL Γ' Γ ρ qs ls ps ms Δ as π ms' hq hp hS hm hms hπ
    have hfst : (S.zip ms').map (·.1) = S :=
      List.map_fst_zip (by rw [hms.length_eq, hm]; exact Nat.le_refl _)
    rcases List.mem_cons.1 hL with rfl | hL'
    · -- The entry is the lifting: its shape is that of the destructors of `D`, lifted before it.
      have hLs : Entry.typeDeclaration (decl.lifting D S ns body) ∈ sig :=
        he ▸ List.mem_append_right pre List.mem_cons_self
      obtain ⟨T, hT, hTn, hb⟩ := hord pre sig₁ decl D S ns body he hdecl hD
      have hq' : (qs ++ [v.quality]).length = decl.sorts + 1 := by
        rw [List.length_append, hq]
        rfl
      have hp' : (v.grades ps ms).length = decl.liftingGrades S := v.length_grades hp hm
      -- The factor of the instance of the lifting is that of its destructors.
      generalize hI : Term.inst (Lifting.name D S) (qs ++ [v.quality]) ls (v.grades ps ms) as =
        B at hπ
      cases hπ with
      | var => cases hI
      | inst hdecl₂ hD₂ hL₂ hq₂ hp₂ hds =>
        injection hI with _ _ hD₃ hq₃ _ hp₃
        obtain ⟨hD₄, hS₄⟩ := Lifting.name_inj hD₃
        subst hD₄ hS₄ hq₃ hp₃
        obtain rfl := Entry.typeDeclaration.inj (hsig.entry_unique hdecl hdecl₂ hD hD₂)
        have heL := Entry.typeDeclaration.inj
          (hsig.entry_unique hLs hL₂ TypeDeclaration.name_mem_lifting_names
            TypeDeclaration.name_mem_lifting_names)
        obtain rfl := TypeDeclaration.lifting_destructors heL
        obtain rfl := TypeDeclaration.lifting_body heL
        -- The shape of the destructors of `D` gives the lifting the factor of its destructors.
        have hfind : decl.codataTypes.find? (·.name == D) = some T := by
          obtain ⟨T₀, hT₀⟩ := Option.isSome_iff_exists.1
            ((List.find?_isSome (p := fun (x : CodataType decl.sorts decl.grades decl.levels decl.scope) => x.name == D)).2 ⟨T, hT, beq_iff_eq.2 hTn⟩)
          have hT₀' : T₀.name = D := beq_iff_eq.1 (List.find?_some (p := fun (x : CodataType decl.sorts decl.grades decl.levels decl.scope) => x.name == D) hT₀)
          rw [hT₀, List.eq_of_nodup_map (TypeDeclaration.codataTypes_nodup (hsig.nodup hdecl))
            (List.mem_of_find?_eq_some hT₀) hT (hT₀'.trans hTn.symm)]
        let I : Instance (decl.sorts + 1) (decl.liftingGrades S) :=
          .ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hp'
        have hLd := hb I
        rw [Instance.liftingVariables_ofLists qs ps v ms hq hp hq' hp',
          show I.lifted = .ofLists qs ps hq hp from
            Instance.lifted_ofLists qs ps v.quality _ hq hp hq' hp'] at hLd
        have hF := hLd.shape_factor hsub ih D (fun _ _ => ⟨_, _, _, _, _, _, _, _, _, rfl⟩)
          (ν := Shape.motives (S.zip ms')) (ν₀ := Nesting.lift (Shape.motives (S.zip ms')))
          (fun x => .inr ⟨.succ x, Args.bound _, InstanceArgs.identity_rename_toSubst Ren.weaken x,
            rfl⟩)
          (Lifting.Shapes.lift (Lifting.base_shapes hS (by rw [hms.length_eq, hm])
            (fun j h₁ h₂ => by
              have hj : j < ms.length := hm ▸ h₁
              have hf := Lifting.motiveGrade_ofLists hS (qs ++ [v.quality]) ps v ms hq' hp hm hp'
                0 j h₁
              have ho := Lifting.motiveGrade_ofLists hS (qs ++ [v.quality]) ps v ms hq' hp hm hp'
                1 j h₁
              have hmj : (ms'[j].factor, ms'[j].ownership) = (ms[j].factor, ms[j].ownership) := by
                have := congrArg (·[j]?) hms
                simpa [List.getElem?_map, h₂, hj] using this
              obtain ⟨h₃, h₄⟩ := Prod.mk.inj hmj
              exact ⟨h₃.trans hf.symm, h₄.trans ho.symm⟩) decl.scope))
          (fun E => by
            show ((Lifting.base S _ decl.scope).block E).map _ = none
            rw [Lifting.base_block]
            rfl)
        rw [Destructors.shape_substLevels] at hF
        have hu := Destructors.Factor.unique hsig
          (TypeDeclaration.liftingScope_distinctMotives _ _ _) hF hds
        refine ⟨((T.body (.ofLists qs ps hq hp)).shape sig v (sig.shapes v sig₁) D
          (Shape.motives (S.zip ms'))).1, ?_⟩
        simp only [Signature.shapes, hfst, TypeDeclaration.lifting_names, ↓reduceIte]
        rw [hsig.findSome?_eq hdecl hD (fun e' _ he' => ?_)]
        · simp only [hq, hp, ↓reduceDIte, hfind, Option.map_some, hu]
        · cases e' with
          | typeDeclaration decl' =>
            simp only at he'
            split at he'
            · split at he'
              · obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.1
                  (Option.isSome_map.symm.trans he' : _)
                have := List.find?_some hT'
                exact (beq_iff_eq.1 this) ▸ TypeDeclaration.codata_name_mem_names
                  (List.mem_of_find?_eq_some hT')
              · cases he'
            · cases he'
          | constantDefinition _ => cases he'
          | constantDeclaration _ => cases he'
    · -- The entry is not the lifting: its names are not the name of the lifting.
      have hne : ∀ L, e = .typeDeclaration L → L.names ≠ [Lifting.name D S] := by
        rintro L rfl hLn
        obtain ⟨-, -, hfresh, -⟩ := Signature.Distinct.suffix pre (he ▸ hsig)
        exact hfresh _ hL' (Lifting.name D S) (by simp [Entry.names, hLn])
          TypeDeclaration.name_mem_lifting_names
      cases e with
      | typeDeclaration L =>
        simp only [Signature.shapes, hfst, hne L rfl, ↓reduceIte]
        exact ih k v hdecl hD hL' hq hp hS hm hms hπ
      | constantDefinition _ =>
        simp only [Signature.shapes]
        exact ih k v hdecl hD hL' hq hp hS hm hms hπ
      | constantDeclaration _ =>
        simp only [Signature.shapes]
        exact ih k v hdecl hD hL' hq hp hS hm hms hπ

/-! ## Shapes of the Types Lifted in a Signature -/

-- ADE: none.
/-- A type lifted, in a signature whose names are distinct and that declares each lifting after the
destructors that it lifts, has a shape, which carries the factor and the ownership of the recursive
result that it is the type of, where the shapes of the variables follow the lifting, and those of
the types of the block carry their ownerships. -/
theorem Term.Lifts.shape_eq (hsig : sig.Distinct) (hord : sig.LiftsInOrder)
    {block : Name → Option Shape.Motive} {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ} {n : Nest Name}
    {e : Term k Γ'} {A : Term k Γ} {A' : Term k Γ'} {m : Lifting.Result k}
    (h : Term.Lifts sig v ρ n e A A' m) {ν : Nesting Shape.Motive Γ} (hν : ρ.Shapes @ν)
    (hb : ∀ D b, ρ.block D = some b → ∃ Υ, block D = some ⟨Υ, .linearLinear, b.ownership⟩) :
    ∃ m', A.shape v (sig.shapes v sig) block @ν n = some m' ∧ m'.Of m :=
  h.shape (fun _ h => h) (hord.liftingsHaveShapes hsig sig [] rfl) hν hb

end Sic.Core
