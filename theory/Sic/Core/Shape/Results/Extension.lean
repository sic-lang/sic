module

public import Sic.Core.Shape.Recursion
import Sic.Core.Positivity.Nesting
import Sic.Core.Shape.Results.Lifting

/-!
# Shapes in a Signature With More Entries

The shape that a signature gives a type, when it has one, is the shape that a signature with more
entries before them gives it, when their names are distinct: the shape of a lifting reads the
entries from the lifting on, which an extension does not change, and the shape of a type, where no
variable has a position, has no argument without shape at a position, so that the shapes of the
liftings that it reads are given, and given alike.
The shapes of the nested fields of a constructor of a block of the signature are then the same in
the signature with more entries, when each nested field has a shape, as the other fields have none
in both, and so is the requirement of the recursion of a recursor on the block, which reads them.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat} {v : Lifting.Variables} {md : Mode} {ax : Grade → Multiplicity}

/-! ## Shapes of the Liftings -/

/-- A lifting that has a shape along the entries of a signature is declared by one of them. -/
theorem Signature.mem_of_shapes {D : Name} {qs : List Quality} {ps : List Grade}
    {ms : List (Nat × Shape.Motive)} {σ : Shape × Grade} :
    (sig : Signature) → Signature.shapes v md ax sig D qs ps ms = some σ →
      ∃ L, Entry.typeDeclaration L ∈ sig ∧ Lifting.name D (ms.map (·.1)) ∈ L.names
  | [], h => nomatch h
  | .typeDeclaration L :: sig, h => by
    by_cases hL : L.names = [Lifting.name D (ms.map (·.1))]
    · exact ⟨L, List.mem_cons_self, by rw [hL]; exact List.mem_singleton_self _⟩
    · simp only [Signature.shapes, hL, ↓reduceIte] at h
      obtain ⟨L', h₁, h₂⟩ := Signature.mem_of_shapes sig h
      exact ⟨L', List.mem_cons_of_mem _ h₁, h₂⟩
  | .constantDefinition _ :: sig, h => by
    simp only [Signature.shapes] at h
    obtain ⟨L', h₁, h₂⟩ := Signature.mem_of_shapes sig h
    exact ⟨L', List.mem_cons_of_mem _ h₁, h₂⟩
  | .constantDeclaration _ :: sig, h => by
    simp only [Signature.shapes] at h
    obtain ⟨L', h₁, h₂⟩ := Signature.mem_of_shapes sig h
    exact ⟨L', List.mem_cons_of_mem _ h₁, h₂⟩

/-- A lifting that has a shape along the entries of a signature has the same shape along the
entries of a signature with more entries before them, whose names are distinct. -/
theorem Signature.shapes_append_of_eq_some {sig pre : Signature} (hd : (pre ++ sig).Distinct)
    {D : Name} {qs : List Quality} {ps : List Grade} {ms : List (Nat × Shape.Motive)}
    {σ : Shape × Grade} (h : Signature.shapes v md ax sig D qs ps ms = some σ) :
    Signature.shapes v md ax (pre ++ sig) D qs ps ms = some σ := by
  obtain ⟨L, hL, hn⟩ := Signature.mem_of_shapes sig h
  rw [Signature.shapes_append hL hn pre hd, h]

/-! ## Shapes of the Types -/

mutual

/-- A type, where no variable has a position, keeps the shape that it has where `lookup₁` gives the
shapes of the liftings, where `lookup₂` gives them, when `lookup₂` gives each shape that `lookup₁`
gives: each instance at a nesting with positions has its arguments at a position with shapes. -/
theorem Term.shape_of_extends {lookup₁ lookup₂ : Shape.Lookup}
    {block : Name → Option Shape.Motive}
    (hl : ∀ D qs ps ms σ, lookup₁ D qs ps ms = some σ → lookup₂ D qs ps ms = some σ) :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} → (∀ (a : Scope.Entry) (x : Var Γ a), ν x = .plain) →
      {n : Nest Name} → (A : Term k Γ) → {s : Shape.Motive} →
        A.shape v lookup₁ block @ν n = some s → A.shape v lookup₂ block @ν n = some s
  | _, _, _, _, .var _ _, _, h => h
  | _, ν, hν, n, .inst D qs _ ps as, s, h => by
    cases n with
    | direct E => exact h
    | plain =>
      simp only [Term.shape] at h ⊢
      split at h
      · next m ms hm =>
        rw [InstanceArgs.shapes_of_extends hl hν as hm]
        cases h₁ : lookup₁ D qs ps (m :: ms) with
        | none => rw [h₁] at h; exact nomatch h
        | some σ => rw [h₁] at h; simp only [hl _ _ _ _ _ h₁]; exact h
      · exact nomatch h
    | inst ns =>
      simp only [Term.shape] at h ⊢
      split at h
      · next m ms hm =>
        rw [InstanceArgs.shapes_of_extends hl hν as hm]
        cases h₁ : lookup₁ D qs ps (m :: ms) with
        | none => rw [h₁] at h; exact nomatch h
        | some σ => rw [h₁] at h; simp only [hl _ _ _ _ _ h₁]; exact h
      · exact nomatch h
  | _, _, _, _, .sort _, _, h => nomatch h
  | _, _, _, _, .const _ _ _ _, _, h => nomatch h
  | _, _, _, _, .ctor _ _ _ _ _ _ _, _, h => nomatch h
  | _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _, _, h => nomatch h
  | _, _, _, _, .obs _ _ _ _ _ _ _ _, _, h => nomatch h
  | _, _, _, _, .corec _ _ _ _ _ _ _ _ _, _, h => nomatch h

/-- The arguments of an instance, where no variable has a position, keep the shapes that they have
where `lookup₁` gives the shapes of the liftings, where `lookup₂` gives them, when `lookup₂` gives
each shape that `lookup₁` gives: an argument at no position has no shape whatever the liftings. -/
theorem InstanceArgs.shapes_of_extends {lookup₁ lookup₂ : Shape.Lookup}
    {block : Name → Option Shape.Motive}
    (hl : ∀ D qs ps ms σ, lookup₁ D qs ps ms = some σ → lookup₂ D qs ps ms = some σ) :
    {Γ : Scope} → {ν : Nesting Shape.Motive Γ} → (∀ (a : Scope.Entry) (x : Var Γ a), ν x = .plain) →
      {ns : List (Nest Name)} → {Δ : Scope} → (as : InstanceArgs k Γ Δ) →
        {l : List (Nat × Shape.Motive)} →
          as.shapes v lookup₁ block @ν ns = some l → as.shapes v lookup₂ block @ν ns = some l
  | _, _, _, _, _, .nil, _, h => h
  | _, ν, hν, ns, _, .snoc (e := e) as B, l, h => by
    obtain ⟨l₀, h₀, rfl⟩ := InstanceArgs.shapes_snoc_eq_some h
    have hν' := Nesting.liftN_plain e.params.length hν
    rw [InstanceArgs.shapes, InstanceArgs.shapes_of_extends hl hν as h₀]
    cases hB : B.shape v lookup₁ block (Nesting.liftN _ @ν) (ns.headD .plain) with
    | some m =>
      rw [Term.shape_of_extends hl hν' B hB]
      rfl
    | none =>
      -- An argument without shape is at no position, where no lifting gives it one.
      rw [InstanceArgs.shapes, h₀, hB] at h
      simp only at h
      split at h
      · next hp =>
        rw [Nest.eq_plain_of_isPlain hp, Term.shape_eq_none_of_avoids
          fun x hx => absurd (hν' _ x) hx]
        simp [Nest.isPlain]
      · exact nomatch h

end

/-! ## Shapes of the Nested Fields -/

/-- The skeleton of a type that an entry of a signature declares is the same along the entries of a
signature with more entries before them, whose names are distinct. -/
theorem Signature.skeleton_append {sig pre : Signature} (hd : (pre ++ sig).Distinct) {e₀ : Entry}
    (he₀ : e₀ ∈ sig) {D : Name} (hD : D ∈ e₀.names) (qs : List Quality) (ps : List Grade) :
    (pre ++ sig).skeleton D qs ps = sig.skeleton D qs ps := by
  have hf : ∀ e ∈ pre ++ sig, (Entry.skeleton D qs ps e).isSome → D ∈ e.names := fun e _ h =>
    if hn : D ∈ e.names then hn else by rw [Entry.skeleton_of_not_mem hn] at h; exact nomatch h
  unfold Signature.skeleton
  rw [hd.findSome?_eq (List.mem_append_right pre he₀) hD hf,
    (Signature.Distinct.suffix pre hd).findSome?_eq he₀ hD
      fun e he => hf e (List.mem_append_right pre he)]

/-- The shapes of the types of a block that an entry of a signature declares are the same along the
entries of a signature with more entries before them, whose names are distinct. -/
theorem Signature.blockShapes_append {sig pre : Signature} (hd : (pre ++ sig).Distinct)
    {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig) (qs : List Quality)
    (ps : List Grade) (χ : Grade) :
    (pre ++ sig).blockShapes decl.names qs ps χ = sig.blockShapes decl.names qs ps χ := by
  funext D
  unfold Signature.blockShapes
  split
  · next hD => rw [Signature.skeleton_append hd hdecl hD]
  · rfl

/-- A type at a position has the shape that the shapes of the types of the block give it, or that of
its variable, whatever the shapes of the liftings. -/
theorem Term.shape_direct {lookup₁ lookup₂ : Shape.Lookup} {block : Name → Option Shape.Motive}
    {Γ : Scope} {ν : Nesting Shape.Motive Γ} (E : Name) (A : Term k Γ) :
    A.shape v lookup₁ block @ν (.direct E) = A.shape v lookup₂ block @ν (.direct E) := by
  cases A <;> rfl

/-- The shapes of the nested results of the fields of a telescope are the same where `lookup₂`
gives the shapes of the liftings as where `lookup₁` does, when `lookup₂` gives each shape that
`lookup₁` gives and each nested field has a shape where `lookup₁` gives them: a field at no
position has no shape, and a recursive field the shape of the type of the block, whatever the
liftings. -/
theorem Telescope.nestedShapes_of_extends {lookup₁ lookup₂ : Shape.Lookup}
    {block : Name → Option Shape.Motive}
    (hl : ∀ D qs ps ms σ, lookup₁ D qs ps ms = some σ → lookup₂ D qs ps ms = some σ)
    (names : List Name) :
    {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) →
      (∀ (l : Nat) (ns : List (Nest Name)), (Θ.nest names)[l]? = some (.inst ns) →
        ∃ σ, (Θ.nestedShapes v lookup₁ block names)[l]? = some (some σ)) →
      Θ.nestedShapes v lookup₂ block names = Θ.nestedShapes v lookup₁ block names
  | _, [], .nil, _ => rfl
  | Γ, _ :: _, .cons _ _ A Θ, h => by
    simp only [Telescope.nestedShapes]
    rw [Telescope.nestedShapes_of_extends hl names Θ fun l ns hl' => h (l + 1) ns hl']
    congr 1
    have h₀ : ∀ (a : Scope.Entry) (x : Var Γ a), (Nesting.plain : Nesting Shape.Motive Γ) x =
        .plain := fun _ _ => rfl
    cases hn : A.blockNest names with
    | plain =>
      rw [Term.shape_eq_none_of_avoids (lookup := lookup₂) (A := A) (ν := Nesting.plain)
          fun x hx => absurd (h₀ _ x) hx,
        Term.shape_eq_none_of_avoids (lookup := lookup₁) (A := A) (ν := Nesting.plain)
          fun x hx => absurd (h₀ _ x) hx]
    | direct E => rw [Term.shape_direct E A]
    | inst ns =>
      obtain ⟨σ, hσ⟩ := h 0 ns (by simp [Telescope.nest, hn])
      simp only [Telescope.nestedShapes, List.getElem?_cons_zero, Option.some.injEq, hn] at hσ
      cases hA : A.shape v lookup₁ block Nesting.plain (.inst ns) with
      | none => rw [hA] at hσ; exact nomatch hσ
      | some s => rw [Term.shape_of_extends hl h₀ A hA]

/-- The shapes of the nested results of the fields of a constructor of a block that an entry of a
signature declares are the same along the entries of a signature with more entries before them,
whose names are distinct, when each nested field has a shape along the entries of the signature. -/
theorem Constructor.nestedShapes_append {sig pre : Signature} (hd : (pre ++ sig).Distinct)
    {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig) (qs : List Quality)
    (ps : List Grade) (χ : Grade)
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    {I : Instance decl.sorts decl.grades}
    (h : con.NestedHaveShapes sig v md ax decl.names qs ps χ I) :
    con.nestedShapes (pre ++ sig) v md ax decl.names qs ps χ I =
      con.nestedShapes sig v md ax decl.names qs ps χ I := by
  unfold Constructor.nestedShapes
  rw [Signature.blockShapes_append hd hdecl]
  exact Telescope.nestedShapes_of_extends
    (fun _ _ _ _ _ hσ => Signature.shapes_append_of_eq_some hd hσ) decl.names _ h

/-- Each nested field of a constructor of a block that an entry of a signature declares has a shape
along the entries of a signature with more entries before them, whose names are distinct, when it
has one along the entries of the signature. -/
theorem Constructor.NestedHaveShapes.append {sig pre : Signature} (hd : (pre ++ sig).Distinct)
    {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig) {qs : List Quality}
    {ps : List Grade} {χ : Grade}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    {I : Instance decl.sorts decl.grades}
    (h : con.NestedHaveShapes sig v md ax decl.names qs ps χ I) :
    con.NestedHaveShapes (pre ++ sig) v md ax decl.names qs ps χ I := by
  intro l ns hl
  rw [Constructor.nestedShapes_append hd hdecl qs ps χ h]
  exact h l ns hl

/-- A field of a telescope whose recursive result has the shape of a lifting is nested, when the
types of the block have the shape of the recursor itself: a field at no position has no shape, and
a recursive field the shape of the type of its block. -/
theorem Telescope.nest_of_nestedShapes {lookup : Shape.Lookup}
    {block : Name → Option Shape.Motive}
    (hb : ∀ D μ, block D = some μ → ∃ K, μ.next = .recursor K) (names : List Name) :
    {Γ : Scope} → {ps : List Parameter} → (Θ : Telescope k Γ ps) → {l : Nat} → {σ : Shape} →
      (Θ.nestedShapes v lookup block names)[l]? = some (some σ) →
        ∃ ms, (Θ.nest names)[l]? = some (.inst ms)
  | _, [], .nil, _, _, h => nomatch h
  | Γ, _ :: _, .cons _ _ A Θ, l + 1, _, h =>
    Telescope.nest_of_nestedShapes hb names Θ h
  | Γ, _ :: _, .cons _ _ A Θ, 0, σ, h => by
    simp only [Telescope.nestedShapes, List.getElem?_cons_zero, Option.some.injEq] at h
    simp only [Telescope.nest, List.getElem?_cons_zero, Option.some.injEq]
    have h₀ : ∀ (a : Scope.Entry) (x : Var Γ a), (Nesting.plain : Nesting Shape.Motive Γ) x =
        .plain := fun _ _ => rfl
    cases hn : A.blockNest names with
    | inst ms => exact ⟨ms, rfl⟩
    | plain =>
      rw [hn, Term.shape_eq_none_of_avoids (A := A) (ν := Nesting.plain)
        fun x hx => absurd (h₀ _ x) hx] at h
      exact nomatch h
    | direct E =>
      rw [hn] at h
      exfalso
      cases A with
      | inst D _ _ _ _ =>
        simp only [Term.shape] at h
        cases hD : block D with
        | none => rw [hD] at h; exact nomatch h
        | some μ =>
          rw [hD] at h
          obtain ⟨K, hK⟩ := hb D μ hD
          obtain ⟨next, f, o⟩ := μ
          cases hK
          exact nomatch h
      | var x _ => exact nomatch h
      | sort _ => exact nomatch h
      | const _ _ _ _ => exact nomatch h
      | ctor _ _ _ _ _ _ _ => exact nomatch h
      | recursor _ _ _ _ _ _ _ _ _ _ _ _ => exact nomatch h
      | obs _ _ _ _ _ _ _ _ => exact nomatch h
      | corec _ _ _ _ _ _ _ _ _ => exact nomatch h
      | equality _ _ _ _ _ => exact nomatch h
      | refl _ _ _ _ => exact nomatch h
      | transp _ _ _ _ _ _ => exact nomatch h
      | propExt _ _ _ _ _ => exact nomatch h
      | coind _ _ _ _ _ _ _ _ _ _ => exact nomatch h

/-- A field of a constructor whose recursive result has the shape of a lifting is nested. -/
theorem Constructor.nest_of_nestedShapes {j g k' : Nat} {Δ : Scope} {sig : Signature}
    {names : List Name} {qs : List Quality} {ps : List Grade} {χ : Grade}
    {con : Constructor j g k' Δ} {I : Instance j g} {l : Nat} {σ : Shape}
    (h : (con.nestedShapes sig v md ax names qs ps χ I)[l]? = some (some σ)) :
    ∃ ms, ((con.fields I).nest names)[l]? = some (.inst ms) :=
  Telescope.nest_of_nestedShapes (fun D μ hD => by
    unfold Signature.blockShapes at hD
    split at hD
    · cases hD; exact ⟨_, rfl⟩
    · exact nomatch hD) names _ h

/-! ## Requirement of the Recursion -/

/-- The requirement of the recursion of a recursor on a block that an entry of a signature declares,
whose nested fields have shapes, is the same along the entries of a signature with more entries
before them, whose names are distinct. -/
theorem TypeDeclaration.recursionRequirement_append {sig pre : Signature}
    (hd : (pre ++ sig).Distinct) {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig)
    {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} (h : decl.NestedHaveShapes sig v m χ qs ps I) :
    decl.recursionRequirement (pre ++ sig) v m χ qs ps I =
      decl.recursionRequirement sig v m χ qs ps I := by
  have hn : ∀ ax ∈ [Grade.run, Grade.total],
      decl.nestedPairs (pre ++ sig) v m χ qs ps I ax = decl.nestedPairs sig v m χ qs ps I ax :=
    fun ax hxs => by
      unfold TypeDeclaration.nestedPairs
      congr 1
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      rw [Constructor.nestedShapes_append hd hdecl qs ps χ (h i x.1 x.2.1 x.2.2 hi ax hxs)]
  unfold TypeDeclaration.recursionRequirement
  exact Grade.ext (by simp only [Parameter.recursion]; rw [hn Grade.run (by simp)])
    (by simp only [Parameter.recursion]; rw [hn Grade.total (by simp)])

/-- The nested fields of the constructors of a block that an entry of a signature declares have
shapes along the entries of a signature with more entries before them, whose names are distinct,
when they have shapes along the entries of the signature. -/
theorem TypeDeclaration.NestedHaveShapes.append {sig pre : Signature}
    (hd : (pre ++ sig).Distinct) {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig)
    {v : Lifting.Variables} {m : Mode} {χ : Grade} {qs : List Quality} {ps : List Grade}
    {I : Instance decl.sorts decl.grades} (h : decl.NestedHaveShapes sig v m χ qs ps I) :
    decl.NestedHaveShapes (pre ++ sig) v m χ qs ps I :=
  fun i j T con hi ax hxs => (h i j T con hi ax hxs).append hd hdecl

end Sic.Core
