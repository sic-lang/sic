module

public import Sic.Core.Substitution

/-!
# Prelude

The prelude of annex 17 of RFC 36: three type declarations that the type system uses for its own
needs, the unit `Unit`, the pair `Pair` and the type of positions `Step`, the packing `⟨Θ⟩` of a
telescope into nested pairs, the packing `⟨t̄⟩` of its arguments and the unpacking of a term of a
packing, with the commutation of these definitions with the renamings and the substitutions; the
typing of a corecursor reads them, and the modules of `Sic/Core/Prelude/` give their properties.

The packing lives in a universe, whatever the sorts of the entries of the telescope, so that a
recursor on it may build a term of any sort: a data type of propositions with a constructor has
motives that are propositions.
ADE have no prelude: their pairs and their unit are types of the theory, which a program names.
-/

@[expose] public section

namespace Sic.Core

/-! ## Declarations -/

/-- `mk : ()`, the constructor of the unit, without fields. -/
def Prelude.unitMk : Constructor 0 0 1 [] := { name := "mk", params := fun _ => [], fields := fun _ => .nil }

/-- `Unit ≔ mk : ()`, the type of the unit, which uses no parameter. -/
def Prelude.unitType : DataType 0 0 1 [] :=
  { name := "Unit", usage := fun _ => 𝟘ᶜ, constructors := [Prelude.unitMk] }

-- ADE: `Unitʷ` and `Unitˢ`, in `Definition/Untyped.agda`, as a declared type.
/-- `data.{; l; | ⊤} ε : U_l where Unit ▶ 00ᵞ ≔ mk : ε`: the unit, at each level, with a single constructor
without fields.
RFC: `\mathsf{prelude}.\mathsf{Unit}` -/
def Prelude.unit : TypeDeclaration where
  sorts := 0
  levels := 1
  grades := 0
  constraint _ := True
  scope := []
  params _ := .empty
  sort _ := ⟨.type, .var 0⟩
  body := .data [Prelude.unitType]

/-- The ownership of the result of the second parameter `X` of the pair, a type, which states
nothing. -/
def Prelude.pairOwnership : ResultOwnership 1 := ⟨some .unrestrictedUnrestricted, fun _ => none⟩

/-- The scope of the parameters of the pair, `A` and `X`, the last one first: `X` is a second-order
variable over a variable `x : A`, whose uses in `X` its grade `ωωᵖ` does not bound, since the scope
of the parameters is the same at all the instances. -/
abbrev Prelude.pairScope : Scope :=
  [.secondOrder [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩] Prelude.pairOwnership, .var]

/-- `mk : (x : A ▶ p; ωωᵖ ◀ r, y : X[x] ▶ 11ᵖ; 00ᵖ ◀ 11ᵖ)`, the constructor of the pair. -/
def Prelude.pairMk : Constructor 1 2 2 Prelude.pairScope where
  name := "mk"
  params ι := [⟨ι.grades 0, ι.grades 1⟩, ⟨Grade.one, Grade.one⟩]
  fields ι := .cons .unrestrictedUnrestricted ⟨ι.grades 0, ι.grades 1⟩ (.var₀ (.succ .zero))
    (.cons Grade.zero ⟨Grade.one, Grade.one⟩
      (.var (.succ .zero) (.cons (.var₀ .zero) .nil)) .nil)

/-- `Pair ▶ 00ᵞ • p • 11ᵖ ≔ mk : …`, the type of the pair, which uses `A` with the grade `p` of its
field and `X` once. -/
def Prelude.pairType : DataType 1 2 2 Prelude.pairScope :=
  { name := "Pair", usage := fun ι => (𝟘ᶜ ∙ ι.grades 0) ∙ Grade.one,
    constructors := [Prelude.pairMk] }

-- ADE: `Σʷ` and `Σˢ`, in `Definition/Untyped.agda`, as a declared type.
/-- `data.{s; l₁, l₂; p, r | s = Ω → ⌞p⌟ ≠ 11ᵐ} (A : s_{l₁}, X : (x : A ▶ ωωᵖ; ωωᵖ ◀ ωωᵖ ⊢ U_{l₂} ◀ ωωᵖ))
: U_{l₁ ⊔ l₂} where Pair ▶ 00ᵞ • p • 11ᵖ ≔ mk : (x : A ▶ p; ωωᵖ ◀ r, y : X[x] ▶ 11ᵖ; 00ᵖ ◀ 11ᵖ)`:
the pair of a term of `A`, of any sort, used with the grade `p` and of the requirement `r`, and of a
term of `X[x]`, used once, in a universe; the constraint admits the instances where a proposition
`A` has a grade without use at run time, which the formation requires.
RFC: `\mathsf{prelude}.\mathsf{Pair}` -/
def Prelude.pair : TypeDeclaration where
  sorts := 1
  levels := 2
  grades := 2
  constraint ι := ι.sorts 0 = .prop → (ι.grades 0).mode ≠ .oneOne
  scope := Prelude.pairScope
  params ι := (Context.empty.var (.sort ⟨ι.sorts 0, .var 0⟩)).secondOrder
    (.cons .unrestrictedUnrestricted ⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩
      (.var₀ .zero) .nil)
    (.sort ⟨.type, .var 1⟩) Prelude.pairOwnership
  sort _ := ⟨.type, .max (.var 0) (.var 1)⟩
  body := .data [Prelude.pairType]

/-- The scope of the parameters of the type of positions, `A` and `B`, the last one first. -/
abbrev Prelude.stepScope : Scope := [.var, .var]

/-- `next : (x : A ▶ p; 00ᵖ ◀ ωωᵖ)`, the constructor of a new state. -/
def Prelude.stepNext : Constructor 1 2 2 Prelude.stepScope where
  name := "next"
  params ι := [⟨ι.grades 0, .unrestrictedUnrestricted⟩]
  fields ι := .cons Grade.zero ⟨ι.grades 0, .unrestrictedUnrestricted⟩ (.var₀ (.succ .zero)) .nil

/-- `done : (x : B ▶ q; 00ᵖ ◀ ωωᵖ)`, the constructor of a term already built. -/
def Prelude.stepDone : Constructor 1 2 2 Prelude.stepScope where
  name := "done"
  params ι := [⟨ι.grades 1, .unrestrictedUnrestricted⟩]
  fields ι := .cons Grade.zero ⟨ι.grades 1, .unrestrictedUnrestricted⟩ (.var₀ .zero) .nil

/-- `Step ▶ 00ᵞ • p • q ≔ next : … | done : …`, the type of positions, which uses `A` with the grade
`p` of its new states and `B` with the grade `q` of its terms already built. -/
def Prelude.stepType : DataType 1 2 2 Prelude.stepScope :=
  { name := "Step", usage := fun ι => (𝟘ᶜ ∙ ι.grades 0) ∙ ι.grades 1,
    constructors := [Prelude.stepNext, Prelude.stepDone] }

-- ADE: none.
/-- `data.{s; l₁, l₂; p, q | s = Ω → ⌞q⌟ ≠ 11ᵐ} (A : U_{l₁}, B : s_{l₂}) : U_{l₁ ⊔ l₂}
where Step ▶ 00ᵞ • p • q ≔ next : (x : A ▶ p; 00ᵖ ◀ ωωᵖ) | done : (x : B ▶ q; 00ᵖ ◀ ωωᵖ)`: the
type of the positions of a corecursor, either a new state of `A`, used with the grade `p`, or a term
of `B`, of any sort, already built, used with the grade `q`, in a universe; the constraint admits the
instances where a proposition `B` has a grade without use at run time.
RFC: `\mathsf{prelude}.\mathsf{Step}` -/
def Prelude.step : TypeDeclaration where
  sorts := 1
  levels := 2
  grades := 2
  constraint ι := ι.sorts 0 = .prop → (ι.grades 1).mode ≠ .oneOne
  scope := Prelude.stepScope
  params ι := (Context.empty.var (.sort ⟨.type, .var 0⟩)).var (.sort ⟨ι.sorts 0, .var 1⟩)
  sort _ := ⟨.type, .max (.var 0) (.var 1)⟩
  body := .data [Prelude.stepType]

/-- The prelude, the unit, then the pair, then the type of positions, the last one first.
RFC: `\mathsf{prelude}_\Sigma` -/
def Signature.prelude : Signature :=
  [.typeDeclaration Prelude.step, .typeDeclaration Prelude.pair, .typeDeclaration Prelude.unit]

/-- `Σ ∋ prelude`: the signature holds the declarations of the prelude.
RFC: `\mathsf{prelude}_\in` -/
def Signature.HasPrelude (sig : Signature) : Prop := ∀ e ∈ Signature.prelude, e ∈ sig

/-- The prelude holds its own declarations. -/
theorem Signature.hasPrelude_prelude : Signature.prelude.HasPrelude := fun _ h => h

/-! ## Packing -/

variable {k : Nat}

/-- `level_κ̄(l) = l₁ ⊔ (… ⊔ (lₐ ⊔ l))`: the level of the packing of a telescope whose entries live
in the sorts `κ̄`, of levels `l̄`, below the level `l`.
RFC: `\mathsf{level}_{\bar\kappa}` -/
def Telescope.packLevel (κs : List (Universe k)) (l : Level k) : Level k :=
  κs.foldr (fun κ l' => .max κ.level l') l

/-- The arguments `(A, x. B)` of an instance of the pair. -/
abbrev Prelude.pairArgs {Γ : Scope} (A : Term k Γ) (B : Term k (.var :: Γ)) :
    InstanceArgs k Γ Prelude.pairScope :=
  .snoc (.snoc .nil A) B

-- ADE: none.
/-- `⟨Θ⟩_{κ̄; l}`: the telescope `Θ`, whose entries live in the sorts `κ̄`, packed in the universe
`U_l`, the nested pairs of its entries, with their grades and their requirements, which end with
the unit of `U_l`; the Lean takes `U_l` for a sort that `κ̄` lacks, a case that the judgment
`Σ; Γ ⊢ Θ : κ̄ ≤ l` excludes.
RFC: `\mathsf{pack}_\Theta` -/
def Telescope.pack {Γ : Scope} : {ps : List Parameter} → Telescope k Γ ps → List (Universe k) →
    Level k → Term k Γ
  | [], .nil, _, l => .inst "Unit" [] [l] [] .nil
  | _ :: _, .cons _ p A Θ, κs, l =>
    .inst "Pair" [(κs.headD ⟨.type, l⟩).quality]
      [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l] [p.usage, p.requirement]
      (Prelude.pairArgs A (Θ.pack κs.tail l))

-- ADE: none.
/-- `⟨t̄⟩_{Θ; κ̄; l}`: the arguments `t̄` of the telescope `Θ`, whose entries live in the sorts `κ̄`,
packed as a term of `⟨Θ⟩_{κ̄; l}`, the nested pairs of the arguments, which end with the unit of
`U_l`; each pair carries its instance, which the rest of the telescope, instantiated by the
arguments before it, gives.
RFC: `\mathsf{pack}_{\bar t}` -/
def Args.pack {Γ : Scope} : {ps : List Parameter} → Args k Γ ps → Telescope k Γ ps →
    List (Universe k) → Level k → Term k Γ
  | [], .nil, .nil, _, l => .ctor "Unit" [] [l] [] .nil "mk" .nil
  | _ :: _, .cons t ts, .cons _ p A Θ, κs, l =>
    .ctor "Pair" [(κs.headD ⟨.type, l⟩).quality]
      [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l] [p.usage, p.requirement]
      (Prelude.pairArgs A (Θ.pack κs.tail l)) "mk"
      (.cons t (.cons (ts.pack (Θ.subst₀ (Subst₀.single t)) κs.tail l) .nil))

-- ADE: none.
/-- `Pair.{s; l₁, l₂; p, r} (A, x. B)`: the instance of the pair at the sort `κ = s_{l₁}`. -/
abbrev Prelude.pairInst {Γ : Scope} (κ : Universe k) (l₂ : Level k) (p r : Grade) (A : Term k Γ)
    (B : Term k (.var :: Γ)) : Term k Γ :=
  .inst "Pair" [κ.quality] [κ.level, l₂] [p, r] (Prelude.pairArgs A B)

/-- The signature that holds the prelude has its pair. -/
theorem Signature.HasPrelude.pair {sig : Signature} (hpre : sig.HasPrelude) :
    sig.HasDataType "Pair" Prelude.pair Prelude.pairType :=
  ⟨hpre _ (by simp [Signature.prelude]), List.mem_singleton_self _, rfl⟩

/-- The signature that holds the prelude has its unit. -/
theorem Signature.HasPrelude.unit {sig : Signature} (hpre : sig.HasPrelude) :
    sig.HasDataType "Unit" Prelude.unit Prelude.unitType :=
  ⟨hpre _ (by simp [Signature.prelude]), List.mem_singleton_self _, rfl⟩

-- ADE: none.
/-- The type `X[y]` of the second field of the pair, at the abstraction `x. B` for `X`, is `B`. -/
theorem Prelude.pairSecond {Γ : Scope} (B : Term k (.var :: Γ)) :
    (B.rename (Ren.liftN 1 Ren.weaken)).instantiate
      (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil) =
      B :=
  Term.subst₀_single_zero_rename_lift_weaken B

-- ADE: none.
/-- The packing of a telescope, substituted, is the packing of the telescope substituted. -/
theorem Telescope.pack_subst : {Γ Δ : Scope} → {ps : List Parameter} → (θ : Subst k Γ Δ) →
    (Θ : Telescope k Δ ps) → (κs : List (Universe k)) → (l : Level k) →
      (Θ.pack κs l).subst θ = (Θ.subst θ).pack κs l
  | _, _, [], _, .nil, _, _ => rfl
  | _, _, _ :: _, θ, .cons _ _ A Θ, κs, l => by
    show Term.inst _ _ _ _ (Prelude.pairArgs (A.subst θ) ((Θ.pack κs.tail l).subst (Subst.lift θ))) = _
    rw [Telescope.pack_subst (Subst.lift θ) Θ]
    rfl

-- ADE: none.
/-- The packing of a telescope, renamed, is the packing of the telescope renamed. -/
theorem Telescope.pack_rename {Γ Δ : Scope} {ps : List Parameter} (ξ : Ren Γ Δ)
    (Θ : Telescope k Δ ps) (κs : List (Universe k)) (l : Level k) :
    (Θ.pack κs l).rename ξ = (Θ.rename ξ).pack κs l := by
  rw [Term.rename_eq_subst, Telescope.rename_eq_subst, Telescope.pack_subst]

-- ADE: none.
/-- The packing of a telescope, substituted, is the packing of the telescope substituted. -/
theorem Telescope.pack_subst₀ {Γ Δ : Scope} {ps : List Parameter} (σ : Subst₀ k Γ Δ)
    (Θ : Telescope k Δ ps) (κs : List (Universe k)) (l : Level k) :
    (Θ.pack κs l).subst₀ σ = (Θ.subst₀ σ).pack κs l := by
  rw [Term.subst₀_eq_subst, Telescope.subst₀_eq_subst, Telescope.pack_subst]

-- ADE: none.
/-- The packing of arguments, renamed, is the packing of the arguments renamed. -/
theorem Args.pack_rename : {Γ Δ : Scope} → {ps : List Parameter} → (ξ : Ren Γ Δ) →
    (ts : Args k Δ ps) → (Θ : Telescope k Δ ps) → (κs : List (Universe k)) → (l : Level k) →
      (ts.pack Θ κs l).rename ξ = (ts.rename ξ).pack (Θ.rename ξ) κs l
  | _, _, [], _, .nil, .nil, _, _ => rfl
  | _, _, _ :: _, ξ, .cons t ts, .cons _ p A Θ, κs, l => by
    have h₁ := Args.pack_rename ξ ts (Θ.subst₀ (Subst₀.single t)) κs.tail l
    have h₂ := Telescope.subst₀_rename_comm_of (σ₁ := Subst₀.single t) (ξ₁ := ξ)
      (σ₂ := Subst₀.single (t.rename ξ)) (ξ₂ := Ren.lift ξ) (fun x => by cases x <;> rfl) Θ
    have h₃ := Telescope.pack_rename (Ren.lift ξ) Θ κs.tail l
    show Term.ctor _ _ _ _ (Prelude.pairArgs (A.rename ξ) ((Θ.pack κs.tail l).rename (Ren.lift ξ))) _
      (.cons (t.rename ξ) (.cons ((ts.pack (Θ.subst₀ (Subst₀.single t)) κs.tail l).rename ξ) .nil)) = _
    rw [h₁, h₂, h₃]
    rfl

/-! ## Unpacking -/

-- ADE: `prodrec` and `unitrec`, in `Definition/Untyped.agda`, nested.
/-- `unpack_r u : ⟨Θ⟩_{κ̄; l} return C with b`: the term `b`, over the variables of the telescope
`Θ`, at the terms that the packed term `u` holds, by a recursor on each pair, then on the unit, each
using its term with the grade `r`, with the motive `C`, which does not depend on the term
eliminated.
RFC: `\mathsf{unpack}` -/
def Term.unpack (r : Grade) : {Γ : Scope} → {ps : List Parameter} → Term k Γ →
    Telescope k Γ ps → List (Universe k) → Level k → Term k Γ → Term k (Γ.extend ps.length) →
      Term k Γ
  | _, [], u, .nil, _, l, C, b =>
    .recursor r "Unit" [] [l] [] .nil u (.cons 0 (C.rename Ren.weaken) .nil) (.cons 0 0 b .nil)
  | _, _ :: ps, u, .cons _ p A Θ, κs, l, C, b =>
    .recursor r "Pair" [(κs.headD ⟨.type, l⟩).quality]
      [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l] [p.usage, p.requirement]
      (Prelude.pairArgs A (Θ.pack κs.tail l)) u (.cons 0 (C.rename Ren.weaken) .nil)
      (.cons 2 0 (Term.unpack r (.var₀ .zero) (Θ.rename Ren.weaken) κs.tail l
        (C.rename (Ren.weakenN 2)) (b.rename (Ren.liftN ps.length Ren.weaken))) .nil)

-- ADE: none.
/-- The unpacking, substituted, is the unpacking of the terms substituted. -/
theorem Term.unpack_subst₀ (r : Grade) : {Γ Δ : Scope} → {ps : List Parameter} →
    (σ : Subst₀ k Γ Δ) → (u : Term k Δ) → (Θ : Telescope k Δ ps) → (κs : List (Universe k)) →
    (l : Level k) → (C : Term k Δ) → (b : Term k (Δ.extend ps.length)) →
      (Term.unpack r u Θ κs l C b).subst₀ σ =
        Term.unpack r (u.subst₀ σ) (Θ.subst₀ σ) κs l (C.subst₀ σ) (b.subst₀ (Subst₀.liftN _ σ))
  | _, _, [], σ, u, .nil, _, l, C, b => by
    show Term.recursor r "Unit" [] [l] [] .nil (u.subst₀ σ)
      (.cons 0 ((C.rename Ren.weaken).subst₀ (Subst₀.lift σ)) .nil) (.cons 0 0 (b.subst₀ σ) .nil) =
      Term.recursor r "Unit" [] [l] [] .nil (u.subst₀ σ)
      (.cons 0 ((C.subst₀ σ).rename Ren.weaken) .nil) (.cons 0 0 (b.subst₀ σ) .nil)
    exact congrArg (fun X => Term.recursor r "Unit" [] [l] [] .nil (u.subst₀ σ) (.cons 0 X .nil)
      (.cons 0 0 (b.subst₀ σ) .nil)) (Term.rename_weaken_subst₀_lift σ C)
  | _, _, _ :: ps, σ, u, .cons _ p A Θ, κs, l, C, b => by
    show Term.recursor r "Pair" _ _ _
      (Prelude.pairArgs (A.subst₀ σ) ((Θ.pack κs.tail l).subst₀ (Subst₀.lift σ))) (u.subst₀ σ)
      (.cons 0 ((C.rename Ren.weaken).subst₀ (Subst₀.lift σ)) .nil)
      (.cons 2 0 ((Term.unpack r (.var₀ .zero) (Θ.rename Ren.weaken) κs.tail l
        (C.rename (Ren.weakenN 2)) (b.rename (Ren.liftN ps.length Ren.weaken))).subst₀
          (Subst₀.lift (Subst₀.lift σ))) .nil) = _
    have h₁ := Telescope.pack_subst₀ (Subst₀.lift σ) Θ κs.tail l
    have h₂ := Term.rename_weaken_subst₀_lift (b := .var) σ C
    have h₃ := Term.unpack_subst₀ r (Subst₀.lift (Subst₀.lift σ)) (.var₀ .zero) (Θ.rename Ren.weaken)
      κs.tail l (C.rename (Ren.weakenN 2)) (b.rename (Ren.liftN ps.length Ren.weaken))
    have h₅ := (Telescope.subst₀_rename_comm_of (σ₁ := Subst₀.lift (e := .var) σ)
      (ξ₁ := Ren.weaken (e := .var)) (σ₂ := Subst₀.lift (e := .var) (Subst₀.lift (e := .var) σ))
      (ξ₂ := Ren.weaken (e := .var)) (fun _ => rfl) Θ).symm
    have h₆ := (Term.subst₀_rename_comm_of (σ₁ := σ) (ξ₁ := Ren.weakenN 2)
      (σ₂ := Subst₀.lift (e := .var) (Subst₀.lift (e := .var) σ)) (ξ₂ := Ren.weakenN 2) (fun x => by
        show _ = ((σ x).rename Ren.weaken).rename Ren.weaken
        rw [Val.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := Ren.weaken) (ξ₃ := Ren.weakenN 2)
          (fun _ => rfl)]
        rfl) C).symm
    have h₇ := (Term.subst₀_rename_comm_of (σ₁ := Subst₀.liftN ps.length (Subst₀.lift σ))
      (ξ₁ := Ren.liftN ps.length (Ren.weaken (e := .var)))
      (σ₂ := Subst₀.liftN ps.length (Subst₀.lift (e := .var) (Subst₀.lift (e := .var) σ)))
      (ξ₂ := Ren.liftN ps.length (Ren.weaken (e := .var)))
      (Subst₀.liftN_rename_comm_of ps.length (fun _ => rfl)) b).symm
    show _ = Term.recursor r "Pair" _ _ _
      (Prelude.pairArgs (A.subst₀ σ) ((Θ.subst₀ (Subst₀.lift σ)).pack κs.tail l)) (u.subst₀ σ)
      (.cons 0 ((C.subst₀ σ).rename Ren.weaken) .nil)
      (.cons 2 0 (Term.unpack r (.var₀ .zero) ((Θ.subst₀ (Subst₀.lift σ)).rename Ren.weaken) κs.tail l
        ((C.subst₀ σ).rename (Ren.weakenN 2))
        ((b.subst₀ (Subst₀.liftN ps.length (Subst₀.lift σ))).rename (Ren.liftN ps.length Ren.weaken))) .nil)
    rw [h₁]
    let F := fun (X : Term k (.var :: _)) (Y : Term k (.var :: .var :: _)) =>
      Term.recursor r "Pair" [(κs.headD ⟨.type, l⟩).quality]
        [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l] [p.usage, p.requirement]
        (Prelude.pairArgs (A.subst₀ σ) ((Θ.subst₀ (Subst₀.lift σ)).pack κs.tail l)) (u.subst₀ σ)
        (.cons 0 X .nil) (.cons 2 0 Y .nil)
    refine (congrArg (fun X => F X _) h₂).trans (congrArg (F _) (h₃.trans ?_))
    rw [h₅]
    erw [h₆, h₇]
    rfl

-- ADE: none.
/-- The unpacking in the branch of a pair, at the fields `t` and `P`, is the unpacking of `P` into
the term at `t`. -/
theorem Term.unpack_branch_instantiate (r : Grade) {Γ : Scope} {p : Parameter} {ps : List Parameter}
    (t P : Term k Γ) (Θ : Telescope k (.var :: Γ) ps) (κs : List (Universe k)) (l : Level k)
    (C : Term k Γ) (b : Term k (Scope.extend (.var :: Γ) ps.length)) :
    (Term.unpack r (.var₀ .zero) (Θ.rename Ren.weaken) κs l (C.rename (Ren.weakenN 2))
      (b.rename (Ren.liftN ps.length Ren.weaken))).instantiate
        (ps := [p, ⟨Grade.one, Grade.one⟩]) (.cons t (.cons P .nil)) =
      Term.unpack r P (Θ.subst₀ (Subst₀.single t)) κs l C
        (b.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) := by
  show ((Term.unpack r (.var₀ .zero) (Θ.rename Ren.weaken) κs l (C.rename (Ren.weakenN 2))
      (b.rename (Ren.liftN ps.length Ren.weaken))).subst₀ (Subst₀.lift (Subst₀.single t))).subst₀
        (Subst₀.single P) = _
  have h₁ := (Telescope.subst₀_rename_comm_of (σ₁ := Subst₀.single t)
    (ξ₁ := Ren.weaken (e := .var)) (σ₂ := Subst₀.lift (e := .var) (Subst₀.single t))
    (ξ₂ := Ren.weaken (e := .var)) (fun _ => rfl) Θ).symm
  have h₂ : (C.rename (Ren.weakenN 2)).subst₀ (Subst₀.lift (e := .var) (Subst₀.single t)) =
      C.rename Ren.weaken :=
    (Term.subst₀_rename_of (σ := Subst₀.lift (e := .var) (Subst₀.single t)) (ξ := Ren.weakenN 2)
      (σ' := fun x => .var (Ren.weaken x)) (fun _ => rfl) C).trans
      (Term.subst₀_eq_rename_of (fun _ => rfl) C)
  have h₃ := (Term.subst₀_rename_comm_of (σ₁ := Subst₀.liftN ps.length (Subst₀.single t))
    (ξ₁ := Ren.liftN ps.length (Ren.weaken (e := .var)))
    (σ₂ := Subst₀.liftN ps.length (Subst₀.lift (e := .var) (Subst₀.single t)))
    (ξ₂ := Ren.liftN ps.length (Ren.weaken (e := .var)))
    (Subst₀.liftN_rename_comm_of ps.length (fun _ => rfl)) b).symm
  have h₄ : ((Θ.subst₀ (Subst₀.single t)).rename Ren.weaken).subst₀ (Subst₀.single P) =
      Θ.subst₀ (Subst₀.single t) :=
    (Telescope.subst₀_rename_of (σ := Subst₀.single P) (ξ := Ren.weaken) (σ' := Subst₀.id)
      (fun _ => rfl) _).trans
      (Telescope.subst₀_id_of (σ := Subst₀.id) (fun _ => rfl) _)
  have h₅ : ((b.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))).rename
      (Ren.liftN ps.length Ren.weaken)).subst₀ (Subst₀.liftN ps.length (Subst₀.single P)) =
      b.subst₀ (Subst₀.liftN ps.length (Subst₀.single t)) :=
    (Term.subst₀_rename_of (σ := Subst₀.liftN ps.length (Subst₀.single P))
      (ξ := Ren.liftN ps.length Ren.weaken) (σ' := Subst₀.liftN ps.length Subst₀.id)
      (Subst₀.liftN_rename_of ps.length (fun _ => rfl)) _).trans
      (Term.subst₀_id_of (Subst₀.liftN_id_of ps.length (fun _ => rfl)) _)
  rw [Term.unpack_subst₀, h₁]
  erw [h₂, h₃]
  rw [Term.unpack_subst₀, h₄, Term.subst₀_single_rename_weaken]
  erw [h₅]
  rfl

end Sic.Core
