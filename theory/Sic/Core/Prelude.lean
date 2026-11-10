module

public import Sic.Core.Typing.Substitution

/-!
# Prelude

The prelude of annex 17 of RFC 36: three type declarations that the type system uses for its own
needs, the unit `Unit`, the pair `Pair` and the type of positions `Step`, the packing `⟨Θ⟩` of a
telescope into nested pairs and the packing `⟨t̄⟩` of its arguments, with the formation of the
prelude and the typing, the usage and the ownership of the packings.

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

/-! ## Formation -/

/-- A sort is a term of the universe above its level, in a well-formed context. -/
theorem HasType.sort {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ}
    (hctx : WfCtx sig ctx) : (κ : Universe k) →
      HasType sig ctx (.sort κ) (.sort ⟨.type, .succ κ.level⟩)
  | ⟨.type, _⟩ => .univ hctx
  | ⟨.prop, _⟩ => .prop hctx

/-- A term of a sort is a type. -/
theorem WfType.ofSort {sig : Signature} {k : Nat} {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ} :
    {κ : Universe k} → HasType sig ctx A (.sort κ) → WfType sig ctx A
  | ⟨.type, _⟩, h => .univType h
  | ⟨.prop, _⟩, h => .propType h

/-- The unit is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.unit {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.unit :=
  .data (Ts := _) rfl ⟨⟨Fin.elim0, Fin.elim0⟩, trivial⟩ (fun _ _ => .empty h)
    (fun _ _ T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      obtain _ | ⟨_, ⟨⟩⟩ := hc
      exact .nil (.empty h))
    (fun ι _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      exact ⟨_, .cons .nil .nil, fun x => x.elim0⟩)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.unit] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The parameters of the pair form a context, whatever the sort of `A`. -/
theorem WfCtx.pairParams {sig : Signature} (h : WfSig sig) (ι : Instance 1 2) :
    WfCtx sig (Prelude.pair.params ι) := by
  have hA : WfCtx sig (Context.empty.var (.sort ⟨ι.sorts 0, .var 0⟩) : Context 2 [.var]) :=
    .var (WfType.ofSort (HasType.sort (.empty h) _))
  have hx := WfCtx.var (WfType.ofSort (HasType.var hA .zero))
  exact .secondOrder (WfType.ofSort (HasType.sort hx ⟨.type, .var 1⟩)) (.inl rfl)

/-- The pair is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.pair {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.pair :=
  .data (Ts := _) rfl ⟨⟨fun _ => .type, fun _ => Grade.zero⟩, fun h => nomatch h⟩
    (fun ι _ => WfCtx.pairParams h ι)
    (fun ι hι T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      obtain _ | ⟨_, ⟨⟩⟩ := hc
      have hctx := WfCtx.pairParams h ι
      have hA : HasType sig (Prelude.pair.params ι) (.var₀ (.succ .zero))
          (.sort ⟨ι.sorts (0 : Fin 1), .var (0 : Fin 2)⟩) :=
        .var hctx (.succSecondOrder .zero)
      have hx := WfCtx.var (WfType.ofSort hA)
      have hB : HasType sig ((Prelude.pair.params ι).var (.var₀ (.succ .zero)))
          (.var (.succ .zero) (.cons (.var₀ .zero) .nil)) (.sort ⟨.type, .var (1 : Fin 2)⟩) :=
        .secondOrder (.succVar .zero) (.cons (.var hx .zero) (.nil hx))
      exact .cons rfl hA ⟨fun h => (by cases h), fun _ => (by simp [Prelude.pair, Level.value]; omega)⟩
        (.cons rfl hB ⟨fun h => (by cases h), fun _ => (by simp [Prelude.pair, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hB))) nofun)
        hι)
    (fun (ι : Instance 1 2) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.pairMk) (.cons (δ := (𝟘ᶜ ∙ Grade.zero) ∙ Grade.one)
        (Usage.var .nil) (.sub (.cons (δ := 𝟘ᶜ) (Usage.var (.cons (Usage.var .nil) .nil))
          (.sub .nil ?_)) ?_)) .nil, ?_⟩
      all_goals
        intro x
        try simp only [Prelude.pairType]
        generalize ι.grades 0 = p
        generalize ι.grades 1 = ρ
        revert x p ρ
        decide)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The parameters of the type of positions form a context, whatever the sort of `B`. -/
theorem WfCtx.stepParams {sig : Signature} (h : WfSig sig) (ι : Instance 1 2) :
    WfCtx sig (Prelude.step.params ι) := by
  have hS : WfCtx sig (Context.empty.var (.sort ⟨.type, .var 0⟩) : Context 2 [.var]) :=
    .var (WfType.ofSort (HasType.sort (.empty h) _))
  exact .var (WfType.ofSort (HasType.sort hS ⟨ι.sorts 0, .var 1⟩))

/-- The type of positions is well formed in every well-formed signature. -/
theorem WfTypeDeclaration.step {sig : Signature} (h : WfSig sig) :
    WfTypeDeclaration sig Prelude.step :=
  .data (Ts := _) rfl ⟨⟨fun _ => .type, fun _ => Grade.zero⟩, fun h => nomatch h⟩
    (fun ι _ => WfCtx.stepParams h ι)
    (fun ι hι T hT c hc => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      have hctx := WfCtx.stepParams h ι
      obtain _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩ := hc
      · have hS : HasType sig (Prelude.step.params ι) (.var₀ (.succ .zero))
            (.sort ⟨.type, .var (0 : Fin 2)⟩) :=
          .var hctx (.succVar .zero)
        exact .cons rfl hS ⟨fun h => (by cases h), fun _ => (by simp [Prelude.step, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hS))) nofun
      · have hT : HasType sig (Prelude.step.params ι) (.var₀ .zero)
            (.sort ⟨ι.sorts (0 : Fin 1), .var (1 : Fin 2)⟩) :=
          .var hctx .zero
        exact .cons rfl hT ⟨fun h => (by cases h), fun _ => (by simp [Prelude.step, Level.value]; omega)⟩
          (.nil (.var (WfType.ofSort hT))) hι)
    (fun (ι : Instance 1 2) _ T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      refine ⟨_, .cons (c := Prelude.stepNext) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_))
        (.cons (c := Prelude.stepDone) (.cons (δ := 𝟘ᶜ) (Usage.var .nil) (.sub .nil ?_)) .nil), ?_⟩
      all_goals
        intro x
        try simp only [Prelude.stepType]
        generalize ι.grades 0 = r
        generalize ι.grades 1 = p
        revert x r p
        decide)
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.step] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The prelude is a well-formed signature.
RFC: `\mathsf{prelude}_{\vdash}` -/
theorem WfSig.prelude : WfSig Signature.prelude :=
  have hu : WfSig [.typeDeclaration Prelude.unit] :=
    .typeDeclaration (.unit .empty) (by decide) nofun
  have hp : WfSig [.typeDeclaration Prelude.pair, .typeDeclaration Prelude.unit] :=
    .typeDeclaration (.pair hu) (by decide) (by decide)
  .typeDeclaration (.step hp) (by decide) (by decide)

/-- `Σ ∋ prelude`: the signature holds the declarations of the prelude.
RFC: `\mathsf{prelude}_\in` -/
def Signature.HasPrelude (sig : Signature) : Prop := ∀ e ∈ Signature.prelude, e ∈ sig

/-- The prelude holds its own declarations. -/
theorem Signature.hasPrelude_prelude : Signature.prelude.HasPrelude := fun _ h => h

/-! ## Packing -/

variable {k : Nat}

-- ADE: none.
/-- `Σ; Γ ⊢ Θ : κ̄ ≤ l`: the types of the telescope `Θ` live in the sorts `κ̄`, one for each entry,
whose levels are below `l`, and an entry whose type is a proposition has a grade without use at run
time, as in a telescope in a sort; the packing of `Θ` needs the sort of each entry, which the
telescope does not give. -/
inductive WfTelescopeSorts : Signature → {Γ : Scope} → {ps : List Parameter} → Context k Γ →
    Telescope k Γ ps → List (Universe k) → Level k → Prop where
  /-- The empty telescope, of no sort, below every level.
  RFC: `\mathsf{tel}_{\bar\kappa\varepsilon}` -/
  | nil {sig : Signature} {Γ : Scope} {ctx : Context k Γ} {l : Level k} (hctx : WfCtx sig ctx) :
      WfTelescopeSorts sig ctx .nil [] l
  /-- The first entry, whose type lives in the sort `κ` of a level below `l`, with a grade without
  use at run time if it is a proposition, and the others.
  RFC: `\mathsf{tel}_{\bar\kappa,}` -/
  | cons {sig : Signature} {Γ : Scope} {ps : List Parameter} {ctx : Context k Γ} {q : Grade}
      {p : Parameter} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps} {κ : Universe k}
      {κs : List (Universe k)} {l : Level k} (hA : HasType sig ctx A (.sort κ))
      (hl : κ.level ≤ l) (hΘ : WfTelescopeSorts sig (ctx.var A) Θ κs l)
      (hp : κ.quality = .prop → p.usage.mode ≠ .oneOne) :
      WfTelescopeSorts sig ctx (.cons q p A Θ) (κ :: κs) l

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
/-- The arguments `(A, x. B)` are arguments of the parameters of the pair, when `A` is a type of the
sort `κ` and `B` a type of `U_{l₂}` over a variable of `A`. -/
theorem HasInstanceArgs.pair {Γ : Scope} {ctx : Context k Γ} {A : Term k Γ}
    {B : Term k (.var :: Γ)} {κ : Universe k} {l₂ : Level k} (p r : Grade)
    (hA : HasType sig ctx A (.sort κ)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩)) :
    HasInstanceArgs sig ctx (Prelude.pairArgs A B)
      ((Prelude.pair.params (.ofLists [κ.quality] [p, r] rfl rfl)).substLevels
        ([κ.level, l₂].getFin rfl)) := by
  show HasInstanceArgs sig _ (Prelude.pairArgs A B)
    ((Context.empty.var (.sort κ)).secondOrder
      (.cons .unrestrictedUnrestricted ⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩
        (.var₀ .zero) .nil)
      (.sort ⟨.type, l₂⟩) Prelude.pairOwnership)
  have has : HasInstanceArgs sig _ (.snoc (e := .var) .nil A) (Context.empty.var (.sort κ)) :=
    .var (.nil (contextPresuppositions.hasType hA)) hA
  exact .secondOrder (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩])
    (Θ := .cons .unrestrictedUnrestricted ⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩
      (.var₀ .zero) .nil)
    (A := .sort ⟨.type, l₂⟩) has hB

-- ADE: none.
/-- `Pair.{s; l₁, l₂; p, r} (A, x. B)`: the instance of the pair at the sort `κ = s_{l₁}`. -/
abbrev Prelude.pairInst {Γ : Scope} (κ : Universe k) (l₂ : Level k) (p r : Grade) (A : Term k Γ)
    (B : Term k (.var :: Γ)) : Term k Γ :=
  .inst "Pair" [κ.quality] [κ.level, l₂] [p, r] (Prelude.pairArgs A B)

-- ADE: `ΠΣⱼ`, in `Definition/Typed.agda`.
/-- An instance of the pair is a type of the universe of the join of its levels. -/
theorem HasType.pairInst {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {κA : Universe k}
    {l₂ : Level k} {p ρ : Grade} {A : Term k Γ} {B : Term k (.var :: Γ)}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩)) :
    HasType sig ctx (Prelude.pairInst κA l₂ p ρ A B) (.sort ⟨.type, .max κA.level l₂⟩) :=
  .inst (D := "Pair") (decl := Prelude.pair) (ζ := Prelude.pairType.usage)
    ⟨hpre _ (by simp [Signature.prelude]), .inl ⟨_, List.mem_singleton_self _, rfl, rfl⟩⟩
    rfl rfl rfl hadm (HasInstanceArgs.pair p ρ hA hB)

-- ADE: none.
/-- The packing of a telescope is a type of the universe of the level of its packing.
RFC: `\mathsf{pack}_{\Theta:}` -/
theorem HasType.packLevel {sig : Signature} (hpre : sig.HasPrelude) {Γ : Scope}
    {ps : List Parameter} {ctx : Context k Γ} {Θ : Telescope k Γ ps} {κs : List (Universe k)}
    {l : Level k} (h : WfTelescopeSorts sig ctx Θ κs l) :
    HasType sig ctx (Θ.pack κs l) (.sort ⟨.type, Telescope.packLevel κs l⟩) := by
  induction h with
  | nil hctx =>
    refine .inst (D := "Unit") (decl := Prelude.unit) (ζ := Prelude.unitType.usage)
      ⟨hpre _ (by simp [Signature.prelude]), .inl ⟨_, List.mem_singleton_self _, rfl, rfl⟩⟩
      rfl rfl rfl trivial ?_
    exact .nil hctx
  | cons hA _ _ hp ih => exact HasType.pairInst hpre hp hA ih

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

variable {Base : ∀ {Γ Δ : Scope}, Context k Γ → Subst k Γ Δ → Context k Δ → Prop}

-- ADE: none.
/-- A telescope whose entries live in sorts, substituted by a lifted substitution of a family that
`Subst.Liftable` accepts, lives in the sorts. -/
theorem WfTelescopeSorts.subst (hB : Subst.Liftable sig @Base) {Γ Δ : Scope} {ps : List Parameter}
    {ctx' : Context k Γ} {θ : Subst k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps}
    {κs : List (Universe k)} {l : Level k} :
    WfTelescopeSorts sig ctx Θ κs l → Subst.Lifted @Base ctx' @θ ctx → WfCtx sig ctx' →
      WfTelescopeSorts sig ctx' (Θ.subst θ) κs l
  | .nil _, _, hctx => .nil hctx
  | .cons hA hl hΘ hp, hθ, hctx =>
    have hA' := hB.stable.hasType hA hθ
    .cons hA' hl (WfTelescopeSorts.subst hB hΘ (hθ.var _) (.var (WfType.ofSort hA'))) hp

-- ADE: none.
/-- A telescope whose entries live in sorts, renamed by a typed renaming, lives in the sorts. -/
theorem WfTelescopeSorts.rename {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
    {ξ : Ren Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κs : List (Universe k)}
    {l : Level k} (h : WfTelescopeSorts sig ctx Θ κs l) (hξ : TypedRen sig ctx' ξ ctx) :
    WfTelescopeSorts sig ctx' (Θ.rename ξ) κs l := by
  rw [Telescope.rename_eq_subst]
  exact h.subst TypedRen.liftable (.base ⟨_, hξ, fun _ => rfl⟩) hξ.wfCtx

-- ADE: none.
/-- A telescope whose entries live in sorts, substituted by a typed substitution of the first order,
lives in the sorts. -/
theorem WfTelescopeSorts.subst₀ {Γ Δ : Scope} {ps : List Parameter} {ctx' : Context k Γ}
    {σ : Subst₀ k Γ Δ} {ctx : Context k Δ} {Θ : Telescope k Δ ps} {κs : List (Universe k)}
    {l : Level k} (h : WfTelescopeSorts sig ctx Θ κs l) (hσ : TypedSubst sig ctx' σ ctx) :
    WfTelescopeSorts sig ctx' (Θ.subst₀ σ) κs l := by
  rw [Telescope.subst₀_eq_subst]
  exact h.subst TypedSubst.liftable (.base ⟨_, hσ, rfl⟩) hσ.wfCtx

-- ADE: `prodⱼ` and `starⱼ`, in `Definition/Typed.agda`.
/-- The packing of arguments of a telescope whose entries live in sorts is a term of the packing of
the telescope.
RFC: `\mathsf{pack}_{\bar t:}` -/
theorem HasType.packArgs (hpre : sig.HasPrelude) : {Γ : Scope} → {ps : List Parameter} →
    {ctx : Context k Γ} → {ts : Args k Γ ps} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → WfTelescopeSorts sig ctx Θ κs l →
      HasArgs sig ctx ts Θ → HasType sig ctx (ts.pack Θ κs l) (Θ.pack κs l)
  | _, [], _, .nil, .nil, _, _, .nil hctx, _ =>
    .ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl rfl
      trivial (.nil hctx) (.nil hctx)
  | _, p :: _, _, .cons t ts, .cons _ _ A Θ, κ :: κs, l, .cons hA hl hΘ hp, .cons ht hts => by
    have hr := HasType.packArgs hpre (hΘ.subst₀ (TypedSubst.single ht)) hts
    rw [← Telescope.pack_subst₀] at hr
    have hctx := contextPresuppositions.hasType hA
    refine .ctor (con := Prelude.pairMk) (ts := .cons t (.cons (ts.pack (Θ.subst₀ (Subst₀.single t)) κs l) .nil))
      (qs := [κ.quality]) (ls := [κ.level, Telescope.packLevel κs l])
      (ps := [p.usage, p.requirement])
      hpre.pair (List.mem_singleton_self _) rfl rfl rfl hp
      (HasInstanceArgs.pair p.usage p.requirement hA (HasType.packLevel hpre hΘ)) ?_
    show HasArgs sig _ _ (.cons .unrestrictedUnrestricted ⟨p.usage, p.requirement⟩ A
      (.cons Grade.zero ⟨Grade.one, Grade.one⟩ (((Θ.pack κs l).rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)) .nil))
    rw [Prelude.pairSecond]
    exact .cons ht (.cons hr (.nil hctx))

-- ADE: none.
/-- The packing of arguments uses the variables as the arguments do: each pair uses its first term
with the grade of its entry and the rest once, and the unit uses none.
RFC: `\mathsf{pack}_{\bar t▶}` -/
theorem Usage.pack {sig : Signature} (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} :
    {ps : List Parameter} → {γ : GradeVector Γ.length} → {ts : Args k Γ ps} →
      (Θ : Telescope k Γ ps) → (κs : List (Universe k)) → (l : Level k) →
      UsageArgs sig γ m ts → Usage sig γ m (ts.pack Θ κs l)
  | [], _, .nil, .nil, _, l, .nil =>
    Usage.ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl
      .nil
  | p :: _, _, .cons t ts, .cons _ _ A Θ, κs, l, .cons (γ := γ) (δ := δ) ht hts => by
    have hr := Usage.pack hpre (Θ.subst₀ (Subst₀.single t)) κs.tail l hts
    have hm : m ⊙ Grade.one = m := by cases m <;> decide
    refine .sub (Usage.ctor (con := Prelude.pairMk)
      (ts := .cons t (.cons (ts.pack (Θ.subst₀ (Subst₀.single t)) κs.tail l) .nil))
      (qs := [(κs.headD ⟨.type, l⟩).quality]) (ps := [p.usage, p.requirement])
      hpre.pair (List.mem_singleton_self _) rfl rfl (.cons ht (.cons (hm ▸ hr) .nil))) ?_
    intro x
    show p.usage * γ x + δ x ≤ p.usage * γ x + (Grade.one * δ x + Grade.zero)
    generalize p.usage * γ x = a
    generalize δ x = b
    revert a b
    decide

-- ADE: none.
/-- The packing of arguments that satisfy the requirements of their entries is a new value, of the
ownership `11ᵖ`, as every constructor: each pair requires of its first term the requirement of its
entry, and of the rest a new value, which it is.
RFC: `\mathsf{pack}_{\bar t◀}` -/
theorem Ownership.pack {sig : Signature} (hpre : sig.HasPrelude) {Γ : Scope}
    {φ : Var Γ .var → Grade} {m : Mode} :
    {ps : List Parameter} → {ts : Args k Γ ps} → {os : List Grade} →
      (Θ : Telescope k Γ ps) → (κs : List (Universe k)) → (l : Level k) →
      OwnershipArgs sig φ m ts os → Ownership sig φ m .linearLinear (ts.pack Θ κs l)
  | [], .nil, _, .nil, _, l, .nil =>
    Ownership.ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl
      rfl .nil
  | p :: _, .cons t ts, _, .cons _ _ A Θ, κs, l, .cons ht hr hts => by
    have hm : m ⊙ Grade.one = m := by cases m <;> decide
    exact Ownership.ctor (con := Prelude.pairMk)
      (ts := .cons t (.cons (ts.pack (Θ.subst₀ (Subst₀.single t)) κs.tail l) .nil))
      (qs := [(κs.headD ⟨.type, l⟩).quality]) (ps := [p.usage, p.requirement])
      hpre.pair (List.mem_singleton_self _) rfl rfl
      (.cons ht hr (.cons (hm ▸ Ownership.pack hpre (Θ.subst₀ (Subst₀.single t)) κs.tail l hts)
        (fun _ => by decide) .nil))

end Sic.Core
