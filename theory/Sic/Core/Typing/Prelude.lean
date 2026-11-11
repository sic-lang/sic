module

public import Sic.Core.Typing
import Sic.Core.Typing.Renaming
import Sic.Core.Typing.Substitution

/-!
# Typing of the Prelude

The typing of the prelude of annex 18 of RFC 36: each of its declarations is well formed in the
declarations before it, at every instance that its constraint admits; the packing of a telescope
whose entries live in sorts is a type of a universe, and the packing of its arguments a term of it;
a term `u` of the packing `⟨Θ⟩` of a telescope, unpacked into a term `b` over the variables of `Θ`,
by a recursor on each pair, then on the unit, with a motive that does not depend on the term
unpacked, is typed, computes on the packing of arguments and is extensional.

The rules of the recursors on the pair and on the unit are the rules of the data types at the
instances of the prelude, whose premises on the block hold by computation.

ADE have no prelude: their pairs and their unit are types of the theory, which a program names, and
a program of their theory nests the eliminations of their pairs and of their unit itself.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

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
  exact .secondOrder (WfType.ofSort (HasType.sort hx ⟨.type, .var 1⟩))

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
    (fun T hT => by
      simp only [TypeDeclaration.dataTypes, Prelude.pair] at hT
      obtain _ | ⟨_, ⟨⟩⟩ := hT
      decide)

/-- The parameters of the type of positions form a context, whatever the sort of `B`. -/
theorem WfCtx.stepParams {sig : Signature} (h : WfSig sig) (ι : Instance 1 3) :
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

/-! ## Packing -/

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
theorem HasType.packLevel {sig : Signature} (hpre : sig.HasPrelude) {Γ : Scope} :
    {ps : List Parameter} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → WfTelescopeSorts sig ctx Θ κs l →
      HasType sig ctx (Θ.pack κs l) (.sort ⟨.type, Telescope.packLevel κs l⟩)
  | _, _, _, _, _, .nil hctx => by
    refine .inst (D := "Unit") (decl := Prelude.unit) (ζ := Prelude.unitType.usage)
      ⟨hpre _ (by simp [Signature.prelude]), .inl ⟨_, List.mem_singleton_self _, rfl, rfl⟩⟩
      rfl rfl rfl trivial ?_
    exact .nil hctx
  | _, _, _, _, _, .cons hA _ hΘ hp => HasType.pairInst hpre hp hA (HasType.packLevel hpre hΘ)

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
    have hr := HasType.packArgs hpre (stableUnderSubstitution.wfTelescopeSorts hΘ (TypedSubst.single ht)) hts
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

/-! ## Rules of the Pair and of the Unit -/

-- ADE: `prodrecⱼ`, in `Definition/Typed.agda`.
theorem HasType.pairRecursor {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {κA : Universe k} {l₂ : Level k}
    {p ρ r : Grade} {A t : Term k Γ} {B C : Term k (.var :: Γ)} {κ : Universe k}
    {u : Term k (.var :: .var :: Γ)}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩))
    (ht : HasType sig ctx t (Prelude.pairInst κA l₂ p ρ A B))
    (hC : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) C (.sort κ))
    (hu : HasType sig ((ctx.var A).var B) u
      (C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩])) :
    HasType sig ctx (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) t
      (.cons 0 C .nil) (.cons 2 0 #v[] u .nil)) (C.subst₀ (Subst₀.single t)) := by
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) (h' := 0) (κ := κ) hpre.pair rfl rfl rfl hadm
    (HasInstanceArgs.pair p ρ hA hB) ht rfl rfl rfl ?_ ?_ rfl ?_ ?_ (fun h => nomatch h)
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      show HasType sig ((ctx.var A).var ((B.rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)))
        u ((C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
          [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]).rename (Ren.weakenN 0))
      rw [Prelude.pairSecond]
      exact (congrArg (HasType sig ((ctx.var A).var B) u)
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `unitrecⱼ`, in `Definition/Typed.agda`.
/-- The recursor on a term of the unit, whose branch has the motive at the constructor. -/
theorem HasType.unitRecursor {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {l : Level k}
    {r : Grade} {t u : Term k Γ} {C : Term k (.var :: Γ)} {κ : Universe k}
    (ht : HasType sig ctx t (.inst "Unit" [] [l] [] .nil))
    (hC : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) C (.sort κ))
    (hu : HasType sig ctx u (C.atCtor "Unit" [] [l] [] .nil "mk" [])) :
    HasType sig ctx (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 #v[] u .nil))
      (C.subst₀ (Subst₀.single t)) := by
  refine .recursor (decl := Prelude.unit) (T := Prelude.unitType) (h' := 0) (κ := κ) hpre.unit rfl rfl
    rfl trivial (.nil (contextPresuppositions.hasType ht)) ht rfl rfl rfl ?_ ?_ rfl ?_ ?_
    (fun h => nomatch h)
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      exact (congrArg (HasType sig ctx u)
        (Term.rename_id_of (Γ := Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `prodrec-β`, in `Definition/Typed.agda`.
/-- The recursor on a pair built by its constructor is its branch at the fields. -/
theorem EqTerm.pairIota {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {κA : Universe k}
    {l₂ : Level k} {p ρ r : Grade} {A t P : Term k Γ} {B C : Term k (.var :: Γ)} {κ : Universe k}
    {u : Term k (.var :: .var :: Γ)}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩))
    (ht : HasType sig ctx t A) (hP : HasType sig ctx P (B.subst₀ (Subst₀.single t)))
    (hC : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) C (.sort κ))
    (hu : HasType sig ((ctx.var A).var B) u
      (C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩])) :
    EqTerm sig ctx (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B)
      (.ctor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        (.cons t (.cons P .nil)))
      (.cons 0 C .nil) (.cons 2 0 #v[] u .nil))
      (u.instantiate (ps := [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) (.cons t (.cons P .nil)))
      (C.subst₀ (Subst₀.single (.ctor "Pair" [κA.quality] [κA.level, l₂] [p, ρ]
        (Prelude.pairArgs A B) "mk" (.cons t (.cons P .nil))))) := by
  refine .iota (decl := Prelude.pair) (T := Prelude.pairType) (con := Prelude.pairMk) (i := 0)
    (j := 0) (κ := κ) (qs := [κA.quality]) (ls := [κA.level, l₂]) (ps := [p, ρ])
    (Cs := .cons 0 C .nil) (us := .cons 2 0 #v[] u .nil) (C := C) (u := u)
    (ts := .cons t (.cons P .nil)) hpre.pair (List.mem_singleton_self _) rfl rfl
    rfl hadm (HasInstanceArgs.pair p ρ hA hB) ?_ rfl rfl rfl rfl ?_ ?_ rfl ?_ ?_
    (fun h => nomatch h)
  · show HasArgs sig _ _ (.cons .unrestrictedUnrestricted ⟨p, ρ⟩ A
      (.cons Grade.zero ⟨Grade.one, Grade.one⟩ ((B.rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)) .nil))
    rw [Prelude.pairSecond]
    exact .cons ht (.cons hP (.nil (contextPresuppositions.hasType ht)))
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      show HasType sig ((ctx.var A).var ((B.rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)))
        u ((C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
          [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]).rename (Ren.weakenN 0))
      rw [Prelude.pairSecond]
      exact (congrArg (HasType sig ((ctx.var A).var B) u)
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `unitrec-β`, in `Definition/Typed.agda`.
/-- The recursor on the constructor of the unit is its branch. -/
theorem EqTerm.unitIota {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {l : Level k}
    {r : Grade} {u : Term k Γ} {C : Term k (.var :: Γ)} {κ : Universe k} (hctx : WfCtx sig ctx)
    (hC : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) C (.sort κ))
    (hu : HasType sig ctx u (C.atCtor "Unit" [] [l] [] .nil "mk" [])) :
    EqTerm sig ctx (.recursor r "Unit" [] [l] [] .nil (.ctor "Unit" [] [l] [] .nil "mk" .nil)
      (.cons 0 C .nil) (.cons 0 0 #v[] u .nil)) u
      (C.subst₀ (Subst₀.single (.ctor "Unit" [] [l] [] .nil "mk" .nil))) := by
  refine .iota (decl := Prelude.unit) (T := Prelude.unitType) (con := Prelude.unitMk) (i := 0)
    (j := 0) (κ := κ) (qs := []) (ls := [l]) (ps := []) (Cs := .cons 0 C .nil)
    (us := .cons 0 0 #v[] u .nil) (C := C) (u := u) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl
    rfl trivial (.nil hctx) (.nil hctx) rfl rfl rfl rfl ?_ ?_ rfl ?_ ?_ (fun h => nomatch h)
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      exact (congrArg (HasType sig ctx u)
        (Term.rename_id_of (Γ := Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: none.
/-- A term over a pair, at the constructor applied to the variables of its fields, has its type at
the constructor. -/
theorem HasType.pairAtCtor {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude)
    {κA : Universe k} {l₂ : Level k} {p ρ : Grade} {A : Term k Γ} {B e Cm : Term k (.var :: Γ)}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩))
    (he : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) e Cm) :
    HasType sig ((ctx.var A).var B)
      (e.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩])
      (Cm.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) := by
  have hctxA : WfCtx sig (ctx.var A) := .var (WfType.ofSort hA)
  have hctx₂ : WfCtx sig ((ctx.var A).var B) := .var (WfType.ofSort hB)
  have hW : TypedRen sig ((ctx.var A).var B) (Ren.weakenN 2) ctx :=
    (TypedRen.weaken hctx₂).comp (TypedRen.weaken hctxA)
  have hA₂ := stableUnderRenaming.hasType hA hW
  have hB₂ := stableUnderRenaming.hasType hB (TypedRen.lift hW (WfType.ofSort hA₂))
  have hx : HasType sig ((ctx.var A).var B) (.var₀ (.succ .zero)) (A.rename (Ren.weakenN 2)) := by
    have h := HasType.var hctx₂ (.succVar (.zero (A := A)))
    rw [Term.rename_rename_of (α₁ := Ren.weaken) (α₂ := Ren.weaken) (α₃ := Ren.weakenN 2)
      (fun _ => rfl)] at h
    exact h
  have hy : HasType sig ((ctx.var A).var B) (.var₀ .zero)
      ((B.rename (Ren.lift (Ren.weakenN 2))).subst₀ (Subst₀.single (.var₀ (.succ .zero)))) := by
    have e : (B.rename (Ren.lift (Ren.weakenN 2))).subst₀ (Subst₀.single (.var₀ (.succ .zero))) =
        B.rename Ren.weaken :=
      (Term.subst₀_rename_of (σ := Subst₀.single (.var₀ (.succ .zero)))
        (α := Ren.lift (Ren.weakenN 2))
        (σ' := fun x => Subst₀.single (.var₀ (.succ .zero)) (Ren.lift (Ren.weakenN 2) x))
        (fun _ => rfl) B).trans (Term.subst₀_eq_rename_of_eta (α := Ren.weaken) (fun x => by
          cases x <;> rfl) B)
    exact (congrArg (HasType sig ((ctx.var A).var B) (.var₀ .zero)) e).mpr (.var hctx₂ .zero)
  have hMK : HasType sig ((ctx.var A).var B)
      (.ctor "Pair" [κA.quality] [κA.level, l₂] [p, ρ]
        ((Prelude.pairArgs A B).rename (Ren.weakenN 2)) "mk"
        (Args.bound (Γ := Γ) [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]).terms)
      ((Prelude.pairInst κA l₂ p ρ A B).rename (Ren.weakenN 2)) := by
    refine .ctor (con := Prelude.pairMk) (ts := Args.bound (Γ := Γ) [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩])
      (qs := [κA.quality])
      (ls := [κA.level, l₂]) (ps := [p, ρ]) hpre.pair (List.mem_singleton_self _) rfl rfl rfl hadm
      (HasInstanceArgs.pair p ρ hA₂ hB₂) ?_
    show HasArgs sig _ _ (.cons .unrestrictedUnrestricted ⟨p, ρ⟩ (A.rename (Ren.weakenN 2))
      (.cons Grade.zero ⟨Grade.one, Grade.one⟩
        (((B.rename (Ren.lift (Ren.weakenN 2))).rename (Ren.liftN 1 Ren.weaken)).instantiate
          (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩])
          (.cons (Term.var₀ .zero) .nil)) .nil))
    rw [Prelude.pairSecond]
    exact .cons hx (.cons hy (.nil hctx₂))
  have he₂ := stableUnderRenaming.hasType he
    (TypedRen.lift hW (WfType.ofSort
      (stableUnderRenaming.hasType (HasType.pairInst hpre hadm hA hB) hW)))
  exact stableUnderSubstitution.hasType he₂ (TypedSubst.single hMK)

-- ADE: none: their weak pairs have no extensionality.
/-- A term over a pair is the recursor on the pair whose branch is the term at the constructor. -/
theorem EqTerm.pairEta {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {κA : Universe k}
    {l₂ : Level k} {p ρ r : Grade} {A t : Term k Γ} {B e Cm : Term k (.var :: Γ)} {κ : Universe k}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩))
    (ht : HasType sig ctx t (Prelude.pairInst κA l₂ p ρ A B))
    (he : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) e Cm)
    (hC : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) Cm (.sort κ)) :
    EqTerm sig ctx (e.subst₀ (Subst₀.single t))
      (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) t
        (.cons 0 Cm .nil)
        (.cons 2 0 #v[] (e.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
          [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) .nil))
      (Cm.subst₀ (Subst₀.single t)) := by
  refine .etaCtor (decl := Prelude.pair) (T := Prelude.pairType) (con := Prelude.pairMk) (i := 0)
    (j := 0) (κ := κ) (qs := [κA.quality]) (ls := [κA.level, l₂]) (ps := [p, ρ])
    (Cs := .cons 0 Cm .nil) (C := Cm) (e := e) hpre.pair rfl rfl rfl rfl hadm ?_
    (HasInstanceArgs.pair p ρ hA hB) ht he rfl rfl rfl rfl ?_ ?_ rfl ?_ ?_ (fun h => nomatch h)
  · intro R hR
    change R ∈ [none, none] at hR
    cases hR with
    | head => rfl
    | tail _ h => cases h with
      | head => rfl
      | tail _ h => cases h
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨Cm, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨_, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      show HasType sig ((ctx.var A).var ((B.rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)))
        _ ((Cm.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
          [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]).rename (Ren.weakenN 0))
      rw [Prelude.pairSecond]
      exact (congrArg (HasType sig ((ctx.var A).var B) _)
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr
        (HasType.pairAtCtor hpre hadm hA hB he)

-- ADE: `unitrec-β-η`, in `Definition/Typed.agda`.
/-- A term over the unit is the recursor on the unit whose branch is the term at the constructor. -/
theorem EqTerm.unitEta {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {l : Level k}
    {r : Grade} {t : Term k Γ} {e Cm : Term k (.var :: Γ)} {κ : Universe k}
    (ht : HasType sig ctx t (.inst "Unit" [] [l] [] .nil))
    (he : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) e Cm)
    (hC : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) Cm (.sort κ)) :
    EqTerm sig ctx (e.subst₀ (Subst₀.single t))
      (.recursor r "Unit" [] [l] [] .nil t (.cons 0 Cm .nil)
        (.cons 0 0 #v[] (e.atCtor "Unit" [] [l] [] .nil "mk" []) .nil))
      (Cm.subst₀ (Subst₀.single t)) := by
  have hctx := contextPresuppositions.hasType ht
  have hmk : HasType sig ctx (.ctor "Unit" [] [l] [] .nil "mk" .nil) (.inst "Unit" [] [l] [] .nil) :=
    .ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl rfl
      trivial (.nil hctx) (.nil hctx)
  have hu : HasType sig ctx (e.atCtor "Unit" [] [l] [] .nil "mk" [])
      (Cm.atCtor "Unit" [] [l] [] .nil "mk" []) := by
    have h := stableUnderSubstitution.hasType he (TypedSubst.single hmk)
    rw [← Term.rename_id_of (Γ := .var :: Γ) (α := Ren.lift (Ren.weakenN 0))
      (Ren.lift_id_of (fun _ => rfl)) e,
      ← Term.rename_id_of (Γ := .var :: Γ) (α := Ren.lift (Ren.weakenN 0))
      (Ren.lift_id_of (fun _ => rfl)) Cm] at h
    exact h
  refine .etaCtor (decl := Prelude.unit) (T := Prelude.unitType) (con := Prelude.unitMk) (i := 0)
    (j := 0) (κ := κ) (qs := []) (ls := [l]) (ps := []) (Cs := .cons 0 Cm .nil) (C := Cm) (e := e)
    hpre.unit rfl rfl rfl rfl trivial (fun R hR => nomatch hR) (.nil hctx) ht he rfl rfl rfl rfl ?_ ?_
    rfl ?_ ?_ (fun h => nomatch h)
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨Cm, rfl⟩
  · intro j T' C' hj hC'
    match j, hj, hC' with
    | 0, rfl, rfl => exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨_, rfl⟩
  · intro i j T' con C' R u' hi hC' hR hu'
    match i, hi, hC', hR, hu' with
    | 0, rfl, rfl, rfl, rfl =>
      exact (congrArg (HasType sig ctx _)
        (Term.rename_id_of (Γ := Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `prodrec-cong`, in `Definition/Typed.agda`.
/-- Two recursors on a pair whose branches are equal are equal. -/
theorem EqTerm.pairRecursorBranch {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude)
    {κA : Universe k} {l₂ : Level k} {p ρ r : Grade} {A t : Term k Γ} {B C : Term k (.var :: Γ)}
    {κ : Universe k} {u₁ u₂ : Term k (.var :: .var :: Γ)}
    (hadm : κA.quality = .prop → p.mode ≠ .oneOne)
    (hA : HasType sig ctx A (.sort κA)) (hB : HasType sig (ctx.var A) B (.sort ⟨.type, l₂⟩))
    (ht : HasType sig ctx t (Prelude.pairInst κA l₂ p ρ A B))
    (hC : HasType sig (ctx.var (Prelude.pairInst κA l₂ p ρ A B)) C (.sort κ))
    (hu : EqTerm sig ((ctx.var A).var B) u₁ u₂
      (C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
        [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩])) :
    EqTerm sig ctx
      (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) t
        (.cons 0 C .nil) (.cons 2 0 #v[] u₁ .nil))
      (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) t
        (.cons 0 C .nil) (.cons 2 0 #v[] u₂ .nil))
      (C.subst₀ (Subst₀.single t)) := by
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) (h' := 0) (κ := κ) (C₁ := C)
    hpre.pair rfl rfl rfl rfl hadm (EqInstanceArgs.refl (HasInstanceArgs.pair p ρ hA hB))
    (fun _ _ => rfl) (.refl ht) rfl rfl rfl rfl ?_ ?_ ?_ rfl rfl ?_ ?_
    (funext fun i => by cases i <;> rfl) ?_ (fun h => nomatch h)
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' hj
    match j, hj with
    | 0, _ => exact ⟨C, rfl⟩
  · intro j T' C₁' C₂' hj h₁ h₂
    match j, hj, h₁, h₂ with
    | 0, rfl, rfl, rfl => exact .refl hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u₁, rfl⟩
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u₂, rfl⟩
  · intro i j T' con C' R v₁ v₂ hi hC' hR hv₁ hv₂
    match i, hi, hC', hR, hv₁, hv₂ with
    | 0, rfl, rfl, rfl, rfl, rfl =>
      show EqTerm sig ((ctx.var A).var ((B.rename (Ren.liftN 1 Ren.weaken)).instantiate
        (ps := [⟨.unrestrictedUnrestricted, .unrestrictedUnrestricted⟩]) (.cons (Term.var₀ .zero) .nil)))
        u₁ u₂ ((C.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
          [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]).rename (Ren.weakenN 0))
      rw [Prelude.pairSecond]
      exact (congrArg (EqTerm sig ((ctx.var A).var B) u₁ u₂)
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (α := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

/-! ## Unpacking -/

-- ADE: none.
/-- What the unpacking of the rest of a telescope, in the branch of the pair, asks of its telescope,
of its packed term, of its motive and of its term: the premises of `(unpack:)` in the context
extended by the first entry and by the packing of the rest. -/
structure UnpackBranch (sig : Signature) {Γ : Scope} {ps : List Parameter} (ctx : Context k Γ)
    (A : Term k Γ) (Θ : Telescope k (.var :: Γ) ps) (κs : List (Universe k)) (l : Level k)
    (C : Term k Γ) (κ : Universe k) : Prop where
  /-- The rest of the telescope, renamed, lives in its sorts. -/
  tel : WfTelescopeSorts sig ((ctx.var A).var (Θ.pack κs l)) (Θ.rename Ren.weaken) κs l
  /-- The variable of the second field is a term of the packing of the rest. -/
  var : HasType sig ((ctx.var A).var (Θ.pack κs l)) (.var₀ .zero) ((Θ.rename Ren.weaken).pack κs l)
  /-- The motive, renamed, is a type of its sort. -/
  motive : HasType sig ((ctx.var A).var (Θ.pack κs l)) (C.rename (Ren.weakenN 2)) (.sort κ)
  /-- A term over the telescope that has the motive, renamed, has the motive. -/
  term : ∀ {b : Term k (Scope.extend (.var :: Γ) ps.length)},
    HasType sig ((ctx.var A).append Θ) b (C.rename (Ren.weakenN (ps.length + 1))) →
      HasType sig (((ctx.var A).var (Θ.pack κs l)).append (Θ.rename Ren.weaken))
        (b.rename (Ren.liftN ps.length Ren.weaken))
        ((C.rename (Ren.weakenN 2)).rename (Ren.weakenN ps.length))

-- ADE: none.
/-- The premises of `(unpack:)` give those of the unpacking of the rest of the telescope, in the
branch of the pair. -/
theorem UnpackBranch.of (hpre : sig.HasPrelude) {Γ : Scope} {ps : List Parameter}
    {ctx : Context k Γ} {A : Term k Γ} {Θ : Telescope k (.var :: Γ) ps}
    {κs : List (Universe k)} {l : Level k} {C : Term k Γ} {κ : Universe k}
    (hΘ : WfTelescopeSorts sig (ctx.var A) Θ κs l) (hC : HasType sig ctx C (.sort κ)) :
    UnpackBranch sig ctx A Θ κs l C κ := by
  have hB := HasType.packLevel hpre hΘ
  have hctx₂ : WfCtx sig ((ctx.var A).var (Θ.pack κs l)) := .var (WfType.ofSort hB)
  have hw := TypedRen.weaken hctx₂
  have hΘ₂ := stableUnderRenaming.wfTelescopeSorts hΘ hw
  have hu₂ : HasType sig ((ctx.var A).var (Θ.pack κs l)) (.var₀ .zero)
      ((Θ.rename Ren.weaken).pack κs l) := by
    rw [← Telescope.pack_rename]
    exact .var hctx₂ .zero
  have hC₂ : HasType sig ((ctx.var A).var (Θ.pack κs l)) (C.rename (Ren.weakenN 2)) (.sort κ) := by
    have h := stableUnderRenaming.hasType (stableUnderRenaming.hasType hC
      (TypedRen.weaken (contextPresuppositions.hasType hB))) hw
    rw [Term.rename_rename_of (α₁ := Ren.weaken) (α₂ := Ren.weaken) (α₃ := Ren.weakenN 2)
      (fun _ => rfl)] at h
    exact h
  refine ⟨hΘ₂, hu₂, hC₂, fun {b} hb => ?_⟩
  have hL := @Subst.liftN_eta_of k (.var :: .var :: Γ) (.var :: Γ) ps.length
    (Ren.toSubst Ren.weaken) Ren.weaken (fun _ => rfl)
  have hb₂ : HasType sig (((ctx.var A).var (Θ.pack κs l)).append (Θ.rename Ren.weaken))
      (b.rename (Ren.liftN ps.length Ren.weaken))
      ((C.rename (Ren.weakenN (ps.length + 1))).rename (Ren.liftN ps.length Ren.weaken)) := by
    rw [Telescope.rename_eq_subst, Term.rename_eq_subst_of hL b]
    erw [Term.rename_eq_subst_of hL (C.rename (Ren.weakenN (ps.length + 1)))]
    exact TypedRen.liftable.stable.hasType hb
      (Subst.Lifted.append Θ (.base ⟨Ren.weaken, hw, fun _ => rfl⟩))
  erw [Term.rename_rename_of (α₁ := Ren.liftN ps.length Ren.weaken)
    (α₂ := Ren.weakenN (ps.length + 1)) (α₃ := fun x => Ren.weakenN ps.length (Ren.weakenN 2 x))
    (fun x => by
      show Ren.liftN ps.length Ren.weaken (Var.weakenN ps.length x.succ) = _
      rw [Ren.liftN_weakenN]
      rfl)] at hb₂
  erw [Term.rename_rename_of (α₁ := Ren.weakenN ps.length) (α₂ := Ren.weakenN 2)
    (α₃ := fun x => Ren.weakenN ps.length (Ren.weakenN 2 x)) (fun _ => rfl)]
  exact hb₂

-- ADE: `prodrecⱼ` and `unitrecⱼ`, in `Definition/Typed.agda`, nested.
/-- The unpacking of a term of the packing of a telescope whose entries live in sorts, into a term
over the variables of the telescope, of a type that does not depend on them, has this type.
RFC: `\mathsf{unpack}_{:}` -/
theorem HasType.unpack (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} → {ps : List Parameter} →
    {ctx : Context k Γ} → {u : Term k Γ} → {Θ : Telescope k Γ ps} → {κs : List (Universe k)} →
    {l : Level k} → {C : Term k Γ} → {κ : Universe k} → {b : Term k (Γ.extend ps.length)} →
    WfTelescopeSorts sig ctx Θ κs l → HasType sig ctx u (Θ.pack κs l) →
    HasType sig ctx C (.sort κ) → HasType sig (ctx.append Θ) b (C.rename (Ren.weakenN ps.length)) →
      HasType sig ctx (Term.unpack r u Θ κs l C b) C
  | _, [], ctx, u, .nil, _, l, C, κ, b, .nil hctx, hu, hC, hb => by
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre (.nil (l := l) hctx)))))
    have h := HasType.unitRecursor (r := r) hpre hu hC' (by
      rw [Term.atCtor_rename_weaken]
      exact hb)
    rwa [Term.subst₀_single_rename_weaken] at h
  | _, _ :: ps, ctx, _, .cons q p A Θ, κA :: κs, l, C, κ, b, .cons hA hl hΘ hp, hu, hC, hb => by
    have hW : WfTelescopeSorts sig ctx (.cons q p A Θ) (κA :: κs) l := .cons hA hl hΘ hp
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre hW))))
    obtain ⟨hΘ₂, hu₂, hC₂, hb₂⟩ := UnpackBranch.of (A := A) hpre hΘ hC
    have h := HasType.pairRecursor (r := r) hpre hp hA (HasType.packLevel hpre hΘ) hu hC' (by
      rw [Term.atCtor_rename_weaken]
      exact HasType.unpack hpre r hΘ₂ hu₂ hC₂ (hb₂ hb))
    rwa [Term.subst₀_single_rename_weaken] at h

-- ADE: `prodrec-β` and `unitrec-β`, in `Definition/Typed.agda`, nested.
/-- The unpacking of the packing of arguments of the telescope is the term at the arguments.
RFC: `\mathsf{unpack}_\beta` -/
theorem EqTerm.unpackBeta (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} →
    {ps : List Parameter} → {ctx : Context k Γ} → {ts : Args k Γ ps} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → {C : Term k Γ} → {κ : Universe k} →
    {b : Term k (Γ.extend ps.length)} →
    WfTelescopeSorts sig ctx Θ κs l → HasArgs sig ctx ts Θ → HasType sig ctx C (.sort κ) →
    HasType sig (ctx.append Θ) b (C.rename (Ren.weakenN ps.length)) →
      EqTerm sig ctx (Term.unpack r (ts.pack Θ κs l) Θ κs l C b) (b.instantiate ts) C
  | _, [], ctx, .nil, .nil, _, l, C, κ, b, .nil hctx, _, hC, hb => by
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre (.nil (l := l) hctx)))))
    have h := EqTerm.unitIota (r := r) hpre hctx hC' (by
      rw [Term.atCtor_rename_weaken]
      exact hb)
    rwa [Term.subst₀_single_rename_weaken] at h
  | Γ, _ :: ps, ctx, .cons t ts, .cons q p A Θ, κA :: κs, l, C, κ, b, .cons hA hl hΘ hp,
      .cons ht hts, hC, hb => by
    have hW : WfTelescopeSorts sig ctx (.cons q p A Θ) (κA :: κs) l := .cons hA hl hΘ hp
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre hW))))
    obtain ⟨hΘ₂, hu₂, hC₂, hb₂⟩ := UnpackBranch.of (A := A) hpre hΘ hC
    have hσ := TypedSubst.single ht
    have hΘt := stableUnderSubstitution.wfTelescopeSorts hΘ hσ
    have hP := HasType.packArgs hpre hΘt hts
    rw [← Telescope.pack_subst₀] at hP
    have h := EqTerm.pairIota (r := r) hpre hp hA (HasType.packLevel hpre hΘ) ht hP hC' (by
      rw [Term.atCtor_rename_weaken]
      exact HasType.unpack hpre r hΘ₂ hu₂ hC₂ (hb₂ hb))
    rw [Term.subst₀_single_rename_weaken] at h
    erw [Term.unpack_branch_instantiate] at h
    have hbt : HasType sig (ctx.append (Θ.subst₀ (Subst₀.single t)))
        (b.subst₀ (Subst₀.liftN ps.length (Subst₀.single t))) (C.rename (Ren.weakenN ps.length)) := by
      have e : (C.rename (Ren.weakenN (ps.length + 1))).subst₀
          (Subst₀.liftN ps.length (Subst₀.single t)) = C.rename (Ren.weakenN ps.length) :=
        (Term.subst₀_rename_of (σ := Subst₀.liftN ps.length (Subst₀.single t))
          (α := Ren.weakenN (ps.length + 1)) (σ' := fun x => .var (Ren.weakenN ps.length x))
          (fun x => by
            show Subst₀.liftN ps.length (Subst₀.single t) (Var.weakenN ps.length x.succ) = _
            rw [Subst₀.liftN_weakenN]
            rfl) C).trans (Term.subst₀_eq_rename_of (fun _ => rfl) C)
      rw [← e, Telescope.subst₀_eq_subst]
      erw [Term.subst₀_liftN_eq_subst ps.length (Subst₀.single t) b,
        Term.subst₀_liftN_eq_subst ps.length (Subst₀.single t) (C.rename (Ren.weakenN (ps.length + 1)))]
      exact TypedSubst.liftable.stable.hasType hb
        (Subst.Lifted.append Θ (.base ⟨Subst₀.single t, hσ, rfl⟩))
    exact .trans h (EqTerm.unpackBeta hpre r hΘt hts hC hbt)

-- ADE: `unitrec-β-η`, in `Definition/Typed.agda`, for the unit only: their weak pairs have no
-- extensionality.
/-- A term over a term of the packing of a telescope is the unpacking of the term into the term at
the packing of the variables of the telescope.
RFC: `\mathsf{unpack}_\eta` -/
theorem EqTerm.unpackEta (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} →
    {ps : List Parameter} → {ctx : Context k Γ} → {u : Term k Γ} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → {C : Term k Γ} → {κ : Universe k} →
    {e : Term k (.var :: Γ)} →
    WfTelescopeSorts sig ctx Θ κs l → HasType sig ctx u (Θ.pack κs l) →
    HasType sig ctx C (.sort κ) → HasType sig (ctx.var (Θ.pack κs l)) e (C.rename Ren.weaken) →
      EqTerm sig ctx (e.subst₀ (Subst₀.single u)) (Term.unpack r u Θ κs l C (e.atPack Θ κs l)) C
  | _, [], ctx, u, .nil, _, l, C, κ, e, .nil hctx, hu, hC, he => by
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre (.nil (l := l) hctx)))))
    have h := EqTerm.unitEta (r := r) hpre hu he hC'
    rw [Term.subst₀_single_rename_weaken] at h
    exact h
  | Γ, _ :: ps, ctx, u, .cons q p A Θ, κA :: κs, l, C, κ, e, .cons hA hl hΘ hp, hu, hC, he => by
    have hW : WfTelescopeSorts sig ctx (.cons q p A Θ) (κA :: κs) l := .cons hA hl hΘ hp
    have hC' := stableUnderRenaming.hasType hC
      (TypedRen.weaken (.var (WfType.ofSort (HasType.packLevel hpre hW))))
    have hB := HasType.packLevel hpre hΘ
    obtain ⟨hΘ₂, hu₂, hC₂, _⟩ := UnpackBranch.of (A := A) hpre hΘ hC
    have hctx₂ : WfCtx sig ((ctx.var A).var (Θ.pack κs l)) := .var (WfType.ofSort hB)
    have hw := TypedRen.weaken hctx₂
    have he' := HasType.pairAtCtor hpre hp hA hB he
    rw [Term.atCtor_rename_weaken] at he'
    have he'' := stableUnderRenaming.hasType he'
      (TypedRen.lift hw (WfType.ofSort (stableUnderRenaming.hasType hB hw)))
    rw [Telescope.pack_rename] at he''
    erw [Term.rename_rename_of (α₁ := Ren.lift (Ren.weaken (e := .var)))
      (α₂ := Ren.weakenN (Γ := Γ) 2) (α₃ := fun x => x.succ.succ.succ) (fun _ => rfl),
      ← Term.rename_rename_of (α₁ := Ren.weaken (e := .var)) (α₂ := Ren.weakenN (Γ := Γ) 2)
        (α₃ := fun x => x.succ.succ.succ) (fun _ => rfl)] at he''
    have ih := EqTerm.unpackEta hpre r hΘ₂ hu₂ hC₂ he''
    erw [Term.subst₀_single_zero_rename_lift_weaken, Term.atPack_pair] at ih
    have h₁ := EqTerm.pairEta (r := r) hpre hp hA hB hu he hC'
    have h₂ := EqTerm.pairRecursorBranch (r := r) hpre hp hA hB hu hC' (by
      rw [Term.atCtor_rename_weaken]
      exact ih)
    have h := h₁.trans h₂
    rw [Term.subst₀_single_rename_weaken] at h
    exact h

end Sic.Core
