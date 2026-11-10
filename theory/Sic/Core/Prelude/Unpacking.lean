module

public import Sic.Core.Prelude.Packing
import Sic.Core.Ownership.Renaming
import Sic.Core.Usage.Renaming

/-!
# Unpacking

The unpacking of annex 17 of RFC 36: a term `u` of the packing `⟨Θ⟩` of a telescope, unpacked into a
term `b` over the variables of `Θ`, by a recursor on each pair, then on the unit, with a motive that
does not depend on the term unpacked; its typing, its computation on the packing of arguments, its
extensionality, its usage and its ownership, derived from the rules of the recursors of the pair and
of the unit.

The rules of the recursors on the pair and on the unit are the rules of the data types at the
instances of the prelude, whose premises on the block hold by computation.

ADE have no unpacking: a program of their theory nests the eliminations of their pairs and of their
unit itself.
-/

@[expose] public section

namespace Sic.Core

variable {sig : Signature} {k : Nat}

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
      (.cons 0 C .nil) (.cons 2 0 u .nil)) (C.subst₀ (Subst₀.single t)) := by
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
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `unitrecⱼ`, in `Definition/Typed.agda`.
/-- The recursor on a term of the unit, whose branch has the motive at the constructor. -/
theorem HasType.unitRecursor {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {l : Level k}
    {r : Grade} {t u : Term k Γ} {C : Term k (.var :: Γ)} {κ : Universe k}
    (ht : HasType sig ctx t (.inst "Unit" [] [l] [] .nil))
    (hC : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) C (.sort κ))
    (hu : HasType sig ctx u (C.atCtor "Unit" [] [l] [] .nil "mk" [])) :
    HasType sig ctx (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 u .nil))
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
        (Term.rename_id_of (Γ := Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

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
      (.cons 0 C .nil) (.cons 2 0 u .nil))
      (u.instantiate (ps := [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) (.cons t (.cons P .nil)))
      (C.subst₀ (Subst₀.single (.ctor "Pair" [κA.quality] [κA.level, l₂] [p, ρ]
        (Prelude.pairArgs A B) "mk" (.cons t (.cons P .nil))))) := by
  refine .iota (decl := Prelude.pair) (T := Prelude.pairType) (con := Prelude.pairMk) (i := 0)
    (j := 0) (κ := κ) (qs := [κA.quality]) (ls := [κA.level, l₂]) (ps := [p, ρ])
    (Cs := .cons 0 C .nil) (us := .cons 2 0 u .nil) (C := C) (u := u)
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
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

-- ADE: `unitrec-β`, in `Definition/Typed.agda`.
/-- The recursor on the constructor of the unit is its branch. -/
theorem EqTerm.unitIota {Γ : Scope} {ctx : Context k Γ} (hpre : sig.HasPrelude) {l : Level k}
    {r : Grade} {u : Term k Γ} {C : Term k (.var :: Γ)} {κ : Universe k} (hctx : WfCtx sig ctx)
    (hC : HasType sig (ctx.var (.inst "Unit" [] [l] [] .nil)) C (.sort κ))
    (hu : HasType sig ctx u (C.atCtor "Unit" [] [l] [] .nil "mk" [])) :
    EqTerm sig ctx (.recursor r "Unit" [] [l] [] .nil (.ctor "Unit" [] [l] [] .nil "mk" .nil)
      (.cons 0 C .nil) (.cons 0 0 u .nil)) u
      (C.subst₀ (Subst₀.single (.ctor "Unit" [] [l] [] .nil "mk" .nil))) := by
  refine .iota (decl := Prelude.unit) (T := Prelude.unitType) (con := Prelude.unitMk) (i := 0)
    (j := 0) (κ := κ) (qs := []) (ls := [l]) (ps := []) (Cs := .cons 0 C .nil)
    (us := .cons 0 0 u .nil) (C := C) (u := u) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl
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
        (Term.rename_id_of (Γ := Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

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
    rw [Term.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := Ren.weaken) (ξ₃ := Ren.weakenN 2)
      (fun _ => rfl)] at h
    exact h
  have hy : HasType sig ((ctx.var A).var B) (.var₀ .zero)
      ((B.rename (Ren.lift (Ren.weakenN 2))).subst₀ (Subst₀.single (.var₀ (.succ .zero)))) := by
    have e : (B.rename (Ren.lift (Ren.weakenN 2))).subst₀ (Subst₀.single (.var₀ (.succ .zero))) =
        B.rename Ren.weaken :=
      (Term.subst₀_rename_of (σ := Subst₀.single (.var₀ (.succ .zero)))
        (ξ := Ren.lift (Ren.weakenN 2))
        (σ' := fun x => Subst₀.single (.var₀ (.succ .zero)) (Ren.lift (Ren.weakenN 2) x))
        (fun _ => rfl) B).trans (Term.subst₀_eq_rename_of_eta (ξ := Ren.weaken) (fun x => by
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
        (.cons 2 0 (e.atCtor "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) "mk"
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
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr
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
        (.cons 0 0 (e.atCtor "Unit" [] [l] [] .nil "mk" []) .nil))
      (Cm.subst₀ (Subst₀.single t)) := by
  have hctx := contextPresuppositions.hasType ht
  have hmk : HasType sig ctx (.ctor "Unit" [] [l] [] .nil "mk" .nil) (.inst "Unit" [] [l] [] .nil) :=
    .ctor (con := Prelude.unitMk) (ts := .nil) hpre.unit (List.mem_singleton_self _) rfl rfl rfl
      trivial (.nil hctx) (.nil hctx)
  have hu : HasType sig ctx (e.atCtor "Unit" [] [l] [] .nil "mk" [])
      (Cm.atCtor "Unit" [] [l] [] .nil "mk" []) := by
    have h := stableUnderSubstitution.hasType he (TypedSubst.single hmk)
    rw [← Term.rename_id_of (Γ := .var :: Γ) (ξ := Ren.lift (Ren.weakenN 0))
      (Ren.lift_id_of (fun _ => rfl)) e,
      ← Term.rename_id_of (Γ := .var :: Γ) (ξ := Ren.lift (Ren.weakenN 0))
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
        (Term.rename_id_of (Γ := Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

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
        (.cons 0 C .nil) (.cons 2 0 u₁ .nil))
      (.recursor r "Pair" [κA.quality] [κA.level, l₂] [p, ρ] (Prelude.pairArgs A B) t
        (.cons 0 C .nil) (.cons 2 0 u₂ .nil))
      (C.subst₀ (Subst₀.single t)) := by
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) (h' := 0) (κ := κ) (C₁ := C)
    hpre.pair rfl rfl rfl rfl hadm (EqInstanceArgs.refl (HasInstanceArgs.pair p ρ hA hB))
    (fun _ _ => rfl) (.refl ht) rfl rfl rfl rfl ?_ ?_ ?_ rfl rfl ?_ ?_ ?_ (fun h => nomatch h)
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
        (Term.rename_id_of (Γ := .var :: .var :: Γ) (ξ := Ren.weakenN 0) (fun _ => rfl) _)).mpr hu

/-! ## Packing of the Variables -/

-- ADE: none.
/-- `e[⟨x̄⟩ / z]`: the term `e`, over a term `z` of the packing of the telescope `Θ`, at the packing
of the variables of `Θ`, under them. -/
def Term.atPack {Γ : Scope} {ps : List Parameter} (e : Term k (.var :: Γ)) (Θ : Telescope k Γ ps)
    (κs : List (Universe k)) (l : Level k) : Term k (Γ.extend ps.length) :=
  (e.rename (Ren.lift (Ren.weakenN ps.length))).subst₀
    (Subst₀.single ((Args.bound ps).pack (Θ.rename (Ren.weakenN ps.length)) κs l))

-- ADE: none.
/-- The term `e` at the packing of the variables of a telescope that starts with an entry `x : A`, in
the branch of the pair of `x` and `y`, is the term `e` at the pair of `x` and of the packing of the
variables of the rest, which unpacks `y`. -/
theorem Term.atPack_pair {Γ : Scope} {p : Parameter} {ps : List Parameter} (q : Grade)
    (A : Term k Γ) (Θ : Telescope k (.var :: Γ) ps) (κA : Universe k) (κs : List (Universe k))
    (l : Level k) (e : Term k (.var :: Γ)) :
    ((e.atCtor "Pair" [κA.quality] [κA.level, Telescope.packLevel κs l] [p.usage, p.requirement]
      (Prelude.pairArgs A (Θ.pack κs l)) "mk" [⟨p.usage, p.requirement⟩, ⟨Grade.one, Grade.one⟩]).rename
        (Ren.lift (Ren.weaken (e := .var)))).atPack (Θ.rename Ren.weaken) κs l =
      (e.atPack (.cons q p A Θ) (κA :: κs) l).rename (Ren.liftN ps.length (Ren.weaken (e := .var))) := by
  -- The renaming that skips `y` and the variables of the rest, on the scope of the telescope.
  let ρ : Ren ((Scope.extend (.var :: .var :: Γ) ps.length)) Γ :=
    fun v => Var.weakenN ps.length (Var.succ (Var.succ v))
  have hρ : ∀ {a} (v : Var Γ a), Ren.liftN ps.length (Ren.weaken (e := .var))
      (Ren.weakenN (Γ := Γ) (ps.length + 1) v) = ρ v :=
    fun v => Ren.liftN_weakenN ps.length Ren.weaken v.succ
  let MK : Term k (.var :: .var :: Γ) := .ctor "Pair" [κA.quality]
    [κA.level, Telescope.packLevel κs l] [p.usage, p.requirement]
    ((Prelude.pairArgs A (Θ.pack κs l)).rename (Ren.weakenN 2)) "mk"
    (Args.bound (Γ := Γ) [⟨p.usage, p.requirement⟩, ⟨Grade.one, Grade.one⟩]).terms
  let PK' := (Args.bound (k := k) (Γ := .var :: .var :: Γ) ps).pack
    ((Θ.rename Ren.weaken).rename (Ren.weakenN ps.length)) κs l
  let PK := (Args.bound (k := k) (Γ := Γ) (p :: ps)).pack
    ((Telescope.cons q p A Θ).rename (Ren.weakenN (ps.length + 1))) (κA :: κs) l
  have hL : ((((e.rename (Ren.lift (Ren.weakenN 2))).subst₀ (Subst₀.single MK)).rename
      (Ren.lift (Ren.weaken (e := .var)))).rename (Ren.lift (Ren.weakenN ps.length))).subst₀
        (Subst₀.single PK') =
      e.subst₀ (fun x => (((Subst₀.single MK (Ren.lift (Ren.weakenN 2) x)).rename
        (Ren.lift (Ren.weaken (e := .var)))).rename (Ren.lift (Ren.weakenN ps.length))).subst₀
          (Subst₀.single PK')) := by
    let σ₁ : Subst₀ k (.var :: .var :: .var :: Γ) (.var :: .var :: .var :: Γ) := fun x =>
      (Subst₀.single MK x).rename (Ren.lift (Ren.weaken (e := .var)))
    let σ₂ : Subst₀ k (.var :: Scope.extend (.var :: .var :: Γ) ps.length)
        (.var :: .var :: .var :: Γ) := fun x =>
      (σ₁ x).rename (Ren.lift (Ren.weakenN ps.length))
    have a₁ := Term.rename_subst₀_of (σ := Subst₀.single MK)
      (ξ := Ren.lift (Ren.weaken (e := .var))) (σ' := σ₁) (fun _ => rfl)
      (e.rename (Ren.lift (Ren.weakenN 2)))
    have a₂ := Term.rename_subst₀_of (σ := σ₁) (ξ := Ren.lift (Ren.weakenN ps.length)) (σ' := σ₂)
      (fun _ => rfl) (e.rename (Ren.lift (Ren.weakenN 2)))
    have a₃ := Term.subst₀_subst₀_of (σ := σ₂) (τ := Subst₀.single PK')
      (σ' := fun x => (σ₂ x).subst₀ (Subst₀.single PK')) (fun _ => rfl)
      (e.rename (Ren.lift (Ren.weakenN 2)))
    have a₄ := Term.subst₀_rename_of (σ := fun x => (σ₂ x).subst₀ (Subst₀.single PK'))
      (ξ := Ren.lift (Ren.weakenN 2))
      (σ' := fun x => (σ₂ (Ren.lift (Ren.weakenN 2) x)).subst₀ (Subst₀.single PK')) (fun _ => rfl) e
    exact (congrArg (fun t => (t.rename (Ren.lift (Ren.weakenN ps.length))).subst₀
      (Subst₀.single PK')) a₁).trans ((congrArg (·.subst₀ (Subst₀.single PK')) a₂).trans
        (a₃.trans a₄))
  have hR : ((e.rename (Ren.lift (Ren.weakenN (ps.length + 1)))).subst₀ (Subst₀.single PK)).rename
      (Ren.liftN ps.length (Ren.weaken (e := .var))) =
      e.subst₀ (fun x => (Subst₀.single PK (Ren.lift (Ren.weakenN (ps.length + 1)) x)).rename
        (Ren.liftN ps.length (Ren.weaken (e := .var)))) := by
    exact (Term.rename_subst₀_of (σ := Subst₀.single PK)
      (ξ := Ren.liftN ps.length (Ren.weaken (e := .var)))
      (σ' := fun x => (Subst₀.single PK x).rename (Ren.liftN ps.length (Ren.weaken (e := .var))))
      (fun _ => rfl) _).trans (Term.subst₀_rename_of (fun _ => rfl) e)
  refine hL.trans ((Term.subst₀_congr (fun x => ?_) e).trans hR.symm)
  cases x with
  | succ v =>
    show Val.var (Var.weakenN ps.length v.succ.succ) =
      Val.var (Ren.liftN ps.length (Ren.weaken (e := .var)) (Ren.weakenN (ps.length + 1) v))
    rw [hρ]
  | zero =>
    show Val.term _ = Val.term _
    congr 1
    let L : Ren (Scope.extend (.var :: .var :: Γ) ps.length) (Scope.extend (.var :: Γ) ps.length) :=
      fun x => Ren.liftN ps.length (Ren.weaken (e := .var) (Γ := .var :: Γ)) x
    let W' : Ren (Scope.extend (.var :: Γ) ps.length) Γ := fun x => Ren.weakenN (ps.length + 1) x
    let s₃ : Ren (.var :: .var :: .var :: Γ) Γ := fun v => v.succ.succ.succ
    let m : Ren (.var :: Scope.extend (.var :: .var :: Γ) ps.length) Γ := fun v =>
      Ren.lift (e := .var) (Ren.weakenN (Γ := .var :: .var :: Γ) ps.length) v.succ.succ.succ
    have hA : (((A.rename (Ren.weakenN 2)).rename (Ren.lift (Ren.weaken (e := .var)))).rename
        (Ren.lift (Ren.weakenN ps.length))).subst₀ (Subst₀.single PK') = (A.rename W').rename L := by
      have e₁ : (A.rename (Ren.weakenN 2)).rename (Ren.lift (Ren.weaken (e := .var))) =
          A.rename s₃ :=
        Term.rename_rename_of (ξ₁ := Ren.lift (Ren.weaken (e := .var))) (ξ₂ := Ren.weakenN 2)
          (fun _ => rfl) A
      have e₂ : (A.rename s₃).rename (Ren.lift (Ren.weakenN ps.length)) =
          A.rename m :=
        Term.rename_rename_of (ξ₁ := Ren.lift (Ren.weakenN ps.length))
          (ξ₂ := s₃) (fun _ => rfl) A
      have e₃ : (A.rename m).subst₀
          (Subst₀.single PK') = A.rename ρ := Term.subst₀_rename_eq_rename_of (fun _ => rfl) A
      exact (congrArg (fun (t : Term k (.var :: .var :: .var :: Γ)) =>
        (t.rename (Ren.lift (Ren.weakenN ps.length))).subst₀ (Subst₀.single PK')) e₁).trans
        ((congrArg (·.subst₀ (Subst₀.single PK')) e₂).trans
          (e₃.trans (Term.rename_rename_of hρ A).symm))
    have hB : ((((Θ.pack κs l).rename (Ren.lift (Ren.weakenN 2))).rename
        (Ren.lift (Ren.lift (Ren.weaken (e := .var))))).rename
          (Ren.lift (Ren.lift (Ren.weakenN ps.length)))).subst₀ (Subst₀.lift (Subst₀.single PK')) =
        ((Θ.rename (Ren.lift W')).pack κs l).rename (Ren.lift L) := by
      have e₁ : ((Θ.pack κs l).rename (Ren.lift (Ren.weakenN 2))).rename
          (Ren.lift (Ren.lift (Ren.weaken (e := .var)))) =
          (Θ.pack κs l).rename (Ren.lift s₃) :=
        Term.rename_rename_of (Ren.lift_comp_of (ξ₁ := Ren.lift (Ren.weaken (e := .var)))
          (ξ₂ := Ren.weakenN 2) (fun _ => rfl)) _
      have e₂ : ((Θ.pack κs l).rename (Ren.lift s₃)).rename
          (Ren.lift (Ren.lift (Ren.weakenN ps.length))) =
          (Θ.pack κs l).rename (Ren.lift m) :=
        Term.rename_rename_of (Ren.lift_comp_of (ξ₁ := Ren.lift (Ren.weakenN ps.length))
          (ξ₂ := s₃) (fun _ => rfl)) _
      have e₃ : ((Θ.pack κs l).rename (Ren.lift m)).subst₀
          (Subst₀.lift (Subst₀.single PK')) = (Θ.pack κs l).rename (Ren.lift ρ) :=
        Term.subst₀_rename_eq_rename_of (fun x => by cases x <;> rfl) _
      have e₄ : ((Θ.rename (Ren.lift W')).pack κs l).rename (Ren.lift L) =
          (Θ.pack κs l).rename (Ren.lift ρ) := by
        rw [← Telescope.pack_rename]
        exact Term.rename_rename_of (Ren.lift_comp_of hρ) _
      exact (congrArg (fun (t : Term k (.var :: .var :: .var :: .var :: Γ)) =>
        (t.rename (Ren.lift (Ren.lift (Ren.weakenN ps.length)))).subst₀
          (Subst₀.lift (Subst₀.single PK'))) e₁).trans
        ((congrArg (·.subst₀ (Subst₀.lift (Subst₀.single PK'))) e₂).trans (e₃.trans e₄.symm))
    have hT : ((Θ.rename (Ren.lift W')).subst₀ (Subst₀.single (.var₀ (Var.weakenN ps.length .zero)))).rename L =
        (Θ.rename Ren.weaken).rename (Ren.weakenN ps.length) := by
      rw [Telescope.rename_subst₀_of (σ' := fun z =>
          (Subst₀.single (.var₀ (Var.weakenN ps.length .zero)) z).rename L) (fun _ => rfl),
        Telescope.subst₀_rename_of (σ' := fun z =>
          (Subst₀.single (.var₀ (Var.weakenN ps.length .zero)) (Ren.lift W' z)).rename L)
          (fun _ => rfl),
        Telescope.subst₀_eq_rename_of_eta (ξ := fun v => Var.weakenN ps.length (Ren.weaken v))
          (fun x => by
            cases x with
            | zero =>
              show Term.var₀ (Ren.liftN ps.length (Ren.weaken (e := .var) (Γ := .var :: Γ))
                (Var.weakenN ps.length .zero)) = _
              rw [Ren.liftN_weakenN]
              rfl
            | succ v =>
              show Var.eta (Ren.liftN ps.length (Ren.weaken (e := .var) (Γ := .var :: Γ))
                (Ren.weakenN (ps.length + 1) v)) = _
              rw [hρ]
              rfl),
        Telescope.rename_rename_of (ξ₁ := Ren.weakenN ps.length) (ξ₂ := Ren.weaken)
          (ξ₃ := fun v => Var.weakenN ps.length (Ren.weaken v)) (fun _ => rfl)]
    have hrest := Args.pack_rename L (Args.bound (k := k) (Γ := .var :: Γ) ps)
      ((Θ.rename (Ren.lift W')).subst₀ (Subst₀.single (.var₀ (Var.weakenN ps.length .zero)))) κs l
    rw [Args.bound_rename, hT] at hrest
    show Term.ctor _ _ _ _ _ _ _ = Term.ctor _ _ _ _ _ _ _
    congr 1
    · show InstanceArgs.snoc (.snoc .nil _) _ = InstanceArgs.snoc (.snoc .nil _) _
      congr 1
      exact congrArg (InstanceArgs.snoc (e := .var) .nil) hA
    · show Terms.cons _ (Terms.cons _ .nil) = Terms.cons _ (Terms.cons _ .nil)
      congr 1
      · show Term.var₀ (Var.weakenN ps.length (Var.succ .zero)) =
          Term.var₀ (Ren.liftN ps.length (Ren.weaken (e := .var) (Γ := .var :: Γ))
            (Var.weakenN ps.length .zero))
        rw [Ren.liftN_weakenN]
        rfl
      · congr 1
        exact hrest.symm

/-! ## Typing, Computation and Extensionality -/

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
    rw [Term.rename_rename_of (ξ₁ := Ren.weaken) (ξ₂ := Ren.weaken) (ξ₃ := Ren.weakenN 2)
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
  erw [Term.rename_rename_of (ξ₁ := Ren.liftN ps.length Ren.weaken)
    (ξ₂ := Ren.weakenN (ps.length + 1)) (ξ₃ := fun x => Ren.weakenN ps.length (Ren.weakenN 2 x))
    (fun x => by
      show Ren.liftN ps.length Ren.weaken (Var.weakenN ps.length x.succ) = _
      rw [Ren.liftN_weakenN]
      rfl)] at hb₂
  erw [Term.rename_rename_of (ξ₁ := Ren.weakenN ps.length) (ξ₂ := Ren.weakenN 2)
    (ξ₃ := fun x => Ren.weakenN ps.length (Ren.weakenN 2 x)) (fun _ => rfl)]
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
          (ξ := Ren.weakenN (ps.length + 1)) (σ' := fun x => .var (Ren.weakenN ps.length x))
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
    erw [Term.rename_rename_of (ξ₁ := Ren.lift (Ren.weaken (e := .var)))
      (ξ₂ := Ren.weakenN (Γ := Γ) 2) (ξ₃ := fun x => x.succ.succ.succ) (fun _ => rfl),
      ← Term.rename_rename_of (ξ₁ := Ren.weaken (e := .var)) (ξ₂ := Ren.weakenN (Γ := Γ) 2)
        (ξ₃ := fun x => x.succ.succ.succ) (fun _ => rfl)] at he''
    have ih := EqTerm.unpackEta hpre r hΘ₂ hu₂ hC₂ he''
    erw [Term.subst₀_single_zero_rename_lift_weaken, Term.atPack_pair] at ih
    have h₁ := EqTerm.pairEta (r := r) hpre hp hA hB hu he hC'
    have h₂ := EqTerm.pairRecursorBranch (r := r) hpre hp hA hB hu hC' (by
      rw [Term.atCtor_rename_weaken]
      exact ih)
    have h := h₁.trans h₂
    rw [Term.subst₀_single_rename_weaken] at h
    exact h

/-! ## Usage and Ownership of the Recursors of the Pair and of the Unit -/

-- ADE: `prodrecₘ`, in `Graded/Usage.agda`.
/-- The recursor on a term of the pair uses the variables of its term `r` times and those of its
branch, whose uses of the two fields cover `⌜m⌝ · r` times their grades. -/
theorem Usage.pairRecursor (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} {q : Quality}
    {ls : List (Level k)} {p ρ r g₀ g₁ : Grade} {as : InstanceArgs k Γ Prelude.pairScope}
    {t : Term k Γ} {C : Term k (.var :: Γ)} {u : Term k (.var :: .var :: Γ)}
    {γ δ : GradeVector Γ.length}
    (hC : Usage sig 𝟘ᶜ .zeroZero C) (ht : Usage sig γ (m ⊙ r) t)
    (hu : Usage (Γ := .var :: .var :: Γ) sig ((δ ∙ g₀) ∙ g₁) m u)
    (hg₀ : m.grade * r * p ≤ g₀) (hg₁ : m.grade * r * Grade.one ≤ g₁) :
    Usage sig ((r ·ᶜ γ) +ᶜ δ) m
      (.recursor r "Pair" [q] ls [p, ρ] as t (.cons 0 C .nil) (.cons 2 0 u .nil)) := by
  have hz : ∀ a b c : Grade, a ≤ b → a ≤ b + Grade.zero * c := by decide
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) (δs := fun _ => δ)
    (gs := fun _ l => if l = 0 then g₀ else g₁) (es := fun _ _ => Grade.zero) hpre.pair rfl rfl
    ?_ ht rfl ?_ ?_ ?_ ?_ ?_
  · intro j n C' hj
    match j, hj with
    | 0, hj => cases hj; exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu
  · intro i j T' con l p' hi hl
    match i, hi with
    | 0, rfl =>
      match l, hl with
      | 0, rfl => exact hz _ _ _ hg₀
      | 1, rfl => exact hz _ _ _ hg₁
  · intro i j T' con hi
    match i, hi with
    | 0, rfl =>
      intro x
      show δ x ≤ δ x + Grade.zero * δ x
      generalize δ x = a
      revert a
      decide
  · intro _ ⟨T', hT', h2⟩
    rcases hT' with _ | ⟨_, ⟨⟩⟩
    exact absurd h2 (by decide)

-- ADE: `unitrecₘ`, in `Graded/Usage.agda`.
/-- The recursor on a term of the unit uses the variables of its term `r` times and those of its
branch. -/
theorem Usage.unitRecursor (hpre : sig.HasPrelude) {Γ : Scope} {m : Mode} {l : Level k}
    {r : Grade} {t u : Term k Γ} {C : Term k (.var :: Γ)} {γ δ : GradeVector Γ.length}
    (hC : Usage sig 𝟘ᶜ .zeroZero C) (ht : Usage sig γ (m ⊙ r) t) (hu : Usage sig δ m u) :
    Usage sig ((r ·ᶜ γ) +ᶜ δ) m
      (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 u .nil)) := by
  refine .recursor (decl := Prelude.unit) (T := Prelude.unitType) (δs := fun _ => δ)
    (gs := fun _ _ => Grade.zero) (es := fun _ _ => Grade.zero) hpre.unit rfl rfl
    ?_ ht rfl ?_ ?_ ?_ ?_ ?_
  · intro j n C' hj
    match j, hj with
    | 0, hj => cases hj; exact hC
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu
  · intro i j T' con l p' hi hl
    match i, hi with
    | 0, rfl => exact nomatch hl
  · intro i j T' con hi
    match i, hi with
    | 0, rfl =>
      intro x
      show δ x ≤ δ x + Grade.zero * δ x
      generalize δ x = a
      revert a
      decide
  · intro _ ⟨T', hT', h2⟩
    rcases hT' with _ | ⟨_, ⟨⟩⟩
    exact absurd h2 (by decide)

-- ADE: none.
/-- The recursor on a term of the pair has the ownership of its branch, checked with the ownership
`o` of the term times the requirement of each field for its variable. -/
theorem Ownership.pairRecursor (hpre : sig.HasPrelude) {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {q : Quality} {ls : List (Level k)} {p ρ r o p' : Grade}
    {as : InstanceArgs k Γ Prelude.pairScope} {t : Term k Γ} {C : Term k (.var :: Γ)}
    {u : Term k (.var :: .var :: Γ)} (ht : Ownership sig φ (m ⊙ r) o t)
    (hu : Ownership sig (Ownership.extendFields φ o [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) m p' u) :
    Ownership sig φ m p'
      (.recursor r "Pair" [q] ls [p, ρ] as t (.cons 0 C .nil) (.cons 2 0 u .nil)) := by
  refine .recursor (decl := Prelude.pair) (T := Prelude.pairType) hpre.pair rfl rfl ht rfl ?_ ?_
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu

-- ADE: none.
/-- The recursor on a term of the unit has the ownership of its branch. -/
theorem Ownership.unitRecursor (hpre : sig.HasPrelude) {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {l : Level k} {r o p' : Grade} {t u : Term k Γ} {C : Term k (.var :: Γ)}
    (ht : Ownership sig φ (m ⊙ r) o t) (hu : Ownership sig φ m p' u) :
    Ownership sig φ m p'
      (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 u .nil)) := by
  refine .recursor (decl := Prelude.unit) (T := Prelude.unitType) hpre.unit rfl rfl ht rfl ?_ ?_
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu

/-! ## Usage and Ownership of the Unpacking -/

-- ADE: `prodrecₘ` and `unitrecₘ`, in `Graded/Usage.agda`, nested.
/-- The unpacking uses the variables of its term `r` times and those of its branch, which uses the
variable of each entry of the telescope `⌜m⌝ · r` times its grade; its motive, a type, uses no
variable.
RFC: `\mathsf{unpack}_{▶}` -/
theorem Usage.unpack (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} → {ps : List Parameter} →
    {m : Mode} → {γ δ : GradeVector Γ.length} → {u : Term k Γ} → {Θ : Telescope k Γ ps} →
    {κs : List (Universe k)} → {l : Level k} → {C : Term k Γ} →
    {b : Term k (Γ.extend ps.length)} →
    Usage sig 𝟘ᶜ .zeroZero C → Usage sig γ (m ⊙ r) u →
    Usage sig (δ.extendParams (m.grade * r) ps) m b →
      Usage sig ((r ·ᶜ γ) +ᶜ δ) m (Term.unpack r u Θ κs l C b)
  | _, [], _, _, _, _, .nil, _, _, _, _, hC, hu, hb => by
    have hC' := usageStableUnderRenaming.usage (Ren.weaken (e := .var)) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC'
    exact Usage.unitRecursor hpre hC' hu hb
  | Γ, p :: ps, m, γ, δ, u, .cons _ _ A Θ, κs, l, C, b, hC, hu, hb => by
    have hC₁ := usageStableUnderRenaming.usage (Ren.weaken (e := .var)) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC₁
    have hC₂ := usageStableUnderRenaming.usage (Ren.weakenN (Γ := Γ) 2) hC
    rw [GradeVector.rename_commutes.rename_zero] at hC₂
    have hb' := usageStableUnderRenaming.usage (Ren.liftN ps.length (Ren.weaken (e := .var))) hb
    erw [GradeVector.rename_extendParams (Γ := .var :: .var :: Γ) (Δ := .var :: Γ) (δ ∙ (m.grade * r * p.usage))
      (m.grade * r) ps (Ren.weaken (e := .var)), GradeVector.rename_weaken] at hb'
    have hy : Usage sig (GradeVector.update 𝟘ᶜ (Var.toFin .zero) (m ⊙ r).grade +ᶜ 𝟘ᶜ) (m ⊙ r)
        (Term.var₀ (Γ := .var :: .var :: Γ) (k := k) .zero) := .var .nil
    have ih := Usage.unpack hpre r (Θ := Θ.rename Ren.weaken) (κs := κs.tail) (l := l) hC₂ hy hb'
    have hz : ∀ r a : Grade, r * a ≤ r * (a + Grade.zero) + Grade.zero := by decide
    have hs : ∀ r c : Grade, c ≤ r * (Grade.zero + Grade.zero) + c := by decide
    have hm : ∀ (m : Mode) (r : Grade), m.grade * r * Grade.one ≤ r * (m ⊙ r).grade := by decide
    refine Usage.pairRecursor (g₁ := r * (m ⊙ r).grade) hpre hC₁ hu (.sub ih ?_) (Grade.le_refl _)
      (hm m r)
    intro y
    cases y using Fin.cases with
    | zero =>
      exact (congrArg (fun c => r * (m ⊙ r).grade ≤ r * (c + Grade.zero) + Grade.zero)
        (ite_eq_left rfl)).mpr (hz r _)
    | succ y =>
      exact (congrArg (fun c => (δ ∙ (m.grade * r * p.usage)) y ≤ r * (c + Grade.zero) +
        (δ ∙ (m.grade * r * p.usage)) y) (ite_eq_right (Fin.succ_ne_zero y))).mpr (hs r _)

-- ADE: none.
/-- The unpacking has the ownership of its branch, checked with the ownership `o` of its term times
the requirement of each entry of the telescope for its variable: the second field of each pair
requires `11ᵖ`, so that each entry keeps the ownership `o` times its requirement.
RFC: `\mathsf{unpack}_{◀}` -/
theorem Ownership.unpack (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} →
    {ps : List Parameter} → {φ : Var Γ .var → Grade} → {m : Mode} → {o p' : Grade} →
    {u : Term k Γ} → {Θ : Telescope k Γ ps} → {κs : List (Universe k)} → {l : Level k} →
    {C : Term k Γ} → {b : Term k (Γ.extend ps.length)} →
    Ownership sig φ (m ⊙ r) o u → Ownership sig (Ownership.extendFields φ o ps) m p' b →
      Ownership sig φ m p' (Term.unpack r u Θ κs l C b)
  | _, [], _, _, _, _, _, .nil, _, _, _, _, hu, hb => Ownership.unitRecursor hpre hu hb
  | Γ, p :: ps, φ, m, o, p', u, .cons _ _ A Θ, κs, l, C, b, hu, hb => by
    have h1 : o * Grade.one = o := Grade.modality.semiring.mul_one o
    let φ' : Var (.var :: .var :: Γ) .var → Grade :=
      Ownership.extendFields φ o [⟨p.usage, p.requirement⟩, ⟨Grade.one, Grade.one⟩]
    have hy₀ : Ownership sig φ' (m ⊙ r) (o * Grade.one) (Term.var₀ (k := k) .zero) :=
      Ownership.var (φ := φ') (x := .zero)
    have hy : Ownership sig φ' (m ⊙ r) o (Term.var₀ (k := k) .zero) := h1 ▸ hy₀
    have hb' := ownershipStableUnderRenaming.ownership (Ren.liftN ps.length (Ren.weaken (e := .var)))
      (Ownership.extendFields_liftN (φ' := φ') (ξ := Ren.weaken)
        (fun | .zero => rfl | .succ _ => rfl) o ps) hb
    have ih := Ownership.unpack hpre r (Θ := Θ.rename Ren.weaken) (κs := κs.tail) (l := l)
      (C := C.rename (Ren.weakenN 2)) hy hb'
    exact Ownership.pairRecursor hpre hu ih

end Sic.Core
