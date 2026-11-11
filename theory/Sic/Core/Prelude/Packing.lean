module

public import Sic.Core.Ownership
public import Sic.Core.Typing
public import Sic.Core.Usage
import Sic.Core.Typing.Substitution

/-!
# Packing

The properties of the packings of annex 17 of RFC 36: the packing of a telescope whose entries live
in sorts is a type of a universe, and the packing of its arguments a term of it, with their usage
and their ownership.
-/

@[expose] public section

namespace Sic.Core

variable {sig : Signature} {k : Nat}

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
