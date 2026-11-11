module

public import Sic.Core.Ownership
public import Sic.Core.Prelude
import Sic.Core.Ownership.Renaming

/-!
# Ownership of the Prelude

The ownership of the prelude of annex 18 of RFC 36: its declarations are data types only, whose
values have the ownerships that their constructors give, and the packing of arguments, the recursors
on the pair, on the unit and on the type of positions, the unpacking of a term of a packing and the
resumption of a position, which an observation of a recursive destructor computes, have the
ownerships that their rules show.

The rules of the recursors on the pair, on the unit and on the type of positions are the rules of
the data types at the instances of the prelude, whose premises on the block hold by computation; the
resumption shows what the rules of the corecursors require of the branches of their recursive
destructors.

ADE have no prelude and no codata types, hence no positions: their pairs and their unit are types of
the theory, and a program of their theory nests the eliminations of their pairs and of their unit
itself.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Formation -/

/-- The prelude declares data types only, whose values have the ownerships that their constructors
give.
RFC: `\mathsf{prelude}_{◀}` -/
theorem OwnershipSig.prelude : OwnershipSig Signature.prelude :=
  .data (.data (.data .empty rfl) rfl) rfl

/-! ## Packing -/

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

/-! ## Recursors of the Pair, of the Unit and of the Type of Positions -/

-- ADE: none.
/-- The recursor on a term of the pair has the ownership of its branch, checked with the ownership
`o` of the term times the requirement of each field, times the grade `⌜m⌝ · r` of the recursor times
the grade of the field, for its variable. -/
theorem Ownership.pairRecursor (hpre : sig.HasPrelude) {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {q : Quality} {ls : List (Level k)} {p ρ r o p' : Grade}
    {as : InstanceArgs k Γ Prelude.pairScope} {t : Term k Γ} {C : Term k (.var :: Γ)}
    {u : Term k (.var :: .var :: Γ)} (ht : Ownership sig φ (m ⊙ r) o t)
    (hu : Ownership sig
      (Ownership.extendFields φ o (m.grade * r) [⟨p, ρ⟩, ⟨Grade.one, Grade.one⟩]) m p' u) :
    Ownership sig φ m p'
      (.recursor r "Pair" [q] ls [p, ρ] as t (.cons 0 C .nil) (.cons 2 0 #v[] u .nil)) := by
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
      (.recursor r "Unit" [] [l] [] .nil t (.cons 0 C .nil) (.cons 0 0 #v[] u .nil)) := by
  refine .recursor (decl := Prelude.unit) (T := Prelude.unitType) hpre.unit rfl rfl ht rfl ?_ ?_
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu

-- ADE: none.
/-- The recursor on a term of the type of positions has the ownership of its branches, each checked
with the ownership `o` of the term times the requirement of its field, times the grade `⌜m⌝ · r`
of the recursor times the grade of the field, for its variable. -/
theorem Ownership.stepRecursor (hpre : sig.HasPrelude) {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {q : Quality} {ls : List (Level k)} {p q' ρ r o p' : Grade}
    {as : InstanceArgs k Γ Prelude.stepScope} {t : Term k Γ} {C : Term k (.var :: Γ)}
    {u₀ u₁ : Term k (.var :: Γ)} (ht : Ownership sig φ (m ⊙ r) o t)
    (hu₀ : Ownership sig (Ownership.extendFields φ o (m.grade * r) [⟨p, Grade.one⟩]) m p' u₀)
    (hu₁ : Ownership sig (Ownership.extendFields φ o (m.grade * r) [⟨q', ρ⟩]) m p' u₁) :
    Ownership sig φ m p'
      (.recursor r "Step" [q] ls [p, q', ρ] as t (.cons 0 C .nil)
        (.cons 1 0 #v[] u₀ (.cons 1 0 #v[] u₁ .nil))) := by
  refine .recursor (decl := Prelude.step) (T := Prelude.stepType) hpre.step rfl rfl ht rfl ?_ ?_
  · intro i j T' con hi
    match i, hi with
    | 0, rfl => exact ⟨u₀, rfl⟩
    | 1, rfl => exact ⟨u₁, rfl⟩
  · intro i j T' con u' hi hu'
    match i, hi, hu' with
    | 0, rfl, rfl => exact hu₀
    | 1, rfl, rfl => exact hu₁

/-! ## Unpacking -/

-- ADE: none.
/-- The ownerships of the variables extended by those of the variables of a telescope are the same
for two ownerships `o₁` and `o₂` that give each entry the same ownership. -/
theorem Ownership.extendFields_congr {o₁ o₂ g : Grade}
    (h : ∀ p : Parameter, (o₁ * p.requirement) * (g * p.usage) =
      (o₂ * p.requirement) * (g * p.usage)) :
    {Γ : Scope} → (φ : Var Γ .var → Grade) → (ps : List Parameter) →
      Ownership.extendFields φ o₁ g ps = Ownership.extendFields φ o₂ g ps
  | _, _, [] => rfl
  | Γ, φ, p :: ps => by
    show Ownership.extendFields (Γ := .var :: Γ) _ o₁ g ps =
      Ownership.extendFields (Γ := .var :: Γ) _ o₂ g ps
    rw [Ownership.extendFields_congr h _ ps, h p]

-- ADE: none.
/-- The unpacking has the ownership of its branch, checked with the ownership `o` of its term times
the requirement of each entry of the telescope, times the grade `⌜m⌝ · r` times the grade of the
entry, for its variable: the second field of each pair requires `11ᵖ` and has the grade `11ᵖ`, and
`⌜m⌝ · r` is idempotent, so that each entry keeps the ownership `o` times its requirement times the
grade with which the branch uses it.
RFC: `\mathsf{unpack}_{◀}` -/
theorem Ownership.unpack (hpre : sig.HasPrelude) (r : Grade) : {Γ : Scope} →
    {ps : List Parameter} → {φ : Var Γ .var → Grade} → {m : Mode} → {o p' : Grade} →
    {u : Term k Γ} → {Θ : Telescope k Γ ps} → {κs : List (Universe k)} → {l : Level k} →
    {C : Term k Γ} → {b : Term k (Γ.extend ps.length)} →
    Ownership sig φ (m ⊙ r) o u →
    Ownership sig (Ownership.extendFields φ o (m.grade * r) ps) m p' b →
      Ownership sig φ m p' (Term.unpack r u Θ κs l C b)
  | _, [], _, _, _, _, _, .nil, _, _, _, _, hu, hb => Ownership.unitRecursor hpre hu hb
  | Γ, p :: ps, φ, m, o, p', u, .cons _ _ A Θ, κs, l, C, b, hu, hb => by
    let φ' : Var (.var :: .var :: Γ) .var → Grade :=
      Ownership.extendFields φ o (m.grade * r) [⟨p.usage, p.requirement⟩, ⟨Grade.one, Grade.one⟩]
    have hy : Ownership sig φ' (m ⊙ r) ((o * Grade.one) * ((m.grade * r) * Grade.one))
        (Term.var₀ (k := k) .zero) :=
      Ownership.var (φ := φ') (x := .zero)
    have hb' := ownershipStableUnderRenaming.ownership (Ren.liftN ps.length (Ren.weaken (e := .var)))
      (Ownership.extendFields_liftN (φ' := φ') (α := Ren.weaken)
        (fun | .zero => rfl | .succ _ => rfl) o (m.grade * r) ps) hb
    have hi : ∀ (m : Mode) (r o ρ q : Grade),
        (((o * Grade.one) * ((m.grade * r) * Grade.one)) * ρ) * ((m.grade * r) * q) =
          (o * ρ) * ((m.grade * r) * q) := by decide
    rw [← Ownership.extendFields_congr (fun p => hi m r o p.requirement p.usage)] at hb'
    have ih := Ownership.unpack hpre r (Θ := Θ.rename Ren.weaken) (κs := κs.tail) (l := l)
      (C := C.rename (Ren.weakenN 2)) hy hb'
    exact Ownership.pairRecursor hpre hu ih

/-! ## Resumption -/

-- ADE: none.
/-- The resumption of a position `v` of the ownership `o` has every ownership `p'` below the
ownership `11ᵖ` of the corecursor resumed, a new value, and below the ownership of the term already
built, which the recursor gives the ownership `o` times its requirement `χ`, times the grade
`⌜m⌝ · q_s` with which the branch uses it, since a position resumes the corecursor or gives a term
already built: the corecursor from the variables of the state, each of the ownership `o` times the
grade `⌜m⌝ · r` of the new state, times its requirement, times the grade with which the corecursor
uses it, has the ownership `11ᵖ` of a new value.
RFC: `\mathsf{resume}_{◀}` -/
theorem Ownership.resume (hpre : sig.HasPrelude) {Γ Δ : Scope} {ps' : List Parameter} {r : Grade}
    {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ Δ} {Ss : States k Γ} {gs : CorecBranches k Γ} {κ : Universe k}
    {χ : Grade} {S : Telescope k Γ ps'} {κs : List (Universe k)} {v : Term k Γ} {m : Mode}
    {φ : Var Γ .var → Grade} {o p' : Grade} (hv : Ownership sig φ m o v)
    (hc : Ownership sig (Ownership.extendFields φ (o * (m.grade * r)) (m.grade * r) ps') m
      .linearLinear (Term.corecAt r D qs ls ps as Ss gs ps'))
    (hp₁ : p' ≤ .linearLinear) (hp₂ : p' ≤ (o * χ) * (m.grade * Prelude.doneGrade κ.quality)) :
    Ownership sig φ m p' (Term.resume r D qs ls ps as Ss gs κ χ S κs v) := by
  have hv' : Ownership sig φ (m ⊙ Grade.one) o v := by
    have : ∀ m : Mode, m ⊙ Grade.one = m := by decide
    rw [this]; exact hv
  let φ' : Var (.var :: Γ) .var → Grade :=
    Ownership.extendFields φ o (m.grade * Grade.one) [⟨r, Grade.one⟩]
  have hx : φ' .zero = o * (m.grade * r) := by
    show (o * Grade.one) * ((m.grade * Grade.one) * r) = o * (m.grade * r)
    generalize o = a; generalize m = b; generalize r = c; revert a b c; decide
  have hy : Ownership sig φ' (m ⊙ r) (o * (m.grade * r)) (Term.var₀ (k := k) .zero) :=
    hx ▸ Ownership.var (φ := φ') (x := .zero)
  have hc' := ownershipStableUnderRenaming.ownership (Ren.liftN ps'.length (Ren.weaken (e := .var)))
    (Ownership.extendFields_liftN (φ' := φ') (α := Ren.weaken)
      (fun _ => rfl) (o * (m.grade * r)) (m.grade * r) ps') hc
  erw [Term.corecAt_rename] at hc'
  have hn := Ownership.unpack hpre r (Θ := S.rename Ren.weaken) (κs := κs)
    (l := Telescope.packLevel κs .zero)
    (C := (Term.inst D qs ls ps as).rename Ren.weaken) hy (.sub hc' hp₁)
  have hd : Ownership sig
      (Ownership.extendFields φ o (m.grade * Grade.one) [⟨Prelude.doneGrade κ.quality, χ⟩]) m p'
      (Term.var₀ (k := k) .zero) := by
    refine .sub (Ownership.var (x := .zero)) ?_
    show p' ≤ (o * χ) * ((m.grade * Grade.one) * Prelude.doneGrade κ.quality)
    have : ∀ (m : Mode) (q : Grade), (m.grade * Grade.one) * q = m.grade * q := by decide
    rw [this]; exact hp₂
  exact Ownership.stepRecursor hpre hv' hn hd

end Sic.Core
