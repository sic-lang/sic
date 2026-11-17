module

public import Sic.Core.Erasure.Nested
public import Sic.Core.Erasure.Ownership
import Sic.Core.Erasure.Ownership.Renaming

/-!
# Ownership of the Corecursors of the Nested Results

The corecursor that the evaluation builds for a nested result, in `Sic/Core/Erasure/Nested.lean`,
has the ownership `1` of a new value, when the branches of the recursor have their ownerships, the
shape has the ownerships `ς` and `χ` of the branches and meets the requirements of the recursions,
and the variable of the field, seen at `ς`, keeps the ownership `o` of the term of each level of the
recursion: each built branch sees the scope at `ς · φ`, observes the path from the field, whose
ownership keeps `o` at each step, as the shape requires, and gives the recursor on the observation,
whose branches are checked a second time at `ς · φ` with the ownership `χ` of the result of the
lifted destructor, or the corecursor of the next lifting, a new value, whose branches see the scope
at `ς · ς · φ = ς · φ`.
At the multiplicity `0`, the recursor runs on the skeleton of the motive, of the ownership `1`,
which keeps `o` when `o ≤ 1`, as the term of a recursor on an erased term.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

namespace MultiplicityVector

-- ADE: none.
/-- The vector of a branch at a variable of the scope, shifted under the binders of the branch, is
the vector of the scope at this variable. -/
theorem extendBinders_shift {m a b : Nat} (φ : MultiplicityVector m) (πs : Fin a → Multiplicity)
    (πs' : Fin b → Multiplicity) (x : Fin m) :
    φ.extendBinders πs πs' (TargetRen.shift m (a + b) x) = φ x := by
  have h₁ : ¬ ((x : Nat) + (a + b) < b) := by omega
  have h₂ : ¬ ((x : Nat) + (a + b) < a + b) := by omega
  simp only [MultiplicityVector.extendBinders, TargetRen.shift, h₁, h₂, ↓reduceDIte,
    Nat.add_sub_cancel, Fin.eta]

-- ADE: none.
/-- The vector of a built branch at the variable of an argument is the ownership of the argument. -/
theorem extendBinders_argVar {m c : Nat} (φ : MultiplicityVector m) (πs : Fin 0 → Multiplicity)
    (πs' : Fin c → Multiplicity) (k : Fin c) :
    φ.extendBinders πs πs' (Shape.argVar m c k) = πs' k := by
  have hv : (Shape.argVar m c k : Nat) = c - 1 - k := rfl
  have hk : (Shape.argVar m c k : Nat) < c := by rw [hv]; omega
  simp only [MultiplicityVector.extendBinders, hk, ↓reduceDIte]
  exact congrArg πs' (Fin.ext (show c - 1 - (Shape.argVar m c k : Nat) = k by rw [hv]; omega))

end MultiplicityVector

-- ADE: none.
/-- The scale of a shape times `ς` is `ς`, since `ς · ς = ς`. -/
theorem Shape.Next.scale_mul (ς : Multiplicity) : (next : Shape.Next) → next.scale ς * ς = ς
  | .recursor _ => by cases ς <;> rfl
  | .lifting _ => Multiplicity.mul_idem ς

-- ADE: none.
/-- The variables as terms have the ownerships `ws`, which meet the requirements of their positions,
when each variable at a position of a multiplicity other than `0` has the ownership at its
position, `↯` having every ownership. -/
theorem Targets.Ownership.ofVars {Ω : Name → Multiplicity} {n : Nat} {φ : MultiplicityVector n} :
    {c : Nat} → (πs ϱs ws : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (∀ k, πs k ≠ .zero → φ (xs k) = ws k) → (∀ k, ϱs k ≤ ws k) →
        Targets.Ownership Ω φ (List.ofFn ws) (Targets.ofVars πs ϱs xs)
  | 0, _, _, _, _, _, _ => .nil
  | _ + 1, πs, ϱs, ws, xs, hx, hϱ => by
    have hs := Targets.Ownership.ofVars (Ω := Ω) (fun k => πs k.succ) (fun k => ϱs k.succ)
      (fun k => ws k.succ) (fun k => xs k.succ) (fun k h => hx k.succ h) (fun k => hϱ k.succ)
    have hM : Target.Ownership Ω φ (ws 0) (if πs 0 = .zero then .erased else .var (xs 0)) := by
      split
      · exact .erased _
      · rename_i h
        rw [← hx 0 h]
        exact .var _
    rw [List.ofFn_succ]
    exact .cons hM (hϱ 0) hs

-- ADE: none.
/-- The branches of a recursor checked a second time, with the scope at `ς · φ` and the ownership
`χ`, have their ownerships, the scope of the second check at `ς · ς · φ = ς · φ`. -/
theorem TargetBranches.Ownership.second {Ω : Name → Multiplicity} {n : Nat}
    {φ : MultiplicityVector n} {o o' ς χ : Multiplicity} :
    {Ns : TargetBranches n} → TargetBranches.Ownership Ω φ o o' ς χ Ns →
      TargetBranches.Ownership Ω (ς ·ᶜ φ) o χ ς χ Ns
  | _, .nil => .nil
  | _, .cons _ hN' hks hNs => by
    have h : ς ·ᶜ (ς ·ᶜ φ) = ς ·ᶜ φ :=
      funext fun x => (by decide : ∀ a b : Multiplicity, a * (a * b) = a * b) ς (φ x)
    refine .cons hN' ?_ hks hNs.second
    rw [h]
    exact hN'

mutual

-- ADE: none.
/-- The branches built from a shape of the ownerships `ς` and `χ`, which meets the requirements of
the recursions at `o`, for the recursor `rec_ρ · ◀ ϱ with N̄` on the observations of the path `M`,
have their ownerships, when `M` and the branches of the recursor, checked a second time, keep `o`
with the scope at `ς · φ`: each built branch observes the path at the ownerships of its arguments,
which keeps `o`, and gives the recursor, of the ownership `χ`, or the corecursor of the next
lifting, of the ownership `1`. -/
theorem TargetCorecBranches.Ownership.branches {Ω : Name → Multiplicity}
    {ρ ϱ o ς χ : Multiplicity} (hϱ : o * ϱ = o) (hz : ρ = .zero → o ≤ .one) :
    {m : Nat} → {φ : MultiplicityVector m} → {M : Target m} → {Ns : TargetBranches m} →
      (σ : Shape) → Target.Ownership Ω (ς ·ᶜ φ) o M →
        TargetBranches.Ownership Ω (ς ·ᶜ φ) o χ ς χ Ns → σ.Uniform ς χ → σ.Requires o ς →
          TargetCorecBranches.Ownership Ω φ (σ.branches ρ ϱ M Ns)
  | _, _, _, _, .nil, _, _, _, _ => .nil
  | m, φ, M, Ns, .cons i c ρᵢ πs ϱs πs' ϱs' _ _ ψ₀ ς₀ next rest, hM, hNs,
      ⟨rfl, rfl, hnext, hrest⟩, ⟨hreq, hreqn, hreqr⟩ => by
    refine .cons (fun os v hos hv => ?_) (fun h => absurd rfl h)
      (TargetCorecBranches.Ownership.branches hϱ hz rest hM hNs hrest hreqr)
    have hv' : v = next.ownership χ := by
      rcases hv with ⟨_, hv⟩ | ⟨h, _⟩
      · rw [ResultOwnership.value_const] at hv
        exact (Option.some.inj hv).symm
      · exact absurd rfl h
    subst hv'
    show Target.Ownership Ω _ _ (if ρᵢ = .zero then .erased else _)
    by_cases hρᵢ : ρᵢ = .zero
    · simp only [hρᵢ, ↓reduceIte]
      exact .erased _
    · simp only [hρᵢ, ↓reduceIte]
      obtain ⟨hς₀, hargs⟩ := hreq hρᵢ
      obtain ⟨hϱs, v₀, hv₀, hov⟩ := hargs os hos
      -- The scope of the branch: the scope of the corecursor at `ς · φ`, then the arguments.
      have key : ∀ φb : MultiplicityVector (m + (0 + c)),
          (∀ x, φb (TargetRen.shift m (0 + c) x) = ς * φ x) →
          (∀ k, φb (Shape.argVar m c k) = os k * πs' k) →
          Target.Ownership Ω φb (next.ownership χ)
            (next.body ρ ϱ
              (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
                (Targets.ofVars πs ϱs (Shape.argVar m c)))
              (Ns.rename (TargetRen.shift m (0 + c)))) := by
        intro φb hsh harg
        have hsh' : ∀ x, (next.scale ς ·ᶜ φb) (TargetRen.shift m (0 + c) x) = (ς ·ᶜ φ) x :=
          fun x => by
            show next.scale ς * φb _ = ς * φ x
            rw [hsh x, (by decide : ∀ a b f : Multiplicity, a * (b * f) = (a * b) * f),
              next.scale_mul ς]
        have hO : Target.Ownership Ω (next.scale ς ·ᶜ φb) o
            (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
              (Targets.ofVars πs ϱs (Shape.argVar m c))) :=
          .sub (.obs (hM.rename _ hsh')
            (Targets.Ownership.ofVars πs ϱs (Shape.argOwnerships (next.scale ς) os πs ϱs πs') _
              (fun k hk => by
                show next.scale ς * φb _ = _
                rw [harg k]
                simp only [Shape.argOwnerships, hk, ↓reduceIte])
              hϱs) hv₀ hς₀) hov
        exact Target.Ownership.body hϱ hz next hO (hNs.rename _ hsh') hnext hreqn
      exact key _ (fun x => MultiplicityVector.extendBinders_shift _ _ _ x)
        (fun k => MultiplicityVector.extendBinders_argVar _ _ _ k)

-- ADE: none.
/-- The result of the observation `O` of a field, for the shape of a result of the ownerships `ς`
and `χ`, which meets the requirements of the recursions at `o`, has the ownership of the result of
the lifted destructor, when `O` and the branches of the recursor keep `o` with the scope at the scale
of the shape: the recursor on `O`, or on the skeleton of the motive at the multiplicity `0`, whose
branches are checked at `o · ϱ = o`, has the ownership `χ`, and the corecursor of the next lifting
the ownership `1`. -/
theorem Target.Ownership.body {Ω : Name → Multiplicity} {ρ ϱ o ς χ : Multiplicity}
    (hϱ : o * ϱ = o) (hz : ρ = .zero → o ≤ .one) {m : Nat} {φ : MultiplicityVector m}
    {O : Target m} {Ns : TargetBranches m} :
    (next : Shape.Next) → Target.Ownership Ω (next.scale ς ·ᶜ φ) o O →
      TargetBranches.Ownership Ω (next.scale ς ·ᶜ φ) o χ ς χ Ns → next.Uniform ς χ →
        next.Requires o ς → Target.Ownership Ω φ (next.ownership χ) (next.body ρ ϱ O Ns)
  | .recursor K, hO, hNs, _, _ => by
    have h1 : (Shape.Next.scale ς (.recursor K) ·ᶜ φ) = φ :=
      (MultiplicityVector.module Multiplicity.modality).one_smul φ
    rw [h1] at hO hNs
    show Target.Ownership Ω φ χ (.recursor ρ ϱ (if ρ = .zero then K.target else O) Ns)
    refine .recursor (o := o) ?_ (by rw [hϱ]; exact hNs)
    split
    · rename_i h
      exact .sub K.ownership (hz h)
    · exact hO
  | .lifting σ, hO, hNs, hσ, hreq =>
    .corec (os := []) .nil (TargetCorecBranches.Ownership.branches hϱ hz σ hO hNs hσ hreq)

end

-- ADE: none.
/-- `l.σ` at run time, over the scope of the recursor and the field, the variable `0`, has the
ownership `1` of a new value, when the branches of the recursor have their ownerships, of which `o`
is the ownership of the term of each level of the recursion, the shape has their ownerships `ς` and
`χ` and meets the requirements of the recursions at `o`, and the field, seen at `ς`, keeps `o`. -/
theorem Target.Ownership.nested {Ω : Name → Multiplicity} {ρ ϱ o o' ς χ : Multiplicity}
    (hϱ : o * ϱ = o) (hz : ρ = .zero → o ≤ .one) {n : Nat} {φ : MultiplicityVector n}
    {φ' : MultiplicityVector (n + 1)} (hφ : ∀ x, φ' (TargetRen.shift n 1 x) = φ x)
    (hf : o ≤ ς * φ' 0) {σ : Shape} {Ns : TargetBranches n}
    (hNs : TargetBranches.Ownership Ω φ o o' ς χ Ns) (hσ : σ.Uniform ς χ)
    (hreq : σ.Requires o ς) : Target.Ownership Ω φ' .one (Target.nested ρ ϱ σ Ns) :=
  .corec (os := []) .nil
    (TargetCorecBranches.Ownership.branches hϱ hz σ (.sub (.var 0) hf)
      (hNs.second.rename (TargetRen.shift n 1) fun x => by
        show ς * φ' _ = ς * φ x
        rw [hφ x])
      hσ hreq)

end Sic.Core
