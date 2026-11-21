module

public import Sic.Core.RunTime.Relation
import Sic.Core.Soundness.Recursors.Nested

/-!
# Branches Built From a Shape at Run Time

The branches that the evaluation builds from a shape, one for each element of the shape, and the
arguments of the destructors that they lift: the variables of the arguments as terms, and arguments
related to addresses at the telescope of a lifted destructor, whose entries are used more.
None of them reads a nesting.

ADE have no nested fields.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Branches Built From a Shape -/

/-- The branch built at the index `k` from a shape is the branch of the element of the shape at this
index: without state, it binds the arguments of the lifted destructor and observes the term by the
destructor that it lifts, then gives the result of this observation, or `↯` when the destructor is
never observed at run time. -/
theorem Shape.branches_get {m : Nat} (ρ ϱ : Multiplicity) (M : Target m) (Ns : TargetBranches m) :
    (k : Nat) → (σ : Shape) → {i c : Nat} → {ρᵢ : Multiplicity} →
      {πs ϱs πs' ϱs' : Fin c → Multiplicity} → {ψ : ResultOwnership Multiplicity c} →
      {ς : Multiplicity} → {ψ₀ : ResultOwnership Multiplicity c} → {ς₀ : Multiplicity} →
      {next : Shape.Next} → {rest : Shape} →
      σ.drop k = .cons i c ρᵢ πs ϱs πs' ϱs' ψ ς ψ₀ ς₀ next rest →
      (σ.branches ρ ϱ M Ns).get k = some (.none, ⟨0, c, Fin.elim0, Fin.elim0, πs', ϱs', ψ, ς,
        if ρᵢ = .zero then .erased else
          next.body ρ ϱ
            (.obs (M.rename (TargetRen.shift m (0 + c))) i ψ₀ ς₀
              (Targets.ofVars πs ϱs (Shape.argVar m c)))
            (Ns.rename (TargetRen.shift m (0 + c)))⟩)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by
    cases h
    rfl
  | _ + 1, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, h => nomatch h
  | k + 1, .cons .., _, _, _, _, _, _, _, _, _, _, _, _, _, h =>
    Shape.branches_get ρ ϱ M Ns k _ h

/-! ## Arguments of a Built Branch -/

/-- The variables as terms, renamed, are the variables renamed, as terms. -/
theorem Targets.rename_ofVars {n n' : Nat} (α : TargetRen n' n) :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).rename α = Targets.ofVars πs ϱs (α ∘ xs)
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.rename, Targets.rename_ofVars α]
    split <;> rfl

/-- The variables as terms are stored at their multiplicities. -/
theorem Targets.multiplicities_ofVars {n : Nat} :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).multiplicities = List.ofFn πs
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.multiplicities, List.ofFn_succ,
      Targets.multiplicities_ofVars]

/-- The variables as terms are stored at their requirements. -/
theorem Targets.requirements_ofVars {n : Nat} :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) →
      (Targets.ofVars πs ϱs xs).requirements = List.ofFn ϱs
  | 0, _, _, _ => rfl
  | _ + 1, πs, ϱs, xs => by
    simp only [Targets.ofVars, Targets.requirements, List.ofFn_succ,
      Targets.requirements_ofVars]

/-- The variables as terms evaluate, in an environment whose cells bind the variables at a position
of a multiplicity other than `0` to addresses, to these addresses at these positions, and to new
addresses of `↯` at the others, in a heap that extends the first. -/
theorem Targets.evalAll_ofVars (P : Program) (ϖ : Multiplicity) {n : Nat} (E : List Nat) :
    {c : Nat} → (πs ϱs : Fin c → Multiplicity) → (xs : Fin c → Fin n) → (H : Heap) →
      (bs : Fin c → Nat) →
      (∀ k, πs k ≠ .zero → ∃ c' π, E[(xs k : Nat)]? = some c' ∧ H[c']? = some (.cell π (bs k))) →
      ∃ as H' R, EvalAll P ϖ H E (Targets.ofVars πs ϱs xs) as H' R ∧ H.Extends H' ∧
        as.length = c ∧ ∀ k : Fin c, πs k ≠ .zero → as[(k : Nat)]? = some (bs k)
  | 0, _, _, _, H, _, _ => ⟨[], H, [], .nil, List.prefix_refl _, rfl, fun k => k.elim0⟩
  | c + 1, πs, ϱs, xs, H, bs, hE => by
    by_cases h0 : πs 0 = .zero
    · obtain ⟨as, H', R, hev, hH', hl, hk'⟩ := Targets.evalAll_ofVars P ϖ E
        (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ) (H ++ [.erased])
        (fun k => bs k.succ) (fun k hk => by
          obtain ⟨c', π, h₁, h₂⟩ := hE k.succ hk
          exact ⟨c', π, h₁, Heap.Extends.getElem? (List.prefix_append _ _) h₂⟩)
      refine ⟨H.length :: as, H', [] ++ R, ?_, (List.prefix_append _ _).trans hH',
        by simp [hl], fun k hk => ?_⟩
      · simp only [Targets.ofVars, h0, ↓reduceIte]
        exact .cons .erased hev
      · cases k using Fin.cases with
        | zero => exact absurd h0 hk
        | succ k => exact hk' k hk
    · obtain ⟨c', π, h₁, h₂⟩ := hE 0 h0
      obtain ⟨as, H', R, hev, hH', hl, hk'⟩ := Targets.evalAll_ofVars P ϖ E
        (fun k => πs k.succ) (fun k => ϱs k.succ) (fun k => xs k.succ) H
        (fun k => bs k.succ) (fun k hk => hE k.succ hk)
      refine ⟨bs 0 :: as, H', [c'] ++ R, ?_, hH', by simp [hl], fun k hk => ?_⟩
      · simp only [Targets.ofVars, h0, ↓reduceIte]
        exact .cons (.var h₁ h₂) hev
      · cases k using Fin.cases with
        | zero => rfl
        | succ k => exact hk' k hk

/-! ## Arguments of a Lifted Destructor -/

section

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- Arguments related to addresses at a telescope whose entries are used more are related to them at
the telescope: the relation reads the types of the entries only, which are the same. -/
theorem RunsAsArgs.of_scale {H : Heap} (r : Grade) :
    {ps : List Parameter} → {g : Nat → Grade} → {Θ : Telescope 0 [] ps} → (ts : Args 0 [] ps) →
      (ts' : Args 0 [] (ps.map (Parameter.scale r))) → ts.terms = ts'.terms → {bs : List Nat} →
      RunsAsArgs sig ι P H g ts' bs (Θ.scale r) → RunsAsArgs sig ι P H g ts bs Θ
  | [], _, .nil, .nil, .nil, _, [], _ => trivial
  | _ :: _, _, .cons _ _ _ _, .cons t ts, .cons t' ts', h, b :: bs, hb => by
    injection h with _ h₁ h₂
    subst h₁
    obtain ⟨hb₁, hb₂⟩ := hb
    refine ⟨hb₁, RunsAsArgs.of_scale r ts ts' h₂ ?_⟩
    rw [← Telescope.scale_subst₀]
    exact hb₂
  | [], _, .nil, .nil, .nil, _, _ :: _, hb => (hb : False).elim
  | _ :: _, _, .cons _ _ _ _, .cons _ _, .cons _ _, _, [], hb => (hb : False).elim

/-- Arguments related to addresses are related to addresses that are the same at each position whose
grade is used at run time. -/
theorem RunsAsArgs.of_addrs {H : Heap} :
    {ps : List Parameter} → {g : Nat → Grade} → {ts : Args 0 [] ps} →
      {Θ : Telescope 0 [] ps} → {bs as : List Nat} → as.length = bs.length →
      (∀ l, g l ∉ Mode.oneOne.erased → as[l]? = bs[l]?) →
      RunsAsArgs sig ι P H g ts bs Θ → RunsAsArgs sig ι P H g ts as Θ
  | [], _, .nil, .nil, [], [], _, _, h => h
  | _ :: _, _, .cons _ _, .cons _ _ _ _, b :: bs, a :: as, hl, heq, h =>
    ⟨fun hg => by
      cases Option.some.inj (heq 0 hg)
      exact h.1 hg,
    RunsAsArgs.of_addrs (Nat.succ.inj hl) (fun l hg => heq (l + 1) hg) h.2⟩
  | [], _, .nil, .nil, _ :: _, _, _, _, h => (h : False).elim
  | _ :: _, _, .cons _ _, .cons _ _ _ _, [], _, _, _, h => (h : False).elim
  | [], _, .nil, .nil, [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, _, .cons _ _, .cons _ _ _ _, _ :: _, [], hl, _, _ => nomatch hl

end

end Sic.Core
