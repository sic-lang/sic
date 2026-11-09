module

public import Sic.Core.Soundness.Judgments

/-!
# Independence of the Judgments

The usage, the ownership and the typing of annexes 11 to 13 of RFC 36 are independent: for each of
them, a term passes the two others and fails it, its variables being declared with their types,
grades and ownerships, so that none of the three judgments follows from the two others.

The terms are `X[x, x]`, `X[x]` and `U₀`, in the empty signature: `x : U₀` is a variable, and `X` a
second-order variable whose result is a shared term of `U₀`.
A judgment that holds is derived by its rules.
A judgment that fails is refuted by inversion: the usage and the ownership through the rules
`(sub_▶)` and `(sub_◀)`, which only lower the grades, and the typing through its meaning, which
relates `U₀` to no universe.
-/

@[expose] public section

namespace Sic.Core

/-! ## The Programs -/

/-- The universe `U₀`. -/
abbrev Term.u₀ {k : Nat} {Γ : Scope} : Term k Γ := .sort ⟨.type, .zero⟩

/-- An entry used once, which requires nothing of its argument. -/
def Parameter.linear : Parameter := ⟨Grade.one, .unrestrictedUnrestricted, none⟩

/-- An entry used once, which requires its argument to be owned alone. -/
def Parameter.unique : Parameter := ⟨Grade.one, Grade.one, none⟩

/-- The scope of a variable `x` and of a second-order variable `X` whose telescope has the
parameters `ps`, and whose result is shared. -/
abbrev Scope.xX (ps : List Parameter) : Scope :=
  [.secondOrder ps (some .unrestrictedUnrestricted), .var]

/-- The context `x : U₀, X : (Θ ⊢ U₀ ◀ ωωᵖ)`. -/
def Context.xX {ps : List Parameter} (Θ : Telescope 0 [.var] ps) : Context 0 (Scope.xX ps) :=
  (Context.empty.var Term.u₀).secondOrder Θ Term.u₀ (some .unrestrictedUnrestricted)

/-- The variable `x`. -/
abbrev Var.x {ps : List Parameter} : Var (Scope.xX ps) .var := .succ .zero

/-- The second-order variable `X`. -/
abbrev Var.X {ps : List Parameter} :
    Var (Scope.xX ps) (.secondOrder ps (some .unrestrictedUnrestricted)) :=
  .zero

/-- The telescope `(y : U₀ ▶ 11ᵖ; 00ᵖ ◀ ωωᵖ, z : U₀ ▶ 11ᵖ; 00ᵖ ◀ ωωᵖ)`, of two entries used once. -/
def Telescope.twice : Telescope 0 [.var] [Parameter.linear, Parameter.linear] :=
  .cons .zero Parameter.linear Term.u₀ (.cons .zero Parameter.linear Term.u₀ .nil)

/-- The telescope `(y : U₀ ▶ 11ᵖ; 00ᵖ ◀ 11ᵖ)`, of one entry that requires its argument to be owned
alone. -/
def Telescope.once : Telescope 0 [.var] [Parameter.unique] :=
  .cons .zero Parameter.unique Term.u₀ .nil

/-- `X[x, x]`. -/
def Term.appTwice : Term 0 (Scope.xX [Parameter.linear, Parameter.linear]) :=
  .var Var.X (.cons (.var₀ Var.x) (.cons (.var₀ Var.x) .nil))

/-- `X[x]`. -/
def Term.appOnce : Term 0 (Scope.xX [Parameter.unique]) :=
  .var Var.X (.cons (.var₀ Var.x) .nil)

/-- `x ≔ 11ᵖ, X ≔ 11ᵖ`: each variable is used once. -/
def GradeVector.ones {ps : List Parameter} : GradeVector (Scope.xX ps).length := fun _ => Grade.one

/-- `x ≔ 11ᵖ`: the variable is owned alone. -/
def Ownership.alone {ps : List Parameter} : Var (Scope.xX ps) .var → Grade := fun _ => Grade.one

/-- `x ≔ ωωᵖ`: the variable is shared. -/
def Ownership.shared {ps : List Parameter} : Var (Scope.xX ps) .var → Grade :=
  fun _ => .unrestrictedUnrestricted

/-! ## Derivations -/

/-- `x : U₀` is a well-formed context. -/
theorem WfCtx.x : WfCtx [] (Context.empty.var (Term.u₀ : Term 0 []) : Context 0 [.var]) :=
  .var (.univType (.univ (.empty .empty)))

/-- `x : U₀, X : (y : U₀, z : U₀ ⊢ U₀ ◀ ωωᵖ)` is a well-formed context. -/
theorem WfCtx.xX_twice : WfCtx [] (Context.xX Telescope.twice) :=
  .secondOrder (.univType (.univ (.var (.univType (.univ (.var (.univType (.univ WfCtx.x))))))))
    (.inl rfl)

/-- `x : U₀, X : (y : U₀ ⊢ U₀ ◀ ωωᵖ)` is a well-formed context. -/
theorem WfCtx.xX_once : WfCtx [] (Context.xX Telescope.once) :=
  .secondOrder (.univType (.univ (.var (.univType (.univ WfCtx.x))))) (.inl rfl)

/-- `X[x, x]` is a term of `U₀`. -/
theorem HasType.appTwice : HasType [] (Context.xX Telescope.twice) Term.appTwice Term.u₀ := by
  have hx : HasType [] (Context.xX Telescope.twice) (.var₀ Var.x) Term.u₀ :=
    .var WfCtx.xX_twice (.succSecondOrder .zero)
  exact .secondOrder .zero (.cons hx (.cons hx (.nil WfCtx.xX_twice)))

/-- `X[x]` is a term of `U₀`. -/
theorem HasType.appOnce : HasType [] (Context.xX Telescope.once) Term.appOnce Term.u₀ := by
  have hx : HasType [] (Context.xX Telescope.once) (.var₀ Var.x) Term.u₀ :=
    .var WfCtx.xX_once (.succSecondOrder .zero)
  exact .secondOrder .zero (.cons hx (.nil WfCtx.xX_once))

/-! ## Inversions -/

/-- The grades of a variable alone give it at most the grade of the mode. -/
theorem Usage.var₀_le {sig : Signature} {k : Nat} {Γ : Scope} {m : Mode} {v : Var Γ .var} :
    ∀ {γ : GradeVector Γ.length} {t : Term k Γ}, Usage sig γ m t → t = .var₀ v →
      γ v.toFin ≤ m.grade
  | _, _, .var hts, he => by
    cases he
    cases hts
    simp only [GradeVector.add, GradeVector.update, GradeVector.zero, ite_true]
    cases m <;> decide
  | _, _, .const _ _, he => by cases he
  | _, _, .sort, he => by cases he
  | _, _, .sub h hle, he => Grade.le_trans _ _ _ (hle _) (Usage.var₀_le h he)

/-- The grades of an application `X[t̄]` are at most the grade of the mode for `X` and the uses of
its arguments. -/
theorem Usage.var_inv {sig : Signature} {k : Nat} {Γ : Scope} {m : Mode} {e : Scope.Entry}
    {X : Var Γ e} {ts : Args k Γ e.params} :
    ∀ {γ : GradeVector Γ.length} {t : Term k Γ}, Usage sig γ m t → t = .var X ts →
      ∃ δ, UsageArgs sig δ m ts ∧ γ ≤ᶜ (GradeVector.update 𝟘ᶜ X.toFin m.grade +ᶜ δ)
  | _, _, .var hts, he => by
    cases he
    exact ⟨_, hts, GradeVector.preorder.refl _⟩
  | _, _, .const _ _, he => by cases he
  | _, _, .sort, he => by cases he
  | _, _, .sub h hle, he => by
    obtain ⟨δ, hts, hδ⟩ := Usage.var_inv h he
    exact ⟨δ, hts, GradeVector.preorder.trans hle hδ⟩

/-- `X[x, x]`, checked in the mode `11ᵐ`, gives `x` at most the grade `ωωᵖ`: each argument uses `x`
with at most `11ᵖ`, and `11ᵖ + 11ᵖ = ωωᵖ`. -/
theorem Usage.appTwice_le {sig : Signature}
    {γ : GradeVector (Scope.xX [Parameter.linear, Parameter.linear]).length}
    (h : Usage sig γ .oneOne Term.appTwice) :
    γ (Var.x (ps := [Parameter.linear, Parameter.linear])).toFin ≤ .unrestrictedUnrestricted := by
  obtain ⟨δ, hts, hle⟩ := Usage.var_inv h rfl
  cases hts with
  | cons ht₁ hts =>
    cases hts with
    | cons ht₂ hts =>
      cases hts
      have h₁ := Usage.var₀_le ht₁ rfl
      have h₂ := Usage.var₀_le ht₂ rfl
      have h := hle (Var.x (ps := [Parameter.linear, Parameter.linear])).toFin
      revert h h₁ h₂
      simp only [GradeVector.add, GradeVector.update, GradeVector.smul, GradeVector.zero]
      have key : ∀ a b c : Grade, a ≤ (Mode.oneOne ⊙ Parameter.linear.usage).grade →
          b ≤ (Mode.oneOne ⊙ Parameter.linear.usage).grade →
          c ≤ Grade.zero +
            (Parameter.linear.usage * a + (Parameter.linear.usage * b + Grade.zero)) →
          c ≤ .unrestrictedUnrestricted := by
        decide
      intro h₁ h₂ h
      simp only [show (Var.x (ps := [Parameter.linear, Parameter.linear])).toFin ≠
        (Var.X (ps := [Parameter.linear, Parameter.linear])).toFin by decide, ↓reduceIte] at h
      exact key _ _ _ h₁ h₂ h

/-- A variable alone has at most the ownership that `φ` gives it. -/
theorem Ownership.var₀_le {sig : Signature} {k : Nat} {Γ : Scope} {φ : Var Γ .var → Grade}
    {m : Mode} {v : Var Γ .var} :
    ∀ {o : Grade} {t : Term k Γ}, Ownership sig φ m o t → t = .var₀ v → o ≤ φ v
  | _, _, .var, he => by cases he; exact Grade.le_refl _
  | _, _, .secondOrder _ _, he => by cases he
  | _, _, .const _, he => by cases he
  | _, _, .sort, he => by cases he
  | _, _, .sub h hle, he => Grade.le_trans _ _ _ hle (Ownership.var₀_le h he)

/-- The ownership of an application `X[t̄]` of a second-order variable gives ownerships to its
arguments, which satisfy the requirements of their entries. -/
theorem Ownership.secondOrder_inv {sig : Signature} {k : Nat} {Γ : Scope}
    {φ : Var Γ .var → Grade} {m : Mode} {ps : List Parameter} {χ₀ : Option Grade}
    {X : Var Γ (.secondOrder ps χ₀)} {ts : Args k Γ ps} :
    ∀ {p : Grade} {t : Term k Γ}, Ownership sig φ m p t → t = .var X ts →
      ∃ os, OwnershipArgs sig φ m ts os
  | _, _, .var, he => by cases he
  | _, _, .secondOrder hts _, he => by cases he; exact ⟨_, hts⟩
  | _, _, .const _, he => by cases he
  | _, _, .sort, he => by cases he
  | _, _, .sub h _, he => Ownership.secondOrder_inv h he

/-- `U₀` is not a term of `U₀`: by the soundness of the typing, the equality of the canonical type
`U₀` would relate `U₀` to itself, while it relates only the universes below `U₀`, of which there are
none. -/
theorem HasType.not_u₀ : ¬ HasType [] (.empty : Context 0 []) Term.u₀ Term.u₀ := by
  intro h
  let ι : Interpretation := fun _ _ => Term.u₀
  obtain ⟨-, hcl⟩ := soundness.hasType (ι := ι) (sig := []) (fun _ h => nomatch h) h Fin.elim0
  obtain ⟨-, hcl, -⟩ := hcl (fun x => nomatch x) (fun x => nomatch x) (by
    rw [show Context.atLevels Fin.elim0 (.empty : Context 0 []) = .empty from rfl, EqSubst]
    trivial)
  obtain ⟨v, w₁, w₂, R, hA, ht, -, hR, hw⟩ := hcl not_computesToProp_sort
  have hu : Term.subst (fun x => nomatch x : Subst 0 [] [])
      (Term.atLevels Fin.elim0 (Term.u₀ : Term 0 [])) = Term.u₀ := rfl
  rw [hu] at hA ht
  cases hA.sort_inv
  cases ht.sort_inv
  have h₀ : Level.closedValue (.zero : Level 0) = 0 := rfl
  cases hR with
  | univ n h =>
    cases levelRel_univ_iff.1 h with
    | univ hl _ =>
      obtain ⟨R', hR', -⟩ := hw
      cases levelRel_univ_iff.1 hR' with
      | univ hl' hk' => omega
      | data _ _ _ _ hv => cases hv
    | data _ _ _ _ hv => cases hv
  | prop _ _ h _ => cases levelRel_prop_iff.1 h with | data _ _ _ _ hv => cases hv

/-! ## Independence -/

-- ADE: none.
/-- `X[x, x]` is a term of `U₀`, and its value is shared, while its uses of `x` are two, which the
grade `11ᵖ` of `x` does not allow.
RFC: `\mathsf{independent}.{▶}` -/
theorem independent_usage :
    HasType [] (Context.xX Telescope.twice) Term.appTwice Term.u₀ ∧
      Ownership [] Ownership.alone .oneOne .unrestrictedUnrestricted Term.appTwice ∧
      ¬ Usage [] GradeVector.ones .oneOne Term.appTwice := by
  refine ⟨HasType.appTwice, ?_, fun h => ?_⟩
  · exact .secondOrder (.cons .var (fun _ => by decide) (.cons .var (fun _ => by decide) .nil)) rfl
  · exact absurd (Usage.appTwice_le h) (by decide)

-- ADE: none.
/-- `X[x]` is a term of `U₀`, and it uses `x` once, while it passes the shared `x` to an entry that
requires its argument to be owned alone.
RFC: `\mathsf{independent}.{◀}` -/
theorem independent_ownership :
    HasType [] (Context.xX Telescope.once) Term.appOnce Term.u₀ ∧
      Usage [] GradeVector.ones .oneOne Term.appOnce ∧
      ∀ p, ¬ Ownership [] Ownership.shared .oneOne p Term.appOnce := by
  refine ⟨HasType.appOnce, ?_, fun p h => ?_⟩
  · exact .sub (.var (.cons (.var .nil) .nil)) (by intro i; revert i; decide)
  · obtain ⟨os, hts⟩ := Ownership.secondOrder_inv h rfl
    cases hts with
    | cons ht hr _ =>
      have key : ∀ o : Grade, Parameter.unique.requirement ≤ o →
          o ≤ .unrestrictedUnrestricted → False := by
        decide
      exact key _ (hr (by decide)) (Ownership.var₀_le ht rfl)

-- ADE: none.
/-- `U₀` uses no variable, and has the ownership `ωωᵖ`, while it is not a term of `U₀`.
RFC: `\mathsf{independent}.{:}` -/
theorem independent_typing :
    Usage [] 𝟘ᶜ .oneOne (Term.u₀ : Term 0 []) ∧
      Ownership [] (fun x : Var [] .var => nomatch x) .oneOne .unrestrictedUnrestricted
        (Term.u₀ : Term 0 []) ∧
      ¬ HasType [] (.empty : Context 0 []) Term.u₀ Term.u₀ :=
  ⟨.sort, .sort, HasType.not_u₀⟩

end Sic.Core
