module

import Sic.Core.Reduction
import Sic.Core.WellFormed
import all Sic.Core.Substitution.Validation
import all Sic.Core.Syntax.Validation
import all Sic.Core.TypedSubstitution.Validation
import all Sic.Core.Typing.Validation
import all Sic.Core.WellFormed.Validation

/-!
# Validation of the Reduction

The reduction of `Sic.Core.Reduction` checked against the formalization of ADE, on the
polymorphic identity of RFC 24, and on the examples of the literature, whose equalities it proves.

| Definition | Definition of ADE |
| --- | --- |
| `Neutral` | `Neutral`, in `Definition/Untyped/Neutral.agda` |
| `Whnf` | `Whnf`, in `Definition/Untyped/Whnf.agda` |
| `TermRed.conv`, `TermRed.app`, `TermRed.beta` | `conv`, `app-subst`, `β-red` of `_⊢_⇒_∷_`, in `Definition/Typed.agda` |
| `TermRedStar.refl`, `TermRedStar.step` | `id`, `_⇨_` of `_⊢_⇒*_∷_`, in `Definition/Typed.agda` |
| `TermRedWhnf` | `_⊢_↘_∷_`, in `Definition/Typed.agda` |

ADE also reduce types, with `_⊢_⇒_`, which a reduction of a term in a universe replaces here, as the
equality of types does in `Sic.Core.Typing`.
Their `β-red` reduces an abstraction applied with another grade, which their premise `p ≡ p′`
equates, while `TermRed.beta` writes the same grade on both.
-/

namespace Sic.Core.Reduction.Validation

open Grade Substitution.Validation Syntax.Validation Term TypedSubstitution.Validation
  Typing.Validation WellFormed.Validation

/-- The context `A : U_l` of a type variable, over the level variable `l`. -/
def Γ₁ : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_Γ₁ : ⊢ Γ₁ := .snoc (.univ .empty)

/--
The polymorphic identity applied to a type, `(λ_𝟘 (A : U_l). λ_𝟙 (x : A). x) ∘_𝟘 A`, reduces in one
step to the identity `λ_𝟙 (x : A). x` of `A`, a weak head normal form.
-/
example : Γ₁ ⊢ app 𝟘 identity.wk1 (var 0) ↘ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`, as for the type of
  -- the polymorphic identity, but in `Γ₁`.
  have hU : Γ₁ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ wfCon_Γ₁
  have hA : Γ₁ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc hU)
  have hA' : Γ₁ ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hPi : Γ₁ ∙ univ (.var 0) ⊢ pi 𝟙 𝟘 (var 0) (var 1) : univ (.var 0 ⊔ .var 0) := .pi hA hA'
  have hIdType := HasType.pi (p := 𝟘) (q := 𝟙 + 𝟙) hU hPi
  -- `A : U_l` in `Γ₁`, and `A : U_l` after `x : A`, for the identity of `A`.
  have hB : Γ₁ ⊢ var 0 : univ (.var 0) := .var wfCon_Γ₁
  have hB' : Γ₁ ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hB)
  ⟨.step (.beta hIdType (.lam hPi (.var (.snoc hA))) hB)
    (.refl (.lam (.pi hB hB') (.var (.snoc hB)))), .lam⟩

/-- A variable applied to an argument, `x ∘_𝟙 y`, is neutral, so that it does not reduce. -/
example {Γ : Con 0 2} : ¬ Γ ⊢ app 𝟙 (var 0) (var 1) ⇒ u : A := Neutral.not_termRed (.app .var)

/-!
The examples of the literature reduce as the literature says, which proves their equalities.
Each step applies an abstraction that the previous steps moved by a substitution of their arguments,
which `termRed_beta_subst` reduces from the typing of the body of the abstraction before the
substitution: the bodies of a closed term, one under each of its binders, are typed in the context
of the domains of its type, `contextAt`.
-/

/--
`(β)` for an abstraction moved by the substitution `σ`, from the typing of its body alone: its
argument replaces its variable, and `σ` the others.
-/
theorem termRed_beta_subst (ht : Γ ∙ A ⊢ t : B) (hσ : Δ ⊢ˢ σ : Γ) (hΔ : ⊢ Δ)
    (ha : Δ ⊢ a : A.subst σ) :
    Δ ⊢ app p ((lam p A t).subst σ) a ⇒ t.subst (σ.cons a) : B.subst (σ.cons a) := by
  have ⟨_, hA⟩ := wfCon_snoc_inv ht.wfCon
  have ⟨_, hB⟩ := ht.wfType
  have hPi' := (HasType.pi (p := p) (q := 𝟘) hA hB).subst hσ hΔ
  have ⟨_, hA'⟩ := hPi'.inv_pi.1
  have h := TermRed.beta hPi' (ht.subst (hσ.lift (.snoc hA')) (.snoc hA')) ha
  rwa [subst_lift_instantiate, subst_lift_instantiate] at h

/-- The body of an abstraction, or the term itself, moved, for any other term. -/
def body : Term k n → Term k (n + 1)
  | lam _ _ t => t
  | t => t.wk1

/-- The codomain of a type of functions, or the term itself, moved, for any other term. -/
def codomain : Term k n → Term k (n + 1)
  | pi _ _ _ B => B
  | t => t.wk1

/-- The domain of a type of functions, or the term itself, for any other term. -/
def domain : Term k n → Term k n
  | pi _ _ A _ => A
  | t => t

/-- The body of the closed term `t` under its first `j` binders. -/
def bodyAt : (j : Nat) → Term k 0 → Term k j
  | 0, t => t
  | j + 1, t => body (bodyAt j t)

/-- The codomain of the closed type `T` after its first `j` domains. -/
def codomainAt : (j : Nat) → Term k 0 → Term k j
  | 0, T => T
  | j + 1, T => codomain (codomainAt j T)

/-- The context of the first `j` domains of the closed type `T`. -/
def contextAt (T : Term k 0) : (j : Nat) → Con k j
  | 0 => .empty
  | j + 1 => contextAt T j ∙ domain (codomainAt j T)

/-! The bodies of `K`, `S`, `1`, `2` and `succ`, under the binders that the examples apply. -/

theorem hasType_combinatorK_4 :
    contextAt combinatorKType 4 ⊢ bodyAt 4 combinatorK : codomainAt 4 combinatorKType :=
  have hA : .empty ∙ univ (.var 0) ∙ univ (.var 0) ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (.univ (.snoc (.univ .empty))))
  .var (.snoc (.var (.snoc hA) : .empty ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ⊢ var 1 : _))

theorem hasType_combinatorK_3 :
    contextAt combinatorKType 3 ⊢ bodyAt 3 combinatorK : codomainAt 3 combinatorKType :=
  hasType_lam hasType_combinatorK_4

theorem hasType_combinatorK_2 :
    contextAt combinatorKType 2 ⊢ bodyAt 2 combinatorK : codomainAt 2 combinatorKType :=
  hasType_lam hasType_combinatorK_3

theorem hasType_combinatorK_1 :
    contextAt combinatorKType 1 ⊢ bodyAt 1 combinatorK : codomainAt 1 combinatorKType :=
  hasType_lam hasType_combinatorK_2

theorem hasType_combinatorS_5 :
    contextAt combinatorSType 5 ⊢ bodyAt 5 combinatorS : codomainAt 5 combinatorSType :=
  hasType_lam (hasType_combinatorS_body .empty)

theorem hasType_combinatorS_4 :
    contextAt combinatorSType 4 ⊢ bodyAt 4 combinatorS : codomainAt 4 combinatorSType :=
  hasType_lam hasType_combinatorS_5

theorem hasType_combinatorS_3 :
    contextAt combinatorSType 3 ⊢ bodyAt 3 combinatorS : codomainAt 3 combinatorSType :=
  hasType_lam hasType_combinatorS_4

theorem hasType_combinatorS_2 :
    contextAt combinatorSType 2 ⊢ bodyAt 2 combinatorS : codomainAt 2 combinatorSType :=
  hasType_lam hasType_combinatorS_3

theorem hasType_combinatorS_1 :
    contextAt combinatorSType 1 ⊢ bodyAt 1 combinatorS : codomainAt 1 combinatorSType :=
  hasType_lam hasType_combinatorS_2

theorem hasType_churchOne_3 :
    contextAt churchNat 3 ⊢ bodyAt 3 churchOne : codomainAt 3 churchNat :=
  .app (hasType_ΓNat_f .empty) (hasType_ΓNat_x .empty)

theorem hasType_churchOne_2 :
    contextAt churchNat 2 ⊢ bodyAt 2 churchOne : codomainAt 2 churchNat :=
  hasType_lam hasType_churchOne_3

theorem hasType_churchOne_1 :
    contextAt churchNat 1 ⊢ bodyAt 1 churchOne : codomainAt 1 churchNat :=
  hasType_lam hasType_churchOne_2

theorem hasType_churchTwo_3 :
    contextAt churchNat 3 ⊢ bodyAt 3 churchTwo : codomainAt 3 churchNat :=
  .app (hasType_ΓNat_f .empty) (.app (hasType_ΓNat_f .empty) (hasType_ΓNat_x .empty))

theorem hasType_churchTwo_2 :
    contextAt churchNat 2 ⊢ bodyAt 2 churchTwo : codomainAt 2 churchNat :=
  hasType_lam hasType_churchTwo_3

theorem hasType_churchTwo_1 :
    contextAt churchNat 1 ⊢ bodyAt 1 churchTwo : codomainAt 1 churchNat :=
  hasType_lam hasType_churchTwo_2

theorem hasType_churchSucc_1 :
    contextAt (pi 𝟙 𝟘 churchNat churchNat) 1 ⊢ bodyAt 1 churchSucc :
      codomainAt 1 (pi 𝟙 𝟘 churchNat churchNat) :=
  hasType_numeral (.snoc (hasType_churchNat .empty)) (hasType_churchSucc_body .empty)

/-! `S K K` is the identity. -/

/--
`S K K` reduces, by `(β)` on each of its five arguments, to
`λ_𝟙 (z : A). (x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)`, where `x` and `y` are the two `K`.
-/
theorem skk_termRedStar :
    ΓA ⊢ skk ⇒* lam 𝟙 (var 0) (app 𝟘 (app 𝟙 skkX.wk1 (var 0)) (app 𝟙 skkY.wk1 (var 0))) :
      pi 𝟙 𝟘 (var 0) (var 1) :=
  have hσ₀ : ΓA ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_1 hσ₀ wfCon_ΓA hasType_ΓA_var
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hasType_ΓA_var
  have β₂ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_2 hσ₁ wfCon_ΓA hasType_skkB
  have hσ₂ := substWf_cons (A := (univ (.var 0) : Term 1 1)) hσ₁ hasType_skkB
  have β₃ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_3 hσ₂ wfCon_ΓA hasType_ΓA_var
  have hσ₃ := substWf_cons (A := (univ (.var 0) : Term 1 2)) hσ₂ hasType_ΓA_var
  have β₄ := termRed_beta_subst (p := 𝟙) hasType_combinatorS_4 hσ₃ wfCon_ΓA hasType_skkX
  have hσ₄ := substWf_cons (A := (pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) : Term 1 3)) hσ₃
    hasType_skkX
  have β₅ := termRed_beta_subst (p := 𝟘) hasType_combinatorS_5 hσ₄ wfCon_ΓA hasType_skkY
  .step (.app (.app (.app (.app β₁ hasType_skkB) hasType_ΓA_var) hasType_skkX) hasType_skkY)
    (.step (.app (.app (.app β₂ hasType_ΓA_var) hasType_skkX) hasType_skkY)
      (.step (.app (.app β₃ hasType_skkX) hasType_skkY)
        (.step (.app β₄ hasType_skkY)
          (.step β₅ (.refl β₅.hasType_reduct)))))

/--
The body `K ∘_𝟘 A ∘_𝟘 B ∘_𝟙 z ∘_𝟘 (K ∘_𝟘 A ∘_𝟘 A ∘_𝟙 z)` reduces to `z`, as `K` discards its
second argument.
-/
theorem skk_body_termRedStar :
    ΓA ∙ var 0 ⊢ app 𝟘 (app 𝟙 skkX.wk1 (var 0)) (app 𝟙 skkY.wk1 (var 0)) ⇒* var 0 : var 1 :=
  have h : ⊢ ΓA ∙ var 0 := .snoc hasType_ΓA_var
  have hA : ΓA ∙ var 0 ⊢ var 1 : univ (.var 0) := .var h
  have hB := hasType_skkB.wk (.step .id) h
  have hz : ΓA ∙ var 0 ⊢ var 0 : var 1 := .var h
  have hw := HasType.app (hasType_skkY.wk (.step .id) h) hz
  have hσ₀ : ΓA ∙ var 0 ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_1 hσ₀ h hA
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hA
  have β₂ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_2 hσ₁ h hB
  have hσ₂ := substWf_cons (A := (univ (.var 0) : Term 1 1)) hσ₁ hB
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_combinatorK_3 hσ₂ h hz
  have hσ₃ := substWf_cons (A := (var 1 : Term 1 2)) hσ₂ hz
  have β₄ := termRed_beta_subst (p := 𝟘) hasType_combinatorK_4 hσ₃ h hw
  .step (.app (.app (.app β₁ hB) hz) hw)
    (.step (.app (.app β₂ hz) hw)
      (.step (.app β₃ hw)
        (.step β₄ (.refl β₄.hasType_reduct))))

/--
`S K K` is the identity `λ_𝟙 (z : A). z` of `A`: it reduces to an abstraction whose body reduces to
its variable, as `S K K X` reduces to `X` in exercise 2.16 of Hindley and Seldin.
-/
theorem skk_termEq : ΓA ⊢ skk ≡ lam 𝟙 (var 0) (var 0) : pi 𝟙 𝟘 (var 0) (var 1) :=
  .trans skk_termRedStar.termEq
    (.lam (.pi hasType_ΓA_var (.var (.snoc hasType_ΓA_var))) (.refl hasType_ΓA_var)
      skk_body_termRedStar.termEq)

/-! The successor of `1` is `2`. -/

/-- `2 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x` reduces to `f ∘_𝟙 (f ∘_𝟙 x)`: `2` applies `f` twice. -/
theorem churchTwo_termRedStar :
    ΓNat .empty ⊢ app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchTwo (var 2)) (var 1)) (var 0) ⇒*
      app 𝟙 (var 1) (app 𝟙 (var 1) (var 0)) : var 2 :=
  have h := wfCon_ΓNat (Γ := (.empty : Con 1 0)) .empty
  have hX : ΓNat .empty ⊢ var 2 : univ (.var 0) := .var h
  have hσ₀ : ΓNat .empty ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_churchTwo_1 hσ₀ h hX
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hX
  have β₂ := termRed_beta_subst (p := 𝟙 + 𝟙) hasType_churchTwo_2 hσ₁ h (hasType_ΓNat_f .empty)
  have hσ₂ := substWf_cons (A := (churchFunType : Term 1 1)) hσ₁ (hasType_ΓNat_f .empty)
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_churchTwo_3 hσ₂ h (hasType_ΓNat_x .empty)
  .step (.app (.app β₁ (hasType_ΓNat_f .empty)) (hasType_ΓNat_x .empty))
    (.step (.app β₂ (hasType_ΓNat_x .empty)) (.step β₃ (.refl β₃.hasType_reduct)))

/-- `1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x` reduces to `f ∘_𝟙 x`. -/
theorem churchOne_termRedStar :
    ΓNat .empty ⊢ app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 churchOne (var 2)) (var 1)) (var 0) ⇒*
      app 𝟙 (var 1) (var 0) : var 2 :=
  have h := wfCon_ΓNat (Γ := (.empty : Con 1 0)) .empty
  have hX : ΓNat .empty ⊢ var 2 : univ (.var 0) := .var h
  have hσ₀ : ΓNat .empty ⊢ˢ Fin.elim0 : .empty := substWf_empty
  have β₁ := termRed_beta_subst (p := 𝟘) hasType_churchOne_1 hσ₀ h hX
  have hσ₁ := substWf_cons (A := (univ (.var 0) : Term 1 0)) hσ₀ hX
  have β₂ := termRed_beta_subst (p := 𝟙 + 𝟙) hasType_churchOne_2 hσ₁ h (hasType_ΓNat_f .empty)
  have hσ₂ := substWf_cons (A := (churchFunType : Term 1 1)) hσ₁ (hasType_ΓNat_f .empty)
  have β₃ := termRed_beta_subst (p := 𝟙) hasType_churchOne_3 hσ₂ h (hasType_ΓNat_x .empty)
  .step (.app (.app β₁ (hasType_ΓNat_f .empty)) (hasType_ΓNat_x .empty))
    (.step (.app β₂ (hasType_ΓNat_x .empty)) (.step β₃ (.refl β₃.hasType_reduct)))

/--
`succ ∘_𝟙 1` is `2`, as `S n` is `n + 1` in Girard, Lafont and Taylor: `succ ∘_𝟙 1` reduces to
`λ_𝟘 (X : U_l). λ_{𝟙 + 𝟙} (f : Π^𝟘_𝟙 (y : X). X). λ_𝟙 (x : X). f ∘_𝟙 (1 ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)`,
whose body is equal to the body of `2`, under the three binders, by the congruences.
-/
theorem churchSucc_one_termEq :
    (.empty : Con 1 0) ⊢ app 𝟙 churchSucc churchOne ≡ churchTwo : churchNat :=
  have β := termRed_beta_subst (p := 𝟙) hasType_churchSucc_1 (σ := Fin.elim0) substWf_empty .empty
    (hasType_churchOne .empty)
  have hNat := hasType_churchNat (Γ := (.empty : Con 1 0)) .empty
  have ⟨⟨_, hU⟩, _, hNat₂⟩ := hNat.inv_pi
  have ⟨⟨_, hf⟩, _, hNat₃⟩ := hNat₂.inv_pi
  have ⟨⟨_, hx⟩, _⟩ := hNat₃.inv_pi
  .trans β.termEq (.lam hNat (.refl hU) (.lam hNat₂ (.refl hf) (.lam hNat₃ (.refl hx)
    (.app (.refl (hasType_ΓNat_f .empty)) churchOne_termRedStar.termEq))))

end Sic.Core.Reduction.Validation
