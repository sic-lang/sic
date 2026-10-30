module

import Sic.Core.Typing
import all Sic.Core.Syntax.Validation

/-!
# Validation of the Typing

The judgments of `Sic.Core.Typing` checked against RFC 24, against the formalization of ADE, and on
the examples of the literature.

| Rule of RFC 24 | Constructor | Rule of ADE, in `Definition/Typed.agda` |
| --- | --- | --- |
| `(ctx_ε)`, `(ctx_,)` | `WfCon.empty`, `WfCon.snoc` | `ε`, `∙_` of `_»⊢_` |
| `(var)` | `HasType.var` | `var`, with `_∷_∈_` |
| `(conv)` | `HasType.conv` | `conv` of `_⊢_∷_` |
| `(univ)` | `HasType.univ` | `Uⱼ` |
| `(Π)` | `HasType.pi` | `ΠΣⱼ` of `_⊢_∷_` |
| `(λ)` | `HasType.lam` | `lamⱼ` |
| `(∘)` | `HasType.app` | `_∘ⱼ_` |
| `(refl)`, `(sym)`, `(trans)` | `TermEq.refl`, `TermEq.symm`, `TermEq.trans` | `refl`, `sym`, `trans` of `_⊢_≡_∷_` |
| `(conv_≡)` | `TermEq.conv` | `conv` of `_⊢_≡_∷_` |
| `(univ_≡)` | `TermEq.univ` | `U-cong` |
| Congruences | `TermEq.pi`, `TermEq.lam`, `TermEq.app` | `ΠΣ-cong`, none, `app-cong` |
| `(β)` | `TermEq.beta` | `β-red` |
| `(η)` | `TermEq.eta` | `η-eq` |

ADE have five judgments, with two for the types, `Γ ⊢ A` and `Γ ⊢ A ≡ B`, which RFC 24 replaces by
the typing and the equality of a term in a universe.
Their abstraction does not carry the type of its argument, so that they have no congruence of
abstraction, and state `η` as the equality of two functions whose applications to a variable are
equal.
The inversion `HasType.inv_pi` is the part of `inversion-ΠΣ-U`, in
`Definition/Typed/Inversion/Primitive.agda`, that types the domain and the codomain.
-/

namespace Sic.Core.Typing.Validation

open Grade Syntax.Validation Term

/-! The examples of RFC 24, as derivations. -/

/-- The context `A : U₀, B : U₀` of the constant function. -/
def Γ₂ : Con 0 2 := .empty ∙ univ .zero ∙ univ .zero

theorem wfCon_Γ₂ : ⊢ Γ₂ := .snoc (.univ (.snoc (.univ .empty)))

/--
The constant function `λ_𝟙 (x : A). λ_𝟘 (y : B). x` has the type
`Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`.
-/
theorem hasType_constant : Γ₂ ⊢ constant : constantType :=
  -- `A : U₀` in `Γ₂`, `B : U₀` after `x : A`, and `A : U₀` after `y : B`.
  have hA : Γ₂ ⊢ var 1 : univ .zero := .var wfCon_Γ₂
  have hB : Γ₂ ∙ var 1 ⊢ var 1 : univ .zero := .var (.snoc hA)
  have hA' : Γ₂ ∙ var 1 ∙ var 1 ⊢ var 3 : univ .zero := .var (.snoc hB)
  have hPi := HasType.pi hB hA'
  .lam (.pi hA hPi) (.lam hPi (.var (.snoc hB)))

/--
The polymorphic identity `λ_𝟘 (A : U_l). λ_𝟙 (x : A). x` has the type
`Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟘_𝟙 (x : A). A` in the empty context, with its level variable `l`.
-/
theorem hasType_identity : .empty ⊢ identity : identityType :=
  -- `U_l : U_{l + 1}`, then `A : U_l` after `A`, and `A : U_l` after `x : A`.
  have hU : (.empty : Con 1 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ .empty
  have hA : .empty ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc hU)
  have hA' : .empty ∙ univ (.var 0) ∙ var 0 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hPi := HasType.pi hA hA'
  .lam (.pi hU hPi) (.lam hPi (.var (.snoc hA)))

/-! The examples of the literature, as derivations. -/

/--
`K` has its type `Π^{𝟙 + 𝟙}_𝟘 (A : U_l). Π^𝟙_𝟘 (B : U_l). Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A`, in
every well-formed context, since it is closed.
-/
theorem hasType_combinatorK (h : ⊢ Γ) : Γ ⊢ combinatorK : combinatorKType :=
  -- `U_l` in `Γ` and after `A`, `A` after `B`, `B` after `x`, and `A` after `y`.
  have hU : Γ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ h
  have hU' : Γ ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ (.snoc hU)
  have hA : Γ ∙ univ (.var 0) ∙ univ (.var 0) ⊢ var 1 : univ (.var 0) := .var (.snoc hU')
  have hB : Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ⊢ var 1 : univ (.var 0) := .var (.snoc hA)
  have hA' : Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ var 1 ∙ var 1 ⊢ var 3 : univ (.var 0) :=
    .var (.snoc hB)
  have hy := HasType.pi hB hA'
  have hx := HasType.pi hA hy
  have hB' := HasType.pi hU' hx
  .lam (.pi hU hB') (.lam hB' (.lam hx (.lam hy (.var (.snoc hB)))))

/-- The context `A : U_l, B : U_l, C : U_l` of the bound types of `S`, after `Γ`. -/
def ΓS (Γ : Con 1 n) : Con 1 (n + 3) := Γ ∙ univ (.var 0) ∙ univ (.var 0) ∙ univ (.var 0)

theorem wfCon_ΓS (h : ⊢ Γ) : ⊢ ΓS Γ := .snoc (.univ (.snoc (.univ (.snoc (.univ h)))))

/-- The type `Π^𝟘_𝟙 (a : A). Π^𝟘_𝟘 (b : B). C` of `x`. -/
theorem hasType_combinatorS_x (h : ⊢ Γ) :
    ΓS Γ ⊢ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) : univ (.var 0 ⊔ (.var 0 ⊔ .var 0)) :=
  have hA : ΓS Γ ⊢ var 2 : univ (.var 0) := .var (wfCon_ΓS h)
  have hB : ΓS Γ ∙ var 2 ⊢ var 2 : univ (.var 0) := .var (.snoc hA)
  .pi hA (.pi hB (.var (.snoc hB)))

/-- The type `Π^𝟘_𝟙 (a : A). B` of `y`, after `x`. -/
theorem hasType_combinatorS_y (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ⊢ pi 𝟙 𝟘 (var 3) (var 3) :
      univ (.var 0 ⊔ .var 0) :=
  have hA : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ⊢ var 3 : univ (.var 0) :=
    .var (.snoc (hasType_combinatorS_x h))
  .pi hA (.var (.snoc hA))

/-- The type `A` of `z`, after `x` and `y`. -/
theorem hasType_combinatorS_z (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ⊢ var 4 :
      univ (.var 0) :=
  .var (.snoc (hasType_combinatorS_y h))

/--
The body `(x ∘_𝟙 z) ∘_𝟘 (y ∘_𝟙 z)` of `S` has the type `C`: `x ∘_𝟙 z` is a function of `B`, of
which `y ∘_𝟙 z` is a term.
-/
theorem hasType_combinatorS_body (h : ⊢ Γ) :
    ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      app 𝟘 (app 𝟙 (var 2) (var 0)) (app 𝟙 (var 1) (var 0)) : var 3 :=
  have h' := WfCon.snoc (hasType_combinatorS_z h)
  have hx : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 2 : pi 𝟙 𝟘 (var 5) (pi 𝟘 𝟘 (var 5) (var 5)) := .var h'
  have hy : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 1 : pi 𝟙 𝟘 (var 5) (var 5) := .var h'
  have hz : ΓS Γ ∙ pi 𝟙 𝟘 (var 2) (pi 𝟘 𝟘 (var 2) (var 2)) ∙ pi 𝟙 𝟘 (var 3) (var 3) ∙ var 4 ⊢
      var 0 : var 5 := .var h'
  .app (.app hx hz) (.app hy hz)

/-- `S` has its type, in every well-formed context. -/
theorem hasType_combinatorS (h : ⊢ Γ) : Γ ⊢ combinatorS : combinatorSType :=
  have hU : Γ ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ h
  have hU' : Γ ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) := .univ (.snoc hU)
  have hU'' : Γ ∙ univ (.var 0) ∙ univ (.var 0) ⊢ univ (.var 0) : univ (.succ (.var 0)) :=
    .univ (.snoc hU')
  have hz := HasType.pi (hasType_combinatorS_z h) (.var (.snoc (hasType_combinatorS_z h)))
  have hy := HasType.pi (hasType_combinatorS_y h) hz
  have hx := HasType.pi (hasType_combinatorS_x h) hy
  have hC := HasType.pi hU'' hx
  have hB := HasType.pi hU' hC
  .lam (.pi hU hB) (.lam hB (.lam hC (.lam hx (.lam hy (.lam hz (hasType_combinatorS_body h))))))

/-- The context `A : U_l` in which `S K K` is the identity of `A`. -/
def ΓA : Con 1 1 := .empty ∙ univ (.var 0)

theorem wfCon_ΓA : ⊢ ΓA := .snoc (.univ .empty)

/-- The type variable `A`. -/
theorem hasType_ΓA_var : ΓA ⊢ var 0 : univ (.var 0) := .var wfCon_ΓA

/--
`B = Π^𝟘_𝟘 (y : A). A`, the type of the argument that the first `K` discards, a type of `U_l` since
`l ⊔ l` equals `l`.
-/
def skkB : Term 1 1 := pi 𝟘 𝟘 (var 0) (var 1)

theorem hasType_skkB : ΓA ⊢ skkB : univ (.var 0) :=
  .conv (.pi hasType_ΓA_var (.var (.snoc hasType_ΓA_var)))
    (.univ wfCon_ΓA fun _ => Nat.max_self _)

/-- `K ∘_𝟘 A ∘_𝟘 B`, of the type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : B). A` of `x` in `S`. -/
def skkX : Term 1 1 := app 𝟘 (app 𝟘 combinatorK (var 0)) skkB

/-- `K ∘_𝟘 A ∘_𝟘 A`, of the type `Π^𝟘_𝟙 (x : A). Π^𝟘_𝟘 (y : A). A`, which is `Π^𝟘_𝟙 (a : A). B`. -/
def skkY : Term 1 1 := app 𝟘 (app 𝟘 combinatorK (var 0)) (var 0)

/-- `S ∘_𝟘 A ∘_𝟘 B ∘_𝟘 A ∘_𝟙 (K ∘_𝟘 A ∘_𝟘 B) ∘_𝟘 (K ∘_𝟘 A ∘_𝟘 A)`, the `S K K` of `A`. -/
def skk : Term 1 1 :=
  app 𝟘 (app 𝟙 (app 𝟘 (app 𝟘 (app 𝟘 combinatorS (var 0)) skkB) (var 0)) skkX) skkY

theorem hasType_skkX : ΓA ⊢ skkX : pi 𝟙 𝟘 (var 0) (pi 𝟘 𝟘 skkB.wk1 (var 2)) :=
  .app (.app (hasType_combinatorK wfCon_ΓA)
    hasType_ΓA_var) hasType_skkB

theorem hasType_skkY : ΓA ⊢ skkY : pi 𝟙 𝟘 (var 0) skkB.wk1 :=
  .app (.app (hasType_combinatorK wfCon_ΓA)
    hasType_ΓA_var) hasType_ΓA_var

/-- `S K K` has the type `Π^𝟘_𝟙 (z : A). A` of the identity of `A`. -/
theorem hasType_skk : ΓA ⊢ skk : pi 𝟙 𝟘 (var 0) (var 1) :=
  .app (.app (.app (.app (.app (hasType_combinatorS wfCon_ΓA) hasType_ΓA_var) hasType_skkB)
    hasType_ΓA_var) hasType_skkX) hasType_skkY

/-- The context `X : U_l, f : Π^𝟘_𝟙 (y : X). X, x : X` of the bodies of the numerals, after `Γ`. -/
def ΓNat (Γ : Con 1 n) : Con 1 (n + 3) := Γ ∙ univ (.var 0) ∙ churchFunType ∙ var 1

/-- The type `Π^𝟘_𝟙 (y : X). X` of `f`, at the level `l ⊔ l`. -/
theorem hasType_churchFunType (h : ⊢ Γ) :
    Γ ∙ univ (.var 0) ⊢ churchFunType : univ (.var 0 ⊔ .var 0) :=
  have hX : Γ ∙ univ (.var 0) ⊢ var 0 : univ (.var 0) := .var (.snoc (.univ h))
  .pi hX (.var (.snoc hX))

theorem wfCon_ΓNat (h : ⊢ Γ) : ⊢ ΓNat Γ :=
  .snoc (.var (.snoc (hasType_churchFunType h)) : Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : _)

/-- `Nat_l` is a type, of the level `(l + 1) ⊔ ((l ⊔ l) ⊔ (l ⊔ l))`, which is `l + 1`. -/
theorem hasType_churchNat (h : ⊢ Γ) :
    Γ ⊢ churchNat : univ (.succ (.var 0) ⊔ ((.var 0 ⊔ .var 0) ⊔ (.var 0 ⊔ .var 0))) :=
  have hx : Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (hasType_churchFunType h))
  .pi (.univ h) (.pi (hasType_churchFunType h) (.pi hx (.var (wfCon_ΓNat h))))

/-- A numeral has the type `Nat_l` when its body has the type `X`. -/
theorem hasType_numeral (h : ⊢ Γ) (hb : ΓNat Γ ⊢ b : var 2) :
    Γ ⊢ lam 𝟘 (univ (.var 0)) (lam (𝟙 + 𝟙) churchFunType (lam 𝟙 (var 1) b)) : churchNat :=
  have hx : Γ ∙ univ (.var 0) ∙ churchFunType ⊢ var 1 : univ (.var 0) :=
    .var (.snoc (hasType_churchFunType h))
  have hx' := HasType.pi hx (.var (wfCon_ΓNat h) : ΓNat Γ ⊢ var 2 : univ (.var 0))
  have hf := HasType.pi (hasType_churchFunType h) hx'
  .lam (.pi (.univ h) hf) (.lam hf (.lam hx' hb))

/-- `f`, in the bodies of the numerals. -/
theorem hasType_ΓNat_f (h : ⊢ Γ) : ΓNat Γ ⊢ var 1 : pi 𝟙 𝟘 (var 2) (var 3) := .var (wfCon_ΓNat h)

/-- `x`, in the bodies of the numerals. -/
theorem hasType_ΓNat_x (h : ⊢ Γ) : ΓNat Γ ⊢ var 0 : var 2 := .var (wfCon_ΓNat h)

theorem hasType_churchOne (h : ⊢ Γ) : Γ ⊢ churchOne : churchNat :=
  hasType_numeral h (.app (hasType_ΓNat_f h) (hasType_ΓNat_x h))

theorem hasType_churchTwo (h : ⊢ Γ) : Γ ⊢ churchTwo : churchNat :=
  hasType_numeral h (.app (hasType_ΓNat_f h) (.app (hasType_ΓNat_f h) (hasType_ΓNat_x h)))

/-- The body `f ∘_𝟙 (m ∘_𝟘 X ∘_{𝟙 + 𝟙} f ∘_𝟙 x)` of `succ`, after `m : Nat_l`. -/
theorem hasType_churchSucc_body (h : ⊢ Γ) :
    ΓNat (Γ ∙ churchNat) ⊢
      app 𝟙 (var 1) (app 𝟙 (app (𝟙 + 𝟙) (app 𝟘 (var 3) (var 2)) (var 1)) (var 0)) : var 2 :=
  have h' : ⊢ Γ ∙ churchNat := .snoc (hasType_churchNat h)
  have hm : ΓNat (Γ ∙ churchNat) ⊢ var 3 : churchNat := .var (wfCon_ΓNat h')
  have hX : ΓNat (Γ ∙ churchNat) ⊢ var 2 : univ (.var 0) := .var (wfCon_ΓNat h')
  .app (hasType_ΓNat_f h') (.app (.app (.app hm hX) (hasType_ΓNat_f h')) (hasType_ΓNat_x h'))

/-- `succ` has the type `Π^𝟘_𝟙 (m : Nat_l). Nat_l`. -/
theorem hasType_churchSucc (h : ⊢ Γ) : Γ ⊢ churchSucc : pi 𝟙 𝟘 churchNat churchNat :=
  have h' : ⊢ Γ ∙ churchNat := .snoc (hasType_churchNat h)
  .lam (.pi (hasType_churchNat h) (hasType_churchNat h'))
    (hasType_numeral h' (hasType_churchSucc_body h))

end Sic.Core.Typing.Validation
