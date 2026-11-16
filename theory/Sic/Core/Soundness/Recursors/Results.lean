module

public import Sic.Core.Soundness.DeclaredTypes
public import Sic.Core.Soundness.Recursors.Nested
import Sic.Core.Meaning.Judgments
import Sic.Core.Results.Substitution
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Substitution

/-!
# Meaning of the Recursive Results of the Fields of a Constructor

The recursive results of the terms of the fields of a constructor, on two sides, are equal
arguments of the telescope of the recursive results, at the terms of the first side, when the
equality of the fields relates these terms: the result of a recursive field is that of a term of a
type of the block, which the relation at its position makes equal, and the result of a field
nested below a codata type is equal by the meaning of the recursive result of a nested field,
which `Nested` proves.

The telescope of the recursive results is in the scope of the fields, and each result is in the
scope of the results before it: the statement is at a closed substitution of the scope of the
fields, and at closed terms of the results before, which the induction extends, result by result.
The types of the fields of the second side are any types of the same shape as those of the first,
as the types of the fields of a constructor at two instances and at two lists of terms are.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {v : Lifting.Variables}

/-! ## Shape of the Types of the Fields -/

/-- The types of the entries of a telescope, at two instantiations of its levels and at two
substitutions, have the same shape, one by one, at the nestings of the entries. -/
theorem Telescope.similar_types {k k' : Nat} (names : List Name) (ls₁ ls₂ : Fin k → Level k') :
    {Γ Ξ : Scope} → {ps : List Parameter} → (Θ : Telescope k Ξ ps) → (θ₁ θ₂ : Subst k' Γ Ξ) →
      Terms.Similar (Θ.nest names) ((Θ.substLevels ls₁).subst θ₁).types
        ((Θ.substLevels ls₂).subst θ₂).types
  | _, _, _, .nil, _, _ => trivial
  | _, _, _, .cons _ _ A Θ, θ₁, θ₂ =>
    ⟨(Term.similar_subst _ ls₁ ls₂ (ν := Nesting.plain) (fun _ => .plain) A).rename _ _,
      Telescope.similar_types names ls₁ ls₂ Θ (Subst.lift θ₁) (Subst.lift θ₂)⟩

/-- The types of the entries of a telescope, at two instantiations of its levels, at two
substitutions and at arguments of each, have the same shape, one by one, at the nestings of the
entries: the types of the fields of a constructor at two instances and at two lists of terms. -/
theorem Telescope.similar_typesAt {k k' : Nat} (names : List Name) (ls₁ ls₂ : Fin k → Level k')
    {Γ Ξ : Scope} {ps : List Parameter} (Θ : Telescope k Ξ ps) (θ₁ θ₂ : Subst k' Γ Ξ)
    (ts₁ ts₂ : Args k' Γ ps) :
    Terms.Similar (Θ.nest names) (((Θ.substLevels ls₁).subst θ₁).typesAt ts₁)
      (((Θ.substLevels ls₂).subst θ₂).typesAt ts₂) := by
  rw [← Telescope.types_toSubst₀, ← Telescope.types_toSubst₀]
  exact (Telescope.similar_types names ls₁ ls₂ Θ θ₁ θ₂).subst₀ _ _

/-! ## Equality of the Recursive Results -/

-- ADE: none.
/-- The recursive results `r̄₁` and `r̄₂` of the closed terms `t̄₁` and `t̄₂` of fields are equal
arguments of the telescope `R` of the recursive results of the fields, substituted by the closed
substitution `θ'` of its scope, in a signature whose names are distinct and whose liftings are
those of its types: `θ` gives the fields the terms `t̄₁` and their types the types of the closed
telescope `Θ` at these terms, the lifting of the block substituted by `θ` and `θ'` is the closed
lifting `ρ₁` of the first side, and `R` is a telescope of a meaningful context, of which `θ'` is a
substitution.
The terms are related, at each field whose nesting has a position, by an equality that the graph
of the nestings gives the type of the field, where the relation `(L D).2` at a position that holds
the type `D` of the block relates terms whose results are equal terms of the motive of `D`, and
does not read their computation; the types of the fields of the second side have the shape of
those of the first. -/
theorem EqSubst.resultTerms (hd : sig.Distinct)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.grades + 3) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    {ρ₁ ρ₂ : Lifting 0 [] []} {φ₁ φ₂ : Name → Term 0 [.var]} {n : Nat} {s : Quality}
    {L : Name → NestLeaf} (hL : ∀ D, ResultLeaf sig ι ρ₁ φ₁ φ₂ D (L D))
    (hLc : ∀ D, LeafCongr sig ι s (L D).2) {Δ' Δ : Scope} {ρ : Lifting 0 Δ' Δ}
    {ns : List (Nest Name)} {ps : List Parameter} {As xs : Terms 0 Δ} {ps' : List Parameter}
    {R : Telescope 0 Δ' ps'} (h : Terms.ResultTypes sig v ρ ns ps As xs R) :
    ∀ {θ : Subst 0 [] Δ} {θ' : Subst 0 [] Δ'}, Lifting.Substitutes θ θ' ρ ρ₁ →
      ∀ {ctx : Context 0 Δ'}, ValidCtx₀ sig ι (ctx.append R) → EqSubst sig ι ctx θ' θ' →
      ∀ {Θ : Telescope 0 [] ps} {ts₁ ts₂ : Args 0 [] ps} {As₂ : Terms 0 []}
        {rs₁ rs₂ : Args 0 [] ps'},
        As.subst θ = Θ.typesAt ts₁ → xs.subst θ = ts₁.terms →
        Terms.NestedRel sig ι n s L ns Θ ts₁.terms ts₂.terms →
        Terms.Similar ns (Θ.typesAt ts₁) As₂ →
        Terms.ResultTerms sig v ρ₁ φ₁ ns ps (Θ.typesAt ts₁) ts₁.terms rs₁ →
        Terms.ResultTerms sig v ρ₂ φ₂ ns ps As₂ ts₂.terms rs₂ →
        EqSubst sig ι (Context.empty.append (R.subst θ')) rs₁.toSubst rs₂.toSubst := by
  have hid : ∀ {a} (y : Var [] a), ρ₁.ren y = y := fun y => nomatch y
  induction h with
  | nil =>
    intro θ θ' _ ctx _ _ Θ ts₁ ts₂ As₂ rs₁ rs₂ _ _ _ _ _ _
    cases rs₁
    cases rs₂
    exact (EqSubst.empty_iff _ _).2 trivial
  | plain h ih =>
    intro θ θ' hs ctx hctx hθ' Θ ts₁ ts₂ As₂ rs₁ rs₂ hAs hxs hN hS hr₁ hr₂
    cases Θ with
    | cons q _ A₁ Θ =>
      cases ts₁ with
      | cons t₁ ts₁ =>
        cases ts₂ with
        | cons t₂ ts₂ =>
          rw [Terms.subst, Telescope.typesAt] at hAs
          rw [Terms.subst, Args.terms] at hxs
          injection hAs with _ hA hAs
          injection hxs with _ hx hxs
          subst hA hx
          rw [Telescope.typesAt, Args.terms] at hr₁
          rw [Args.terms] at hr₂
          obtain ⟨-, hN₂⟩ := hN
          cases hr₁ with
          | plain hr₁ =>
            cases hr₂ with
            | plain hr₂ =>
              obtain ⟨-, hS₂⟩ := hS
              exact ih hs hctx hθ' hAs hxs hN₂ hS₂ hr₁ hr₂
  | @recursive _ _ ρ D _ p _ _ _ x _ _ b R hD h ih =>
    intro θ θ' hs ctx hctx hθ' Θ ts₁ ts₂ As₂ rs₁ rs₂ hAs hxs hN hS hr₁ hr₂
    cases Θ with
    | cons q _ A₁ Θ =>
      cases ts₁ with
      | cons t₁ ts₁ =>
        cases ts₂ with
        | cons t₂ ts₂ =>
          rw [Terms.subst, Telescope.typesAt] at hAs
          rw [Terms.subst, Args.terms] at hxs
          injection hAs with _ hA hAs
          injection hxs with _ hx hxs
          subst hA hx
          rw [Telescope.typesAt, Args.terms] at hr₁
          rw [Args.terms] at hr₂
          obtain ⟨hN₁, hN₂⟩ := hN
          cases hr₁ with
          | recursive hr₁ =>
            cases hr₂ with
            | recursive hr₂ =>
              obtain ⟨-, hS₂⟩ := hS
              obtain ⟨F, hF, hFt⟩ := hN₁ (fun h => nomatch h)
              have hLD := hL D
              have hF' : NestRel sig ι n (fun m _ => levelRel sig ι m) s s (.direct (L D)) _ F :=
                hF
              generalize L D = leaf at hF' hLD
              obtain ⟨T, Rl⟩ := leaf
              cases hF' with
              | direct _ _ =>
                have he : ValidEqTerm₀ sig ι ((φ₁ D).subst₀ (Subst₀.single (x.subst θ)))
                    ((φ₂ D).subst₀ (Subst₀.single t₂))
                    ((b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))).subst θ') := by
                  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ θ') b.motive,
                    hs.subst_rename₀ x, Term.rename_id_of hid]
                  exact hLD (b.subst θ θ') (by rw [hs.block, hD]; rfl) _ _ hFt
                have hctx' : ValidCtx₀ sig ι ((ctx.var _).append R) := hctx
                exact (EqSubst.args_cons_subst_iff θ').2 ⟨he,
                  ih (hs.ofSnoc (e := .var) _) hctx'
                    ((EqSubst.var_iff ..).2 ⟨hθ', he.trans he.symm⟩) hAs hxs hN₂ hS₂ hr₁ hr₂⟩
  | @nested _ _ ρ ms _ p _ _ _ x _ _ A' l R hA h ih =>
    intro θ θ' hs ctx hctx hθ' Θ ts₁ ts₂ As₂ rs₁ rs₂ hAs hxs hN hS hr₁ hr₂
    cases Θ with
    | cons q _ A₁ Θ =>
      cases ts₁ with
      | cons t₁ ts₁ =>
        cases ts₂ with
        | cons t₂ ts₂ =>
          rw [Terms.subst, Telescope.typesAt] at hAs
          rw [Terms.subst, Args.terms] at hxs
          injection hAs with _ hA hAs
          injection hxs with _ hx hxs
          subst hA hx
          rw [Telescope.typesAt, Args.terms] at hr₁
          rw [Args.terms] at hr₂
          obtain ⟨hN₁, hN₂⟩ := hN
          cases hr₁ with
          | nested he₁ hr₁ =>
            cases hr₂ with
            | nested he₂ hr₂ =>
              obtain ⟨hS₁, hS₂⟩ := hS
              obtain ⟨F, hF, hFt⟩ := hN₁ (fun h => nomatch h)
              have hL' := hA.subst hs
              rw [hs.subst_rename₀ x, Term.rename_id_of hid] at hL'
              have hctx' : ValidCtx₀ sig ι ((ctx.var A').append R) := hctx
              have hty : ValidType₀ sig ι (A'.subst θ') :=
                ((validCtx₀_var ctx A').1 (ValidCtx₀.append_left hctx')).2 θ' θ' hθ'
              have he := NestRel.resultSound (v := v) hd hlifts hF
                (Nest.map_rel₃ (r := fun a _ _ => LeafCongr sig ι s a.2) (f := L) (g := L)
                  (h := L) hLc (.inst ms))
                (Nest.rel_map (r := ResultLeaf sig ι ρ₁ φ₁ φ₂) (f := L) hL (.inst ms)) _ _ hFt
                _ _ _ _ l hS₁ he₁ he₂ hL' hty
              exact (EqSubst.args_cons_subst_iff θ').2 ⟨he,
                ih (hs.ofSnoc (e := .var) _) hctx'
                  ((EqSubst.var_iff ..).2 ⟨hθ', he.trans he.symm⟩) hAs hxs hN₂ hS₂ hr₁ hr₂⟩

end Sic.Core
