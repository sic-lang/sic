module

public import Sic.Core.Typing.Renaming
import Sic.Core.Typing.Extension
import Sic.Core.Typing.Identity
import Sic.Core.Typing.Levels
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Reflexivity
import Sic.Core.Typing.Signature

/-!
# Typing at the Observations of a Term

The arguments and the result of a destructor of a codata type of annex 15 of RFC 36, in which the
destructors before it are the observations of a term of an instance of the type at variables, are
typed in the context of the term: the lifting of a codata type declares each of its destructors at
the arguments of the destructor that it lifts, and lifts its result, both at the observations of
the parameter `y`.

The substitution of the destructors before a position by the observations of a term is a
substitution of the second order, which gives a destructor an abstraction that is not a variable.
The substitutions that give each parameter a variable, and each destructor before a position the
observation of a term by it, are a family that `Subst.Liftable` accepts: the rules `(d)` and
`(d_≡)` type the observation at arguments of the telescope of the destructor, substituted.
The arguments of the instance are variables, so that an application of a parameter stays one: the
stability of the typing under the substitutions that give a parameter any abstraction would need the
equality of a type substituted by equal substitutions.

The judgment of the destructors of a block types each destructor in the context of the destructors
before it that are not recursive, while a position has them all: the proof follows this judgment,
at the destructors renamed in the scope of the position, where the substitution of the position
gives each variable what the substitution of the judgment gives the variable that it renames.

ADE have no declared types.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat} {decl : TypeDeclaration} {D : Name}
  {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level k)} {ps : List Grade} {hqp : Instance.AsMany decl.sorts decl.grades qs ps}
  {hl : ls.length = decl.levels}

/-! ## Substitutions of Observations -/

/-- The substitution `θ` of the context `Ξ` in the context `Γ` observes the term `t` of the instance
`D.{s̄; l̄; p̄} ā` of the codata type `T`: it gives each variable a variable, declared with its type,
substituted, and each second-order variable either a variable, declared with its telescope and its
type, substituted, or the observation of `t` by a destructor of `T`, whose telescope and result, at
the observations of `t` by the destructors before it, are this telescope and this type,
substituted. -/
structure Subst.Observes (sig : Signature) {k : Nat} {decl : TypeDeclaration} (D : Name)
    (T : CodataType decl.sorts decl.grades decl.levels decl.scope) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels) {Γ Ξ : Scope}
    (as : InstanceArgs k Γ decl.scope) (t : Term k Γ) (ctx' : Context k Γ) (θ : Subst k Γ Ξ)
    (ctx : Context k Ξ) : Prop where
  /-- The arguments of the instance are arguments of its parameters. -/
  args : HasInstanceArgs sig ctx' as
    ((decl.params hqp.inst).substLevels (ls.getFin hl))
  /-- The term is a term of the instance. -/
  term : HasType sig ctx' t (.inst D qs ls ps as)
  /-- The image of a variable is a variable, declared with its type, substituted. -/
  varIn : ∀ {x : Var Ξ .var} {A : Term k Ξ}, ctx.VarIn x A →
    ∃ y, θ x = Var.eta y ∧ ctx'.VarIn y (A.subst θ)
  /-- The image of a second-order variable is a variable, declared with its telescope and its type,
  substituted, or the observation of the term by a destructor, whose telescope and result are this
  telescope and this type, substituted. -/
  secondOrderIn : ∀ {ps' : List Parameter} {ψ : ResultOwnership Grade ps'.length}
    {X : Var Ξ (.secondOrder ps' ψ)} {Θ : Telescope k Ξ ps'} {A : Term k (Ξ.extend ps'.length)},
    ctx.SecondOrderIn X Θ A →
      (∃ Y, θ X = Var.eta Y ∧ ctx'.SecondOrderIn Y (Θ.subst θ) (A.subst (Subst.liftN _ θ))) ∨
      ∃ (d : Name) (p q ς : Grade) (Ξ' : Scope) (Θ' : Telescope decl.levels Ξ' ps')
        (B' : Term decl.levels (Ξ'.extend ps'.length))
        (hd : (T.body hqp.inst).Pos d p q ς Ξ' Θ' B' ψ),
        θ X = t.observation D qs ls ps as d ps' ∧
        Θ.subst θ = (Θ'.substLevels (ls.getFin hl)).subst
          (hd.obsSubst (t.observation D qs ls ps as) as.toSubst) ∧
        A.subst (Subst.liftN _ θ) = (B'.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))

/-- The substitutions that observe a term of an instance of the codata type `T`. -/
def Subst.Observes.Base (sig : Signature) {k : Nat} {decl : TypeDeclaration} (D : Name)
    (T : CodataType decl.sorts decl.grades decl.levels decl.scope) (qs : List Quality)
    (ls : List (Level k)) (ps : List Grade) (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    (hl : ls.length = decl.levels) {Γ Ξ : Scope}
    (ctx' : Context k Γ) (θ : Subst k Γ Ξ) (ctx : Context k Ξ) : Prop :=
  ∃ (as : InstanceArgs k Γ decl.scope) (t : Term k Γ),
    Subst.Observes sig D T qs ls ps hqp hl as t ctx' @θ ctx

/-- A substitution that observes a term, followed by the observation of the term by a destructor,
observes the term, in the context extended by a second-order variable whose telescope and type,
substituted, are the telescope and the result of the destructor, at the observations of the term by
the destructors before it. -/
theorem Subst.Observes.snoc {Γ Ξ : Scope} {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
    {ctx' : Context k Γ} {θ : Subst k Γ Ξ} {ctx : Context k Ξ}
    (h : Subst.Observes sig D T qs ls ps hqp hl as t ctx' @θ ctx) {d : Name} {p q ς : Grade}
    {ps' : List Parameter} {ψ : ResultOwnership Grade ps'.length} {Ξ' : Scope}
    {Θ' : Telescope decl.levels Ξ' ps'} {B' : Term decl.levels (Ξ'.extend ps'.length)}
    (hd : (T.body hqp.inst).Pos d p q ς Ξ' Θ' B' ψ) {Θ : Telescope k Ξ ps'}
    {B : Term k (Ξ.extend ps'.length)}
    (hΘ : Θ.subst θ = (Θ'.substLevels (ls.getFin hl)).subst
      (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))
    (hB : B.subst (Subst.liftN _ θ) = (B'.substLevels (ls.getFin hl)).subst
      (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))) :
    Subst.Observes sig D T qs ls ps hqp hl as t ctx'
      (Subst.snoc (e := .secondOrder ps' ψ) θ (t.observation D qs ls ps as d ps'))
      (ctx.secondOrder Θ B ψ) where
  args := h.args
  term := h.term
  varIn := fun
    | .succSecondOrder (A := A) hx => by
      obtain ⟨y, hy, hyin⟩ := h.varIn hx
      refine ⟨y, hy, ?_⟩
      rw [Term.subst_snoc_rename_weaken]
      exact hyin
  secondOrderIn := fun
    | .zero => by
      refine .inr ⟨d, p, q, ς, Ξ', Θ', B', hd, rfl, ?_, ?_⟩
      · rw [Telescope.subst_snoc_rename_weaken]
        exact hΘ
      · rw [Term.subst_liftN_snoc_rename_weaken]
        exact hB
    | .succSecondOrder hX => by
      rw [Telescope.subst_snoc_rename_weaken, Term.subst_liftN_snoc_rename_weaken]
      exact h.secondOrderIn hX

/-- A substitution that observes a term, lifted under variables, observes the term, renamed, when
the context of the substitution is well formed. -/
theorem Subst.Observes.Base.lifted {Γ Ξ : Scope} {ctx' : Context k Γ} {θ : Subst k Γ Ξ}
    {ctx : Context k Ξ} :
    Subst.Lifted (@Subst.Observes.Base sig k decl D T qs ls ps hqp hl) ctx' @θ ctx →
      WfCtx sig ctx' → Subst.Observes.Base sig D T qs ls ps hqp hl ctx' @θ ctx
  | .base h, _ => h
  | .var (θ := θ) _ h, .var hB => by
    obtain ⟨as, t, hO⟩ := Subst.Observes.Base.lifted h (contextPresuppositions.wfType hB)
    have hw := TypedRen.weaken (.var hB)
    refine ⟨as.rename Ren.weaken, t.rename Ren.weaken,
      stableUnderRenaming.hasInstanceArgs hO.args hw, stableUnderRenaming.hasType hO.term hw,
      ?_, ?_⟩
    · intro x A hx
      cases hx with
      | zero => exact ⟨.zero, rfl, by rw [Term.subst_lift_rename_weaken]; exact .zero⟩
      | succVar hx =>
        obtain ⟨y, hy, hyin⟩ := hO.varIn hx
        refine ⟨y.succ, ?_, by rw [Term.subst_lift_rename_weaken]; exact .succVar hyin⟩
        show Term.rename _ _ = _
        dsimp only
        rw [hy]
        exact Var.eta_rename Ren.weaken y
    · intro ps' ψ X Θ A hX
      cases hX with
      | succVar hX =>
        rw [Telescope.subst_lift_rename_weaken, Term.subst_liftN_lift_rename_weaken]
        rcases hO.secondOrderIn hX with ⟨Y, hY, hYin⟩ | ⟨d, p, q, ς, Ξ', Θ', B', hd, hθ, hΘ, hA⟩
        · refine .inl ⟨Y.succ, ?_, .succVar hYin⟩
          show Term.rename _ _ = _
          dsimp only
          rw [hY]
          exact Var.eta_rename Ren.weaken Y
        · refine .inr ⟨d, p, q, ς, Ξ', Θ', B', hd, ?_, ?_, ?_⟩
          · show Term.rename _ _ = _
            dsimp only
            rw [hθ]
            exact Term.observation_rename Ren.weaken D qs ls ps as t d ps'
          · rw [hΘ]
            exact Telescope.rename_subst_of
              (fun x => hd.obsSubst_observation_rename Ren.weaken D qs ls ps as t x) _
          · rw [hA]
            exact Term.rename_subst_of (Subst.liftN_rename_after_of ps'.length
              (fun x => hd.obsSubst_observation_rename Ren.weaken D qs ls ps as t x)) _

/-- The substitutions that observe a term of an instance of a codata type of the signature, which
its constraint admits, give what the stability of the typing asks of a family of substitutions: the
rules `(d)` and `(d_≡)` type the observation of the term at arguments. -/
theorem Subst.Observes.liftable (hT : sig.HasCodataType D decl T)
    (hadm : decl.constraint hqp.inst) :
    Subst.Liftable sig (@Subst.Observes.Base sig k decl D T qs ls ps hqp hl) where
  wfCtx := fun ⟨_, _, h⟩ => contextPresuppositions.hasType h.term
  secondOrder := fun hθ hX hts => by
    obtain ⟨as, t, hO⟩ := Subst.Observes.Base.lifted hθ (contextPresuppositions.hasArgs hts)
    rcases hO.secondOrderIn hX with ⟨Y, hY, hYin⟩ | ⟨d, p, q, ς, Ξ', Θ', B', hd, hθX, hΘ, hA⟩
    · rw [hY, Var.eta_instantiate]
      exact .secondOrder hYin hts
    · rw [hθX, Term.observation_instantiate, hA]
      exact .obs hT hqp hl hadm hd hO.args hO.term (hΘ ▸ hts)
  eqSecondOrder := fun hθ hX hts => by
    obtain ⟨as, t, hO⟩ := Subst.Observes.Base.lifted hθ (contextPresuppositions.eqArgs hts)
    rcases hO.secondOrderIn hX with ⟨Y, hY, hYin⟩ | ⟨d, p, q, ς, Ξ', Θ', B', hd, hθX, hΘ, hA⟩
    · rw [hY, Var.eta_instantiate, Var.eta_instantiate]
      exact .secondOrder hYin hts
    · rw [hθX, Term.observation_instantiate, Term.observation_instantiate, hA]
      exact .obs hT hqp hl hl hadm hd (EqInstanceArgs.refl hO.args) (fun _ _ => rfl)
        (.refl hO.term) (hΘ ▸ hts)
  varIn := fun hθ hx hctx => by
    obtain ⟨as, t, hO⟩ := Subst.Observes.Base.lifted hθ hctx
    obtain ⟨y, hy, hyin⟩ := hO.varIn hx
    rw [Term.var_subst_of hy]
    exact .var hctx hyin

/-! ## Destructors at the Observations of a Term -/

/-- The arguments and the result of a destructor at a position of destructors in a sort, renamed,
at a substitution that gives each variable what a substitution that observes a term gives the
variable that it renames, followed by the observations of the term by the destructors before the
position: the arguments are a telescope in the universe of the level of the sort, and the result,
when the destructor is not recursive, is in a sort that the sort bounds.
The observations are those of the destructors of `T`, of which the destructors renamed are the last
ones, as `link` states. -/
theorem WfDestructors.observations (hT : sig.HasCodataType D decl T)
    (hadm : decl.constraint hqp.inst) {Γ : Scope} {ctx' : Context k Γ}
    {as : InstanceArgs k Γ decl.scope} {t : Term k Γ} {ι : Instance decl.sorts decl.grades} :
    {Δ : Scope} → {ns : List Name} → {ν : Nesting Nat Δ} →
      {as₀ : InstanceArgs decl.levels Δ decl.scope} →
      {ctx : Context decl.levels Δ} → {ds : Destructors decl.levels Δ ns} →
      {κ : Universe decl.levels} → WfDestructors sig decl ι @ν as₀ ctx ds κ →
      ∀ (Ξ₀ : Scope) (ds' : Destructors decl.levels Ξ₀ ns) (β : Ren Ξ₀ Δ), ds' = ds.rename β →
      ∀ (θ' : Subst k Γ Ξ₀) (θ : Subst k Γ Δ), (∀ {a} (x : Var Δ a), θ' (β x) = θ x) →
      Subst.Observes sig D T qs ls ps hqp hl as t ctx' @θ (ctx.substLevels (ls.getFin hl)) →
      (∀ {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
        {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
        {ψ : ResultOwnership Grade ps'.length} (h : Destructors.Pos d p q ς ds' Ξ Θ B ψ),
        ∃ hd : (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ, ∀ {a} (x : Var Ξ a),
          hd.obsSubst (t.observation D qs ls ps as) as.toSubst x =
            h.obsSubst (t.observation D qs ls ps as) @θ' x) →
      ∀ {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
        {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
        {ψ : ResultOwnership Grade ps'.length} (h : Destructors.Pos d p q ς ds' Ξ Θ B ψ),
        WfTelescope sig ctx'
            ((Θ.substLevels (ls.getFin hl)).subst
              (h.obsSubst (t.observation D qs ls ps as) @θ'))
            ⟨.type, (κ.substLevels (ls.getFin hl)).level⟩ ∧
          (B.blockName decl.names = none → ∃ κ₁, κ₁ ≼ κ ∧
            HasType sig
              (ctx'.append ((Θ.substLevels (ls.getFin hl)).subst
                (h.obsSubst (t.observation D qs ls ps as) @θ')))
              ((B.substLevels (ls.getFin hl)).subst
                (Subst.liftN _ (h.obsSubst (t.observation D qs ls ps as) @θ')))
              (.sort (κ₁.substLevels (ls.getFin hl))))
  | _, _, _, _, _, _, _, .nil _ =>
    fun Ξ₀ ds' β e θ' θ hβ hO link {d p q ς ps' Ξ Θ B ψ} h => by
    rw [Destructors.rename] at e
    subst e
    nomatch h
  | _, _, _, _, ctx, _, κ, .cons (d := d₀) (ps := ps₀) (Θ := Θ₀) (B := B₀) (ψ := ψ₀) (ds := ds₀)
      (κ₁ := κ₁) _ _ hΘ hB hκ _ hds =>
    fun Ξ₀ ds' β e θ' θ hβ hO link {d p q ς ps' Ξ Θ B ψ} h => by
    rw [Destructors.rename] at e
    subst e
    have hΘ' : ((Θ₀.rename β).substLevels (ls.getFin hl)).subst @θ' =
        (Θ₀.substLevels (ls.getFin hl)).subst @θ := by
      rw [Telescope.substLevels_rename]
      exact Telescope.subst_rename_of hβ _
    have hB' : ((B₀.rename (Ren.liftN ps₀.length β)).substLevels (ls.getFin hl)).subst
          (Subst.liftN ps₀.length @θ') =
        (B₀.substLevels (ls.getFin hl)).subst (Subst.liftN ps₀.length @θ) := by
      rw [Term.substLevels_rename]
      exact Term.subst_rename_of (Subst.liftN_rename_of ps₀.length hβ) _
    cases h with
    | here =>
      refine ⟨?_, fun _ => ⟨κ₁, hκ, ?_⟩⟩
      · have h₁ := (Subst.Observes.liftable hT hadm).stable.wfTelescope
          (stableUnderLevels.wfTelescope (ls.getFin hl) hΘ) (.base ⟨as, t, hO⟩)
        rw [← hΘ'] at h₁
        exact h₁
      · have h₂ := stableUnderLevels.hasType (ls.getFin hl) hB
        rw [Context.substLevels_append] at h₂
        have h₃ := (Subst.Observes.liftable hT hadm).stable.hasType h₂
          (Subst.Lifted.append (Θ₀.substLevels (ls.getFin hl)) (.base ⟨as, t, hO⟩))
        rw [← hΘ', ← hB'] at h₃
        exact h₃
    | there h' =>
      obtain ⟨hd, hθ⟩ := link (.here (ds := ds₀.rename (Ren.lift β)))
      refine WfDestructors.observations hT hadm hds _ _ (Ren.lift β) rfl
        (Subst.snoc (e := .secondOrder ps₀ ψ₀) @θ' (t.observation D qs ls ps as d₀ ps₀))
        (Subst.snoc (e := .secondOrder ps₀ ψ₀) @θ (t.observation D qs ls ps as d₀ ps₀))
        (fun x => match x with
          | .zero => rfl
          | .succ x => hβ x)
        (hO.snoc hd ?_ ?_) (fun h'' => link (.there h'')) h'
      · rw [Telescope.substLevels_rename]
        exact (Telescope.subst_rename_of (fun x => (hθ (β x)).trans (hβ x)) _).symm
      · rw [Term.substLevels_rename]
        exact (Term.subst_rename_of
          (Subst.liftN_rename_of ps₀.length (fun x => (hθ (β x)).trans (hβ x))) _).symm
  | _, _, _, _, ctx, _, κ, .nested (d := d₀) (ps := ps₀) (Θ := Θ₀) (B := B₀) (ψ := ψ₀) (ds := ds₀)
      (κ₁ := κ₁) _ _ hΘ hB hκ _ hds =>
    fun Ξ₀ ds' β e θ' θ hβ hO link {d p q ς ps' Ξ Θ B ψ} h => by
    rw [Destructors.rename,
      Destructors.rename_rename_of (α₁ := Ren.lift β) (α₂ := Ren.weaken)
        (α₃ := fun x => (β x).succ) (fun _ => rfl)] at e
    subst e
    have hΘ' : ((Θ₀.rename β).substLevels (ls.getFin hl)).subst @θ' =
        (Θ₀.substLevels (ls.getFin hl)).subst @θ := by
      rw [Telescope.substLevels_rename]
      exact Telescope.subst_rename_of hβ _
    have hB' : ((B₀.rename (Ren.liftN ps₀.length β)).substLevels (ls.getFin hl)).subst
          (Subst.liftN ps₀.length @θ') =
        (B₀.substLevels (ls.getFin hl)).subst (Subst.liftN ps₀.length @θ) := by
      rw [Term.substLevels_rename]
      exact Term.subst_rename_of (Subst.liftN_rename_of ps₀.length hβ) _
    cases h with
    | here =>
      refine ⟨?_, fun _ => ⟨κ₁, hκ, ?_⟩⟩
      · have h₁ := (Subst.Observes.liftable hT hadm).stable.wfTelescope
          (stableUnderLevels.wfTelescope (ls.getFin hl) hΘ) (.base ⟨as, t, hO⟩)
        rw [← hΘ'] at h₁
        exact h₁
      · have h₂ := stableUnderLevels.hasType (ls.getFin hl) hB
        rw [Context.substLevels_append] at h₂
        have h₃ := (Subst.Observes.liftable hT hadm).stable.hasType h₂
          (Subst.Lifted.append (Θ₀.substLevels (ls.getFin hl)) (.base ⟨as, t, hO⟩))
        rw [← hΘ', ← hB'] at h₃
        exact h₃
    | there h' =>
      exact WfDestructors.observations hT hadm hds _ _ (fun x => (β x).succ) rfl
        (Subst.snoc (e := .secondOrder ps₀ ψ₀) @θ' (t.observation D qs ls ps as d₀ ps₀)) @θ
        (fun x => hβ x) hO (fun h'' => link (.there h'')) h'
  | _, _, _, _, ctx, _, κ, .recursive (d := d₀) (ps := ps₀) (Θ := Θ₀) (ψ := ψ₀) (ds := ds₀) hD hΘ _
      hds =>
    fun Ξ₀ ds' β e θ' θ hβ hO link {d p q ς ps' Ξ Θ B ψ} h => by
    rw [Destructors.rename,
      Destructors.rename_rename_of (α₁ := Ren.lift β) (α₂ := Ren.weaken)
        (α₃ := fun x => (β x).succ) (fun _ => rfl)] at e
    subst e
    cases h with
    | here =>
      refine ⟨?_, fun hn => ?_⟩
      · have h₁ := (Subst.Observes.liftable hT hadm).stable.wfTelescope
          (stableUnderLevels.wfTelescope (ls.getFin hl) hΘ) (.base ⟨as, t, hO⟩)
        rw [← Telescope.subst_rename_of hβ, ← Telescope.substLevels_rename] at h₁
        exact h₁
      · simp [TypeDeclaration.blockInstance, Term.rename, Term.blockName, hD] at hn
    | there h' =>
      exact WfDestructors.observations hT hadm hds _ _ (fun x => (β x).succ) rfl
        (Subst.snoc (e := .secondOrder ps₀ ψ₀) @θ' (t.observation D qs ls ps as d₀ ps₀)) @θ
        (fun x => hβ x) hO (fun h'' => link (.there h'')) h'

/-- The arguments and the result of a destructor of a codata type of a well-formed signature, at an
instance that its constraint admits, at variables that a typed renaming of its parameters gives,
and at the observations of a term of this instance by the destructors before it: the arguments are
a telescope in the universe of the level of the sort of the type, and the result, when the
destructor is not recursive, is in a sort that this sort bounds. -/
theorem Destructors.Pos.hasType_observations (hT : sig.HasCodataType D decl T)
    (hadm : decl.constraint hqp.inst) {Γ : Scope} {ctx' : Context k Γ}
    {α : Ren Γ decl.scope}
    (hα : TypedRen sig ctx' α ((decl.params hqp.inst).substLevels (ls.getFin hl)))
    {t : Term k Γ}
    (ht : HasType sig ctx' t (.inst D qs ls ps ((InstanceArgs.identity decl.scope).rename α)))
    {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership Grade ps'.length}
    (hd : (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ) :
    WfTelescope sig ctx'
        ((Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst
            (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α))
            ((InstanceArgs.identity decl.scope).rename α).toSubst))
        ⟨.type, ((decl.sort hqp.inst).substLevels (ls.getFin hl)).level⟩ ∧
      (B.blockName decl.names = none → ∃ κ₁, κ₁ ≼ decl.sort hqp.inst ∧
        HasType sig
          (ctx'.append ((Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst
              (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α))
              ((InstanceArgs.identity decl.scope).rename α).toSubst)))
          ((B.substLevels (ls.getFin hl)).subst
            (Subst.liftN _ (hd.obsSubst
              (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α))
              ((InstanceArgs.identity decl.scope).rename α).toSubst)))
          (.sort (κ₁.substLevels (ls.getFin hl)))) := by
  have hsig := presuppositions.wfCtx hα.wfCtx
  obtain ⟨sig', hs, hdecl⟩ := hsig.wfTypeDeclaration hT.1
  replace hs := Signature.subset_of_cons_suffix hs
  cases hdecl with
  | data hb _ _ _ _ _ _ => exact absurd hT.2.1 (by simp [TypeDeclaration.codataTypes, hb])
  | codata hb _ hΔ hds _ _ _ =>
    have hP := stableUnderLevels.wfCtx (ls.getFin hl)
      (stableUnderExtension.wfCtx hs hsig (hΔ _ hadm))
    have hθ : ∀ {a} (x : Var decl.scope a),
        ((InstanceArgs.identity (k := k) decl.scope).rename α).toSubst x = Var.eta (α x) :=
      fun x => InstanceArgs.identity_rename_toSubst α x
    refine WfDestructors.observations hT hadm
      (stableUnderExtension.wfDestructors hs hsig (hds _ hadm T hT.2.1))
      _ _ (fun x => x) (Destructors.rename_id_of (fun _ => rfl) _).symm _ _ (fun _ => rfl)
      ⟨stableUnderRenaming.hasInstanceArgs (HasInstanceArgs.identity hP) hα, ht, ?_, ?_⟩
      (fun h => ⟨h, fun _ => rfl⟩) hd
    · intro x A hx
      refine ⟨α x, hθ x, ?_⟩
      rw [← Term.rename_eq_subst_of hθ]
      exact hα.varIn hx
    · intro ps' ψ X Θ A hX
      refine .inl ⟨α X, hθ X, ?_⟩
      rw [← Telescope.rename_eq_subst_of hθ, ← Term.rename_eq_subst_of (Subst.liftN_eta_of _ hθ)]
      exact hα.secondOrderIn hX

end Sic.Core
