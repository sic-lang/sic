module

public import Sic.Core.Lifting.Recursion
public import Sic.Core.Typing.Lifting.Types
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Identity
import Sic.Core.Typing.Levels
import Sic.Core.Typing.Lifting.Context
import Sic.Core.Typing.Lifting.Observations
import Sic.Core.Typing.Prelude
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature

/-!
# Typing of the Destructors Lifted

The destructors of the lifting of a codata type of annex 20 of RFC 36 are destructors of the sort of
the lifting, in the context of a typed lifting, when the type that they lift is a codata type of a
well-formed signature without recursive destructor, and the level of its sort is below the level of
the sort of the lifting.

The destructors lifted are those of the type at the observations of a term `t` of an instance of it
at variables, which the lifting takes as its parameter `y`: the arguments of a destructor, at these
observations, are a telescope of the context of `t`, and so are they, renamed and used more, in the
context of the lifting; its result, at these observations, is a type of which the observation of `t`
by the destructor is a term, so that its lifting at this observation is a type.

The proof is by structural recursion on the destructors that are lifted, as the relation of their
lifting is: each destructor lifted extends the context of the lifting by a second-order variable,
which no variable lifted is.
The destructors are the last ones of the type, as `link` states, as for their typing at the
observations of a term.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {k : Nat}

/-! ## Telescopes in a Sort -/

/-- A telescope in a sort is a telescope in each sort that bounds it. -/
theorem WfTelescope.mono {Γ : Scope} {κ κ' : Universe k} (hκ : κ ≼ κ') :
    {ps : List Parameter} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
      WfTelescope sig ctx Θ κ → WfTelescope sig ctx Θ κ'
  | _, _, _, .nil hctx => .nil hctx
  | _, _, _, .cons hA hκ₁ hΘ hp =>
    .cons hA (Universe.preorder.trans hκ₁ hκ) (WfTelescope.mono (Γ := .var :: Γ) hκ hΘ) hp

/-! ## Telescopes Used More -/

/-- A telescope in a sort, whose entries are used `r` times more, is a telescope in this sort: an
entry without use at run time stays one. -/
theorem WfTelescope.scale {Γ : Scope} {κ : Universe k} (r : Grade) :
    {ps : List Parameter} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
      WfTelescope sig ctx Θ κ → WfTelescope sig ctx (Θ.scale r) κ
  | _, _, _, .nil hctx => .nil hctx
  | _, _, _, .cons hA hκ₁ hΘ hp =>
    .cons hA hκ₁ (WfTelescope.scale (Γ := .var :: Γ) r hΘ)
      (fun h => Mode.mul_mode_ne_oneOne r _ (hp h))

/-- A term of a scope extended by as many variables, one more of which is in the scope. -/
theorem Term.cast_extend_succ {Γ : Scope} {n m : Nat} (h' : n = m) (h : n + 1 = m + 1)
    (B : Term k (Γ.extend (n + 1))) :
    (h ▸ B : Term k (Γ.extend (m + 1))) = (h' ▸ B : Term k (Scope.extend (.var :: Γ) m)) := by
  subst h'
  rfl

/-- A term of a sort in a context extended by a telescope is one in the context extended by the
telescope whose entries are used `r` times more, which has the same types. -/
theorem HasType.append_scale {Γ : Scope} (r : Grade) {κ : Universe k} :
    {ps : List Parameter} → {ctx : Context k Γ} → {Θ : Telescope k Γ ps} →
      {B : Term k (Γ.extend ps.length)} →
      (h : ps.length = (ps.map (Parameter.scale r)).length) →
      HasType sig (ctx.append Θ) B (.sort κ) →
        HasType sig (ctx.append (Θ.scale r)) (h ▸ B) (.sort κ)
  | [], _, .nil, _, _, hB => hB
  | _ :: ps, _, .cons _ _ _ _, B, h, hB => by
    have h' : ps.length = (ps.map (Parameter.scale r)).length := (List.length_map _).symm
    rw [Term.cast_extend_succ h' h B]
    exact HasType.append_scale (Γ := .var :: Γ) r h' hB

/-! ## Observation of a Term -/

variable {decl : TypeDeclaration} {D : Name}
  {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level k)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}

-- ADE: none.
/-- The observation of a term of an instance of a codata type by a destructor, as an abstraction
over the variables of its telescope, is a term of its result, in the context extended by this
telescope, both at the observations of the term by the destructors before it. -/
theorem HasType.observation (hT : sig.HasCodataType D decl T)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {Γ : Scope} {ctx : Context k Γ}
    {as : InstanceArgs k Γ decl.scope} {t : Term k Γ}
    (has : HasInstanceArgs sig ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (ht : HasType sig ctx t (.inst D qs ls ps as)) {d : Name} {p q ς : Grade}
    {ps' : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps'}
    {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership Grade ps'.length}
    (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ)
    (hΘ : WfCtx sig (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
      (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))) :
    HasType sig
      (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
        (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
      (t.observation D qs ls ps as d ps')
      ((B.substLevels (ls.getFin hl)).subst
        (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst))) := by
  have hw := TypedRen.weakenN hΘ
  have hbs := HasArgs.bound hΘ
  rw [Telescope.rename_subst_of
    (fun x => hd.obsSubst_observation_rename (Ren.weakenN ps'.length) D qs ls ps as t x)] at hbs
  have h := HasType.obs hT hq hl hp hadm hd (stableUnderRenaming.hasInstanceArgs has hw)
    (stableUnderRenaming.hasType ht hw) hbs
  rw [← Term.rename_subst_of (Subst.liftN_rename_after_of ps'.length
      (fun x => hd.obsSubst_observation_rename (Ren.weakenN ps'.length) D qs ls ps as t x)),
    Term.instantiate_bound_rename] at h
  exact h

/-! ## Sort and Names of a Lifting -/

/-- A level below a level is below this level joined to others. -/
theorem Level.le_joins {l' : Level k} :
    (ls : List (Level k)) → (l : Level k) → l' ≤ l → l' ≤ l.joins ls
  | [], _, h => h
  | l₁ :: ls, l, h =>
    Level.le_joins ls (.max l l₁) fun ρ => Nat.le_trans (h ρ) (Nat.le_max_left _ _)

/-- The destructors lifted are among the destructors that are lifted, in their order. -/
theorem Destructors.Lifts.sublist {Γ₀ : Scope} {v : Lifting.Variables} {κ : Universe k}
    {o : Name → (ps : List Parameter) → Term k (Γ₀.extend ps.length)} :
    {Γ' : Scope} → {ρ : Lifting k Γ' Γ₀} → {Ξ : Scope} → {θ : Subst k Γ₀ Ξ} → {ns : List Name} →
      {ds : Destructors k Ξ ns} → {ns' : List Name} → {ds' : Destructors k Γ' ns'} →
      Destructors.Lifts sig v κ o ρ @θ ds ds' → ns'.Sublist ns
  | _, _, _, _, _, _, _, _, .nil => .slnil
  | _, _, _, _, _, _, _, _, .lifted _ _ h => (Destructors.Lifts.sublist h).cons_cons _
  | _, _, _, _, _, _, _, _, .absent _ h => (Destructors.Lifts.sublist h).cons _

/-! ## Typing of the Destructors Lifted -/

/-- The grade of the result of a destructor of a lifting whose motives are propositions has no use
at run time. -/
theorem Lifting.resultGrade_prop_mode (p : Grade) :
    (Lifting.resultGrade .prop p).mode ≠ .oneOne :=
  Mode.mul_zeroOne_grade_mode_ne_oneOne p.mode

-- ADE: none.
/-- The destructors of a codata type of a well-formed signature, none of which is recursive, at an
instance that its constraint admits, lifted at a term of this instance at variables that a typed
renaming of its parameters gives, are destructors of the lifting of the type, in the sort of the
lifting, whose level is above the level of the sort of the type, in the context of a typed lifting
whose motives have the quality of the lifting, and which lifts no type of a block.
The destructors are the last ones of the type `T`, at the observations of the term by those before
them, as `link` states. -/
theorem Destructors.Lifts.wfDestructors {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {S : List Nat}
    {ns₀ : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns₀}
    {I : Instance (decl.sorts + 1) (decl.grades + 3)} {qs : List Quality}
    {ls : List (Level (decl.levels + S.length))} {ps : List Grade} {hq : qs.length = decl.sorts}
    {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
    (hT : sig.HasCodataType D decl T) (hadm : decl.constraint (.ofLists qs ps hq hp))
    {Γ₀ : Scope} {ctx₀ : Context (decl.levels + S.length) Γ₀} {α : Ren Γ₀ decl.scope}
    (hα : TypedRen sig ctx₀ α
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {t : Term (decl.levels + S.length) Γ₀}
    (ht : HasType sig ctx₀ t (.inst D qs ls ps ((InstanceArgs.identity decl.scope).rename α)))
    {v : Lifting.Variables} {κ : Universe (decl.levels + S.length)}
    (hκ : ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).level ≤ κ.level) :
    {Ξ : Scope} → {ns : List Name} → (ds : Destructors decl.levels Ξ ns) →
      ∀ (Γ' : Scope) (ρ : Lifting (decl.levels + S.length) Γ' Γ₀)
        (θ : Subst (decl.levels + S.length) Γ₀ Ξ) (ns' : List Name)
        (ds' : Destructors (decl.levels + S.length) Γ' ns')
        (ctx' : Context (decl.levels + S.length) Γ')
        (as' : InstanceArgs (decl.levels + S.length) Γ' (.var :: decl.scope.lifted S))
        (ν' : Nesting Nat Γ'), (∀ (e : Scope.Entry) (x : Var Γ' e), ν' x = .plain) →
        Destructors.Lifts sig v κ
          (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α)) ρ @θ
          (ds.substLevels (ls.getFin hl)) ds' →
        Lifting.Typed sig v.quality ctx' ρ ctx₀ → (∀ D', ρ.block D' = none) → Subst.Neutral @θ →
        (∀ r ∈ ds.recursion decl.names, r = none) →
        (∀ {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ' : Scope}
          {Θ : Telescope decl.levels Ξ' ps'} {B : Term decl.levels (Ξ'.extend ps'.length)}
          {ψ : ResultOwnership Grade ps'.length} (h : Destructors.Pos d p q ς ds Ξ' Θ B ψ),
          ∃ hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ' Θ B ψ, ∀ {a} (x : Var Ξ' a),
            hd.obsSubst
                (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α))
                ((InstanceArgs.identity decl.scope).rename α).toSubst x =
              h.obsSubst
                (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α)) @θ x) →
        WfDestructors sig (decl.lifting D S ns₀ body) I @ν' as' ctx' ds' κ
  | _, _, .nil => fun _ _ _ _ _ _ _ _ _ h hρ _ _ _ _ => by
    cases h
    exact .nil hρ.ren.wfCtx
  | _, _, .cons (d := d) (ps := ps') p q ς Θ B ψ ds =>
    fun Γ' ρ θ ns' ds' ctx' as' ν' hν h hρ hρb hθ hrec link => by
    have hrec' : ∀ r ∈ ds.recursion decl.names, r = none :=
      fun r hr => hrec r (List.mem_cons_of_mem _ hr)
    cases h with
    | absent _ hds =>
      exact Destructors.Lifts.wfDestructors hT hadm hα ht hκ ds _ _ _ _ _ _ as' @ν' hν hds hρ
        hρb (hθ.snoc (.obs ..)) hrec' (fun h' => link (.there h'))
    | lifted hB hκ' hds =>
      obtain ⟨hd, hx⟩ := link .here
      have hx : ∀ {a} (x : Var _ a),
          hd.obsSubst (t.observation D qs ls ps ((InstanceArgs.identity decl.scope).rename α))
            ((InstanceArgs.identity decl.scope).rename α).toSubst x = θ x := hx
      have hP := stableUnderLevels.wfCtx (ls.getFin hl)
        ((presuppositions.wfCtx hα.wfCtx).wfCtx_params hT.1 hadm)
      have hn : B.blockName decl.names = none := hrec _ List.mem_cons_self
      obtain ⟨hΘ₀, hB₀⟩ := hd.hasType_observations hT hadm hα ht
      obtain ⟨κ₁, _, hBσ⟩ := hB₀ hn
      have hΘctx := contextPresuppositions.hasType hBσ
      have hobs := HasType.observation hT hadm
        (stableUnderRenaming.hasInstanceArgs (HasInstanceArgs.identity hP) hα) ht hd hΘctx
      rw [Telescope.subst_congr hx] at hΘ₀ hBσ hobs hΘctx
      rw [Term.subst_congr (Subst.liftN_congr ps'.length hx)] at hBσ hobs
      have he := stableUnderRenaming.hasType hobs (hρ.ren.liftN hΘctx)
      have hB' := HasType.append_scale v.recursion (List.length_map _).symm
        (Term.Lifts.hasType (hρ.liftN hΘctx) hB hBσ (by rw [Lifting.liftN_ren]; exact he))
      have hκ₀ : (⟨.type, ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).level⟩ :
          Universe (decl.levels + S.length)) ≼ ⟨.type, κ.level⟩ := ⟨fun h => h, hκ⟩
      refine .cons ?_ (Term.nest_plain (Nesting.liftN_plain _ hν) _)
        (((stableUnderRenaming.wfTelescope hΘ₀ hρ.ren).mono hκ₀).scale v.recursion)
        hB' hκ' (fun hs => ?_) ?_
      · exact (Term.blockName_cast [Lifting.name D S] _ _).trans
          (hB.blockName (Lifting.liftN_block _ hρb)
            (hT.2.2 ▸ TypeDeclaration.codata_name_mem_names hT.2.1)
            (Term.blockName_subst_neutral (hθ.liftN _) decl.names _
              ((Term.blockName_substLevels decl.names _ B).trans hn)) S)
      · exact (show v.quality = .prop from hs) ▸ Lifting.resultGrade_prop_mode p
      · exact Destructors.Lifts.wfDestructors hT hadm hα ht hκ ds _ _ _ _ _ _
          (as'.rename Ren.weaken) (Nesting.lift @ν') (Nesting.lift_plain hν) hds
          (hρ.weakenSecondOrder (.secondOrder (.ofSort hB'))) (Lifting.weaken_block hρb)
          (hθ.snoc (.obs ..)) hrec'
          (fun h' => link (.there h'))

end Sic.Core
