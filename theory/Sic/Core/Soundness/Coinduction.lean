module

public import Sic.Core.Soundness.Signature
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Corecursors
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Levels
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Soundness.Transport
import Sic.Core.Syntax.Signature

/-!
# Soundness of the Rule of the Coinduction

The rule `(coind)` of annex 15 of RFC 36 keeps the meaning of annex 21, as `Rules` proves it of the
other rules: at a closed substitution of the context, the proof makes the two terms equal terms of
their instance, by `(eq_ν)`, which relates two terms when some relations, one for each type of the
block, relate them and are consistent with the clauses of the destructors.
The relations are those of the pairs of canonical terms that two closed terms of each type compute
to, which its relation `A_j` makes true; a branch of a destructor that is not recursive makes the
observations of the two terms equal, and a branch of a recursive destructor makes the relation of
the type of its result true at the observations, which compute to a pair of these relations.
On a proposition, any two proofs are equal.

ADE have no codata types.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

-- ADE: none.
/-- `(coind)` keeps the meaning: at a closed substitution of the context, the two terms are equal
terms of their instance, which `ValidTermΓ.of_equality_eq` makes any term a proof of their
equality. -/
theorem ValidTermΓ.coind {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {l' : Level 0} {t₁ t₂ t : Term 0 Γ} {As : Terms 0 (Γ.extend 2)}
    {gs : DestructorBranches 0 Γ} {h' : Nat} {A : Term 0 (Γ.extend 2)} {κs : Nat → Universe 0}
    (hh : decl.codataTypes[h']? = some T) (hA : As.get h' = some A)
    (hAl : As.length = decl.codataTypes.length)
    (hAt : ∀ j T' A', decl.codataTypes[j]? = some T' → As.get j = some A' →
      ValidTermΓ sig ι ((ctx.var (.inst T'.name qs ls ps as)).var
        ((Term.inst T'.name qs ls ps as).rename Ren.weaken)) A' (.sort ⟨.prop, l'⟩))
    (ht₁ : ValidTermΓ sig ι ctx t₁ (.inst D qs ls ps as))
    (ht₂ : ValidTermΓ sig ι ctx t₂ (.inst D qs ls ps as))
    (ht : ValidTermΓ sig ι ctx t ((A.subst₀ (Subst₀.liftN 1 (Subst₀.single t₁))).subst₀
      (Subst₀.single t₂)))
    (hgs : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length),
      decl.codataCases[i]? = some (j, T', d) →
      (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ →
      ∃ g, gs.get i = some ⟨0, 3, ps₁.length, g⟩)
    (hΘ : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length),
      decl.codataCases[i]? = some (j, T', d) →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      (Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
            T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst) =
        (Θ.substLevels (ls.getFin hl)).subst
          (hd.obsSubst ((Term.var₀ (.succ .zero) : Term 0 (Γ.extend 3)).observation
            T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst))
    (hB : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length),
      decl.codataCases[i]? = some (j, T', d) →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      (B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
            T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)) =
        (B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubst ((Term.var₀ (.succ .zero) : Term 0 (Γ.extend 3)).observation
            T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
    (hBt : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length) (A' : Term 0 (Γ.extend 2)),
      decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      B.blockName decl.names = none →
      ValidTermΓ sig ι ((((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
          ((Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
            T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
        (.sort (κs i)))
    (hgt : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length) (A' : Term 0 (Γ.extend 2))
        (g : Term 0 ((Γ.extend 3).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      B.blockName decl.names = none →
      gs.get i = some ⟨0, 3, ps₁.length, g⟩ →
      ValidTermΓ sig ι ((((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
          ((Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
        g
        (.equality (κs i).quality (κs i).level
          ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
          ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) d ps₁)
          ((Term.var₀ (.succ .zero) : Term 0 (Γ.extend 3)).observation T'.name qs ls ps
            (as.rename (Ren.weakenN 3)) d ps₁)))
    (hgr : ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length) (A' : Term 0 (Γ.extend 2)) (D' : Name) (j' : Nat)
        (A'' : Term 0 (Γ.extend 2)) (g : Term 0 ((Γ.extend 3).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) → As.get j = some A' →
      (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
      B.blockName decl.names = some D' → decl.names.idxOf? D' = some j' →
      As.get j' = some A'' →
      gs.get i = some ⟨0, 3, ps₁.length, g⟩ →
      ValidTermΓ sig ι ((((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
          ((Θ.substLevels (ls.getFin hl)).subst
            (hd.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
              T'.name qs ls ps (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst)))
        g
        ((((A''.rename (Ren.liftN 2 (Ren.weakenN 3))).rename
            (Ren.liftN 2 (Ren.weakenN ps₁.length))).subst₀
          (Subst₀.liftN 1 (Subst₀.single
            ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation T'.name qs ls
              ps (as.rename (Ren.weakenN 3)) d ps₁)))).subst₀
          (Subst₀.single ((Term.var₀ (.succ .zero) : Term 0 (Γ.extend 3)).observation T'.name
            qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)))) :
    ValidTermΓ sig ι ctx (.coind D qs ls ps as t₁ t₂ As t gs)
      (.equality ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).quality
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).level
        (.inst D qs ls ps as) t₁ t₂) := by
  obtain ⟨⟨hdecl, hT, rfl⟩, hv⟩ := hent.hasCodataType h
  have hctx := ht₁.1.1
  have hd := hctx.distinct
  -- The instance is a type of its sort, so that the equality is a proposition.
  have hI : ValidEqTermΓ sig ι ctx (.inst T.name qs ls ps as) (.inst T.name qs ls ps as)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) :=
    ValidEqTermΓ.inst hent h.hasDeclaredType hq hl hl hp hadm has
      (fun _ => Level.equivalence.refl _)
  refine ValidTermΓ.of_equality_eq (ValidEqTermΓ.equality hI ht₁ ht₂ (Level.equivalence.refl _))
    fun σ hσ => ?_
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · -- In a universe: the levels and the arguments of the instance at `σ`.
    let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
    let L := ls.getFin hl
    let a := as.subst σ
    have has' : EqSubst sig ι ((decl.params I).substLevels L) a.toSubst a.toSubst := has.2 σ σ hσ
    obtain ⟨S, hS, hU⟩ := hv.codataUnivRel hd hdecl hq hl hp hadm has' hs
    have hnames := hd.nodup hdecl
    have hn := TypeDeclaration.codataTypes_nodup hnames
    let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
    let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
    have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
    have hθ := EqSubst.levelEquiv
      (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has'
    have hmean : ∀ T' ∈ decl.codataTypes, _ := fun T' hT' =>
      (hv.destructors I hadm hT' ρ).2 _ _ hθ
    have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    have hlev : ∀ {T' : CodataType decl.sorts decl.grades decl.levels decl.scope} {s : Quality}
        {rs : Nat → Option TermRel} {S : ObsRel},
        DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
          ((T'.body I).substLevels L) a.toSubst S →
        DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
          ((T'.body I).substLevels Lρ) a.toSubst S := fun hS =>
      DesRel.levelEquiv hd (fun m _ => levelRel_levelInvariant hd m) hS
        (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
        (Subst.LevelEquiv.refl _)
    have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
        ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
      fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
        fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
    -- The instances of the block at the levels without variables, at the arguments.
    let Xi : Name → Term 0 [] := fun D' =>
      ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst a.toSubst
    have hX : ∀ D', Term.LevelEquiv (Xi D') (.inst D' qs ls ps a) := fun D' =>
      decl.blockInstance_atLevels_subst hq hl hp a D'
    -- The instances of the block are types of the universe, not propositions.
    have hcI : ∀ D', Computesι sig ι (.inst D' qs ls ps a) (.inst D' qs ls ps a) :=
      fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
    have hnp : ∀ T' ∈ decl.codataTypes, ¬ ComputesToProp sig ι (.inst T'.name qs ls ps a) :=
      fun T' hT' ⟨v', hv', k', b, hk⟩ => by
        cases Computesι.det hd (hcI _) hv'
        exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hU T' hT').1) hk
    -- A closed term of an instance computes to a corecursor, whose observations it has.
    have hcan : ∀ T' ∈ decl.codataTypes, ∀ {x v : Term 0 []},
        ValidEqTerm₀ sig ι x x (.inst T'.name qs ls ps a) → Computesι sig ι x v →
        ∃ o, v.CorecObservations T'.name o := fun T' hT' {x v} hx hxv => by
      obtain ⟨w, o, hw, hc⟩ := ValidEqTerm₀.computes_corec hd hmono hT' (hcI _)
        (levelRel_univ_iff.2 (hU T' hT').1) hx
      cases Computesι.det hd hw hxv
      exact ⟨o, hc⟩
    -- A closed term of an instance computes.
    have hcomp : ∀ T' ∈ decl.codataTypes, ∀ {x y : Term 0 []},
        ValidEqTerm₀ sig ι x y (.inst T'.name qs ls ps a) → ∃ v, Computesι sig ι x v :=
      fun T' hT' {x y} hx => by
        obtain ⟨-, w₁, -, -, -, hw₁, -⟩ := hx.2.1 (hnp T' hT')
        exact ⟨w₁, hw₁⟩
    -- Two terms of `Γ.extend 2` instantiated, at `σ`.
    let p₀ : Parameter := ⟨Grade.one, Grade.one⟩
    have hsnoc : ∀ c₁ c₂ : Term 0 [],
        @Eq (Subst 0 [] (Γ.extend 2))
          (Subst.append σ (Args.cons (p := p₀) c₁ (Args.cons (p := p₀) c₂ .nil)).toSubst)
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ c₁) c₂) := fun c₁ c₂ =>
      Subst.ext fun {b} (v : Var (.var :: .var :: Γ) b) => match b, v with
        | _, .zero => rfl
        | _, .succ .zero => rfl
        | _, .succ (.succ _) => rfl
    have hinst : ∀ (B : Term 0 (Γ.extend 2)) (c₁ c₂ : Term 0 []),
        (B.subst (Subst.liftN 2 σ)).instantiate (Args.cons (p := p₀) c₁ (Args.cons (p := p₀) c₂ .nil)) =
          B.subst (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ c₁) c₂) := fun B c₁ c₂ =>
      (Term.instantiate_eq_subst _ _).trans ((Term.subst_append (n := 2) σ
        (Args.cons (p := p₀) c₁ (Args.cons (p := p₀) c₂ .nil)).toSubst B).trans
        (congrArg (fun θ : Subst 0 [] (Γ.extend 2) => B.subst θ) (hsnoc c₁ c₂)))
    -- The substitutions of the contexts of the relations and of the branches.
    have hσ2 : ∀ (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (x y y' : Term 0 []),
        ValidEqTerm₀ sig ι x x (.inst T'.name qs ls ps a) →
        ValidEqTerm₀ sig ι y y' (.inst T'.name qs ls ps a) →
        EqSubst sig ι ((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken))
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y)
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y') := fun T' x y y' hx hy =>
      (EqSubst.var_iff _ _ _ _).2 ⟨(EqSubst.var_iff _ _ _ _).2 ⟨hσ, hx⟩,
        by rw [Term.subst_weaken]; exact hy⟩
    have hσ3 : ∀ (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (A' : Term 0 (Γ.extend 2)) (x y z : Term 0 []),
        ValidEqTerm₀ sig ι x x (.inst T'.name qs ls ps a) →
        ValidEqTerm₀ sig ι y y (.inst T'.name qs ls ps a) →
        ValidEqTerm₀ sig ι z z (A'.subst (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y)) →
        EqSubst sig ι (((ctx.var (.inst T'.name qs ls ps as)).var
          ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A')
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y) z)
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y) z) :=
      fun T' A' x y z hx hy hz => (EqSubst.var_iff _ _ _ _).2 ⟨hσ2 T' x y y hx hy, hz⟩
    -- An observation of a variable of the context of a branch, at a substitution of it.
    have hobs3 : ∀ (N : Name) (σ3 : Subst 0 [] (Γ.extend 3)) (X : Var (Γ.extend 3) .var) (d : Name)
        {ps₁ : List Parameter} (ts : Args 0 [] ps₁),
        ((Term.var₀ X).observation N qs ls ps (as.rename (Ren.weakenN 3)) d ps₁).subst
          (Subst.append σ3 ts.toSubst) =
          .obs N qs ls ps ((as.rename (Ren.weakenN 3)).subst σ3) (σ3 X) d ts.terms :=
      fun N σ3 X d ps₁ ts => by
        rw [← Term.subst_append, Term.observation_subst, Term.observation_subst_args]
        rfl
    -- The relations of the pairs of canonical terms of two closed terms of a type of the block
    -- that its relation makes true, joined with the equalities of the instances.
    let X : Name → TermRel := fun D' v w =>
      ∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (A' : Term 0 (Γ.extend 2)) (x y z : Term 0 []),
        decl.codataTypes[j]? = some T' ∧ T'.name = D' ∧ As.get j = some A' ∧
        ValidEqTerm₀ sig ι x x (.inst D' qs ls ps a) ∧ ValidEqTerm₀ sig ι y y (.inst D' qs ls ps a) ∧
        ValidEqTerm₀ sig ι z z (A'.subst (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y)) ∧
        Computesι sig ι x v ∧ Computesι sig ι y w
    let Y : Name → TermRel := fun D' v w =>
      CodataType.blockRel decl.codataTypes S D' v w ∨ X D' v w
    -- The relations of the recursive destructors relate alike the terms that compute alike.
    have hRF : ∀ (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) i R,
        ((T'.body I).recursionAt decl.names i).map (fun D' => (Y D').computed sig ι) = some R →
        ∀ {a₁ a₁' b₁ b₁' : Term 0 []}, (Quality.type = .prop ∨
          ((∀ w, Computesι sig ι a₁ w ↔ Computesι sig ι a₁' w) ∧
            ∀ w, Computesι sig ι b₁ w ↔ Computesι sig ι b₁' w)) → (R a₁ b₁ ↔ R a₁' b₁') := by
      intro T' i R hi a₁ a₁' b₁ b₁' hab
      cases hr : (T'.body I).recursionAt decl.names i with
      | none => rw [hr] at hi; cases hi
      | some D' =>
        rw [hr] at hi
        cases hi
        rcases hab with hab | ⟨ha, hb⟩
        · cases hab
        · exact ⟨fun ⟨v, w, hv, hw, h⟩ => ⟨v, w, (ha v).1 hv, (hb w).1 hw, h⟩,
            fun ⟨v, w, hv, hw, h⟩ => ⟨v, w, (ha v).2 hv, (hb w).2 hw, h⟩⟩
    -- The relations are consistent with the clauses of the destructors.
    have hcons : ∀ T' ∈ decl.codataTypes, ∀ v w, X T'.name v w → corecRel T'.name (S Y T') v w := by
      intro T' hT' v w hvw
      obtain ⟨j, T'', A', x, y, z, hj, hn', hA', hx, hy, hz, hxv, hyw⟩ := hvw
      cases List.eq_of_nodup_map hn (List.mem_of_getElem? hj) hT' hn'
      have h'' : sig.HasCodataType T'.name decl T' := ⟨hdecl, hT', rfl⟩
      have hσ3' := hσ3 T' A' x y z hx hy hz
      have has3 : (as.rename (Ren.weakenN 3)).subst
          (Subst.snoc (e := .var) (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y) z) = a :=
        InstanceArgs.subst_rename_of (fun _ => rfl) as
      -- At a destructor, the branch is meaningful at the two terms and at equal arguments, and
      -- the observations of each term are equal terms of the result at the first term.
      have hpre : ∀ (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length) (hpos : (T'.body I).Pos d p q ς Ξ Θ B ψ)
          (ts us : Args 0 [] ps₁),
          EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst
            (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst))) ts.toSubst us.toSubst →
          ∃ i : Nat, decl.codataCases[i]? = some (j, T', d) ∧
            EqSubst sig ι ((((ctx.var (.inst T'.name qs ls ps as)).var
                ((Term.inst T'.name qs ls ps as).rename Ren.weaken)).var A').append
                ((Θ.substLevels L).subst
                  (hpos.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
                    T'.name qs ls ps (as.rename (Ren.weakenN 3)))
                    (as.rename (Ren.weakenN 3)).toSubst)))
              (Subst.append (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                (Subst.snoc (e := .var) σ x) y) z) ts.toSubst)
              (Subst.append (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                (Subst.snoc (e := .var) σ x) y) z) us.toSubst) ∧
            ((B.substLevels L).subst (Subst.liftN _
              (hpos.obsSubst ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation
                T'.name qs ls ps (as.rename (Ren.weakenN 3)))
                (as.rename (Ren.weakenN 3)).toSubst))).subst
              (Subst.append (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                (Subst.snoc (e := .var) σ x) y) z) ts.toSubst) =
              (B.substLevels L).subst (Subst.append
                (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst) ∧
            ValidEqTerm₀ sig ι (.obs T'.name qs ls ps a x d ts.terms)
              (.obs T'.name qs ls ps a x d us.terms)
              ((B.substLevels L).subst (Subst.append
                (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst)) ∧
            ValidEqTerm₀ sig ι (.obs T'.name qs ls ps a y d ts.terms)
              (.obs T'.name qs ls ps a y d us.terms)
              ((B.substLevels L).subst (Subst.append
                (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst)) := by
        intro d p q ς ps₁ Ξ Θ B ψ hpos ts us hτ
        have hmem : (j, T', d) ∈ decl.codataCases := by
          have := TypeDeclaration.mem_casesFrom_of (f := CodataType.destructors) (i := 0) hj
            hpos.mem
          rwa [Nat.zero_add] at this
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
        -- The scope of the destructor at the substitution is that of the observations of a term.
        have hc : ∀ (X₀ : Var (Γ.extend 3) .var) (w₀ : Term 0 []),
            (Term.var₀ X₀).subst (Subst.snoc (e := .var) (Subst.snoc (e := .var)
              (Subst.snoc (e := .var) σ x) y) z) = w₀ → ∀ {a'} (u : Var Ξ a'),
            ((hpos.obsSubst ((Term.var₀ X₀).observation T'.name qs ls ps
              (as.rename (Ren.weakenN 3))) (as.rename (Ren.weakenN 3)).toSubst) u).subst
              (Subst.liftN a'.params.length (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                (Subst.snoc (e := .var) σ x) y) z)) =
            hpos.obsSubst (w₀.observation T'.name qs ls ps a) a.toSubst u := fun X₀ w₀ hw {_} u =>
          hpos.obsSubst_subst _ (o' := w₀.observation T'.name qs ls ps a)
            (fun d' ps' => (Term.observation_subst _ T'.name qs ls ps _ _ d' ps').trans
              (hw ▸ has3 ▸ rfl))
            (θ' := a.toSubst)
            (fun u => (InstanceArgs.toSubst_subst _ _ u).trans
              (congrArg (fun as' : InstanceArgs 0 [] decl.scope => as'.toSubst u) has3)) u
        have hcx := fun {a'} (u : Var Ξ a') => hc (.succ (.succ .zero)) x rfl u
        have hcy := fun {a'} (u : Var Ξ a') => hc (.succ .zero) y rfl u
        have hΘx := Telescope.subst_subst_of hcx (Θ.substLevels L)
        have hΘxy : (Θ.substLevels L).subst
              (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) =
            (Θ.substLevels L).subst
              (hpos.obsSubst (y.observation T'.name qs ls ps a) a.toSubst) := by
          exact (Telescope.subst_subst_of hcx _).symm.trans
            ((congrArg (fun Θ' => Telescope.subst (Subst.snoc (e := .var)
              (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y) z) Θ')
              (hΘ i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos)).trans (Telescope.subst_subst_of hcy _))
        have hBxy : (B.substLevels L).subst
              (Subst.liftN _ (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst)) =
            (B.substLevels L).subst
              (Subst.liftN _ (hpos.obsSubst (y.observation T'.name qs ls ps a) a.toSubst)) := by
          exact (Term.subst_subst_of (Subst.liftN_subst_of _ hcx) _).symm.trans
            ((congrArg (fun t => Term.subst (Subst.liftN ps₁.length (Subst.snoc (e := .var)
              (Subst.snoc (e := .var) (Subst.snoc (e := .var) σ x) y) z)) t)
              (hB i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos)).trans
              (Term.subst_subst_of (Subst.liftN_subst_of _ hcy) _))
        have hox := (ValidEqTerm₀.obs hd h'' hv hq hl hp hadm hpos has' hx
          (bs₁ := ts) (bs₂ := us) hτ).1
        have hoy := (ValidEqTerm₀.obs hd h'' hv hq hl hp hadm hpos has' hy
          (bs₁ := ts) (bs₂ := us) (by rw [← hΘxy]; exact hτ)).1
        rw [← hBxy] at hoy
        rw [Term.instantiate_eq_subst, Term.subst_append] at hox hoy
        refine ⟨i, hi, (EqSubst.append_append_iff _ _ _ _ _ _).2 ⟨hσ3',
          (congrArg (fun Θ' => EqSubst sig ι (Context.empty.append Θ') ts.toSubst us.toSubst)
            hΘx).mpr hτ⟩,
          (Term.subst_append _ _ _).symm.trans
            ((congrArg (fun t => Term.subst ts.toSubst t)
              (Term.subst_subst_of (Subst.liftN_subst_of _ hcx) _)).trans (Term.subst_append _ _ _)),
          hox, hoy⟩
      have hnonrec : ∀ (d : Name) (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership Grade ps₁.length) (hpos : (T'.body I).Pos d p q ς Ξ Θ B ψ)
          (ts us : Args 0 [] ps₁),
          EqSubst sig ι (Context.empty.append ((Θ.substLevels Lρ).subst
            (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst))) ts.toSubst us.toSubst →
          (T'.body I).recursionAt decl.names hpos.index = none →
          ValidEqTerm₀ sig ι (((x.observation T'.name qs ls ps a) d ps₁).subst ts.toSubst)
            (((y.observation T'.name qs ls ps a) d ps₁).subst us.toSubst)
            ((B.substLevels Lρ).subst (Subst.append
              (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst)) := by
        intro d p q ς ps₁ Ξ Θ B ψ hpos ts us hτ hr
        rw [Term.observation_subst_args, Term.observation_subst_args]
        have hτL := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
          (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
            (Telescope.substLevels_levelEquiv hls Θ))) hτ
        obtain ⟨i, hi, hσB, hBx, hox, hoy⟩ := hpre d p q ς ps₁ Ξ Θ B ψ hpos ts us hτL
        have hB0 : B.blockName decl.names = none := (hpos.recursionAt_index decl.names).symm.trans hr
        obtain ⟨g, hg⟩ := hgs i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
        have hgv := (hgt i j T' d p q ς ps₁ Ξ Θ B ψ A' g hi hA' hpos hB0 hg).2 _ _ hσB
        have hBv := (hBt i j T' d p q ς ps₁ Ξ Θ B ψ A' hi hA' hpos hB0).2 _ _ hσB
        -- The branch at the substitution is a proof that the observations of the two terms at the
        -- first arguments are equal.
        have ho₁ := (hobs3 T'.name (Subst.snoc (e := .var) (Subst.snoc (e := .var)
          (Subst.snoc (e := .var) σ x) y) z) (.succ (.succ .zero)) d ts).trans
          (congrArg (fun as' => Term.obs T'.name qs ls ps as' x d ts.terms) has3)
        have ho₂ := (hobs3 T'.name (Subst.snoc (e := .var) (Subst.snoc (e := .var)
          (Subst.snoc (e := .var) σ x) y) z) (.succ .zero) d ts).trans
          (congrArg (fun as' => Term.obs T'.name qs ls ps as' y d ts.terms) has3)
        have hgv' := (congrArg (ValidEqTerm₀ sig ι _ _)
          (congr (congr (congrArg (Term.equality (κs i).quality (κs i).level) hBx) ho₁) ho₂)).mp hgv
        have hBxv := (congrArg (fun A₀ => ValidEqTerm₀ sig ι A₀ A₀ (.sort (κs i))) hBx).mp hBv.left
        have hE := ValidEqTerm₀.equality hBxv hox.left hoy.left (Level.equivalence.refl _)
        have hxy : ValidEqTerm₀ sig ι (.obs T'.name qs ls ps a x d ts.terms)
            (.obs T'.name qs ls ps a y d ts.terms) _ := ⟨hox.1, ValidEqTerm₀.equality_eq hE hgv'⟩
        exact (hxy.trans hoy).levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _)
          (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
            (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
      -- The observations of the two terms by each destructor are related: by the equality of its
      -- result if it is not recursive, and otherwise, computed, by the relations, since the branch
      -- makes the relation of the type of the result true at them.
      have hS₁ : S Y T' (x.observation T'.name qs ls ps a) (y.observation T'.name qs ls ps a) :=
        DesRel.of_obsRel hd Lρ (T'.body I) (hmean T' hT') (fun i hi => by rw [hi]; rfl)
          (fun i D' hi => by rw [hi]; exact ⟨_, rfl⟩) (hlev (hS Y T' hT')) hnonrec
          (fun d p q ς ps₁ Ξ Θ B ψ hpos ts us hτ D' R hD' hR e => by
            rw [hD'] at hR
            cases hR
            rw [Term.observation_subst_args, Term.observation_subst_args]
            have hτL := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
              (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
                (Telescope.substLevels_levelEquiv hls Θ))) hτ
            obtain ⟨i, hi, hσB, -, hox, hoy⟩ := hpre d p q ς ps₁ Ξ Θ B ψ hpos ts us hτL
            have hBD : B.blockName decl.names = some D' :=
              (hpos.recursionAt_index decl.names).symm.trans hD'
            obtain ⟨T'', hT'', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT'
              (Destructors.recursionAt_mem hD')
            obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hT''
            have hidx := TypeDeclaration.idxOf?_codataTypes hnames hj'
            obtain ⟨A'', hA''⟩ := Terms.get_of_lt_length
              (hAl ▸ (List.getElem?_eq_some_iff.1 hj').1)
            obtain ⟨g, hg⟩ := hgs i j T' d p q ς ps₁ Ξ Θ B ψ hi hpos
            -- The result of the destructor is the instance of the type of the block it names.
            have hty : Term.LevelEquiv ((B.substLevels L).subst (Subst.append
                (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst))
                (.inst T''.name qs ls ps a) := by
              have hE := Term.LevelEquiv.subst (Subst.LevelEquiv.refl (Subst.append
                  (hpos.obsSubst (x.observation T'.name qs ls ps a) a.toSubst) ts.toSubst))
                (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B)
              rw [e] at hE
              exact hE.trans (hX _)
            have hxD := hox.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) hty
            have hyD := hoy.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) hty
            have hx'v := hxD.left
            have hy'v := hyD.symm.left
            obtain ⟨v', hv'⟩ := hcomp T'' hT'' hx'v
            obtain ⟨w', hw'⟩ := hcomp T'' hT'' hy'v
            -- The branch is a proof of the relation of the type of the result at the
            -- observations at the first arguments.
            have hgv := (hgr i j T' d p q ς ps₁ Ξ Θ B ψ A' T''.name j' A'' g hi hA' hpos hBD hidx
              hA'' hg).2 _ _ hσB
            have ho₁ := (hobs3 T'.name (Subst.snoc (e := .var) (Subst.snoc (e := .var)
              (Subst.snoc (e := .var) σ x) y) z) (.succ (.succ .zero)) d ts).trans
              (congrArg (fun as' => Term.obs T'.name qs ls ps as' x d ts.terms) has3)
            have ho₂ := (hobs3 T'.name (Subst.snoc (e := .var) (Subst.snoc (e := .var)
              (Subst.snoc (e := .var) σ x) y) z) (.succ .zero) d ts).trans
              (congrArg (fun as' => Term.obs T'.name qs ls ps as' y d ts.terms) has3)
            have hR2 := (Term.subst_rename_of (Subst.liftN_rename_of 2
                (fun u => Subst.append_weakenN (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                  (Subst.snoc (e := .var) σ x) y) z) ts.toSubst u))
                ((A''.rename (Ren.liftN 2 (Ren.weakenN 3))))).trans
              (Term.subst_rename_of (α := Ren.liftN 2 (Ren.weakenN 3)) (θ' := Subst.liftN 2 σ)
                (Subst.liftN_rename_of 2 (fun _ => rfl)) A'')
            have hgv' : ValidEqTerm₀ sig ι
                (g.subst (Subst.append (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                  (Subst.snoc (e := .var) σ x) y) z) ts.toSubst))
                (g.subst (Subst.append (Subst.snoc (e := .var) (Subst.snoc (e := .var)
                  (Subst.snoc (e := .var) σ x) y) z) us.toSubst))
                (A''.subst (Subst.snoc (e := .var)
                (Subst.snoc (e := .var) σ (.obs T'.name qs ls ps a x d ts.terms))
                (.obs T'.name qs ls ps a y d ts.terms))) := by
              refine (congrArg (ValidEqTerm₀ sig ι _ _) ?_).mp hgv
              refine (Term.instantiate_subst (ps := [p₀, p₀]) _
                ((A''.rename (Ren.liftN 2 (Ren.weakenN 3))).rename (Ren.liftN 2 (Ren.weakenN ps₁.length)))
                (Args.cons ((Term.var₀ (.succ (.succ .zero)) : Term 0 (Γ.extend 3)).observation T'.name
                  qs ls ps (as.rename (Ren.weakenN 3)) d ps₁)
                  (Args.cons ((Term.var₀ (.succ .zero) : Term 0 (Γ.extend 3)).observation T'.name qs ls
                    ps (as.rename (Ren.weakenN 3)) d ps₁) .nil))).trans ?_
              exact (congr (congrArg (Term.instantiate (ps := [p₀, p₀])) hR2)
                (congr (congrArg Args.cons ho₁) (congr (congrArg Args.cons ho₂) rfl))).trans
                (hinst A'' _ _)
            -- The relation relates the second observation at the second arguments too.
            have hAtv := (hAt j' T'' A'' hj' hA'').2 _ _ (hσ2 T'' _ _ _ hx'v hyD)
            have hz := hgv'.left.conv (ValidEqTerm₀.propType hAtv)
            exact ⟨v', w', hv', hw', .inr ⟨j', T'', A'', _, _, _, hj', rfl, hA'', hx'v, hy'v, hz,
              hv', hw'⟩⟩)
      obtain ⟨o₁, hc₁⟩ := hcan T' hT' hx hxv
      obtain ⟨o₂, hc₂⟩ := hcan T' hT' hy hyw
      exact ⟨o₁, o₂, hc₁, hc₂, DesRel.obsEquiv hd (hRF T') (hlev (hS Y T' hT')) hS₁
        (ObsEquiv.of_computes hd hxv hc₁) (ObsEquiv.of_computes hd hyw hc₂)⟩
    -- The two terms compute to canonical terms that the relation of their type relates.
    have hT1 := ht₁.2 σ σ hσ
    have hT2 := ht₂.2 σ σ hσ
    obtain ⟨v, hv₁⟩ := hcomp T hT hT1
    obtain ⟨w, hw₂⟩ := hcomp T hT hT2
    have htv := (congrArg (ValidEqTerm₀ sig ι _ _)
      ((Term.instantiate_subst (ps := [p₀, p₀]) σ A (Args.cons t₁ (Args.cons t₂ .nil))).trans
        (hinst A _ _))).mp (ht.2 σ σ hσ)
    have hrel : CodataType.blockRel decl.codataTypes S T.name v w :=
      CodataType.blockRel_coind hmono hcons
        ⟨h', T, A, _, _, _, hh, rfl, hA, hT1, hT2, htv.left, hv₁, hw₂⟩
    exact ⟨fun _ => ⟨_, v, w, _, hcI _, hv₁, hw₂, .univ _ (levelRel_univ_iff.2 (hU T hT).1), hrel⟩,
      fun hp => absurd hp (hnp T hT)⟩
  · -- On a proposition, any two proofs are equal.
    have e : (decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl) =
        ⟨.prop, ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)).level⟩ := by
      rw [Universe.substLevels, hs]
    rw [e] at hI
    exact ((ValidEqTermΓ.irr ht₁ ht₂ hI).2 σ σ hσ).2

end

end Sic.Core
