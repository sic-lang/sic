module

public import Sic.Core.Soundness.Nesting.Equality
public import Sic.Core.Soundness.Nesting.RunTime
import Sic.Core.Substitution.Nesting
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Inversion
import Sic.Core.Typing.Lifting.Context
import Sic.Core.Typing.Presuppositions

/-!
# Nested Fields of a Block

A nested field of a block, as annex 14 of RFC 36 forms it, has the type `A₀[D̄ x̄_Δ / X̄]`, where `A₀`
is typed in the signature before the block, with a type variable of `X̄` for each type of the
block, in which it is strictly positive.
Its meaning in annex 18 has three parts, proved here from the readings of the nested types, at two
equal closed substitutions of the context: the graph of the nestings of the equality reads the two
types with one equality, that of run time with one relation, and the two types are equal when the
instances of the types of the block are.

The types of the block have no meaning yet: the readings are taken at the substitutions that give
the type variables the unit of the prelude, a type of every universe, at which `A₀` has its
meaning, and at those that give them the instances of the types of the block, whose positions hold
the relations given for these types.
The nesting of the field, read on the declaration with the names of the block, is that of `A₀` at
the nestings of the type variables, since no type of the block occurs in `A₀`, typed before the
block.

The soundness of the typing is proved from these properties, which take it as a hypothesis, as the
readings do.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Type Variables of a Block -/

section

variable {k : Nat}

/-- The arguments that `f` gives for names are, for each variable of their telescope, the term
that `f` gives for one of the names. -/
theorem Args.ofNames_toSubst₀ {Γ : Scope} (f : Name → Term k Γ) :
    (names : List Name) →
      (z : Var (Scope.extend [] (List.replicate names.length (⟨.zero, .zero⟩ : Parameter)).length)
        .var) →
      ∃ D, D ∈ names ∧ (Args.ofNames f names).toSubst₀ (Ren.liftN _ Ren.empty z) = .term (f D)
  | [], z => nomatch z
  | D :: names, z => by
    rcases Var.cases_extend (Γ := [.var])
      (List.replicate names.length (⟨.zero, .zero⟩ : Parameter)).length z with ⟨y, rfl⟩ | ⟨z', rfl⟩
    · cases y with
      | zero =>
        refine ⟨D, List.mem_cons_self, ?_⟩
        show (Subst₀.liftN _ (Subst₀.single (f D))
          (Ren.liftN _ (Ren.lift Ren.empty) (Var.weakenN _ .zero))).subst₀
            (Args.ofNames f names).toSubst₀ = _
        rw [Ren.liftN_weakenN, Subst₀.liftN_weakenN]
        show Val.term (((f D).rename (Ren.weakenN _)).subst₀ (Args.ofNames f names).toSubst₀) = _
        rw [Term.subst₀_rename_of (α := Ren.weakenN _) (σ' := Subst₀.id)
          (Args.toSubst₀_weakenN (Args.ofNames f names)), Term.subst₀_id]
      | succ y => exact nomatch y
    · obtain ⟨D', hD', h⟩ := Args.ofNames_toSubst₀ f names z'
      refine ⟨D', List.mem_cons_of_mem _ hD', ?_⟩
      show (Subst₀.liftN _ (Subst₀.single (f D))
        (Ren.liftN _ (Ren.lift Ren.empty) (Ren.liftN _ Ren.empty z'))).subst₀
          (Args.ofNames f names).toSubst₀ = _
      rw [Ren.liftN_comp_of _ (α₃ := Ren.empty) (fun y => nomatch y) z',
        Subst₀.liftN_rename_of _ (α := Ren.empty) (σ' := fun x => nomatch x) (fun x => nomatch x),
        Subst₀.liftN_empty]
      exact h

/-- The telescope of the type variables of a sort, where levels replace the level variables, is
that of the sort where they do. -/
theorem Telescope.sorts_substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k')
    (κ : Universe k) : (n : Nat) →
      (Telescope.sorts (Γ := Γ) κ n).substLevels ls' = Telescope.sorts (κ.substLevels ls') n
  | 0 => rfl
  | n + 1 => by
    rw [Telescope.sorts, Telescope.substLevels, Telescope.sorts_substLevels ls' κ n]
    rfl

/-- A substitution does not change the telescope of the type variables of a sort. -/
theorem Telescope.sorts_subst {Ξ Γ : Scope} (σ : Subst k Ξ Γ) (κ : Universe k) : (n : Nat) →
    (Telescope.sorts (Γ := Γ) κ n).subst σ = Telescope.sorts κ n
  | 0 => rfl
  | n + 1 => by
    rw [Telescope.sorts, Telescope.subst, Telescope.sorts_subst (Subst.lift σ) κ n]
    rfl

/-- A substitution of the first order does not change the telescope of the type variables of a
sort. -/
theorem Telescope.sorts_subst₀ {Ξ Γ : Scope} (σ : Subst₀ k Ξ Γ) (κ : Universe k) : (n : Nat) →
    (Telescope.sorts (Γ := Γ) κ n).subst₀ σ = Telescope.sorts κ n
  | 0 => rfl
  | n + 1 => by
    rw [Telescope.sorts, Telescope.subst₀, Telescope.sorts_subst₀ (Subst₀.lift σ) κ n]
    rfl

/-- The arguments that `f` gives for names, where levels replace the level variables. -/
theorem Args.ofNames_substLevels {k' : Nat} {Γ : Scope} (ls' : Fin k → Level k')
    (f : Name → Term k Γ) : (names : List Name) →
      (Args.ofNames f names).substLevels ls' = Args.ofNames (fun D => (f D).substLevels ls') names
  | [] => rfl
  | D :: names => by
    rw [Args.ofNames, Args.substLevels, Args.ofNames_substLevels ls' f names]
    rfl

/-- The arguments that `f` gives for names, substituted. -/
theorem Args.ofNames_subst {Ξ Γ : Scope} (σ : Subst k Ξ Γ) (f : Name → Term k Γ) :
    (names : List Name) →
      (Args.ofNames f names).subst σ = Args.ofNames (fun D => (f D).subst σ) names
  | [] => rfl
  | D :: names => by
    rw [Args.ofNames, Args.subst, Args.ofNames_subst σ f names]
    rfl

/-- `B[t̄ / Θ][ρ][σ] = B[ρ][σ, t̄[ρ][σ]]`. -/
theorem Term.instantiate_atLevels_subst {Γ : Scope} {ps : List Parameter} (ρ : Fin k → Nat)
    (σ : Subst 0 [] Γ) (B : Term k (Γ.extend ps.length)) (ts : Args k Γ ps) :
    ((B.instantiate ts).atLevels ρ).subst σ =
      (B.atLevels ρ).subst (Subst.append σ ((ts.atLevels ρ).subst σ).toSubst) := by
  rw [Term.atLevels, Term.substLevels_instantiate, Term.instantiate_subst,
    Term.instantiate_eq_subst, Term.subst_append]
  rfl

mutual

/-- A type typed in a signature has the same nesting whatever the names that the signature does not
declare hold, since none of them occurs in it. -/
theorem Term.nest_of_fresh {α : Type} {sigT : Signature} (mark : Name → Option α)
    (hmark : ∀ e ∈ sigT, ∀ D ∈ e.names, mark D = none) :
    {Γ : Scope} → {ctx : Context k Γ} → {T : Term k Γ} → {ν : Nesting α Γ} → (A : Term k Γ) →
      HasType sigT ctx A T → A.nest mark @ν = A.nest (fun _ => none) @ν
  | _, _, _, _, .var _ _, _ => rfl
  | _, ctx, _, _, .inst D qs ls ps as, hA => by
    have h : mark D = none ∧ ∃ params, HasInstanceArgs sigT ctx as params := by
      obtain ⟨decl, ζ, hΔ, hq, hl, hp, hD, -, has⟩ := hA.inst_inv
      subst hΔ
      have hm : D ∈ decl.names := by
        rcases hD.2 with ⟨T, hT, rfl, -⟩ | ⟨T, hT, rfl, -⟩
        · exact TypeDeclaration.name_mem_names hT
        · exact TypeDeclaration.codata_name_mem_names hT
      exact ⟨hmark _ hD.1 D hm, _, has⟩
    obtain ⟨hD, params, has⟩ := h
    rw [Term.nest, Term.nest, hD]
    exact congrArg Nest.ofArgs (InstanceArgs.nest_of_fresh mark hmark as has)
  | _, _, _, _, .sort _, _ => rfl
  | _, _, _, _, .const _ _ _ _, _ => rfl
  | _, _, _, _, .ctor _ _ _ _ _ _ _, _ => rfl
  | _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, _, _, .obs _ _ _ _ _ _ _ _, _ => rfl
  | _, _, _, _, .corec _ _ _ _ _ _ _ _ _, _ => rfl

/-- The arguments of an instance typed in a signature have the same nestings whatever the names
that the signature does not declare hold. -/
theorem InstanceArgs.nest_of_fresh {α : Type} {sigT : Signature} (mark : Name → Option α)
    (hmark : ∀ e ∈ sigT, ∀ D ∈ e.names, mark D = none) :
    {Γ Δ : Scope} → {ctx : Context k Γ} → {ν : Nesting α Γ} → (as : InstanceArgs k Γ Δ) →
      {params : Context k Δ} → HasInstanceArgs sigT ctx as params →
      as.nest mark @ν = as.nest (fun _ => none) @ν
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .snoc (e := .var) as a, _, .var has ha => by
    rw [InstanceArgs.nest, InstanceArgs.nest, Term.nest_of_fresh mark hmark a ha,
      InstanceArgs.nest_of_fresh mark hmark as has]
  | _, _, _, _, .snoc (e := .secondOrder _ _) as B, _, .secondOrder has hB => by
    rw [InstanceArgs.nest, InstanceArgs.nest, Term.nest_of_fresh mark hmark B hB,
      InstanceArgs.nest_of_fresh mark hmark as has]

end

end

/-! ## Nested Fields -/

section

variable {sig : Signature} {ι : Interpretation}

/-- The arguments that two functions give for names are equal arguments of the telescope of the
type variables of a sort, when the functions give each name equal types of the sort. -/
theorem EqSubst.ofNames {κ : Universe 0} (f₁ f₂ : Name → Term 0 []) : (names : List Name) →
    (∀ D ∈ names, ValidEqTerm₀ sig ι (f₁ D) (f₂ D) (.sort κ)) →
      EqSubst sig ι (Context.empty.append (Telescope.sorts κ names.length))
        (Args.ofNames f₁ names).toSubst (Args.ofNames f₂ names).toSubst
  | [], _ => (EqSubst.empty_iff _ _).2 trivial
  | D :: names, h => by
    show EqSubst sig ι
      (Context.empty.append (.cons .zero ⟨.zero, .zero⟩ (.sort κ) (Telescope.sorts κ names.length)))
      (Args.cons (f₁ D) (Args.ofNames f₁ names)).toSubst
      (Args.cons (f₂ D) (Args.ofNames f₂ names)).toSubst
    rw [EqSubst.args_cons_iff, Telescope.sorts_subst₀]
    exact ⟨h D List.mem_cons_self,
      EqSubst.ofNames f₁ f₂ names fun D' hD' => h D' (List.mem_cons_of_mem _ hD')⟩

-- ADE: none.
/-- The type `A₀[D̄ ā / X̄]` of a nested field of a block, where `A₀` is typed in the signature
before the block, in the context extended by a type variable of the sort `κ` for each type of the
block, and strictly positive in these variables, is read by a reading `rd` of the nested types at
its nesting, at two equal closed substitutions of the context, where each position holds what
`f₁` and `f₂` give the type of the block it holds: `rd` reads the instances of the types of the
block as given, and reads without position the types of a sort that `κ` bounds, of which `U₁` and
`U₂` are two for the type variables. -/
theorem Term.readsBlockNest {α J : Type} {rd : J → Nest α → Nest α → Term 0 [] → Term 0 [] → Prop}
    {sigT : Signature} (hS : TypingSound sig ι) (hent : sig.ValidEntries ι sigT)
    (hread : ReadsNested sig ι rd sigT) {decl : TypeDeclaration}
    (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) (I : Instance decl.sorts decl.grades)
    {Γ : Scope} (as : InstanceArgs decl.levels Γ decl.scope) {ctx : Context decl.levels Γ}
    {κ κ₁ : Universe decl.levels}
    {A₀ : Term decl.levels
      (Γ.extend (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length)}
    (hA₀ : HasType sigT (ctx.append (Telescope.sorts κ decl.names.length)) A₀ (.sort κ₁))
    (hpos : ∀ z : Var (Scope.extend []
        (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) .var,
      Term.Positive (sigT.PositiveIn decl) (Ren.liftN _ Ren.empty z) A₀)
    (ρ : Fin decl.levels → Nat) {σ₁ σ₂ : Subst 0 [] Γ}
    (hσ : EqSubst sig ι (ctx.atLevels ρ) σ₁ σ₂) (f₁ f₂ : Name → α) (j : J)
    {U₁ U₂ : Term 0 []} (hU : ValidEqTerm₀ sig ι U₁ U₂ (.sort (κ.atLevels ρ)))
    (hpl : ∀ A₁ A₂, ValidEqTerm₀ sig ι A₁ A₂ (.sort (κ₁.atLevels ρ)) → rd j .plain .plain A₁ A₂)
    (hdir : ∀ D ∈ decl.names, ∀ s, rd s (.direct (f₁ D)) (.direct (f₂ D))
      (((decl.blockInstance I D as).atLevels ρ).subst σ₁)
      (((decl.blockInstance I D as).atLevels ρ).subst σ₂)) :
    rd j (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map f₁)
      (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map f₂)
      (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₁)
      (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₂) := by
  let mark : Name → Option Name := fun D => if D ∈ decl.names then some D else none
  let νX : Nesting Name
      (Γ.extend (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) :=
    fun x => ((decl.blockArgs I as).toSubst₀ x).nest mark Nesting.plain
  let τ : Subst 0 [] Γ → Subst 0 [] (Scope.extend []
      (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) :=
    fun σ => (((decl.blockArgs I as).atLevels ρ).subst σ).toSubst
  let τE : Term 0 [] → Subst 0 [] (Scope.extend []
      (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) :=
    fun U => (Args.ofNames (fun _ => U) decl.names).toSubst
  -- The variables of the context have no position.
  have hold : ∀ (e : Scope.Entry) (y : Var Γ e), νX (y.weakenN _) = .plain := fun e y => by
    show ((decl.blockArgs I as).toSubst₀ (y.weakenN _)).nest mark Nesting.plain = _
    rw [Args.toSubst₀_weakenN]
    rfl
  -- A type variable has the position that holds its type of the block, and is given its instance.
  have hnew : ∀ z : Var (Scope.extend []
        (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) .var,
      ∃ D, D ∈ decl.names ∧ νX (Ren.liftN _ Ren.empty z) = .direct D ∧
        ∀ σ : Subst 0 [] Γ, τ σ z = ((decl.blockInstance I D as).atLevels ρ).subst σ := fun z => by
    obtain ⟨D, hD, h⟩ := Args.ofNames_toSubst₀ (fun D => decl.blockInstance I D as) decl.names z
    refine ⟨D, hD, ?_, fun σ => ?_⟩
    · show ((decl.blockArgs I as).toSubst₀ (Ren.liftN _ Ren.empty z)).nest mark Nesting.plain = _
      rw [TypeDeclaration.blockArgs, h]
      show (decl.blockInstance I D as).nest mark Nesting.plain = _
      rw [TypeDeclaration.blockInstance, Term.nest]
      have hm : mark D = some D := by
        show (if D ∈ decl.names then some D else none) = some D
        simp only [hD, ite_true]
      rw [hm]
    · have e := Term.instantiate_atLevels_subst ρ σ (Term.var₀ (Ren.liftN _ Ren.empty z))
        (decl.blockArgs I as)
      rw [Term.instantiate_eq_subst₀, Term.subst₀_var, TypeDeclaration.blockArgs, h] at e
      exact (Subst.append_liftN_empty σ (τ σ) z).symm.trans e.symm
  have hmp : ∀ (g : Name → α) (n : Nest Name), (n.map g).isPlain = n.isPlain := fun g n => by
    cases n <;> rfl
  -- The substitutions that give the type variables `U₁` and `U₂` are equal.
  have hE : EqSubst sig ι ((ctx.append (Telescope.sorts κ decl.names.length)).atLevels ρ)
      (Subst.append σ₁ (τE U₁)) (Subst.append σ₂ (τE U₂)) := by
    rw [Context.atLevels, Context.substLevels_append, Telescope.sorts_substLevels]
    refine (EqSubst.append_append_iff _ _ _ _ _ _).2 ⟨hσ, ?_⟩
    rw [Telescope.sorts_subst]
    exact EqSubst.ofNames _ _ _ fun _ _ => hU
  have hplain := hpl _ _ ((hS.hasType hent hA₀ ρ).2 _ _ hE)
  -- The two pairs of substitutions, at the nestings of the type variables.
  have hNS : NestSubst sig ι rd ((ctx.append (Telescope.sorts κ decl.names.length)).atLevels ρ)
      (fun x => x) (fun x => (νX x).map f₁) (fun x => (νX x).map f₂)
      (Subst.append σ₁ (τE U₁)) (Subst.append σ₂ (τE U₂))
      (Subst.append σ₁ (τ σ₁)) (Subst.append σ₂ (τ σ₂)) :=
    { isPlain := fun x => (hmp f₁ _).trans (hmp f₂ _).symm
      left := fun x hx => by
        rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · rw [Subst.append_weakenN, Subst.append_weakenN]
        · obtain rfl := Var.extend_var (Γ := []) (fun y => nomatch y) _ z
          obtain ⟨D, -, hD, -⟩ := hnew z
          rw [hmp, hD] at hx
          exact nomatch hx
      right := fun x hx => by
        rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · rw [Subst.append_weakenN, Subst.append_weakenN]
        · obtain rfl := Var.extend_var (Γ := []) (fun y => nomatch y) _ z
          obtain ⟨D, -, hD, -⟩ := hnew z
          rw [hmp, hD] at hx
          exact nomatch hx
      var := fun x hx s _ => by
        rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · rw [hmp, hold] at hx
          exact nomatch hx
        · obtain ⟨D, hDm, hD, hτ⟩ := hnew z
          rw [Subst.append_liftN_empty, Subst.append_liftN_empty, hτ, hτ]
          show rd s ((νX (Ren.liftN _ Ren.empty z)).map f₁) ((νX (Ren.liftN _ Ren.empty z)).map f₂)
            _ _
          rw [hD]
          exact hdir D hDm s
      secondOrder := fun X _ _ _ hp => by
        rcases Var.cases_extend _ X with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · rw [hmp, hold] at hp
          exact nomatch hp
        · exact nomatch Var.extend_var (Γ := []) (fun y => nomatch y) _ z }
  have hr := hread hA₀ decl fresh ρ (fun x => x)
    (fun e x hx => by
      rw [Term.rename_id]
      rcases Var.cases_extend _ x with ⟨y, rfl⟩ | ⟨z, rfl⟩
      · rw [hmp, hold] at hx
        exact nomatch hx
      · obtain rfl := Var.extend_var (Γ := []) (fun y => nomatch y) _ z
        exact hpos z)
    hE hNS j (by rw [Term.rename_id]; exact hplain)
  rw [Term.rename_id] at hr
  -- The nesting of the field is that of `A₀`, at the nestings of the type variables.
  have hmark : ∀ (g : Name → α), ∀ e ∈ sigT, ∀ D ∈ e.names, (mark D).map g = none :=
    fun g e he D hD => by
      have hn : D ∉ decl.names := fun h => fresh e he D h hD
      show (if D ∈ decl.names then some D else none).map g = none
      simp only [hn, ite_false, Option.map_none]
  have hnest : ∀ (g : Name → α),
      ((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map g =
        A₀.nest (fun _ => none) (fun x => (νX x).map g) := fun g => by
    rw [Term.blockNest, Term.nest_instantiate, Term.nest_map g mark (fun _ _ => rfl) A₀]
    exact Term.nest_of_fresh _ (hmark g) A₀ hA₀
  rw [hnest, hnest, Term.instantiate_atLevels_subst, Term.instantiate_atLevels_subst]
  exact hr

-- ADE: none.
/-- The meaning of a nested field of a block, whose type is `A₀[D̄ ā / X̄]`, where `A₀` is typed in
the signature before the block, which holds the prelude, in the context extended by a type variable
of the universe `κ` for each type of the block, in a sort that `κ` bounds, and strictly positive in
these variables, at two equal closed substitutions of the context, given the soundness of the
typing: the graph of the nestings of the equality reads the two types with one equality, whatever
the relations given at the positions of the types of the block, that of run time reads them with
one relation, for each program and whatever the relations given at these positions, and they are
equal types of the sort of `A₀` when the instances of the types of the block are equal types of
`κ`. -/
theorem Term.validBlockNest {sigT : Signature} (hS : TypingSound sig ι) (hd : sig.Distinct)
    (hent : sig.ValidEntries ι sigT) (hpre : sigT.HasPrelude) {decl : TypeDeclaration}
    (fresh : ∀ e ∈ sigT, ∀ D ∈ decl.names, D ∉ e.names) (I : Instance decl.sorts decl.grades)
    {Γ : Scope} (as : InstanceArgs decl.levels Γ decl.scope) {ctx : Context decl.levels Γ}
    {κ κ₁ : Universe decl.levels}
    {A₀ : Term decl.levels
      (Γ.extend (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length)}
    (hA₀ : HasType sigT (ctx.append (Telescope.sorts κ decl.names.length)) A₀ (.sort κ₁))
    (hκ : κ₁ ≼ κ) (hq : κ.quality = .type)
    (hpos : ∀ z : Var (Scope.extend []
        (List.replicate decl.names.length (⟨.zero, .zero⟩ : Parameter)).length) .var,
      Term.Positive (sigT.PositiveIn decl) (Ren.liftN _ Ren.empty z) A₀)
    (ρ : Fin decl.levels → Nat) {σ₁ σ₂ : Subst 0 [] Γ}
    (hσ : EqSubst sig ι (ctx.atLevels ρ) σ₁ σ₂) :
    (∀ R : Name → TermRel, ∃ F,
      NestRel sig ι (κ.atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        (κ.atLevels ρ).quality
        (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map fun D =>
          (((decl.blockInstance I D as).atLevels ρ).subst σ₁, R D))
        (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₁) F ∧
      NestRel sig ι (κ.atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        (κ.atLevels ρ).quality
        (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map fun D =>
          (((decl.blockInstance I D as).atLevels ρ).subst σ₂, R D))
        (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₂) F) ∧
    (∀ (P : Program) (Q : Name → RunRel), ∃ R,
      RunNestRel sig ι P (κ.atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map fun D =>
          (((decl.blockInstance I D as).atLevels ρ).subst σ₁, Q D))
        (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₁) R ∧
      RunNestRel sig ι P (κ.atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        (((A₀.instantiate (decl.blockArgs I as)).blockNest decl.names).map fun D =>
          (((decl.blockInstance I D as).atLevels ρ).subst σ₂, Q D))
        (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₂) R) ∧
    ((∀ D ∈ decl.names, ValidEqTerm₀ sig ι (((decl.blockInstance I D as).atLevels ρ).subst σ₁)
        (((decl.blockInstance I D as).atLevels ρ).subst σ₂) (.sort (κ.atLevels ρ))) →
      ∃ κ₁' : Universe 0, κ₁' ≼ κ.atLevels ρ ∧
        ValidEqTerm₀ sig ι (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₁)
          (((A₀.instantiate (decl.blockArgs I as)).atLevels ρ).subst σ₂) (.sort κ₁')) := by
  obtain ⟨q, l⟩ := κ
  obtain rfl : q = .type := hq
  have hκρ : κ₁.atLevels ρ ≼ Universe.atLevels ρ ⟨.type, l⟩ := Universe.substLevels_bounded _ hκ
  -- The unit of the prelude is a type of `κ`, for the type variables.
  have hctx : WfCtx sigT ctx := WfCtx.of_append (contextPresuppositions.hasType hA₀)
  have hUnit : HasType sigT ctx (.inst "Unit" [] [l] [] .nil) (.sort ⟨.type, l⟩) :=
    .inst (D := "Unit") (decl := Prelude.unit) (ζ := Prelude.unitType.usage)
      ⟨hpre _ (by simp [Signature.prelude]), .inl ⟨_, List.mem_singleton_self _, rfl, rfl⟩⟩
      rfl rfl rfl trivial (by exact .nil hctx)
  have hU : ValidEqTerm₀ sig ι (((Term.inst "Unit" [] [l] [] .nil).atLevels ρ).subst σ₁)
      (((Term.inst "Unit" [] [l] [] .nil).atLevels ρ).subst σ₂)
      (.sort (Universe.atLevels ρ ⟨.type, l⟩)) := (hS.hasType hent hUnit ρ).2 σ₁ σ₂ hσ
  refine ⟨fun R => ?_, fun P Q => ?_, fun hinst => ?_⟩
  · exact Term.readsBlockNest hS hent (NestReads.readsNested hS hd _ hent) fresh I as hA₀ hpos ρ hσ
      _ _ (Universe.atLevels ρ ⟨.type, l⟩).quality hU
      (fun _ _ h => (nestReading sig ι hd _).plain ⟨Nat.le_refl _, rfl⟩ hκρ h)
      (fun D _ _ => ⟨R D, .direct (.refl _), .direct (.refl _)⟩)
  · exact Term.readsBlockNest hS hent (RunNestReads.readsNested hS hd P _ hent) fresh I as hA₀ hpos
      ρ hσ _ _ () hU
      (fun _ _ h => (runNestReading sig ι hd P _).plain (i := ()) (Nat.le_refl _) hκρ h)
      (fun D _ _ => ⟨Q D, .direct (.refl _), .direct (.refl _)⟩)
  · have hE : EqSubst sig ι
        ((ctx.append (Telescope.sorts ⟨.type, l⟩ decl.names.length)).atLevels ρ)
        (Subst.append σ₁ (((decl.blockArgs I as).atLevels ρ).subst σ₁).toSubst)
        (Subst.append σ₂ (((decl.blockArgs I as).atLevels ρ).subst σ₂).toSubst) := by
      rw [Context.atLevels, Context.substLevels_append, Telescope.sorts_substLevels]
      refine (EqSubst.append_append_iff _ _ _ _ _ _).2 ⟨hσ, ?_⟩
      rw [Telescope.sorts_subst, TypeDeclaration.blockArgs, Args.atLevels,
        Args.ofNames_substLevels, Args.ofNames_subst, Args.ofNames_subst]
      exact EqSubst.ofNames _ _ _ hinst
    have h := (hS.hasType hent hA₀ ρ).2 _ _ hE
    rw [← Term.instantiate_atLevels_subst, ← Term.instantiate_atLevels_subst] at h
    exact ⟨κ₁.atLevels ρ, hκρ, h⟩

end

end Sic.Core
