module

public import Sic.Core.RunTime.Relation.Recursors.Constructor
public import Sic.Core.RunTime.Relation.Recursors.Nested
public import Sic.Core.RunTime.Relation.Recursors.Skeleton
import Sic.Core.Erasure.Fields
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.RunTime.Relation.Data
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Relation.Skeleton
import Sic.Core.RunTime.Subsumption
import Sic.Core.Shape.Results.Factor
import Sic.Core.Shape.Results.Fields
import Sic.Core.Soundness.Closed
import Sic.Core.Syntax.Signature
import Sic.Math.Relation

/-!
# Run Time of the Recursors

The recursors at run time: the erasure of a recursor evaluates its term, or the term of the
skeleton of its instance when its grade is erased, then eliminates the value of the case of its
constructor by the branch of the case, with its fields and its recursive results, each the recursor
on its recursive field, the corecursor of the shape of the type of its nested field,
`RunsAs.nested`, or `↯` when its grade is erased.

When the grade of the recursor is used at run time, the term of the recursor is related to the
address of its value at its instance, by `(®_μ)`, the least relations closed under its clauses: the
relations of the canonical terms that `(®_μ)` relates and on whose addresses the recursor evaluates
to the address of a value related to the recursor at the motive are closed, since the recursor on a
constructor steps to its branch, at the terms of the fields and at the recursive results, which
these relations relate to the addresses of the fields and of the results.

When the grade of the recursor is erased, every type of the block has one constructor at most, and
every field of the branch is erased, so that the term of the skeleton of the instance stands for
the term: the term computes to a canonical term that `(eq_μ)` relates, and the relations of the
canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`, and on the terms of whose
skeletons the recursor evaluates to the address of a value related to the recursor at the motive,
are closed, since the term of the skeleton of a type unfolds into its constructor, applied to the
terms of the skeletons of the types of its recursive fields,
within a depth that their ancestors, fewer than the types of the block, never reach.

Both cases eliminate a constructor in the same way, once its fields are related to their addresses
and its recursive results evaluated, which `RunsAs.recursor_ctor` states.

ADE prove the validity of their recursors at run time in the modules of
`Graded/Erasure/LogicalRelation/Fundamental/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- The fields of arguments related at the recursive fields by `Q`, a recursive field of a type `D`
of which is marked by `rs`, have terms that `Q D` relates. -/
theorem Terms.RecRel.exists_of_mem {Q : Name → TermRel} {D : Name} : {ps : List Parameter} →
    (rs : List (Option Name)) → rs.length = ps.length → (ts us : Args 0 [] ps) →
    Terms.RecRel Q rs ts.terms us.terms → some D ∈ rs → ∃ t u, Q D t u
  | [], [], _, .nil, .nil, _, h => nomatch h
  | _ :: _, some _ :: rs, hl, .cons t ts, .cons u us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      exact ⟨t, u, hq.1⟩
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq.2 hm
  | _ :: _, none :: rs, hl, .cons _ ts, .cons _ us, hq, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
    · exact Terms.RecRel.exists_of_mem rs (Nat.succ.inj hl) ts us hq hm
  | [], _ :: _, hl, _, _, _, _ => nomatch hl
  | _ :: _, [], hl, _, _, _, _ => nomatch hl


/-! ## Recursors -/

/-- The grades of a branch of a recursor used at run time make the field of a recursive result
used at run time used too, when the factor of the result is: the usage covers the uses of the
recursions on the field by the grade of the field. -/
theorem _root_.Sic.Grading.Grade.used_of_result : ∀ r p g e π : Grade,
    r ∉ Mode.oneOne.erased → r * p ≤ g + (e * π) * r → e ∉ Mode.oneOne.erased →
      π.run ≠ .zero → p ∉ Mode.oneOne.erased := by
  decide

/-- The grade of the recursive result of the field at the position `l`, the `j`-th field whose
nesting has a position, and that grade times the factor of the result, read from the grades `es`
and the factors `πs` of the results. -/
theorem Telescope.resultGrades_of_index {ns : List (Nest Name)} {es πs : List Grade} {j l : Nat}
    (hj : (Telescope.nestPositions ns 0)[j]? = some l) {e π : Grade} (he : es[j]? = some e)
    (hπ : πs[j]? = some π) :
    Telescope.resultGrades ns es l = e ∧
      Telescope.resultGrades ns (List.zipWith (· * ·) es πs) l = e * π := by
  have hj' : (Telescope.nestPositions ns 0)[j]? = some (0 + l) := by rw [Nat.zero_add]; exact hj
  refine ⟨?_, ?_⟩
  · rw [Telescope.resultGrades_of_nestPositions ns es 0 j l hj', List.getD_eq_getElem?_getD, he]
    rfl
  · rw [Telescope.resultGrades_of_nestPositions ns _ 0 j l hj', List.getD_eq_getElem?_getD,
      List.getElem?_zipWith, he, hπ]
    rfl

/-- A field at a position of the fields of a constructor at which a type of the block is
recursive has its recursions among the positions of the recursive fields. -/
theorem Telescope.mem_positions_of_recursionAt {k' : Nat} {Γ : Scope} {ps : List Parameter}
    {names : List Name} {Θ : Telescope k' Γ ps} {l : Nat} {D : Name}
    (h : Θ.recursionAt names l = some D) :
    l ∈ (Θ.recursion names).zipIdx.filterMap (fun y => y.1.map fun _ => y.2) ∧ l < ps.length := by
  unfold Telescope.recursionAt at h
  cases hx : (Θ.recursion names)[l]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    cases h
    refine ⟨List.mem_filterMap.2 ⟨(some D, l), List.mem_zipIdx_iff_getElem?.2 hx, rfl⟩, ?_⟩
    rw [← Telescope.length_recursion names Θ]
    exact (List.getElem?_eq_some_iff.1 hx).1

section

variable {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {decl : TypeDeclaration} {D : Name}
  {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {as : InstanceArgs 0 Γ decl.scope} {r ς χ' : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
  {χ : GradeVector Γ.length} {δs : Nat → GradeVector Γ.length} {gs : Nat → Nat → Grade}
  {κ : Universe 0}
  {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
    Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
      (con.nestResultParams (.ofLists qs ps hq hp) decl.names)} {πs : Nat → List Grade}

/-- `r ∉ S`, by induction on `(®_μ)`: the erased recursor, its branches renamed by `g` in an
environment `E'` that binds each variable `g x` as `E` binds `x`, eliminates the address of a term
of the instance related to it to the address of a value to which the recursor on the term is related
at the motive at the term; the recursive result of a nested field is the corecursor of its shape,
`RunsAs.nested`, whose leaves are the recursor on the terms of the types of the block. -/
theorem RunsAs.recursor (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {h' : Nat} {C : Term 0 (.var :: Γ)} (hh : decl.dataTypes[h']? = some T)
    (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hRs : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ' Cs) (Rs con) (πs i))
    (hctx : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ValidCtx₀ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con)))
    (hsorts : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) → ∀ θ,
      EqSubst sig ι (ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) θ θ →
      Telescope.ValidSorts₀ sig ι ((Rs con).subst θ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t₁ t₂,
      ValidEqTerm₀ sig ι t₁ t₂ ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidEqTerm₀ sig ι
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₁ κ (Cs.subst σ) (us.subst σ))
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₂ κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs Rs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hprop : ∀ {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope},
      sig.HasCodataType D decl T → ∀ {qs : List Quality} {ps : List Grade}
        (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades),
        decl.constraint (.ofLists qs ps hq hp) →
        (decl.sort (.ofLists qs ps hq hp)).quality = .prop →
        ∀ {d : Name} {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope}
          {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
          {ψ : ResultOwnership Grade ps₁.length},
          (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ → p ∈ Mode.oneOne.erased)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∉ Mode.oneOne.erased) {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {m : Nat} (g : TargetRen m Γ.length) (E' : List Nat)
    (hgE : ∀ x : Fin Γ.length, E'[(g x : Nat)]? = E[(x : Nat)]?) {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []} {a : Nat}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ))
    (ht : RunsAs sig ι P H₁ t a ((Term.inst D qs ls ps as).subst σ)) :
    ∃ b H₂ tr, EvalRec P ϖ₀ H₁ E' r.run
        (sig.recursionRequirement D qs ps ⟨κ.quality, r, ς⟩ χ').run
        ((us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
          ((sig.caseFieldParams D qs ps).getD [])).rename g) a b H₂ tr ∧
      H₁.Extends H₂ ∧
      RunsAs sig ι P H₂ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The relations of run time of the block at the arguments substituted.
  obtain ⟨S, hS, hU⟩ := hv.runUnivRel hd hdecl hq hl hp hadm hasσ hs P
  have ihmono : ∀ m,
      m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Monotone ((levelRel sig ι m).run P) := fun m _ => levelRel_run_mono hd m
  have hmono : ∀ X Y : Name → RunRel, (∀ D H v a, X D H v a → Y D H v a) →
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ H ts as, S X c H ts as → S Y c H ts as :=
    fun X Y hXY T hT c hc H =>
      RunTelRel.mono hd ihmono (K := Eq) (fun e => e ▸ List.prefix_refl _) (fun _ => rfl)
        (hS X T hT c hc) _ _ (hS Y T hT c hc)
        (fun _ => Nest.map_rel₃
          (fun D' H _ e _ _ => e ▸ RunRel.computed_mono (hXY D' H)) _) H H rfl
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let ϱ := (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  have hρ : r.run ≠ .zero := fun h0 =>
    hr ((by decide : ∀ g : Grade, g.run = .zero → g ∈ Mode.oneOne.erased) r h0)
  -- The relations of the canonical terms that `(®_μ)` relates and on whose addresses the erased
  -- recursor evaluates, in each heap that extends `H`, with its branches renamed by any renaming in
  -- any environment that binds the renamed scope as `E` binds the scope, to the address of a value
  -- related to the recursor at the motive.
  let X : Name → RunRel := fun D' H₀ w a => DataType.runBlockRel sig (.ofLists qs ps hq hp) decl.dataTypes S D' H₀ w a ∧
    ∀ ϖ' H', H₀.Extends H' → H.Extends H' →
      ∀ {m' : Nat} (g' : TargetRen m' Γ.length) (E'' : List Nat),
      (∀ x : Fin Γ.length, E''[(g' x : Nat)]? = E[(x : Nat)]?) →
      ValidTerm₀ sig ι w (.inst D' qs ls ps (as.subst σ)) →
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        ∃ b H₂ tr, EvalRec P ϖ' H' E'' r.run ϱ (Ns.rename g') a b H₂ tr ∧ H'.Extends H₂ ∧
          RunsAs sig ι P H₂ (f D' w) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w))
  -- These relations are monotone in the heap: the relation of the block is.
  have hXmono : ∀ D', (X D').Monotone := by
    intro D' H₀ H₀' hH₀ w a hX
    have hD' : D' ∈ decl.names := hX.1 (fun D'' _ _ _ => D'' ∈ decl.names)
      (fun T' hT' _ _ _ _ => TypeDeclaration.name_mem_names hT')
    obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
    exact ⟨RunUnivRel.mono hd ihmono (hU T₃ hT₃).1 hH₀ hX.1,
      fun ϖ' H' hH' hHH' => hX.2 ϖ' H' (hH₀.trans hH') hHH'⟩
  -- The leaves of the nested results: the recursor on a term of a type of the block, on the address
  -- of a path that runs to it, in a heap that extends `H`.
  have hleaf : ∀ {m₁ : Nat} (g₁ : TargetRen m₁ Γ.length) (E₁ : List Nat),
      (∀ x : Fin Γ.length, E₁[(g₁ x : Nat)]? = E[(x : Nat)]?) → ∀ D',
      RunResultLeaf sig ι P
        (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
        (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ))
        (sig.blockShapes decl.names qs ps χ') r.run ϱ (Ns.rename g₁) E₁ H D'
        (.inst D' qs ls ps (as.subst σ), (X D').computed sig ι) := by
    intro m₁ g₁ E₁ hE₁ D' b ms hb hms t hvt m₂ g₂ E₂ hE₂ H₃ O hHH₃ hO ϖ H₄ hH₄
    obtain ⟨hD', C₀, hC₀, rfl⟩ := Lifting.ofMotives_block_inv hb
    simp only [Signature.blockShapes, hD', ↓reduceIte, Option.some.injEq] at hms
    subst hms
    obtain ⟨a, H₅, tr₁, hevO, hH₅, v, hcv, hXv⟩ := hO hρ (by decide : Grade.linearLinear.run ≠ .zero) id E₂ (fun _ => rfl)
      (ϖ * r.run) H₄ hH₄
    rw [Target.rename_id] at hevO
    obtain ⟨j₃, T₃, C₃, hj₃, rfl, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hD' hC₀
    have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hvt
    obtain ⟨b', H₆, tr₂, hev, hH₆, hrun⟩ := hXv.2 ϖ H₅ (List.prefix_refl _)
      (hHH₃.trans (hH₄.trans hH₅)) (g₂ ∘ g₁) E₂ (fun x => (hE₂ (g₁ x)).trans (hE₁ x))
      (hvv.trans hvv.symm) C₃ ((hidx j₃ T₃ hj₃).symm ▸ hC₃)
    refine ⟨b', H₆, tr₁ ++ tr₂, ?_, hH₅.trans hH₆, ?_⟩
    · show Eval P ϖ H₄ E₂ (.recursor r.run ϱ (if r.run = .zero then _ else O)
        ((Ns.rename g₁).rename g₂)) b' H₆ _
      rw [ite_eq_right_of_eq_false _ _ (eq_false hρ), TargetBranches.rename_rename]
      exact .recursor hevO hev
    · rw [Term.recursorAt_subst₀]
      exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃ hcv.1 hvt hrun
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ H₀ w a, T'.runCtorRel sig (.ofLists qs ps hq hp) T'.name (S X) H₀ w a →
      X T'.name H₀ w a := by
    intro T' hT' H₀ w a hc
    have hcb := DataType.runCtorRel_mono (List.prefix_refl H₀)
      (fun c hc' ts bs => hmono X _ (fun _ _ _ _ h => h.1) T' hT' c hc' H₀ ts bs) hc
    refine ⟨DataType.runBlockRel_fold hmono hT' hcb,
      fun ϖ' H' hH' hHH' _ g' E'' hg' hwv C' hC' => ?_⟩
    obtain ⟨con, hcon, i, fs, bs, hw, hi, ha, hSX⟩ := hc
    -- The case of the constructor.
    obtain ⟨j₀, hij⟩ := hd.cases_of_constructorCase ⟨hdecl, hT', rfl⟩ hcon hi
    obtain ⟨i', j, hi', hj⟩ := TypeDeclaration.exists_cases hT' hcon
    obtain rfl : i = i' := List.getElem?_inj_of_nodup_map (hd.cases_nodup hdecl) hij hi' rfl
    rw [hidx j T' hj] at hC'
    have hRt := hRs i j T' con hi'
    have hfac := Constructor.ResultTypes.factors_recursiveResults hd hord hRt
    obtain ⟨u₁, hu₁⟩ := hus i j T' con hi'
    have hlg := Branches.length_grades hu₁
    -- A field of a recursive result used at run time, whose factor is, is used at run time.
    have hused : ∀ l (p : Parameter) (j' : Nat) (w' : RecursiveResult),
        (con.params (.ofLists qs ps hq hp))[l]? = some p →
        (Telescope.nestPositions ((con.fields (.ofLists qs ps hq hp)).nest decl.names) 0)[j']? = some l →
        (con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ' (.ofLists qs ps hq hp))[j']? =
          some w' → w'.factor ≠ .zero →
        Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names) (us.grades i) l ∉
          Mode.oneOne.erased → p.usage ∉ Mode.oneOne.erased := by
      intro l p j' w' hl' hj' hw' hfw he
      obtain ⟨πT, hπT, hfπ⟩ := hfac j' w' hw'
      have hlt : j' < (us.grades i).length := by
        rw [hlg, ← Telescope.length_nestPositions _ _ (Telescope.length_nest _ _) 0]
        exact (List.getElem?_eq_some_iff.1 hj').1
      obtain ⟨e₀, he₀⟩ : ∃ e₀, (us.grades i)[j']? = some e₀ := ⟨_, List.getElem?_eq_getElem hlt⟩
      obtain ⟨hre, hrz⟩ := Telescope.resultGrades_of_index hj' he₀ hπT
      have hgl := hg i j T' con l p hi' hl'
      rw [hrz] at hgl
      rw [hre] at he
      exact Grade.used_of_result r p.usage (gs i l) e₀ πT hr hgl he (hfπ ▸ hfw)
    obtain ⟨v, H₃, tr, hev, hH₃, hrun⟩ := RunsAs.recursor_ctor (ϱ := ϱ) hd hord ⟨hdecl, hT, rfl⟩
      hv hadm has hCs hCv hus hRs hctx hsorts hrec husr hg hχ hs hσ hEV hE g' E'' hg' hj hcon hi'
      hw hwv hHH' ϖ' (hH'.getElem? ha)
      (fun l p hlp => ⟨_, by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ π π' : Multiplicity, π * π' ≤ π * π') _ _⟩)
      (fun l p hlp => ⟨_, _, by rw [List.getElem?_map, hlp]; rfl,
        by rw [List.getElem?_map, hlp]; rfl,
        (by decide : ∀ a r q : Grade, (a * (r * q)).run ≤ a.run * (r.run * q.run)) _ _ _⟩)
      (fun l D' hl => by
        -- The requirement of the recursion is below the coefficient of the field.
        obtain ⟨hmem, hlt⟩ := Telescope.mem_positions_of_recursionAt hl
        refine ⟨_, _, by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl,
          by rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl, fun hne => ?_⟩
        show (sig.recursionRequirement T.name qs ps ⟨κ.quality, r, ς⟩ χ').run ≤ _
        rw [hd.recursionRequirement_eq ⟨hdecl, hT, rfl⟩ hq hp]
        have h1 : Mode.oneOne.grade * r = r := Grade.modality.semiring.one_mul r
        have hle := TypeDeclaration.recursionRequirement_run_le (sig := sig)
          (v := ⟨κ.quality, r, ς⟩) (m := .oneOne) (χ := χ') (qs := qs) (ps := ps) hi' hmem
          (List.getElem?_eq_getElem hlt) (by rw [h1]; rwa [(Grade.run_op _ _).2.1])
        rw [h1] at hle
        rwa [(Grade.run_op _ _).2.1] at hle)
      (fun h0 => absurd h0 hρ)
      fun ts hfs hts hrecV => by
        subst hfs
        -- The fields, related at their types.
        refine ⟨(RunsAsArgs.of_fields hd hdecl hv hT' hcon hq hl hp hadm hasσ hs hS
          (fun T' hT' => (hU T' hT').1) (fun _ _ _ _ h => h.1) hts (gs i)
          (fun l p hl' hgl => (by decide : ∀ r p g x : Grade, r ∉ Mode.oneOne.erased →
            r * p ≤ g + x * r → g ∉ Mode.oneOne.erased → p ∉ Mode.oneOne.erased) r p.usage
            (gs i l) _ hr (hg i j T' con l p hi' hl') hgl) hSX).mono hd hH', ?_⟩
        -- The recursive results used at run time, of fields that `X` relates.
        rw [Telescope.recursion_eq_map_nest] at hrecV
        refine RunTelRel.recAt (hS X T' hT' con hcon) _ (Telescope.length_nest _ _) _ ts
          (fun l D hD => ?_) (fun l ms hms => ⟨fun h0 => ?_, fun p A t R b hl' hA htA hRn hb he => ?_⟩)
          (fun l D p hD hl' he => ?_) bs hSX hts hrecV
        · -- A recursive field: the recursor on it, by `X`.
          have hr' : (con.fields (.ofLists qs ps hq hp)).nestAt decl.names l = .direct D := by
            simp only [Telescope.nestAt, hD, Option.getD_some]
          refine ⟨(_, (X D).computed sig ι), by rw [hr']; rfl,
            fun t b ⟨v, hcv, hXv⟩ hVt ϖ'' H'' hH'' _ g₂ E₂ hg₂ => ?_⟩
          have hDn := Telescope.mem_names_of_direct_mem (List.mem_of_getElem? hD)
          obtain ⟨C₃, hC₃⟩ := Motives.get_idxOf hT hnd hCs hDn
          obtain ⟨j₃, T₃, C₃', hj₃, rfl, hC₃', -⟩ :=
            Motives.get_subst_idxOf hT hnd hCs σ hDn (Motives.get_subst σ hC₃)
          rw [hidx j₃ T₃ hj₃, hC₃'] at hC₃
          cases hC₃
          have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
          obtain ⟨b', H₃, tr', hev, hH₃, hrun⟩ := hXv.2 ϖ'' H'' (hH'.trans hH'')
            (hHH'.trans hH'') g₂ E₂ hg₂ (hvv.trans hvv.symm) C₃ ((hidx j₃ T₃ hj₃).symm ▸ hC₃')
          refine ⟨b', H₃, tr', hev, hH₃, fun b₁ hb₁ => ?_⟩
          obtain ⟨-, C₄, hC₄, rfl⟩ := Lifting.ofMotives_block_inv hb₁
          obtain ⟨j₄, T₄, C₄', hj₄, hT₄, hC₄', rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hDn hC₄
          have hj₄₃ : j₄ = j₃ :=
            List.getElem?_inj_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hj₄ hj₃ hT₄
          rw [hj₄₃, hC₃'] at hC₄'
          cases hC₄'
          rw [Term.recursorAt_subst₀]
          exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃' hcv.1 hVt hrun
        · -- A nested field has a position.
          have hn : (con.fields (.ofLists qs ps hq hp)).nestAt decl.names l = .inst ms := by
            simp only [Telescope.nestAt, hms, Option.getD_some]
          rw [hn] at h0
          exact nomatch Nest.map_eq_plain.1 h0
        · -- A nested field: the corecursor of its shape, `RunsAs.nested`.
          have hn : (con.fields (.ofLists qs ps hq hp)).nestAt decl.names l = .inst ms := by
            simp only [Telescope.nestAt, hms, Option.getD_some]
          rw [hn] at hRn
          intro σ' π χ'' e A' mr hsh hres hL hrun hval ϖ'' H'' c π' hH'' hcell _ g₂ E₂ hg₂
          obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1
            (Telescope.mem_nestPositions.2 ⟨_, hms, rfl⟩ : 0 + l ∈ _)
          rw [Nat.zero_add] at hj'
          have hσ' := (Constructor.nestedShapes_shape (ls.getFin hl) (as.subst σ) ts hA hms σ').2
            ⟨π, χ'', hsh⟩
          have hw : (con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ'
              (.ofLists qs ps hq hp))[j']? = some (.nested l σ') :=
            (Constructor.recursiveResults_eq_nested hj' σ').2 ⟨by
              unfold Telescope.recursionAt
              rw [Telescope.recursion_eq_map_nest, List.getElem?_map, hms]
              rfl, hσ'⟩
          have hpu : π.run ≠ .zero → p.usage ∉ Mode.oneOne.erased := fun hπ =>
            hused l p j' _ hl' hj' hw (by
              show σ'.factor ≠ .zero
              rw [Shape.factor_eq_run hsh]
              exact hπ) he
          have hτm : Nest.All (fun x => RunRel.Monotone x.2)
              ((Nest.inst ms).map fun D' =>
                (Term.inst D' qs ls ps (as.subst σ), (X D').computed sig ι)) :=
            Nest.map_rel₃ (r := fun (x _ _ : RunNestLeaf) => RunRel.Monotone x.2)
              (fun D' => @fun _ _ hH₀ _ _ hx =>
                RunRel.computed_mono (fun _ _ h => hXmono D' hH₀ h) hx) _
          have hmR : R.Monotone := levelRel_runNest_mono hd hRn hτm
          exact RunsAs.nested hd hord (fun hdecl hD hL => hord.lifts hdecl hD hL) hr
            Signature.blockShapes_of_block hprop hRn
            (Nest.map_rel₃ (r := fun (x _ _ : RunNestLeaf) => RunLeafCongr sig ι x.2)
              (fun _ => RunRel.computed_leafCongr _) _) hτm
            (Nest.rel_map (fun D' => hleaf g₂ E₂ hg₂ D') _) htA hres hL hsh hrun hval
            (hHH'.trans hH'') (fun hπ => ⟨π', b, hcell, hmR (hH'.trans hH'') (hb (hpu hπ))⟩) ϖ''
            H'' (List.prefix_refl _)
        · -- The field of a recursive result used at run time is used too.
          obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1
            (Telescope.mem_nestPositions.2 ⟨_, hD, rfl⟩ : 0 + l ∈ _)
          rw [Nat.zero_add] at hj'
          have hw : (con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ'
              (.ofLists qs ps hq hp))[j']? = some (.field l) := by
            rw [Constructor.getElem?_recursiveResults, hj', Option.map_some]
            congr 1
            have hrec' : (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l = some D := by
              unfold Telescope.recursionAt
              rw [Telescope.recursion_eq_map_nest, List.getElem?_map, hD]
              rfl
            rw [hrec']
            rfl
          exact hused l p j' _ hl' hj' hw (by decide : Multiplicity.one ≠ .zero) he
    exact ⟨v, H₃, tr, hev, hH₃, hrun C' hC'⟩
  -- The term of the recursor, related to its address by `(®_μ)`, which the relations `X` contain.
  obtain ⟨v, hv₀, hp₀ | ⟨R, hR, w, htw, hRw⟩⟩ := ht
  · cases Computesι.det hd hv₀ (hI _)
    obtain ⟨_, _, hp₁⟩ := hp₀
    exact (RunUnivRel.not_prop hd (hU T hT).1 (levelRel_prop_iff.1 hp₁)).elim
  · cases Computesι.det hd hv₀ (hI _)
    rw [HasRun.eq hd hR (.univ _ (levelRel_run_iff.2 (hU T hT).1))] at hRw
    have hwv := (ValidEqTerm₀.redStar_iff hd htw.1).1 htv
    have hC₀ : Cs.get (decl.names.idxOf T.name) = some ⟨0, C⟩ := (hidx h' T hh).symm ▸ hC
    obtain ⟨b, H₂, tr, hev, hH₂, hrun⟩ :=
      (hRw X hclosed).2 ϖ₀ H₁ (List.prefix_refl _) hH₁ g E' hgE (hwv.trans hwv.symm) C hC₀
    exact ⟨b, H₂, tr, hev, hH₂, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC htw.1 htv hrun⟩

/-- `r ∈ S`, by induction on `(eq_μ)`: the term of the skeleton of the instance evaluates to an
address that the erased recursor, its branches renamed by `g` in an environment `E'` that binds
each variable `g x` as `E` binds `x`, eliminates to the address of a value to which the recursor on
a term of the instance is related at the motive at the term, when every type of the block has one
constructor at most; the recursive result of a nested field is the corecursor of its shape,
`RunsAs.nestedSkeleton`, whose leaves are the recursor on the terms of the skeletons of the types of
the block. -/
theorem RunsAs.recursor_skeleton (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {h' : Nat} {C : Term 0 (.var :: Γ)} (hh : decl.dataTypes[h']? = some T)
    (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hRs : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ' Cs) (Rs con) (πs i))
    (hctx : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ValidCtx₀ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con)))
    (hsorts : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) → ∀ θ,
      EqSubst sig ι (ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) θ θ →
      Telescope.ValidSorts₀ sig ι ((Rs con).subst θ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t₁ t₂,
      ValidEqTerm₀ sig ι t₁ t₂ ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidEqTerm₀ sig ι
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₁ κ (Cs.subst σ) (us.subst σ))
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₂ κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs Rs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hr : r ∈ Mode.oneOne.erased) (h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1)
    {σ : Subst 0 [] Γ} {H : Heap} {E V : List Nat}
    (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V) (hE : RunsAsSubst sig ι P H ctx χ σ V)
    {m : Nat} (g : TargetRen m Γ.length) (E' : List Nat)
    (hgE : ∀ x : Fin Γ.length, E'[(g x : Nat)]? = E[(x : Nat)]?) {H₁ : Heap}
    (hH₁ : H.Extends H₁) (ϖ₀ : Multiplicity) {t : Term 0 []}
    (htv : ValidTerm₀ sig ι t ((Term.inst D qs ls ps as).subst σ)) :
    ∃ a H₂ b H₃ tr,
      Eval P (ϖ₀ * r.run) H₁ E' (((sig.skeleton D qs ps).target : Target Γ.length).rename g) a H₂
        [] ∧
      EvalRec P ϖ₀ H₂ E' r.run .omega ((us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
        ((sig.caseFieldParams D qs ps).getD [])).rename g) a b H₃ tr ∧ H₁.Extends H₃ ∧
      RunsAs sig ι P H₃ (.recursor r ς χ' D qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
        ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hmonoM, hrecM, hNM, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  have hval : ∀ T' ∈ decl.dataTypes, ∀ a b,
      (DataType.blockRel decl.dataTypes SM T'.name).computed sig ι a b →
        ValidEqTerm₀ sig ι a b (.inst T'.name qs ls ps (as.subst σ)) :=
    fun T' hT' _ _ hab => (FieldRel.univ rfl (hUM T' hT').1).validEqTerm hd (hI _) hab
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  let Ns := us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ')
    ((sig.caseFieldParams T.name qs ps).getD [])
  let f : Name → Term 0 [] → Term 0 [] := fun D' t =>
    .recursor r ς χ' D' qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)
  -- The erased recursor on the term of a skeleton of the type `D'` of a canonical term `v`, within
  -- the depth of the number of the types of the block minus that of the ancestors `A` of `D'`,
  -- evaluated in any scope and environment, since it mentions no variable, evaluates, in each heap
  -- that extends the heap of this term, with its branches renamed by any renaming in any
  -- environment that binds the renamed scope as `E` binds the scope, to the address of a value
  -- related to the recursor on `v` at the motive.
  let Pk : Name → Term 0 [] → Prop := fun D' v => ∀ (A : List Name) (d : Nat), A.Nodup →
    (∀ X ∈ A, X ∈ decl.names) → (∀ X ∈ A, Relation.TransGen (decl.Below I) D' X) →
    d + A.length = decl.names.length → ∀ {n₁ : Nat} ϖ' (E₁ : List Nat) H₂ a H₃ tr₀, H.Extends H₂ →
    Eval P ϖ' H₂ E₁ ((decl.skeleton I d D').target : Target n₁) a H₃ tr₀ →
    ValidTerm₀ sig ι v (.inst D' qs ls ps (as.subst σ)) → ∀ ϖ'' H', H₃.Extends H' →
    ∀ {m' : Nat} (g' : TargetRen m' Γ.length) (E'' : List Nat),
    (∀ x : Fin Γ.length, E''[(g' x : Nat)]? = E[(x : Nat)]?) →
    ∃ b H₄ tr, EvalRec P ϖ'' H' E'' r.run .omega (Ns.rename g') a b H₄ tr ∧ H'.Extends H₄ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get (decl.names.idxOf D') = some ⟨0, C'⟩ →
        RunsAs sig ι P H₄ (f D' v) b ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))
  -- The relations of the canonical terms that `(eq_μ)` relates, whose type is accessible for `≺`,
  -- and on the terms of whose skeletons the erased recursor evaluates as `Pk` states.
  let X : Name → TermRel := fun D' v w =>
    DataType.blockRel decl.dataTypes SM D' v w ∧ Acc (decl.Below I) D' ∧ Pk D' v
  have hr0 : r.run = .zero := Mode.run_of_mem_oneOne_erased r hr
  -- The leaves of the nested results: the recursor on the term of the skeleton of a type of the
  -- block, which stands for a term of this type that `X` relates, in a heap that extends `H`.
  have hleaf : ∀ {m₁ : Nat} (g₁ : TargetRen m₁ Γ.length) (E₁ : List Nat),
      (∀ x : Fin Γ.length, E₁[(g₁ x : Nat)]? = E[(x : Nat)]?) → ∀ D',
      SkeletonResultLeaf sig ι P
        (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
        (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ))
        (sig.blockShapes decl.names qs ps χ') .omega (Ns.rename g₁) E₁ H D'
        (.inst D' qs ls ps (as.subst σ), (X D').computed sig ι) := by
    intro m₁ g₁ E₁ hE₁ D' b ms hb hms t t' htt m₂ g₂ E₂ hE₂ H₃ O hHH₃ ϖ H₄ hH₄
    obtain ⟨hD', C₀, hC₀, rfl⟩ := Lifting.ofMotives_block_inv hb
    simp only [Signature.blockShapes, hD', ↓reduceIte, Option.some.injEq] at hms
    subst hms
    obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
    obtain ⟨v, w', hcv, hcw, hXv⟩ := htt
    have htu := hval T₃ hT₃ t t' ⟨v, w', hcv, hcw, hXv.1⟩
    have hvt := htu.trans htu.symm
    have hvv := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hvt
    obtain ⟨a, H₅, hev, hH₅⟩ := (decl.skeleton I decl.names.length T₃.name).target_isData.eval
      (n := m₂) P (ϖ * .zero) H₄ E₂
    obtain ⟨j₃, T₄, C₃, hj₃, hT₄, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hD' hC₀
    obtain rfl : T₄ = T₃ := List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd)
      (List.mem_of_getElem? hj₃) hT₃ hT₄
    obtain ⟨b', H₆, tr, hevr, hH₆, hrun⟩ := hXv.2.2 [] _ List.nodup_nil (fun _ h => nomatch h)
      (fun _ h => nomatch h) rfl _ E₂ H₄ a H₅ [] (hHH₃.trans hH₄) hev (hvv.trans hvv.symm) ϖ H₅
      (List.prefix_refl _) (g₂ ∘ g₁) E₂ (fun x => (hE₂ (g₁ x)).trans (hE₁ x))
    refine ⟨b', H₆, [] ++ tr, ?_, hH₅.trans hH₆, ?_⟩
    · show Eval P ϖ H₄ E₂ (.recursor .zero .omega
        (if (Multiplicity.zero : Multiplicity) = .zero then (sig.skeleton _ qs ps).target
          else O) ((Ns.rename g₁).rename g₂)) b' H₆ _
      rw [ite_eq_left rfl, TargetBranches.rename_rename, hd.skeleton ⟨hdecl, hT₃, rfl⟩ hq hp]
      rw [hr0] at hevr
      exact .recursor hev hevr
    · rw [Term.recursorAt_subst₀]
      exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₃ hC₃ hcv.1 hvt
        (hrun C₃ ((hidx j₃ _ hj₃).symm ▸ hC₃))
  have hclosed : ∀ T' ∈ decl.dataTypes, ∀ v w, T'.ctorRel T'.name (SM X) v w →
      X T'.name v w := by
    intro T' hT' v w hc
    obtain ⟨con, hcon, fs, fs₂, hvc, hwc, hSX⟩ := hc
    have hSX' := hmonoM X _ (fun _ _ _ h => h.1) T' hT' con hcon fs fs₂ hSX
    obtain ⟨ts, us', rfl, rfl, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hSX'
    have hrX := hrecM X T' hT' con hcon _ _ hSX
    have hcons : T'.constructors = [con] :=
      List.eq_singleton_of_mem_of_length_le_one hcon (h1 T' hT')
    -- The type is accessible for `≺`: each type below it is that of a recursive field.
    have hacc : Acc (decl.Below I) T'.name := Acc.intro _ fun D'' ⟨T₀, hT₀, hn₀, c₀, hc₀, hm⟩ => by
      cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT₀ hT' hn₀
      rw [hcons] at hc₀
      cases hc₀
      obtain ⟨_, _, _, _, _, _, hX₁⟩ :=
        Terms.RecRel.exists_of_mem _ (Telescope.length_recursion _ _) ts us' hrX hm
      exact hX₁.2.1
    refine ⟨DataType.blockRel_closed hmonoM hT'
      ⟨con, hcon, ts.terms, us'.terms, hvc, hwc, hSX'⟩, hacc, ?_⟩
    intro A d hA hAn hAD hdA n₁ _ E₁ H₂ a H₃ _ hH₂ hev hvv ϖ'' H' hH' _ g' E'' hg'
    -- The depth is not reached, since the ancestors are fewer than the types of the block.
    have hlt := TypeDeclaration.length_ancestors_lt hacc (TypeDeclaration.name_mem_names hT') hA
      hAn hAD
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    -- The term of the skeleton unfolds into the constructor of the case of the type.
    obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
    rw [TypeDeclaration.skeleton_succ hnd I hT' rfl hcons
      (Entry.constructorCase_of_cases (hd.cases_nodup hdecl) hi)] at hev
    cases hev with
    | @ctor _ _ _ H₂₀ _ _ _ bs _ hall =>
    have hH₂₀ : H₂₀.Extends H' := (List.prefix_append H₂₀ _).trans hH'
    have hHH' : H.Extends H' := hH₂.trans (hall.extends.trans hH₂₀)
    have hbl : bs.length = (con.params I).length := by
      rw [EvalAll.length_ofList _ hall, List.length_map, Telescope.length_recursion]
    -- The fields of the term of the skeleton are stored at the multiplicity `0`, and the grade of
    -- the recursor has no use at run time.
    have hπv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target n₁))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          r.run * π₀ ≤ r.run * p.usage.run := fun l p hlp => by
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨.zero, ?_, (by decide : ∀ (r : Grade) (π π' : Multiplicity),
        r ∈ Mode.oneOne.erased → r.run * π ≤ r.run * π') r _ _ hr⟩
      rw [Targets.multiplicities_ofList, List.map_map, List.getElem?_map,
        List.getElem?_eq_getElem hl, Option.map_some]
      congr 1
      simp only [Function.comp_apply]
      split <;> rfl
    -- The fields of the term of the skeleton are stored at the requirement `ω`, and the
    -- coefficients of their ownerships are `0`, since the grade of the recursor has no use at run
    -- time.
    have hκv : ∀ (l : Nat) (p : Parameter), (con.params I)[l]? = some p →
        ∃ π₀ ϱ₀, (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target n₁))
            | none => (.zero, .erased))).multiplicities[l]? = some π₀ ∧
          (Targets.ofList (((con.fields I).recursion decl.names).map fun
            | some D' => ((.zero : Multiplicity), ((decl.skeleton I d' D').target : Target n₁))
            | none => (.zero, .erased))).requirements[l]? = some ϱ₀ ∧
          (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀) := fun l p hlp => by
      obtain ⟨π₀, hπ₀, -⟩ := hπv l p hlp
      have hl : l < ((con.fields I).recursion decl.names).length := by
        rw [Telescope.length_recursion]
        exact (List.getElem?_eq_some_iff.1 hlp).1
      refine ⟨π₀, .omega, hπ₀, ?_, (by decide : ∀ (r a q : Grade) (π : Multiplicity),
        r ∈ Mode.oneOne.erased → (a * (r * q)).run ≤ .omega * (r.run * π)) r _ _ _ hr⟩
      rw [Targets.requirements_ofList, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hl)]
      rfl
    obtain ⟨b, H₄, tr, hevr, hH₄, hrun⟩ := RunsAs.recursor_ctor hd hord ⟨hdecl, hT, rfl⟩ hv hadm
      has hCs hCv hus hRs hctx hsorts hrec husr hg hχ hs hσ hEV hE g' E'' hg' hj hcon hi hvc hvv
      hHH' ϖ''
      (hH'.getElem? List.getElem?_concat_length) hπv hκv
      (fun l _ hl => by
        -- The fields of the term of the skeleton, which the recursor does not use, state nothing of
        -- the requirement of its recursion.
        obtain ⟨-, hlt⟩ := Telescope.mem_positions_of_recursionAt hl
        obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, -⟩ := hκv l _ (List.getElem?_eq_getElem hlt)
        exact ⟨π₀, ϱ₀, hπ₀, hϱ₀, fun hne => absurd ((by decide : ∀ (g : Grade) (π : Multiplicity),
          g ∈ Mode.oneOne.erased → g.run * π = .zero) r π₀ hr) hne⟩)
      (fun _ => rfl)
      fun ts' hfs _ _ => by
        obtain rfl := Args.terms_inj hfs
        -- The fields are erased, at grades erased since the grade of the recursor is.
        refine ⟨RunsAsArgs.of_erased ts' bs _ (fun l p hl' => (by decide : ∀ r p g x : Grade,
          r ∈ Mode.oneOne.erased → r * p ≤ g + x * r → g ∈ Mode.oneOne.erased) r p.usage
          (gs i l) _ hr (hg i j T' con l p hi hl')) hbl, ?_⟩
        -- The recursive results used at run time, on the terms of the skeletons of the recursive
        -- fields.
        rw [Telescope.recursion_eq_map_nest] at hall hrX
        refine EvalAll.recAt (V := fun D => (X D).computed sig ι)
          (L := fun D => (.inst D qs ls ps (as.subst σ), (X D).computed sig ι)) (sE := .type) _
          ?_ ?_ (Telescope.length_nest _ _) _ _ ts' us'
          (List.prefix_refl _) hall hrX (hNM X T' hT' con hcon _ _ hSX)
        rotate_left
        · -- A nested field: the corecursor of its shape, `RunsAs.nestedSkeleton`, never reads it.
          intro ms A t u F b _ hF htu σ' π χ'' e A' mr hsh hres hL hrun hval ϖ'' H''' c π' hH''' _
            _ g₂ E₂ hg₂
          rw [hr0]
          exact RunsAs.nestedSkeleton hd hord (fun hdecl hD hL => hord.lifts hdecl hD hL)
            Signature.blockShapes_of_block hF
            (Nest.map_rel₃ (r := fun (x _ _ : NestLeaf) => LeafCongr sig ι .type x.2)
              (fun D' a a' b b' h => by
                rcases h with h | ⟨ha, hb⟩
                · cases h
                · exact ⟨fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).1 hv, (hb w).1 hw, hx⟩,
                    fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).2 hv, (hb w).2 hw, hx⟩⟩) _)
            (Nest.rel_map (fun D' => hleaf g₂ E₂ hg₂ D') _) htu hres hL hsh hrun hval c H'''
            (hHH'.trans hH''') ϖ'' H''' (List.prefix_refl _)
        intro D'' hD'' t u ⟨v₁, w₁, hcv, hcw, hX₁⟩ ϖa Ha b' Hb Rb hHa hevb hHb ϖb H'' hH'' _ g₂ E₂
          hg₂
        have hDn := Telescope.mem_recursion ((Telescope.recursion_eq_map_nest _ _) ▸ hD'')
        obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hDn
        have htu := hval T₃ hT₃ t u ⟨v₁, w₁, hcv, hcw, hX₁.1⟩
        have hVt := htu.trans htu.symm
        have hvv₁ := (ValidEqTerm₀.redStar_iff hd hcv.1).1 hVt
        have hb : decl.Below I T₃.name T'.name :=
          ⟨T', hT', rfl, con, hcons, (Telescope.recursion_eq_map_nest _ _) ▸ hD''⟩
        obtain ⟨b'', H₅, tr', hev', hH₅, hrun'⟩ := hX₁.2.2 (T'.name :: A) d'
          (List.nodup_cons.2 ⟨fun hm => hacc.not_transGen_self (hAD _ hm), hA⟩)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact TypeDeclaration.name_mem_names hT'
            · exact hAn X hX)
          (fun X hX => by
            rcases List.mem_cons.1 hX with rfl | hX
            · exact .single hb
            · exact .trans (.single hb) (hAD X hX))
          (by simp only [List.length_cons]; omega) ϖa _ Ha b' Hb Rb (hH₂.trans hHa) hevb
          (hvv₁.trans hvv₁.symm) ϖb H'' (hHb.trans (hH₂₀.trans hH'')) g₂ E₂ hg₂
        refine ⟨b'', H₅, tr', hev', hH₅, fun b₁ hb₁ => ?_⟩
        obtain ⟨-, C₄, hC₄, rfl⟩ := Lifting.ofMotives_block_inv hb₁
        obtain ⟨j₄, T₄, C₄', hj₄, hT₄, hC₄', rfl⟩ :=
          Motives.get_subst_idxOf hT hnd hCs σ hDn hC₄
        obtain rfl : T₄ = T₃ := List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd)
          (List.mem_of_getElem? hj₄) hT₃ hT₄
        rw [Term.recursorAt_subst₀]
        exact RunsAs.recursor_of_redStar hd hCv hrec hσ hj₄ hC₄' hcv.1 hVt
          (hrun' C₄' ((hidx j₄ _ hj₄).symm ▸ hC₄'))
    refine ⟨b, H₄, tr, hevr, hH₄, fun C' hC' => hrun C' ?_⟩
    rwa [hidx j T' hj] at hC'
  -- The term of the recursor computes to a canonical term that `(eq_μ)` relates, which the
  -- relations `X` contain.
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ := htv.2.1 fun ⟨v, hv', _, _, hk⟩ => by
    cases Computesι.det hd (hI _) hv'
    exact HasEq.univ_not_prop hd (levelRel_univ_iff.2 (hUM T hT).1) hk
  cases Computesι.det hd (hI _) hv'
  have hX := ((HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T hT).1)) _ _).1 hrel) X
    hclosed
  have hww := (ValidEqTerm₀.redStar_iff hd hw₁.1).1 htv
  obtain ⟨a, H₂, hev, hH₂⟩ :=
    (decl.skeleton I decl.names.length T.name).target_isData.eval (n := m) P (ϖ₀ * r.run) H₁ E'
  obtain ⟨b, H₃, tr, hevr, hH₃, hrun⟩ := hX.2.2 [] _ List.nodup_nil (fun _ h => nomatch h)
    (fun _ h => nomatch h) rfl _ E' H₁ a H₂ [] hH₁ hev (hww.trans hww.symm) ϖ₀ H₂
    (List.prefix_refl _) g E' hgE
  refine ⟨a, H₂, b, H₃, tr, ?_, hevr, hH₂.trans hH₃, RunsAs.recursor_of_redStar hd hCv hrec hσ hh hC
    hw₁.1 htv (hrun C ((hidx h' T hh).symm ▸ hC))⟩
  rw [Skeleton.target_rename, hd.skeleton ⟨hdecl, hT, rfl⟩ hq hp]
  exact hev

-- ADE: the cases `natrecₘ`, `prodrecₘ`, `unitrecₘ` and `emptyrecₘ` of `fundamental`, in
-- `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- `(rec)` keeps the validity at run time: the erasure of the recursor evaluates its term, or the
term of the skeleton of its instance when its grade `r` is erased, then the branch of the case of
its value, in every environment that binds the scope through a renaming. A recursor on a block of
propositions has no constructor, in the mode `11ᵐ`, so that no term of its instance is true and none
is substituted. -/
theorem RunValidRen.recursor (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {γ : GradeVector Γ.length} {t : Term 0 Γ} {h' : Nat} {C : Term 0 (.var :: Γ)}
    (hh : decl.dataTypes[h']? = some T) (hC : Cs.get h' = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hRs : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ' Cs) (Rs con) (πs i))
    (hctx : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ValidCtx₀ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con)))
    (hsorts : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) → ∀ θ,
      EqSubst sig ι (ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)) θ θ →
      Telescope.ValidSorts₀ sig ι ((Rs con).subst θ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t₁ t₂,
      ValidEqTerm₀ sig ι t₁ t₂ ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidEqTerm₀ sig ι
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₁ κ (Cs.subst σ) (us.subst σ))
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₂ κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)))
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (htr : r ∉ Mode.oneOne.erased → RunValidRen sig ι P hΓ ctx γ t (.inst D qs ls ps as))
    (husr : RunValidBranches sig ι P hΓ ctx decl qs ls ps hq hl hp as Cs us δs gs Rs)
    (hg : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      Mode.oneOne.grade * r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)) l) * r)
    (hχ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      χ ≤ᶜ δs i +ᶜ Telescope.resultSum
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names) ·ᶜ χ)
    (hr : (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) → r.mode = .oneOne)
    (hempty : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases = [])
    (hprop : ∀ {decl : TypeDeclaration} {D : Name}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope},
      sig.HasCodataType D decl T → ∀ {qs : List Quality} {ps : List Grade}
        (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades),
        decl.constraint (.ofLists qs ps hq hp) →
        (decl.sort (.ofLists qs ps hq hp)).quality = .prop →
        ∀ {d : Name} {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope}
          {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
          {ψ : ResultOwnership Grade ps₁.length},
          (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ → p ∈ Mode.oneOne.erased) :
    RunValidRen sig ι P hΓ ctx ((r ·ᶜ γ) +ᶜ χ) (.recursor r ς χ' D qs ls ps as t κ Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  intro w σ H E V hσ hEV hE _ g E' hgE
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hS := Mode.erasesUncounted .oneOne
  have hEχ : RunsAsSubst sig ι P H ctx χ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
    h (hS.add _ _ (by rw [Grade.modality.semiring.add_comm]; exact h'))) hE
  have hg' : ∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
      (con.params (.ofLists qs ps hq hp))[l]? = some p →
      r * p.usage ≤ gs i l +
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (List.zipWith (· * ·) (us.grades i) (πs i)) l) * r := fun i j T' con l p hi hl' => by
    have h₁ := hg i j T' con l p hi hl'
    rwa [show Mode.oneOne.grade = Grade.one from rfl, Grade.modality.semiring.one_mul] at h₁
  have htσ : ValidTerm₀ sig ι (t.subst σ) ((Term.inst T.name qs ls ps as).subst σ) :=
    ht.2 σ σ hσ
  have hCσ : (C.subst₀ (Subst₀.single t)).subst σ =
      (C.subst (Subst.lift σ)).subst₀ (Subst₀.single (t.subst σ)) :=
    Term.subst_subst₀_of (Subst₀.Swaps.single _ _) C
  rw [hCσ]
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality with
  | prop =>
    -- No term of an instance of a block of propositions without constructor is true.
    have hasσ := has.2 σ σ hσ
    obtain ⟨S, hP, hmono, -, -, -⟩ := hv.propRel hd hdecl hq hl hp hadm hasσ hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have hI : Computesι sig ι (.inst T.name qs ls ps (as.subst σ))
        (.inst T.name qs ls ps (as.subst σ)) := ⟨.refl _, .inst _ _ _ _ _⟩
    obtain ⟨v', R', hv', hR', hrel⟩ := htσ.2.2 ⟨_, hI, _, _, hP'⟩
    cases Computesι.det hd hI hv'
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      (HasEq.unique hd hR' (.prop _ _ hP' fun _ _ => .rfl) _ _).1 hrel
    obtain ⟨T₀, hT₀, -, con₀, hcon₀, -⟩ := DataType.blockTruth_inv hmono htrue
    obtain ⟨i, j, hi, -⟩ := TypeDeclaration.exists_cases hT₀ hcon₀
    rw [hempty hs] at hi
    cases hi
  | type =>
    by_cases hrS : r ∈ Mode.oneOne.erased
    · -- The term of the skeleton of the instance stands for the term.
      have h1 : ∀ T' ∈ decl.dataTypes, T'.constructors.length ≤ 1 := fun T' hT' => by
        refine Nat.le_of_not_lt fun h2 => ?_
        exact (by decide : ∀ r : Grade, r ∈ Mode.oneOne.erased → r.mode ≠ .oneOne) r hrS
          (hr ⟨T', hT', h2⟩)
      obtain ⟨a, H₂, b, H₃, tr, hev, hevr, hH₃, hrun⟩ := RunsAs.recursor_skeleton hd hord h hv hadm
        has hh hC hCs hCv hus hRs hctx hsorts hrec husr hg' hχ hs hrS h1 hσ hEV hEχ g E' hgE
        (List.prefix_refl H) w htσ
      refine ⟨b, H₃, [] ++ tr, ?_, hH₃, hrun⟩
      show Eval P w H E' ((Target.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _).rename g) b H₃ _
      rw [ite_eq_left hrS, ite_eq_left hrS]
      exact .recursor hev hevr
    · -- The term evaluates to the address of its value.
      have hγ : RunsAsSubst sig ι P H ctx γ σ V := RunsAsSubst.of_counted ctx (fun x h h' =>
        h (hS.mul _ _ hrS (hS.add _ _ h'))) hE
      obtain ⟨a, H₁, tr₁, hev, hH₁, hta⟩ := htr hrS (w * r.run) σ H E V hσ hEV hγ g E' hgE
      obtain ⟨b, H₂, tr₂, hevr, hH₂, hrun⟩ := RunsAs.recursor hd hord h hv hadm has hh hC hCs hCv
        hus hRs hctx hsorts hrec husr hg' hχ hprop hs hrS hσ hEV hEχ g E' hgE hH₁ w htσ hta
      refine ⟨b, H₂, tr₁ ++ tr₂, ?_, hH₁.trans hH₂, hrun⟩
      show Eval P w H E' ((Target.recursor _ (if r ∈ Mode.oneOne.erased then _ else _)
        (if r ∈ Mode.oneOne.erased then _ else _) _).rename g) b H₂ _
      rw [ite_eq_right hrS, ite_eq_right hrS]
      exact .recursor hev hevr

end

end Sic.Core
