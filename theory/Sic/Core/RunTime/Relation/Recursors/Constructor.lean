module

public import Sic.Core.Lifting.Extension
public import Sic.Core.RunTime.Relation.Recursors.Results
import Sic.Core.Erasure.Fields
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Results.Existence
import Sic.Core.Results.Substitution
import Sic.Core.RunTime.Monotonicity
import Sic.Core.RunTime.Relation.Computation
import Sic.Core.RunTime.Relation.DeclaredTypes
import Sic.Core.RunTime.Relation.Recursors.Erasure
import Sic.Core.RunTime.Relation.Substitution
import Sic.Core.RunTime.Subsumption
import Sic.Core.Soundness.Closed
import Sic.Core.Shape.Results.Fields
import Sic.Core.Soundness.Recursors
import Sic.Core.Soundness.Recursors.Results
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Constructors at Run Time

The erased recursor eliminates the address of a constructor of a type of a block by the branch of
its case, which `RunsAs.recursor_ctor` states, as both cases of the recursors at run time do.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {sig : Signature} {ι : Interpretation} {P : Program}

/-- Terms related to themselves at the recursive fields by `Q` are related to themselves by `Q'`,
when `Q'` relates each term to itself that `Q` does. -/
theorem Terms.RecRel.of_diag {Q Q' : Name → TermRel} :
    (rs : List (Option Name)) → {ts : Terms 0 []} →
      (∀ D, some D ∈ rs → ∀ t, Q D t t → Q' D t t) → Terms.RecRel Q rs ts ts →
        Terms.RecRel Q' rs ts ts
  | some D :: rs, .cons _ _, h, hqs =>
    ⟨h D (List.mem_cons_self ..) _ hqs.1,
      Terms.RecRel.of_diag rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hqs.2⟩
  | none :: rs, .cons _ _, h, hs =>
    Terms.RecRel.of_diag (Q := Q) rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hs
  | [], _, _, _ | some _ :: _, .nil, _, _ | none :: _, .nil, _, _ => trivial

/-! ## Branches -/

section

variable {Γ : Scope} {hΓ : Γ.FirstOrder} {ctx : Context 0 Γ} {decl : TypeDeclaration} {D : Name}
  {T : DataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
  {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
  {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
  {as : InstanceArgs 0 Γ decl.scope} {r ς χ' : Grade} {Cs : Motives 0 Γ} {us : Branches 0 Γ}
  {χ : GradeVector Γ.length} {δs : Nat → GradeVector Γ.length} {gs : Nat → Nat → Grade}
  {κ : Universe 0}

/-- The branches of a recursor are valid at run time: each branch, in the context extended by the
fields of its constructor and by its recursive results `Rs`, the types that the typing gives them,
at the grades of its variables, in every environment that binds its scope through a renaming. -/
def RunValidBranches (sig : Signature) (ι : Interpretation) (P : Program) (hΓ : Γ.FirstOrder)
    (ctx : Context 0 Γ) (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0))
    (ps : List Grade) (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) (as : InstanceArgs 0 Γ decl.scope) (Cs : Motives 0 Γ)
    (us : Branches 0 Γ) (δs : Nat → GradeVector Γ.length) (gs : Nat → Nat → Grade)
    (Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
      Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names)) : Prop :=
  ∀ i j T' con C' u, decl.cases[i]? = some (j, T', con) → Cs.get j = some ⟨0, C'⟩ →
    us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
      (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
    RunValidRen sig ι P ((hΓ.extend _).extend _)
      ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con))
      (((δs i).extendGrades (gs i) (con.params (.ofLists qs ps hq hp))).extendResults
        (Telescope.resultGrades ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
          (us.grades i))
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
        (con.params (.ofLists qs ps hq hp))) u
      ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
        (Ren.weakenN _))

/-- The motives of a block of data types, one for each type, give one to each name of the block. -/
theorem Motives.get_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩) {D' : Name}
    (hD' : D' ∈ decl.names) : ∃ C, Cs.get (decl.names.idxOf D') = some ⟨0, C⟩ := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  rw [TypeDeclaration.idxOf_dataTypes hnd hj]
  exact hCs j T' hj

/-- The motive of a name of a block of data types in its motives substituted by `σ` is the motive of
the type of this name, substituted. -/
theorem Motives.get_subst_idxOf (hT : T ∈ decl.dataTypes) (hnd : decl.names.Nodup)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (σ : Subst 0 [] Γ) {D' : Name} (hD' : D' ∈ decl.names) {C}
    (hC : (Cs.subst σ).get (decl.names.idxOf D') = some ⟨0, C⟩) :
    ∃ j T' C', decl.dataTypes[j]? = some T' ∧ T'.name = D' ∧ Cs.get j = some ⟨0, C'⟩ ∧
      C = C'.subst (Subst.lift σ) := by
  obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
  obtain ⟨C', hC'⟩ := hCs j T' hj
  rw [TypeDeclaration.idxOf_dataTypes hnd hj, Motives.get_subst σ hC'] at hC
  cases hC
  exact ⟨j, T', C', hj, rfl, hC', rfl⟩

/-- A recursor on a term is related at the motive at the term as on the value of the term. -/
theorem RunsAs.recursor_of_redStar (hd : sig.Distinct)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hrec : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ∀ σ, EqSubst sig ι ctx σ σ → ∀ t₁ t₂,
      ValidEqTerm₀ sig ι t₁ t₂ ((Term.inst T'.name qs ls ps as).subst σ) →
      ValidEqTerm₀ sig ι
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₁ κ (Cs.subst σ) (us.subst σ))
        (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t₂ κ (Cs.subst σ) (us.subst σ))
        ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t₁)))
    {σ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ σ) {j : Nat}
    {T' : DataType decl.sorts decl.grades decl.levels decl.scope} {C' : Term 0 (.var :: Γ)}
    (hj : decl.dataTypes[j]? = some T') (hCj : Cs.get j = some ⟨0, C'⟩) {t v : Term 0 []}
    (htv : RedStar (sig.interpret ι) t v)
    (hvt : ValidTerm₀ sig ι t (.inst T'.name qs ls ps (as.subst σ))) {H : Heap} {b : Nat}
    (hrun : RunsAs sig ι P H
      (.recursor r ς χ' T'.name qs ls ps (as.subst σ) v κ (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single v))) :
    RunsAs sig ι P H (.recursor r ς χ' T'.name qs ls ps (as.subst σ) t κ (Cs.subst σ) (us.subst σ)) b
      ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single t)) := by
  have hvv := (ValidEqTerm₀.redStar_iff hd htv).1 hvt
  have hrv := hrec j T' C' hj hCj σ hσ v v (hvv.trans hvv.symm)
  have hmot := (hCv j T' C' hj hCj).motive hσ hvv
  exact (RunsAs.redStar_iff hd (RedStar.recursor htv)).2 (hrun.conv hd hrv.2 hmot.2)

/-- The erased recursor, its branches renamed by `g` in an environment `E'` that binds each variable
`g x` as `E` binds `x`, eliminates the address of a constructor of a type of the block, by the
branch of its case, to the address of a value to which the recursor on a term of the instance that
computes to this constructor is related at the motive at the term, when the fields of the
constructor are related to their addresses at their grades in the branch, and what computes each
recursive result used at run time, the recursor on a recursive field or the corecursor of the shape
of a nested field, with the branches renamed by any renaming in any such environment, is related
to the result: the recursive results of the branch are those of the typing, `Rs` with the factors
`πs`, whose contexts are meaningful and whose types are terms of universes. -/
theorem RunsAs.recursor_ctor (hd : sig.Distinct) (hord : sig.LiftsInOrder)
    (h : sig.HasDataType D decl T)
    (hv : ValidTypeDeclaration sig ι decl) (hadm : decl.constraint (.ofLists qs ps hq hp))
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
      Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names)} {πs : Nat → List Grade}
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
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {σ : Subst 0 [] Γ} {H : Heap}
    {E V : List Nat} (hσ : EqSubst sig ι ctx σ σ) (hEV : H.Binds E V)
    (hE : RunsAsSubst sig ι P H ctx χ σ V) {m : Nat} (g : TargetRen m Γ.length) (E' : List Nat)
    (hgE : ∀ x : Fin Γ.length, E'[(g x : Nat)]? = E[(x : Nat)]?)
    {i j : Nat} {T' : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T') (hcon : con ∈ T'.constructors)
    (hi : decl.cases[i]? = some (j, T', con)) {fs : Terms 0 []} {w : Term 0 []}
    (hw : w.IsCtor T'.name con.name fs)
    (hwv : ValidTerm₀ sig ι w (.inst T'.name qs ls ps (as.subst σ))) {H' : Heap}
    (hH' : H.Extends H') (ϖ₀ : Multiplicity) {a : Nat} {πv ϱv : List Multiplicity}
    {bs : List Nat} (ha : H'[a]? = some (.ctor i πv ϱv bs))
    (hπv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀, πv[l]? = some π₀ ∧ r.run * π₀ ≤ r.run * p.usage.run)
    (hκv : ∀ (l : Nat) (p : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p →
      ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
        (p.requirement * (r * p.usage)).run ≤ ϱ₀ * (r.run * π₀))
    {ϱ : Multiplicity}
    (hϱv : ∀ l D', (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l = some D' →
      ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧
        (r.run * π₀ ≠ .zero → ϱ ≤ ϱ₀ * (r.run * π₀)))
    (hϱ0 : r.run = .zero → ϱ = .omega)
    (hfr : ∀ ts : Args 0 [] (con.params (.ofLists qs ps hq hp)), ts.terms = fs →
      EqSubst sig ι (Context.empty.append
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ))) ts.toSubst ts.toSubst →
      Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
        ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms →
      RunsAsArgs sig ι P H' (gs i) ts bs
        (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)) ∧
      Terms.RecAt
        (fun D' t b => ∀ ϖ' H'', H'.Extends H'' → ∀ {m' : Nat} (g' : TargetRen m' Γ.length)
          (E'' : List Nat), (∀ x : Fin Γ.length, E''[(g' x : Nat)]? = E[(x : Nat)]?) →
          ∃ v H₂ tr, EvalRec P ϖ' H'' E'' r.run ϱ ((us.erase sig Mode.oneOne.erased hΓ r
            (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
            ((sig.caseFieldParams D qs ps).getD [])).rename g') b v H₂ tr ∧ H''.Extends H₂ ∧
          ∀ b₁, (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ)).block
            D' = some b₁ →
            RunsAs sig ι P H₂ ((Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ)
              (us.subst σ) D').subst₀ (Subst₀.single t)) v (b₁.motive.subst₀ (Subst₀.single t)))
        (fun ν A t b => ∀ (σ' : Shape) (π χ'' : Grade) (e A' : Term 0 [])
          (mr : Lifting.Result 0),
          A.shape ⟨κ.quality, r, ς⟩ (Signature.shapes ⟨κ.quality, r, ς⟩ .oneOne Grade.run sig)
            (sig.blockShapes decl.names qs ps χ') Nesting.plain ν = some ⟨.lifting σ', π, χ''⟩ →
          Term.NestedResult sig ⟨κ.quality, r, ς⟩
            (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ))
            (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ν A t e →
          Term.Lifts sig ⟨κ.quality, r, ς⟩
            (Lifting.ofMotives decl.names qs ls ps (as.subst σ) κ.level χ' (Cs.subst σ)) ν t A A'
            mr →
          (∃ vA R', Computesι sig ι A' vA ∧ HasRun sig ι P vA R') → ValidTerm₀ sig ι e A' →
          ∀ ϖ' H'' (c : Nat) (π' : Multiplicity), H'.Extends H'' →
          H''[c]? = some (.cell π' b) → ∀ {m' : Nat} (g' : TargetRen m' Γ.length)
          (E'' : List Nat), (∀ x : Fin Γ.length, E''[(g' x : Nat)]? = E[(x : Nat)]?) →
          ∃ w H₂ tr, Eval P ϖ' H'' (c :: E'') (Target.nested r.run ϱ σ'
            ((us.erase sig Mode.oneOne.erased hΓ r
              (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
              ((sig.caseFieldParams D qs ps).getD [])).rename g')) w H₂ tr ∧
            H''.Extends H₂ ∧ RunsAs sig ι P H₂ e w A')
        ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
        ((con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)).typesAt ts)
        (us.grades i) ts.terms bs) :
    ∃ v H₃ tr, EvalRec P ϖ₀ H' E' r.run ϱ ((us.erase sig Mode.oneOne.erased hΓ r
        (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ')
        ((sig.caseFieldParams D qs ps).getD [])).rename g) a v H₃ tr ∧
      H'.Extends H₃ ∧
      ∀ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ →
        RunsAs sig ι P H₃ (.recursor r ς χ' T'.name qs ls ps (as.subst σ) w κ (Cs.subst σ) (us.subst σ))
          v ((C'.subst (Subst.lift σ)).subst₀ (Subst₀.single w)) := by
  obtain ⟨hdecl, hT, rfl⟩ := id h
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hT' : T' ∈ decl.dataTypes := List.mem_of_getElem? hj
  have hasσ := has.2 σ σ hσ
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls ps (as.subst σ))
      (.inst D' qs ls ps (as.subst σ)) := fun _ => (Whnf.inst ..).computes
  -- The equality of the block at the arguments substituted.
  obtain ⟨SM, hUM, hval, hmonoM, hrecM, hNM, hiffM⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
  -- The meaning of the constructor gives the arguments of its fields.
  obtain ⟨qs', ls', ps', Δ', as', rfl⟩ := hw
  obtain ⟨v', w₁, w₂, R', hv', hw₁, -, hR', hrel⟩ :=
    hwv.2.1 (Computesι.not_computesToProp hd (hI _) (levelRel_univ_iff.2 (hUM T' hT').1))
  cases Computesι.det hd (hI _) hv'
  cases Computesι.det hd hw₁ (Whnf.ctor ..).computes
  have hrel' := (HasEq.unique hd hR' (.univ _ (levelRel_univ_iff.2 (hUM T' hT').1)) _ _).1 hrel
  obtain ⟨T'', hT'', hn'', con'', hcon'', fs₁, fs₂, hv₁, -, hS''⟩ :=
    DataType.blockRel_inv hmonoM hrel'
  cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup hnd) hT'' hT' hn''
  obtain ⟨-, hcn, rfl⟩ := hv₁.inj ⟨_, _, _, _, _, rfl⟩
  cases List.eq_of_nodup_map (hd.constructors_nodup ⟨hdecl, hT', rfl⟩) hcon'' hcon hcn
  have hself := (hiffM T' hT' con hcon).2.2 _ _ hS''
  obtain ⟨ts, -, rfl, -, -⟩ := (hiffM T' hT' con hcon).2.1 _ _ hself
  have hts := ((hiffM T' hT' con hcon).1 ts ts).1 hself
  have hrecV : Terms.RecRel (fun D t _ => ValidTerm₀ sig ι t (.inst D qs ls ps (as.subst σ)))
      ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ts.terms ts.terms :=
    Terms.RecRel.mono _ (fun D hD t₁ t₂ h₁₂ => by
        obtain ⟨T₃, hT₃, rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.mem_recursion hD)
        have h' := hval T₃ hT₃ t₁ t₂ h₁₂
        exact h'.trans h'.symm)
      (hrecM _ T' hT' con hcon _ _ hself)
  obtain ⟨hfa, hQ⟩ := hfr ts rfl hts hrecV
  -- The case of the constructor, its branch and its recursive results, those of the typing.
  obtain ⟨u, hu⟩ := hus i j T' con hi
  have hRt := hRs i j T' con hi
  have hρ := Lifting.ofMotives_substitutes σ decl.names qs ls ps as κ.level χ' Cs
  obtain ⟨rs, hrs⟩ := Constructor.ResultTypes.exists_resultTerms hd hord (fun _ => rfl)
    (fun _ => rfl) (hRt.subst hρ)
    (Term.recursorAt r ς χ' qs ls ps (as.subst σ) κ (Cs.subst σ) (us.subst σ)) ts
  have hθ : EqSubst sig ι (ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
      (Subst.append σ ts.toSubst) (Subst.append σ ts.toSubst) :=
    (EqSubst.append_append_iff ctx _ σ σ _ _).2 ⟨hσ, by rw [Constructor.fieldsAt_subst]; exact hts⟩
  -- The recursive results are equal arguments of their types: the recursor on a recursive field
  -- and the result of a nested field.
  have hEq := EqSubst.constructorResultTerms hd hord
    (L := fun D' => (.inst D' qs ls ps (as.subst σ),
      (DataType.blockRel decl.dataTypes SM D').computed sig ι))
    (fun D' b hb a₁ a₂ ha₁₂ => by
      obtain ⟨hD', C, hC, rfl⟩ := Lifting.ofMotives_block_inv hb
      obtain ⟨j₃, T₃, C₃, hj₃, rfl, hC₃, rfl⟩ := Motives.get_subst_idxOf hT hnd hCs σ hD' hC
      rw [Term.recursorAt_subst₀, Term.recursorAt_subst₀]
      exact hrec j₃ T₃ C₃ hj₃ hC₃ σ hσ a₁ a₂ (hval T₃ (List.mem_of_getElem? hj₃) a₁ a₂ ha₁₂))
    (fun D' a a' b b' h => by
      rcases h with h | ⟨ha, hb⟩
      · cases h
      · exact ⟨fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).1 hv, (hb w).1 hw, hx⟩,
          fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).2 hv, (hb w).2 hw, hx⟩⟩)
    hRt hρ (hctx i j T' con hi) hθ (hNM _ T' hT' con hcon _ _ hself) hrs hrs
  obtain ⟨gs₀, hgs, hget⟩ := Branches.get_erase sig Mode.oneOne.erased hΓ r us
    (sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ') ((sig.caseFieldParams T.name qs ps).getD [])
    hu
  -- The recursive results that the erasure reads, those of the fields of the constructor.
  have hws : ((sig.recursiveResults T.name qs ps ⟨κ.quality, r, ς⟩ χ').drop i).headD [] =
      con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ' (.ofLists qs ps hq hp) := by
    rw [hd.recursiveResults ⟨hdecl, hT, rfl⟩ hq hp, TypeDeclaration.recursiveResults]
    exact List.headD_drop (by rw [List.getElem?_map, hi]; rfl)
  rw [hws] at hget
  rw [hgs] at hQ
  have hfac := Constructor.ResultTypes.factors_recursiveResults hd hord hRt
  have hfac' : ∀ (j : Nat) (w : RecursiveResult), ((Telescope.nestPositions
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) 0).map fun l =>
        RecursiveResult.ofField ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l)
          (con.nestedShapes sig ⟨κ.quality, r, ς⟩ .oneOne Grade.run decl.names qs ps χ'
            (.ofLists qs ps hq hp))[l]?.join l)[j]? = some w →
      ∃ π : Grade, (πs i)[j]? = some π ∧ w.factor = π.run := by
    rw [← Constructor.recursiveResults_eq_map]
    exact hfac
  -- The types of the fields, which `θ` gives the types of the fields at the terms.
  have hAs : ((con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as).types.subst
      (Subst.append σ ts.toSubst)) =
      (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) (as.subst σ)).typesAt ts :=
    (Telescope.types_subst_append σ _ ts).trans
      (congrArg (Telescope.typesAt · ts) (Constructor.fieldsAt_subst con _ _ as σ))
  have hxs := Args.bound_terms_subst_append (Γ := Γ) σ ts
  have hrs' := hrs
  unfold Constructor.ResultTerms at hrs'
  rw [← hAs, ← hxs] at hrs'
  rw [← hAs, ← hxs] at hQ
  obtain ⟨vs, H₂, tr₁, hevs, hH₂, hruns⟩ := Args.evalResults hd (h := hRt)
    (f := (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names)
    (s := fun l => (con.nestedShapes sig ⟨κ.quality, r, ς⟩ .oneOne Grade.run decl.names qs ps χ'
      (.ofLists qs ps hq hp))[l]?.join)
    (lookup := Signature.shapes ⟨κ.quality, r, ς⟩ .oneOne Grade.run sig)
    (block := sig.blockShapes decl.names qs ps χ')
    (hρ.appendArgs ts) 0 bs List.drop_zero
    (RunsAsArgs.length hfa) gs₀.toList
    gs₀.length_toList
    (fun l D' hl => by
      rw [Nat.zero_add]
      unfold Telescope.recursionAt
      rw [Telescope.recursion_eq_map_nest, List.getElem?_map, hl]
      rfl)
    (fun l ms hl => by
      rw [Nat.zero_add]
      unfold Telescope.recursionAt
      rw [Telescope.recursion_eq_map_nest, List.getElem?_map, hl]
      rfl)
    (fun l ms A hn hA => by
      rw [Nat.zero_add]
      rw [hAs] at hA
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1
        (Telescope.mem_nestPositions.2 ⟨_, hn, rfl⟩ : 0 + l ∈ _)
      rw [Nat.zero_add] at hj'
      obtain ⟨σ', hσ'⟩ := hRt.nestedShapes_isSome (md := .oneOne) (ax := Grade.run) hd hord hj' hn
      obtain ⟨π, χ'', hsh⟩ := (Constructor.nestedShapes_shape (ls.getFin hl) (as.subst σ) ts hA hn
        σ').1 hσ'
      exact ⟨σ', π, χ'', by rw [hσ']; rfl, hsh⟩)
    hrs' hEq (hsorts i j T' con hi _ hθ) hQ ϖ₀ H' (List.prefix_refl _) g E' hgE
  -- The branch, at the substitution of its context by `σ`, the fields and the results.
  have hEqbr := (EqSubst.append_append_iff _ (Rs con) _ _ _ _).2 ⟨hθ, hEq⟩
  have hχi : RunsAsSubst sig ι P H₂ ctx (δs i) σ V :=
    RunsAsSubst.of_counted ctx (fun x hδ => (by decide : ∀ c d x : Grade,
        c ≤ d + x → d ∉ Mode.oneOne.erased → c ∉ Mode.oneOne.erased) _ _ _
        (hχ i j T' con hi x) hδ) (hE.mono hd (hH'.trans hH₂))
  have hfa₂ : RunsAsArgs sig ι P H₂ (gs i) ts bs
      ((con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as).subst σ) := by
    rw [Constructor.fieldsAt_subst]
    exact hfa.mono hd hH₂
  have hσr := RunsAsSubst.append _ (Rs con) (RunsAsSubst.append ctx _ hχi hfa₂) hruns
  obtain ⟨C', hC'⟩ : ∃ C' : Term 0 (.var :: Γ), Cs.get j = some ⟨0, C'⟩ := hCs j T' hj
  have hbr := husr i j T' con C' u hi hC' hu
  rw [hgs, GradeVector.extendResults_resultGrades] at hbr
  -- The branch binds its variables to cells, at the multiplicities of its binders.
  let ws := con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ' (.ofLists qs ps hq hp)
  let πs₀ : Fin (con.params (.ofLists qs ps hq hp)).length → Multiplicity := fun l =>
    r.fieldMultiplicity
      (((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?.map (·.usage))
      ((ws.zip gs₀.toList).find? fun x => x.1.fieldPosition == some (l : Nat))
  let πs₀' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length → Multiplicity :=
    fun j => gs₀[j].run
  have hlen : ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)).length = (bs ++ vs).length := by
    simp only [List.length_map, List.length_append, List.length_ofFn, RunsAsArgs.length hfa,
      RunsAsArgs.length hruns]
  let H₂' := H₂.bind ((List.ofFn πs₀ ++ List.ofFn πs₀').map (ϖ₀ * ·)) (bs ++ vs)
  have hH₂' : H₂.Extends H₂' := List.prefix_append _ _
  have hB : H₂'.Binds ((List.range' H₂.length (bs ++ vs).length).reverse ++ E)
      (vs.reverse ++ (bs.reverse ++ V)) := by
    have h' := (Heap.binds_bind H₂ hlen).reverse.append (hEV.mono (hH'.trans (hH₂.trans hH₂')))
    rwa [List.reverse_append, List.append_assoc] at h'
  -- The renamed branch runs in the environment `E'` extended by the cells of its variables, which
  -- binds its renamed scope as the environment of the branch binds it.
  have hL : ((List.range' H₂.length (bs ++ vs).length).reverse).length =
      (con.params (.ofLists qs ps hq hp)).length +
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length := by
    simp only [List.length_reverse, List.length_range', List.length_append, RunsAsArgs.length hfa,
      RunsAsArgs.length hruns]
  obtain ⟨v, H₃, tr₂, hev, hH₃, hrun⟩ := hbr ϖ₀ _ H₂' _ _ hEqbr hB (hσr.mono hd hH₂')
    (fun x => g.lift _ (Fin.cast (Scope.length_extend_extend Γ _ _) x))
    ((List.range' H₂.length (bs ++ vs).length).reverse ++ E')
    (fun x => TargetRen.getElem?_lift hgE _ hL _)
  rw [← Target.rename_cast] at hev
  -- The erased recursor steps to the erased branch.
  have hks : List.ofFn
      (fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else (ws[(j : Nat)]?).getD .erased) =
      List.zipWith (fun e w => if e ∈ Mode.oneOne.erased then RecursiveResult.erased else w)
        gs₀.toList ((Telescope.nestPositions ((con.fields (.ofLists qs ps hq hp)).nest
          decl.names) 0).map fun l => RecursiveResult.ofField
            ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l)
            (con.nestedShapes sig ⟨κ.quality, r, ς⟩ .oneOne Grade.run decl.names qs ps χ'
              (.ofLists qs ps hq hp))[l]?.join l) := by
    rw [← Constructor.recursiveResults_eq_map]
    exact List.ofFn_ite_getElem? (· ∈ Mode.oneOne.erased) _ (Option.getD · .erased) gs₀ ws
      (Constructor.length_recursiveResults _ _ _ _ _ _ _ _)
  have hπs' : List.ofFn πs₀' = gs₀.toList.map Grade.run := by
    apply List.ext_getElem <;> simp [πs₀']
  rw [← hπs'] at hevs
  -- The parameter of each field, which the signature gives the case.
  have hfs : ∀ (l : Nat) (p' : Parameter), (con.params (.ofLists qs ps hq hp))[l]? = some p' →
      ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[l]? = some p' :=
    fun l p' hp' => by
      rw [hd.caseFieldParams ⟨hdecl, hT, rfl⟩ hq hp, Option.getD_some,
        List.headD_drop (by rw [List.getElem?_map, hi]; rfl), hp']
  -- The uses of each field by the branch are within those that the constructor allows: by its
  -- variable and by the recursions of the recursive results on it.
  have hπ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length,
      ∃ π₀, πv[(l : Nat)]? = some π₀ ∧ r.run * π₀ ≤ πs₀ l + r.run * recursionsAt
      (List.ofFn fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
        if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else (ws[(j : Nat)]?).getD .erased)
      (List.ofFn πs₀') l := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, hπ₀, hle⟩ := hπv l p' hp'
    refine ⟨π₀, hπ₀, ?_⟩
    have hgl := hg i j T' con l p' hi hp'
    rw [hgs] at hgl
    have he := Grade.fieldMultiplicity_results r p'.usage con (.ofLists qs ps hq hp)
      gs₀.toList (πs i) hfac l
    have hr := Telescope.recursionsAt_results Mode.oneOne.erased
      (fun e => (Mode.erased_values.1 e).1) _ _
      ((con.fields (.ofLists qs ps hq hp)).nest decl.names) 0 gs₀.toList (πs i) hfac' l
    rw [Nat.zero_add] at hr
    rw [hks, hπs', hr]
    simp only [πs₀, ws, hfs l p' hp', Option.map_some, he]
    exact Grade.run_mul_le_fieldMultiplicity π₀ r p'.usage _ _ hle hgl
  -- The coefficient of the ownership of each field is within the one that the constructor
  -- allows.
  have hκ : ∀ l : Fin (con.params (.ofLists qs ps hq hp)).length, ∃ π₀ ϱ₀,
      πv[(l : Nat)]? = some π₀ ∧ ϱv[(l : Nat)]? = some ϱ₀ ∧
      r.fieldCoefficient ((((sig.caseFieldParams T.name qs ps).getD []).drop i).headD [])[(l : Nat)]?
        ≤ ϱ₀ * (r.run * π₀) := by
    intro l
    obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
      ⟨_, List.getElem?_eq_getElem l.2⟩
    obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hκv l p' hp'
    refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
    rw [hfs l p' hp']
    exact hle
  -- The requirement of the recursion is within the requirement times the uses of each field on
  -- which a recursive result recurses by the recursor: such a field is recursive and has
  -- recursions, so that the constructor allows uses of it unless the grade of the recursor has
  -- none at run time.
  have hϱ : ∀ (j' : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) (l : Nat),
      (if gs₀[j'] ∈ Mode.oneOne.erased then RecursiveResult.erased
        else (ws[(j' : Nat)]?).getD .erased) = .field l →
        ∃ π₀ ϱ₀, πv[l]? = some π₀ ∧ ϱv[l]? = some ϱ₀ ∧ ϱ ≤ ϱ₀ * (r.run * π₀) := by
    intro j' l hl
    have hl₀ := hl
    split at hl
    · cases hl
    · rename_i hg'
      obtain ⟨w', hw', rfl⟩ : ∃ w', ws[(j' : Nat)]? = some w' ∧ w' = .field l := by
        cases hw : ws[(j' : Nat)]? with
        | none => rw [hw] at hl; cases hl
        | some w' => rw [hw] at hl; exact ⟨w', rfl, hl⟩
      rw [Constructor.getElem?_recursiveResults] at hw'
      obtain ⟨l', hl', he'⟩ := Option.map_eq_some_iff.1 hw'
      obtain ⟨rfl, hrec'⟩ := RecursiveResult.ofField_eq_field.1 he'
      obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.1 hrec'
      obtain ⟨π₀, ϱ₀, hπ₀, hϱ₀, hle⟩ := hϱv l D' hD'
      refine ⟨π₀, ϱ₀, hπ₀, hϱ₀, ?_⟩
      have hlt : l < (con.params (.ofLists qs ps hq hp)).length := by
        rw [← Telescope.length_recursion decl.names (con.fields (.ofLists qs ps hq hp))]
        have : ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)[l]?.isSome := by
          unfold Telescope.recursionAt at hD'
          cases hx : ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)[l]? with
          | none => rw [hx] at hD'; cases hD'
          | some _ => rfl
        obtain ⟨_, hx⟩ := Option.isSome_iff_exists.1 this
        exact (List.getElem?_eq_some_iff.1 hx).1
      obtain ⟨π₁, hπ₁, hle₁⟩ := hπ ⟨l, hlt⟩
      cases hπ₀.symm.trans hπ₁
      have hne := recursionsAt_ne_zero (l := l) (k := .field l) (π := πs₀' j') rfl
        ((by decide : ∀ g : Grade, g ∉ Mode.oneOne.erased → g.run * .one ≠ .zero) _ hg')
        (ks := List.ofFn
          fun j : Fin (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length =>
          if gs₀[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
          else (ws[(j : Nat)]?).getD .erased)
        (πs := List.ofFn πs₀') (j := j')
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]; exact congrArg some hl₀)
        (by rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn])
      by_cases hz : r.run * π₀ = .zero
      · rw [hϱ0 ((by decide : ∀ ρ π₀ π x : Multiplicity, ρ * π₀ ≤ π + ρ * x → x ≠ .zero →
          ρ * π₀ = .zero → ρ = .zero) _ _ _ _ hle₁ hne hz)]
        exact (by decide : ∀ x : Multiplicity, .omega ≤ x) _
      · exact hle hz
  refine ⟨v, H₃, tr₁ ++ tr₂, .iota ha (by rw [TargetBranches.get_rename, hget]; rfl)
    (RunsAsArgs.length hfa) hπ hκ hϱ (hks ▸ hevs) hev, hH₂.trans (hH₂'.trans hH₃),
    fun C'' hC'' => ?_⟩
  rw [hC'] at hC''
  cases hC''
  -- The recursor on the constructor steps to the branch, at the motive at the constructor.
  rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hrun
  have hrun₁ := (RunsAs.redStar_iff hd
    (.step (Red.iota_subst (D' := T'.name) (qs'' := qs') (ls'' := ls') (ps'' := ps') (as := as')
      ⟨hdecl, hT', rfl⟩ hi σ hq hl hp ts hu hrs) (.refl _))).2 hrun
  have hca : ValidEqTerm₀ sig ι
      (.ctor T'.name qs ls ps (as.subst σ) con.name ts.terms)
      (.ctor T'.name qs' ls' ps' as' con.name ts.terms) (.inst T'.name qs ls ps (as.subst σ)) :=
    hval T' hT' _ _ ⟨_, _, (Whnf.ctor ..).computes, (Whnf.ctor ..).computes,
      DataType.blockRel_closed hmonoM hT' ⟨con, hcon, ts.terms, ts.terms, ⟨_, _, _, _, _, rfl⟩,
        ⟨_, _, _, _, _, rfl⟩, hself⟩⟩
  have hmot := (hCv j T' C' hj hC').motive hσ hca
  have hrw := hrec j T' C' hj hC' σ hσ _ _ hwv
  exact hrun₁.conv hd (hrw.conv hmot.symm).2 hmot.2

end

end Sic.Core
