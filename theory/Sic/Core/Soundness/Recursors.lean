module

public import Sic.Core.Lifting.Extension
public import Sic.Core.Soundness.DeclaredTypes
public import Sic.Core.Soundness.Signature
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Results.Existence
import Sic.Core.Results.Extension
import Sic.Core.Results.Substitution
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Recursors.Results
import Sic.Core.Soundness.Rules
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Soundness of the Rules of the Recursors

The rules `(rec)`, `(rec_≡)`, `(ι)` and `(η_c)` of annex 15 of RFC 36 keep the meaning of annex 21,
as `Rules` proves it of the other rules, from the meaning of the data types.

ADE prove the validity of the rules of their eliminators in
`Definition/LogicalRelation/Substitution/Introductions/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Recursors

A recursor on two equal closed terms of an instance of a data type of a meaningful declaration
computes, by the reduction of their terms, then by `(ι_⟶)`, to the branches of the constructor that
both compute to, at the terms of their fields, which the equality of the instance relates; the
branches at equal substitutions of the fields are equal terms of the motive at the constructor,
which the motive makes equal to the motive at the term.
On a proposition, whose proofs need not compute, the truth of the instance gives a constructor with
terms of its fields, whose branch is a proof of the motive, then a proposition, at the constructor:
the motive is then true at the term, and the recursors are equal proofs of it. -/

/-- `(ι_⟶)` steps a recursor whose branches are substituted by `σ`, on a constructor of a declared
type of `Σ` applied to the terms of closed arguments of its fields, to the branch of the
constructor substituted by `σ` followed by the arguments and by their recursive results. -/
theorem Red.iota_subst {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {i j : Nat} (hi : decl.cases[i]? = some (j, T, con))
    {Γ : Scope} (σ : Subst 0 [] Γ) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (ts : Args 0 [] (con.params (.ofLists qs ps hq hp))) {us : Branches 0 Γ} {ps' : List Parameter}
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend ps'.length)}
    (hu : us.get i = some ⟨_, _, u⟩) {r ς χ : Grade} {κ : Universe 0} {D' : Name}
    {qs'' : List Quality} {ls'' : List (Level 0)} {ps'' : List Grade} {Δ : Scope}
    {as : InstanceArgs 0 [] Δ} {as' : InstanceArgs 0 [] decl.scope} {Cs : Motives 0 []}
    {rs : Args 0 [] ps'}
    (hrs : Constructor.ResultTerms sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names (ls.getFin hl) as'
      (Lifting.ofMotives decl.names qs ls ps as' κ.level χ Cs)
      (Term.recursorAt r ς χ qs ls ps as' κ Cs (us.subst σ)) ts rs) :
    Red (sig.interpret ι) (.recursor r ς χ D' qs ls ps as' (.ctor D qs'' ls'' ps'' as con.name ts.terms) κ
      Cs (us.subst σ)) (u.subst (Subst.append (Subst.append σ ts.toSubst) rs.toSubst)) :=
  .iota (List.mem_map_of_mem (f := Entry.interpret ι) h.1) hi h.2.2 rfl hq hl hp
    (Branches.get_subst σ hu)
    (Terms.ResultTerms.ofTypeDeclarations
      (fun _ hdecl => List.mem_map_of_mem (f := Entry.interpret ι) hdecl) hrs)
    (Term.instantiateTerms₂_subst_append σ u ts rs)

/-- `(ι_⟶)` steps a recursor whose branches are substituted by `σ`, on a constructor none of whose
fields has a position applied to the terms of closed arguments of its fields, to the branch of the
constructor substituted by `σ` followed by the arguments. -/
theorem Red.iota_subst₀ {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {i j : Nat} (hi : decl.cases[i]? = some (j, T, con))
    {Γ : Scope} (σ : Subst 0 [] Γ) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (ts : Args 0 [] (con.params (.ofLists qs ps hq hp))) {us : Branches 0 Γ}
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend 0)}
    (hu : us.get i = some ⟨_, 0, u⟩)
    (h0 : ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ν = .plain)
    {r ς χ : Grade} {κ : Universe 0} {D' : Name} {qs'' : List Quality} {ls'' : List (Level 0)}
    {ps'' : List Grade} {Δ : Scope} {as : InstanceArgs 0 [] Δ}
    {as' : InstanceArgs 0 [] decl.scope} {Cs : Motives 0 []} :
    Red (sig.interpret ι) (.recursor r ς χ D' qs ls ps as' (.ctor D qs'' ls'' ps'' as con.name ts.terms) κ
      Cs (us.subst σ)) (u.subst (Subst.append σ ts.toSubst)) :=
  Red.iota_plain (List.mem_map_of_mem (f := Entry.interpret ι) h.1) hi h.2.2 rfl hq hl hp h0 ts rfl
    (Branches.get_subst σ hu)
    ((Term.instantiateTerms_terms _ ts).trans
      (congrArg some ((Term.instantiate_eq_subst _ ts).trans (Term.subst_append σ _ u))))

/-- `C[T.c(x̄) / z][σ, t̄ / x̄] = C[σ⇑][T[σ].c(t̄) / z]`: the motive at a constructor, substituted by
`σ` followed by closed arguments of its fields, is the motive substituted by `σ` at the constructor
of the instance substituted, applied to the arguments. -/
theorem Term.atCtor_subst_append {Γ Δ : Scope} (σ : Subst 0 [] Γ) (C : Term 0 (.var :: Γ))
    (D : Name) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 Γ Δ)
    (c : Name) {fs : List Parameter} (ts : Args 0 [] fs) :
    (C.atCtor D qs ls ps as c fs).subst (Subst.append σ ts.toSubst) =
      (C.subst (Subst.lift σ)).subst₀ (Subst₀.single (.ctor D qs ls ps (as.subst σ) c ts.terms)) := by
  rw [← Term.subst_append, Term.atCtor_subst, ← Term.instantiate_eq_subst, Term.atCtor_instantiate]

/-- A motive of a sort, meaningful over a term of an instance, gives equal types at equal
substitutions and equal terms of the instance. -/
theorem ValidTermΓ.motive {Γ : Scope} {ctx : Context 0 Γ} {A : Term 0 Γ} {C : Term 0 (.var :: Γ)}
    {κ : Universe 0} (hC : ValidTermΓ sig ι (ctx.var A) C (.sort κ)) {σ₁ σ₂ : Subst 0 [] Γ}
    {a₁ a₂ : Term 0 []} (hσ : EqSubst sig ι ctx σ₁ σ₂) (ha : ValidEqTerm₀ sig ι a₁ a₂ (A.subst σ₁)) :
    ValidEqType₀ sig ι ((C.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a₁))
      ((C.subst (Subst.lift σ₂)).subst₀ (Subst₀.single a₂)) := by
  rw [Term.subst_lift_single, Term.subst_lift_single]
  have hC' := hC.2 _ _ ((EqSubst.var_iff ctx A (Subst.append (n := 1) σ₁ (Subst.closedSingle a₁))
    (Subst.append (n := 1) σ₂ (Subst.closedSingle a₂))).2 ⟨hσ, ha⟩)
  obtain ⟨s, l⟩ := κ
  cases s
  · exact ValidEqTerm₀.univType hC'
  · exact ValidEqTerm₀.propType hC'

/-- A motive of a universe of propositions, meaningful over a term of an instance, is a proposition
at a substitution and a term of the instance. -/
theorem ValidTermΓ.motive_prop {Γ : Scope} {ctx : Context 0 Γ} {A : Term 0 Γ}
    {C : Term 0 (.var :: Γ)} {l : Level 0} (hC : ValidTermΓ sig ι (ctx.var A) C (.sort ⟨.prop, l⟩))
    {σ : Subst 0 [] Γ} {a : Term 0 []} (hσ : EqSubst sig ι ctx σ σ)
    (ha : ValidEqTerm₀ sig ι a a (A.subst σ)) :
    ComputesToProp sig ι ((C.subst (Subst.lift σ)).subst₀ (Subst₀.single a)) := by
  rw [Term.subst_lift_single]
  have hC' := hC.2 _ _ ((EqSubst.var_iff ctx A (Subst.append (n := 1) σ (Subst.closedSingle a))
    (Subst.append (n := 1) σ (Subst.closedSingle a))).2 ⟨hσ, ha⟩)
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, -, hR, hw⟩ := hC'.2.1 not_computesToProp_sort
  cases hc.sort_inv
  exact ⟨w₁, hw₁, HasEq.prop_isProp hR hw⟩

/-- Relations at the recursive fields grow with the relations. -/
theorem Terms.RecRel.mono {Q Q' : Name → TermRel} :
    (rs : List (Option Name)) → {ts₁ ts₂ : Terms 0 []} →
      (∀ D, some D ∈ rs → ∀ t₁ t₂, Q D t₁ t₂ → Q' D t₁ t₂) → Terms.RecRel Q rs ts₁ ts₂ →
        Terms.RecRel Q' rs ts₁ ts₂
  | some D :: rs, .cons _ _, .cons _ _, h, hqs => by
    simp only [Terms.RecRel] at hqs ⊢
    exact ⟨h D (List.mem_cons_self ..) _ _ hqs.1,
      Terms.RecRel.mono rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hqs.2⟩
  | none :: rs, .cons _ _, .cons _ _, h, hs =>
    Terms.RecRel.mono rs (fun D hD => h D (List.mem_cons_of_mem _ hD)) hs
  | [], _, _, _, _ | some _ :: _, .nil, _, _, _ | none :: _, .nil, _, _, _
  | some _ :: _, .cons _ _, .nil, _, _ | none :: _, .cons _ _, .nil, _, _ => trivial

/-- Two terms equal in a type that computes to a proposition make it true, so that any two terms are
equal in it. -/
theorem ValidEqTerm₀.prop_any (hd : sig.Distinct) {t u t' u' A : Term 0 []}
    (h : ValidEqTerm₀ sig ι t u A) (hA : ComputesToProp sig ι A) : ValidEqTerm₀ sig ι t' u' A := by
  obtain ⟨w, R, hw, hR, hrel⟩ := h.2.2 hA
  exact ⟨h.1, fun hn => absurd hA hn, fun _ => ⟨w, R, hw, hR, hR.prop_any hd (hA.isProp hd hw) hrel⟩⟩

/-- `(rec_≡)` at closed terms, for each type of the block: at equal substitutions `σ₁` and `σ₂` of the
context, the recursors on equal closed terms `t₁` and `t₂` of the instance of a type `T` of the
block are equal terms of its motive at `t₁`, the motive and the branches substituted, by induction
on `(eq_μ)` or on `(true_μ)`, which relate the terms of all the types of the block together: the
statement for the type of the term of `(rec_≡)`, and for the other types, which the recursors on
their recursive fields reach. -/
theorem ValidEqTerm₀.recursor_block {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) (hord : sig.LiftsInOrder) {decl : TypeDeclaration} {D : Name}
    {T₀ : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T₀) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    {r ς χ : Grade} {Cs₁ Cs₂ : Motives 0 Γ}
    {us₁ us₂ : Branches 0 Γ} {κ : Universe 0} {as₁' : InstanceArgs 0 Γ decl.scope}
    (hctx : ValidCtx₀ sig ι ctx)
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₁'
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs₁.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs₁.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls₁ ps as₁)) C' (.sort κ))
    (hus₁ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hus₂ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    {Rs₁ Rs₂ : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
      Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
    (hRs₁ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls₁.getFin hl₁) as₁ (Lifting.ofMotives decl.names qs ls₁ ps as₁ κ.level χ Cs₁)
        (Rs₁ con) πs)
    (hRs₂ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls₂.getFin hl₂) as₂ (Lifting.ofMotives decl.names qs ls₂ ps as₂ κ.level χ Cs₂)
        (Rs₂ con) πs)
    (hut : ∀ i j T' con C' u₁ u₂, decl.cases[i]? = some (j, T', con) →
      Cs₁.get j = some ⟨0, C'⟩ →
      us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
      us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
      ValidEqTermΓ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)).append (Rs₁ con))
        u₁ u₂
        ((C'.atCtor T'.name qs ls₁ ps as₁ con.name (con.params (.ofLists qs ps hq hp))).rename
          (Ren.weakenN _)))
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop)
    {σ₁ σ₂ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ₁ σ₂) {h' : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} {C₁ : Term 0 (.var :: Γ)}
    (hh : decl.dataTypes[h']? = some T) (hC : Cs₁.get h' = some ⟨0, C₁⟩) {t₁ t₂ : Term 0 []}
    (ht' : ValidEqTerm₀ sig ι t₁ t₂ (.inst T.name qs ls₁ ps (as₁.subst σ₁))) :
    ValidEqTerm₀ sig ι
      (.recursor r ς χ T.name qs ls₁ ps (as₁.subst σ₁) t₁ κ (Cs₁.subst σ₁) (us₁.subst σ₁))
      (.recursor r ς χ T.name qs ls₂ ps (as₂.subst σ₂) t₂ κ (Cs₂.subst σ₂) (us₂.subst σ₂))
      ((C₁.subst (Subst.lift σ₁)).subst₀ (Subst₀.single t₁)) := by
  obtain ⟨hsig, hv⟩ := hent.hasDataType h
  obtain ⟨hdecl, -, -⟩ := id hsig
  have hT : T ∈ decl.dataTypes := List.mem_of_getElem? hh
  have hd := hctx.distinct
  have hnd : decl.names.Nodup := hd.nodup hdecl
  have hCv₀ := hCv h' T C₁ hh hC
  have hidx : ∀ j T', decl.dataTypes[j]? = some T' → decl.names.idxOf T'.name = j :=
    fun _ _ hj => TypeDeclaration.idxOf_dataTypes hnd hj
  have hCsN : ∀ D' ∈ decl.names, ∃ C, Cs₁.get (decl.names.idxOf D') = some ⟨0, C⟩ :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
      rw [hidx j T' hj]
      exact hCs j T' hj
  -- The motive of a type of the block in the motives substituted is its motive, substituted.
  have hK : ∀ τ : Subst 0 [] Γ, ∀ D' ∈ decl.names, ∀ C,
      (Cs₁.subst τ).get (decl.names.idxOf D') = some ⟨0, C⟩ → ∃ j T' C',
        decl.dataTypes[j]? = some T' ∧ T'.name = D' ∧ Cs₁.get j = some ⟨0, C'⟩ ∧
          C = C'.subst (Subst.lift τ) := by
    intro τ D' hD' C hC'
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
    obtain ⟨C', hC''⟩ := hCs j T' hj
    rw [hidx j T' hj, Motives.get_subst τ hC''] at hC'
    cases hC'
    exact ⟨j, T', C', hj, rfl, hC'', rfl⟩
  -- The branches of a constructor, at equal substitutions of the context, at equal arguments of its
  -- fields, related at the fields whose nestings have a position by relations whose terms have
  -- recursive results equal in their motives, are equal terms of the motive at the constructor, and
  -- the recursors on the constructor step to them.
  have hbranch : ∀ τ₁ τ₂ : Subst 0 [] Γ, EqSubst sig ι ctx τ₁ τ₂ → ∀ T' ∈ decl.dataTypes,
      ∀ con ∈ T'.constructors, ∀ C' : Term 0 (.var :: Γ),
      Cs₁.get (decl.names.idxOf T'.name) = some ⟨0, C'⟩ →
      ∀ ts₁ ts₂ : Args 0 [] (con.params (.ofLists qs ps hq hp)),
      EqSubst sig ι (Context.empty.append
        ((con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁).subst τ₁)) ts₁.toSubst
        ts₂.toSubst →
      ∀ (n : Nat) (s : Quality) (L : Name → NestLeaf),
      (∀ D', ResultLeaf sig ι
        (Lifting.ofMotives decl.names qs ls₁ ps (as₁.subst τ₁) κ.level χ (Cs₁.subst τ₁))
        (Term.recursorAt r ς χ qs ls₁ ps (as₁.subst τ₁) κ (Cs₁.subst τ₁) (us₁.subst τ₁))
        (Term.recursorAt r ς χ qs ls₂ ps (as₂.subst τ₂) κ (Cs₂.subst τ₂) (us₂.subst τ₂)) D'
        (L D')) →
      (∀ D', LeafCongr sig ι s (L D').2) →
      Terms.NestedRel sig ι n s L ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
        (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) (as₁.subst τ₁)) ts₁.terms ts₂.terms →
      ∃ v₁ v₂, ValidEqTerm₀ sig ι v₁ v₂ ((C'.subst (Subst.lift τ₁)).subst₀
          (Subst₀.single (.ctor T'.name qs ls₁ ps (as₁.subst τ₁) con.name ts₁.terms))) ∧
        (∀ {qs'' : List Quality} {ls'' : List (Level 0)} {ps'' : List Grade} {Δ'' : Scope}
          {as'' : InstanceArgs 0 [] Δ''},
          Red (sig.interpret ι) (.recursor r ς χ T'.name qs ls₁ ps (as₁.subst τ₁)
            (.ctor T'.name qs'' ls'' ps'' as'' con.name ts₁.terms) κ (Cs₁.subst τ₁)
            (us₁.subst τ₁)) v₁) ∧
        (∀ {qs'' : List Quality} {ls'' : List (Level 0)} {ps'' : List Grade} {Δ'' : Scope}
          {as'' : InstanceArgs 0 [] Δ''},
          Red (sig.interpret ι) (.recursor r ς χ T'.name qs ls₂ ps (as₂.subst τ₂)
            (.ctor T'.name qs'' ls'' ps'' as'' con.name ts₂.terms) κ (Cs₂.subst τ₂)
            (us₂.subst τ₂)) v₂) := by
    intro τ₁ τ₂ hτ T' hT' con hcon C' hC' ts₁ ts₂ hts n s L hL hLc hN
    obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
    rw [hidx j T' hj] at hC'
    obtain ⟨u₁, hu₁⟩ := hus₁ i j T' con hi
    obtain ⟨u₂, hu₂⟩ := hus₂ i j T' con hi
    have hρ₁ := Lifting.ofMotives_substitutes τ₁ decl.names qs ls₁ ps as₁ κ.level χ Cs₁
    have hρ₂ := Lifting.ofMotives_substitutes τ₂ decl.names qs ls₂ ps as₂ κ.level χ Cs₂
    obtain ⟨πs₁, hR₁⟩ := hRs₁ i j T' con hi
    obtain ⟨rs₁, hrs₁⟩ := Constructor.ResultTypes.exists_resultTerms hd hord (fun _ => rfl)
      (fun _ => rfl) (hR₁.subst hρ₁)
      (Term.recursorAt r ς χ qs ls₁ ps (as₁.subst τ₁) κ (Cs₁.subst τ₁) (us₁.subst τ₁)) ts₁
    obtain ⟨πs₂, hR₂⟩ := hRs₂ i j T' con hi
    obtain ⟨rs₂, hrs₂⟩ := Constructor.ResultTypes.exists_resultTerms hd hord (fun _ => rfl)
      (fun _ => rfl) (hR₂.subst hρ₂)
      (Term.recursorAt r ς χ qs ls₂ ps (as₂.subst τ₂) κ (Cs₂.subst τ₂) (us₂.subst τ₂)) ts₂
    have hb := hut i j T' con C' u₁ u₂ hi hC' hu₁ hu₂
    have hfs := (EqSubst.append_append_iff ctx _ τ₁ τ₂ _ _).2 ⟨hτ, hts⟩
    have hres := EqSubst.constructorResultTerms hd hord
      hL hLc hR₁ hρ₁ hb.1.1 (hfs.left (ValidCtx₀.append_left hb.1.1)) hN hrs₁
      hrs₂
    have hb' := hb.2 _ _ ((EqSubst.append_append_iff _ (Rs₁ con) _ _ _ _).2 ⟨hfs, hres⟩)
    rw [Term.subst_append_rename_weakenN, Term.atCtor_subst_append] at hb'
    have hsig' : sig.HasDataType T'.name decl T' := ⟨hdecl, hT', rfl⟩
    exact ⟨_, _, hb', Red.iota_subst hsig' hi τ₁ hq hl₁ hp ts₁ hu₁ hrs₁,
      Red.iota_subst hsig' hi τ₂ hq hl₂ hp ts₂ hu₂ hrs₂⟩
  have hσ₁ := hσ.left hctx
  have hI : ∀ D', Computesι sig ι (.inst D' qs ls₁ ps (as₁.subst σ₁))
      (.inst D' qs ls₁ ps (as₁.subst σ₁)) := fun _ => (Whnf.inst ..).computes
  have hasσ := has.2 σ₁ σ₁ hσ₁
  have htσ : ValidEqTerm₀ sig ι t₁ t₁ (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
    ht'.trans ht'.symm
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · -- An instance in a universe: induction on `(eq_μ)`.
    obtain ⟨S, hU, hval, hmono, -, hnest, hiff⟩ := hv.univRel hd hdecl hq hl₁ hp hadm hasσ hs
    let X : Name → TermRel := fun D' a b => DataType.blockRel decl.dataTypes S D' a b ∧
      ∀ C' : Term 0 (.var :: Γ), Cs₁.get (decl.names.idxOf D') = some ⟨0, C'⟩ → ValidEqTerm₀ sig ι
        (.recursor r ς χ D' qs ls₁ ps (as₁.subst σ₁) a κ (Cs₁.subst σ₁) (us₁.subst σ₁))
        (.recursor r ς χ D' qs ls₂ ps (as₂.subst σ₂) b κ (Cs₂.subst σ₂) (us₂.subst σ₂))
        ((C'.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a))
    have hclosed : ∀ T' ∈ decl.dataTypes, ∀ a b, T'.ctorRel T'.name (S X) a b →
        X T'.name a b := by
      rintro T' hT' a b ⟨con, hcon, fs₁, fs₂, ⟨qs₁', ls₁', ps₁', Δ₁', as₁'', rfl⟩,
        ⟨qs₂', ls₂', ps₂', Δ₂', as₂'', rfl⟩, hS⟩
      have hSb := hmono X _ (fun _ _ _ h => h.1) T' hT' con hcon fs₁ fs₂ hS
      refine ⟨DataType.blockRel_closed hmono hT' ⟨con, hcon, fs₁, fs₂, ⟨_, _, _, _, _, rfl⟩,
        ⟨_, _, _, _, _, rfl⟩, hSb⟩, fun C' hC' => ?_⟩
      obtain ⟨ts₁, ts₂, rfl, rfl, hts⟩ := (hiff T' hT' con hcon).2.1 fs₁ fs₂ hSb
      have hQ : ∀ D', ResultLeaf sig ι
          (Lifting.ofMotives decl.names qs ls₁ ps (as₁.subst σ₁) κ.level χ (Cs₁.subst σ₁))
          (Term.recursorAt r ς χ qs ls₁ ps (as₁.subst σ₁) κ (Cs₁.subst σ₁) (us₁.subst σ₁))
          (Term.recursorAt r ς χ qs ls₂ ps (as₂.subst σ₂) κ (Cs₂.subst σ₂) (us₂.subst σ₂)) D'
          (.inst D' qs ls₁ ps (as₁.subst σ₁), (X D').computed sig ι) := by
        intro D' b hb a₁ a₂ hX
        obtain ⟨hD', C, hC, rfl⟩ := Lifting.ofMotives_block_inv hb
        rw [Term.recursorAt_subst₀, Term.recursorAt_subst₀]
        obtain ⟨j'', T'', C'', hj'', rfl, hC'', rfl⟩ := hK σ₁ D' hD' C hC
        obtain ⟨v', w', hv', hw', hXvw⟩ := hX
        have hT'' := List.mem_of_getElem? hj''
        have hP := hXvw.2 C'' ((hidx j'' T'' hj'').symm ▸ hC'')
        have hvt : ValidEqTerm₀ sig ι v' a₁ (.inst T''.name qs ls₁ ps (as₁.subst σ₁)) := by
          have h₁₂ := hval T'' hT'' a₁ a₂ ⟨v', w', hv', hw', hXvw.1⟩
          exact (ValidEqTerm₀.redStar_iff hd hv'.1).1 (h₁₂.trans h₁₂.symm)
        have hP' := hP.conv ((hCv j'' T'' C'' hj'' hC'').motive hσ₁ hvt)
        exact (ValidEqTerm₀.redStar_iff hd (RedStar.recursor hv'.1)).2
          ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw'.1)).2 hP'.symm).symm
      obtain ⟨v₁, v₂, hb, hr₁, hr₂⟩ := hbranch σ₁ σ₂ hσ T' hT' con hcon C' hC' ts₁ ts₂
        (by rw [Constructor.fieldsAt_subst]; exact hts) _ .type _ hQ
        (fun D' a a' b b' h => by
          rcases h with h | ⟨ha, hb⟩
          · cases h
          · exact ⟨fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).1 hv, (hb w).1 hw, hx⟩,
              fun ⟨v, w, hv, hw, hx⟩ => ⟨v, w, (ha v).2 hv, (hb w).2 hw, hx⟩⟩)
        (hnest X T' hT' con hcon _ _ hS)
      obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
      have hca : ValidEqTerm₀ sig ι (.ctor T'.name qs ls₁ ps (as₁.subst σ₁) con.name ts₁.terms)
          (.ctor T'.name qs₁' ls₁' ps₁' as₁'' con.name ts₁.terms)
          (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
        hval T' hT' _ _ ⟨_, _, (Whnf.ctor ..).computes, (Whnf.ctor ..).computes,
          DataType.blockRel_closed hmono hT' ⟨con, hcon, ts₁.terms, ts₁.terms,
            ⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, rfl⟩, (hiff T' hT' con hcon).2.2 _ _ hSb⟩⟩
      have hb' := hb.conv ((hCv j T' C' hj ((hidx j T' hj) ▸ hC')).motive hσ₁ hca)
      exact (ValidEqTerm₀.red_iff hd hr₁).2 ((ValidEqTerm₀.red_iff hd hr₂).2 hb'.symm).symm
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hnp := Computesι.not_computesToProp hd (hI _) hU'
    obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht'.2.1 hnp
    cases Computesι.det hd (hI _) hv'
    have hrel' := (HasEq.unique hd hR' (.univ _ hU') w₁ w₂).1 hrel
    have hP := (hrel' X hclosed).2 C₁ ((hidx h' T hh).symm ▸ hC)
    have hwt : ValidEqTerm₀ sig ι w₁ t₁ (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
      (ValidEqTerm₀.redStar_iff hd hw₁.1).1 htσ
    have hP' := hP.conv (hCv₀.motive hσ₁ hwt)
    exact (ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₁.1)).2
      ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₂.1)).2 hP'.symm).symm
  · -- A proposition: induction on `(true_μ)`.
    obtain ⟨S, hP, hmono, -, hnest, hiff⟩ := hv.propRel hd hdecl hq hl₁ hp hadm hasσ hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have hprop : ComputesToProp sig ι (.inst T.name qs ls₁ ps (as₁.subst σ₁)) :=
      ⟨_, hI _, _, _, hP'⟩
    obtain ⟨v', R', hv', hR', hrel⟩ := ht'.2.2 hprop
    cases Computesι.det hd (hI _) hv'
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      (HasEq.unique hd hR' (.prop _ _ hP' fun _ _ => .rfl) _ _).1 hrel
    obtain ⟨T₀, hT₀, -, con₀, hcon₀, -⟩ := DataType.blockTruth_inv hmono htrue
    obtain ⟨i₀, j₀, hi₀, -⟩ := TypeDeclaration.exists_cases hT₀ hcon₀
    obtain ⟨s, l⟩ := κ
    have hs' : s = .prop := hκ hs (List.ne_nil_of_mem (List.mem_of_getElem? hi₀))
    subst hs'
    have hvalP : ∀ T' ∈ decl.dataTypes, ∀ a,
        DataType.blockTruth decl.dataTypes S T'.name →
          ValidEqTerm₀ sig ι a a (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
      fun T' hT' _ hb => (FieldRel.prop (hP T' hT').1 :
        FieldRel sig ι _ (fun m _ => levelRel sig ι m) .prop _
          (fun _ _ => DataType.blockTruth decl.dataTypes S T'.name)).validEqTerm hd (hI _) hb
    let B : Name → Prop := fun D' => DataType.blockTruth decl.dataTypes S D' ∧
      ∀ C' : Term 0 (.var :: Γ), Cs₁.get (decl.names.idxOf D') = some ⟨0, C'⟩ → ∀ a,
        ValidEqTerm₀ sig ι a a (.inst D' qs ls₁ ps (as₁.subst σ₁)) → ValidEqTerm₀ sig ι
          (.recursor r ς χ D' qs ls₁ ps (as₁.subst σ₁) a ⟨.prop, l⟩ (Cs₁.subst σ₁) (us₁.subst σ₁))
          (.recursor r ς χ D' qs ls₁ ps (as₁.subst σ₁) a ⟨.prop, l⟩ (Cs₁.subst σ₁) (us₁.subst σ₁))
          ((C'.subst (Subst.lift σ₁)).subst₀ (Subst₀.single a))
    have hclosed : ∀ T' ∈ decl.dataTypes, T'.truth (S B) → B T'.name := by
      rintro T' hT' ⟨con, hcon, fs, hfs⟩
      have hSb := hmono B _ (fun _ h => h.1) T' hT' con hcon fs fs hfs
      refine ⟨DataType.blockTruth_closed hmono hT' ⟨con, hcon, fs, hSb⟩, fun C' hC' a ha => ?_⟩
      obtain ⟨ts₁, ts₂, rfl, h₂, hts⟩ := (hiff T' hT' con hcon).2.1 fs fs hSb
      cases Args.terms_inj h₂
      have hQ : ∀ D', ResultLeaf sig ι
          (Lifting.ofMotives decl.names qs ls₁ ps (as₁.subst σ₁) l χ (Cs₁.subst σ₁))
          (Term.recursorAt r ς χ qs ls₁ ps (as₁.subst σ₁) ⟨.prop, l⟩ (Cs₁.subst σ₁)
            (us₁.subst σ₁))
          (Term.recursorAt r ς χ qs ls₂ ps (as₂.subst σ₁) ⟨.prop, l⟩ (Cs₂.subst σ₁)
            (us₂.subst σ₁)) D'
          (.inst D' qs ls₁ ps (as₁.subst σ₁), fun _ _ => B D') := by
        intro D' b hb a₁ a₂ hB
        obtain ⟨hD', C, hC, rfl⟩ := Lifting.ofMotives_block_inv hb
        rw [Term.recursorAt_subst₀, Term.recursorAt_subst₀]
        obtain ⟨j'', T'', C'', hj'', rfl, hC'', rfl⟩ := hK σ₁ D' hD' C hC
        have ha₁ := hvalP T'' (List.mem_of_getElem? hj'') a₁ hB.1
        exact (hB.2 C'' ((hidx j'' T'' hj'').symm ▸ hC'') a₁ ha₁).prop_any hd
          ((hCv j'' T'' C'' hj'' hC'').motive_prop hσ₁ ha₁)
      obtain ⟨v₁, v₂, hb, -, -⟩ := hbranch σ₁ σ₁ hσ₁ T' hT' con hcon C' hC' ts₁ ts₁
        (by rw [Constructor.fieldsAt_subst]; exact hts) _ .prop _ hQ
        (fun _ _ _ _ _ _ => Iff.rfl) (hnest B T' hT' con hcon _ _ hfs)
      obtain ⟨i, j, hi, hj⟩ := TypeDeclaration.exists_cases hT' hcon
      have hCj := hCv j T' C' hj ((hidx j T' hj) ▸ hC')
      have hca : ValidEqTerm₀ sig ι (.ctor T'.name qs ls₁ ps (as₁.subst σ₁) con.name ts₁.terms) a
          (.inst T'.name qs ls₁ ps (as₁.subst σ₁)) :=
        ha.prop_any hd ⟨_, hI _, _, _, levelRel_prop_iff.2 (hP T' hT').1⟩
      exact (hb.conv (hCj.motive hσ₁ hca)).prop_any hd (hCj.motive_prop hσ₁ ha)
    exact ((htrue B hclosed).2 C₁ ((hidx h' T hh).symm ▸ hC) _ htσ).prop_any hd
      (hCv₀.motive_prop hσ₁ htσ)

-- ADE: `natrec-congᵛ`, `prodrec-congᵛ`, `unitrec-congᵛ` and `emptyrec-congᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(rec_≡)` keeps the meaning, and `(rec)` with it: at equal substitutions of the context, the
recursors on the canonical terms that `(eq_μ)` relates are equal terms of the motive, by induction on
`(eq_μ)`, the least relations closed under its clauses: the relations of the canonical terms that
`(eq_μ)` relates and on which the recursors are equal are closed, since the recursors on two
constructors step to their branches, at equal arguments of the fields and at recursive results that
these relations make equal. On a proposition, the truths of its instances whose motives are true at
every proof are closed likewise, so that the motive at the term is true. -/
theorem ValidEqTermΓ.recursor {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) (hord : sig.LiftsInOrder) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    {r ς χ : Grade} {t₁ t₂ : Term 0 Γ} {Cs₁ Cs₂ : Motives 0 Γ}
    {us₁ us₂ : Branches 0 Γ} {κ : Universe 0} {h' : Nat} {C₁ : Term 0 (.var :: Γ)}
    {as₁' : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₁'
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (ht : ValidEqTermΓ sig ι ctx t₁ t₂ (.inst D qs ls₁ ps as₁)) (hh : decl.dataTypes[h']? = some T)
    (hC : Cs₁.get h' = some ⟨0, C₁⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs₁.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs₁.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls₁ ps as₁)) C' (.sort κ))
    (hus₁ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    (hus₂ : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    {Rs₁ Rs₂ : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
      Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
    (hRs₁ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls₁.getFin hl₁) as₁ (Lifting.ofMotives decl.names qs ls₁ ps as₁ κ.level χ Cs₁)
        (Rs₁ con) πs)
    (hRs₂ : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls₂.getFin hl₂) as₂ (Lifting.ofMotives decl.names qs ls₂ ps as₂ κ.level χ Cs₂)
        (Rs₂ con) πs)
    (hut : ∀ i j T' con C' u₁ u₂, decl.cases[i]? = some (j, T', con) →
      Cs₁.get j = some ⟨0, C'⟩ →
      us₁.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₁⟩ →
      us₂.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u₂⟩ →
      ValidEqTermΓ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls₁.getFin hl₁) as₁)).append (Rs₁ con))
        u₁ u₂
        ((C'.atCtor T'.name qs ls₁ ps as₁ con.name (con.params (.ofLists qs ps hq hp))).rename
          (Ren.weakenN _)))
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop) :
    ValidEqTermΓ sig ι ctx (.recursor r ς χ D qs ls₁ ps as₁ t₁ κ Cs₁ us₁)
      (.recursor r ς χ D qs ls₂ ps as₂ t₂ κ Cs₂ us₂) (C₁.subst₀ (Subst₀.single t₁)) := by
  obtain ⟨hsig, -⟩ := hent.hasDataType h
  obtain ⟨-, -, hD⟩ := id hsig
  subst hD
  have hctx := ht.1.1
  have ht₁ := ht.trans ht.symm
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
      Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
    exact (hCv h' T C₁ hh hC).motive hσ (ht₁.2 σ₁ σ₂ hσ)
  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
  exact ValidEqTerm₀.recursor_block hent hord h hq hl₁ hl₂ hp hadm hctx has hCs hCv hus₁ hus₂ hRs₁
    hRs₂ hut hκ hσ hh hC (ht.2 σ₁ σ₂ hσ)

-- ADE: `natrec-zeroᵛ`, `natrec-sucᵛ`, `prodrec-βᵛ` and `unitrec-βᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(ι)` keeps the meaning: at equal substitutions of the context, the recursors on the constructor
are equal terms of the motive, by `(rec_≡)`, and the second one steps to the substituted instance of
the branch by the arguments and by the recursive results. -/
theorem ValidEqTermΓ.iota {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) (hord : sig.LiftsInOrder) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) (hc : con ∈ T.constructors) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {ts : Args 0 Γ (con.params (.ofLists qs ps hq hp))}
    (hts : ValidArgsΓ sig ι ctx ts (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
    {i j : Nat} (hi : decl.cases[i]? = some (j, T, con)) {r ς χ : Grade} {Cs : Motives 0 Γ}
    {us : Branches 0 Γ} {κ : Universe 0} {C : Term 0 (.var :: Γ)} (hC : Cs.get j = some ⟨0, C⟩)
    (hCs : ∀ j T', decl.dataTypes[j]? = some T' → ∃ C', Cs.get j = some ⟨0, C'⟩)
    (hCv : ∀ j T' C', decl.dataTypes[j]? = some T' → Cs.get j = some ⟨0, C'⟩ →
      ValidTermΓ sig ι (ctx.var (.inst T'.name qs ls ps as)) C' (.sort κ))
    (hus : ∀ i j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ u, us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩)
    {Rs : (con : Constructor decl.sorts decl.grades decl.levels decl.scope) →
      Telescope 0 (Γ.extend (con.params (.ofLists qs ps hq hp)).length)
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
    (hRs : ∀ (i : Nat) j T' con, decl.cases[i]? = some (j, T', con) →
      ∃ πs, Constructor.ResultTypes sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
        (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs) (Rs con) πs)
    (hut : ∀ i j T' con C' u, decl.cases[i]? = some (j, T', con) →
      Cs.get j = some ⟨0, C'⟩ →
      us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
        (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
      ValidTermΓ sig ι
        ((ctx.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as)).append (Rs con)) u
        ((C'.atCtor T'.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))).rename
          (Ren.weakenN _)))
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop)
    {u : Term 0 ((Γ.extend (con.params (.ofLists qs ps hq hp)).length).extend
      (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length)}
    (hu : us.get i = some ⟨_, _, u⟩)
    {rs : Args 0 Γ (con.nestResultParams (.ofLists qs ps hq hp) decl.names)}
    (hrs : Constructor.ResultTerms sig ⟨κ.quality, r, ς⟩ con (.ofLists qs ps hq hp) decl.names
      (ls.getFin hl) as (Lifting.ofMotives decl.names qs ls ps as κ.level χ Cs)
      (Term.recursorAt r ς χ qs ls ps as κ Cs us) ts rs) :
    ValidEqTermΓ sig ι ctx (.recursor r ς χ D qs ls ps as (.ctor D qs ls ps as con.name ts.terms) κ Cs us)
      ((u.instantiate (rs.rename (Ren.weakenN _))).instantiate ts)
      (C.subst₀ (Subst₀.single (.ctor D qs ls ps as con.name ts.terms))) := by
  obtain ⟨hsig, -⟩ := hent.hasDataType h
  have hD := h.2.2
  subst hD
  have hd := has.1.distinct
  have hct := ValidEqTermΓ.ctor hent h hc hq hl hl hp hadm has (fun _ => Level.equivalence.refl _) hts
  have hj := TypeDeclaration.dataTypes_getElem?_of_cases (List.mem_of_getElem? hi)
  have hrec := ValidEqTermΓ.recursor hent hord h hq hl hl hp hadm has hct hj hC hCs hCv hus hus hRs
    hRs
    (fun i j T' con C' u₁ u₂ hi hC hu₁ hu₂ => by
      cases Branches.get_inj hu₁ hu₂
      exact hut i j T' con C' u₁ hi hC hu₁) hκ
  refine ⟨hrec.1, fun σ₁ σ₂ hσ => ?_⟩
  have hr := hrec.2 σ₁ σ₂ hσ
  rw [Term.instantiate_instantiate_subst_closed]
  have hred := Red.iota_subst (ι := ι) hsig hi σ₂ hq hl hp (ts.subst σ₂) hu
    (Constructor.ResultTerms.subst_recursorAt σ₂ hrs) (D' := T.name) (as := as.subst σ₂)
    (ls'' := ls) (qs'' := qs) (ps'' := ps)
  rw [Args.terms_subst] at hred
  exact ((ValidEqTerm₀.red_iff hd hred).1 hr.symm).symm

-- ADE: `unitrec-β-ηᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Unit.agda`.
/-- `(η_c)` keeps the meaning: at equal substitutions of the context, the term `t` of an instance in
a universe computes to the single constructor of its type, at fields equal to those of the other
substitution, without recursive results since it has no recursive field, so that the recursor at the
other substitution steps to `e` at this constructor, equal to `e` at the term `t` since the two are
equal terms of the instance; on a proposition, the motive is a proposition, true since `e` proves
it. -/
theorem ValidEqTermΓ.etaCtor {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasDataType D decl T) (hc : T.constructors = [con]) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    (hr : ∀ ν ∈ (con.fields (.ofLists qs ps hq hp)).nest decl.names, ν = .plain)
    {as : InstanceArgs 0 Γ decl.scope} {r ς χ : Grade} {t : Term 0 Γ} {Cs : Motives 0 Γ}
    {us : Branches 0 Γ} {κ : Universe 0} {i j : Nat} {C e : Term 0 (.var :: Γ)}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (he : ValidTermΓ sig ι (ctx.var (.inst D qs ls ps as)) e C)
    (hCv : ValidTermΓ sig ι (ctx.var (.inst D qs ls ps as)) C (.sort κ))
    (hi : decl.cases[i]? = some (j, T, con))
    (hu : us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length, 0,
      e.atCtor T.name qs ls ps as con.name (con.params (.ofLists qs ps hq hp))⟩)
    (hκ : (decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] →
      κ.quality = .prop) :
    ValidEqTermΓ sig ι ctx (e.subst₀ (Subst₀.single t)) (.recursor r ς χ D qs ls ps as t κ Cs us)
      (C.subst₀ (Subst₀.single t)) := by
  obtain ⟨hsig, hv⟩ := hent.hasDataType h
  obtain ⟨hdecl, hT, hD⟩ := id hsig
  subst hD
  have hctx := ht.1.1
  have hd := hctx.distinct
  have hcon : con ∈ T.constructors := hc ▸ List.mem_singleton_self con
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
      Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
    exact hCv.motive hσ (ht.2 σ₁ σ₂ hσ)
  have ht' := ht.2 σ₁ σ₂ hσ
  have hσ₁ := hσ.left hctx
  rw [Term.subst_subst₀_of (Subst₀.Swaps.single _ _),
    Term.subst_subst₀_of (Subst₀.Swaps.single _ _)]
  have hI : Computesι sig ι (.inst T.name qs ls ps (as.subst σ₁))
      (.inst T.name qs ls ps (as.subst σ₁)) := (Whnf.inst ..).computes
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht'.1.2
  cases Computesι.det hd hcv hI
  have hasσ := has.2 σ₁ σ₁ hσ₁
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · -- An instance in a universe: the term computes to the constructor, at both substitutions.
    obtain ⟨S, hU, -, hmono, hrec, -, hiff⟩ := hv.univRel hd hdecl hq hl hp hadm hasσ hs
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hnp := Computesι.not_computesToProp hd hI hU'
    obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht'.2.1 hnp
    cases Computesι.det hd hI hv'
    have hrel' := (HasEq.unique hd hR' (.univ _ hU') w₁ w₂).1 hrel
    obtain ⟨T', hT', hn, con', hcon', fs₁, fs₂, ⟨qs₁, ls₁, ps₁, Δ₁, as₁, rfl⟩,
      ⟨qs₂, ls₂, ps₂, Δ₂, as₂, rfl⟩, hS₁₂⟩ := DataType.blockRel_inv hmono hrel'
    cases List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hdecl)) hT' hT hn
    rw [hc, List.mem_singleton] at hcon'
    subst hcon'
    obtain ⟨ts₁, ts₂, rfl, rfl, -⟩ := (hiff T hT con' hcon).2.1 fs₁ fs₂ hS₁₂
    have hct : ValidEqTerm₀ sig ι (t.subst σ₁)
        (.ctor T.name qs ls ps (as.subst σ₂) con'.name ts₂.terms)
        (.inst T.name qs ls ps (as.subst σ₁)) :=
      ⟨ht'.1, fun _ => ⟨_, _, _, _, hI, hw₁, (Whnf.ctor ..).computes, .univ _ hU',
        DataType.blockRel_closed hmono hT ⟨con', hcon, ts₁.terms, ts₂.terms,
          ⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, rfl⟩, hS₁₂⟩⟩,
        fun hp => absurd hp hnp⟩
    have hb := he.2 _ _ ((EqSubst.var_iff ctx _
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))
      (Subst.append (n := 1) σ₂ (Subst.closedSingle _))).2 ⟨hσ, hct⟩)
    have hbr : ValidEqTerm₀ sig ι ((e.subst (Subst.lift σ₁)).subst₀ (Subst₀.single (t.subst σ₁)))
        ((e.atCtor T.name qs ls ps as con'.name (con'.params (.ofLists qs ps hq hp))).subst
          (Subst.append σ₂ ts₂.toSubst))
        ((C.subst (Subst.lift σ₁)).subst₀ (Subst₀.single (t.subst σ₁))) := by
      rw [Term.atCtor_subst_append, Term.subst_lift_single, Term.subst_lift_single,
        Term.subst_lift_single]
      exact hb
    exact ((ValidEqTerm₀.redStar_iff hd (RedStar.recursor hw₂.1)).2
      ((ValidEqTerm₀.red_iff hd (Red.iota_subst₀ hsig hi σ₂ hq hl hp ts₂ hu hr)).2 hbr.symm)).symm
  · -- A proposition: the motive is one, which `e` proves.
    obtain ⟨s, l⟩ := κ
    have hs' : s = .prop := hκ hs (List.ne_nil_of_mem (List.mem_of_getElem? hi))
    subst hs'
    have ht₁ := ht.2 σ₁ σ₁ hσ₁
    have hCp := hCv.motive_prop hσ₁ ht₁
    have hb := he.2 _ _ ((EqSubst.var_iff ctx _
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))
      (Subst.append (n := 1) σ₁ (Subst.closedSingle (t.subst σ₁)))).2 ⟨hσ₁, ht₁⟩)
    rw [Term.subst_lift_single] at hCp
    rw [Term.subst_lift_single, Term.subst_lift_single]
    obtain ⟨w, R'', hw, hR'', hrel''⟩ := hb.2.2 hCp
    exact ⟨hb.1, fun hn => absurd hCp hn,
      fun _ => ⟨w, R'', hw, hR'', hR''.prop_any hd (hCp.isProp hd hw) hrel''⟩⟩

end

end Sic.Core
