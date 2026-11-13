module

public import Sic.Core.Usage
import Sic.Core.Syntax.Signature
import Sic.Core.Syntax.Terms

/-!
# Inversion of the Usage

The judgments of usage of annex 12 of RFC 36, inverted: a term of a given form uses its variables as
the rule of its form allows, with grades above those of the judgment, since the subsumption
`(sub_▶)` may end its derivation.
Each lemma takes the entries of the signature that the term names, in a signature whose names are
distinct, so that the rule of the derivation reads the same entries.
The proofs are by structural recursion on the derivation, whose term is given by an equation, so
that the subsumption keeps it.

ADE invert their usage in `Graded/Usage/Inversion.agda`, one lemma `inv-usage-…` for each form of
term, which gives the grades of the rule above those of the judgment.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Variables and Constants -/

-- ADE: `inv-usage-var` and `inv-usage-app`, in `Graded/Usage/Inversion.agda`.
/-- The application `x[t̄]` uses `x` with the grade of the mode, and its arguments as their
telescope does, with grades above those of the judgment. -/
theorem Usage.inv_var {sig : Signature} {k : Nat} {Γ : Scope} {e : Scope.Entry} {x : Var Γ e}
    {ts : Args k Γ e.params} {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {t : Term k Γ}, Usage sig γ m t → t = .var x ts →
      ∃ δ, γ ≤ᶜ (GradeVector.update 𝟘ᶜ x.toFin m.grade) +ᶜ δ ∧ UsageArgs sig δ m ts
  | _, _, .var hts, he => by
    cases he
    exact ⟨_, (Sic.Math.Vector.preorder Grade.modality).refl _, hts⟩
  | _, _, .sub h hle, he =>
    have ⟨δ, hδ, hts⟩ := Usage.inv_var h he
    ⟨δ, (Sic.Math.Vector.preorder Grade.modality).trans hle hδ, hts⟩
  | _, _, .const .., he | _, _, .sort, he | _, _, .inst .., he | _, _, .ctor .., he
  | _, _, .recursor .., he | _, _, .obs .., he | _, _, .corec .., he => nomatch he

-- ADE: `inv-usage-defn`, in `Graded/Usage/Inversion.agda`.
/-- A constant of an entry of the mode `m₂`, in a signature whose names are distinct, uses no
variable, in a mode `m` that `m₂` allows. -/
theorem Usage.inv_const {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope} {f : Name}
    {j k' g : Nat} {m₂ : Mode} {p : Grade} {A : Instance j g → Term k' []}
    (h : sig.HasConstant f j k' g m₂ p A) {qs : List Quality} {ls : List (Level k)}
    {ps : List Grade} {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {t : Term k Γ}, Usage sig γ m t → t = .const f qs ls ps →
      γ ≤ᶜ 𝟘ᶜ ∧ m ·ᵐ m₂ = m
  | _, _, .const h' hm, he => by
    cases he
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hd.hasConstant_unique h h'
    exact ⟨(Sic.Math.Vector.preorder Grade.modality).refl _, hm⟩
  | _, _, .sub h' hle, he =>
    have ⟨hγ, hm⟩ := Usage.inv_const hd h h' he
    ⟨(Sic.Math.Vector.preorder Grade.modality).trans hle hγ, hm⟩
  | _, _, .var .., he | _, _, .sort, he | _, _, .inst .., he | _, _, .ctor .., he
  | _, _, .recursor .., he | _, _, .obs .., he | _, _, .corec .., he => nomatch he

/-! ## Declared Types -/

-- ADE: `inv-usage-prodʷ`, in `Graded/Usage/Inversion.agda`, for the pairs.
/-- A constructor of a data type, in a signature whose names are distinct, uses the variables of
the terms of its fields as their telescope does, with grades above those of the judgment. -/
theorem Usage.inv_ctor {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {decl : TypeDeclaration} {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hc : con ∈ T.constructors) {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    {ts : Args k Γ (con.params (.ofLists qs ps hq hp))} {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {t : Term k Γ}, Usage sig γ m t →
      t = .ctor D qs ls ps as con.name ts.terms → ∃ γ', γ ≤ᶜ γ' ∧ UsageArgs sig γ' m ts
  | _, _, .ctor (con := con') (ts := ts') h' hc' _ _ hts, he => by
    injection he with _ hΔ hD hqs hls hps has hn hts'
    subst hD hqs hls hps
    obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h' h
    cases hT
    cases List.eq_of_nodup_map (hd.constructors_nodup h) hc' hc hn
    cases Args.terms_inj hts'
    exact ⟨_, (Sic.Math.Vector.preorder Grade.modality).refl _, hts⟩
  | _, _, .sub h' hle, he =>
    have ⟨γ', hγ, hts⟩ := Usage.inv_ctor hd h hc hq hp h' he
    ⟨γ', (Sic.Math.Vector.preorder Grade.modality).trans hle hγ, hts⟩
  | _, _, .var .., he | _, _, .const .., he | _, _, .sort, he | _, _, .inst .., he
  | _, _, .recursor .., he | _, _, .obs .., he | _, _, .corec .., he => nomatch he

-- ADE: `inv-usage-app`, `inv-usage-fst` and `inv-usage-snd`, in `Graded/Usage/Inversion.agda`.
/-- An observation of a term of a codata type, by the destructor at a position of the type at the
instance, in a signature whose names are distinct, uses the variables of its term once and those of
its arguments as their telescope does, with grades above those of the judgment, in a mode that the
grade of the destructor allows. -/
theorem Usage.inv_obs {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ decl.scope} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) {d : Name} {p q : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership ps'.length} (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {t : Term k Γ} {bs : Args k Γ ps'} {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {u : Term k Γ}, Usage sig γ m u →
      u = .obs D qs ls ps as t d bs.terms →
        ∃ γ' δ, γ ≤ᶜ γ' +ᶜ δ ∧ Usage sig γ' m t ∧ UsageArgs sig δ m bs ∧ m ·ᵐ p.mode = m
  | _, _, .obs (bs := bs') h' _ _ hpos' ht hbs hm, he => by
    injection he with _ hΔ hD hqs hls hps has ht' hd' hbs'
    subst hD hqs hls hps ht' hd'
    obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h' h
    cases hT
    obtain ⟨rfl, rfl⟩ := hpos'.params_unique (hd.destructors_nodup h) hpos
    cases Args.terms_inj hbs'
    exact ⟨_, _, (Sic.Math.Vector.preorder Grade.modality).refl _, ht, hbs, hm⟩
  | _, _, .sub h' hle, he =>
    have ⟨γ', δ, hγ, ht, hbs, hm⟩ := Usage.inv_obs hd h hq hp hpos h' he
    ⟨γ', δ, (Sic.Math.Vector.preorder Grade.modality).trans hle hγ, ht, hbs, hm⟩
  | _, _, .var .., he | _, _, .const .., he | _, _, .sort, he | _, _, .inst .., he
  | _, _, .ctor .., he | _, _, .recursor .., he | _, _, .corec .., he => nomatch he

-- ADE: `inv-usage-natrec-no-nr`, `inv-usage-prodrec`, `inv-usage-unitrec` and
-- `inv-usage-emptyrec`, in `Graded/Usage/Inversion.agda`.
/-- A recursor on a block of data types, in a signature whose names are distinct, uses the
variables as the premises of `(rec_▶)` allow, with grades above those of the judgment. -/
theorem Usage.inv_recursor {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {decl : TypeDeclaration} {D : Name} {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ decl.scope} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) {r : Grade} {t : Term k Γ} {Cs : Motives k Γ}
    {us : Branches k Γ} {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {v : Term k Γ}, Usage sig γ m v →
      v = .recursor r D qs ls ps as t Cs us →
      ∃ (γ' χ : GradeVector Γ.length) (δs : Nat → GradeVector Γ.length) (gs : Nat → Nat → Grade),
        γ ≤ᶜ (r ·ᶜ γ') +ᶜ χ ∧
        (∀ j n (C : Term k (Γ.extend (n + 1))), Cs.get j = some ⟨n, C⟩ →
          Usage sig 𝟘ᶜ .zeroZero C) ∧
        Usage sig γ' (m ⊙ r) t ∧
        (∀ i j T' con u, decl.cases[i]? = some (j, T', con) →
          us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
            (con.resultParams (.ofLists qs ps hq hp) decl.names).length, u⟩ →
          Usage sig (((δs i).extendGrades (gs i) (con.params (.ofLists qs ps hq hp))).extendResults
            (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
            ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)
            (con.params (.ofLists qs ps hq hp))) m u) ∧
        (∀ i j T' con l (p : Parameter), decl.cases[i]? = some (j, T', con) →
          (con.params (.ofLists qs ps hq hp))[l]? = some p →
          m.grade * r * p.usage ≤ gs i l +
            (if ((con.fields (.ofLists qs ps hq hp)).recursionAt decl.names l).isSome then
              (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names)) l
              else Grade.zero) * r) ∧
        (∀ i j T' con, decl.cases[i]? = some (j, T', con) →
          χ ≤ᶜ δs i +ᶜ Telescope.resultSum
            (us.resultGrades i ((con.fields (.ofLists qs ps hq hp)).recursion decl.names))
            ((con.fields (.ofLists qs ps hq hp)).recursion decl.names) ·ᶜ χ) ∧
        (m = .oneOne → (∃ T' ∈ decl.dataTypes, 2 ≤ T'.constructors.length) →
          r.mode = .oneOne) ∧
        ((decl.sort (.ofLists qs ps hq hp)).quality = .prop → decl.cases ≠ [] → m ≠ .oneOne)
  | _, _, .recursor h' _ _ hC ht _ _ hu hg hχ hr hprop, he => by
    injection he with _ hΔ hr' hD hqs hls hps has ht' hCs hus
    subst hr' hD hqs hls hps ht' hCs hus
    obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h' h
    cases hT
    cases has
    exact ⟨_, _, _, _, (Sic.Math.Vector.preorder Grade.modality).refl _, hC, ht, hu, hg, hχ, hr,
      hprop⟩
  | _, _, .sub h' hle, he =>
    have ⟨γ', χ, δs, gs, hγ, hC, ht, hu, hg, hχ, hr, hprop⟩ := Usage.inv_recursor hd h hq hp h' he
    ⟨γ', χ, δs, gs, (Sic.Math.Vector.preorder Grade.modality).trans hle hγ, hC, ht, hu, hg, hχ, hr,
      hprop⟩
  | _, _, .var .., he | _, _, .const .., he | _, _, .sort, he | _, _, .inst .., he
  | _, _, .ctor .., he | _, _, .obs .., he | _, _, .corec .., he => nomatch he

-- ADE: none.
/-- A corecursor of a block of codata types, from a state of the type at a position of the block,
in a signature whose names are distinct, uses the variables as the premises of `(corec_▶)` allow,
with grades above those of the judgment. -/
theorem Usage.inv_corec {sig : Signature} (hd : sig.Distinct) {k : Nat} {Γ : Scope}
    {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ decl.scope} (hq : qs.length = decl.sorts)
    (hp : ps.length = decl.grades) {r : Grade} {Ss : States k Γ} {gs : CorecBranches k Γ}
    {h' : Nat} {ps' : List Parameter} {S : Telescope k Γ ps'} {ss : Args k Γ ps'}
    (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩) {m : Mode} :
    ∀ {γ : GradeVector Γ.length} {v : Term k Γ}, Usage sig γ m v →
      v = .corec r D qs ls ps as ss.terms Ss gs →
      ∃ (γ' δ : GradeVector Γ.length) (δs : Nat → GradeVector Γ.length),
        γ ≤ᶜ (r ·ᶜ γ') +ᶜ δ ∧
        (∀ j (ps'' : List Parameter) (S' : Telescope k Γ ps''),
          Ss.get j = some ⟨0, ps'', S'⟩ → UsageTelescope sig 𝟘ᶜ .zeroZero S') ∧
        UsageArgs sig γ' (m ⊙ r) ss ∧
        (∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q : Grade)
          (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
          (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
          decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
          (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
          gs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ →
          Usage sig (((δs i).extendParams ((m ⊙ p).grade * r) ps'').extendParams (m ⊙ p).grade ps₁)
            (m ⊙ p) g) ∧
        (∀ i j T' d (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership ps₁.length), decl.codataCases[i]? = some (j, T', d) →
          (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ → δ ≤ᶜ p ·ᶜ δs i) ∧
        (∀ i j T' d (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
          (ψ : ResultOwnership ps₁.length) (D' : Name), decl.codataCases[i]? = some (j, T', d) →
          (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ → B.blockName decl.names = some D' →
          δ ≤ᶜ (p ·ᶜ δs i) +ᶜ (p ·ᶜ δ))
  | _, _, .corec (ss := ss') h₁ _ _ hh₁ hS₁ hSu hss _ _ _ _ hgu hδ hδr, he => by
    injection he with _ hΔ hr' hD hqs hls hps has hss' hSs hgs
    subst hr' hD hqs hls hps hSs hgs
    obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h₁ h
    cases hT
    have hi := (TypeDeclaration.idxOf?_codataTypes (hd.nodup h.1) hh₁).symm.trans
      (TypeDeclaration.idxOf?_codataTypes (hd.nodup h.1) hh)
    cases Option.some.inj hi
    cases hS₁.symm.trans hS
    cases Args.terms_inj hss'
    exact ⟨_, _, _, (Sic.Math.Vector.preorder Grade.modality).refl _, hSu, hss, hgu, hδ, hδr⟩
  | _, _, .sub h₁ hle, he =>
    have ⟨γ', δ, δs, hγ, hSu, hss, hgu, hδ, hδr⟩ := Usage.inv_corec hd h hq hp hh hS h₁ he
    ⟨γ', δ, δs, (Sic.Math.Vector.preorder Grade.modality).trans hle hγ, hSu, hss, hgu, hδ, hδr⟩
  | _, _, .var .., he | _, _, .const .., he | _, _, .sort, he | _, _, .inst .., he
  | _, _, .ctor .., he | _, _, .recursor .., he | _, _, .obs .., he => nomatch he

end Sic.Core
