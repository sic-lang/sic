module

public import Sic.Core.Lifting.Substitution
public import Sic.Core.Nesting.Relation
public import Sic.Core.Soundness.Corecursors
public import Sic.Core.Soundness.Recursors.Similar
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Observations
import Sic.Core.Lifting.Recursion
import Sic.Core.Lifting.Shape
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Results.Substitution
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.DeclaredTypes
import Sic.Core.Soundness.Substitution
import Sic.Core.Substitution.Nesting
import Sic.Core.Syntax.Signature

/-!
# Meaning of the Recursive Result of a Nested Field

The recursive results of two terms of a field nested below a codata type, which the equality of
the type of the field relates, are equal terms of this type lifted at the first term, when the
results of the terms of the types of the block are equal terms of their motives: the equality of
the field is that of the graph of the nestings of annex 18 of RFC 36, which this module follows,
clause by clause.

At a position, the results are those of the terms of a type of the block.
At an instance of a codata type, they are corecursors of its lifting, without state, whose
observations step to their branches, the results of the observations of the terms, which the
equality of the destructors of the type relates: the lifting has the destructors of the type whose
results have a position, at the same arguments, and its results are the results of these, lifted,
so that the equality of its destructors, which the meaning of the type lifted gives, relates the
observations of the corecursors, destructor by destructor.
A proposition declared as a codata type has proofs that need not compute: its destructors relate
some abstractions, and the results of its destructors are propositions, whose truth holds of any
term.

The second term is of an instance of the type of the field at other levels and arguments, of the
same shape, which is all that its result reads of it.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Relations That Do Not Read the Computation -/

-- ADE: none.
/-- The relation `R`, given at a position that holds a type of a sort of the quality `sT`, relates
the terms that compute as terms that it relates, and any terms when the quality is that of the
propositions. -/
def LeafCongr (sig : Signature) (ι : Interpretation) (sT : Quality) (R : TermRel) : Prop :=
  ∀ a a' b b', (sT = .prop ∨ ((∀ w, Computesι sig ι a w ↔ Computesι sig ι a' w) ∧
    ∀ w, Computesι sig ι b w ↔ Computesι sig ι b' w)) → (R a b ↔ R a' b')

/-- The equality that the graph of the nestings gives a type relates the terms that compute as
terms that it relates, and any terms when the quality is that of the propositions, when the
relations at its positions do. -/
theorem NestRel.congr_computes {n : Nat} {sT s : Quality} {τ : Nest NestLeaf} {A : Term 0 []}
    {F : TermRel} (hF : NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A F)
    (hτ : Nest.All (fun x => LeafCongr sig ι sT x.2) τ) {a a' b b' : Term 0 []}
    (h : s = .prop ∨ ((∀ w, Computesι sig ι a w ↔ Computesι sig ι a' w) ∧
      ∀ w, Computesι sig ι b w ↔ Computesι sig ι b' w)) : F a b ↔ F a' b' := by
  cases hF with
  | plain _ hF => exact hF.congr_computes h
  | direct hs _ =>
    cases hτ with
    | direct hR => exact hR a a' b b' (hs ▸ h)
  | codata _ _ _ _ _ hs =>
    rcases h with h | ⟨ha, hb⟩
    · exact absurd (hs.symm.trans h) (by decide)
    · simp only [TermRel.computed, ha, hb]
  | codataProp => exact .rfl

/-! ## Telescopes Used More -/

/-- A telescope whose entries are used more, substituted by a substitution of the first order. -/
theorem Telescope.scale_subst₀ {k : Nat} (r : Grade) :
    {Γ Δ : Scope} → {ps : List Parameter} → (σ : Subst₀ k Γ Δ) → (Θ : Telescope k Δ ps) →
      (Θ.scale r).subst₀ σ = (Θ.subst₀ σ).scale r
  | _, _, _, _, .nil => rfl
  | _, _, _, σ, .cons _ p A Θ =>
    congrArg (Telescope.cons .unrestrictedUnrestricted (p.scale r) (A.subst₀ σ))
      (Telescope.scale_subst₀ r (Subst₀.lift σ) Θ)

/-- A telescope whose entries are used more is a telescope in the same sort, with the same
equality: the meaning ignores the grades. -/
theorem TelRel.scale {n : Nat} (r : Grade) {s : Quality} :
    {rs : Nat → Nest NestLeaf} → {ps : List Parameter} → {Θ : Telescope 0 [] ps} →
      {S : FieldsRel} → TelRel sig ι n (fun m _ => levelRel sig ι m) s rs Θ S →
        TelRel sig ι n (fun m _ => levelRel sig ι m) s rs (Θ.scale r) S
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hA hF G hG hresp hrs =>
    .cons hA hF G (fun a ha => by
      rw [Telescope.scale_subst₀]
      exact (hG a ha).scale r) hresp hrs
  | _, _, _, _, .nested hrs hF G hG =>
    .nested hrs hF G fun a => by
      rw [Telescope.scale_subst₀]
      exact (hG a).scale r

/-- Arguments of a telescope whose entries are used more are arguments of the telescope. -/
theorem Args.exists_terms_map {k : Nat} {Γ : Scope} (f : Parameter → Parameter) :
    (ps : List Parameter) → (ts' : Args k Γ (ps.map f)) → ∃ ts : Args k Γ ps, ts.terms = ts'.terms
  | [], .nil => ⟨.nil, rfl⟩
  | _ :: ps, .cons t ts' =>
    have ⟨ts, h⟩ := Args.exists_terms_map f ps ts'
    ⟨.cons t ts, congrArg (Terms.cons t) h⟩

/-- A term over as many variables as two equal numbers, brought to the other number, is
instantiated by terms as the term is. -/
theorem Term.instantiateTerms_cast {k : Nat} {Γ : Scope} {n m : Nat} (h : n = m)
    (g : Term k (Γ.extend n)) (ts : Terms k Γ) :
    (h ▸ g : Term k (Γ.extend m)).instantiateTerms ts = g.instantiateTerms ts := by
  subst h
  rfl

/-- A term over the variables of a telescope, brought over those of a telescope of the same length,
is substituted by closed arguments of this telescope as the term is by the same arguments of the
first one. -/
theorem Term.subst_toSubst_cast {k : Nat} {ps ps' : List Parameter} (h : ps'.length = ps.length)
    (X : Term k (Scope.extend [] ps'.length)) (ts : Args k [] ps) (ts' : Args k [] ps')
    (hts : ts.terms = ts'.terms) :
    (h ▸ X : Term k (Scope.extend [] ps.length)).subst ts.toSubst = X.subst ts'.toSubst := by
  rw [← Term.instantiate_eq_subst, ← Term.instantiate_eq_subst]
  apply Option.some.inj
  rw [← Term.instantiateTerms_terms, ← Term.instantiateTerms_terms, hts,
    Term.instantiateTerms_cast h X]

/-! ## Corecursors Without State -/

/-- `(β_⟶)` for a closed corecursor without state, at a destructor that is not recursive: the
observation steps to the branch of its destructor at the arguments. -/
theorem Red.beta_stateless {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h₀ : sig.HasCodataType T.name decl T) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) {Δ : Scope} {as : InstanceArgs 0 [] Δ} {r : Grade}
    {Ss : States 0 []} {gs : CorecBranches 0 []} {j i : Nat} {d : Name}
    (hi : decl.codataCases[i]? = some (j, T, d))
    (hrec : (T.body (.ofLists qs ps hq hp)).resultName decl.names d = none)
    {ps₁ : List Parameter} {g : Term 0 (Scope.extend [] ps₁.length)}
    (hg : gs.get i = some ⟨0, 0, ps₁.length, g⟩) (ts : Args 0 [] ps₁) {Δ' : Scope} {D' : Name}
    {qs' : List Quality} {ls' : List (Level 0)} {ps'' : List Grade} {as' : InstanceArgs 0 [] Δ'} :
    Red (sig.interpret ι)
      (.obs D' qs' ls' ps'' as' (.corec r T.name qs ls ps as .nil Ss gs) d ts.terms)
      (g.subst ts.toSubst) := by
  have hv : Term.instantiateTerms₂ (Γ := []) (m := 0) g .nil ts.terms =
      some (g.subst ts.toSubst) := by
    have e₁ : Terms.rename (Γ := []) (Δ := []) (Ren.weakenN 0) ts.terms = ts.terms :=
      Terms.rename_id_of (fun _ => rfl) _
    have e₂ : (Term.instantiateTerms (Γ := []) g ts.terms).bind
        (fun t => Term.instantiateTerms (n := 0) t .nil) = some (g.subst ts.toSubst) := by
      rw [Term.instantiateTerms_terms, Option.bind_some, Term.instantiate_eq_subst]
      rfl
    exact (congrArg (fun us => (Term.instantiateTerms (Γ := []) g us).bind
      fun t => Term.instantiateTerms (n := 0) t .nil) e₁).trans e₂
  have h := Red.beta (sig := sig.interpret ι) (D' := D') (qs' := qs') (ls' := ls') (ps' := ps'')
    (as' := as') (r := r) (as := as) (Ss := Ss)
    (List.mem_map_of_mem (f := Entry.interpret ι) h₀.1) hi rfl hq hl hp hg hv
  rw [hrec] at h
  exact h

/-! ## Equality of the Destructors, Position by Position -/

-- ADE: none.
/-- Observations whose results are related, destructor by destructor, at equal arguments, by the
equality of the result of the destructor, are related by the equality of the destructors, none of
which is recursive, at instantiated levels: the destructors before each destructor being the
observations `o₁`, as the equality of the destructors reads them, from the first one. -/
theorem DesRel.of_positions (hd : sig.Distinct) {n : Nat} {s : Quality} {k' : Nat}
    (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {rs : Nat → Option TermRel} →
      (∀ i, rs i = none) → {θ : Subst 0 [] Γ} → {S : ObsRel} →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (ds.substLevels L) @θ S →
      {o₁ o₂ : Observations} →
      (∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (SΘ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels L).subst (hpos.obsSubst o₁ θ)) SΘ →
        ∀ (ts us : Args 0 [] ps), SΘ ts.terms us.terms → ∀ (v : Term 0 []) (F : TermRel),
        Computesι sig ι
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o₁ θ) ts.toSubst)) v →
        FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F →
        F ((o₁ d ps).subst ts.toSubst) ((o₂ d ps).subst us.toSubst)) →
      S o₁ o₂
  | _, _, .nil, _, _, _, _, h, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q ς Θ B ψ ds, rs, hN, θ, _, h, o₁, o₂, hv => by
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    cases h with
    | recursive hrs => rw [hN 0] at hrs; cases hrs
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
      have hSp := TelRel.isPer hd ih (fun _ => .plain) hΘ
      have hEp := AbstractionRel.isPer hSp (fun ts hts =>
        have ⟨v, hv'⟩ := hB ts hts
        FieldRel.isPer hd ih (hF ts hts v hv')) hBresp
      have hA : AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) := fun ts us hts => by
        have htt := hSp.trans hts (hSp.symm hts)
        obtain ⟨v, hv''⟩ := hB ts htt
        exact hv d p q ς ps _ Θ B ψ .here SΘ hΘ ts us hts v _ hv'' (hF ts htt v hv'')
      have hff := hEp.trans hA (hEp.symm hA)
      exact ⟨hA, DesRel.of_positions hd L ds (fun i => hN (i + 1)) (hG _ hff)
        fun d' p' q' ς' ps' Ξ' Θ' B' ψ' hpos => hv d' p' q' ς' ps' Ξ' Θ' B' ψ' (.there hpos)⟩

-- ADE: none.
/-- Observations that the equality of the destructors, none of which is recursive, at instantiated
levels, relates to themselves give, at each position, at arguments that the equality of the
telescope of its destructor relates, terms that the equality of its result relates: the converse of
`DesRel.of_positions`, for the observations related to themselves. -/
theorem DesRel.positions (hd : sig.Distinct) {n : Nat} {s : Quality} {k' : Nat}
    (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {rs : Nat → Option TermRel} →
      (∀ i, rs i = none) → {θ : Subst 0 [] Γ} → {S : ObsRel} →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (ds.substLevels L) @θ S →
      {o : Observations} → S o o →
      ∀ (d : Name) (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length)
        (hpos : ds.Pos d p q ς Ξ Θ B ψ) (SΘ : FieldsRel),
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels L).subst (hpos.obsSubst o θ)) SΘ →
        ∀ (ts us : Args 0 [] ps), SΘ ts.terms us.terms → ∀ (v : Term 0 []) (F : TermRel),
        Computesι sig ι
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o θ) ts.toSubst)) v →
        FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F →
        F ((o d ps).subst ts.toSubst) ((o d ps).subst us.toSubst)
  | _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _, _, _, _, _, _, _, _, _ =>
    nomatch hpos
  | _, _, .cons _ _ _ _ _ _ ds, _, hN, _, _, h, _, ho, _, _, _, _, _, _, _, _, _, hpos, _, hΘ',
      ts, us, hts, v, _, hv, hF' => by
    have ihm : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    cases h with
    | recursive hrs => rw [hN 0] at hrs; cases hrs
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF _ G hG _ =>
      obtain ⟨hA, hGo⟩ := ho
      cases hpos with
      | here =>
        have hts' := (TelRel.unique hd ihm hΘ' _ _ hΘ _ _).1 hts
        have hSp := TelRel.isPer hd ihm (fun _ => .plain) hΘ
        have htt := hSp.trans hts' (hSp.symm hts')
        exact (FieldRel.unique hd ihm (hF ts htt v hv) _ _ hF' _ _).1 (hA ts us hts')
      | there hpos' =>
        exact DesRel.positions hd L ds (fun i => hN (i + 1)) (hG _ hA) hGo _ _ _ _ _ _ _ _ _ hpos'
          _ hΘ' ts us hts v _ hv hF'

end

section

variable {sig : Signature} {ι : Interpretation} {v : Lifting.Variables}

/-! ## Recursive Results and Liftings of an Instance -/

/-- A type of the shape of an instance, at the nesting of an instance, is an instance of the same
declared type, at the same sorts and grades. -/
theorem Term.Similar.inst_inv {k : Nat} {Γ Δ : Scope} {ns : List (Nest Name)} {D : Name}
    {qs : List Quality} {ls₁ : List (Level k)} {ps : List Grade} {as₁ : InstanceArgs k Γ Δ}
    {A₂ : Term k Γ} :
    Term.Similar (.inst ns) (.inst D qs ls₁ ps as₁) A₂ →
      ∃ (ls₂ : List (Level k)) (as₂ : InstanceArgs k Γ Δ),
        A₂ = .inst D qs ls₂ ps as₂ ∧ InstanceArgs.Similar ns as₁ as₂
  | .inst h => ⟨_, _, rfl, h⟩

/-- The recursive result of a term of an instance of a codata type of `Σ`, at the nesting of an
instance, is a corecursor of a lifting of this type, as the rule gives it. -/
theorem Term.NestedResult.inst_inv {k : Nat} (hd : sig.Distinct) {Γ : Scope} {ρ : Lifting k Γ Γ}
    {φ : Name → Term k (.var :: Γ)} {ns : List (Nest Name)} {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
    {as : InstanceArgs k Γ decl.scope} {t e : Term k Γ}
    (hres : Term.NestedResult sig v ρ φ (.inst ns) (.inst D qs ls ps as) t e) :
    ∃ (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (S : List Nat) (ms : List (Lifting.Result k)) (Δ' : Scope) (as' : InstanceArgs k Γ Δ')
      (nms : List Name)
      (body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms)
      (gs : CorecBranches k Γ),
      e = .corec v.recursion (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms.map (·.level))
        (v.grades ps ms) (.snoc (e := .var) as' t) .nil (.cons 0 .nil [] .nil) gs ∧
      InstanceArgs.Lifts sig v ρ ns as S ms as' ∧
      .typeDeclaration (decl.lifting D S nms body) ∈ sig ∧
      (∀ i d, nms[i]? = some d →
        ∃ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
          (_ : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) (g : _),
        gs.get i = some ⟨0, 0, ps₁.length, g⟩) ∧
      (∀ i d (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length) (g : Term k (Γ.extend ps₁.length)),
        nms[i]? = some d → (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        gs.get i = some ⟨0, 0, ps₁.length, g⟩ →
        Term.NestedResult sig v (ρ.liftN ps₁.length)
          (fun E => (φ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
          (B.nest (fun _ => none)
            (Nesting.liftN ps₁.length (hpos.nesting (Nesting.ofArgs ns))))
          ((B.substLevels (ls.getFin hl)).subst
            (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))
          (t.observation D qs ls ps as d ps₁) g) := by
  generalize hA : Term.inst D qs ls ps as = A at hres
  cases hres with
  | inst h₂ _ hq₂ hl₂ hp₂ has₂ _ hL₂ _ hgs₂ hgt₂ =>
    injection hA with _ _ hD hqs hls hps has
    subst hD hqs hls hps
    obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h h₂
    cases eq_of_heq hT
    cases eq_of_heq has
    exact ⟨hq₂, hl₂, hp₂, _, _, _, _, _, _, _, rfl, has₂, hL₂, hgs₂, hgt₂⟩

/-- An instance of a declared type of `Σ` lifted at the nesting of an instance is the instance of
a lifting of this type, as the rule gives it. -/
theorem Term.Lifts.inst_inv {k : Nat} (hd : sig.Distinct) {Γ' Γ : Scope} {ρ : Lifting k Γ' Γ}
    {ns : List (Nest Name)} {decl : TypeDeclaration} {D : Name}
    (hdecl : .typeDeclaration decl ∈ sig) (hD : D ∈ decl.names) {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ decl.scope} {e A' : Term k Γ'}
    {m : Lifting.Result k} (hL : Term.Lifts sig v ρ (.inst ns) e (.inst D qs ls ps as) A' m) :
    ∃ (S : List Nat) (ms : List (Lifting.Result k)) (Δ' : Scope) (as' : InstanceArgs k Γ' Δ'),
      A' = .inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms.map (·.level)) (v.grades ps ms)
        (.snoc (e := .var) as' e) ∧
      InstanceArgs.Lifts sig v ρ ns as S ms as' := by
  generalize hA : Term.inst D qs ls ps as = A at hL
  cases hL with
  | inst h₂ hD₂ _ _ _ _ has₂ _ _ _ =>
    injection hA with _ _ hD' hqs hls hps has
    subst hD' hqs hls hps
    cases Entry.typeDeclaration.inj (hd.entry_unique hdecl h₂ (n := D) hD hD₂)
    cases eq_of_heq has
    exact ⟨_, _, _, _, rfl, has₂⟩

/-- The type of a field that the graph of the types reads is a type. -/
theorem FieldRel.validType {n : Nat} {s : Quality} {A v : Term 0 []} {F : TermRel}
    (hd : sig.Distinct) (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F)
    (hA : Computesι sig ι A v) : ValidType₀ sig ι A := by
  cases hF with
  | univ _ hu =>
    exact ⟨hd, v, v, _, hA, hA, .univ n (levelRel_univ_iff.2 hu), .univ n (levelRel_univ_iff.2 hu),
      fun _ _ => .rfl⟩
  | univBelow _ m _ hu => exact ⟨hd, v, v, _, hA, hA, .univ m hu, .univ m hu, fun _ _ => .rfl⟩
  | prop hu =>
    exact ⟨hd, v, v, fun _ _ => _, hA, hA, .prop n _ (levelRel_prop_iff.2 hu) fun _ _ => .rfl,
      .prop n _ (levelRel_prop_iff.2 hu) fun _ _ => .rfl, fun _ _ => .rfl⟩
  | propBelow m _ hu =>
    exact ⟨hd, v, v, fun _ _ => _, hA, hA, .prop m _ hu fun _ _ => .rfl,
      .prop m _ hu fun _ _ => .rfl, fun _ _ => .rfl⟩

/-! ## Soundness of the Recursive Results -/

-- ADE: none.
/-- The relation `x.2` given at a position that holds the type `D` of the block relates terms whose
recursive results are equal terms of the motive of `D` at the first one. -/
def ResultLeaf (sig : Signature) (ι : Interpretation) (ρ₁ : Lifting 0 [] [])
    (φ₁ φ₂ : Name → Term 0 [.var]) (D : Name) (x : NestLeaf) : Prop :=
  ∀ b, ρ₁.block D = some b → ∀ a a', x.2 a a' →
    ValidEqTerm₀ sig ι ((φ₁ D).subst₀ (Subst₀.single a)) ((φ₂ D).subst₀ (Subst₀.single a'))
      (b.motive.subst₀ (Subst₀.single a))

-- ADE: none.
/-- The recursive results of the closed terms `t₁` and `t₂`, of the type `A₁`, whose nesting is
`ν`, and of any type of the same shape, are equal terms of `A₁` lifted at `t₁`, when this type
lifted is a type: `ρ₁` and `ρ₂` give the types of the block their motives, and `φ₁` and `φ₂` the
results of the terms of these types, on each side. -/
def ResultSoundAt (sig : Signature) (ι : Interpretation) (v : Lifting.Variables)
    (ρ₁ ρ₂ : Lifting 0 [] []) (φ₁ φ₂ : Name → Term 0 [.var]) (ν : Nest Name)
    (A₁ t₁ t₂ : Term 0 []) : Prop :=
  ∀ (A₂ e₁ e₂ A' : Term 0 []) (m : Lifting.Result 0), Term.Similar ν A₁ A₂ →
    Term.NestedResult sig v ρ₁ φ₁ ν A₁ t₁ e₁ → Term.NestedResult sig v ρ₂ φ₂ ν A₂ t₂ e₂ →
    Term.Lifts sig v ρ₁ ν t₁ A₁ A' m → ValidType₀ sig ι A' → ValidEqTerm₀ sig ι e₁ e₂ A'

/-- A closed lifting, under the variables of a telescope, substituted by closed arguments of the
telescope. -/
theorem Lifting.Substitutes.closedArgs (ρ : Lifting 0 [] []) {ps : List Parameter}
    (ts : Args 0 [] ps) :
    Lifting.Substitutes ts.toSubst ts.toSubst (ρ.liftN ps.length) ρ :=
  Lifting.Substitutes.ofLiftN (ρ := ρ) (fun x => nomatch x) ps.length (fun x => nomatch x)
    (fun x => nomatch x) fun x => by
      have hid : ∀ {a} (y : Var [] a), ρ.ren y = y := fun y => nomatch y
      have e₁ : (ρ.liftN ps.length).ren x = x := by
        rw [Lifting.liftN_ren]
        exact Ren.liftN_id_of ps.length hid x
      rw [e₁, Term.rename_id_of (Ren.liftN_id_of _ hid)]

/-- The result of a term of a type of the block, renamed under the arguments of a destructor and
substituted by closed arguments, is this result. -/
theorem Term.subst_lift_toSubst_rename {ps : List Parameter} (ts : Args 0 [] ps)
    (t : Term 0 [.var]) :
    (t.rename (Ren.lift (Ren.weakenN ps.length))).subst (Subst.lift ts.toSubst) = t :=
  have key : ∀ {a} (x : Var [.var] a),
      Subst.lift ts.toSubst (Ren.lift (Ren.weakenN ps.length) x) = Var.eta x
    | _, .zero => rfl
    | _, .succ x => nomatch x
  (Term.subst_rename_of key t).trans (Term.subst_id_of (fun _ => rfl) t)

/-- Two terms that the equality of a type relates, both head normal forms, are equal terms of the
type. -/
theorem HasEq.validEqTerm_whnf (hd : sig.Distinct) {A v t u : Term 0 []} {R : TermRel}
    (hA : Computesι sig ι A v) (hR : HasEq sig ι v R) (ht : Whnf (sig.interpret ι) t)
    (hu : Whnf (sig.interpret ι) u) (h : R t u) : ValidEqTerm₀ sig ι t u A :=
  ⟨⟨hd, v, v, R, hA, hA, hR, hR, fun _ _ => .rfl⟩,
    fun _ => ⟨v, t, u, R, hA, ⟨.refl _, ht⟩, ⟨.refl _, hu⟩, hR, h⟩,
    fun ⟨v', hv', _⟩ => by
      cases Computesι.det hd hA hv'
      exact ⟨v, R, hA, hR, h⟩⟩

-- ADE: none.
/-- The recursive results of two terms of an instance of a codata type of `Σ` without recursive
destructor, at the nesting of an instance, are equal terms of the instance lifted, when the results
of their observations are, destructor by destructor, at equal arguments: the results are
corecursors of the lifting of the type, which the signature declares, and whose destructors are
those of the type lifted, and the equality of the destructors of the lifting, which the meaning of
the instance lifted gives, relates their observations, which step to their branches. -/
theorem ResultSoundAt.inst (hd : sig.Distinct)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    {ρ₁ ρ₂ : Lifting 0 [] []} {φ₁ φ₂ : Name → Term 0 [.var]} {n : Nat} {decl : TypeDeclaration}
    {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope}
    (hrec : ∀ r ∈ (T.body (.ofLists qs ps hq hp)).recursion decl.names, r = none)
    {ns : List (Nest Name)} {t₁ t₂ : Term 0 []}
    (horacle : ∀ (ls₂ : List (Level 0)) (as₂ : InstanceArgs 0 [] decl.scope) (d : Name)
      (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
      (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ),
      ∃ SΘ, TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (t₁.observation D qs ls ps as) as.toSubst)) SΘ ∧
        ∀ ts us : Args 0 [] ps₁, SΘ ts.terms us.terms →
          ResultSoundAt sig ι v ρ₁ ρ₂ φ₁ φ₂
            (B.nest (fun _ => none)
              (Nesting.liftN ps₁.length (hpos.nesting (Nesting.ofArgs ns))))
            ((B.substLevels (ls.getFin hl)).subst
              (Subst.append (hpos.obsSubst (t₁.observation D qs ls ps as) as.toSubst) ts.toSubst))
            ((t₁.observation D qs ls ps as d ps₁).subst ts.toSubst)
            ((t₂.observation D qs ls₂ ps as₂ d ps₁).subst us.toSubst)) :
    ResultSoundAt sig ι v ρ₁ ρ₂ φ₁ φ₂ (.inst ns) (.inst D qs ls ps as) t₁ t₂ := by
  intro A₂ e₁ e₂ A' mA hsim h₁ h₂ hL hA'
  have hρ₁ : ∀ {a} (x : Var [] a), ρ₁.motive x = none := fun x => nomatch x
  have hρ₂ : ∀ {a} (x : Var [] a), ρ₂.motive x = none := fun x => nomatch x
  have hid₁ : ∀ {a} (x : Var [] a), ρ₁.ren x = x := fun x => nomatch x
  obtain ⟨ls₂, as₂, rfl, hsas⟩ := hsim.inst_inv
  obtain ⟨_, _, _, S, ms₁, Δ', as', nms, body, gs₁, rfl, has₁, hLm, hgs₁, hgt₁⟩ :=
    h₁.inst_inv hd h
  obtain ⟨_, hl₂, _, S₂, ms₂, Δ₂', as₂', nms₂, body₂, gs₂, rfl, has₂, hLm₂, hgs₂, hgt₂⟩ :=
    h₂.inst_inv hd h
  obtain rfl := InstanceArgs.Lifts.positions_eq hρ₁ hρ₂ has₁ has₂
  have he := Entry.typeDeclaration.inj (hd.entry_unique hLm hLm₂ (n := Lifting.name D S)
    List.mem_cons_self List.mem_cons_self)
  obtain rfl := TypeDeclaration.lifting_destructors he
  obtain rfl := TypeDeclaration.lifting_body he
  have hDn : D ∈ decl.names := h.2.2 ▸ TypeDeclaration.codata_name_mem_names h.2.1
  obtain ⟨S', ms'', Δ'', as'', rfl, has'⟩ := hL.inst_inv hd h.1 hDn
  obtain ⟨rfl, rfl, hsg⟩ := InstanceArgs.Lifts.unique hd has₁ has'
  cases hsg
  have hq' : (qs ++ [v.quality]).length = decl.sorts + 1 := by
    rw [List.length_append, hq]
    rfl
  have hp' : (v.grades ps ms₁).length = decl.liftingGrades S := v.length_grades hp has₁.length_eq
  have hp₂' : (v.grades ps ms₂).length = decl.liftingGrades S := v.length_grades hp has₂.length_eq
  have hl' : (ls ++ ms₁.map (·.level)).length = decl.levels + S.length := by
    rw [List.length_append, hl, List.length_map, has₁.length_eq]
  have hl₂' : (ls₂ ++ ms₂.map (·.level)).length = decl.levels + S.length := by
    rw [List.length_append, hl₂, List.length_map, has₂.length_eq]
  obtain ⟨hΔ, -⟩ := has₁.instantiates hρ₁ S
    (fun i => (decl.liftingMotive S (.ofLists (qs ++ [v.quality]) (v.grades ps ms₁) hq' hp')
      i).substLevels ((ls ++ ms₁.map (·.level)).getFin hl'))
    (fun _ _ => Iff.rfl)
    (fun j h₁ h₂ => TypeDeclaration.liftingMotive_ofLists has₁.nodup hq' hl has₁.length_eq hl' hp
      hp' j h₁ h₂)
  subst hΔ
  -- The lifting, its type and its destructors.
  let declL := decl.lifting D S nms body
  let TL : CodataType declL.sorts declL.grades declL.levels declL.scope :=
    { name := Lifting.name D S
      usage := fun _ _ => .unrestrictedUnrestricted
      positive := fun _ => false
      destructors := nms
      body := body }
  have hTLmem : TL ∈ declL.codataTypes := List.mem_cons_self
  have hTL : sig.HasCodataType (Lifting.name D S) declL TL := ⟨hLm, hTLmem, rfl⟩
  have hLf := hlifts h.1 hDn hLm
  let I' : Instance (decl.sorts + 1) (decl.liftingGrades S) :=
    .ofLists (qs ++ [v.quality]) (v.grades ps ms₁) hq' hp'
  -- The type has no recursive destructor at the instance of the type declaration that each
  -- instance of the lifting at the qualities and grades of the instance holds.
  have hFrecAt : ∀ (ms : List (Lifting.Result 0)) (hpm : (v.grades ps ms).length = decl.liftingGrades S),
      ∀ T' ∈ decl.codataTypes, T'.name = D →
        ∀ r ∈ (T'.body (Instance.ofLists (qs ++ [v.quality]) (v.grades ps ms) hq' hpm).lifted).recursion
          decl.names, r = none := fun ms hpm T' hT' hn' => by
    cases eq_of_heq (hd.hasCodataType_unique ⟨h.1, hT', hn'⟩ h).2
    rw [Instance.lifted_ofLists qs ps v.quality _ hq hp]
    exact hrec
  have hFrec := hFrecAt ms₁ hp'
  have hrecL : ∀ r ∈ (TL.body I').recursion declL.names, r = none := hLf.recursion I' hFrec
  -- The observations of the results.
  let L := ls.getFin hl
  let L₂ := ls₂.getFin hl₂
  let L' := (ls ++ ms₁.map (·.level)).getFin hl'
  let f₁ := t₁.observation D qs ls ps as
  let f₂ := t₂.observation D qs ls₂ ps as₂
  let θ' : Subst 0 [] (.var :: decl.scope.lifted S) :=
    (InstanceArgs.snoc (e := .var) as' t₁).toSubst
  generalize he₁ : Term.corec v.recursion (Lifting.name D S) (qs ++ [v.quality])
    (ls ++ ms₁.map (·.level)) (v.grades ps ms₁) (.snoc (e := .var) as' t₁) .nil
    (.cons 0 .nil [] .nil) gs₁ = e₁
  generalize he₂ : Term.corec v.recursion (Lifting.name D S) (qs ++ [v.quality])
    (ls₂ ++ ms₂.map (·.level)) (v.grades ps ms₂) (.snoc (e := .var) as₂' t₂) .nil
    (.cons 0 .nil [] .nil) gs₂ = e₂
  let o₁' : Observations := e₁.observation (Lifting.name D S) (qs ++ [v.quality])
    (ls ++ ms₁.map (·.level)) (v.grades ps ms₁) (.snoc (e := .var) as' t₁)
  let o₂ : Observations := e₂.observation (Lifting.name D S) (qs ++ [v.quality])
    (ls₂ ++ ms₂.map (·.level)) (v.grades ps ms₂) (.snoc (e := .var) as₂' t₂)
  have hC : ∀ {nL : Nat} {s' : Quality} {rs : Nat → Option TermRel} {S' : ObsRel}
      {o₂' : Observations}, (∀ i, rs i = none) →
      DesRel sig ι nL (fun m _ => levelRel sig ι m) s' rs ((body I').substLevels L') @θ' S' →
      ObsEquiv sig ι s' o₂' o₂ → S' o₁' o₂' := by
    intro nL s' rs S' o₂' hrs hDes hO
    refine DesRel.of_positions hd L' (body I') hrs hDes ?_
    intro d' p' q' ς' ps₁' Ξ' Θ' B' ψ' hpos' SΘ' hΘ' ts' us' hts' vB F' hvB hF'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hpos'.mem
    obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, hpos, g₁, hg₁⟩ := hgs₁ i d' hi
    obtain ⟨_, _, _, ps₂, _, _, _, _, hpos₂, g₂, hg₂⟩ := hgs₂ i d' hi
    obtain ⟨-, rfl⟩ := hpos.params_unique (hd.destructors_nodup h) hpos₂
    obtain ⟨mr, hps, hΘeq, hBL⟩ := TypeDeclaration.Lifts.observation (v := v) hd h hLf
      (ρ := ρ₁) hρ₁ hq hl hp hq' hl' hp' has₁ t₁ hpos hpos' o₁'
    subst hps
    have ht₁ : t₁.rename ρ₁.ren = t₁ := Term.rename_id_of hid₁ t₁
    rw (transparency := .default) [ht₁] at hΘeq hBL
    obtain ⟨SΘ, hΘ, hsound⟩ := horacle ls₂ as₂ d' p q ς ps₁ Ξ Θ B ψ hpos
    -- The arguments of the destructor of the lifting are those of the destructor of the type.
    have hΘ'' : TelRel sig ι nL (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
        (((Θ.substLevels L).subst (hpos.obsSubst f₁ as.toSubst)).scale (v.recursion * mr.factor)) SΘ' := by
      have e := hΘeq
      rw [Telescope.rename_id_of hid₁] at e
      exact e ▸ hΘ'
    have ihm : ∀ m, m < max nL n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSS := TelRel.unique hd ihm (TelRel.levelLe (Nat.le_max_left nL n) hΘ'') _ _
      (TelRel.levelLe (Nat.le_max_right nL n) (hΘ.scale (v.recursion * mr.factor)))
    obtain ⟨ts, hts⟩ := Args.exists_terms_map (Parameter.scale (v.recursion * mr.factor)) ps₁ ts'
    obtain ⟨us, hus⟩ := Args.exists_terms_map (Parameter.scale (v.recursion * mr.factor)) ps₁ us'
    have hSΘ : SΘ ts.terms us.terms := (hSS _ _).1 (hts ▸ hus ▸ hts')
    -- The results of the observations, at the arguments.
    have hφ₁ : (fun E => ((φ₁ E).rename (Ren.lift (Ren.weakenN ps₁.length))).subst
        (Subst.lift ts.toSubst)) = φ₁ := funext fun E => Term.subst_lift_toSubst_rename ts (φ₁ E)
    have hφ₂ : (fun E => ((φ₂ E).rename (Ren.lift (Ren.weakenN ps₁.length))).subst
        (Subst.lift us.toSubst)) = φ₂ := funext fun E => Term.subst_lift_toSubst_rename us (φ₂ E)
    have hN₁ := (hgt₁ i d' p q ς ps₁ Ξ Θ B ψ g₁ hi hpos hg₁).subst
      (Lifting.Substitutes.closedArgs ρ₁ ts)
    rw [hφ₁, Term.subst_append] at hN₁
    have hN₂ := (hgt₂ i d' p q ς ps₁ Ξ Θ B ψ g₂ hi hpos hg₂).subst
      (Lifting.Substitutes.closedArgs ρ₂ us)
    rw [hφ₂, Term.subst_append] at hN₂
    have hsim' : Term.Similar
        (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hpos.nesting (Nesting.ofArgs ns))))
        ((B.substLevels L).subst (Subst.append (hpos.obsSubst f₁ as.toSubst) ts.toSubst))
        ((B.substLevels L₂).subst (Subst.append (hpos.obsSubst f₂ as₂.toSubst) us.toSubst)) := by
      have hs := (Term.similar_subst (fun _ => none) L L₂
        (Subst.Similar.liftN ps₁.length (hpos.similar f₁ f₂ hsas.toSubst)) B).subst ts.toSubst us.toSubst
      rwa [Term.subst_append, Term.subst_append] at hs
    have hL' := hBL.subst (Lifting.Substitutes.closedArgs ρ₁ ts)
    rw [Term.rename_id_of (Ren.liftN_id_of _ hid₁), Term.subst_append,
      Term.subst_toSubst_cast _ _ ts ts' hts, Term.subst_append] at hL'
    have hE := hsound ts us hSΘ _ _ _ _ mr hsim' hN₁ hN₂ hL' (hF'.validType hd hvB)
    have hFg : F' (g₁.subst ts.toSubst) (g₂.subst us.toSubst) := hF'.of_validEqTerm hvB hE
    -- The observations of the corecursors step to their branches.
    have hiL : declL.codataCases[i]? = some (0, TL, d') := by
      show (List.map (fun c => (0, TL, c)) nms ++ [])[i]? = _
      rw [List.append_nil, List.getElem?_map, hi]
      rfl
    have hrecN : (TL.body I').resultName declL.names d' = none :=
      (hpos'.resultName declL.names (hd.destructors_nodup hTL)).trans
        (hLf.blockName_pos I' hFrec hpos')
    -- The destructor has no result of the block at the instance of the second side either.
    let I₂' : Instance (decl.sorts + 1) (decl.liftingGrades S) :=
      .ofLists (qs ++ [v.quality]) (v.grades ps ms₂) hq' hp₂'
    obtain ⟨_, _, _, _, _, _, _, _, ⟨hpos₂'⟩⟩ := Destructors.exists_pos (TL.body I₂') hpos'.mem
    have hrecN₂ : (TL.body I₂').resultName declL.names d' = none :=
      (hpos₂'.resultName declL.names (hd.destructors_nodup hTL)).trans
        (hLf.blockName_pos I₂' (hFrecAt ms₂ hp₂') hpos₂')
    have hr₁ : ∀ w, Computesι sig ι ((o₁' d' _).subst ts'.toSubst) w ↔
        Computesι sig ι (g₁.subst ts.toSubst) w := fun w => by
      subst he₁
      rw [Term.observation_subst_args, ← hts]
      exact Computesι.red_iff hd (Red.beta_stateless hTL hq' hl' hp' hiL hrecN hg₁ ts)
    have hr₂ : s' = .prop ∨ ∀ w, Computesι sig ι ((o₂' d' _).subst us'.toSubst) w ↔
        Computesι sig ι (g₂.subst us.toSubst) w := hO.imp_right fun hO' w =>
      (hO' d' _ us'.toSubst w).trans (by
        subst he₂
        rw [Term.observation_subst_args, ← hus]
        exact Computesι.red_iff hd (Red.beta_stateless hTL hq' hl₂' hp₂' hiL hrecN₂ hg₂ us))
    exact (hF'.congr_computes (hr₂.elim .inl fun h₂ => .inr ⟨hr₁, h₂⟩)).2 hFg
  -- The meaning of the instance lifted.
  obtain ⟨-, vA, -, R, hcA, -, hR, -, -⟩ := id hA'
  have hIA : Computesι sig ι
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t₁))
      (.inst (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms₁.map (·.level))
        (v.grades ps ms₁) (.snoc (e := .var) as' t₁)) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  cases Computesι.det hd hIA hcA
  have hrs : ∀ {α : Type} (f : Name → α) (i : Nat),
      ((TL.body I').recursionAt declL.names i).map f = none := fun f i => by
    rw [Destructors.recursionAt_eq_none hrecL i]
    rfl
  have hw₁ : Whnf (sig.interpret ι) e₁ := he₁ ▸ .corec ..
  have hw₂ : Whnf (sig.interpret ι) e₂ := he₂ ▸ .corec ..
  have hc₁ : e₁.CorecObservations (Lifting.name D S) o₁' :=
    ⟨_, _, _, _, _, _, _, _, _, he₁.symm, by subst he₁; rfl⟩
  have hc₂ : e₂.CorecObservations (Lifting.name D S) o₂ :=
    ⟨_, _, _, _, _, _, _, _, _, he₂.symm, by subst he₂; rfl⟩
  refine HasEq.validEqTerm_whnf hd hIA hR hw₁ hw₂ ?_
  rcases HasEq.instCodata_inv hd hTL hq' hl' hp' hR with ⟨-, S', hS', rfl⟩ | ⟨-, S', hS', hRb⟩
  · refine ⟨fun N a b => N = Lifting.name D S ∧ a = e₁ ∧ b = e₂, fun T' hT' a b hX => ?_,
      rfl, rfl, rfl⟩
    cases List.mem_singleton.1 hT'
    obtain ⟨-, rfl, rfl⟩ := hX
    exact ⟨o₁', o₂, hc₁, hc₂, hC (hrs _) (hS' _ TL hTLmem) (.inr fun _ _ _ _ => .rfl)⟩
  · refine (hRb _ _).2 ⟨fun N => N = Lifting.name D S, fun T' hT' _ => ?_, rfl⟩
    cases List.mem_singleton.1 hT'
    exact ⟨o₁', hC (hrs _) (hS' _ TL hTLmem) (.inl rfl)⟩

/-- The nestings of the variables of the scope of a position are the same at instantiated levels,
and so is the nesting of the result of its destructor. -/
theorem Destructors.Pos.nest_substLevels {α : Type} {k k' : Nat} (L : Fin k → Level k') {d : Name}
    {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {nms : List Name} → {ds : Destructors k Γ nms} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : ds.Pos d p q ς Ξ Θ B ψ) →
      (ν : Nesting α Γ) →
        B.nest (fun _ => none) (Nesting.liftN ps.length (hpos.nesting @ν)) =
          (B.substLevels L).nest (fun _ => none)
            (Nesting.liftN ps.length ((hpos.substLevels L).nesting @ν))
  | _, _, _, _, _, B, _, .here, _ => (Term.nest_substLevels (fun _ => none) L B).symm
  | _, _, _, _, _, _, _, .there h, _ => h.nest_substLevels L _

/-- Related nestings stay related when the last two are replaced by nestings equal to them. -/
theorem Nest.Rel₃.cast {α β γ : Type} {r : α → β → γ → Prop} {n : Nest α} {m m' : Nest β}
    {o o' : Nest γ} (h : Nest.Rel₃ r n m o) (hm : m = m') (ho : o = o') : Nest.Rel₃ r n m' o' :=
  hm ▸ ho ▸ h

/-- The observations `f₁` and `f₂`, which compute as `o₁` and `o₂`, do at closed arguments, for a
destructor, or the quality is that of the propositions. -/
theorem ObsEquiv.at {s : Quality} {f₁ f₂ o₁ o₂ : Observations}
    (hf₁ : ObsEquiv sig ι s f₁ o₁) (hf₂ : ObsEquiv sig ι s f₂ o₂) (d : Name)
    (ps : List Parameter) (τ₁ τ₂ : Subst 0 [] (Scope.extend [] ps.length)) :
    s = .prop ∨ ((∀ w, Computesι sig ι ((f₁ d ps).subst τ₁) w ↔
      Computesι sig ι ((o₁ d ps).subst τ₁) w) ∧
      ∀ w, Computesι sig ι ((f₂ d ps).subst τ₂) w ↔ Computesι sig ι ((o₂ d ps).subst τ₂) w) := by
  rcases hf₁ with h₁ | h₁
  · exact .inl h₁
  rcases hf₂ with h₂ | h₂
  · exact .inl h₂
  exact .inr ⟨fun w => h₁ d ps τ₁ w, fun w => h₂ d ps τ₂ w⟩

mutual

-- ADE: none.
/-- The recursive results of two terms that the equality of a type relates, by the graph of the
nestings, are equal terms of the type lifted at the first one, in a signature whose names are
distinct and whose liftings are those of its types: at each position, the relation given relates
terms whose results are equal terms of the motive of the type that the position holds, and does
not read their computation. -/
theorem NestRel.resultSound (hd : sig.Distinct)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    {ρ₁ ρ₂ : Lifting 0 [] []} {φ₁ φ₂ : Name → Term 0 [.var]} {n : Nat} {sT s : Quality}
    {τ : Nest NestLeaf} {A₁ : Term 0 []} {F : TermRel} :
    NestRel sig ι n (fun m _ => levelRel sig ι m) sT s τ A₁ F →
      Nest.All (fun x => LeafCongr sig ι sT x.2) τ →
      ∀ {ν : Nest Name}, Nest.Rel (ResultLeaf sig ι ρ₁ φ₁ φ₂) ν τ →
      ∀ t₁ t₂, F t₁ t₂ → ResultSoundAt sig ι v ρ₁ ρ₂ φ₁ φ₂ ν A₁ t₁ t₂
  | .plain _ _, _, _, hν, _, _, _ => by
    cases hν with
    | plain =>
      intro A₂ e₁ e₂ A' l _ _ _ hL _
      exact (hL.not_avoidsLifted rfl fun x _ => nomatch x).elim
  | .direct _ _, _, _, hν, _, _, ht => by
    cases hν with
    | direct hr =>
      intro A₂ e₁ e₂ A' l _ h₁ h₂ hL _
      cases h₁ with
      | block hD₁ =>
        cases h₂ with
        | block _ =>
          cases hL with
          | block hD' =>
            cases Option.some.inj (hD₁.symm.trans hD')
            exact hr _ hD₁ _ _ ht
          | inst _ _ hn => exact absurd rfl (hn _)
        | inst _ hn => exact absurd rfl (hn _)
      | inst _ hn => exact absurd rfl (hn _)
  | .codata (ls := ls) h hq hl hp hA _ _ _ hrec _ hS, hτ, _, hν, _, _, ht => by
    subst hA
    cases hν with
    | inst hνs =>
      cases hτ with
      | inst hτs =>
        obtain ⟨w₁, w₂, hc₁, hc₂, o₁, o₂, hw₁, hw₂, hSo⟩ := ht
        exact ResultSoundAt.inst hd hlifts h hq hl hp hrec
          fun ls₂ as₂ d p q ς ps₁ Ξ Θ B ψ hpos =>
            NestDesRel.resultSound hd hlifts (hpos.substLevels (ls.getFin hl)) hS
              (Nesting.ofArgs_rel₃ hτs) (Nesting.ofArgs_rel₃ hνs) hSo
              (ObsEquiv.of_computes hd hc₁ hw₁) (ObsEquiv.of_computes hd hc₂ hw₂)
              (funext fun _ => funext fun x => (hpos.obsSubst_posSubstLevels _ _ _ x).symm)
              (hpos.nest_substLevels _ _)
  | .codataProp (ls := ls) h hq hl hp hA _ _ hrec _ hS, hτ, _, hν, _, _, ht => by
    subst hA
    cases hν with
    | inst hνs =>
      cases hτ with
      | inst hτs =>
        obtain ⟨o, hSo⟩ := ht
        exact ResultSoundAt.inst hd hlifts h hq hl hp hrec
          fun ls₂ as₂ d p q ς ps₁ Ξ Θ B ψ hpos =>
            NestDesRel.resultSound hd hlifts (hpos.substLevels (ls.getFin hl)) hS
              (Nesting.ofArgs_rel₃ hτs) (Nesting.ofArgs_rel₃ hνs) hSo (.inl rfl) (.inl rfl)
              (funext fun _ => funext fun x => (hpos.obsSubst_posSubstLevels _ _ _ x).symm)
              (hpos.nest_substLevels _ _)
termination_by structural h _ _ _ _ _ _ => h

-- ADE: none.
/-- At a position of a destructor in destructors that the graph of the nestings reads, at
instantiated levels, observations that compute as observations that the equality of the
destructors relates give, at equal arguments of the destructor, terms whose recursive results are
equal terms of its result lifted at the first one: the destructors before it are, one by one,
equal abstractions for them, or have a result with a position, on which the destructors after
them do not depend. -/
theorem NestDesRel.resultSound (hd : sig.Distinct)
    (hlifts : ∀ {decl : TypeDeclaration} {D : Name} {S : List Nat} {nms : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) nms},
      .typeDeclaration decl ∈ sig → D ∈ decl.names →
      .typeDeclaration (decl.lifting D S nms body) ∈ sig → decl.Lifts sig D S body)
    {ρ₁ ρ₂ : Lifting 0 [] []} {φ₁ φ₂ : Name → Term 0 [.var]} {n : Nat} {sT s : Quality}
    {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {nms : List Name} → {ds : Destructors 0 Γ nms} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : ds.Pos d p q ς Ξ Θ B ψ) →
      {ν' : Nesting NestLeaf Γ} → {θ : Subst 0 [] Γ} → {S : ObsRel} →
      NestDesRel sig ι n (fun m _ => levelRel sig ι m) sT s @ν' ds @θ S →
      Nesting.All (fun x => LeafCongr sig ι sT x.2) @ν' → {ν : Nesting Name Γ} →
      Nesting.Rel (ResultLeaf sig ι ρ₁ φ₁ φ₂) @ν @ν' → {o₁ o₂ f₁ f₂ : Observations} →
      S o₁ o₂ → ObsEquiv sig ι s f₁ o₁ → ObsEquiv sig ι s f₂ o₂ →
      ∀ {σ : (e : Scope.Entry) → Var Ξ e → Term 0 (Scope.extend [] e.params.length)},
      (σ = fun _ x => hpos.obsSubst f₁ θ x) → ∀ {νB : Nest Name},
      νB = B.nest (fun _ => none) (Nesting.liftN ps.length (hpos.nesting @ν)) →
      ∃ SΘ, TelRel sig ι n (fun m _ => levelRel sig ι m) .type (fun _ => .plain)
          (Θ.subst fun {e} x => σ e x) SΘ ∧
        ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
          ResultSoundAt sig ι v ρ₁ ρ₂ φ₁ φ₂ νB
            (B.subst (Subst.append (fun {e} x => σ e x) ts.toSubst))
            ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)
  | _, _, _, _, _, B, _, .here, _, _, _, .cons (SΘ := SΘ) hν hΘ F hF _ _ _ _, _, _, hRel, _, _, _,
      _, hSo, hf₁, hf₂, _, hσ, _, hνB => by
    subst hσ hνB
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    refine ⟨SΘ, hΘ, fun ts us hts => ?_⟩
    have htt := hSp.trans hts (hSp.symm hts)
    exact NestRel.resultSound hd hlifts (hF ts htt) .plain
      ((Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B).cast hν hν) _ _
      ((NestRel.congr_computes (hF ts htt) .plain (hf₁.at hf₂ d ps _ _)).2 (hSo.1 ts us hts))
  | _, _, _, _, _, B, _, .here, _, _, _, .nested (SΘ := SΘ) _ hΘ F hF _ _ _, hAll, _, hRel, _, _, _,
      _, hSo, hf₁, hf₂, _, hσ, _, hνB => by
    subst hσ hνB
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    refine ⟨SΘ, hΘ, fun ts us hts => ?_⟩
    have htt := hSp.trans hts (hSp.symm hts)
    have hAllB := Term.nest_all (p := fun x : NestLeaf => LeafCongr sig ι sT x.2)
      (mark := fun _ => none) (fun _ _ h => nomatch h) (Nesting.liftN_rel₃ ps.length hAll) B
    exact NestRel.resultSound hd hlifts (hF ts htt) hAllB
      (Term.nest_rel₃ (Nesting.liftN_rel₃ ps.length hRel) B) _ _
      ((NestRel.congr_computes (hF ts htt) hAllB (hf₁.at hf₂ d ps _ _)).2 (hSo.1 ts us hts))
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _,
      .cons (SΘ := SΘ) _ hΘ F hF hBresp G hG hresp, hAll, _, hRel, o₁, o₂, f₁, _, hSo, hf₁,
      hf₂, _, hσ, _, hνB => by
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ => .plain) hΘ
    have hFv : ∀ ts : Args 0 [] ps', SΘ ts.terms ts.terms →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts => by
      cases hF ts hts with
      | plain _ hF' => exact ⟨_, hF'⟩
    have hEp := AbstractionRel.isPer hSp
      (fun ts hts => NestRel.isPer hd ih .plain (hF ts hts)) hBresp
    have ho₁ := hEp.trans hSo.1 (hEp.symm hSo.1)
    have hfo : AbstractionRel SΘ F (f₁ d' ps') (o₁ d' ps') :=
      (AbstractionRel.congr_computes hSp hFv
        (hf₁.imp_right fun h => ⟨fun τ w => h d' ps' τ w, fun _ _ => .rfl⟩)).2 ho₁
    exact NestDesRel.resultSound hd hlifts hp (hG _ (hEp.trans hfo (hEp.symm hfo)))
      (Nesting.lift_rel₃ hAll) (Nesting.lift_rel₃ hRel) ((hresp _ _ hfo o₁ o₂).2 hSo.2) hf₁ hf₂
      hσ hνB
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') hp, _, _, _, .nested _ _ _ _ _ _ hG, hAll,
      _, hRel, _, _, f₁, _, hSo, hf₁, hf₂, _, hσ, _, hνB =>
    NestDesRel.resultSound hd hlifts hp (hG (f₁ d' ps')) (Nesting.lift_rel₃ hAll)
      (Nesting.lift_rel₃ hRel) hSo.2 hf₁ hf₂ hσ hνB
termination_by structural _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ => h

end

end

end Sic.Core
