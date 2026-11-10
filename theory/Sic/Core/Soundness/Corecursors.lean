module

public import Sic.Core.Soundness.Recursors

/-!
# Soundness of the Rules of the Corecursors

The rules `(d)`, `(d_≡)`, `(corec)`, `(corec_≡)`, `(β)` and `(η_d)` of annex 13 of RFC 36 keep the
meaning of annex 16, as `Rules` proves it of the other rules, from the meaning of the codata types:
the equality of the corecursors is proved by coinduction, and a recursive destructor resumes its
position, a constructor of the type of positions of the prelude, which the recursors on its
constructor and on the pairs of a packing eliminate, as `Recursors` reduces them.

ADE prove the validity of the rules of their eliminators in
`Definition/LogicalRelation/Substitution/Introductions/`, one module for each type.
-/

@[expose] public section

namespace Sic.Core

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Observations

An observation of two equal closed terms of an instance of a codata type of a meaningful declaration
computes, by the reduction of their terms, then by `(β_⟶)`, as the observations of the corecursors
that both compute to, which the equality of the instance relates, whatever the instance that an
observation carries; the destructors before the one observed are, in its telescope and its result,
the observations of the term, which compute as those of its corecursor, so that the equality of the
destructors relates them, from the first destructor to the observed one.
On a proposition, whose proofs need not compute, the truth of the instance gives abstractions that
its destructors relate, and every result is a proposition, whose truth holds of any term, so that
the observations of the proofs need not compute.
The results of the destructors are types at every pair of equal substitutions of their context,
which the destructors of a meaningful declaration give, so that the type of an observation is a
type. -/

/-- An observation reduces as its term does. -/
theorem RedStar.obs {sig' : Signature} {k : Nat} {Γ Δ : Scope} {D : Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {d : Name} {bs : Terms k Γ}
    {t t' : Term k Γ} (h : RedStar sig' t t') :
    RedStar sig' (.obs D qs ls ps as t d bs) (.obs D qs ls ps as t' d bs) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.obs h) ih

/-- A term computes to the canonical terms of the terms it reduces to, in a signature whose names
are distinct. -/
theorem Computesι.redStar_iff (hd : sig.Distinct) {t t' v : Term 0 []}
    (h : RedStar (sig.interpret ι) t t') : Computesι sig ι t v ↔ Computesι sig ι t' v := by
  induction h with
  | refl => exact .rfl
  | step h _ ih => exact (Computesι.red_iff hd h).trans ih

/-- An observation of a corecursor computes as the observation of the same corecursor by the same
destructor at the same arguments, whatever instance each observation carries, since `(β_⟶)` does
not read it, and the corecursor does not reduce. -/
theorem Computesι.obs_corec_iff {Δ₁ Δ₂ Δ : Scope} {D₁ D₂ D : Name} {qs₁ qs₂ qs : List Quality}
    {ls₁ ls₂ ls : List (Level 0)} {ps₁ ps₂ ps : List Grade} {as₁ : InstanceArgs 0 [] Δ₁}
    {as₂ : InstanceArgs 0 [] Δ₂} {as : InstanceArgs 0 [] Δ} {r : Grade} {ss : Terms 0 []}
    {Ss : States 0 []} {gs : CorecBranches 0 []} {d : Name} {bs : Terms 0 []} {v : Term 0 []} :
    Computesι sig ι (.obs D₁ qs₁ ls₁ ps₁ as₁ (.corec r D qs ls ps as ss Ss gs) d bs) v →
      Computesι sig ι (.obs D₂ qs₂ ls₂ ps₂ as₂ (.corec r D qs ls ps as ss Ss gs) d bs) v := by
  rintro ⟨hs, hv⟩
  cases hs with
  | refl => cases hv with | ne hn => cases hn with | obs hn => cases hn
  | step h hs =>
    cases h with
    | beta h hi hD hq hl hp hg hv' => exact ⟨.step (.beta h hi hD hq hl hp hg hv') hs, hv⟩
    | obs h => exact nomatch h

-- ADE: none.
/-- The observations `f` compute as the observations `o` at all closed arguments, or the quality `s`
is that of the propositions, whose proofs need not compute. -/
def ObsEquiv (sig : Signature) (ι : Interpretation) (s : Quality) (f o : Observations) : Prop :=
  s = .prop ∨ ∀ d ps (τ : Subst 0 [] (Scope.extend [] ps.length)) v,
    Computesι sig ι ((f d ps).subst τ) v ↔ Computesι sig ι ((o d ps).subst τ) v

/-- The equality of the terms of the type of a field relates the terms that compute as the terms it
relates, and any terms when the quality is that of the propositions. -/
theorem FieldRel.congr_computes {n : Nat} {s : Quality} {v : Term 0 []} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F) {a a' b b' : Term 0 []}
    (h : s = .prop ∨ ((∀ w, Computesι sig ι a w ↔ Computesι sig ι a' w) ∧
      ∀ w, Computesι sig ι b w ↔ Computesι sig ι b' w)) : F a b ↔ F a' b' := by
  cases hF with
  | univ hs _ | univBelow hs _ _ _ =>
    rcases h with h | ⟨ha, hb⟩
    · exact absurd (hs.symm.trans h) (by decide)
    · simp only [TermRel.computed, ha, hb]
  | prop _ | propBelow _ _ _ => exact .rfl

/-- The equality of the abstractions for a destructor relates the abstractions that compute as the
abstractions it relates, at all closed arguments, and any abstractions when the quality is that of
the propositions. -/
theorem AbstractionRel.congr_computes {n : Nat} {s : Quality} {ps : List Parameter}
    {SΘ : FieldsRel} {F : Terms 0 [] → TermRel} (hSp : IsPer SΘ)
    (hF : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
      ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms))
    {f₁ f₂ g₁ g₂ : Term 0 (Scope.extend [] ps.length)}
    (h : s = .prop ∨ ((∀ τ w, Computesι sig ι (f₁.subst τ) w ↔ Computesι sig ι (g₁.subst τ) w) ∧
      ∀ τ w, Computesι sig ι (f₂.subst τ) w ↔ Computesι sig ι (g₂.subst τ) w)) :
    AbstractionRel SΘ F f₁ f₂ ↔ AbstractionRel SΘ F g₁ g₂ := by
  have key : ∀ ts us : Args 0 [] ps, SΘ ts.terms us.terms →
      (F ts.terms (f₁.subst ts.toSubst) (f₂.subst us.toSubst) ↔
        F ts.terms (g₁.subst ts.toSubst) (g₂.subst us.toSubst)) := fun ts us hts => by
    obtain ⟨v, hv⟩ := hF ts (hSp.trans hts (hSp.symm hts))
    exact hv.congr_computes (h.imp_right fun ⟨h₁, h₂⟩ => ⟨h₁ _, h₂ _⟩)
  exact ⟨fun h' ts us hts => (key ts us hts).1 (h' ts us hts),
    fun h' ts us hts => (key ts us hts).2 (h' ts us hts)⟩

/-- At observations related by the equality of destructors, whose first destructor `d` is not
recursive, the observations `f₁` and `f₂` that compute as them are, for `d`, equal terms of its
result at equal arguments, and the equality of the destructors after `d`, with `f₁` for `d`, relates
them. -/
theorem DesRel.head (hd : sig.Distinct) {n : Nat} {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
    {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
    {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (.cons (d := d) p q Θ B ψ ds) @θ S)
    (hr : rs 0 = none) {o₁ o₂ f₁ f₂ : Observations} (hS : S o₁ o₂)
    (hf₁ : ObsEquiv sig ι s f₁ o₁) (hf₂ : ObsEquiv sig ι s f₂ o₂) :
    (∀ ts us : Args 0 [] ps, EqSubst sig ι (Context.empty.append (Θ.subst θ)) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)
        (B.subst (Subst.append θ ts.toSubst))) ∧
    ∃ S', DesRel sig ι n (fun m _ => levelRel sig ι m) s (fun i => rs (i + 1)) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ (f₁ d ps)) S' ∧ S' o₁ o₂ := by
  cases h with
  | recursive hrs => rw [hr] at hrs; cases hrs
  | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
    obtain ⟨hA, hGo⟩ := hS
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hFv : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts =>
      have ⟨v, hv⟩ := hB ts hts
      ⟨v, hF ts hts v hv⟩
    have hEp := AbstractionRel.isPer hSp (fun ts hts =>
      have ⟨_, hv⟩ := hFv ts hts
      FieldRel.isPer hd ih hv) hBresp
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    have hA' : AbstractionRel SΘ F (f₁ d ps) (f₂ d ps) :=
      (AbstractionRel.congr_computes hSp hFv (by
        rcases hc hf₁ with h₁ | h₁
        · exact .inl h₁
        rcases hc hf₂ with h₂ | h₂
        · exact .inl h₂
        exact .inr ⟨h₁, h₂⟩)).2 hA
    have ho₁ : AbstractionRel SΘ F (o₁ d ps) (o₁ d ps) := hEp.trans hA (hEp.symm hA)
    have hfo : AbstractionRel SΘ F (f₁ d ps) (o₁ d ps) :=
      (AbstractionRel.congr_computes hSp hFv (by
        rcases hc hf₁ with h₁ | h₁
        · exact .inl h₁
        exact .inr ⟨h₁, fun _ _ => .rfl⟩)).2 ho₁
    refine ⟨fun ts us hτ => ?_, G (f₁ d ps), hG _ (hEp.trans hfo (hEp.symm hfo)),
      (hresp _ _ hfo o₁ o₂).2 hGo⟩
    have hts := (TelRel.eqSubst_iff hd hΘ (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
      (fun _ _ h => by cases h) ts us).2 hτ
    have htt := hSp.trans hts (hSp.symm hts)
    obtain ⟨v, hv⟩ := hB ts htt
    exact (hF ts htt v hv).validEqTerm hd hv (hA' ts us hts)

/-- At observations related by the equality of destructors, whose first destructor `d` is recursive,
with results equal by `R`, the equality of the terms of a type of the graph, the observations `f₁`
and `f₂` that compute as them are, for `d`, related by `R` at equal arguments, and the equality of
the destructors after `d`, at any abstraction for `d`, relates them. -/
theorem DesRel.headRec (hd : sig.Distinct) {n : Nat} {s : Quality} {rs : Nat → Option TermRel}
    {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q : Grade}
    {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership ps.length}
    {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {θ : Subst 0 [] Γ} {S : ObsRel}
    (h : DesRel sig ι n (fun m _ => levelRel sig ι m) s rs (.cons (d := d) p q Θ B ψ ds) @θ S)
    {R : TermRel} (hr : rs 0 = some R) {v : Term 0 []}
    (hR : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) {o₁ o₂ f₁ f₂ : Observations}
    (hS : S o₁ o₂) (hf₁ : ObsEquiv sig ι s f₁ o₁) (hf₂ : ObsEquiv sig ι s f₂ o₂) :
    (∀ ts us : Args 0 [] ps, EqSubst sig ι (Context.empty.append (Θ.subst θ)) ts.toSubst us.toSubst →
      R ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)) ∧
    ∀ f, ∃ S', DesRel sig ι n (fun m _ => levelRel sig ι m) s (fun i => rs (i + 1)) ds
      (Subst.snoc (e := .secondOrder ps ψ) θ f) S' ∧ S' o₁ o₂ := by
  cases h with
  | cons _ _ _ _ _ _ _ _ hrs => rw [hr] at hrs; cases hrs
  | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R' hrs hΘ G hG =>
    rw [hr] at hrs
    cases hrs
    obtain ⟨hA, hGo⟩ := hS
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    refine ⟨fun ts us hτ => ?_, fun f => ⟨G, hG f, hGo⟩⟩
    have hts := (TelRel.eqSubst_iff hd hΘ (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
      (fun _ _ h => by cases h) ts us).2 hτ
    refine (hR.congr_computes ?_).1 (hA ts us hts)
    rcases hc hf₁ with h₁ | h₁
    · exact .inl h₁
    rcases hc hf₂ with h₂ | h₂
    · exact .inl h₂
    exact .inr ⟨fun w => (h₁ _ w).symm, fun w => (h₂ _ w).symm⟩

-- ADE: none.
/-- At a position of a destructor `d` in destructors equal in a sort `κ` at two closed substitutions
of their scope, whose recursive destructors `rs` gives, of the instances `inst D` of the block,
observations that compute as observations related by the equality of the destructors, at the
relations of the recursive destructors that are the equalities of the instances, give results of
`d` that are equal types at equal arguments, and are, for `d`, equal terms of its result at equal
arguments: the destructors before `d` are, one by one, equal abstractions for them, and a recursive
one, on which the destructors after it do not depend, gives terms of an instance. -/
theorem Destructors.Pos.sound (hd : sig.Distinct) {κ : Universe 0} {d : Name} {p q : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} → {Ξ : Scope} →
      {Θ : Telescope 0 Ξ ps} → {B : Term 0 (Ξ.extend ps.length)} →
      {ψ : ResultOwnership ps.length} → (hpos : Destructors.Pos d p q ds Ξ Θ B ψ) →
      {inst : Name → Term 0 Γ} → {rs : Nat → Option Name} → {θ₁ θ₂ : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs ds θ₁ θ₂ → {rsR : Nat → Option TermRel} →
      (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R v, rsR i = some R ∧ Computesι sig ι ((inst D).subst θ₁) v ∧
        FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality v R) →
      (∀ i D, rs i = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι ((inst D).subst θ₁) ((inst D).subst θ₂) (.sort κ₁)) →
      {S : ObsRel} →
      DesRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality rsR ds @θ₁ S →
      {o₁ o₂ f₁ f₂ : Observations} → S o₁ o₂ → ObsEquiv sig ι κ.quality f₁ o₁ →
      ObsEquiv sig ι κ.quality f₂ o₂ →
      (∃ κ₁, ∀ ts us : Args 0 [] ps,
        EqSubst sig ι (Context.empty.append (Θ.subst (hpos.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι (B.subst (Subst.append (hpos.obsSubst f₁ θ₁) ts.toSubst))
          (B.subst (Subst.append (hpos.obsSubst f₂ θ₂) us.toSubst)) (.sort κ₁)) ∧
      ∀ ts us : Args 0 [] ps,
        EqSubst sig ι (Context.empty.append (Θ.subst (hpos.obsSubst f₁ θ₁))) ts.toSubst
          us.toSubst →
        ValidEqTerm₀ sig ι ((f₁ d ps).subst ts.toSubst) ((f₂ d ps).subst us.toSubst)
          (B.subst (Subst.append (hpos.obsSubst f₁ θ₁) ts.toSubst))
  | _, _, _, _, _, B, _, .here, inst, rs, θ₁, θ₂, hv, rsR, hN, hR, hI, _, hS, _, _, _, _, ho, hf₁,
      hf₂ => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    split at hv
    · rename_i hr
      obtain ⟨⟨κ₁, -, hB⟩, -⟩ := hv
      exact ⟨⟨κ₁, fun ts us hτ => hB _ _ hτ⟩, (DesRel.head hd hS (hN 0 hr) ho hf₁ hf₂).1⟩
    · rename_i D hr
      obtain ⟨rfl, -⟩ := hv
      obtain ⟨R, v, hR0, hcv, hFv⟩ := hR 0 D hr
      obtain ⟨κ₁, hI0⟩ := hI 0 D hr
      have hhead := (DesRel.headRec hd hS hR0 hFv ho hf₁ hf₂).1
      refine ⟨⟨κ₁, fun ts us _ => ?_⟩, fun ts us hτ => ?_⟩
      · rw [Term.subst_append_rename_weakenN, Term.subst_append_rename_weakenN]
        exact hI0
      · rw [Term.subst_append_rename_weakenN]
        exact hFv.validEqTerm hd hcv (hhead ts us hτ)
  | _, _, _, _, _, _, _, .there (d' := d') (ps' := ps') (Θ' := Θ') (B' := B') (ψ' := ψ') h, inst,
      rs, θ₁, θ₂, hv, rsR, hN, hR, hI, _, hS, _, _, f₁, f₂, ho, hf₁, hf₂ => by
    rw [ValidEqDestructors₀] at hv
    obtain ⟨-, hv⟩ := hv
    have hsw : ∀ (θ : Subst 0 [] _) (f : Term 0 (Scope.extend [] ps'.length)) D,
        ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ f) =
          (inst D).subst θ := fun θ f D => Term.subst_rename_of (fun _ => rfl) _
    have hN' : ∀ i, rs (i + 1) = none → rsR (i + 1) = none := fun i => hN (i + 1)
    have hR' : ∀ (f : Term 0 (Scope.extend [] ps'.length)) i D, rs (i + 1) = some D → ∃ R v,
        rsR (i + 1) = some R ∧ Computesι sig ι
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ f)) v ∧
        FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality v R :=
      fun f i D hi => by rw [hsw]; exact hR (i + 1) D hi
    have hI' : ∀ (f₁ f₂ : Term 0 (Scope.extend [] ps'.length)) i D, rs (i + 1) = some D → ∃ κ₁,
        ValidEqTerm₀ sig ι
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₁ f₁))
          (((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps' ψ') θ₂ f₂))
          (.sort κ₁) :=
      fun f₁ f₂ i D hi => by rw [hsw, hsw]; exact hI (i + 1) D hi
    split at hv
    · rename_i hr
      obtain ⟨-, hds⟩ := hv
      obtain ⟨hhead, S', hS', ho'⟩ := DesRel.head hd hS (hN 0 hr) ho hf₁ hf₂
      have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ'.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι ((f₁ d' ps').subst τ₁) ((f₂ d' ps').subst τ₂)
            (B'.subst (Subst.append θ₁ τ₁)) := fun τ₁ τ₂ hτ => by
        obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) ts.toSubst @τ₁ :=
          ⟨_, Subst.args_toSubst ps' τ₁⟩
        obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps',
            @Eq (Subst 0 [] (Scope.extend [] ps'.length)) us.toSubst @τ₂ :=
          ⟨_, Subst.args_toSubst ps' τ₂⟩
        exact hhead ts us hτ
      exact h.sound hd (hds _ _ hcond) hN' (hR' _) (hI' _ _) hS' ho' hf₁ hf₂
    · rename_i D hr
      obtain ⟨-, hds⟩ := hv
      obtain ⟨R, v, hR0, -, hFv⟩ := hR 0 D hr
      obtain ⟨-, hrest⟩ := DesRel.headRec hd hS hR0 hFv ho hf₁ hf₂
      obtain ⟨S', hS', ho'⟩ := hrest (f₁ d' ps')
      exact h.sound hd (hds (f₁ d' ps') (f₂ d' ps')) hN' (hR' _) (hI' _ _) hS' ho' hf₁ hf₂

/-- The equality of the canonical terms of an instance of a codata type of `Σ` is, at the equality
`S` of the destructors of the types of its block that the graph gives, `(eq_ν)` for an instance in
a universe, and the truth `(true_ν)` of the instance for a proposition, in a signature whose names
are distinct. -/
theorem HasEq.instCodata_inv (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {R : TermRel} (hR : HasEq sig ι (.inst D qs ls ps as) R) :
    ((decl.sort (.ofLists qs ps hq hp)).quality = .type ∧
      ∃ S : (Name → TermRel) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
        (∀ X, ∀ T' ∈ decl.codataTypes,
          DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
            (fun m _ => levelRel sig ι m) .type
            (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
              fun D' => (X D').computed sig ι)
            ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S X T')) ∧
        R = CodataType.blockRel decl.codataTypes S D) ∨
    ((decl.sort (.ofLists qs ps hq hp)).quality = .prop ∧
      ∃ S : (Name → Prop) → CodataType decl.sorts decl.grades decl.levels decl.scope → ObsRel,
        (∀ B, ∀ T' ∈ decl.codataTypes,
          DesRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
            (fun m _ => levelRel sig ι m) .prop
            (fun i => ((T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i).map
              fun D' => fun _ _ => B D')
            ((T'.body (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) as.toSubst (S B T')) ∧
        ∀ t u, R t u ↔ CodataType.blockTruth decl.codataTypes S D) := by
  cases hR with
  | univ n hU =>
    have hU' := levelRel_univ_iff.1 hU
    cases hU' with
    | data h' _ _ _ hv => exact (hd.inst_data_codata h' h hv.symm).elim
    | codata h' _ _ _ hv hs hn S hS =>
      have hD := congrArg (fun t : Term 0 [] => match t with | .inst D .. => D | _ => "") hv
      dsimp only at hD
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h (hD ▸ h')
      cases hT
      cases hv
      subst hn
      exact .inl ⟨hs, S, fun X T' hT' => hs ▸ hS X T' hT', rfl⟩
  | prop n b hP hRb =>
    have hP' := levelRel_prop_iff.1 hP
    cases hP' with
    | data h' _ _ _ hv => exact (hd.inst_data_codata h' h hv.symm).elim
    | codata h' _ _ _ hv hs hn S hS =>
      have hD := congrArg (fun t : Term 0 [] => match t with | .inst D .. => D | _ => "") hv
      dsimp only at hD
      obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h (hD ▸ h')
      cases hT
      cases hv
      subst hn
      exact .inr ⟨hs, S, fun B T' hT' => hs ▸ hS B T' hT', hRb⟩

/-- The observation of a closed term, substituted by closed arguments, is the observation by the
destructor applied to them. -/
theorem Term.observation_subst_args {Δ : Scope} (D : Name) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 [] Δ) (t : Term 0 []) (d : Name)
    {ps' : List Parameter} (ts : Args 0 [] ps') :
    (t.observation D qs ls ps as d ps').subst ts.toSubst = .obs D qs ls ps as t d ts.terms := by
  rw [← Term.instantiate_eq_subst, Term.observation_instantiate]

/-- The observations of a closed term that computes to a corecursor compute as the observations of
the corecursor, at the instance it carries. -/
theorem ObsEquiv.of_computes (hd : sig.Distinct) {s : Quality} {Δ : Scope} {D D' : Name}
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} {as : InstanceArgs 0 [] Δ}
    {t w : Term 0 []} {o : Observations} (ht : Computesι sig ι t w)
    (hw : w.CorecObservations D' o) : ObsEquiv sig ι s (t.observation D qs ls ps as) o := by
  obtain ⟨r, qs', ls', ps', Δ', as', ss, Ss, gs, rfl, rfl⟩ := hw
  refine .inr fun d xs τ v => ?_
  obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] xs,
      @Eq (Subst 0 [] (Scope.extend [] xs.length)) ts.toSubst @τ :=
    ⟨_, Subst.args_toSubst xs τ⟩
  rw [Term.observation_subst_args, Term.observation_subst_args,
    Computesι.redStar_iff hd (RedStar.obs ht.1)]
  exact ⟨Computesι.obs_corec_iff, Computesι.obs_corec_iff⟩

-- ADE: none.
/-- `(d_≡)`, closed: the observations of two equal closed terms of an instance of a codata type of
`Σ`, whose type declaration is meaningful, at equal arguments of its parameters, by a destructor at
equal arguments of its telescope, are equal terms of its result, and their results are equal
types. -/
theorem ValidEqTerm₀.obs (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {d : Name} {p q : Grade}
    {ps' : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps'}
    {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {a₁ a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      a₁.toSubst a₂.toSubst)
    {t₁ t₂ : Term 0 []} (ht : ValidEqTerm₀ sig ι t₁ t₂ (.inst D qs ls ps a₁))
    {bs₁ bs₂ : Args 0 [] ps'}
    (hbs : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))) bs₁.toSubst bs₂.toSubst) :
    ValidEqTerm₀ sig ι (.obs D qs ls ps a₁ t₁ d bs₁.terms) (.obs D qs ls ps a₂ t₂ d bs₂.terms)
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))).instantiate
            bs₁) ∧
      ValidEqType₀ sig ι
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls ps a₁) a₁.toSubst))).instantiate
            bs₁)
        (((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t₂.observation D qs ls ps a₂) a₂.toSubst))).instantiate
            bs₂) := by
  -- The levels without variables at which the declaration is meaningful.
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm h.2.1 ρ).2 _ _ hθ
  have hn := Level.closedValue_subst_equiv hls (decl.sort I).level
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : InstanceArgs 0 [] decl.scope → Name → Term 0 [] := fun a D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst a.toSubst
  have hX : ∀ a D', Term.LevelEquiv (X a D') (.inst D' qs ls ps a) := fun a D' =>
    decl.blockInstance_atLevels_subst hq hl hp a D'
  have hcX : ∀ a D', Computesι sig ι (X a D') (X a D') := fun _ _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hXeq : ∀ D' ∈ decl.names, ∃ κ₁, ValidEqTerm₀ sig ι (X a₁ D') (X a₂ D') (.sort κ₁) :=
    fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1 hD'
      exact ⟨_, (ValidEqTerm₀.instCodata hd ⟨h.1, hT', rfl⟩ hv hq hl hp hadm has).levelEquiv
        (hX a₁ _).symm (hX a₂ _).symm (Term.LevelEquiv.refl _)⟩
  -- The equality of the instance.
  have hI : Computesι sig ι (.inst D qs ls ps a₁) (.inst D qs ls ps a₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht.1.2
  cases Computesι.det hd hcv hI
  -- Observations related by the equality of the destructors, at the equalities of the instances
  -- for the recursive destructors, which those of the terms compute as.
  have hobs : ∃ (rsR : Nat → Option TermRel) (S : ObsRel) (o₁ o₂ : Observations),
      DesRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
        ((decl.sort I).atLevels ρ).quality rsR ((T.body I).atLevels ρ) a₁.toSubst S ∧
      S o₁ o₂ ∧
      ObsEquiv sig ι (decl.sort I).quality (t₁.observation D qs ls ps a₁) o₁ ∧
      ObsEquiv sig ι (decl.sort I).quality (t₂.observation D qs ls ps a₂) o₂ ∧
      (∀ i, (T.body I).recursionAt decl.names i = none → rsR i = none) ∧
      (∀ i D', (T.body I).recursionAt decl.names i = some D' → ∃ R v, rsR i = some R ∧
        Computesι sig ι (X a₁ D') v ∧
        FieldRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
          ((decl.sort I).atLevels ρ).quality v R) := by
    have hlev : ∀ {s : Quality} {rs : Nat → Option TermRel} {S : ObsRel},
        DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
          ((T.body I).substLevels L) a₁.toSubst S →
        DesRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m) s
          rs ((T.body I).atLevels ρ) a₁.toSubst S := fun hS => by
      have e : ((decl.sort I).atLevels ρ).level.closedValue =
          ((decl.sort I).level.subst L).closedValue := hn
      rw [e]
      exact DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
        (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
        (Subst.LevelEquiv.refl _)
    have hF : ∀ {s : Quality} {R' : TermRel} {D' : Name},
        FieldRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s
          (.inst D' qs ls ps a₁) R' →
        FieldRel sig ι ((decl.sort I).atLevels ρ).level.closedValue (fun m _ => levelRel sig ι m)
          s (X a₁ D') R' := fun hF' => by
      have e : ((decl.sort I).atLevels ρ).level.closedValue =
          ((decl.sort I).level.subst L).closedValue := hn
      rw [e]
      exact FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hF' (hX a₁ _).symm
    rcases HasEq.instCodata_inv hd h hq hl hp hR with ⟨hs, S, hS, rfl⟩ | ⟨hs, S, hS, hRb⟩
    · have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
          (.inst D qs ls ps a₁) (CodataType.blockRel decl.codataTypes S D) :=
        levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
      have hnp : ¬ ComputesToProp sig ι (.inst D qs ls ps a₁) := fun ⟨v, hv, k, b, hk⟩ => by
        cases Computesι.det hd hI hv
        exact HasEq.univ_not_prop hd hU₀ hk
      obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := ht.2.1 hnp
      cases Computesι.det hd hI hv'
      have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
          ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
        fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
          fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
      have hrel' := (HasEq.unique hd hR' hR w₁ w₂).1 hrel
      rw [← h.2.2] at hrel'
      obtain ⟨o₁, o₂, hc₁, hc₂, ho⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel'
      refine ⟨_, _, o₁, o₂, hlev (hs ▸ hS _ T h.2.1), ho, ObsEquiv.of_computes hd hw₁ hc₁,
        ObsEquiv.of_computes hd hw₂ hc₂, fun i hi => by rw [hi]; rfl, fun i D' hi => ?_⟩
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
        (Destructors.recursionAt_mem hi)
      have hU : UnivRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps a₁)
          (CodataType.blockRel decl.codataTypes S T'.name) :=
        .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
      rw [hi]
      exact ⟨_, _, rfl, hcX _ _, hs ▸ hF (.univ rfl hU)⟩
    · have hP : PropRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst D qs ls ps a₁)
          (CodataType.blockTruth decl.codataTypes S D) :=
        .codata h hq hl hp rfl hs rfl S hS
      have hprop : ComputesToProp sig ι (.inst D qs ls ps a₁) :=
        ⟨_, hI, _, _, levelRel_prop_iff.2 hP⟩
      obtain ⟨v', R', hv', hR', hrel⟩ := ht.2.2 hprop
      cases Computesι.det hd hI hv'
      have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
          S B T' o₁ o₂ → S B' T' o₁ o₂ :=
        fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
          fun _ => Option.rel_map (fun D _ _ => hB D) _
      have htrue := (hRb _ _).1 ((HasEq.unique hd hR' hR _ _).1 hrel)
      rw [← h.2.2] at htrue
      obtain ⟨o, ho⟩ := CodataType.blockTruth_unfold hmono h.2.1 htrue
      refine ⟨_, _, o, o, hlev (hs ▸ hS _ T h.2.1), ho, .inl hs, .inl hs,
        fun i hi => by rw [hi]; rfl, fun i D' hi => ?_⟩
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
        (Destructors.recursionAt_mem hi)
      have hP' : PropRel sig ι ((decl.sort I).level.subst L).closedValue
          (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps a₁)
          (CodataType.blockTruth decl.codataTypes S T'.name) :=
        .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
      rw [hi]
      exact ⟨_, _, rfl, hcX _ _, hs ▸ hF (.prop hP')⟩
  obtain ⟨rsR, S, o₁, o₂, hSρ, ho, hf₁, hf₂, hN, hRr⟩ := hobs
  obtain ⟨⟨κ₁, hBeq⟩, hres⟩ := (hpos.substLevels Lρ).sound hd hmean hN hRr
    (fun i D' hi => hXeq D' (Destructors.recursionAt_mem hi)) hSρ ho hf₁ hf₂
  -- The substitutions of the scope of the destructor, at the levels of the declaration and at the
  -- levels without variables, are the same.
  have hcE : ∀ {f : Observations} {a : InstanceArgs 0 [] decl.scope},
      Subst.LevelEquiv ((hpos.substLevels Lρ).obsSubst f a.toSubst) (hpos.obsSubst f a.toSubst) :=
    fun {f a} {_} x => by
      show Term.LevelEquiv ((hpos.substLevels Lρ).obsSubst f a.toSubst x)
        (hpos.obsSubst f a.toSubst x)
      rw [Destructors.Pos.obsSubst_posSubstLevels]
      exact Term.LevelEquiv.refl _
  have hbsρ := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
    (Telescope.LevelEquiv.subst hcE.symm
      (Telescope.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) Θ))) hbs
  have hBE : ∀ {f : Observations} {a : InstanceArgs 0 [] decl.scope}
      {τ : Subst 0 [] (Scope.extend [] ps'.length)},
      Term.LevelEquiv ((B.substLevels Lρ).subst
          (Subst.append ((hpos.substLevels Lρ).obsSubst f a.toSubst) τ))
        ((B.substLevels L).subst (Subst.append (hpos.obsSubst f a.toSubst) τ)) :=
    Term.LevelEquiv.subst (Subst.LevelEquiv.append hcE (Subst.LevelEquiv.refl _))
      (Term.substLevels_levelEquiv hls B)
  rw [Term.instantiate_eq_subst, Term.instantiate_eq_subst, Term.subst_append, Term.subst_append]
  refine ⟨?_, ?_⟩
  · have hr := hres bs₁ bs₂ hbsρ
    rw [Term.observation_subst_args, Term.observation_subst_args] at hr
    exact hr.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) hBE
  · have hB := hBeq bs₁ bs₂ hbsρ
    obtain ⟨s, l⟩ := κ₁
    cases s
    · exact (ValidEqTerm₀.univType hB).levelEquiv hBE hBE
    · exact (ValidEqTerm₀.propType hB).levelEquiv hBE hBE

-- ADE: `∘-congᵛ`, `fst-congᵛ` and `snd-congᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(d_≡)` keeps the meaning, and `(d)` with it: at equal substitutions of the context, the
observations of the terms, at the arguments of the instance and of the telescope substituted, are
the closed observations of `ValidEqTerm₀.obs`, since the observations of the term substituted are
those of the substituted term; the result is a type, since the results at two substitutions are
both equal to the result of the second observation at the second substitution; and the second
observation at levels of the same values is the same term up to its levels. -/
theorem ValidEqTermΓ.obs {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {d : Name} {p q : Grade}
    {ps' : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps'}
    {B : Term decl.levels (Ξ.extend ps'.length)} {ψ : ResultOwnership ps'.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i) {t₁ t₂ : Term 0 Γ}
    (ht : ValidEqTermΓ sig ι ctx t₁ t₂ (.inst D qs ls₁ ps as₁)) {bs₁ bs₂ : Args 0 Γ ps'}
    (hbs : ValidEqArgsΓ sig ι ctx bs₁ bs₂ ((Θ.substLevels (ls₁.getFin hl₁)).subst
      (hpos.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))) :
    ValidEqTermΓ sig ι ctx (.obs D qs ls₁ ps as₁ t₁ d bs₁.terms)
      (.obs D qs ls₂ ps as₂ t₂ d bs₂.terms)
      (((B.substLevels (ls₁.getFin hl₁)).subst
        (Subst.liftN _ (hpos.obsSubst (t₁.observation D qs ls₁ ps as₁) as₁.toSubst))).instantiate
          bs₁) := by
  obtain ⟨h', hv⟩ := hent.hasCodataType h
  have hctx := has.1
  have hd := hctx.distinct
  -- The scope of the destructor, substituted, is that of the observations of the terms substituted.
  have hc : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope) {a}
      (x : Var Ξ a), ((hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst) x).subst
        (Subst.liftN a.params.length σ) =
        hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ)) (as.subst σ).toSubst x :=
    fun σ t as => hpos.obsSubst_subst σ
      (fun d ps' => Term.observation_subst σ D qs ls₁ ps as t d ps')
      (InstanceArgs.toSubst_subst σ as)
  have hΘ : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope),
      ((Θ.substLevels (ls₁.getFin hl₁)).subst
        (hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst)).subst σ =
      (Θ.substLevels (ls₁.getFin hl₁)).subst
        (hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ)) (as.subst σ).toSubst) :=
    fun σ t as => Telescope.subst_subst_of (hc σ t as) _
  have hA : ∀ (σ : Subst 0 [] Γ) (t : Term 0 Γ) (as : InstanceArgs 0 Γ decl.scope)
      (bs : Args 0 Γ ps'),
      (((B.substLevels (ls₁.getFin hl₁)).subst
        (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls₁ ps as) as.toSubst))).instantiate
          bs).subst σ =
      ((B.substLevels (ls₁.getFin hl₁)).subst (Subst.liftN _
        (hpos.obsSubst ((t.subst σ).observation D qs ls₁ ps (as.subst σ))
          (as.subst σ).toSubst))).instantiate (bs.subst σ) :=
    fun σ t as bs => by
      rw [Term.instantiate_subst, Term.subst_subst_of (Subst.liftN_subst_of _ (hc σ t as))]
  have hcl := fun σ₁ σ₂ (hσ : EqSubst sig ι ctx σ₁ σ₂) => by
    have hbs' := hbs.2 σ₁ σ₂ hσ
    rw [hΘ] at hbs'
    exact ValidEqTerm₀.obs hd h' hv hq hl₁ hp hadm hpos (has.2 σ₁ σ₂ hσ) (ht.2 σ₁ σ₂ hσ) hbs'
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · rw [hA, hA]
    exact (hcl σ₁ σ₂ hσ).2.trans (hcl σ₂ σ₂ (hσ.right hctx)).2.symm
  · rw [hA]
    simp only [Term.subst, ← Args.terms_subst]
    exact (hcl σ₁ σ₂ hσ).1.levelEquiv (Term.LevelEquiv.refl _)
      (.obs D qs ps d (Level.ListEquiv.of_getFin hl₁ hl₂ hls) (InstanceArgs.LevelEquiv.refl _)
        (Term.LevelEquiv.refl _) (Terms.LevelEquiv.refl _))
      (Term.LevelEquiv.refl _)

/-! ## Positions

The positions of a corecursor are the constructors of the type of positions, a new state or a term
already built, which has no recursive field, and a new state is a packing, whose canonical terms are
the nested pairs of the arguments of the state: equal positions are the same constructor at equal
terms, and resume, by `(ι_⟶)` on the position and on each pair, to the corecursor from the new state,
or to the term already built. -/

-- ADE: none.
/-- Two equal closed positions compute to new states, equal terms of the packing of the state, or
to terms already built, equal terms of their type: the constructors of the type of positions, which
has no recursive field. -/
theorem ValidEqTerm₀.positions_inv (hpre : sig.HasPrelude) {κ : Universe 0} {r χ : Grade}
    {ps : List Parameter} {S : Telescope 0 [] ps} {κs : List (Universe 0)} {T g₁ g₂ : Term 0 []}
    (h : ValidEqTerm₀ sig ι g₁ g₂ (Term.positions κ r χ S κs T)) :
    (∃ x₁ x₂, (∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
          (as : InstanceArgs 0 [] Δ), Computesι sig ι g₁ (.ctor "Step" qs ls ps as "next"
            (.cons x₁ .nil))) ∧
        (∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
          (as : InstanceArgs 0 [] Δ), Computesι sig ι g₂ (.ctor "Step" qs ls ps as "next"
            (.cons x₂ .nil))) ∧
        ValidEqTerm₀ sig ι x₁ x₂ (S.pack κs (Telescope.packLevel κs .zero))) ∨
    (∃ t₁ t₂, (∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
          (as : InstanceArgs 0 [] Δ), Computesι sig ι g₁ (.ctor "Step" qs ls ps as "done"
            (.cons t₁ .nil))) ∧
        (∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
          (as : InstanceArgs 0 [] Δ), Computesι sig ι g₂ (.ctor "Step" qs ls ps as "done"
            (.cons t₂ .nil))) ∧
        ValidEqTerm₀ sig ι t₁ t₂ T) := by
  obtain ⟨T', hT', -, con, hc, ts₁, ts₂, h₁, h₂, hts⟩ := ValidEqTerm₀.ctor_inv hpre.step
    (qs := [κ.quality]) (ps := [r, Prelude.doneGrade κ.quality, χ]) rfl rfl rfl rfl
    (fun T' hT' c hc i => by
      obtain rfl := List.mem_singleton.1 hT'
      rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩ <;> cases i <;> rfl) h
  obtain rfl := List.mem_singleton.1 hT'
  rcases hc with _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩
  · left
    match ts₁, ts₂, hts with
    | .cons x₁ .nil, .cons x₂ .nil, hts =>
      exact ⟨x₁, x₂, h₁, h₂, (EqSubst.args_cons_iff.1 hts).1⟩
  · right
    match ts₁, ts₂, hts with
    | .cons t₁ .nil, .cons t₂ .nil, hts =>
      exact ⟨t₁, t₂, h₁, h₂, (EqSubst.args_cons_iff.1 hts).1⟩

/-- `x ⇓ ⟨t̄⟩`: the closed term `x` computes to the nested pairs of the terms `t̄`, which end with the
unit, each pair at any instance, its second term computing in turn. -/
def Term.Packs (sig : Signature) (ι : Interpretation) : Term 0 [] → Terms 0 [] → Prop
  | x, .nil => ∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
      (as : InstanceArgs 0 [] Δ), Computesι sig ι x (.ctor "Unit" qs ls ps as "mk" .nil)
  | x, .cons t ts => ∃ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (Δ : Scope)
      (as : InstanceArgs 0 [] Δ) (y : Term 0 []),
      Computesι sig ι x (.ctor "Pair" qs ls ps as "mk" (.cons t (.cons y .nil))) ∧
        Term.Packs sig ι y ts

-- ADE: none.
/-- Two equal closed terms of the packing of a closed telescope compute to the nested pairs of
equal arguments of the telescope: the constructors of the pair and of the unit, which have no
recursive field, at each entry. -/
theorem ValidEqTerm₀.pack_inv (hpre : sig.HasPrelude) :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → (κs : List (Universe 0)) → (l : Level 0) →
      {x₁ x₂ : Term 0 []} → ValidEqTerm₀ sig ι x₁ x₂ (Θ.pack κs l) →
      ∃ ts₁ ts₂ : Args 0 [] ps, Term.Packs sig ι x₁ ts₁.terms ∧ Term.Packs sig ι x₂ ts₂.terms ∧
        EqSubst sig ι (Context.empty.append Θ) ts₁.toSubst ts₂.toSubst
  | [], .nil, _, l, _, _, h => by
    obtain ⟨T', hT', -, con, hc, ts₁, ts₂, h₁, h₂, -⟩ := ValidEqTerm₀.ctor_inv hpre.unit
      (qs := []) (ls := [l]) (ps := []) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rfl) h
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    match ts₁, ts₂ with
    | .nil, .nil =>
      refine ⟨.nil, .nil, ?_, ?_, (EqSubst.empty_iff _ _).2 trivial⟩
      · simp only [Args.terms, Term.Packs]
        exact h₁
      · simp only [Args.terms, Term.Packs]
        exact h₂
  | _ :: _, .cons q p A Θ, κs, l, _, _, h => by
    obtain ⟨T', hT', -, con, hc, ts₁, ts₂, h₁, h₂, hts⟩ := ValidEqTerm₀.ctor_inv hpre.pair
      (qs := [(κs.headD ⟨.type, l⟩).quality])
      (ls := [(κs.headD ⟨.type, l⟩).level, Telescope.packLevel κs.tail l])
      (ps := [p.usage, p.requirement]) rfl rfl rfl rfl
      (fun T' hT' c hc i => by
        obtain rfl := List.mem_singleton.1 hT'
        rcases hc with _ | ⟨_, ⟨⟩⟩
        rcases i with _ | _ | _ <;> rfl) h
    obtain rfl := List.mem_singleton.1 hT'
    rcases hc with _ | ⟨_, ⟨⟩⟩
    match ts₁, ts₂, hts with
    | .cons t₁ (.cons y₁ .nil), .cons t₂ (.cons y₂ .nil), hts =>
      obtain ⟨ht, hys⟩ := EqSubst.args_cons_iff.1 hts
      obtain ⟨hy, -⟩ := EqSubst.args_cons_iff.1 hys
      have e : ValidEqTerm₀ sig ι y₁ y₂ ((Θ.subst₀ (Subst₀.single t₁)).pack κs.tail l) := by
        rw [← Telescope.pack_subst₀, ← Prelude.pairSecond (Θ.pack κs.tail l)]
        exact hy
      obtain ⟨ts₁, ts₂, hp₁, hp₂, hτ⟩ := ValidEqTerm₀.pack_inv hpre _ κs.tail l e
      obtain ⟨qs₁, ls₁, ps₁, Δ₁, as₁, hc₁⟩ := h₁
      obtain ⟨qs₂, ls₂, ps₂, Δ₂, as₂, hc₂⟩ := h₂
      refine ⟨.cons t₁ ts₁, .cons t₂ ts₂, ?_, ?_, EqSubst.args_cons_iff.2 ⟨ht, hτ⟩⟩
      · simp only [Args.terms, Term.Packs]
        exact ⟨qs₁, ls₁, ps₁, Δ₁, as₁, y₁, hc₁, hp₁⟩
      · simp only [Args.terms, Term.Packs]
        exact ⟨qs₂, ls₂, ps₂, Δ₂, as₂, y₂, hc₂, hp₂⟩

-- ADE: none.
/-- The unpacking of a closed term that computes to the nested pairs of arguments of the telescope
reduces to the term at the arguments, by `(ι_⟶)` on each pair, then on the unit. -/
theorem RedStar.unpack (hpre : sig.HasPrelude) (r : Grade) :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → (κs : List (Universe 0)) → (l : Level 0) →
      (C : Term 0 []) → (b : Term 0 (Scope.extend [] ps.length)) → {x : Term 0 []} →
      (ts : Args 0 [] ps) → Term.Packs sig ι x ts.terms →
      RedStar (sig.interpret ι) (Term.unpack r x Θ κs l C b) (b.instantiate ts)
  | [], .nil, _, l, C, b, x, .nil, hx => by
    simp only [Args.terms, Term.Packs] at hx
    obtain ⟨qs, ls, ps, Δ, as, hx, -⟩ := hx
    exact (RedStar.recursor hx).trans (.step (.iota (decl := Prelude.unit) (i := 0)
      (List.mem_map_of_mem (f := Entry.interpret ι) hpre.unit.1) rfl rfl rfl rfl rfl rfl rfl)
      (.refl _))
  | _ :: _, .cons q p A Θ, κs, l, C, b, x, .cons t ts, hx => by
    simp only [Args.terms, Term.Packs] at hx
    obtain ⟨qs, ls, ps, Δ, as, y, ⟨hx, -⟩, hy⟩ := hx
    exact (RedStar.recursor hx).trans (.step (.iota (decl := Prelude.pair) (i := 0)
      (v := Term.unpack r y (Θ.subst₀ (Subst₀.single t)) κs.tail l C
        (b.subst₀ (Subst₀.liftN _ (Subst₀.single t))))
      (List.mem_map_of_mem (f := Entry.interpret ι) hpre.pair.1) rfl rfl rfl rfl rfl rfl
      (congrArg some (Term.unpack_branch_instantiate (p := p) r t y Θ κs.tail l C b)))
      (RedStar.unpack hpre r (Θ.subst₀ (Subst₀.single t)) κs.tail l C _ ts hy))

-- ADE: none.
/-- A closed position that reduces to a term already built resumes, by `(ι_⟶)`, to the term. -/
theorem RedStar.resume_done (hpre : sig.HasPrelude) {r : Grade} {D : Name} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {Δ : Scope} {as : InstanceArgs 0 [] Δ}
    {Ss : States 0 []} {gs : CorecBranches 0 []} {κ : Universe 0} {χ : Grade}
    {ps' : List Parameter} {S : Telescope 0 [] ps'} {κs : List (Universe 0)} {v t : Term 0 []}
    {qs' : List Quality} {ls' : List (Level 0)} {ps'' : List Grade} {Δ' : Scope}
    {as' : InstanceArgs 0 [] Δ'}
    (hv : RedStar (sig.interpret ι) v (.ctor "Step" qs' ls' ps'' as' "done" (.cons t .nil))) :
    RedStar (sig.interpret ι) (Term.resume r D qs ls ps as Ss gs κ χ S κs v) t :=
  (RedStar.recursor hv).trans (.step (.iota (decl := Prelude.step) (i := 1) (v := t)
    (List.mem_map_of_mem (f := Entry.interpret ι) hpre.step.1) rfl rfl rfl rfl rfl rfl rfl)
    (.refl _))

-- ADE: none.
/-- A closed position that reduces to a new state, which computes to the nested pairs of arguments
of the state, resumes, by `(ι_⟶)` and the unpacking, to the corecursor from the arguments. -/
theorem RedStar.resume_next (hpre : sig.HasPrelude) {r : Grade} {D : Name} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {Δ : Scope} {as : InstanceArgs 0 [] Δ}
    {Ss : States 0 []} {gs : CorecBranches 0 []} {κ : Universe 0} {χ : Grade}
    {ps' : List Parameter} {S : Telescope 0 [] ps'} {κs : List (Universe 0)} {v x : Term 0 []}
    {qs' : List Quality} {ls' : List (Level 0)} {ps'' : List Grade} {Δ' : Scope}
    {as' : InstanceArgs 0 [] Δ'}
    (hv : RedStar (sig.interpret ι) v (.ctor "Step" qs' ls' ps'' as' "next" (.cons x .nil)))
    (ts : Args 0 [] ps') (hx : Term.Packs sig ι x ts.terms) :
    RedStar (sig.interpret ι) (Term.resume r D qs ls ps as Ss gs κ χ S κs v)
      (.corec r D qs ls ps as ts.terms Ss gs) := by
  have hc : ∀ {a} (y : Var [] a), Subst₀.toSubst (Subst₀.single x) (Ren.weaken (e := .var) y) =
      (fun y => nomatch y : Subst 0 [] []) y := fun y => nomatch y
  have hid : ∀ {a} (y : Var [] a), (fun y => nomatch y : Subst 0 [] []) y = Var.eta y :=
    fun y => nomatch y
  have hb : ((Term.corecAt r D qs ls ps (as.rename Ren.weaken) (Ss.rename Ren.weaken)
      (gs.rename Ren.weaken) ps').subst₀ (Subst₀.liftN ps'.length (Subst₀.single x))).instantiate ts =
      .corec r D qs ls ps as ts.terms Ss gs := by
    rw [Term.subst₀_liftN_eq_subst, Term.corecAt_subst, InstanceArgs.subst_rename_of hc,
      States.subst_rename_of hc, CorecBranches.subst_rename_of hc, InstanceArgs.subst_id_of hid,
      States.subst_id_of hid, CorecBranches.subst_id_of hid, Term.corecAt_instantiate]
  refine (RedStar.recursor hv).trans (.step (.iota (decl := Prelude.step) (i := 0)
    (List.mem_map_of_mem (f := Entry.interpret ι) hpre.step.1) rfl rfl rfl rfl rfl rfl rfl) ?_)
  rw [← hb]
  erw [Term.unpack_subst₀]
  exact RedStar.unpack hpre r _ κs _ _ _ ts hx

/-! ## Corecursors

A corecursor is a canonical term of the instance it carries, and two corecursors of a codata type of
a meaningful declaration are equal when their observations are, destructor by destructor: the
destructors before the one observed are, in its telescope and its result, the observations of the
first corecursor, from the first destructor to the last one, as the equality of the destructors
reads them.
An observation of a corecursor computes, by `(β_⟶)`, as the branch of its destructor at the state
and the arguments, which the premises of `(corec)` make equal terms of the result of the
destructor, whose telescope and result, over the state, observe the corecursor from the state:
the corecursor itself, once the state is substituted.
On a proposition, the observations of the corecursor, related to themselves, make it true. -/

-- ADE: none.
/-- Observations whose results are equal, destructor by destructor, at equal arguments, are related
by the equality of the destructors, at instantiated levels: as terms of the result of each
destructor that is not recursive, and by the relation `R` that `rsR` gives each recursive one,
whose result is the instance of the block, as the meaning of the destructors says; the destructors
before each destructor being the observations `o₁`, as the equality of the destructors reads them,
from the first one. -/
theorem DesRel.of_obsRel (hd : sig.Distinct) {n : Nat} {s : Quality} {κ : Universe 0} {k' : Nat}
    (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {inst : Name → Term 0 Γ} →
      {rs : Nat → Option Name} → {θ θ' : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs (ds.substLevels L) θ θ' →
      {rsR : Nat → Option TermRel} → (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R, rsR i = some R) →
      {S : ObsRel} →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rsR (ds.substLevels L) @θ S →
      {o₁ o₂ : Observations} →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o₁ θ)))
          ts.toSubst us.toSubst → rs hpos.index = none →
        ValidEqTerm₀ sig ι ((o₁ d ps).subst ts.toSubst) ((o₂ d ps).subst us.toSubst)
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o₁ θ) ts.toSubst))) →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o₁ θ)))
          ts.toSubst us.toSubst → ∀ D R, rs hpos.index = some D → rsR hpos.index = some R →
        (B.substLevels L).subst (Subst.append (hpos.obsSubst o₁ θ) ts.toSubst) =
          (inst D).subst θ →
        R ((o₁ d ps).subst ts.toSubst) ((o₂ d ps).subst us.toSubst)) →
      S o₁ o₂
  | _, _, .nil, _, _, _, _, _, _, _, _, _, h, _, _, _, _ => by
    cases h
    trivial
  | _, _, .cons (d := d) (ps := ps) p q Θ B ψ ds, inst, rs, θ, θ', hm, rsR, hN, hS, _, h, o₁, o₂,
      hv, hr => by
    have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
    rw [Destructors.substLevels, ValidEqDestructors₀] at hm
    obtain ⟨-, hm⟩ := hm
    have hsw : ∀ (f : Term 0 (Scope.extend [] ps.length)) D,
        ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ f) =
          (inst D).subst θ := fun f D => Term.subst_rename_of (fun _ => rfl) _
    have hv' : ∀ (d' : Name) (p' q' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope k' Ξ' ps') (B' : Term k' (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership ps'.length) (hpos : ds.Pos d' p' q' Ξ' Θ' B' ψ')
        (ts us : Args 0 [] ps'),
        EqSubst sig ι (Context.empty.append ((Θ'.substLevels L).subst
          (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))))) ts.toSubst
          us.toSubst → rs (hpos.index + 1) = none →
        ValidEqTerm₀ sig ι ((o₁ d' ps').subst ts.toSubst) ((o₂ d' ps').subst us.toSubst)
          ((B'.substLevels L).subst (Subst.append
            (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))) ts.toSubst)) :=
      fun d' p' q' ps' Ξ' Θ' B' ψ' hpos ts us hτ =>
        hv d' p' q' ps' Ξ' Θ' B' ψ' (.there hpos) ts us hτ
    have hr' : ∀ (d' : Name) (p' q' : Grade) (ps' : List Parameter) (Ξ' : Scope)
        (Θ' : Telescope k' Ξ' ps') (B' : Term k' (Ξ'.extend ps'.length))
        (ψ' : ResultOwnership ps'.length) (hpos : ds.Pos d' p' q' Ξ' Θ' B' ψ')
        (ts us : Args 0 [] ps'),
        EqSubst sig ι (Context.empty.append ((Θ'.substLevels L).subst
          (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))))) ts.toSubst
          us.toSubst → ∀ D R, rs (hpos.index + 1) = some D → rsR (hpos.index + 1) = some R →
        (B'.substLevels L).subst (Subst.append
            (hpos.obsSubst o₁ (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps))) ts.toSubst) =
          ((inst D).rename Ren.weaken).subst (Subst.snoc (e := .secondOrder ps ψ) θ (o₁ d ps)) →
        R ((o₁ d' ps').subst ts.toSubst) ((o₂ d' ps').subst us.toSubst) :=
      fun d' p' q' ps' Ξ' Θ' B' ψ' hpos ts us hτ D R hD hR e =>
        hr d' p' q' ps' Ξ' Θ' B' ψ' (.there hpos) ts us hτ D R hD hR (e.trans (hsw _ D))
    split at hm
    · rename_i hr0
      obtain ⟨-, hds⟩ := hm
      cases h with
      | recursive hrs => rw [hN 0 hr0] at hrs; cases hrs
      | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
        have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
        have hEp := AbstractionRel.isPer hSp (fun ts hts =>
          have ⟨v, hv'⟩ := hB ts hts
          FieldRel.isPer hd ih (hF ts hts v hv')) hBresp
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        have hA : AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) := fun ts us hts => by
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv''⟩ := hB ts htt
          exact (hF ts htt v hv'').of_validEqTerm hv'' (hv d p q ps _ Θ B ψ .here ts us
            ((hT ts us).1 hts) hr0)
        have hff := hEp.trans hA (hEp.symm hA)
        have hcond : ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst θ))
            τ₁ τ₂ → ValidEqTerm₀ sig ι ((o₁ d ps).subst τ₁) ((o₁ d ps).subst τ₂)
              ((B.substLevels L).subst (Subst.append θ τ₁)) := fun τ₁ τ₂ hτ => by
          obtain ⟨ts, rfl⟩ : ∃ ts : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) ts.toSubst @τ₁ :=
            ⟨_, Subst.args_toSubst ps τ₁⟩
          obtain ⟨us, rfl⟩ : ∃ us : Args 0 [] ps,
              @Eq (Subst 0 [] (Scope.extend [] ps.length)) us.toSubst @τ₂ :=
            ⟨_, Subst.args_toSubst ps τ₂⟩
          have hts := (hT ts us).2 hτ
          have htt := hSp.trans hts (hSp.symm hts)
          obtain ⟨v, hv''⟩ := hB ts htt
          exact (hF ts htt v hv'').validEqTerm hd hv'' (hff ts us hts)
        exact ⟨hA, DesRel.of_obsRel hd L ds (hds _ _ hcond) (fun i => hN (i + 1))
          (fun i => hS (i + 1)) (hG _ hff) hv' hr'⟩
    · rename_i D hr0
      obtain ⟨hBD, hds⟩ := hm
      obtain ⟨R, hR0⟩ := hS 0 D hr0
      cases h with
      | cons _ _ _ _ _ _ _ _ hrs => rw [hR0] at hrs; cases hrs
      | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R' hrs hΘ G hG =>
        rw [hR0] at hrs
        cases hrs
        have hT := TelRel.eqSubst_iff hd hΘ
          (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _) (fun _ _ h => by cases h)
        refine ⟨fun ts us hts => ?_, DesRel.of_obsRel hd L ds (hds (o₁ d ps) (o₁ d ps))
          (fun i => hN (i + 1)) (fun i => hS (i + 1)) (hG _) hv' hr'⟩
        have e : (B.substLevels L).subst (Subst.append θ ts.toSubst) = (inst D).subst θ := by
          rw [hBD, Term.subst_append_rename_weakenN]
        exact hr d p q ps _ Θ B ψ .here ts us ((hT ts us).1 hts) D R hr0 hR0 e

-- ADE: none.
/-- Observations equal, destructor by destructor, at equal arguments, are related by the equality
of the destructors, at instantiated levels, at relations of the recursive destructors that the
equalities of the instances of the block relate: the destructors before each destructor being the
observations `o₁`, as the equality of the destructors reads them, from the first one, and the
results of a recursive destructor being terms of an instance, as the meaning of the destructors
says: `DesRel.of_obsRel`, whose relation of a recursive destructor relates equal terms of the
instance. -/
theorem DesRel.of_obs (hd : sig.Distinct) {n : Nat} {s : Quality} {κ : Universe 0} {k' : Nat}
    (L : Fin k' → Level 0) :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k' Γ ns) → {inst : Name → Term 0 Γ} →
      {rs : Nat → Option Name} → {θ θ' : Subst 0 [] Γ} →
      ValidEqDestructors₀ sig ι κ inst rs (ds.substLevels L) θ θ' →
      {rsR : Nat → Option TermRel} → (∀ i, rs i = none → rsR i = none) →
      (∀ i D, rs i = some D → ∃ R v, rsR i = some R ∧ Computesι sig ι ((inst D).subst θ) v ∧
        FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) →
      {S : ObsRel} →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rsR (ds.substLevels L) @θ S →
      {o₁ o₂ : Observations} →
      (∀ (d : Name) (p q : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k' Ξ ps)
        (B : Term k' (Ξ.extend ps.length)) (ψ : ResultOwnership ps.length)
        (hpos : ds.Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps),
        EqSubst sig ι (Context.empty.append ((Θ.substLevels L).subst (hpos.obsSubst o₁ θ)))
          ts.toSubst us.toSubst →
        ValidEqTerm₀ sig ι ((o₁ d ps).subst ts.toSubst) ((o₂ d ps).subst us.toSubst)
          ((B.substLevels L).subst (Subst.append (hpos.obsSubst o₁ θ) ts.toSubst))) →
      S o₁ o₂
  | _, _, ds, _, _, _, _, hm, _, hN, hR, _, h, _, _, hv =>
    DesRel.of_obsRel hd L ds hm hN (fun i D hi => have ⟨R, _, hR', _⟩ := hR i D hi; ⟨R, hR'⟩) h
      (fun d p q ps Ξ Θ B ψ hpos ts us hτ _ => hv d p q ps Ξ Θ B ψ hpos ts us hτ)
      (fun d p q ps Ξ Θ B ψ hpos ts us hτ D R hD hRi e => by
        obtain ⟨R', v, hR', hcv, hFv⟩ := hR _ D hD
        rw [hRi] at hR'
        cases hR'
        have he := hv d p q ps Ξ Θ B ψ hpos ts us hτ
        rw [e] at he
        exact hFv.of_validEqTerm hcv he)

-- ADE: none.
/-- `(corec)`, closed, by coinduction: pairs `P` of corecursors of the types of a block of codata
types of `Σ`, whose type declaration is meaningful, at the same levels and at equal arguments of its
parameters, are equal terms of their instance, when the observations of each pair by each
destructor, at equal arguments of its telescope, are equal terms of its result, or, for a recursive
destructor, compute to a pair of `P` of the type of its result: the relations that `(eq_ν)` gives
the instances, joined with `P`, are consistent with the clauses of the destructors, so that `(eq_ν)`
relates the pairs, or their observations make the instance true, for propositions. -/
theorem ValidEqTerm₀.corec (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {a₁ a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      a₁.toSubst a₂.toSubst)
    (P : Name → TermRel)
    (hP : ∀ T ∈ decl.codataTypes, ∀ v w, P T.name v w →
      ∃ (r₁ r₂ : Grade) (ss₁ ss₂ : Terms 0 []) (Ss₁ Ss₂ : States 0 []) (gs₁ gs₂ : CorecBranches 0 []),
        v = .corec r₁ T.name qs ls ps a₁ ss₁ Ss₁ gs₁ ∧ w = .corec r₂ T.name qs ls ps a₂ ss₂ Ss₂ gs₂ ∧
        ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
          (ψ : ResultOwnership ps'.length)
          (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps'),
          EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
            (hpos.obsSubst (v.observation T.name qs ls ps a₁) a₁.toSubst))) ts.toSubst us.toSubst →
          ValidEqTerm₀ sig ι (.obs T.name qs ls ps a₁ v d ts.terms)
              (.obs T.name qs ls ps a₂ w d us.terms)
              ((B.substLevels (ls.getFin hl)).subst (Subst.append
                (hpos.obsSubst (v.observation T.name qs ls ps a₁) a₁.toSubst) ts.toSubst)) ∨
            ∃ D', B.blockName decl.names = some D' ∧
              ∃ v' w', Computesι sig ι (.obs T.name qs ls ps a₁ v d ts.terms) v' ∧
                Computesι sig ι (.obs T.name qs ls ps a₂ w d us.terms) w' ∧ P D' v' w')
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    {v w : Term 0 []} (hvw : P T.name v w) :
    ValidEqTerm₀ sig ι v w (.inst T.name qs ls ps a₁) := by
  have hI : ValidEqTerm₀ sig ι (.inst T.name qs ls ps a₁) (.inst T.name qs ls ps a₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩) :=
    ValidEqTerm₀.instCodata hd ⟨hdecl, hT, rfl⟩ hv hq hl hp hadm has
  have hn := TypeDeclaration.codataTypes_nodup (hd.nodup hdecl)
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean : ∀ T' ∈ decl.codataTypes, _ := fun T' hT' =>
    (hv.destructors I hadm hT' ρ).2 _ _ hθ
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the first arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst a₁.toSubst
  have hX : ∀ D', Term.LevelEquiv (X D') (.inst D' qs ls ps a₁) := fun D' =>
    decl.blockInstance_atLevels_subst hq hl hp a₁ D'
  have hcX : ∀ D', Computesι sig ι (X D') (X D') := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hlev : ∀ {T' : CodataType decl.sorts decl.grades decl.levels decl.scope} {s : Quality}
      {rs : Nat → Option TermRel} {S : ObsRel},
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T'.body I).substLevels L) a₁.toSubst S →
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T'.body I).substLevels Lρ) a₁.toSubst S := fun hS =>
    DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  -- The observations of a pair of `P`, at the levels without variables.
  have hobs : ∀ T' ∈ decl.codataTypes, ∀ v w, P T'.name v w →
      ∃ (r₁ r₂ : Grade) (ss₁ ss₂ : Terms 0 []) (Ss₁ Ss₂ : States 0 []) (gs₁ gs₂ : CorecBranches 0 []),
        v = .corec r₁ T'.name qs ls ps a₁ ss₁ Ss₁ gs₁ ∧ w = .corec r₂ T'.name qs ls ps a₂ ss₂ Ss₂ gs₂ ∧
        ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
          (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
          (ψ : ResultOwnership ps'.length)
          (hpos : (T'.body I).Pos d p q Ξ Θ B ψ) (ts us : Args 0 [] ps'),
          EqSubst sig ι (Context.empty.append ((Θ.substLevels Lρ).subst
            (hpos.obsSubst (v.observation T'.name qs ls ps a₁) a₁.toSubst))) ts.toSubst us.toSubst →
          ValidEqTerm₀ sig ι (((v.observation T'.name qs ls ps a₁) d ps').subst ts.toSubst)
              (((w.observation T'.name qs ls ps a₂) d ps').subst us.toSubst)
              ((B.substLevels Lρ).subst (Subst.append
                (hpos.obsSubst (v.observation T'.name qs ls ps a₁) a₁.toSubst) ts.toSubst)) ∨
            ∃ D', B.blockName decl.names = some D' ∧
              ∃ v' w', Computesι sig ι (((v.observation T'.name qs ls ps a₁) d ps').subst
                  ts.toSubst) v' ∧
                Computesι sig ι (((w.observation T'.name qs ls ps a₂) d ps').subst us.toSubst) w' ∧
                P D' v' w' := fun T' hT' v w h => by
    obtain ⟨r₁, r₂, ss₁, ss₂, Ss₁, Ss₂, gs₁, gs₂, hv₁, hw₂, hob⟩ := hP T' hT' v w h
    refine ⟨r₁, r₂, ss₁, ss₂, Ss₁, Ss₂, gs₁, gs₂, hv₁, hw₂,
      fun d p q ps' Ξ Θ B ψ hpos ts us hτ => ?_⟩
    rw [Term.observation_subst_args, Term.observation_subst_args]
    have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hls Θ))) hτ
    exact (hob d p q ps' Ξ Θ B ψ hpos ts us hτ').imp_left fun he => he.levelEquiv
      (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) (Term.LevelEquiv.subst
        (Subst.LevelEquiv.refl _)
        (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
  have hw : Computesι sig ι (.inst T.name qs ls ps a₁) (.inst T.name qs ls ps a₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  cases hs : (decl.sort I).quality
  · rw [hs] at hI
    obtain ⟨S, hS, hU⟩ := hv.codataUnivRel hd hdecl hq hl hp hadm has hs
    have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
        ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
      fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
        fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
    -- The relations of the instances, joined with `P`.
    let Y : Name → TermRel := fun D' a b => CodataType.blockRel decl.codataTypes S D' a b ∨ P D' a b
    have hF : ∀ D', D' ∈ decl.names → FieldRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) .type (X D')
        ((CodataType.blockRel decl.codataTypes S D').computed sig ι) := fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT hD'
      exact FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
        (.univ rfl (hU T' hT').1) (hX _).symm
    have hcons : ∀ T' ∈ decl.codataTypes, ∀ a b, Y T'.name a b →
        corecRel T'.name (S Y T') a b := by
      intro T' hT' a b hab
      rcases hab with hab | hab
      · exact corecRel_mono (hmono _ _ (fun _ _ _ h => .inl h) T' hT') _ _
          (CodataType.blockRel_unfold hmono hT' hab)
      · obtain ⟨r₁, r₂, ss₁, ss₂, Ss₁, Ss₂, gs₁, gs₂, rfl, rfl, hob⟩ := hobs T' hT' a b hab
        refine ⟨_, _, ⟨r₁, qs, ls, ps, _, a₁, ss₁, Ss₁, gs₁, rfl, rfl⟩,
          ⟨r₂, qs, ls, ps, _, a₂, ss₂, Ss₂, gs₂, rfl, rfl⟩, ?_⟩
        refine DesRel.of_obsRel hd Lρ (T'.body I) (hmean T' hT') (fun i hi => by rw [hi]; rfl)
          (fun i D' hi => by rw [hi]; exact ⟨_, rfl⟩) (hlev (hS Y T' hT'))
          (fun d p q ps' Ξ Θ B ψ hpos ts us hτ hr => (hob d p q ps' Ξ Θ B ψ hpos ts us hτ).resolve_right
            fun ⟨D', hD', _⟩ => by rw [← hpos.recursionAt_index, hr] at hD'; cases hD')
          (fun d p q ps' Ξ Θ B ψ hpos ts us hτ D' R hD' hR e => ?_)
        rw [hD'] at hR
        cases hR
        rcases hob d p q ps' Ξ Θ B ψ hpos ts us hτ with he | ⟨D'', hD'', v', w', hv', hw', hP'⟩
        · exact TermRel.computed_mono (fun _ _ h => .inl h)
            ((hF D' (Destructors.recursionAt_mem hD')).of_validEqTerm (hcX D') (by rw [e] at he; exact he))
        · rw [← hpos.recursionAt_index, hD'] at hD''
          cases hD''
          exact ⟨v', w', hv', hw', .inr hP'⟩
    have hrel : CodataType.blockRel decl.codataTypes S T.name v w := ⟨Y, hcons, .inr hvw⟩
    have hU' : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
        (.inst T.name qs ls ps a₁) (CodataType.blockRel decl.codataTypes S T.name) :=
      levelRel_univ_iff.2 (hU T hT).1
    obtain ⟨r₁, r₂, ss₁, ss₂, Ss₁, Ss₂, gs₁, gs₂, rfl, rfl, -⟩ := hP T hT v w hvw
    have hct : ∀ (r : Grade) (a : InstanceArgs 0 [] decl.scope) (ss : Terms 0 [])
        (Ss : States 0 []) (gs : CorecBranches 0 []),
        Computesι sig ι (.corec r T.name qs ls ps a ss Ss gs) (.corec r T.name qs ls ps a ss Ss gs) :=
      fun _ _ _ _ _ => ⟨.refl _, .corec _ _ _ _ _ _ _ _ _⟩
    refine ⟨(ValidEqTerm₀.univType hI).left,
      fun _ => ⟨_, _, _, _, hw, hct _ _ _ _ _, hct _ _ _ _ _, .univ _ hU', hrel⟩,
      fun ⟨v, hv', _, _, hP⟩ => ?_⟩
    cases Computesι.det hd hw hv'
    exact (HasEq.univ_not_prop hd hU' hP).elim
  · rw [hs] at hI
    obtain ⟨S, hS, hPr⟩ := hv.codataPropRel hd hdecl hq hl hp hadm has hs
    have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
        S B T' o₁ o₂ → S B' T' o₁ o₂ :=
      fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
        fun _ => Option.rel_map (fun D _ _ => hB D) _
    -- The truths of the instances, joined with `P`.
    let Y : Name → Prop := fun D' => CodataType.blockTruth decl.codataTypes S D' ∨ ∃ a b, P D' a b
    have hF : ∀ D', D' ∈ decl.names → FieldRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) .prop (X D')
        (fun _ _ => CodataType.blockTruth decl.codataTypes S D') := fun D' hD' => by
      obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT hD'
      exact FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
        (.prop (hPr T' hT').1) (hX _).symm
    have hcons : ∀ T' ∈ decl.codataTypes, Y T'.name → (S Y T').truth := by
      intro T' hT' hY
      rcases hY with hY | ⟨a, b, hab⟩
      · exact ObsRel.truth_mono (hmono _ _ (fun _ h => .inl h) T' hT')
          (CodataType.blockTruth_unfold hmono hT' hY)
      · obtain ⟨r₁, r₂, ss₁, ss₂, Ss₁, Ss₂, gs₁, gs₂, rfl, rfl, hob⟩ := hobs T' hT' a b hab
        have hS₁ := DesRel.of_obsRel hd Lρ (T'.body I) (hmean T' hT')
          (fun i hi => by rw [hi]; rfl) (fun i D' hi => by rw [hi]; exact ⟨_, rfl⟩)
          (hlev (hS Y T' hT'))
          (fun d p q ps' Ξ Θ B ψ hpos ts us hτ hr => (hob d p q ps' Ξ Θ B ψ hpos ts us hτ).resolve_right
            fun ⟨D', hD', _⟩ => by rw [← hpos.recursionAt_index, hr] at hD'; cases hD')
          (fun d p q ps' Ξ Θ B ψ hpos ts us hτ D' R hD' hR e => by
            rw [hD'] at hR
            cases hR
            rcases hob d p q ps' Ξ Θ B ψ hpos ts us hτ with he | ⟨D'', hD'', v', w', -, -, hP'⟩
            · exact .inl ((hF D' (Destructors.recursionAt_mem hD')).of_validEqTerm (hcX D')
                (by rw [e] at he; exact he))
            · rw [← hpos.recursionAt_index, hD'] at hD''
              cases hD''
              exact .inr ⟨v', w', hP'⟩)
        have hSp := DesRel.isPer hd ih (fun i x hx => by
          cases hr : (T'.body I).recursionAt decl.names i with
          | none => rw [hr] at hx; cases hx
          | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩)
          (hlev (hS Y T' hT'))
        exact ⟨_, hSp.trans hS₁ (hSp.symm hS₁)⟩
    have htrue : CodataType.blockTruth decl.codataTypes S T.name := ⟨Y, hcons, .inr ⟨v, w, hvw⟩⟩
    have hP' : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).prop
        (.inst T.name qs ls ps a₁) (CodataType.blockTruth decl.codataTypes S T.name) :=
      levelRel_prop_iff.2 (hPr T hT).1
    refine ⟨(ValidEqTerm₀.propType hI).left, fun hn => absurd ⟨_, hw, _, _, hP'⟩ hn,
      fun _ => ⟨_, fun _ _ => CodataType.blockTruth decl.codataTypes S T.name, hw,
        .prop _ _ hP' fun _ _ => .rfl, htrue⟩⟩

/-- The scope of a destructor, over the state of a corecursor, at the corecursor from the state,
substituted by a closed substitution of the context followed by closed arguments of the state, is
the scope of the destructor at the corecursor from these arguments. -/
theorem Destructors.Pos.obsSubst_corecAt {k' : Nat} {Γ Δ : Scope} {d : Name} {p q : Grade}
    {ps₁ : List Parameter} {ns : List Name} {ds : Destructors k' Δ ns} {Ξ : Scope}
    {Θ : Telescope k' Ξ ps₁} {B : Term k' (Ξ.extend ps₁.length)} {ψ : ResultOwnership ps₁.length}
    (hpos : ds.Pos d p q Ξ Θ B ψ) (σ : Subst 0 [] Γ) (r : Grade) (D : Name) (qs : List Quality)
    (ls : List (Level 0)) (ps : List Grade) (as : InstanceArgs 0 Γ Δ) (Ss : States 0 Γ)
    (gs : CorecBranches 0 Γ) {ps' : List Parameter} (ss : Args 0 [] ps')
    (hΔ : ∀ {a} (x : Var Δ a), ((as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) = (as.subst σ).toSubst x) :
    ∀ {a} (x : Var Ξ a),
      (hpos.obsSubst ((Term.corecAt r D qs ls ps as Ss gs ps').observation D qs ls ps
          (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) =
      hpos.obsSubst ((Term.corec r D qs ls ps (as.subst σ) ss.terms (Ss.subst σ)
        (gs.subst σ)).observation D qs ls ps (as.subst σ)) (as.subst σ).toSubst x :=
  hpos.obsSubst_subst (Subst.append σ ss.toSubst) (fun d' ps'' => by
    rw [Term.observation_subst, Term.corecAt_subst_append,
      InstanceArgs.subst_rename_of (ξ := Ren.weakenN ps'.length) (θ' := σ)
        (fun y => Subst.append_weakenN σ ss.toSubst y)])
    hΔ

-- ADE: none.
/-- The arguments of an instance, renamed under the variables of a state, substituted by a closed
substitution followed by closed arguments of the state, are the arguments substituted, as a
substitution of the parameters. -/
theorem InstanceArgs.toSubst_rename_subst_append {Γ Δ : Scope} (σ : Subst 0 [] Γ)
    (as : InstanceArgs 0 Γ Δ) {ps' : List Parameter} (ss : Args 0 [] ps') {a : Scope.Entry}
    (x : Var Δ a) :
    ((as.rename (Ren.weakenN ps'.length)).toSubst x).subst
        (Subst.liftN a.params.length (Subst.append σ ss.toSubst)) = (as.subst σ).toSubst x := by
  rw [InstanceArgs.toSubst_subst,
    InstanceArgs.subst_rename_of (ξ := Ren.weakenN ps'.length) (θ' := σ)
      (fun y => Subst.append_weakenN σ ss.toSubst y)]

-- ADE: none.
/-- `(β_⟶)` for a corecursor whose states and branches are substituted by a closed substitution of
the context, from closed arguments of a state: the observation steps to the branch of its
destructor at the substitution, the state and the arguments, resumed if the destructor is
recursive. -/
theorem Red.beta_corec (hd : sig.Distinct) {Γ : Scope} {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h₀ : sig.HasCodataType T.name decl T) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades) {as : InstanceArgs 0 Γ decl.scope} {r : Grade}
    {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {h' i : Nat} {d : Name}
    (hi : decl.codataCases[i]? = some (h', T, d)) {p q : Grade} {ps₁ : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
    {ψ : ResultOwnership ps₁.length} (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {ps' : List Parameter} {g : Term 0 ((Γ.extend ps'.length).extend ps₁.length)}
    (hg : gs.get i = some ⟨0, ps'.length, ps₁.length, g⟩) (σ : Subst 0 [] Γ)
    (ss : Args 0 [] ps') (ts : Args 0 [] ps₁) {Δ' : Scope} {D' : Name} {qs' : List Quality}
    {ls' : List (Level 0)} {ps'' : List Grade} {as' : InstanceArgs 0 [] Δ'} :
    Red (sig.interpret ι)
      (.obs D' qs' ls' ps'' as' (.corec r T.name qs ls ps (as.subst σ) ss.terms (Ss.subst σ)
        (gs.subst σ)) d ts.terms)
      (Term.observed decl.names (B.blockName decl.names) r qs ls ps (as.subst σ) (Ss.subst σ)
        (gs.subst σ) ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
        (ψ.constant.getD .unrestrictedUnrestricted)
        (g.subst (Subst.append (Subst.append σ ss.toSubst) ts.toSubst))) := by
  rw [← hpos.resultName decl.names (hd.destructors_nodup h₀),
    ← hpos.resultConstant (hd.destructors_nodup h₀)]
  exact .beta (List.mem_map_of_mem (f := Entry.interpret ι) h₀.1) hi rfl hq hl hp
    (CorecBranches.get_subst σ hg) (Term.instantiateTerms₂_subst_append σ g _ _)

-- ADE: none.
/-- The branches of a destructor, as `(corec)` and `(corec_≡)` premise them, at equal substitutions
of the context, equal closed arguments of the state and equal arguments of the telescope of the
destructor, are equal terms of the result of the destructor at the first ones, the positions of the
state of the type it names if it is recursive. -/
theorem ValidEqTerm₀.corecBranch {Γ : Scope} {ctx : Context 0 Γ} {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} {hq : qs.length = decl.sorts}
    {hl : ls.length = decl.levels} {hp : ps.length = decl.grades}
    {as : InstanceArgs 0 Γ decl.scope} {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ}
    {ps' : List Parameter} {S : Telescope 0 Γ ps'} {d : Name} {p q : Grade}
    {ps₁ : List Parameter} {Ξ : Scope} {Θ : Telescope decl.levels Ξ ps₁}
    {B : Term decl.levels (Ξ.extend ps₁.length)} {ψ : ResultOwnership ps₁.length}
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
    {g₁ g₂ : Term 0 ((Γ.extend ps'.length).extend ps₁.length)}
    (hgv : ValidEqTermΓ sig ι ((ctx.append S).append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corecAt r T.name qs ls ps as Ss gs ps').observation T.name qs ls
        ps (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst)))
      g₁ g₂
      (Term.branchResult decl.names B
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted)
        ((Ss.rename (Ren.weakenN ps'.length)).rename (Ren.weakenN ps₁.length))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hpos.obsSubst ((Term.corecAt r T.name qs ls ps as Ss gs ps').observation T.name qs ls
            ps (as.rename (Ren.weakenN ps'.length))) (as.rename (Ren.weakenN ps'.length)).toSubst)))))
    {σ₁ σ₂ : Subst 0 [] Γ} (hσ : EqSubst sig ι ctx σ₁ σ₂) {ss₁ ss₂ : Args 0 [] ps'}
    (hss : EqSubst sig ι (Context.empty.append (S.subst σ₁)) ss₁.toSubst ss₂.toSubst)
    {ts us : Args 0 [] ps₁}
    (hts : EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corec r T.name qs ls ps (as.subst σ₁) ss₁.terms (Ss.subst σ₁)
        (gs.subst σ₁)).observation T.name qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst)))
      ts.toSubst us.toSubst) :
    ValidEqTerm₀ sig ι (g₁.subst (Subst.append (Subst.append σ₁ ss₁.toSubst) ts.toSubst))
      (g₂.subst (Subst.append (Subst.append σ₂ ss₂.toSubst) us.toSubst))
      (Term.branchResult decl.names B
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted) (Ss.subst σ₁)
        ((B.substLevels (ls.getFin hl)).subst (Subst.append
          (hpos.obsSubst ((Term.corec r T.name qs ls ps (as.subst σ₁) ss₁.terms (Ss.subst σ₁)
            (gs.subst σ₁)).observation T.name qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst)
          ts.toSubst))) := by
  -- The scope of the destructor at the first state.
  have hc := fun (a : Scope.Entry) (x : Var Ξ a) =>
    hpos.obsSubst_corecAt σ₁ r T.name qs ls ps as Ss gs ss₁
      (InstanceArgs.toSubst_rename_subst_append σ₁ as ss₁) x
  -- The context of the branch at the substitutions and the states.
  have hstate : EqSubst sig ι (ctx.append S) (Subst.append σ₁ ss₁.toSubst)
      (Subst.append σ₂ ss₂.toSubst) :=
    (EqSubst.append_append_iff ctx S _ _ _ _).2 ⟨hσ, hss⟩
  have hτ := (EqSubst.append_append_iff (ctx.append S) _ _ _ _ _).2
    ⟨hstate, by rw [Telescope.subst_subst_of (fun x => hc _ x)]; exact hts⟩
  have hb := hgv.2 _ _ hτ
  have hS : ((Ss.rename (Ren.weakenN ps'.length)).rename (Ren.weakenN ps₁.length)).subst
      (Subst.append (Subst.append σ₁ ss₁.toSubst) ts.toSubst) = Ss.subst σ₁ := by
    rw [States.subst_rename_of (ξ := Ren.weakenN ps₁.length)
        (θ' := Subst.append σ₁ ss₁.toSubst) (fun y => Subst.append_weakenN _ ts.toSubst y),
      States.subst_rename_of (ξ := Ren.weakenN ps'.length) (θ' := σ₁)
        (fun y => Subst.append_weakenN σ₁ ss₁.toSubst y)]
  rw [Term.branchResult_subst, hS] at hb
  conv at hb =>
    arg 5
    arg 7
    rw [← Term.subst_append, Term.subst_subst_of (Subst.liftN_subst_of _ (fun x => hc _ x)),
      Term.subst_append]
  exact hb

-- ADE: none.
/-- The branches `gs₁` and `gs₂` of two corecursors are equal terms of the results of their
destructors, as `(corec_≡)` premises them, over the states `Ss` and the corecursors of the first
branches: the premise that the Lean of `(corec_≡)` reads, at the levels without variables. -/
def CorecBranchesEqValid (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade)
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ)
    (gs₁ gs₂ : CorecBranches 0 Γ) : Prop :=
  (∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps''),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    ∀ (p q : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
      (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length),
    (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ →
    ∃ g₁ g₂, gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ ∧
      gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩) ∧
  ∀ i j T' d (ps'' : List Parameter) (S' : Telescope 0 Γ ps'') (p q : Grade)
    (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
    (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership ps₁.length)
    (g₁ g₂ : Term 0 ((Γ.extend ps''.length).extend ps₁.length)),
    decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
    (hd : (T'.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ) →
    gs₁.get i = some ⟨0, ps''.length, ps₁.length, g₁⟩ →
    gs₂.get i = some ⟨0, ps''.length, ps₁.length, g₂⟩ →
    ValidEqTermΓ sig ι ((ctx.append S').append ((Θ.substLevels (ls.getFin hl)).subst
      (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs ls
        ps (as.rename (Ren.weakenN ps''.length))) (as.rename (Ren.weakenN ps''.length)).toSubst)))
      g₁ g₂
      (Term.branchResult decl.names B
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)) r
        (ψ.constant.getD .unrestrictedUnrestricted)
        ((Ss.rename (Ren.weakenN ps''.length)).rename (Ren.weakenN ps₁.length))
        ((B.substLevels (ls.getFin hl)).subst (Subst.liftN _
          (hd.obsSubst ((Term.corecAt r T'.name qs ls ps as Ss gs₁ ps'').observation T'.name qs
            ls ps (as.rename (Ren.weakenN ps''.length)))
            (as.rename (Ren.weakenN ps''.length)).toSubst))))

/-- The branches of a corecursor are terms of the results of their destructors, as `(corec)`
premises them: the premise that the Lean of `(corec)` and of `(β)` reads, at the levels without
variables. -/
def CorecBranchesValid (sig : Signature) (ι : Interpretation) {Γ : Scope} (ctx : Context 0 Γ)
    (decl : TypeDeclaration) (qs : List Quality) (ls : List (Level 0)) (ps : List Grade)
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 Γ decl.scope) (r : Grade) (Ss : States 0 Γ) (gs : CorecBranches 0 Γ) :
    Prop :=
  CorecBranchesEqValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs gs

-- ADE: `prod-congᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/Sigma.agda`.
/-- `(corec_≡)` keeps the meaning: at equal substitutions of the context, the corecursors of the
block from equal states are pairs of canonical terms whose observations by each destructor compute,
by `(β_⟶)`, as the branches of the destructor, which the premises make equal, and, for a recursive
destructor, resume them: to equal terms already built, or to corecursors of the block from equal
new states, which unpack from the packings of the positions; the coinduction of the closed
`(corec)` makes them all equal; the second corecursor is at the levels of the first one, which its
levels equal, and the instance is a type, as `(D)` gives it. -/
theorem ValidEqTermΓ.corec {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls₁ ls₂ : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl₁ : ls₁.length = decl.levels)
    (hl₂ : ls₂.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sigT.HasPrelude)
    {as₁ as₂ : InstanceArgs 0 Γ decl.scope}
    (has : ValidEqInstanceArgsΓ sig ι ctx as₁ as₂
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls₁.getFin hl₁)))
    (hls : ∀ i, ls₁.getFin hl₁ i ≈ ls₂.getFin hl₂ i)
    {r : Grade} {Ss₁ Ss₂ : States 0 Γ} {gs₁ gs₂ : CorecBranches 0 Γ} {h' : Nat}
    {ps' : List Parameter} {S₁ : Telescope 0 Γ ps'} {ss₁ ss₂ : Args 0 Γ ps'}
    (hh : decl.codataTypes[h']? = some T) (hS₁ : Ss₁.get h' = some ⟨0, ps', S₁⟩)
    (hss : ValidEqArgsΓ sig ι ctx ss₁ ss₂ S₁)
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S₁' S₂' : Telescope 0 Γ ps''),
        Ss₁.get j = some ⟨0, ps'', S₁'⟩ ∧ Ss₂.get j = some ⟨0, ps'', S₂'⟩)
    (hg : CorecBranchesEqValid sig ι ctx decl qs ls₁ ps hq hl₁ hp as₁ r Ss₁ gs₁ gs₂) :
    ValidEqTermΓ sig ι ctx (.corec r D qs ls₁ ps as₁ ss₁.terms Ss₁ gs₁)
      (.corec r D qs ls₂ ps as₂ ss₂.terms Ss₂ gs₂) (.inst D qs ls₁ ps as₁) := by
  obtain ⟨h₀, hv⟩ := hent.hasCodataType h
  have hctx := has.1
  have hd := hctx.distinct
  have hD : T.name = D := h.2.2
  subst hD
  have hnd := hd.nodup h₀.1
  have hn := TypeDeclaration.codataTypes_nodup hnd
  have hpre' : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sig.HasPrelude :=
    fun he e he' => (hent e (hpre he e he')).1
  have hcl : ∀ σ₁ σ₂, EqSubst sig ι ctx σ₁ σ₂ →
      ValidEqTerm₀ sig ι
        (.corec r T.name qs ls₁ ps (as₁.subst σ₁) (ss₁.subst σ₁).terms (Ss₁.subst σ₁) (gs₁.subst σ₁))
        (.corec r T.name qs ls₁ ps (as₂.subst σ₂) (ss₂.subst σ₂).terms (Ss₂.subst σ₂) (gs₂.subst σ₂))
        (.inst T.name qs ls₁ ps (as₁.subst σ₁)) := fun σ₁ σ₂ hσ => by
    -- The corecursors of the block from equal closed states.
    let P : Name → TermRel := fun D' v w =>
      ∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
        (ps'' : List Parameter) (S' : Telescope 0 Γ ps'') (ts₁ ts₂ : Args 0 [] ps''),
        decl.codataTypes[j]? = some T' ∧ T'.name = D' ∧ Ss₁.get j = some ⟨0, ps'', S'⟩ ∧
        EqSubst sig ι (Context.empty.append (S'.subst σ₁)) ts₁.toSubst ts₂.toSubst ∧
        v = .corec r D' qs ls₁ ps (as₁.subst σ₁) ts₁.terms (Ss₁.subst σ₁) (gs₁.subst σ₁) ∧
        w = .corec r D' qs ls₁ ps (as₂.subst σ₂) ts₂.terms (Ss₂.subst σ₂) (gs₂.subst σ₂)
    refine ValidEqTerm₀.corec hd h₀.1 hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ) P ?_
      (List.mem_of_getElem? hh)
      ⟨h', T, ps', S₁, ss₁.subst σ₁, ss₂.subst σ₂, hh, rfl, hS₁, hss.2 σ₁ σ₂ hσ, rfl, rfl⟩
    rintro T' hT' v w ⟨j, T'', ps'', S', ts₁, ts₂, hj, hn', hSj, hts, rfl, rfl⟩
    cases List.eq_of_nodup_map hn (List.mem_of_getElem? hj) hT' hn'
    refine ⟨r, r, ts₁.terms, ts₂.terms, Ss₁.subst σ₁, Ss₂.subst σ₂, gs₁.subst σ₁, gs₂.subst σ₂,
      rfl, rfl, fun d p q ps₁ Ξ Θ B ψ hpos bs₁ bs₂ hbs => ?_⟩
    have h₀' : sig.HasCodataType T'.name decl T' := ⟨h₀.1, List.mem_of_getElem? hj, rfl⟩
    have hmem : (j, T', d) ∈ decl.codataCases := by
      have := TypeDeclaration.mem_casesFrom_of (f := CodataType.destructors) (i := 0) hj hpos.mem
      rwa [Nat.zero_add] at this
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    obtain ⟨g₁, g₂, hg₁, hg₂⟩ := hg.1 i j T' d ps'' S' hi hSj p q ps₁ Ξ Θ B ψ hpos
    have hb := ValidEqTerm₀.corecBranch hpos
      (hg.2 i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g₁ g₂ hi hSj hpos hg₁ hg₂) hσ hts hbs
    have hred₁ := Red.beta_corec (ι := ι) hd h₀' hq hl₁ hp hi hpos hg₁ σ₁ ts₁ bs₁
      (D' := T'.name) (qs' := qs) (ls' := ls₁) (ps'' := ps) (as' := as₁.subst σ₁)
      (as := as₁) (Ss := Ss₁) (r := r)
    have hred₂ := Red.beta_corec (ι := ι) hd h₀' hq hl₁ hp hi hpos hg₂ σ₂ ts₂ bs₂
      (D' := T'.name) (qs' := qs) (ls' := ls₁) (ps'' := ps) (as' := as₂.subst σ₂)
      (as := as₂) (Ss := Ss₂) (r := r)
    cases hbn : B.blockName decl.names with
    | none =>
      simp only [Term.branchResult, hbn] at hb
      simp only [Term.observed, hbn] at hred₁ hred₂
      exact .inl (((ValidEqTerm₀.red_iff hd hred₂).2
        ((ValidEqTerm₀.red_iff hd hred₁).2 hb).symm).symm)
    | some D'' =>
      -- The type of the result, its state, and the prelude that its positions need.
      obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT' (Term.blockName_mem hbn)
      obtain ⟨j₃, hj₃⟩ := List.mem_iff_getElem?.1 hT₃
      obtain ⟨ps₃, S₃, S₃', hS₃, hS₃'⟩ := hSs j₃ T₃ hj₃
      have hpr : sig.HasPrelude := hpre' ⟨j, T', hpos.index, T₃.name, hj,
        by rw [hpos.recursionAt_index]; exact hbn⟩
      have hst₁ : (Ss₁.subst σ₁).stateOf decl.names T₃.name =
          some ⟨ps₃, S₃.subst σ₁, Ss₁.sorts j₃⟩ := by
        rw [States.stateOf_subst, States.stateOf_of_get hnd hj₃ hS₃]
        rfl
      have hst₂ : (Ss₂.subst σ₂).stateOf decl.names T₃.name =
          some ⟨ps₃, S₃'.subst σ₂, Ss₂.sorts j₃⟩ := by
        rw [States.stateOf_subst, States.stateOf_of_get hnd hj₃ hS₃']
        rfl
      simp only [Term.branchResult, hbn, hst₁] at hb
      simp only [Term.observed, hbn, hst₁, hst₂] at hred₁ hred₂
      rcases ValidEqTerm₀.positions_inv hpr hb with
        ⟨x₁, x₂, ⟨_, _, _, _, _, hx₁⟩, ⟨_, _, _, _, _, hx₂⟩, hx⟩ |
        ⟨t₁, t₂, ⟨_, _, _, _, _, ht₁⟩, ⟨_, _, _, _, _, ht₂⟩, ht⟩
      · obtain ⟨us₁, us₂, hp₁, hp₂, hus⟩ := ValidEqTerm₀.pack_inv hpr _ _ _ hx
        exact .inr ⟨T₃.name, rfl, _, _,
          ⟨.step hred₁ (RedStar.resume_next hpr hx₁.1 us₁ hp₁), .corec _ _ _ _ _ _ _ _ _⟩,
          ⟨.step hred₂ (RedStar.resume_next hpr hx₂.1 us₂ hp₂), .corec _ _ _ _ _ _ _ _ _⟩,
          j₃, T₃, ps₃, S₃, us₁, us₂, hj₃, rfl, hS₃, hus, rfl, rfl⟩
      · exact .inl (((ValidEqTerm₀.redStar_iff hd (.step hred₂ (RedStar.resume_done hpr ht₂.1))).2
          ((ValidEqTerm₀.redStar_iff hd (.step hred₁ (RedStar.resume_done hpr ht₁.1))).2
            ht).symm).symm)
  refine ⟨⟨hctx, fun σ₁ σ₂ hσ => ?_⟩, fun σ₁ σ₂ hσ => ?_⟩
  · have hI := (ValidEqTerm₀.instCodata hd h₀ hv hq hl₁ hp hadm (has.2 σ₁ σ₂ hσ)).trans
      (ValidEqTerm₀.instCodata hd h₀ hv hq hl₁ hp hadm (has.2 σ₂ σ₂ (hσ.right hctx))).symm
    show ValidEqType₀ sig ι (.inst T.name qs ls₁ ps (as₁.subst σ₁))
      (.inst T.name qs ls₁ ps (as₁.subst σ₂))
    revert hI
    show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
      (decl.sort (.ofLists qs ps hq hp)).level.subst (ls₁.getFin hl₁)⟩) → _
    cases (decl.sort (.ofLists qs ps hq hp)).quality
    · exact ValidEqTerm₀.univType
    · exact ValidEqTerm₀.propType
  · rw [Term.corec_subst, Term.corec_subst]
    exact (hcl σ₁ σ₂ hσ).levelEquiv (Term.LevelEquiv.refl _)
      (.corec r T.name qs ps (Level.ListEquiv.of_getFin hl₁ hl₂ hls)
        (InstanceArgs.LevelEquiv.refl _) (Terms.LevelEquiv.refl _) (States.LevelEquiv.refl _)
        (CorecBranches.LevelEquiv.refl _))
      (Term.LevelEquiv.refl _)

-- ADE: none.
/-- `(corec)` keeps the meaning: it is `(corec_≡)` at the same corecursor. -/
theorem ValidTermΓ.corec {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sigT.HasPrelude)
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {h' : Nat} {ps' : List Parameter}
    {S : Telescope 0 Γ ps'} {ss : Args 0 Γ ps'} (hh : decl.codataTypes[h']? = some T)
    (hS : Ss.get h' = some ⟨0, ps', S⟩) (hss : ValidArgsΓ sig ι ctx ss S)
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hg : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs) :
    ValidTermΓ sig ι ctx (.corec r D qs ls ps as ss.terms Ss gs) (.inst D qs ls ps as) :=
  ValidEqTermΓ.corec hent h hq hl hl hp hadm hpre has (fun _ => Level.equivalence.refl _) hh hS
    hss (fun j T' hj => have ⟨ps'', S', hS'⟩ := hSs j T' hj; ⟨ps'', S', S', hS', hS'⟩) hg

-- ADE: `β-redᵛ`, `Σ-β₁ᵛ` and `Σ-β₂ᵛ`, in
-- `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(β)` keeps the meaning: the observation is a term of its result, as `(d)` and `(corec)` give
it, so that, at equal substitutions of the context, it is equal to the observation at the second
one, which steps, by `(β_⟶)`, to the right-hand side substituted. -/
theorem ValidEqTermΓ.beta {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    (hpre : (∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope)
      (i : Nat) (D' : Name),
      decl.codataTypes[j]? = some T' ∧
      (T'.body (.ofLists qs ps hq hp)).recursionAt decl.names i = some D') → sigT.HasPrelude)
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl)))
    {r : Grade} {Ss : States 0 Γ} {gs : CorecBranches 0 Γ} {h' i : Nat} {ps' : List Parameter}
    {S : Telescope 0 Γ ps'} {ss : Args 0 Γ ps'} {d : Name} {p q : Grade} {ps₀ : List Parameter}
    {Ξ₀ : Scope} {Θ₀ : Telescope decl.levels Ξ₀ ps₀} {B₀ : Term decl.levels (Ξ₀.extend ps₀.length)}
    {ψ₀ : ResultOwnership ps₀.length} {g : Term 0 ((Γ.extend ps'.length).extend ps₀.length)}
    {bs : Args 0 Γ ps₀} (hh : decl.codataTypes[h']? = some T) (hS : Ss.get h' = some ⟨0, ps', S⟩)
    (hss : ValidArgsΓ sig ι ctx ss S) (hi : decl.codataCases[i]? = some (h', T, d))
    (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ₀ Θ₀ B₀ ψ₀)
    (hgi : gs.get i = some ⟨0, ps'.length, ps₀.length, g⟩)
    (hbs : ValidArgsΓ sig ι ctx bs ((Θ₀.substLevels (ls.getFin hl)).subst
      (hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D qs ls ps as)
        as.toSubst)))
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' →
      ∃ (ps'' : List Parameter) (S' : Telescope 0 Γ ps''), Ss.get j = some ⟨0, ps'', S'⟩)
    (hg : CorecBranchesValid sig ι ctx decl qs ls ps hq hl hp as r Ss gs) :
    ValidEqTermΓ sig ι ctx (.obs D qs ls ps as (.corec r D qs ls ps as ss.terms Ss gs) d bs.terms)
      (Term.observed decl.names (B₀.blockName decl.names) r qs ls ps as Ss gs
        ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
        (ψ₀.constant.getD .unrestrictedUnrestricted)
        ((g.instantiate (bs.rename (Ren.weakenN ps'.length))).instantiate ss))
      (((B₀.substLevels (ls.getFin hl)).subst
        (Subst.liftN _ (hpos.obsSubst ((Term.corec r D qs ls ps as ss.terms Ss gs).observation D
          qs ls ps as) as.toSubst))).instantiate bs) := by
  have hc := ValidTermΓ.corec hent h hq hl hp hadm hpre has hh hS hss hSs hg
  have hobs := ValidEqTermΓ.obs hent h hq hl hl hp hadm hpos has (fun _ => Level.equivalence.refl _)
    hc hbs
  obtain ⟨h₀, -⟩ := hent.hasCodataType h
  have hd := has.1.distinct
  have hD : T.name = D := h.2.2
  subst hD
  refine ⟨hobs.1, fun σ₁ σ₂ hσ => ?_⟩
  have hred := Red.beta_corec (ι := ι) hd h₀ hq hl hp hi hpos hgi σ₂ (ss.subst σ₂) (bs.subst σ₂)
    (D' := T.name) (qs' := qs) (ls' := ls) (ps'' := ps) (as' := as.subst σ₂) (as := as) (Ss := Ss)
    (r := r)
  rw [← Term.instantiate_instantiate_subst_closed, ← Term.observed_subst] at hred
  have h₁ := hobs.2 σ₁ σ₂ hσ
  simp only [Term.subst, ← Args.terms_subst] at h₁
  have h₂ := ((ValidEqTerm₀.red_iff hd hred).1 h₁.symm).symm
  simp only [Term.subst, ← Args.terms_subst]
  exact h₂

/-! ## Extensionality of the Codata Types

Two terms of an instance of a codata type whose observations are equal, destructor by destructor,
are equal: the equality of the destructors relates their observations, as it relates those of two
corecursors, and then the observations of the corecursors they compute to, which compute as theirs.
On a proposition, the observations of the first term, related to themselves, make it true. -/

-- ADE: none.
/-- The equality of destructors relates the observations `o₁` and `o₂` when it relates observations
`f₁` and `f₂` that compute as them, at relations of the recursive destructors that are equalities
of the terms of types of the graph: the abstractions for each destructor compute as each other, so
that the equality of its result relates them, and the destructors after it are the same for
abstractions that the equality of the destructor relates. -/
theorem DesRel.obsEquiv (hd : sig.Distinct) {n : Nat} {s : Quality} :
    {rs : Nat → Option TermRel} → {Γ : Scope} → {ns : List Name} → {ds : Destructors 0 Γ ns} →
      {θ : Subst 0 [] Γ} → {S : ObsRel} →
      (∀ i R, rs i = some R → ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R) →
      DesRel sig ι n (fun m _ => levelRel sig ι m) s rs ds @θ S →
      {f₁ f₂ o₁ o₂ : Observations} → S f₁ f₂ → ObsEquiv sig ι s f₁ o₁ →
      ObsEquiv sig ι s f₂ o₂ → S o₁ o₂
  | _, _, _, .nil, _, _, _, h, _, _, _, _, _, _, _ => by
    cases h
    trivial
  | rs, _, _, .cons (d := d) (ps := ps) _ _ _ _ _ _, _, _, hRF, h, f₁, f₂, o₁, o₂, hS, hf₁, hf₂ => by
    have hc : ∀ {f o : Observations}, ObsEquiv sig ι s f o → s = .prop ∨
        ∀ τ w, Computesι sig ι ((f d ps).subst τ) w ↔ Computesι sig ι ((o d ps).subst τ) w :=
      fun hf => hf.imp_right fun h τ w => h d ps τ w
    have hRF' : ∀ i R, rs (i + 1) = some R →
        ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v R := fun i => hRF (i + 1)
    cases h with
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ hΘ F hB hF hBresp G hG hresp =>
      obtain ⟨hA, hGf⟩ := hS
      have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
      have hSp := TelRel.isPer hd ih (fun _ _ h => by cases h) hΘ
      have hFv : ∀ ts : Args 0 [] ps, SΘ ts.terms ts.terms →
          ∃ v, FieldRel sig ι n (fun m _ => levelRel sig ι m) s v (F ts.terms) := fun ts hts =>
        have ⟨v, hv⟩ := hB ts hts
        ⟨v, hF ts hts v hv⟩
      have hEp := AbstractionRel.isPer hSp (fun ts hts =>
        have ⟨_, hv⟩ := hFv ts hts
        FieldRel.isPer hd ih hv) hBresp
      have hA' : AbstractionRel SΘ F (o₁ d ps) (o₂ d ps) :=
        (AbstractionRel.congr_computes hSp hFv (by
          rcases hc hf₁ with h₁ | h₁
          · exact .inl h₁
          rcases hc hf₂ with h₂ | h₂
          · exact .inl h₂
          exact .inr ⟨h₁, h₂⟩)).1 hA
      have hff : AbstractionRel SΘ F (f₁ d ps) (f₁ d ps) := hEp.trans hA (hEp.symm hA)
      have hfo : AbstractionRel SΘ F (f₁ d ps) (o₁ d ps) :=
        (AbstractionRel.congr_computes hSp hFv (by
          rcases hc hf₁ with h₁ | h₁
          · exact .inl h₁
          exact .inr ⟨fun _ _ => .rfl, h₁⟩)).1 hff
      exact ⟨hA', (hresp _ _ hfo o₁ o₂).1 (DesRel.obsEquiv hd hRF' (hG _ hff) hGf hf₁ hf₂)⟩
    | @recursive _ _ _ _ _ _ _ _ _ _ _ _ _ SΘ R hrs hΘ G hG =>
      obtain ⟨hA, hGf⟩ := hS
      obtain ⟨v, hv⟩ := hRF 0 R hrs
      refine ⟨fun ts us hts => (hv.congr_computes ?_).1 (hA ts us hts),
        DesRel.obsEquiv hd hRF' (hG (o₁ d ps)) hGf hf₁ hf₂⟩
      rcases hc hf₁ with h₁ | h₁
      · exact .inl h₁
      rcases hc hf₂ with h₂ | h₂
      · exact .inl h₂
      exact .inr ⟨h₁ _, h₂ _⟩

-- ADE: none.
/-- `(η_d)`, closed: two closed terms of an instance of a codata type of `Σ`, whose type
declaration is meaningful, at arguments of its parameters, whose observations by each destructor,
at equal arguments of its telescope, are equal terms of its result, whatever the instance that the
second observation carries, are equal terms of the instance: canonical terms that `(eq_ν)` relates,
since the relation that `(eq_d)` gives the corecursors they compute to at `(eq_ν)` is consistent with
the clauses of the destructors, or proofs of a proposition that their observations make true. -/
theorem ValidEqTerm₀.etaObs (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as a₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as.toSubst as.toSubst) {t u : Term 0 []}
    (ht : ValidTerm₀ sig ι t (.inst D qs ls ps as)) (hu : ValidTerm₀ sig ι u (.inst D qs ls ps as))
    (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (.obs D qs ls ps as t d ts.terms) (.obs D qs ls ps a₂ u d us.terms)
        ((B.substLevels (ls.getFin hl)).subst (Subst.append
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst))) :
    ValidEqTerm₀ sig ι t u (.inst D qs ls ps as) := by
  have hI : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  obtain ⟨v, -, R, hcv, -, hR, -⟩ := ht.1.2
  cases Computesι.det hd hcv hI
  have hnd := TypeDeclaration.codataTypes_nodup (hd.nodup h.1)
  let L := ls.getFin hl
  let ρ : Fin decl.levels → Nat := fun i => (L i).closedValue
  let Lρ : Fin decl.levels → Level 0 := fun i => .ofNat (ρ i)
  let I : Instance decl.sorts decl.grades := .ofLists qs ps hq hp
  have hls : ∀ i, Lρ i ≈ L i := fun i => Level.ofNat_closedValue _
  have hθ := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hmean := (hv.destructors I hadm h.2.1 ρ).2 _ _ hθ
  have ih : ∀ m, m < ((decl.sort I).level.subst L).closedValue → (levelRel sig ι m).IsPer :=
    fun m _ => levelRel_isPer hd m
  -- The instances of the block, at the levels without variables and at the arguments.
  let X : Name → Term 0 [] := fun D' =>
    ((decl.blockInstance I D' (.identity decl.scope)).atLevels ρ).subst as.toSubst
  have hX : ∀ D', Term.LevelEquiv (X D') (.inst D' qs ls ps as) := fun D' =>
    decl.blockInstance_atLevels_subst hq hl hp as D'
  have hcX : ∀ D', Computesι sig ι (X D') (X D') := fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  -- The observations at the levels without variables.
  have hobs' : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body I).Pos d p q Ξ Θ B ψ)
      (ts us : Args 0 [] ps'),
      EqSubst sig ι (Context.empty.append ((Θ.substLevels Lρ).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst))) ts.toSubst us.toSubst →
      ValidEqTerm₀ sig ι (((t.observation D qs ls ps as) d ps').subst ts.toSubst)
        (((u.observation D qs ls ps a₂) d ps').subst us.toSubst)
        ((B.substLevels Lρ).subst (Subst.append
          (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) ts.toSubst)) :=
      fun d p q ps' Ξ Θ B ψ hpos ts us hτ => by
    rw [Term.observation_subst_args, Term.observation_subst_args]
    have hτ' := EqSubst.levelEquiv (Context.LevelEquiv.append .empty
      (Telescope.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Telescope.substLevels_levelEquiv hls Θ))) hτ
    exact (hobs d p q ps' Ξ Θ B ψ hpos ts us hτ').levelEquiv (Term.LevelEquiv.refl _)
      (Term.LevelEquiv.refl _) (Term.LevelEquiv.subst (Subst.LevelEquiv.refl _)
        (Term.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) B))
  have hlev : ∀ {s : Quality} {rs : Nat → Option TermRel} {S : ObsRel},
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels L) as.toSubst S →
      DesRel sig ι ((decl.sort I).level.subst L).closedValue (fun m _ => levelRel sig ι m) s rs
        ((T.body I).substLevels Lρ) as.toSubst S := fun hS =>
    DesRel.levelEquiv (fun m _ => levelRel_levelInvariant m) hS
      (Destructors.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _)
      (Subst.LevelEquiv.refl _)
  rcases HasEq.instCodata_inv hd h hq hl hp hR with ⟨hs, S, hS, rfl⟩ | ⟨hs, S, hS, hRb⟩
  · -- An instance in a universe: the terms compute to corecursors, whose observations are theirs.
    have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) →
        ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂, S X T' o₁ o₂ → S Y T' o₁ o₂ :=
      fun X Y hXY T' hT' => DesRel.mono hd ih (hS X T' hT') _ _ _ (hS Y T' hT')
        fun _ => Option.rel_map (fun D _ _ => TermRel.computed_mono (hXY D)) _
    have hU : ∀ T' ∈ decl.codataTypes, UnivRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (CodataType.blockRel decl.codataTypes S T'.name) := fun T' hT' =>
      .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
    have hU₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).univ
        (.inst D qs ls ps as) (CodataType.blockRel decl.codataTypes S D) :=
      levelRel_univ_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
    have hnp : ¬ ComputesToProp sig ι (.inst D qs ls ps as) := fun ⟨v, hv, k, b, hk⟩ => by
      cases Computesι.det hd hI hv
      exact HasEq.univ_not_prop hd hU₀ hk
    have hDS := hlev (hS (CodataType.blockRel decl.codataTypes S) T h.2.1)
    have hS₁ := DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
      (fun i D' hi => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
          (Destructors.recursionAt_mem hi)
        rw [hi]
        exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
          (.univ rfl (hU T' hT')) (hX _).symm⟩)
      hDS hobs'
    obtain ⟨v₁, w₁, w₁', R₁, hv₁, hw₁, -, hR₁, hrel₁⟩ := ht.2.1 hnp
    cases Computesι.det hd hI hv₁
    have hrel₁' := (HasEq.unique hd hR₁ hR w₁ w₁').1 hrel₁
    rw [← h.2.2] at hrel₁'
    obtain ⟨o₁, -, hc₁, -, -⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel₁'
    obtain ⟨v₂, w₂, w₂', R₂, hv₂, hw₂, -, hR₂, hrel₂⟩ := hu.2.1 hnp
    cases Computesι.det hd hI hv₂
    have hrel₂' := (HasEq.unique hd hR₂ hR w₂ w₂').1 hrel₂
    rw [← h.2.2] at hrel₂'
    obtain ⟨o₂, -, hc₂, -, -⟩ := CodataType.blockRel_unfold hmono h.2.1 hrel₂'
    have hS₂ := DesRel.obsEquiv hd (fun i R' hi => by
        cases hr : (T.body I).recursionAt decl.names i with
        | none => rw [hr] at hi; cases hi
        | some D' =>
          rw [hr] at hi
          cases hi
          obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
            (Destructors.recursionAt_mem hr)
          exact ⟨_, .univ rfl (hU T' hT')⟩)
      hDS hS₁ (ObsEquiv.of_computes hd hw₁ hc₁) (ObsEquiv.of_computes hd hw₂ hc₂)
    have hrel := CodataType.blockRel_fold hmono hnd h.2.1 ⟨o₁, o₂, hc₁, hc₂, hS₂⟩
    rw [h.2.2] at hrel
    exact ⟨ht.1, fun _ => ⟨_, w₁, w₂, _, hI, hw₁, hw₂, hR, hrel⟩, fun hp => absurd hp hnp⟩
  · -- A proposition: the observations of the first term make it true.
    have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T' ∈ decl.codataTypes, ∀ o₁ o₂,
        S B T' o₁ o₂ → S B' T' o₁ o₂ :=
      fun B B' hB T' hT' => DesRel.mono hd ih (hS B T' hT') _ _ _ (hS B' T' hT')
        fun _ => Option.rel_map (fun D _ _ => hB D) _
    have hP : ∀ T' ∈ decl.codataTypes, PropRel sig ι ((decl.sort I).level.subst L).closedValue
        (fun m _ => levelRel sig ι m) (.inst T'.name qs ls ps as)
        (CodataType.blockTruth decl.codataTypes S T'.name) := fun T' hT' =>
      .codata ⟨h.1, hT', rfl⟩ hq hl hp rfl hs rfl S hS
    have hP₀ : (levelRel sig ι ((decl.sort I).level.subst L).closedValue).prop
        (.inst D qs ls ps as) (CodataType.blockTruth decl.codataTypes S D) :=
      levelRel_prop_iff.2 (.codata h hq hl hp rfl hs rfl S hS)
    have hDS := hlev (hS (CodataType.blockTruth decl.codataTypes S) T h.2.1)
    have hS₁ := DesRel.of_obs hd Lρ (T.body I) hmean (fun i hi => by rw [hi]; rfl)
      (fun i D' hi => by
        obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_codataTypes h.2.1
          (Destructors.recursionAt_mem hi)
        rw [hi]
        exact ⟨_, _, rfl, hcX _, FieldRel.levelEquiv (fun m _ => levelRel_levelInvariant m)
          (.prop (hP T' hT')) (hX _).symm⟩)
      hDS hobs'
    have hSp := DesRel.isPer hd ih (fun i x hx => by
      cases hr : (T.body I).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩) hDS
    have htrue := CodataType.blockTruth_fold hmono hnd h.2.1 ⟨_, hSp.trans hS₁ (hSp.symm hS₁)⟩
    rw [h.2.2] at htrue
    exact ⟨ht.1, fun hn => absurd ⟨_, hI, _, _, hP₀⟩ hn,
      fun _ => ⟨_, R, hI, hR, (hRb _ _).2 htrue⟩⟩

-- ADE: `η-eqᵛ`, `Σ-ηᵛ` and `η-unitᵛ`, in `Definition/LogicalRelation/Substitution/Introductions/`.
/-- `(η_d)` keeps the meaning: at equal substitutions of the context, the observations of the terms,
at the arguments of the instance substituted, are the closed observations of
`ValidEqTerm₀.etaObs`, since the observations of a term substituted are those of the substituted
term; the second term at the first substitution is equal to itself at the second one. -/
theorem ValidEqTermΓ.etaObs {sigT : Signature} {Γ : Scope} {ctx : Context 0 Γ}
    (hent : sig.ValidEntries ι sigT) {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sigT.HasCodataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as : InstanceArgs 0 Γ decl.scope}
    (has : ValidInstanceArgsΓ sig ι ctx as
      ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) {t u : Term 0 Γ}
    (ht : ValidTermΓ sig ι ctx t (.inst D qs ls ps as))
    (hu : ValidTermΓ sig ι ctx u (.inst D qs ls ps as))
    (hobs : ∀ (d : Name) (p q : Grade) (ps' : List Parameter) (Ξ : Scope)
      (Θ : Telescope decl.levels Ξ ps') (B : Term decl.levels (Ξ.extend ps'.length))
      (ψ : ResultOwnership ps'.length) (hpos : (T.body (.ofLists qs ps hq hp)).Pos d p q Ξ Θ B ψ),
      ValidEqTermΓ sig ι (ctx.append ((Θ.substLevels (ls.getFin hl)).subst
        (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))
        (t.observation D qs ls ps as d ps') (u.observation D qs ls ps as d ps')
        ((B.substLevels (ls.getFin hl)).subst
          (Subst.liftN _ (hpos.obsSubst (t.observation D qs ls ps as) as.toSubst)))) :
    ValidEqTermΓ sig ι ctx t u (.inst D qs ls ps as) := by
  obtain ⟨h', hv⟩ := hent.hasCodataType h
  have hctx := ht.1.1
  have hd := hctx.distinct
  refine ⟨ht.1, fun σ₁ σ₂ hσ => ?_⟩
  have hu' := hu.2 σ₁ σ₂ hσ
  refine ValidEqTerm₀.etaObs (a₂ := as.subst σ₂) hd h' hv hq hl hp hadm
    (has.2 σ₁ σ₁ (hσ.left hctx)) (ht.2 σ₁ σ₁ (hσ.left hctx))
    hu'.right
    fun d p q ps' Ξ Θ B ψ hpos ts us hτ => ?_
  -- The scope of the destructor, substituted, is that of the observations of the term substituted.
  have hc : ∀ {a} (x : Var Ξ a),
      ((hpos.obsSubst (t.observation D qs ls ps as) as.toSubst) x).subst
        (Subst.liftN a.params.length σ₁) =
      hpos.obsSubst ((t.subst σ₁).observation D qs ls ps (as.subst σ₁)) (as.subst σ₁).toSubst x :=
    hpos.obsSubst_subst σ₁ (fun d ps' => Term.observation_subst σ₁ D qs ls ps as t d ps')
      (InstanceArgs.toSubst_subst σ₁ as)
  have hb := (hobs d p q ps' Ξ Θ B ψ hpos).2 _ _
    ((EqSubst.append_append_iff ctx _ σ₁ σ₂ ts.toSubst us.toSubst).2
      ⟨hσ, by rw [Telescope.subst_subst_of hc]; exact hτ⟩)
  rw [← Term.subst_append, ← Term.subst_append, ← Term.subst_append, Term.observation_subst,
    Term.observation_subst, Term.observation_subst_args, Term.observation_subst_args,
    Term.subst_subst_of (Subst.liftN_subst_of _ hc), Term.subst_append] at hb
  exact hb

end

end Sic.Core
