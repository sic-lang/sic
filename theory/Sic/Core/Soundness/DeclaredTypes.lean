module

public import Sic.Core.Soundness.Levels
import Sic.Core.Meaning.Equality.Properties
import Sic.Core.Meaning.Exactness
import Sic.Core.Meaning.Judgments
import Sic.Core.Meaning.Uniqueness
import Sic.Core.Soundness.Closed
import Sic.Core.Soundness.Substitution
import Sic.Core.Syntax.Signature

/-!
# Soundness of the Declared Types

The rules of the declared types of annex 14 of RFC 36 keep the meaning of annex 18: an instance of a
declared type is a type of the sort of its declaration, whose fields are those of its declaration at
its levels and its arguments, and equal arguments give instances with the same equality of their
canonical terms, or the same truth.
The proofs take the premises at two equal closed substitutions of the context, as those of `Rules`.

ADE have no declared types: their types are those of the theory.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

section

variable {sig : Signature} {ι : Interpretation}

/-! ## Declared Types

An instance of a declared type is a type of the sort of its declaration, whose fields are those of
its declaration at its levels and its arguments: the meaning of the declaration makes them closed
telescopes equal in this sort for equal arguments, which the graph of the sort gives the same
equality of their terms, so that equal arguments give instances with the same equality of their
canonical terms, or the same truth.

The equality of the terms of the rest of a telescope is the one that the graph gives it at each
term of its first type: it is defined from the graph, as the relation that some equality of the
terms of the rest relates, rather than chosen among them, since the graph gives one at most.
The instance at levels of the same values then follows as for the constants. -/

/-- The type of the first field of two closed telescopes equal in the sort `κ`, as `(⊨tel_κ,)` gives
it, computes to a type of a sort that `κ` bounds, whose terms are equal by `F`, and so does the
other type, with the same `F`: the terms that `F` relates are equal terms of the type. -/
theorem ValidEqTerm₀.fieldRel {A₁ A₂ : Term 0 []} {κ₁ κ : Universe 0} (hκ : κ₁ ≼ κ)
    (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) :
    ∃ w₁ w₂ F, Computesι sig ι A₁ w₁ ∧ Computesι sig ι A₂ w₂ ∧
      FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w₁ F ∧
      FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w₂ F ∧
      ∀ a₁ a₂, F a₁ a₂ → ValidEqTerm₀ sig ι a₁ a₂ A₁ := by
  obtain ⟨s₁, l₁⟩ := κ₁
  have hd := h.1.1
  have hm : l₁.closedValue ≤ κ.level.closedValue := hκ.2 Fin.elim0
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ n hn =>
    cases levelRel_univ_iff.1 hn with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      subst hl
      obtain ⟨⟨R', h₁, h₂⟩, -⟩ := hvw
      have hs : κ.quality = .type := by
        have := hκ.1
        cases hq : κ.quality with
        | type => rfl
        | prop => exact nomatch this hq
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).univ w R' →
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w
            (R'.computed sig ι) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .univBelow hs _ hlt hw
        · exact .univ hs (heq ▸ levelRel_univ_iff.1 hw)
      refine ⟨w₁, w₂, R'.computed sig ι, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ ⟨v, w, ha₁, ha₂, hR'⟩ => ⟨(ValidEqTerm₀.univType h).left, fun _ =>
          ⟨w₁, v, w, R', hw₁, ha₁, ha₂, .univ _ h₁, hR'⟩, fun ⟨v', hv', hP⟩ => ?_⟩⟩
      cases Computesι.det hd hw₁ hv'
      obtain ⟨_, _, hP⟩ := hP
      exact (HasEq.univ_not_prop hd h₁ hP).elim
    | prop hl _ =>
      subst hl
      obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := hvw
      cases propext hb
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).prop w b₁ →
          FieldRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality w
            (fun _ _ => b₁) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .propBelow _ hlt hw
        · exact .prop (heq ▸ levelRel_prop_iff.1 hw)
      refine ⟨w₁, w₂, fun _ _ => b₁, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂,
        fun a₁ a₂ hb₁ => ⟨(ValidEqTerm₀.propType h).left, fun hn => absurd ⟨w₁, hw₁, _, _, h₁⟩ hn,
          fun _ => ⟨w₁, fun _ _ => b₁, hw₁, .prop _ b₁ h₁ fun _ _ => .rfl, hb₁⟩⟩⟩

/-- The types of two closed terms equal in a sort `κ₁` that `κ` bounds compute to types with a common
relation of run time `R` of the graph of `U_n`, at the level `n` of `κ`, for each program `P`: the
relation that the equality of `U_n` gives them, or the one of the propositions. -/
theorem ValidEqTerm₀.runFieldRel (P : Program) {A₁ A₂ : Term 0 []} {κ₁ κ : Universe 0}
    (hκ : κ₁ ≼ κ) (h : ValidEqTerm₀ sig ι A₁ A₂ (.sort κ₁)) :
    ∃ w₁ w₂ R, Computesι sig ι A₁ w₁ ∧ Computesι sig ι A₂ w₂ ∧
      RunFieldRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) w₁ R ∧
      RunFieldRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) w₂ R := by
  obtain ⟨s₁, l₁⟩ := κ₁
  have hm : l₁.closedValue ≤ κ.level.closedValue := hκ.2 Fin.elim0
  obtain ⟨A₀, w₁, w₂, R, hc, hw₁, hw₂, hR, hvw⟩ := h.2.1 not_computesToProp_sort
  cases hc.sort_inv
  cases hR with
  | prop _ _ hp => exact absurd ⟨_, _, hp⟩ not_isProp_sort
  | univ n hn =>
    cases levelRel_univ_iff.1 hn with
    | data _ _ _ _ hv => cases hv
    | codata _ _ _ _ hv => cases hv
    | univ hl _ =>
      subst hl
      obtain ⟨-, hr⟩ := hvw
      obtain ⟨Q, h₁, h₂⟩ := hr P
      have hF : ∀ w, (levelRel sig ι l₁.closedValue).run P w Q →
          RunFieldRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) w
            (Q.computed sig ι) := fun w hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .univBelow _ hlt hw
        · exact .univ (heq ▸ levelRel_run_iff.1 hw)
      exact ⟨w₁, w₂, _, hw₁, hw₂, hF w₁ h₁, hF w₂ h₂⟩
    | prop hl _ =>
      subst hl
      obtain ⟨b₁, b₂, h₁, h₂, -⟩ := hvw
      have hF : ∀ w b, (levelRel sig ι l₁.closedValue).prop w b →
          RunFieldRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) w
            fun _ _ _ => True := fun w b hw => by
        rcases Nat.lt_or_eq_of_le hm with hlt | heq
        · exact .propBelow _ hlt hw
        · exact .prop (heq ▸ levelRel_prop_iff.1 hw)
      exact ⟨w₁, w₂, _, hw₁, hw₂, hF w₁ b₁ h₁, hF w₂ b₂ h₂⟩

/-- Two closed telescopes equal in the sort `κ` are equal fields without recursive fields. -/
theorem ValidEqTelescope₀.toFields {κ : Universe 0} (inst₁ inst₂ : Name → Term 0 []) :
    {ps : List Parameter} → {Θ₁ Θ₂ : Telescope 0 [] ps} → ValidEqTelescope₀ sig ι κ Θ₁ Θ₂ →
      ValidEqFields₀ sig ι κ inst₁ inst₂ (fun _ => none) Θ₁ Θ₂
  | [], .nil, .nil, h => h
  | _ :: _, .cons _ _ _ _, .cons _ _ _ _, h => by
    rw [ValidEqTelescope₀] at h
    rw [ValidEqFields₀]
    exact ⟨h.1, fun v₁ v₂ hv => ValidEqTelescope₀.toFields inst₁ inst₂ (h.2 v₁ v₂ hv)⟩

/-- Two closed fields equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, whatever the relations `Rf D` of their recursive fields of
the type `D`, in a signature whose names are distinct: the equality of the rest after a recursive
field, on which it does not depend, is the one at any term. -/
theorem ValidEqFields₀.telRel (hd : sig.Distinct) {κ : Universe 0} {inst₁ inst₂ : Name → Term 0 []}
    (Rf : Name → TermRel) :
    {ps : List Parameter} → {rs : Nat → Option Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ inst₁ inst₂ rs Θ₁ Θ₂ →
      ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) Θ₁ S ∧
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs i).map Rf) Θ₂ S
  | [], _, .nil, .nil, _ => ⟨FieldsRel.nil, .nil, .nil⟩
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂, h => by
    have ih : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    rw [ValidEqFields₀] at h
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
      obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ
      have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ ha => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂ (hFv a₁ a₂ ha))
      let G : Term 0 [] → FieldsRel := fun a ts us => ∃ S,
        TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S ∧ S ts us
      have hG : ∀ a S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S → G a = S :=
        fun a S hS => funext fun ts => funext fun us => propext
          ⟨fun ⟨_, hS', hs⟩ => (TelRel.unique hd ih hS' _ _ hS ts us).1 hs, fun hs => ⟨S, hS, hs⟩⟩
      have hresp : ∀ a₁ a₂, F a₁ a₂ → ∀ ts us, G a₁ ts us ↔ G a₂ ts us := fun a₁ a₂ ha ts us => by
        have hFp := FieldRel.isPer hd ih hF₁
        obtain ⟨S, h₁, h₂⟩ := hcommon a₁ a₂ ha
        obtain ⟨S', h₁', h₂'⟩ := hcommon a₂ a₂ (hFp.trans (hFp.symm ha) ha)
        rw [hG a₁ S h₁, hG a₂ S' h₁']
        exact TelRel.unique hd ih h₂ _ _ h₂' ts us
      have hr' : (rs 0).map Rf = none := by rw [hr]; rfl
      refine ⟨FieldsRel.cons F G, .cons hc₁ hF₁ G (fun a ha => ?_) hresp hr',
        .cons hc₂ hF₂ G (fun a ha => ?_) hresp hr'⟩
      · obtain ⟨S, h₁, -⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₂
    · rename_i D hr
      obtain ⟨-, -, hΘ⟩ := h
      let a₀ : Term 0 [] := .sort ⟨.type, .zero⟩
      have hcommon : ∀ a₁ a₂, ∃ S,
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ => ValidEqFields₀.telRel hd Rf (hΘ a₁ a₂)
      obtain ⟨G, h₀₁, h₀₂⟩ := hcommon a₀ a₀
      have hr' : (rs 0).map Rf = some (Rf D) := by rw [hr]; rfl
      refine ⟨FieldsRel.cons (Rf D) fun _ => G, .recursive hr' G fun a => ?_,
        .recursive hr' G fun a => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a₀
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₂ _ _ h₀₂ ts us)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a₀ a
        have hSG : S = G := funext fun ts => funext fun us => propext
          (TelRel.unique hd ih h₁ _ _ h₀₁ ts us)
        exact hSG ▸ h₂

/-- Two closed telescopes equal in the sort `κ` are telescopes of the graph of this sort with the same
equality of the terms of their fields, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.telRel (hd : sig.Distinct) {κ : Universe 0} {ps : List Parameter}
    {Θ₁ Θ₂ : Telescope 0 [] ps} (h : ValidEqTelescope₀ sig ι κ Θ₁ Θ₂) :
    ∃ S, TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => none)
        Θ₁ S ∧
      TelRel sig ι κ.level.closedValue (fun m _ => levelRel sig ι m) κ.quality (fun _ => none)
        Θ₂ S :=
  ValidEqFields₀.telRel hd (fun _ _ _ => False) (h.toFields (fun _ => .sort ⟨.type, .zero⟩)
    (fun _ => .sort ⟨.type, .zero⟩))

/-- Two closed fields equal in a sort `κ` of types are telescopes of the graph of run time of `U_n`,
at the level `n` of `κ`, with the same relation of run time of the terms of their fields, for each
program `P`, whatever the relations `Rf D` of their recursive fields of the type `D`, in a signature
whose names are distinct: the relation of the rest is defined from the graph at the first
telescope, rather than chosen, since the graph gives one at most, and after a recursive field, on
which the rest does not depend, it is the one at any term. -/
theorem ValidEqFields₀.runTelRel (hd : sig.Distinct) (P : Program) {κ : Universe 0}
    (hs : κ.quality = .type) {inst₁ inst₂ : Name → Term 0 []} (Rf : Name → RunRel) :
    {ps : List Parameter} → {rs : Nat → Option Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ inst₁ inst₂ rs Θ₁ Θ₂ →
      ∃ S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs i).map Rf) Θ₁ S ∧
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs i).map Rf) Θ₂ S
  | [], _, .nil, .nil, _ => ⟨RunFieldsRel.nil, .nil, .nil⟩
  | _ :: _, rs, .cons _ _ A₁ Θ₁, .cons _ _ A₂ Θ₂, h => by
    have ihm : ∀ m, m < κ.level.closedValue → (levelRel sig ι m).IsPer :=
      fun m _ => levelRel_isPer hd m
    have ih : ∀ m, m < κ.level.closedValue → RunLevelRel.Unique ((levelRel sig ι m).run P) :=
      fun m _ => levelRel_run_unique hd m
    have hrr : ∀ i, Option.Rel (fun x y : RunRel => ∀ H t a, x H t a ↔ y H t a)
        ((rs (i + 1)).map Rf) ((rs (i + 1)).map Rf) :=
      fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _
    rw [ValidEqFields₀] at h
    split at h
    · rename_i hr
      obtain ⟨⟨κ₁, hκ, hA⟩, hΘ⟩ := h
      obtain ⟨w₁, w₂, F, hc₁, hc₂, hF₁, hF₂, hFv⟩ := hA.fieldRel hκ
      obtain ⟨w₁', w₂', R, hc₁', hc₂', hR₁, hR₂⟩ := hA.runFieldRel P hκ
      cases Computesι.det hd hc₁ hc₁'
      cases Computesι.det hd hc₂ hc₂'
      rw [hs] at hF₁ hF₂
      have hcommon : ∀ a₁ a₂, F a₁ a₂ → ∃ S,
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ ha => ValidEqFields₀.runTelRel hd P hs Rf (hΘ a₁ a₂ (hFv a₁ a₂ ha))
      let G : Term 0 [] → RunFieldsRel := fun a H ts bs => ∃ S,
        RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S ∧ S H ts bs
      have hG : ∀ a S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
          (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a)) S → G a = S :=
        fun a S hS => funext fun H => funext fun ts => funext fun bs => propext
          ⟨fun ⟨_, hS', hs⟩ => (RunTelRel.congr hd ihm ih hS' _ _ hS hrr H ts bs).1 hs,
            fun hs => ⟨S, hS, hs⟩⟩
      have hr' : (rs 0).map Rf = none := by rw [hr]; rfl
      refine ⟨_, .cons hc₁ hF₁ hR₁ G (fun a ha => ?_) hr', .cons hc₂ hF₂ hR₂ G (fun a ha => ?_) hr'⟩
      · obtain ⟨S, h₁, -⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a ha
        rw [hG a S h₁]
        exact h₂
    · rename_i D hr
      obtain ⟨-, -, hΘ⟩ := h
      let a₀ : Term 0 [] := .sort ⟨.type, .zero⟩
      have hcommon : ∀ a₁ a₂, ∃ S,
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map Rf) (Θ₁.subst₀ (Subst₀.single a₁)) S ∧
          RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m)
            (fun i => (rs (i + 1)).map Rf) (Θ₂.subst₀ (Subst₀.single a₂)) S :=
        fun a₁ a₂ => ValidEqFields₀.runTelRel hd P hs Rf (hΘ a₁ a₂)
      obtain ⟨G, h₀₁, h₀₂⟩ := hcommon a₀ a₀
      have hr' : (rs 0).map Rf = some (Rf D) := by rw [hr]; rfl
      refine ⟨_, .recursive hr' G fun a => ?_, .recursive hr' G fun a => ?_⟩
      · obtain ⟨S, h₁, h₂⟩ := hcommon a a₀
        have hSG : S = G := funext fun H => funext fun ts => funext fun bs => propext
          (RunTelRel.congr hd ihm ih h₂ _ _ h₀₂ hrr H ts bs)
        exact hSG ▸ h₁
      · obtain ⟨S, h₁, h₂⟩ := hcommon a₀ a
        have hSG : S = G := funext fun H => funext fun ts => funext fun bs => propext
          (RunTelRel.congr hd ihm ih h₁ _ _ h₀₁ hrr H ts bs)
        exact hSG ▸ h₂

/-- Two closed telescopes equal in a sort `κ` of types are telescopes of the graph of run time of
`U_n`, at the level `n` of `κ`, with the same relation of run time of the terms of their fields, for
each program `P`, in a signature whose names are distinct. -/
theorem ValidEqTelescope₀.runTelRel (hd : sig.Distinct) (P : Program) {κ : Universe 0}
    (hs : κ.quality = .type) {ps : List Parameter} {Θ₁ Θ₂ : Telescope 0 [] ps}
    (h : ValidEqTelescope₀ sig ι κ Θ₁ Θ₂) :
    ∃ S, RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => none) Θ₁ S ∧
      RunTelRel sig ι P κ.level.closedValue (fun m _ => levelRel sig ι m) (fun _ => none) Θ₂ S :=
  ValidEqFields₀.runTelRel hd P hs (fun _ _ _ _ => False)
    (h.toFields (fun _ => .sort ⟨.type, .zero⟩) (fun _ => .sort ⟨.type, .zero⟩))

-- ADE: none.
/-- The recursive fields of a closed telescope, at the positions where `rs` gives a type `D` of the
block, are the instances `inst D`, the rest being so at every term of each field. -/
def Telescope.RecHeads (sig : Signature) (ι : Interpretation) (inst : Name → Term 0 []) :
    {ps : List Parameter} → (Nat → Option Name) → Telescope 0 [] ps → Prop
  | [], _, .nil => True
  | _ :: _, rs, .cons _ _ A Θ => (∀ D, rs 0 = some D → A = inst D) ∧
    ∀ a, ValidEqTerm₀ sig ι a a A →
      Telescope.RecHeads sig ι inst (fun i => rs (i + 1)) (Θ.subst₀ (Subst₀.single a))

/-- A telescope without recursive fields has their instances everywhere. -/
theorem Telescope.recHeads_none (inst : Name → Term 0 []) :
    {ps : List Parameter} → (Θ : Telescope 0 [] ps) → Θ.RecHeads sig ι inst (fun _ => none)
  | [], .nil => trivial
  | _ :: _, .cons _ _ _ _ => by
    rw [Telescope.RecHeads]
    exact ⟨fun _ h => (by cases h), fun _ _ => Telescope.recHeads_none inst _⟩

/-- The first of two equal closed fields has the instances `inst₁` at its recursive fields. -/
theorem ValidEqFields₀.recHeads {κ : Universe 0} {inst₁ inst₂ : Name → Term 0 []} :
    {ps : List Parameter} → {rs : Nat → Option Name} → {Θ₁ Θ₂ : Telescope 0 [] ps} →
      ValidEqFields₀ sig ι κ inst₁ inst₂ rs Θ₁ Θ₂ → Θ₁.RecHeads sig ι inst₁ rs
  | [], _, .nil, .nil, _ => trivial
  | _ :: _, rs, .cons _ _ _ _, .cons _ _ _ _, h => by
    rw [ValidEqFields₀] at h
    rw [Telescope.RecHeads]
    split at h
    · rename_i hr
      refine ⟨fun D hD => ?_, fun a ha => ValidEqFields₀.recHeads (h.2 a a ha)⟩
      rw [hr] at hD
      cases hD
    · rename_i D hr
      refine ⟨fun D' hD' => ?_, fun a _ => ValidEqFields₀.recHeads (h.2.2 a a)⟩
      rw [hr] at hD'
      cases hD'
      exact h.1

/-- Equal closed terms of a type that computes to a type of a field, whose terms are equal by `F`,
are related by `F`: the converse of the last property of `ValidEqTerm₀.fieldRel`. -/
theorem FieldRel.of_validEqTerm {n : Nat} {s : Quality} {A v t u : Term 0 []} {F : TermRel}
    (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F) (hA : Computesι sig ι A v)
    (h : ValidEqTerm₀ sig ι t u A) : F t u := by
  have hd := h.1.1
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u := fun m R hR => by
    have hnp : ¬ ComputesToProp sig ι A := fun ⟨v', hv', _, _, hP⟩ => by
      cases Computesι.det hd hA hv'
      exact HasEq.univ_not_prop hd hR hP
    obtain ⟨v', w₁, w₂, R', hv', ht, hu, hR', hw⟩ := h.2.1 hnp
    cases Computesι.det hd hA hv'
    exact ⟨w₁, w₂, ht, hu, (HasEq.unique hd hR' (.univ m hR) w₁ w₂).1 hw⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b := fun m b hb => by
    obtain ⟨v', R', hv', hR', hR⟩ := h.2.2 ⟨v, hA, m, b, hb⟩
    cases Computesι.det hd hA hv'
    exact (HasEq.unique hd hR' (.prop m b hb fun _ _ => .rfl) t u).1 hR
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU)
  | univBelow _ m _ hU => exact huniv m _ hU
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP)
  | propBelow m _ hP => exact hprop m _ hP

/-- Equal closed arguments of a closed telescope of the graph of a sort, whose fields have the
equality `S`, have terms related by `S`: the converse of `ValidEqTelescope₀.telRel`, for the
arguments. -/
theorem TelRel.of_eqSubst {n : Nat} {s : Quality} {inst : Name → Term 0 []} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} → {rs : Nat → Option Name} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → Θ.RecHeads sig ι inst rs →
      (∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
        ∀ t u, ValidEqTerm₀ sig ι t u (inst D) → R t u) →
      (ts us : Args 0 [] ps) →
      EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst → S ts.terms us.terms
  | [], .nil, _, _, _, .nil, _, _, .nil, .nil, _ => trivial
  | _ :: ps, .cons q p A Θ, _, _, _, h', hH, hR, .cons t ts, .cons u us, h => by
    obtain ⟨ht, hts⟩ := EqSubst.args_cons_iff.1 h
    have hd : sig.Distinct := ht.1.1
    have htt := ht.trans ht.symm
    cases h' with
    | cons hA hF G hG _ _ =>
      have hFtu := hF.of_validEqTerm hA ht
      have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
      exact ⟨hFtu, TelRel.of_eqSubst (hG t (hFp.trans hFtu (hFp.symm hFtu))) (hH.2 t htt)
        (fun i R h => hR (i + 1) R h) ts us hts⟩
    | recursive hrs G hG =>
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      exact ⟨hRD t u (hH.1 D hD ▸ ht), TelRel.of_eqSubst (hG t) (hH.2 t htt)
        (fun i R h => hR (i + 1) R h) ts us hts⟩

/-- Two equal closed terms of the type of a field, whose terms are equal by `F`, are related by `F`:
the converse of `FieldRel.of_validEqTerm`. -/
theorem FieldRel.validEqTerm (hd : sig.Distinct) {n : Nat} {s : Quality} {A v t u : Term 0 []}
    {F : TermRel} (hF : FieldRel sig ι n (fun m _ => levelRel sig ι m) s v F)
    (hA : Computesι sig ι A v) (htu : F t u) : ValidEqTerm₀ sig ι t u A := by
  have huniv : ∀ m R, (levelRel sig ι m).univ v R → R.computed sig ι t u →
      ValidEqTerm₀ sig ι t u A := fun m R hR ⟨w₁, w₂, h₁, h₂, hw⟩ =>
    ⟨⟨hd, v, v, R, hA, hA, .univ m hR, .univ m hR, fun _ _ => .rfl⟩, fun _ => ⟨v, w₁, w₂, R, hA, h₁, h₂, .univ m hR, hw⟩,
      fun ⟨v', hv', _, _, hP⟩ => by
        cases Computesι.det hd hA hv'
        exact (HasEq.univ_not_prop hd hR hP).elim⟩
  have hprop : ∀ m b, (levelRel sig ι m).prop v b → b → ValidEqTerm₀ sig ι t u A :=
    fun m b hP hb =>
      ⟨⟨hd, v, v, fun _ _ => b, hA, hA, .prop m b hP fun _ _ => .rfl,
        .prop m b hP fun _ _ => .rfl, fun _ _ => .rfl⟩, fun hn => absurd ⟨v, hA, m, b, hP⟩ hn,
        fun _ => ⟨v, fun _ _ => b, hA, .prop m b hP fun _ _ => .rfl, hb⟩⟩
  cases hF with
  | univ _ hU => exact huniv n _ (levelRel_univ_iff.2 hU) htu
  | univBelow _ m _ hU => exact huniv m _ hU htu
  | prop hP => exact hprop n _ (levelRel_prop_iff.2 hP) htu
  | propBelow m _ hP => exact hprop m _ hP htu

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are the terms of equal arguments of the telescope: the converse of
`TelRel.of_eqSubst`. -/
theorem TelRel.to_eqSubst (hd : sig.Distinct) {n : Nat} {s : Quality} {inst : Name → Term 0 []} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} → {rs : Nat → Option Name} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → Θ.RecHeads sig ι inst rs →
      (∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
        ∀ t u, R t u → ValidEqTerm₀ sig ι t u (inst D)) →
      (ts us : Terms 0 []) → S ts us →
        ∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append Θ) ts'.toSubst us'.toSubst
  | [], .nil, _, _, _, .nil, _, _, .nil, .nil, _ =>
    ⟨.nil, .nil, rfl, rfl, (EqSubst.empty_iff _ _).2 trivial⟩
  | [], .nil, _, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, _, _, h', hH, hR, ts₀, us₀, hS => by
    have key : ∀ t u (ts us : Terms 0 []) (htu : ValidEqTerm₀ sig ι t u A),
        (∃ ts' us' : Args 0 [] ps, ts'.terms = ts ∧ us'.terms = us ∧
          EqSubst sig ι (Context.empty.append (Θ.subst₀ (Subst₀.single t))) ts'.toSubst
            us'.toSubst) →
        ∃ ts' us' : Args 0 [] (_ :: ps), ts'.terms = .cons t ts ∧ us'.terms = .cons u us ∧
          EqSubst sig ι (Context.empty.append (.cons q p A Θ)) ts'.toSubst us'.toSubst := by
      intro t u ts us htu ⟨ts', us', h₁, h₂, hτ⟩
      subst h₁ h₂
      exact ⟨.cons t ts', .cons u us', rfl, rfl, EqSubst.args_cons_iff.2 ⟨htu, hτ⟩⟩
    cases h' with
    | cons hA hF G hG _ _ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
        have hv := hF.validEqTerm hd hA htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t (hFp.trans htu (hFp.symm htu)))
          (hH.2 t (hv.trans hv.symm)) (fun i R h => hR (i + 1) R h) ts us hts)
    | recursive hrs G hG =>
      obtain ⟨D, hD, hRD⟩ := hR 0 _ hrs
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hv : ValidEqTerm₀ sig ι t u A := hH.1 D hD ▸ hRD t u htu
        exact key t u ts us hv (TelRel.to_eqSubst hd (hG t) (hH.2 t (hv.trans hv.symm))
          (fun i R h => hR (i + 1) R h) ts us hts)

/-- The terms `ts₁` and `ts₂` of fields are related by `Q D` at each recursive field of the type `D`
that the types `rs` of the block mark. -/
def Terms.RecRel (Q : Name → TermRel) : List (Option Name) → Terms 0 [] → Terms 0 [] → Prop
  | some D :: rs, .cons t₁ ts₁, .cons t₂ ts₂ => Q D t₁ t₂ ∧ Terms.RecRel Q rs ts₁ ts₂
  | none :: rs, .cons _ ts₁, .cons _ ts₂ => Terms.RecRel Q rs ts₁ ts₂
  | [], _, _ | _ :: _, .nil, _ | _ :: _, .cons _ _, .nil => True

/-- Terms of the fields of a closed telescope of the graph of a sort, related by the equality `S` of
its fields, are related at its recursive fields, which `rs` marks, by the relations `Rf` that the
graph gives them. -/
theorem TelRel.recRel (hd : sig.Distinct) {n : Nat} {s : Quality} {Rf : Name → TermRel} :
    {ps : List Parameter} → {Θ : Telescope 0 [] ps} → {S : FieldsRel} →
      {rs' : Nat → Option TermRel} →
      TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S → (rs : List (Option Name)) →
      (∀ i, rs' i = (rs[i]?.join).map Rf) → (ts us : Terms 0 []) → S ts us →
        Terms.RecRel Rf rs ts us
  | [], .nil, _, _, .nil, rs, _, .nil, .nil, _ => by
    cases rs with
    | nil => trivial
    | cons o _ => cases o <;> trivial
  | [], .nil, _, _, .nil, _, _, .nil, .cons .., h => nomatch h
  | [], .nil, _, _, .nil, _, _, .cons .., _, h => nomatch h
  | _ :: ps, .cons q p A Θ, _, rs', h', rs, hrs, ts₀, us₀, hS => by
    have htail : ∀ i, rs' (i + 1) = (rs.tail[i]?.join).map Rf := fun i => by
      rw [hrs (i + 1)]
      cases rs <;> rfl
    cases h' with
    | cons hA hF G hG _ hrs₀ =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have hFp := FieldRel.isPer hd (fun m _ => levelRel_isPer hd m) hF
        have ih := TelRel.recRel hd (hG t (hFp.trans htu (hFp.symm htu))) rs.tail htail ts us hts
        match rs, hrs with
        | [], _ => trivial
        | none :: _, _ => exact ih
        | some _ :: _, hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
    | recursive hrs₀ G hG =>
      match ts₀, us₀, hS with
      | .nil, _, h => exact h.elim
      | .cons _ _, .nil, h => exact h.elim
      | .cons t ts, .cons u us, ⟨htu, hts⟩ =>
        have ih := TelRel.recRel hd (hG t) rs.tail htail ts us hts
        match rs, hrs with
        | [], hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
        | none :: _, hrs => exact absurd ((hrs 0).symm.trans hrs₀) (by simp)
        | some D :: _, hrs =>
          have hR := (hrs 0).symm.trans hrs₀
          simp only [List.getElem?_cons_zero, Option.join_some, Option.map_some,
            Option.some.injEq] at hR
          exact ⟨hR ▸ htu, ih⟩

/-- Arguments related by the equality of the fields of a closed telescope of the graph of a sort are
equal arguments of the telescope, and conversely, when its recursive fields are instances whose
equality is the relation of these fields. -/
theorem TelRel.eqSubst_iff (hd : sig.Distinct) {n : Nat} {s : Quality} {ps : List Parameter}
    {Θ : Telescope 0 [] ps} {S : FieldsRel} {rs' : Nat → Option TermRel}
    {rs : Nat → Option Name} {inst : Name → Term 0 []}
    (h : TelRel sig ι n (fun m _ => levelRel sig ι m) s rs' Θ S) (hH : Θ.RecHeads sig ι inst rs)
    (hR : ∀ i R, rs' i = some R → ∃ D, rs i = some D ∧
      ∀ t u, R t u ↔ ValidEqTerm₀ sig ι t u (inst D))
    (ts us : Args 0 [] ps) :
    S ts.terms us.terms ↔ EqSubst sig ι (Context.empty.append Θ) ts.toSubst us.toSubst :=
  ⟨fun hS => by
    obtain ⟨ts', us', h₁, h₂, hτ⟩ := h.to_eqSubst hd hH (fun i R hi =>
      have ⟨D, hD, hRD⟩ := hR i R hi
      ⟨D, hD, fun t u => (hRD t u).1⟩) _ _ hS
    rw [Args.terms_inj h₁, Args.terms_inj h₂] at hτ
    exact hτ,
  fun hτ => h.of_eqSubst hH (fun i R hi =>
    have ⟨D, hD, hRD⟩ := hR i R hi
    ⟨D, hD, fun t u => (hRD t u).2⟩) ts us hτ⟩

/-- Two closed terms that compute to types of `U_l` with the same equality of their terms and, for each
program, a common relation of run time are equal terms of `U_l`, in a signature whose names are
distinct. -/
theorem ValidEqTerm₀.ofUniv (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {R : TermRel}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).univ v R) (hw : (levelRel sig ι l.closedValue).univ w R)
    (hr : ∀ P, ∃ Q, (levelRel sig ι l.closedValue).run P v Q ∧
      (levelRel sig ι l.closedValue).run P w Q) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.type, l⟩) := by
  have hU := HasEq.univ (sig := sig) (ι := ι) (l.closedValue + 1)
    (levelRel_univ_iff.2 (.univ (l := l) rfl rfl))
  exact ⟨⟨hd, _, _, _, Computes.sort _ _, Computes.sort _ _, hU, hU, fun _ _ => .rfl⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, ht, hu, hU, ⟨R, hv, hw⟩, hr⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

/-- Two closed terms that compute to propositions of `Ω_l` with the same truth are equal terms of
`Ω_l`, in a signature whose names are distinct. -/
theorem ValidEqTerm₀.ofProp (hd : sig.Distinct) {t u v w : Term 0 []} {l : Level 0} {b : Prop}
    (ht : Computesι sig ι t v) (hu : Computesι sig ι u w)
    (hv : (levelRel sig ι l.closedValue).prop v b) (hw : (levelRel sig ι l.closedValue).prop w b) :
    ValidEqTerm₀ sig ι t u (.sort ⟨.prop, l⟩) := by
  have hU : HasEq sig ι (.sort ⟨.prop, l⟩)
      (fun P Q => ∃ b₁ b₂, (levelRel sig ι l.closedValue).prop P b₁ ∧
        (levelRel sig ι l.closedValue).prop Q b₂ ∧ (b₁ ↔ b₂)) :=
    .univ (l.closedValue + 1) (levelRel_univ_iff.2 (.prop rfl rfl))
  exact ⟨⟨hd, _, _, _, Computes.sort _ _, Computes.sort _ _, hU, hU, fun _ _ => .rfl⟩,
    fun _ => ⟨_, _, _, _, Computes.sort _ _, ht, hu, hU, b, b, hv, hw, .rfl⟩,
    fun hP => absurd hP not_computesToProp_sort⟩

-- ADE: none.
/-- The instance of a type of a block at the parameters themselves, at the values of the levels
`ls`, substituted by the arguments `ā`, is the instance of the type at `ls` and `ā`, up to the
levels. -/
theorem TypeDeclaration.blockInstance_atLevels_subst (decl : TypeDeclaration) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (as : InstanceArgs 0 [] decl.scope) (D : Name) :
    Term.LevelEquiv (((decl.blockInstance (.ofLists qs ps hq hp) D (.identity decl.scope)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst) (.inst D qs ls ps as) := by
  show Term.LevelEquiv (.inst D (List.ofFn (qs.getFin hq))
    ((List.ofFn Level.var).map (Level.subst fun i => Level.ofNat (ls.getFin hl i).closedValue))
    (List.ofFn (ps.getFin hp))
    (((InstanceArgs.identity decl.scope).substLevels
      fun i => Level.ofNat (ls.getFin hl i).closedValue).subst as.toSubst)) _
  rw [List.ofFn_getFin, List.ofFn_getFin, InstanceArgs.identity_substLevels,
    InstanceArgs.identity_subst_toSubst]
  exact .inst D qs ps (Level.ListEquiv.of_getFin (by simp) hl fun i => by
      simp only [List.getFin, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Fin.val_cast,
        Level.subst]
      exact Level.ofNat_closedValue _) (InstanceArgs.LevelEquiv.refl as)

-- ADE: none.
/-- At equal closed arguments of the parameters of a meaningful type declaration, the fields of each
constructor of one of its types, at relations `Rf D` of its recursive fields of the type `D`, are
telescopes of the graph of its sort with one equality `S Rf c` of their terms, defined from the graph
rather than chosen, since the graph gives one at most; when the relations `Rf D` are the equalities
of the instances of the types of the block, at the first arguments, the equality relates the terms
of equal arguments of the fields, and only them. -/
theorem ValidTypeDeclaration.fieldsRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality} {ls : List (Level 0)}
    {ps : List Grade} (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels)
    (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp)) {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      ∀ Rf, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S Rf c) ∧
        TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S Rf c) ∧
        ((∀ D ∈ decl.names, ∀ t u, Rf D t u ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁)) →
          (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            S Rf c ts.terms us.terms ↔ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
          ∀ fs₁ fs₂, S Rf c fs₁ fs₂ → ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
            ts.terms = fs₁ ∧ us.terms = fs₂ ∧ EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) := by
  have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
    fun i => Level.ofNat_closedValue _
  have has' := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hn : (((decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue).level.closedValue)
      = ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue :=
    Level.subst_equiv hls _ Fin.elim0
  have hΘ : ∀ (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
      (as : InstanceArgs 0 [] decl.scope),
      Telescope.LevelEquiv (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) := fun _ _ =>
    (Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _)
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun Rf c ts us =>
    ∃ S', TelRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) (decl.sort (.ofLists qs ps hq hp)).quality
      (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf)
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' ts us
  refine ⟨S, fun Rf T hT c hc => ?_⟩
  have hF := (hv.fields _ hadm hT hc fun i => (ls.getFin hl i).closedValue).2 _ _ has'
  obtain ⟨S', h₁, h₂⟩ := hF.telRel hd Rf
  have h₁' := hn ▸ TelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₁ (hΘ c as₁)
  have h₂' := hn ▸ TelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₂ (hΘ c as₂)
  have hS : S Rf c = S' := funext fun ts => funext fun us => propext
    ⟨fun ⟨_, h', hs⟩ => (TelRel.unique hd ih h' _ _ h₁' ts us).1 hs, fun hs => ⟨S', h₁', hs⟩⟩
  rw [hS]
  refine ⟨h₁', h₂', fun hRf => ?_⟩
  have hH := hF.recHeads
  have hinst : ∀ D t u, ValidEqTerm₀ sig ι t u (((decl.blockInstance (.ofLists qs ps hq hp) D
        (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
        as₁.toSubst) ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) := fun D t u =>
    have he := decl.blockInstance_atLevels_subst hq hl hp as₁ D
    ⟨fun h => h.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) he,
      fun h => h.levelEquiv (Term.LevelEquiv.refl _) (Term.LevelEquiv.refl _) he.symm⟩
  have hR : ∀ i R, ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map Rf = some R →
      ∃ D, (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i = some D ∧
        ∀ t u, R t u ↔ ValidEqTerm₀ sig ι t u (((decl.blockInstance (.ofLists qs ps hq hp) D
          (.identity decl.scope)).atLevels fun i => (ls.getFin hl i).closedValue).subst
          as₁.toSubst) := fun i R hi => by
    cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
    | none => rw [hr] at hi; cases hi
    | some D =>
      rw [hr] at hi
      cases hi
      exact ⟨D, rfl, fun t u =>
        (hRf D (Telescope.recursionAt_mem hr) t u).trans (hinst D t u).symm⟩
  have hE : ∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
      EqSubst sig ι (Context.empty.append (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as₁.toSubst)) ts.toSubst us.toSubst ↔
      EqSubst sig ι (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
        ts.toSubst us.toSubst := fun _ _ =>
    ⟨EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hΘ c as₁)),
      EqSubst.levelEquiv (Context.LevelEquiv.append .empty (hΘ c as₁).symm)⟩
  refine ⟨fun ts us => (TelRel.eqSubst_iff hd h₁ hH hR ts us).trans (hE ts us),
    fun fs₁ fs₂ hs => ?_⟩
  obtain ⟨ts, us, rfl, rfl, hτ⟩ := TelRel.to_eqSubst hd h₁ hH (fun i R hi =>
    have ⟨D, hD, hRD⟩ := hR i R hi
    ⟨D, hD, fun t u => (hRD t u).1⟩) fs₁ fs₂ hs
  exact ⟨ts, us, rfl, rfl, (hE ts us).1 hτ⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe, at equal closed
arguments of its parameters, are types of the graph of its sort whose equality is `(eq_μ)`, at the
equality `S` of the fields that the graph gives, which grows with the relations of the recursive
fields; at the relations `(eq_μ)` of the recursive fields, `S` relates the terms of equal arguments
of the fields at the first arguments, and only them, and each of them to itself. -/
theorem ValidTypeDeclaration.univRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) :
    ∃ S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockRel decl.dataTypes S T.name) ∧
        UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockRel decl.dataTypes S T.name)) ∧
      (∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us) ∧
      (∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S X c ts us →
        Terms.RecRel (fun D => (X D).computed sig ι)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockRel decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockRel decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockRel decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun X => S₀ fun D => (X D).computed sig ι
  have hU : ∀ T ∈ decl.dataTypes,
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockRel decl.dataTypes S T.name) ∧
      UnivRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockRel decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun X D => (X D).computed sig ι) (fun X T hT c hc => (hS₀ _ T hT c hc).1) X Y
      fun D _ _ => TermRel.computed_mono (hXY D)
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  have hF : ∀ T ∈ decl.dataTypes, FieldRel sig ι
      ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m) .type (.inst T.name qs ls ps as₁)
      ((DataType.blockRel decl.dataTypes S T.name).computed sig ι) := fun T hT =>
    .univ rfl (hU T hT).1
  refine ⟨S, hU, hmono, fun X T hT c hc ts us h =>
    TelRel.recRel hd (hS₀ _ T hT c hc).1 _ (fun _ => rfl) ts us h, fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, ∀ t u,
      (DataType.blockRel decl.dataTypes S D).computed sig ι t u ↔
        ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) := fun D hD t u => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    exact ⟨fun h => (hF T' hT').validEqTerm hd (hI _) h,
      fun h => (hF T' hT').of_validEqTerm (hI _) h⟩
  obtain ⟨-, -, hiff⟩ := hS₀ (fun D => (DataType.blockRel decl.dataTypes S D).computed sig ι) T hT c hc
  obtain ⟨hof, hto⟩ := hiff hRf
  refine ⟨hof, hto, fun fs₁ fs₂ h => ?_⟩
  have hper : IsPer (S (DataType.blockRel decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i x hx => by
      cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D =>
        rw [hr] at hx
        cases hx
        obtain ⟨T', hT', rfl⟩ :=
          TypeDeclaration.mem_names_of_dataTypes hT (Telescope.recursionAt_mem hr)
        exact FieldRel.isPer hd ih (hF T' hT')) (hS₀ _ T hT c hc).1
  exact hper.trans h (hper.symm h)

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe of propositions,
at equal closed arguments of its parameters, are propositions of the graph of its sort whose truth
is `(true_μ)`, at the equality `S` of the fields that the graph gives, which grows with the truths
of the recursive fields; at the truths `(true_μ)` of the recursive fields, `S` relates the terms of
equal arguments of the fields at the first arguments, and only them. -/
theorem ValidTypeDeclaration.propRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .prop) :
    ∃ S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope → FieldsRel,
      (∀ T ∈ decl.dataTypes,
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.blockTruth decl.dataTypes S T.name) ∧
        PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.blockTruth decl.dataTypes S T.name)) ∧
      (∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
        ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us) ∧
      (∀ B, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors, ∀ ts us, S B c ts us →
        Terms.RecRel (fun D _ _ => B D)
          ((c.fields (.ofLists qs ps hq hp)).recursion decl.names) ts us) ∧
      ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
        (∀ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)),
          S (DataType.blockTruth decl.dataTypes S) c ts.terms us.terms ↔ EqSubst sig ι
            (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
            ts.toSubst us.toSubst) ∧
        (∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          ∃ ts us : Args 0 [] (c.params (.ofLists qs ps hq hp)), ts.terms = fs₁ ∧ us.terms = fs₂ ∧
            EqSubst sig ι
              (Context.empty.append (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
              ts.toSubst us.toSubst) ∧
        ∀ fs₁ fs₂, S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₂ →
          S (DataType.blockTruth decl.dataTypes S) c fs₁ fs₁ := by
  obtain ⟨S₀, hS₀⟩ := ValidTypeDeclaration.fieldsRel hd hv hq hl hp hadm has
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  let S : (Name → Prop) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      FieldsRel := fun B => S₀ fun D _ _ => B D
  have hP : ∀ T ∈ decl.dataTypes,
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
        (DataType.blockTruth decl.dataTypes S T.name) ∧
      PropRel sig ι ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
        (DataType.blockTruth decl.dataTypes S T.name) := fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc => hs ▸ (hS₀ _ T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun B T' hT' c hc =>
        hs ▸ (hS₀ _ T' hT' c hc).2.1⟩
  have hmono : ∀ B B' : Name → Prop, (∀ D, B D → B' D) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S B c ts us → S B' c ts us := fun B B' hB =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as₁⟩)
      (F := fun B D (_ _ : Term 0 []) => B D) (fun B T hT c hc => (hS₀ _ T hT c hc).1) B B'
      fun D _ _ => hB D
  have hI : ∀ D, Computesι sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₁) :=
    fun _ => ⟨.refl _, .inst _ _ _ _ _⟩
  refine ⟨S, hP, hmono, fun B T hT c hc ts us h =>
    TelRel.recRel hd (hS₀ _ T hT c hc).1 _ (fun _ => rfl) ts us h, fun T hT c hc => ?_⟩
  have hRf : ∀ D ∈ decl.names, ∀ t u,
      DataType.blockTruth decl.dataTypes S D ↔ ValidEqTerm₀ sig ι t u (.inst D qs ls ps as₁) :=
      fun D hD t u => by
    obtain ⟨T', hT', rfl⟩ := TypeDeclaration.mem_names_of_dataTypes hT hD
    have hF : FieldRel sig ι
        ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m) .prop (.inst T'.name qs ls ps as₁)
        (fun _ _ => DataType.blockTruth decl.dataTypes S T'.name) := .prop (hP T' hT').1
    exact ⟨fun h => hF.validEqTerm hd (hI _) h, fun h => hF.of_validEqTerm (hI _) h⟩
  obtain ⟨hof, hto⟩ := (hS₀ (fun D _ _ => DataType.blockTruth decl.dataTypes S D) T hT c hc).2.2 hRf
  have hper : IsPer (S (DataType.blockTruth decl.dataTypes S) c) :=
    TelRel.isPer hd ih (fun i x hx => by
      cases hr : (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i with
      | none => rw [hr] at hx; cases hx
      | some D => rw [hr] at hx; cases hx; exact ⟨id, fun h _ => h⟩) (hS₀ _ T hT c hc).1
  exact ⟨hof, hto, fun _ _ h => hper.trans h (hper.symm h)⟩

-- ADE: none.
/-- The instances of the types of a meaningful block of data types in a universe, at equal closed
arguments of its parameters, are types of the graph of run time of its sort whose relation of run
time is `(®_μ)`, at a relation `S` of the fields common to the two arguments, for each program `P`:
the fields of each constructor at the two arguments are telescopes of the graph of run time with
the same relation, defined from the graph at the first arguments, rather than chosen, since the
graph gives one at most. -/
theorem ValidTypeDeclaration.runUnivRel (hd : sig.Distinct) {decl : TypeDeclaration}
    (hdecl : .typeDeclaration decl ∈ sig) (hv : ValidTypeDeclaration sig ι decl)
    {qs : List Quality} {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) (P : Program) :
    ∃ S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        RunFieldsRel,
      ∀ T ∈ decl.dataTypes,
        RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₁)
          (DataType.runBlockRel sig decl.dataTypes S T.name) ∧
        RunUnivRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
          (fun m _ => levelRel sig ι m) (.inst T.name qs ls ps as₂)
          (DataType.runBlockRel sig decl.dataTypes S T.name) := by
  have hls : ∀ i, Level.ofNat (ls.getFin hl i).closedValue ≈ ls.getFin hl i :=
    fun i => Level.ofNat_closedValue _
  have has' := EqSubst.levelEquiv
    (Context.substLevels_levelEquiv (fun i => Level.equivalence.symm (hls i)) _) has
  have hn : (((decl.sort (.ofLists qs ps hq hp)).atLevels fun i => (ls.getFin hl i).closedValue).level.closedValue)
      = ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue :=
    Level.subst_equiv hls _ Fin.elim0
  have hΘ : ∀ (c : Constructor decl.sorts decl.grades decl.levels decl.scope)
      (as : InstanceArgs 0 [] decl.scope),
      Telescope.LevelEquiv (((c.fields (.ofLists qs ps hq hp)).atLevels
        fun i => (ls.getFin hl i).closedValue).subst as.toSubst)
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) := fun _ _ =>
    (Telescope.substLevels_levelEquiv hls _).subst (Subst.LevelEquiv.refl _)
  have ihm : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have ih : ∀ m, m < ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue →
      RunLevelRel.Unique ((levelRel sig ι m).run P) := fun m _ => levelRel_run_unique hd m
  let S : (Name → RunRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
      RunFieldsRel := fun X c H ts bs =>
    ∃ S', RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
      (fun m _ => levelRel sig ι m)
      (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
        fun D' => (X D').computed sig ι)
      (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) S' ∧ S' H ts bs
  have hS : ∀ X, ∀ T ∈ decl.dataTypes, ∀ c ∈ T.constructors,
      RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m)
        (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
          fun D' => (X D').computed sig ι)
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁) (S X c) ∧
      RunTelRel sig ι P ((decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)).closedValue
        (fun m _ => levelRel sig ι m)
        (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
          fun D' => (X D').computed sig ι)
        (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₂) (S X c) := fun X T hT c hc => by
    have hF := (hv.fields _ hadm hT hc fun i => (ls.getFin hl i).closedValue).2 _ _ has'
    obtain ⟨S', h₁, h₂⟩ := hF.runTelRel hd P hs fun D' => (X D').computed sig ι
    have h₁' := hn ▸ RunTelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₁ (hΘ c as₁)
    have h₂' := hn ▸ RunTelRel.levelEquiv (fun m _ => levelRel_levelInvariant m) h₂ (hΘ c as₂)
    have hSS : S X c = S' := funext fun H => funext fun ts => funext fun bs => propext
      ⟨fun ⟨_, h', hs⟩ => (RunTelRel.congr hd ihm ih h' _ _ h₁'
          (fun _ => Option.rel_refl (fun _ _ _ _ => .rfl) _) H ts bs).1 hs,
        fun hs => ⟨S', h₁', hs⟩⟩
    rw [hSS]
    exact ⟨h₁', h₂'⟩
  exact ⟨S, fun T hT =>
    ⟨.data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => (hS X T' hT' c hc).1,
      .data ⟨hdecl, hT, rfl⟩ hq hl hp rfl hs rfl S fun X T' hT' c hc => (hS X T' hT' c hc).2⟩⟩

-- ADE: none.
/-- `(D)`, closed: two instances of a declared type of `Σ`, whose type declaration is meaningful, at
the same levels and at equal arguments of its parameters, are equal terms of its sort: the fields
of each constructor at the two arguments are telescopes of the graph of the sort with the same
equality of their terms, and of the graph of run time with the same relation of their terms, for
each program. -/
theorem ValidEqTerm₀.inst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl) {qs : List Quality}
    {ls : List (Level 0)} {ps : List Grade} (hq : qs.length = decl.sorts)
    (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst) :
    ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ((decl.sort (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))) := by
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : ∀ as : InstanceArgs 0 [] decl.scope,
      Computesι sig ι (.inst T.name qs ls ps as) (.inst T.name qs ls ps as) :=
    fun as => ⟨.refl _, .inst _ _ _ _ as⟩
  show ValidEqTerm₀ sig ι _ _ (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
    (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩)
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · obtain ⟨S, hU, -⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofUniv hd (hw as₁) (hw as₂) (levelRel_univ_iff.2 (hU T hT).1)
      (levelRel_univ_iff.2 (hU T hT).2) fun P =>
        have ⟨S', hR⟩ := hv.runUnivRel hd hdecl hq hl hp hadm has hs P
        ⟨_, levelRel_run_iff.2 (hR T hT).1, levelRel_run_iff.2 (hR T hT).2⟩
  · obtain ⟨S, hP, -⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    exact ValidEqTerm₀.ofProp hd (hw as₁) (hw as₂) (levelRel_prop_iff.2 (hP T hT).1)
      (levelRel_prop_iff.2 (hP T hT).2)

-- ADE: none.
/-- `(c)` and `(c_≡)`, closed: two applications of a constructor of a declared type of `Σ`, whose
type declaration is meaningful, at the same levels, at equal arguments of the parameters and at
equal arguments of its fields, are equal terms of the instance: canonical terms that `(eq_c)`
relates, or proofs of a proposition that the first one makes true. -/
theorem ValidEqTerm₀.ctor (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) (hv : ValidTypeDeclaration sig ι decl)
    (hc : con ∈ T.constructors) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hadm : decl.constraint (.ofLists qs ps hq hp))
    {as₁ as₂ : InstanceArgs 0 [] decl.scope}
    (has : EqSubst sig ι ((decl.params (.ofLists qs ps hq hp)).substLevels (ls.getFin hl))
      as₁.toSubst as₂.toSubst)
    {ts us : Args 0 [] (con.params (.ofLists qs ps hq hp))}
    (hts : EqSubst sig ι (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as₁))
      ts.toSubst us.toSubst) :
    ValidEqTerm₀ sig ι (.ctor D qs ls ps as₁ con.name ts.terms)
      (.ctor D qs ls ps as₂ con.name us.terms) (.inst D qs ls ps as₁) := by
  have hI : ValidEqTerm₀ sig ι (.inst D qs ls ps as₁) (.inst D qs ls ps as₂)
      (.sort ⟨(decl.sort (.ofLists qs ps hq hp)).quality,
        (decl.sort (.ofLists qs ps hq hp)).level.subst (ls.getFin hl)⟩) :=
    ValidEqTerm₀.inst hd h hv hq hl hp hadm has
  obtain ⟨hdecl, hT, rfl⟩ := h
  have hw : Computesι sig ι (.inst T.name qs ls ps as₁) (.inst T.name qs ls ps as₁) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  have hct : ∀ (as : InstanceArgs 0 [] decl.scope) (ts : Terms 0 []),
      Computesι sig ι (.ctor T.name qs ls ps as con.name ts)
        (.ctor T.name qs ls ps as con.name ts) :=
    fun _ _ => ⟨.refl _, .ctor _ _ _ _ _ _ _⟩
  cases hs : (decl.sort (.ofLists qs ps hq hp)).quality
  · rw [hs] at hI
    obtain ⟨S, hU, hmono, hrec, hiff⟩ := hv.univRel hd hdecl hq hl hp hadm has hs
    have hU' := levelRel_univ_iff.2 (hU T hT).1
    have hrel : DataType.blockRel decl.dataTypes S T.name
        (.ctor T.name qs ls ps as₁ con.name ts.terms) (.ctor T.name qs ls ps as₂ con.name us.terms) :=
      DataType.blockRel_closed hmono hT ⟨con, hc, ts.terms, us.terms, ⟨qs, ls, ps, _, as₁, rfl⟩,
        ⟨qs, ls, ps, _, as₂, rfl⟩, ((hiff T hT con hc).1 ts us).2 hts⟩
    refine ⟨(ValidEqTerm₀.univType hI).left,
      fun _ => ⟨_, _, _, _, hw, hct _ _, hct _ _, .univ _ hU', hrel⟩, fun ⟨v, hv', _, _, hP⟩ => ?_⟩
    cases Computesι.det hd hw hv'
    exact (HasEq.univ_not_prop hd hU' hP).elim
  · rw [hs] at hI
    obtain ⟨S, hP, hmono, hrec, hiff⟩ := hv.propRel hd hdecl hq hl hp hadm has hs
    have hP' := levelRel_prop_iff.2 (hP T hT).1
    have htrue : DataType.blockTruth decl.dataTypes S T.name :=
      DataType.blockTruth_closed hmono hT ⟨con, hc, ts.terms,
        (hiff T hT con hc).2.2 _ _ (((hiff T hT con hc).1 ts us).2 hts)⟩
    refine ⟨(ValidEqTerm₀.propType hI).left, fun hn => absurd ⟨_, hw, _, _, hP'⟩ hn,
      fun _ => ⟨_, fun _ _ => DataType.blockTruth decl.dataTypes S T.name, hw,
        .prop _ _ hP' fun _ _ => .rfl, htrue⟩⟩

/-- The equality of the terms of an instance in a universe of a data type of `Σ` is `(eq_μ)`, at an
equality of the fields of the constructors of its block that the graph gives. -/
theorem HasEq.dataInst (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type) {as : InstanceArgs 0 [] decl.scope}
    {R : TermRel} (hR : HasEq sig ι (.inst D qs ls ps as) R) :
    ∃ (n : Nat) (S : (Name → TermRel) → Constructor decl.sorts decl.grades decl.levels decl.scope →
        FieldsRel),
      (∀ X, ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors,
        TelRel sig ι n (fun m _ => levelRel sig ι m) .type
          (fun i => ((c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i).map
            fun D' => (X D').computed sig ι)
          (c.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as) (S X c)) ∧
      ∀ t u, R t u ↔ DataType.blockRel decl.dataTypes S D t u := by
  cases hR with
  | univ n hU =>
    rw [levelRel_univ_iff] at hU
    cases hU with
    | data h' _ _ _ hv _ _ S hS =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      cases has
      exact ⟨n, S, hS, fun _ _ => .rfl⟩
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim
  | prop n b hP _ =>
    rw [levelRel_prop_iff] at hP
    cases hP with
    | data h' _ _ _ hv hs' =>
      obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
      subst hD hqs hls hps
      obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
      exact nomatch hs.symm.trans hs'
    | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

/-- A proposition that is an instance of a data type of `Σ` is an instance in a universe of
propositions. -/
theorem PropRel.dataInst_quality (hd : sig.Distinct) {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hp : ps.length = decl.grades)
    {as : InstanceArgs 0 [] decl.scope} {n : Nat} {b : Prop}
    (hP : (levelRel sig ι n).prop (.inst D qs ls ps as) b) :
    (decl.sort (.ofLists qs ps hq hp)).quality = .prop := by
  rw [levelRel_prop_iff] at hP
  cases hP with
  | data h' _ _ _ hv hs' =>
    obtain ⟨-, hD, hqs, hls, hps, has⟩ := Term.inst.inj hv
    subst hD hqs hls hps
    obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h h'
    exact hs'
  | codata h' _ _ _ hv => exact (hd.inst_data_codata h h' hv).elim

-- ADE: none.
/-- Two equal terms of an instance in a universe of a data type of `Σ` whose constructors have no
recursive field compute to the same constructor of a type of the block, applied to equal arguments
of its fields: the canonical terms that `(eq_μ)` relates, which the equality of the instance, its
meaning as a type, gives. -/
theorem ValidEqTerm₀.ctor_inv {decl : TypeDeclaration} {D : Name}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasDataType D decl T) {qs : List Quality} {ls : List (Level 0)} {ps : List Grade}
    (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
    (hs : (decl.sort (.ofLists qs ps hq hp)).quality = .type)
    (hnr : ∀ T' ∈ decl.dataTypes, ∀ c ∈ T'.constructors, ∀ i,
      (c.fields (.ofLists qs ps hq hp)).recursionAt decl.names i = none)
    {as : InstanceArgs 0 [] decl.scope} {t₁ t₂ : Term 0 []}
    (ht : ValidEqTerm₀ sig ι t₁ t₂ (.inst D qs ls ps as)) :
    ∃ T' ∈ decl.dataTypes, T'.name = D ∧ ∃ con ∈ T'.constructors,
      ∃ ts₁ ts₂ : Args 0 [] (con.params (.ofLists qs ps hq hp)),
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₁ (.ctor D qs' ls' ps' as' con.name ts₁.terms)) ∧
        (∃ (qs' : List Quality) (ls' : List (Level 0)) (ps' : List Grade) (Δ' : Scope)
          (as' : InstanceArgs 0 [] Δ'),
          Computesι sig ι t₂ (.ctor D qs' ls' ps' as' con.name ts₂.terms)) ∧
        EqSubst sig ι
          (Context.empty.append (con.fieldsAt (.ofLists qs ps hq hp) (ls.getFin hl) as))
          ts₁.toSubst ts₂.toSubst := by
  obtain ⟨⟨hd, v, -, R, hv, -, hR, -⟩, hne, -⟩ := ht
  have hw : Computesι sig ι (.inst D qs ls ps as) (.inst D qs ls ps as) :=
    ⟨.refl _, .inst _ _ _ _ _⟩
  cases Computesι.det hd hw hv
  obtain ⟨n, S, hS, hiff⟩ := HasEq.dataInst hd h hq hl hp hs hR
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  have hmono : ∀ X Y : Name → TermRel, (∀ D v w, X D v w → Y D v w) → ∀ T ∈ decl.dataTypes,
      ∀ c ∈ T.constructors, ∀ ts us, S X c ts us → S Y c ts us := fun X Y hXY =>
    TelRel.block_mono hd ih (Θ := fun c => ⟨_, c.fieldsAt _ _ as⟩)
      (F := fun X D => (X D).computed sig ι) hS X Y fun D _ _ => TermRel.computed_mono (hXY D)
  obtain ⟨v', w₁, w₂, R', hv', hw₁, hw₂, hR', hrel⟩ := hne fun ⟨v', hv', _, _, hP⟩ => by
    cases Computesι.det hd hw hv'
    exact nomatch hs.symm.trans (PropRel.dataInst_quality hd h hq hp hP)
  cases Computesι.det hd hw hv'
  have hrel' := (hiff w₁ w₂).1 ((HasEq.unique hd hR' hR w₁ w₂).1 hrel)
  obtain ⟨T', hT', hn, c, hc, fs₁, fs₂, ⟨qs₁, ls₁, ps₁, Δ₁, as₁, rfl⟩,
    ⟨qs₂, ls₂, ps₂, Δ₂, as₂, rfl⟩, hfs⟩ := DataType.blockRel_inv hmono hrel'
  obtain ⟨ts₁, ts₂, rfl, rfl, hts⟩ := (hS _ T' hT' c hc).to_eqSubst hd
    (Telescope.recHeads_none (fun _ => .sort ⟨.type, .zero⟩) _)
    (fun i R hi => by rw [hnr T' hT' c hc i] at hi; cases hi) _ _ hfs
  exact ⟨T', hT', hn, c, hc, ts₁, ts₂, ⟨_, _, _, _, _, hn ▸ hw₁⟩, ⟨_, _, _, _, _, hn ▸ hw₂⟩, hts⟩

end
end Sic.Core
