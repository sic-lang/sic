module

public import Sic.Core.Meaning.RunTime.Properties
import Sic.Core.Meaning.Equality.Nesting
import Sic.Core.Meaning.Equality.Properties

/-!
# Uniqueness of the Relations of the Levels

The relations of every level of annex 18 of RFC 36 are unique, by induction on the level: the
equality of the terms of a type is a partial equivalence relation, and it is unique, as are the
truth of a proposition and the relation of run time of a type, given those of the levels below it,
which `Sic.Core.Meaning.Equality.Properties` and `Sic.Core.Meaning.RunTime.Properties` prove on the
graphs of a level.
The graph of the nestings of a level has the same properties, at the relations that a nesting
holds, and agrees with the graph of the types, which `Sic.Core.Meaning.Equality.Nesting` proves.
The graph of the nestings of run time of a level gives a type a unique relation too, at the
relations that a nesting holds.
The equality of the terms of a universe compares the relations of run time of the level below it,
so that its transitivity needs their uniqueness, which the induction gives with the partial
equivalence relations.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- The relations of every level are partial equivalence relations, and their relations of run time
unique, in a signature whose names are distinct. -/
theorem levelRel_isPer {sig : Signature} {ι : Interpretation} (hd : sig.Distinct) (n : Nat) :
    (levelRel sig ι n).IsPer :=
  have ih : ∀ m, m < n → (levelRel sig ι m).IsPer := fun m _ => levelRel_isPer hd m
  { univ_isPer := fun h => UnivRel.isPer hd ih (levelRel_univ_iff.1 h)
    univ_unique := fun h h' =>
      UnivRel.unique hd ih (levelRel_univ_iff.1 h) _ (levelRel_univ_iff.1 h')
    prop_unique := fun h h' =>
      PropRel.unique hd ih (levelRel_prop_iff.1 h) _ (levelRel_prop_iff.1 h')
    run_unique := fun h h' =>
      RunUnivRel.congr hd ih (fun m hm => (ih m hm).run_unique) (levelRel_run_iff.1 h) _
        (levelRel_run_iff.1 h') }
termination_by n
decreasing_by all_goals assumption

/-- `eq(v)` is a partial equivalence relation, symmetric and transitive, in a signature whose names
are distinct.
RFC: `\mathsf{per}_{\mathsf{eq}}.\mathsf{symm}`
RFC: `\mathsf{per}_{\mathsf{eq}}.\mathsf{trans}` -/
theorem HasEq.isPer {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R : TermRel}
    (hd : sig.Distinct) : HasEq sig ι v R → IsPer R
  | .univ n h => (levelRel_isPer hd n).univ_isPer h
  | .prop _ _ _ hR => ⟨fun h => (hR _ _).2 ((hR _ _).1 h), fun h _ => (hR _ _).2 ((hR _ _).1 h)⟩

/-- `eq(v)` is unique: two equalities of the terms of a type relate the same terms, in a signature
whose names are distinct.
RFC: `\mathsf{unique}_{\mathsf{eq}}` -/
theorem HasEq.unique {sig : Signature} {ι : Interpretation} {v : Term 0 []} {R R' : TermRel}
    (hd : sig.Distinct) : HasEq sig ι v R → HasEq sig ι v R' → ∀ t u, R t u ↔ R' t u
  | .univ n h, .univ _ h' => by
    cases HasEq.univ_level hd h h'
    exact (levelRel_isPer hd n).univ_unique h h'
  | .univ _ h, .prop _ _ h' _ => (HasEq.univ_not_prop hd h h').elim
  | .prop _ _ h _, .univ _ h' => (HasEq.univ_not_prop hd h' h).elim
  | .prop k _ h hR, .prop _ _ h' hR' => by
    cases PropRel.level hd (levelRel_prop_iff.1 h) (levelRel_prop_iff.1 h')
    exact fun t u => (hR t u).trans (((levelRel_isPer hd k).prop_unique h h').trans (hR' t u).symm)

/-- `ty(s_n)[λ]` gives a type a partial equivalence relation, symmetric and transitive, when the
relations that the nesting holds are, in a signature whose names are distinct.
RFC: `\mathsf{per}_\lambda.\mathsf{symm}`
RFC: `\mathsf{per}_\lambda.\mathsf{trans}` -/
theorem levelRel_nest_isPer {sig : Signature} {ι : Interpretation} {n : Nat} {s : Quality}
    {τ : Nest NestLeaf} {A : Term 0 []} {F : TermRel} (hd : sig.Distinct)
    (h : NestRel sig ι n (fun m _ => levelRel sig ι m) s τ A F)
    (hτ : Nest.All (fun x => IsPer x.2) τ) : IsPer F :=
  NestRel.isPer hd (fun m _ => levelRel_isPer hd m) hτ h

/-- `ty(s_n)[λ]` gives a type a unique equality of its terms: two equalities of a type at a nesting
relate the same terms, in a signature whose names are distinct.
RFC: `\mathsf{unique}_\lambda` -/
theorem levelRel_nest_unique {sig : Signature} {ι : Interpretation} {n : Nat} {s s' : Quality}
    {τ : Nest NestLeaf} {A : Term 0 []} {F F' : TermRel} (hd : sig.Distinct)
    (h : NestRel sig ι n (fun m _ => levelRel sig ι m) s τ A F)
    (h' : NestRel sig ι n (fun m _ => levelRel sig ι m) s' τ A F') : ∀ t u, F t u ↔ F' t u :=
  NestRel.unique hd (fun m _ => levelRel_isPer hd m) h _ _ h'

/-- `ty(s_n)[λ]` agrees with the graph of the types: when each position of the nesting holds a type
with the equality of its terms, the equality that it gives a type is the one that the type has
without position, if it has one, in a signature whose names are distinct.
The premise `hinv`, that the graph of the types gives the types equal up to the values of their
levels the same equality, is no premise of the RFC, whose levels are equal when their values are;
the invariance of the graph by these levels is proved after this module.
RFC: `\mathsf{agree}_\lambda` -/
theorem levelRel_nest_agree {sig : Signature} {ι : Interpretation} {n : Nat} {s s' : Quality}
    {τ : Nest NestLeaf} {A : Term 0 []} {F F' : TermRel} (hd : sig.Distinct)
    (hinv : ∀ (T A : Term 0 []) (R : TermRel),
      NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain T R → Term.LevelEquiv T A →
        NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain A R)
    (h : NestRel sig ι n (fun m _ => levelRel sig ι m) s τ A F)
    (hτ : Nest.All (fun x => NestRel sig ι n (fun m _ => levelRel sig ι m) .type .plain x.1 x.2) τ)
    (h' : NestRel sig ι n (fun m _ => levelRel sig ι m) s' .plain A F') : ∀ t u, F t u ↔ F' t u :=
  NestRel.agree hd (fun m _ => levelRel_isPer hd m) hinv h hτ _ _ h'

/-- The relations of run time of every level are unique, in a signature whose names are
distinct. -/
theorem levelRel_run_unique {sig : Signature} {ι : Interpretation} {P : Program}
    (hd : sig.Distinct) (n : Nat) : RunLevelRel.Unique ((levelRel sig ι n).run P) :=
  (levelRel_isPer hd n).run_unique

/-- `rt(U_n)[λ]` gives a type a unique relation of run time: two relations of run time of a type at
a nesting relate the same terms to the same addresses in each heap, in a signature whose names are
distinct.
RFC: `\mathsf{unique}_{\circledR\lambda}` -/
theorem levelRel_runNest_unique {sig : Signature} {ι : Interpretation} {P : Program} {n : Nat}
    {τ : Nest RunNestLeaf} {A : Term 0 []} {R R' : RunRel} (hd : sig.Distinct)
    (h : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R)
    (h' : RunNestRel sig ι P n (fun m _ => levelRel sig ι m) τ A R') :
    ∀ H t a, R H t a ↔ R' H t a :=
  RunNestRel.unique hd (fun m _ => levelRel_isPer hd m) (fun m _ => levelRel_run_unique hd m) h _ h'

-- ADE: `irrelevanceTerm`, in `Graded/Erasure/LogicalRelation/Irrelevance.agda`.
/-- `®(v)` is unique: two relations of run time of a type relate the same terms to the same
addresses in each heap, in a signature whose names are distinct.
RFC: `\mathsf{unique}_\circledR` -/
theorem HasRun.unique {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R R' : RunRel} (hd : sig.Distinct) :
    HasRun sig ι P v R → HasRun sig ι P v R' → ∀ H t a, R H t a ↔ R' H t a
  | .univ n h, .univ _ h' => by
    cases RunUnivRel.level hd (levelRel_run_iff.1 h) (levelRel_run_iff.1 h')
    exact levelRel_run_unique hd n h h'
  | .univ _ h, .prop _ _ h' _ => (RunUnivRel.not_prop hd (levelRel_run_iff.1 h)
      (levelRel_prop_iff.1 h')).elim
  | .prop _ _ h _, .univ _ h' => (RunUnivRel.not_prop hd (levelRel_run_iff.1 h')
      (levelRel_prop_iff.1 h)).elim
  | .prop _ _ _ hR, .prop _ _ _ hR' => fun H t a => ⟨fun _ => hR' H t a, fun _ => hR H t a⟩

/-- `®(v)` is unique as a relation, in a signature whose names are distinct. -/
theorem HasRun.eq {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {R R' : RunRel} (hd : sig.Distinct) (h : HasRun sig ι P v R) (h' : HasRun sig ι P v R') :
    R = R' :=
  funext fun H => funext fun t => funext fun a => propext (h.unique hd h' H t a)

/-- Two types with a common relation of run time have the same relations of run time, in a signature
whose names are distinct. -/
theorem HasRun.iff_of_common {sig : Signature} {ι : Interpretation} {P : Program}
    {v w : Term 0 []} {R : RunRel} (hd : sig.Distinct) (hv : HasRun sig ι P v R)
    (hw : HasRun sig ι P w R) (R' : RunRel) : HasRun sig ι P v R' ↔ HasRun sig ι P w R' :=
  ⟨fun h => h.eq hd hv ▸ hw, fun h => h.eq hd hw ▸ hv⟩

/-- The relations of run time of a proposition are those that relate every term to every address,
in a signature whose names are distinct. -/
theorem HasRun.prop_iff {sig : Signature} {ι : Interpretation} {P : Program} {v : Term 0 []}
    {k : Nat} {b : Prop} (hd : sig.Distinct) (hp : (levelRel sig ι k).prop v b) (R : RunRel) :
    HasRun sig ι P v R ↔ ∀ H t a, R H t a :=
  ⟨fun h => (h.eq hd (.prop k b hp fun _ _ _ => trivial)) ▸ fun _ _ _ => trivial,
    fun hR => .prop k b hp hR⟩

end Sic.Core
