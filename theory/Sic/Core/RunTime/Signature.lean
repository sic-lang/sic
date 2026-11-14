module

public import Sic.Core.RunTime.Fundamental
public import Sic.Core.Soundness.Judgments
import Sic.Core.Erasure.Levels
import Sic.Core.RunTime.Computation
import Sic.Core.RunTime.Levels
import Sic.Core.Soundness.Closed
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Presuppositions

/-!
# Programs of a Signature

The programs that realize a signature at run time, and the fundamental lemma of annex 20 of RFC 36
in a well-formed signature whose entries use their variables as their grades allow: a program
realizes the signature when it holds the erasure of the signature by `S^{11ᵐ}` and realizes its
constant declarations of the mode `11ᵐ`, `(hyp_𝒫)`; it then realizes every constant of the mode
`11ᵐ`, those that the signature defines by the fundamental lemma of their bodies.

The realization of the constant definitions is proved entry by entry, each in the signature before
it, as the meaning of a well-formed signature is: the fundamental lemma of its body, at the values
of the levels of an instance, and the constant, which steps to its body at these levels, is related
to the address of this body, since the relation of run time reads the levels of a term by their
values and the erasure reads none.

ADE prove their fundamental lemma in a context of definitions whose terms are all erased by the
extraction or well-resourced, and their extraction compiles the definitions with the term.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- `(hyp_𝒫)`: the program `𝒫` holds the erasure `⌊Σ⌋_{S^{11ᵐ}}` of the signature, and realizes its
constant declarations of the mode `11ᵐ`: each of them, at each closed instance of its variables, is
valid at run time in the empty context, at its type at this instance.
RFC: `\mathsf{hyp}_{\mathcal{P}}` -/
structure ValidProgram (ι : Interpretation) (P : Program) (sig : Signature) : Prop where
  /-- `𝒫 ⊇ ⌊Σ⌋_{S^{11ᵐ}}`. -/
  compile : ∀ f qs ps b, sig.compile Mode.oneOne.erased f qs ps = some b → P f qs ps = some b
  /-- `𝒫` realizes the constant declarations of the mode `11ᵐ`. -/
  constantDeclaration : ∀ c, .constantDeclaration c ∈ sig → c.mode = .oneOne →
    ∀ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (hq : qs.length = c.sorts)
      (hl : ls.length = c.levels) (hp : ps.length = c.grades),
      RunValid sig ι P Scope.FirstOrder.nil .empty 𝟘ᶜ (.const c.name qs ls ps)
        (Signature.instanceType c.type (.ofLists qs ps hq hp) (ls.getFin hl))

-- ADE: none.
/-- The program of a signature whose names are distinct gives a constant of the mode `11ᵐ` that the
signature defines the erasure of its body. -/
theorem Signature.Distinct.findSome?_compile {S : Set Grade} [DecidablePred (· ∈ S)]
    {sigE : Signature} {qs : List Quality} {ps : List Grade} :
    {sig : Signature} → sig.Distinct → {d : ConstantDefinition} → .constantDefinition d ∈ sig →
      d.mode = .oneOne → (hq : qs.length = d.sorts) → (hp : ps.length = d.grades) →
        sig.findSome? (Entry.compile sigE S d.name qs ps)
          = some ((d.body (.ofLists qs ps hq hp)).erase sigE S Scope.FirstOrder.nil)
  | e :: sig, hd, d, h, hm, hq, hp => by
    have hself : Entry.compile sigE S d.name qs ps (.constantDefinition d)
        = some ((d.body (.ofLists qs ps hq hp)).erase sigE S Scope.FirstOrder.nil) := by
      simp only [Entry.compile, hm, hq, hp, and_self, ↓reduceDIte, ↓reduceIte]
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · rw [hself]
    · cases hc : Entry.compile sigE S d.name qs ps e with
      | none => exact Signature.Distinct.findSome?_compile hd.1 h' hm hq hp
      | some x =>
        have he : e = .constantDefinition d := by
          cases e with
          | constantDefinition d' =>
            have hn : d'.name = d.name := by
              simp only [Entry.compile] at hc
              split at hc
              · rename_i hn
                exact hn.1
              · exact nomatch hc
            exact Signature.Distinct.entry_unique hd List.mem_cons_self (List.mem_cons_of_mem _ h') (n := d.name)
              (by simp [Entry.names, hn]) (by simp [Entry.names])
          | _ => simp only [Entry.compile] at hc; exact nomatch hc
        subst he
        rw [hself] at hc
        cases hc
        rfl

-- ADE: none.
/-- A program that holds the erasure of a signature whose names are distinct gives a constant of the
mode `11ᵐ` that the signature defines the erasure of its body. -/
theorem ValidProgram.constantDefinition {ι : Interpretation} {P : Program} {sig : Signature}
    (hP : ValidProgram ι P sig) (hd : sig.Distinct) {d : ConstantDefinition}
    (h : .constantDefinition d ∈ sig) (hm : d.mode = .oneOne) {qs : List Quality} {ps : List Grade}
    (hq : qs.length = d.sorts) (hp : ps.length = d.grades) :
    P d.name qs ps
      = some ((d.body (.ofLists qs ps hq hp)).erase sig Mode.oneOne.erased Scope.FirstOrder.nil) :=
  hP.compile _ _ _ _ (hd.findSome?_compile h hm hq hp)

-- ADE: the case `defn` of `fundamental′`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- A program that realizes a signature `Σ` whose names are distinct realizes the constants of the
mode `11ᵐ` of a well-formed suffix of `Σ` whose entries use their variables as their grades allow,
when the interpretation gives the constant declarations of `Σ` terms of their types: a constant
definition by the fundamental lemma of its body, typed in the signature before it, whose constants
are realized by induction, and a constant declaration by `(hyp_𝒫)`. -/
theorem WfSig.realizes {ι : Interpretation} {P : Program} {sigM : Signature}
    (hι : ValidInterpretation ι sigM) (hd : sigM.Distinct) (hP : ValidProgram ι P sigM) :
    (sig : Signature) → WfSig sig → UsageSig sig → sig <:+ sigM → P.Realizes sigM ι sig
  | [], _, _, _ => fun h => by
    generalize hm : Mode.oneOne = m at h
    cases h with
    | constantDefinition h => exact nomatch h
    | constantDeclaration h => exact nomatch h
  | e :: sig, h, hu, hs => by
    have hw := Presuppositions.tail presuppositions h
    have hu' : UsageSig sig := by cases hu <;> assumption
    have hrest : P.Realizes sigM ι sig :=
      WfSig.realizes hι hd hP sig hw hu' ((List.suffix_cons e sig).trans hs)
    intro hc qs ls ps hq hl hp
    generalize hm : Mode.oneOne = m at hc
    cases hc with
    | constantDeclaration hc =>
      exact hP.constantDeclaration _ (hs.subset hc) hm.symm qs ls ps hq hl hp
    | constantDefinition hc =>
      rcases List.mem_cons.1 hc with rfl | hc'
      · cases h with
        | constantDefinition hdef _ =>
        cases hdef with
        | intro _ _ ht =>
        cases hu with
        | constantDefinition _ hus =>
        rename_i d
        have hent := WfSig.validEntries hι hd sig hw ((List.suffix_cons _ sig).trans hs)
        have hf := fundamentalIn.hasType (hΓ := Scope.FirstOrder.nil) hd hent hrest
          (ht (.ofLists qs ps hq hp)) (hm ▸ hus (.ofLists qs ps hq hp))
          fun i => (ls.getFin hl i).closedValue
        intro w σ H E V hσ hEV hE
        obtain ⟨a, H', R, hev, hH, hr⟩ := hf w σ H E V hσ hEV hE
        cases (hE : V = [])
        cases E with
        | cons => exact hEV.elim
        | nil =>
        have hσ₀ : ∀ t : Term 0 [], t.subst σ = t := fun t => by
          have h := Term.subst_weakenClosed σ t
          rwa [Term.weakenClosed_nil] at h
        refine ⟨a, H', R, .const (hP.constantDefinition hd (hs.subset hc) hm.symm hq hp) ?_, hH,
          ?_⟩
        · rw [Term.atLevels, Term.erase_substLevels] at hev
          exact hev
        · rw [hσ₀, hσ₀] at hr
          rw [hσ₀, Signature.instanceType, Term.subst_weakenClosed]
          have hred := (Red.delta (Γ := []) (hs.subset hc) hq hl hp).interpret (ι := ι)
          rw [Signature.instanceType, Term.weakenClosed_nil] at hred
          exact (RunsAs.redStar_iff hd (.step hred (.refl _))).2
            ((hr.levelEquiv (Term.substLevels_levelEquiv_atLevels _ _).symm).term_levelEquiv hd
              (Term.substLevels_levelEquiv_atLevels _ _).symm)
      · rename_i d
        have hc'' : Signature.HasConstant sig d.name d.sorts d.levels d.grades .oneOne d.ownership d.type :=
          hm ▸ .constantDefinition hc'
        exact hrest hc'' qs ls ps hq hl hp

/-! ## Judgments in a Signature -/

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- Every term typed and used in the mode `11ᵐ`, in a context whose variables are all of the first
order, is valid at run time at every value of its level variables, in a signature whose entries use
their variables as their grades allow, when the interpretation gives the constant declarations of
the signature terms of their types and the program realizes the signature. -/
structure Fundamental : Prop where
  /-- A typing.
  RFC: `\mathsf{fund}_t` -/
  hasType : ∀ {ι : Interpretation} {P : Program} {sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ctx : Context k Γ} {t A : Term k Γ} {γ : GradeVector Γ.length},
    ValidInterpretation ι sig → ValidProgram ι P sig → UsageSig sig → HasType sig ctx t A →
      Usage sig γ .oneOne t →
        ∀ ρ, RunValid sig ι P hΓ (ctx.atLevels ρ) γ (t.atLevels ρ) (A.atLevels ρ)
  /-- Arguments of a telescope.
  RFC: `\mathsf{fund}_{\bar t}` -/
  hasArgs : ∀ {ι : Interpretation} {P : Program} {sig : Signature} {k : Nat} {Γ : Scope}
    {hΓ : Γ.FirstOrder} {ps : List Parameter} {ctx : Context k Γ} {ts : Args k Γ ps}
    {Θ : Telescope k Γ ps} {γ : GradeVector Γ.length},
    ValidInterpretation ι sig → ValidProgram ι P sig → UsageSig sig → HasArgs sig ctx ts Θ →
      UsageArgs sig γ .oneOne ts →
        ∀ ρ, RunValidArgs sig ι P hΓ (ctx.atLevels ρ) γ (ts.atLevels ρ) (Θ.atLevels ρ)

-- ADE: `fundamental`, in `Graded/Erasure/LogicalRelation/Fundamental.agda`.
/-- The fundamental lemma of the run time: the signature of a judgment is well formed, so that it
gives its own entries their meaning and the program realizes its constants of the mode `11ᵐ`. -/
theorem fundamental : Fundamental where
  hasType hι hP hu h hut :=
    have hw := presuppositions.hasType h
    fundamentalIn.hasType hw.distinct (WfSig.validEntries hι hw.distinct _ hw (List.suffix_refl _))
      (WfSig.realizes hι hw.distinct hP _ hw hu (List.suffix_refl _)) h hut
  hasArgs hι hP hu h hut :=
    have hw := presuppositions.hasArgs h
    fundamentalIn.hasArgs hw.distinct (WfSig.validEntries hι hw.distinct _ hw (List.suffix_refl _))
      (WfSig.realizes hι hw.distinct hP _ hw hu (List.suffix_refl _)) h hut

end Sic.Core
