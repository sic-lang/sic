module

public import Sic.Core.Meaning

/-!
# Meaning of the Judgments

The meaning of the judgments of annex 18 of RFC 36 unfolded: the meaning of an entry of the signature
by its clauses, that of a context by its last entry, and the fields and the destructors of a
meaningful type declaration.

ADE have no type declarations, and their contexts have no second-order variables.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Closed Judgments

The clauses of the closed judgments are stated without the meaning `⊨ Σ` of their signature, which
they require, so that the meaning of the signatures is defined from them. -/

/-- `(⊨def)`, as the RFC states it: at each instance of the sort and grade variables and each value
of the level variables, the body is a term of the type; the names of the signature are then
distinct, since an instance exists whatever the numbers of the variables.
RFC: `{\vDash}\mathsf{def}` -/
theorem ValidConstantDefinition.iff {sig : Signature} {ι : Interpretation} {d : ConstantDefinition} :
    ValidConstantDefinition sig ι d ↔
      ∀ inst (ρ : Fin d.levels → Nat),
        ValidTerm₀ sig ι ((d.body inst).atLevels ρ) ((d.type inst).atLevels ρ) :=
  ⟨fun ⟨hd, hc⟩ inst ρ => ⟨⟨hd, (hc inst ρ).1⟩, (hc inst ρ).2⟩,
    fun h => ⟨(h ⟨fun _ => .type, fun _ => .zero⟩ fun _ => 0).1.1,
      fun inst ρ => ⟨(h inst ρ).1.2, (h inst ρ).2⟩⟩⟩

/-- `(⊨decl)`, as the RFC states it: at each instance of the sort and grade variables and each value
of the level variables, the interpretation of the constant is a term of its type.
RFC: `{\vDash}\mathsf{decl}` -/
theorem ValidConstantDeclaration.iff {sig : Signature} {ι : Interpretation}
    {c : ConstantDeclaration} :
    ValidConstantDeclaration sig ι c ↔
      ∀ inst (ρ : Fin c.levels → Nat),
        ValidTerm₀ sig ι ((ι c inst).atLevels ρ) ((c.type inst).atLevels ρ) :=
  ⟨fun ⟨hd, hc⟩ inst ρ => ⟨⟨hd, (hc inst ρ).1⟩, (hc inst ρ).2⟩,
    fun h => ⟨(h ⟨fun _ => .type, fun _ => .zero⟩ fun _ => 0).1.1,
      fun inst ρ => ⟨(h inst ρ).1.2, (h inst ρ).2⟩⟩⟩

/-! ## Hypothetical Judgments -/

/-- `(⊨ctx_x)`, as the RFC states it.
RFC: `{\vDash}\mathsf{ctx}_x` -/
theorem validCtx₀_var {sig : Signature} {ι : Interpretation} {Γ : Scope} (ctx : Context 0 Γ)
    (A : Term 0 Γ) : ValidCtx₀ sig ι (ctx.var A) ↔ ValidTypeΓ sig ι ctx A := by
  rw [ValidCtx₀]; rfl

/-- `(⊨ctx_X)`, as the RFC states it.
RFC: `{\vDash}\mathsf{ctx}_X` -/
theorem validCtx₀_secondOrder {sig : Signature} {ι : Interpretation} {Γ : Scope}
    {ps : List Parameter} (ctx : Context 0 Γ) (Θ : Telescope 0 Γ ps) (A : Term 0 (Γ.extend ps.length))
    (ψ : ResultOwnership Grade ps.length) : ValidCtx₀ sig ι (ctx.secondOrder Θ A ψ) ↔ ValidTypeΓ sig ι (ctx.append Θ) A := by
  rw [ValidCtx₀]; rfl

/-! ## Destructors of a Block -/

/-- The destructors after a destructor that is not recursive are equal for every pair of
abstractions for it whose instances at equal arguments are equal terms of its result, whether its
result has a position or not: the two clauses of the destructors that are not recursive are read as
one, by what does not read the nestings. -/
theorem ValidEqDestructors₀.cons_inv {sig : Signature} {ι : Interpretation} {κ : Universe 0}
    {Γ : Scope} {d : Name} {ns : List Name} {ps : List Parameter} {p q ς : Grade}
    {Θ : Telescope 0 Γ ps} {B : Term 0 (Γ.extend ps.length)} {ψ : ResultOwnership Grade ps.length}
    {ds : Destructors 0 (.secondOrder ps ψ :: Γ) ns} {inst : Name → Term 0 Γ}
    {rs : Nat → Option Name} {nested : Nat → Bool} {θ₁ θ₂ : Subst 0 [] Γ}
    (h : ValidEqDestructors₀ sig ι κ inst rs nested (.cons (d := d) p q ς Θ B ψ ds) θ₁ θ₂) :
    ValidEqTelescope₀ sig ι ⟨.type, κ.level⟩ (Θ.subst θ₁) (Θ.subst θ₂) ∧
    match rs 0 with
    | none =>
      (∃ κ₁, κ₁ ≼ κ ∧ ∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
        ValidEqTerm₀ sig ι (B.subst (Subst.append θ₁ τ₁)) (B.subst (Subst.append θ₂ τ₂))
          (.sort κ₁)) ∧
      ∀ f₁ f₂, (∀ τ₁ τ₂, EqSubst sig ι (Context.empty.append (Θ.subst θ₁)) τ₁ τ₂ →
          ValidEqTerm₀ sig ι (f₁.subst τ₁) (f₂.subst τ₂) (B.subst (Subst.append θ₁ τ₁))) →
        ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken) (fun i => rs (i + 1))
          (fun i => nested (i + 1)) ds
          (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂)
    | some D => B = (inst D).rename (Ren.weakenN ps.length) ∧
      ∀ f₁ f₂, ValidEqDestructors₀ sig ι κ (fun D => (inst D).rename Ren.weaken)
        (fun i => rs (i + 1)) (fun i => nested (i + 1)) ds
        (Subst.snoc (e := .secondOrder ps ψ) θ₁ f₁) (Subst.snoc (e := .secondOrder ps ψ) θ₂ f₂) := by
  rw [ValidEqDestructors₀] at h
  obtain ⟨hΘ, h⟩ := h
  refine ⟨hΘ, ?_⟩
  cases hr : rs 0 with
  | none =>
    rw [hr] at h
    cases hn : nested 0 with
    | false =>
      rw [hn] at h
      exact h
    | true =>
      rw [hn] at h
      exact ⟨h.1, fun f₁ f₂ _ => h.2 f₁ f₂⟩
  | some D =>
    rw [hr] at h
    exact h

/-! ## Signatures and Entries -/

/-- The fields of the constructors of a data type of a meaningful type declaration are fields in its
sort, at each instance that its constraint admits. -/
theorem ValidTypeDeclaration.fields {sig : Signature} {ι : Interpretation} {decl : TypeDeclaration}
    (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    (hadm : decl.constraint I) {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : T ∈ decl.dataTypes)
    {c : Constructor decl.sorts decl.grades decl.levels decl.scope} (hc : c ∈ T.constructors) :
    ValidFields sig ι (decl.params I) decl.names
      (fun D => decl.blockInstance I D (.identity decl.scope)) ((c.fields I).nestAt decl.names)
      (c.fields I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.dataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact h I hadm T hT c hc
  · exact nomatch hT

/-- The destructors of a codata type of a meaningful type declaration are in its sort, with the types
of the block at the parameters themselves as the results of the recursive ones, at each instance
that its constraint admits. -/
theorem ValidTypeDeclaration.destructors {sig : Signature} {ι : Interpretation}
    {decl : TypeDeclaration} (h : ValidTypeDeclaration sig ι decl) (I : Instance decl.sorts decl.grades)
    (hadm : decl.constraint I) {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hT : T ∈ decl.codataTypes) :
    ValidDestructors sig ι (decl.params I) (fun D => decl.blockInstance I D (.identity decl.scope))
      ((T.body I).recursionAt decl.names) ((T.body I).nestedAt (Nesting.ofPositive T.positive))
      (T.body I) (decl.sort I) := by
  unfold ValidTypeDeclaration at h
  unfold TypeDeclaration.codataTypes at hT
  split at h <;> rename_i heq <;> rw [heq] at hT
  · exact nomatch hT
  · exact h I hadm T hT

end Sic.Core
