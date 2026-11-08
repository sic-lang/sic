module

public import Sic.Core.Meaning

/-!
# Extension of the Signature

The soundness of the rules `(f)`, `(δ)` and `(f_≡)` reads an entry of the signature, which the
meaning of the signature makes meaningful in the signature before it, the prefix, while the judgment
that uses it is in the whole signature `Σ' ++ Σ`, whose newer entries come first.
A computation of the prefix is a computation of the whole signature, and it is its only one when the
names are distinct, since the reduction is deterministic: the closed judgments of the prefix are
judgments of the whole signature.

The hypothetical judgments do not extend so: they quantify over the equal substitutions of their
context, which the whole signature may give terms that compute only in it; the rules read their
entries in the empty context, where this does not arise.

ADE extend the typed judgments and the typed reductions along a well-formed extension of their
context of definitions, `» ∇′ ⊇ ∇`; the reduction of Sic is untyped, so that it extends along any
extension, and the meaning of the closed judgments along an extension whose names are distinct.
-/

@[expose] public section

namespace Sic.Core

/-! ## Computation -/

-- ADE: `defn-wkNeutral`, in `Definition/Typed/Weakening/Definition.agda`.
/-- A neutral term of `Σ` is a neutral term of `Σ' ++ Σ`. -/
theorem Neutral.weaken {sig : Signature} {k : Nat} {Γ : Scope} {t : Term k Γ}
    (pre : Signature) : Neutral sig t → Neutral (pre ++ sig) t
  | .var x ts => .var x ts
  | .const h => .const (List.mem_append_right pre h)

-- ADE: `defn-wkWhnf`, in `Definition/Typed/Weakening/Definition.agda`.
/-- A head normal form of `Σ` is a head normal form of `Σ' ++ Σ`. -/
theorem Whnf.weaken {sig : Signature} {k : Nat} {Γ : Scope} {t : Term k Γ}
    (pre : Signature) : Whnf sig t → Whnf (pre ++ sig) t
  | .sort κ => .sort κ
  | .inst D qs ls ps as => .inst D qs ls ps as
  | .ne h => .ne (h.weaken pre)

-- ADE: `defn-wkRedTerm`, in `Definition/Typed/Weakening/Definition.agda`.
/-- A step of reduction of `Σ` is a step of reduction of `Σ' ++ Σ`. -/
theorem Red.weaken {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ}
    (pre : Signature) : Red sig t u → Red (pre ++ sig) t u
  | .delta h hq hl hp => .delta (List.mem_append_right pre h) hq hl hp

-- ADE: `defn-wkRed*Term`, in `Definition/Typed/Weakening/Definition.agda`.
/-- A reduction of `Σ` is a reduction of `Σ' ++ Σ`. -/
theorem RedStar.weaken {sig : Signature} {k : Nat} {Γ : Scope} {t u : Term k Γ}
    (pre : Signature) : RedStar sig t u → RedStar (pre ++ sig) t u
  | .refl t => .refl t
  | .step h hs => .step (h.weaken pre) (hs.weaken pre)

-- ADE: none.
/-- A computation of `Σ` is a computation of `Σ' ++ Σ`. -/
theorem Computes.weaken {sig : Signature} {t v : Term 0 []} (pre : Signature)
    (h : Computes sig t v) : Computes (pre ++ sig) t v :=
  ⟨h.1.weaken pre, h.2.weaken pre⟩

/-- Interpreting the constants of `Σ' ++ Σ` interprets those of `Σ'` and of `Σ`. -/
theorem Signature.interpret_append (ι : Interpretation) (pre sig : Signature) :
    (pre ++ sig).interpret ι = pre.interpret ι ++ sig.interpret ι :=
  List.map_append

-- ADE: none.
/-- A computation of `Σ` in the meaning is a computation of `Σ' ++ Σ`. -/
theorem Computesι.weaken {sig : Signature} {ι : Interpretation} {t v : Term 0 []}
    (pre : Signature) (h : Computesι sig ι t v) : Computesι (pre ++ sig) ι t v := by
  unfold Computesι
  rw [Signature.interpret_append]
  exact Computes.weaken _ h

-- ADE: none.
/-- A closed type that computes in `Σ` computes to a proposition in `Σ' ++ Σ` exactly when it does
in `Σ`, when the names of `Σ' ++ Σ` are distinct. -/
theorem ComputesToProp.weaken_iff {pre sig : Signature} {ι : Interpretation} {A v : Term 0 []}
    (hd : (pre ++ sig).Distinct) (hA : Computesι sig ι A v) :
    ComputesToProp (pre ++ sig) ι A ↔ ComputesToProp sig ι A := by
  constructor
  · rintro ⟨A₁, h₁, hp⟩
    cases Computes.det hd.interpret h₁ (hA.weaken pre)
    exact ⟨_, hA, hp⟩
  · rintro ⟨A₁, h₁, hp⟩
    exact ⟨A₁, h₁.weaken pre, hp⟩

/-! ## Closed Judgments -/

-- ADE: none.
/-- The clause of `(⊨_type≡)` in `Σ` holds in `Σ' ++ Σ`. -/
theorem EqTypeClause.weaken {sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    (pre : Signature) : EqTypeClause sig ι A B → EqTypeClause (pre ++ sig) ι A B
  | ⟨A₀, B₀, R, hA, hB, hA₀, hB₀⟩ => ⟨A₀, B₀, R, hA.weaken pre, hB.weaken pre, hA₀, hB₀⟩

-- ADE: none.
/-- The clauses of `(⊨_≡)` and `(⊨_≡Ω)` in `Σ` hold in `Σ' ++ Σ`, for a type that computes in `Σ`,
when the names of `Σ' ++ Σ` are distinct. -/
theorem EqTermClause.weaken {pre sig : Signature} {ι : Interpretation} {t u A v : Term 0 []}
    (hd : (pre ++ sig).Distinct) (hA : Computesι sig ι A v) (h : EqTermClause sig ι t u A) :
    EqTermClause (pre ++ sig) ι t u A := by
  refine ⟨fun hn => ?_, fun hp => ?_⟩
  · obtain ⟨A₁, v, w, R, h₁, ht, hu, hR, hvw⟩ :=
      h.1 (fun hp => hn ((ComputesToProp.weaken_iff hd hA).2 hp))
    exact ⟨A₁, v, w, R, h₁.weaken pre, ht.weaken pre, hu.weaken pre, hR, hvw⟩
  · obtain ⟨A₁, R, h₁, hR, htu⟩ := h.2 ((ComputesToProp.weaken_iff hd hA).1 hp)
    exact ⟨A₁, R, h₁.weaken pre, hR, htu⟩

-- ADE: none.
/-- `Σ ⊨ A ≡ B` implies `Σ' ++ Σ ⊨ A ≡ B` when `Σ' ++ Σ` is meaningful. -/
theorem ValidEqType₀.weaken {pre sig : Signature} {ι : Interpretation} {A B : Term 0 []}
    (hsig : ValidSig ι (pre ++ sig)) (h : ValidEqType₀ sig ι A B) :
    ValidEqType₀ (pre ++ sig) ι A B :=
  ⟨hsig, h.2.weaken pre⟩

-- ADE: none.
/-- `Σ ⊨ A` implies `Σ' ++ Σ ⊨ A` when `Σ' ++ Σ` is meaningful. -/
theorem ValidType₀.weaken {pre sig : Signature} {ι : Interpretation} {A : Term 0 []}
    (hsig : ValidSig ι (pre ++ sig)) (h : ValidType₀ sig ι A) : ValidType₀ (pre ++ sig) ι A :=
  ValidEqType₀.weaken hsig h

-- ADE: none.
/-- `Σ ⊨ t ≡ u : A` implies `Σ' ++ Σ ⊨ t ≡ u : A` when `Σ' ++ Σ` is meaningful. -/
theorem ValidEqTerm₀.weaken {pre sig : Signature} {ι : Interpretation} {t u A : Term 0 []}
    (hsig : ValidSig ι (pre ++ sig)) (h : ValidEqTerm₀ sig ι t u A) :
    ValidEqTerm₀ (pre ++ sig) ι t u A := by
  obtain ⟨A₀, -, -, hA, -⟩ := h.1.2
  exact ⟨ValidType₀.weaken hsig h.1, h.2.weaken hsig.distinct hA⟩

-- ADE: none.
/-- `Σ ⊨ t : A` implies `Σ' ++ Σ ⊨ t : A` when `Σ' ++ Σ` is meaningful. -/
theorem ValidTerm₀.weaken {pre sig : Signature} {ι : Interpretation} {t A : Term 0 []}
    (hsig : ValidSig ι (pre ++ sig)) (h : ValidTerm₀ sig ι t A) : ValidTerm₀ (pre ++ sig) ι t A :=
  ValidEqTerm₀.weaken hsig h


/-! ## Constants of a Meaningful Signature -/

-- ADE: none.
/-- The signature that a meaningful signature extends is meaningful. -/
theorem ValidSig.drop {ι : Interpretation} :
    (pre : Signature) → {sig : Signature} → ValidSig ι (pre ++ sig) → ValidSig ι sig
  | [], _, h => h
  | .typeDeclaration _ :: _, _, h => by simp only [List.cons_append, ValidSig] at h
  | .constantDefinition _ :: pre, _, h => ValidSig.drop pre h.1
  | .constantDeclaration _ :: pre, _, h => ValidSig.drop pre h.1

-- ADE: none.
/-- A constant of a meaningful signature unfolds, once the constants are interpreted, to a body that
is a term of its type at each instance of its sort and grade variables and each value of its level
variables: the body of a definition, or the interpretation of a declaration. -/
theorem ValidSig.hasConstant {ι : Interpretation} {sig : Signature} (hsig : ValidSig ι sig)
    {f : Name} {j k' g : Nat} {m : Mode} {p : Grade} {A : Instance j g → Term k' []} :
    sig.HasConstant f j k' g m p A →
      ∃ b : Instance j g → Term k' [],
        (∀ (qs : List Quality) (ls : List (Level 0)) (ps : List Grade) (hq : qs.length = j)
            (hl : ls.length = k') (hp : ps.length = g),
          Red (sig.interpret ι) (Term.const (Γ := []) f qs ls ps)
            (Signature.instanceType b (.ofLists qs ps hq hp) (ls.getFin hl))) ∧
        ∀ inst ρ, ValidTerm₀ sig ι ((b inst).atLevels ρ) ((A inst).atLevels ρ)
  | .constantDefinition (d := d) hd => by
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hd
    have hpre : pre ++ .constantDefinition d :: post = (pre ++ [.constantDefinition d]) ++ post :=
      by simp
    refine ⟨d.body, fun _ _ _ hq hl hp =>
      .delta (List.mem_map_of_mem (f := Entry.interpret ι) hd) hq hl hp, fun inst ρ => ?_⟩
    rw [hpre] at hsig ⊢
    exact ValidTerm₀.weaken hsig (ValidConstantDefinition.iff.1
      (ValidSig.constantDefinition_iff.1 (ValidSig.drop pre (by simpa using hsig))).1 inst ρ)
  | .constantDeclaration (c := c) hc => by
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
    have hpre : pre ++ .constantDeclaration c :: post = (pre ++ [.constantDeclaration c]) ++ post :=
      by simp
    refine ⟨ι c, fun _ _ _ hq hl hp =>
      .delta (d := ⟨c.name, c.sorts, c.levels, c.grades, c.mode, c.ownership, c.type, ι c⟩)
        (List.mem_map_of_mem (f := Entry.interpret ι) hc) hq hl hp, fun inst ρ => ?_⟩
    rw [hpre] at hsig ⊢
    exact ValidTerm₀.weaken hsig (ValidConstantDeclaration.iff.1
      (ValidSig.constantDeclaration_iff.1 (ValidSig.drop pre (by simpa using hsig))).1 inst ρ)


-- ADE: none.
/-- A meaningful signature of the core has no declared type, since the kinds of declarations give the
meaning of their type declarations. -/
theorem ValidSig.not_hasDeclaredType {ι : Interpretation} {sig : Signature} (hsig : ValidSig ι sig)
    {D : Name} {decl : TypeDeclaration} : ¬ sig.HasDeclaredType D decl := fun ⟨hd, _⟩ => by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hd
  have h := ValidSig.drop pre hsig
  simp only [ValidSig] at h

end Sic.Core
