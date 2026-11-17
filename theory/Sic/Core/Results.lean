module

public import Sic.Core.Lifting

/-!
# Recursive Results

The recursive results of the fields of a constructor, which a branch of a recursor binds after the
fields: a result for each recursive field, of the motive of its type at the field, and one for each
field nested below a codata type, of the type of the field lifted at the field, where each type of
the block has its motive.

The nesting of the fields, which the declaration gives, tells which fields are recursive, which are
nested, and where the types of the block are in the types of the nested ones.
The results are a relation, as the lifting is: a nested field whose type has no lifting, since the
signature does not declare it, has no result.

The computation of a recursor on a constructor gives these results their terms: the recursor on
the term of a recursive field, and, for the term of a nested field, the corecursor of the lifting of
its type, whose branches are the results of the observations of the term, down to the terms of the
types of the block.
The result of an observation follows the result of its destructor at the arguments of the instance,
which is not a part of the type of the field, so that these terms are a relation by rules too.

The RFC names the variables, so that the type of a field is a type in the context of the fields
and of the results, and writes the result `f(E, t)` of a term of a type of the block for any `f`;
with de Bruijn indices, `f` at a type is a term over a variable, renamed under the arguments of a
destructor, and the types of the fields are renamed in the scope of all
the fields, and the lifting of the block is taken under the fields and weakened under each result.

ADE have no declared types, and no recursive results of this form.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

variable {k : Nat}

/-! ## Block of a Recursor -/

-- ADE: none.
/-- The lifting of the scope of a recursor in itself, which lifts no variable, and the types of the
block whose names are `names`: each has its instance at the variables `qs`, `ls`, `ps` and at the
arguments `as` of the recursor, its motive in `C̄`, without non-uniform parameter, and the level `l`
of the sort of the motives. -/
def Lifting.ofMotives {Γ Δ : Scope} (names : List Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (l : Level k) (Cs : Motives k Γ) :
    Lifting k Γ Γ where
  ren := fun x => x
  motive := fun _ => none
  block := fun D =>
    if D ∈ names then
      match Cs.get (names.idxOf D) with
      | some ⟨0, C⟩ => some ⟨.inst D qs ls ps as, C, l⟩
      | _ => none
    else none

/-- A type of the block that the lifting of the scope of a recursor gives a motive has a name of
the block, its instance at the arguments of the recursor and its motive in `C̄`. -/
theorem Lifting.ofMotives_block_inv {Γ Δ : Scope} {names : List Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {l : Level k}
    {Cs : Motives k Γ} {D : Name} {b : Lifting.BlockMotive k Γ Γ}
    (h : (Lifting.ofMotives names qs ls ps as l Cs).block D = some b) :
    D ∈ names ∧ ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ ∧ b = ⟨.inst D qs ls ps as, C, l⟩ := by
  unfold Lifting.ofMotives at h
  by_cases hD : D ∈ names
  · simp only [hD, ↓reduceIte] at h
    split at h
    · next C hC => exact ⟨hD, C, hC, (Option.some.inj h).symm⟩
    · cases h
  · simp only [hD, ↓reduceIte] at h
    cases h

/-! ## Types of the Fields -/

/-- The types of the entries of the telescope `Θ`, in order, each in the scope of all the
entries. -/
def Telescope.types : {Γ : Scope} → {ps : List Parameter} → Telescope k Γ ps →
    Terms k (Γ.extend ps.length)
  | _, [], .nil => .nil
  | _, _ :: ps, .cons _ _ A Θ => .cons (A.rename (Ren.weakenN (ps.length + 1))) Θ.types

/-! ## Recursive Results -/

/-- The parameters of the recursive results of the fields whose entries have the parameters `ps`,
those of the recursive and of the nested fields, whose nestings `ns` have a position, in order:
each result has the parameter of its field, which no judgment reads. -/
def Telescope.nestResultParams : List (Nest Name) → List Parameter → List Parameter
  | .plain :: ns, _ :: ps => Telescope.nestResultParams ns ps
  | .direct _ :: ns, p :: ps => p :: Telescope.nestResultParams ns ps
  | .inst _ :: ns, p :: ps => p :: Telescope.nestResultParams ns ps
  | [], _ | _ :: _, [] => []

-- ADE: none.
/--
The recursive results `R` of the fields `x̄`, whose types are `Ā`, whose nestings are `ns` and whose
entries have the parameters `ps`, in a signature, where `ρ` gives the types of the block their
motives and `v` the variables of the liftings: a variable `y` for each field whose nesting has a
position, in order.
-/
inductive Terms.ResultTypes (sig : Signature) (v : Lifting.Variables) :
    {Δ' Δ : Scope} → Lifting k Δ' Δ → List (Nest Name) → List Parameter → Terms k Δ → Terms k Δ →
      {ps' : List Parameter} → Telescope k Δ' ps' → Prop where
  /-- No field.
  RFC: `\uparrow_{\Theta\varepsilon}` -/
  | nil {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} : Terms.ResultTypes sig v ρ [] [] .nil .nil .nil
  /-- A field without position, which has no result.
  RFC: `\uparrow_{\Theta\bot}` -/
  | plain {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {ns : List (Nest Name)} {p : Parameter}
      {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ} {R : Telescope k Δ' ps'}
      (h : Terms.ResultTypes sig v ρ ns ps As xs R) :
      Terms.ResultTypes sig v ρ (.plain :: ns) (p :: ps) (.cons A As) (.cons x xs) R
  /-- A recursive field `x` of the type `D` of the block: `y : C_D[x / z]`, the motive of `D` at
  the field.
  RFC: `\uparrow_{\Theta T}` -/
  | recursive {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {D : Name} {ns : List (Nest Name)}
      {p : Parameter} {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ}
      {b : Lifting.BlockMotive k Δ' Δ} {R : Telescope k (.var :: Δ') ps'}
      (hD : ρ.block D = some b) (h : Terms.ResultTypes sig v ρ.weaken ns ps As xs R) :
      Terms.ResultTypes sig v ρ (.direct D :: ns) (p :: ps) (.cons A As) (.cons x xs)
        (.cons Grade.zero p (b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))) R)
  /-- A nested field `x : A`, whose nesting is that of an instance: `y : A'`, the type `A` lifted
  at the field.
  RFC: `\uparrow_{\Theta\lambda}` -/
  | nested {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {ms ns : List (Nest Name)} {p : Parameter}
      {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ} {A' : Term k Δ'}
      {l : Level k} {R : Telescope k (.var :: Δ') ps'}
      (hA : Term.Lifts sig v ρ (.inst ms) (x.rename ρ.ren) A A' l)
      (h : Terms.ResultTypes sig v ρ.weaken ns ps As xs R) :
      Terms.ResultTypes sig v ρ (.inst ms :: ns) (p :: ps) (.cons A As) (.cons x xs)
        (.cons Grade.zero p A' R)

/-- The parameters of the recursive results of the constructor `c` at the instance `I`, in a block
whose types have the names `names`. -/
abbrev Constructor.nestResultParams {j g k' : Nat} {Δ : Scope} (c : Constructor j g k' Δ)
    (I : Instance j g) (names : List Name) : List Parameter :=
  Telescope.nestResultParams ((c.fields I).nest names) (c.params I)

-- ADE: none.
/-- The recursive results `R` of the fields of the constructor `c` at the instance `I`, at the
levels `ls` and at the arguments `ā`, in a block whose types have the names `names`, in the scope
`Γ` extended by its fields, where `ρ` gives the types of the block their motives in `Γ`: the
nestings are those of the fields of the declaration, and the types those of the fields at the
instance. -/
def Constructor.ResultTypes {j g k' : Nat} {Δ Γ : Scope} (sig : Signature) (v : Lifting.Variables)
    (c : Constructor j g k' Δ) (I : Instance j g) (names : List Name) (ls : Fin k' → Level k)
    (as : InstanceArgs k Γ Δ) (ρ : Lifting k Γ Γ) {ps' : List Parameter}
    (R : Telescope k (Γ.extend (c.params I).length) ps') : Prop :=
  Terms.ResultTypes sig v (ρ.liftN (c.params I).length) ((c.fields I).nest names) (c.params I)
    (c.fieldsAt I ls as).types (Args.bound (Γ := Γ) (c.params I)).terms R

/-- The recursive results have the parameters of the fields whose nestings have a position. -/
theorem Terms.ResultTypes.params_eq {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} →
      Terms.ResultTypes sig v ρ ns ps As xs R → ps' = Telescope.nestResultParams ns ps
  | _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, _, _, _, .plain h => h.params_eq
  | _, _, _, _, _, _, _, _, _, .recursive _ h => congrArg _ h.params_eq
  | _, _, _, _, _, _, _, _, _, .nested _ h => congrArg _ h.params_eq

/-! ## Terms of the Recursive Results -/

-- ADE: none.
/--
The recursive result `e` of the term `t` of the type `A`, whose nesting is `n`, in a signature,
where `φ` gives each type `E` of the block the result `z. f(E, z)` of a term `z` of this type, `ρ`
the motives of these types and `v` the variables of the liftings.
The result of a term of a type of the block is `f` at it; the result of a term of an instance of a
codata type is the corecursor without state of the lifting of this instance at the term, which the
signature declares, with a branch for each destructor of the lifting: the result of the
observation of the term by the destructor of the same name, at the variables of its arguments,
whose type is the result of this destructor at the arguments of the instance.
-/
inductive Term.NestedResult (sig : Signature) (v : Lifting.Variables) :
    {Γ : Scope} → Lifting k Γ Γ → (Name → Term k (.var :: Γ)) → Nest Name → Term k Γ → Term k Γ →
      Term k Γ → Prop where
  /-- A term of an instance of a type of the block, at a position that holds this type: `f` at the
  term.
  The position tells that the instance is the one that the motive of the type is over, which a
  well-formed declaration ensures, so the rule does not compare them.
  RFC: `\mathsf{res}_T` -/
  | block {Γ : Scope} {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} {t : Term k Γ}
      {Δ : Scope} {D : Name} {qs : List Quality} {ls : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ Δ} {b : Lifting.BlockMotive k Γ Γ} (hD : ρ.block D = some b) :
      Term.NestedResult sig v ρ φ (.direct D) (.inst D qs ls ps as) t
        ((φ D).subst₀ (Subst₀.single t))
  /-- A term of an instance of a codata type whose nesting is not a position, of which an argument
  at least is lifted: the corecursor of the instance of the lifting of this type, as the lifting of
  the instance at the term gives it, without state, whose branch of each destructor `d` of the
  lifting, at the position `i`, is the result of the observation of the term by the destructor `d`
  of the type, which is one of its destructors, at the position `hd` in the destructors
  `d̄ = (d̄₁ | d : (Θ ⊢ B ◀ ψ) ▶ p; q ◀ ς | d̄₂)` of the type at the instance: the type of this
  observation is `B`, the destructors `d̄₁` before it being the observations of the term by them,
  and its nesting is that of `B`, where the parameters have the nestings of the arguments.
  RFC: `\mathsf{res}_D` -/
  | inst {Γ : Scope} {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} {n : Nest Name}
      {t : Term k Γ} {decl : TypeDeclaration}
      {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {Δ' : Scope} {D : Name}
      {qs : List Quality} {ls ls' : List (Level k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} {S : List Nat} {as' : InstanceArgs k Γ Δ'}
      {ns : List Name}
      {body : Instance (decl.sorts + 1) (decl.grades + 3) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
      {gs : CorecBranches k Γ}
      (h : sig.HasCodataType D decl T) (hn : ∀ E, n ≠ .direct E)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (has : InstanceArgs.Lifts sig v ρ n.args as S ls' as') (hS : S ≠ [])
      (hL : .typeDeclaration (decl.lifting D S ns body) ∈ sig)
      (hgl : gs.length = ns.length)
      (hgs : ∀ i d, ns[i]? = some d →
        ∃ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
          (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length)
          (_ : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) (g : _),
        gs.get i = some ⟨0, 0, ps₁.length, g⟩)
      (hgt : ∀ i d (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope)
        (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
        (ψ : ResultOwnership Grade ps₁.length) (g : Term k (Γ.extend ps₁.length)),
        ns[i]? = some d → (hd : (T.body (.ofLists qs ps hq hp)).Pos d p q ς Ξ Θ B ψ) →
        gs.get i = some ⟨0, 0, ps₁.length, g⟩ →
        Term.NestedResult sig v (ρ.liftN ps₁.length)
          (fun E => (φ E).rename (Ren.lift (Ren.weakenN ps₁.length)))
          (B.nest (fun _ => none) (Nesting.liftN ps₁.length (hd.nesting (Nesting.ofArgs n.args))))
          ((B.substLevels (ls.getFin hl)).subst
            (Subst.liftN _ (hd.obsSubst (t.observation D qs ls ps as) as.toSubst)))
          (t.observation D qs ls ps as d ps₁) g) :
      Term.NestedResult sig v ρ φ n (.inst D qs ls ps as) t
        (.corec v.recursion (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ls')
          (ps ++ [v.recursion, v.requirement, v.ownership]) (.snoc (e := .var) as' t) .nil
          (.cons 0 .nil [] .nil) gs)

/-- The types of the entries of the telescope `Θ` at the arguments `t̄`, in order: the type of each
entry, at the arguments of the entries before it. -/
def Telescope.typesAt {Γ : Scope} :
    {ps : List Parameter} → Telescope k Γ ps → Args k Γ ps → Terms k Γ
  | [], .nil, .nil => .nil
  | _ :: _, .cons _ _ A Θ, .cons t ts =>
    .cons A (Telescope.typesAt (Θ.subst₀ (Subst₀.single t)) ts)

-- ADE: none.
/--
The recursive results `r̄` of the terms `t̄` of fields, whose types are `Ā`, whose nestings are `ns`
and whose entries have the parameters `ps`, in a signature, where `φ` gives each type `E` of the
block the result `z. f(E, z)` of a term of this type: a term for each field whose nesting has a
position, in order, the arguments of the telescope of the recursive results.
-/
inductive Terms.ResultTerms (sig : Signature) (v : Lifting.Variables) {Γ : Scope}
    (ρ : Lifting k Γ Γ) (φ : Name → Term k (.var :: Γ)) :
    List (Nest Name) → List Parameter → Terms k Γ → Terms k Γ → {ps' : List Parameter} →
      Args k Γ ps' → Prop where
  /-- No field.
  RFC: `\mathsf{res}_{\Theta\varepsilon}` -/
  | nil : Terms.ResultTerms sig v ρ φ [] [] .nil .nil .nil
  /-- A field without position, which has no result.
  RFC: `\mathsf{res}_{\Theta\bot}` -/
  | plain {ns : List (Nest Name)} {p : Parameter} {ps ps' : List Parameter} {A t : Term k Γ}
      {As ts : Terms k Γ} {rs : Args k Γ ps'} (h : Terms.ResultTerms sig v ρ φ ns ps As ts rs) :
      Terms.ResultTerms sig v ρ φ (.plain :: ns) (p :: ps) (.cons A As) (.cons t ts) rs
  /-- The term `t` of a recursive field of the type `D` of the block: `f(D, t)`.
  RFC: `\mathsf{res}_{\Theta T}` -/
  | recursive {D : Name} {ns : List (Nest Name)} {p : Parameter} {ps ps' : List Parameter}
      {A t : Term k Γ} {As ts : Terms k Γ} {rs : Args k Γ ps'}
      (h : Terms.ResultTerms sig v ρ φ ns ps As ts rs) :
      Terms.ResultTerms sig v ρ φ (.direct D :: ns) (p :: ps) (.cons A As) (.cons t ts)
        (.cons (p := p) ((φ D).subst₀ (Subst₀.single t)) rs)
  /-- The term `t` of a nested field, whose nesting is that of an instance: its recursive
  result.
  RFC: `\mathsf{res}_{\Theta\lambda}` -/
  | nested {ms ns : List (Nest Name)} {p : Parameter} {ps ps' : List Parameter} {A t e : Term k Γ}
      {As ts : Terms k Γ} {rs : Args k Γ ps'} (he : Term.NestedResult sig v ρ φ (.inst ms) A t e)
      (h : Terms.ResultTerms sig v ρ φ ns ps As ts rs) :
      Terms.ResultTerms sig v ρ φ (.inst ms :: ns) (p :: ps) (.cons A As) (.cons t ts)
        (.cons (p := p) e rs)

-- ADE: none.
/-- The recursive results `r̄` of the terms `t̄` of the fields of the constructor `c` at the
instance `I`, at the levels `ls` and at the arguments `ā`, in a block whose types have the names
`names`: the nestings are those of the fields of the declaration, and the types those of the
fields at the instance and at the terms. -/
def Constructor.ResultTerms {j g k' : Nat} {Δ Γ : Scope} (sig : Signature)
    (v : Lifting.Variables) (c : Constructor j g k' Δ) (I : Instance j g) (names : List Name)
    (ls : Fin k' → Level k) (as : InstanceArgs k Γ Δ) (ρ : Lifting k Γ Γ)
    (φ : Name → Term k (.var :: Γ)) (ts : Args k Γ (c.params I)) {ps' : List Parameter}
    (rs : Args k Γ ps') : Prop :=
  Terms.ResultTerms sig v ρ φ ((c.fields I).nest names) (c.params I)
    ((c.fieldsAt I ls as).typesAt ts) ts.terms rs

/-- The terms of the recursive results have the parameters of the fields whose nestings have a
position. -/
theorem Terms.ResultTerms.params_eq {sig : Signature} {v : Lifting.Variables} {Γ : Scope}
    {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} :
    {ns : List (Nest Name)} → {ps : List Parameter} → {As ts : Terms k Γ} →
      {ps' : List Parameter} → {rs : Args k Γ ps'} → Terms.ResultTerms sig v ρ φ ns ps As ts rs →
        ps' = Telescope.nestResultParams ns ps
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, .plain h => h.params_eq
  | _, _, _, _, _, _, .recursive h => congrArg _ h.params_eq
  | _, _, _, _, _, _, .nested _ h => congrArg _ h.params_eq

/-- The terms of fields whose nestings have no position have no recursive result. -/
theorem Telescope.resultTerms_of_plain {sig : Signature} {v : Lifting.Variables} {k' : Nat}
    {Γ : Scope} {ρ : Lifting k Γ Γ} {φ : Name → Term k (.var :: Γ)} (names : List Name) :
    {Ξ : Scope} → {ps : List Parameter} → (Θ' : Telescope k' Ξ ps) → (Θ : Telescope k Γ ps) →
      (ts : Args k Γ ps) → (∀ ν ∈ Θ'.nest names, ν = .plain) →
        Terms.ResultTerms sig v ρ φ (Θ'.nest names) ps (Θ.typesAt ts) ts.terms .nil
  | _, [], .nil, .nil, .nil, _ => .nil
  | _, _ :: _, .cons _ _ A Θ', .cons _ _ _ Θ, .cons _ ts, h => by
    show Terms.ResultTerms sig v ρ φ (A.blockNest names :: Θ'.nest names) _ (.cons _ _)
      (.cons _ _) .nil
    rw [h (A.blockNest names) List.mem_cons_self]
    exact .plain (Telescope.resultTerms_of_plain names Θ' _ ts
      fun ν hν => h ν (List.mem_cons_of_mem _ hν))

end Sic.Core
