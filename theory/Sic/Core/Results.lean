module

public import Sic.Core.Lifting
public import Sic.Core.Syntax.Grades

/-!
# Recursive Results

The recursive results of the fields of a constructor, which a branch of a recursor binds after the
fields: a result for each recursive field, of the motive of its type at the field, and one for each
field nested below a codata type, of the type of the field lifted at the field, where each type of
the block has its motive.

The nesting of the fields, which the declaration gives, tells which fields are recursive, which are
nested, and where the types of the block are in the types of the nested ones.
The grades of the recursive results, which the usage of a branch of a recursor reads, are at the
positions of these fields.
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
arguments `as` of the recursor, its motive in `C̄`, without non-uniform parameter, the level `l` of
the sort of the motives, and the ownership `χ` of the results of the recursor. -/
def Lifting.ofMotives {Γ Δ : Scope} (names : List Name) (qs : List Quality) (ls : List (Level k))
    (ps : List Grade) (as : InstanceArgs k Γ Δ) (l : Level k) (χ : Grade) (Cs : Motives k Γ) :
    Lifting k Γ Γ where
  ren := fun x => x
  motive := fun _ => none
  block := fun D =>
    if D ∈ names then
      match Cs.get (names.idxOf D) with
      | some ⟨0, C⟩ => some ⟨.inst D qs ls ps as, C, l, χ⟩
      | _ => none
    else none

/-- A type of the block that the lifting of the scope of a recursor gives a motive has a name of
the block, its instance at the arguments of the recursor and its motive in `C̄`. -/
theorem Lifting.ofMotives_block_inv {Γ Δ : Scope} {names : List Name} {qs : List Quality}
    {ls : List (Level k)} {ps : List Grade} {as : InstanceArgs k Γ Δ} {l : Level k} {χ : Grade}
    {Cs : Motives k Γ} {D : Name} {b : Lifting.BlockMotive k Γ Γ}
    (h : (Lifting.ofMotives names qs ls ps as l χ Cs).block D = some b) :
    D ∈ names ∧ ∃ C, Cs.get (names.idxOf D) = some ⟨0, C⟩ ∧ b = ⟨.inst D qs ls ps as, C, l, χ⟩ := by
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

/-- The types of the entries of a telescope have a type at each position before the number of its
entries, and none from it on: `Terms.get` gives a term exactly below the length of the terms. -/
theorem Telescope.get_types_isSome : {Γ : Scope} → {ps : List Parameter} →
    (Θ : Telescope k Γ ps) → (l : Nat) → (Θ.types.get l).isSome ↔ l < ps.length
  | _, [], .nil, _ => by simp [Telescope.types, Terms.get]
  | _, _ :: _, .cons _ _ _ _, 0 => by simp [Telescope.types, Terms.get]
  | _, _ :: _, .cons _ _ _ Θ, l + 1 => by
    simp only [Telescope.types, Terms.get, List.length_cons, Nat.add_lt_add_iff_right]
    exact Telescope.get_types_isSome Θ l

/-! ## Recursive Results -/

-- ADE: none.
/--
The recursive results `R` of the fields `x̄`, whose types are `Ā`, whose nestings are `ns` and whose
entries have the parameters `ps`, in a signature, where `ρ` gives the types of the block their
motives and `v` the variables of the liftings, with their factors `πs`: a variable `y` for each
field whose nesting has a position, in order, and one factor for each result, in the same order,
which the uses of the result multiply.
-/
inductive Terms.ResultTypes (sig : Signature) (v : Lifting.Variables) :
    {Δ' Δ : Scope} → Lifting k Δ' Δ → List (Nest Name) → List Parameter → Terms k Δ → Terms k Δ →
      {ps' : List Parameter} → Telescope k Δ' ps' → List Grade → Prop where
  /-- No field.
  RFC: `\uparrow_{\Theta\varepsilon}` -/
  | nil {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} : Terms.ResultTypes sig v ρ [] [] .nil .nil .nil []
  /-- A field without position, which has no result.
  RFC: `\uparrow_{\Theta\bot}` -/
  | plain {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {ns : List (Nest Name)} {p : Parameter}
      {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ} {R : Telescope k Δ' ps'}
      {πs : List Grade} (h : Terms.ResultTypes sig v ρ ns ps As xs R πs) :
      Terms.ResultTypes sig v ρ (.plain :: ns) (p :: ps) (.cons A As) (.cons x xs) R πs
  /-- A recursive field `x` of the type `D` of the block: `y : C_D[x / z]`, the motive of `D` at
  the field, with the factor `11ᵖ`, since the recursion is on the field itself.
  RFC: `\uparrow_{\Theta T}` -/
  | recursive {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {D : Name} {ns : List (Nest Name)}
      {p : Parameter} {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ}
      {b : Lifting.BlockMotive k Δ' Δ} {R : Telescope k (.var :: Δ') ps'} {πs : List Grade}
      (hD : ρ.block D = some b) (h : Terms.ResultTypes sig v ρ.weaken ns ps As xs R πs) :
      Terms.ResultTypes sig v ρ (.direct D :: ns) (p :: ps) (.cons A As) (.cons x xs)
        (.cons Grade.zero p (b.motive.subst₀ (Subst₀.single (x.rename ρ.ren))) R)
        (Grade.linearLinear :: πs)
  /-- A nested field `x : A`, whose nesting is that of an instance: `y : A'`, the type `A` lifted
  at the field, with the factor `π` of the lifting.
  RFC: `\uparrow_{\Theta\lambda}` -/
  | nested {Δ' Δ : Scope} {ρ : Lifting k Δ' Δ} {ms ns : List (Nest Name)} {p : Parameter}
      {ps ps' : List Parameter} {A x : Term k Δ} {As xs : Terms k Δ} {A' : Term k Δ'}
      {m : Lifting.Result k} {R : Telescope k (.var :: Δ') ps'} {πs : List Grade}
      (hA : Term.Lifts sig v ρ (.inst ms) (x.rename ρ.ren) A A' m)
      (h : Terms.ResultTypes sig v ρ.weaken ns ps As xs R πs) :
      Terms.ResultTypes sig v ρ (.inst ms :: ns) (p :: ps) (.cons A As) (.cons x xs)
        (.cons Grade.zero p A' R) (m.factor :: πs)

-- ADE: none.
/-- The recursive results `R` of the fields of the constructor `c` at the instance `I`, at the
levels `ls` and at the arguments `ā`, in a block whose types have the names `names`, in the scope
`Γ` extended by its fields, where `ρ` gives the types of the block their motives in `Γ`, with their
factors `πs`, one for each result: the nestings are those of the fields of the declaration, and the
types those of the fields at the instance. -/
def Constructor.ResultTypes {j g k' : Nat} {Δ Γ : Scope} (sig : Signature) (v : Lifting.Variables)
    (c : Constructor j g k' Δ) (I : Instance j g) (names : List Name) (ls : Fin k' → Level k)
    (as : InstanceArgs k Γ Δ) (ρ : Lifting k Γ Γ) {ps' : List Parameter}
    (R : Telescope k (Γ.extend (c.params I).length) ps') (πs : List Grade) : Prop :=
  Terms.ResultTypes sig v (ρ.liftN (c.params I).length) ((c.fields I).nest names) (c.params I)
    (c.fieldsAt I ls as).types (Args.bound (Γ := Γ) (c.params I)).terms R πs

/-- The recursive results have the parameters of the fields whose nestings have a position. -/
theorem Terms.ResultTypes.params_eq {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} → {πs : List Grade} →
      Terms.ResultTypes sig v ρ ns ps As xs R πs → ps' = Telescope.nestResultParams ns ps
  | _, _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, _, _, _, _, .plain h => h.params_eq
  | _, _, _, _, _, _, _, _, _, _, .recursive _ h => congrArg _ h.params_eq
  | _, _, _, _, _, _, _, _, _, _, .nested _ h => congrArg _ h.params_eq

/-- The recursive results have a factor each. -/
theorem Terms.ResultTypes.length_factors {sig : Signature} {v : Lifting.Variables} :
    {Δ' Δ : Scope} → {ρ : Lifting k Δ' Δ} → {ns : List (Nest Name)} → {ps : List Parameter} →
      {As xs : Terms k Δ} → {ps' : List Parameter} → {R : Telescope k Δ' ps'} → {πs : List Grade} →
      Terms.ResultTypes sig v ρ ns ps As xs R πs →
        πs.length = (Telescope.nestResultParams ns ps).length
  | _, _, _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, _, _, _, _, .plain h => h.length_factors
  | _, _, _, _, _, _, _, _, _, _, .recursive _ h => congrArg (· + 1) h.length_factors
  | _, _, _, _, _, _, _, _, _, _, .nested _ h => congrArg (· + 1) h.length_factors

/-! ## Grades of the Recursive Results -/

-- ADE: none.
/-- `e_l`: the grade of the recursive result of the field at each position `l` of the fields whose
nestings are `ns`, the first field at `0`, read from the grades `es` of the recursive results in
order, and `0` for a field without result, whose nesting has no position. -/
def Telescope.resultGrades : List (Nest Name) → List Grade → Nat → Grade
  | .plain :: _, _, 0 => Grade.zero
  | .plain :: ns, es, l + 1 => Telescope.resultGrades ns es l
  | _ :: _, e :: _, 0 => e
  | _ :: ns, _ :: es, l + 1 => Telescope.resultGrades ns es l
  | _, _, _ => Grade.zero

/-- A position has the grade `0`, erased, when no grade of a recursive result is left. -/
theorem Telescope.resultGrades_nil : (ns : List (Nest Name)) → (l : Nat) →
    Telescope.resultGrades ns [] l = Grade.zero
  | [], _ | .direct _ :: _, _ | .inst _ :: _, _ | .plain :: _, 0 => rfl
  | .plain :: ns, l + 1 => Telescope.resultGrades_nil ns l

/-- The grade of the recursive result of the field at the position `o + l`, the `j`-th of the fields
whose nestings `ns` have a position from the position `o`, is the `j`-th grade, `0` when there is
none. -/
theorem Telescope.resultGrades_of_nestPositions : (ns : List (Nest Name)) → (es : List Grade) →
    (o j l : Nat) → (Telescope.nestPositions ns o)[j]? = some (o + l) →
      Telescope.resultGrades ns es l = es.getD j Grade.zero
  | [], _, _, _, _, h => nomatch h
  | .plain :: ns, es, o, j, l, h => by
    rw [Telescope.nestPositions_plain] at h
    cases l with
    | zero => exact absurd (Telescope.le_of_mem_nestPositions (List.mem_of_getElem? h)) (by omega)
    | succ l =>
      rw [show o + (l + 1) = o + 1 + l by omega] at h
      exact Telescope.resultGrades_of_nestPositions ns es (o + 1) j l h
  | .direct _ :: ns, es, o, j, l, h | .inst _ :: ns, es, o, j, l, h => by
    rw [Telescope.nestPositions_cons rfl] at h
    cases j with
    | zero =>
      have hl : l = 0 := by
        have := Option.some.inj h
        omega
      subst hl
      cases es <;> rfl
    | succ j =>
      rw [List.getElem?_cons_succ] at h
      cases l with
      | zero =>
        exact absurd (Telescope.le_of_mem_nestPositions (List.mem_of_getElem? h)) (by omega)
      | succ l =>
        rw [show o + (l + 1) = o + 1 + l by omega] at h
        cases es with
        | nil => exact Telescope.resultGrades_nil _ _
        | cons e es => exact Telescope.resultGrades_of_nestPositions ns es (o + 1) j l h

/-- The grade of the recursive result of the field at the position `l`, the `j`-th field whose
nesting has a position, and that grade times the factor of the result, read from the grades `es`
and the factors `πs` of the results. -/
theorem Telescope.resultGrades_of_index {ns : List (Nest Name)} {es πs : List Grade} {j l : Nat}
    (hj : (Telescope.nestPositions ns 0)[j]? = some l) {e π : Grade} (he : es[j]? = some e)
    (hπ : πs[j]? = some π) :
    Telescope.resultGrades ns es l = e ∧
      Telescope.resultGrades ns (List.zipWith (· * ·) es πs) l = e * π := by
  have hj' : (Telescope.nestPositions ns 0)[j]? = some (0 + l) := by rw [Nat.zero_add]; exact hj
  refine ⟨?_, ?_⟩
  · rw [Telescope.resultGrades_of_nestPositions ns es 0 j l hj', List.getD_eq_getElem?_getD, he]
    rfl
  · rw [Telescope.resultGrades_of_nestPositions ns _ 0 j l hj', List.getD_eq_getElem?_getD,
      List.getElem?_zipWith, he, hπ]
    rfl

-- ADE: `_∙_`, in `Graded/Context.agda`, once for each variable.
/-- `γ • e_{l₁} • … • e_{l_b}`: the vector `γ` extended by the grade `e l` of the recursive result of
each field that has one, at its position `l` in the fields whose entries have the parameters `ps`
and whose nestings are `ns`, the first field at `0`, in order. -/
def _root_.Sic.Grading.GradeVector.extendResults {Γ : Scope} (γ : GradeVector Γ.length)
    (e : Nat → Grade) : (ns : List (Nest Name)) → (ps : List Parameter) →
      GradeVector (Γ.extend (Telescope.nestResultParams ns ps).length).length
  | .plain :: ns, _ :: ps => extendResults γ (fun l => e (l + 1)) ns ps
  | .direct _ :: ns, _ :: ps | .inst _ :: ns, _ :: ps =>
    extendResults (Γ := .var :: Γ) (γ ∙ e 0) (fun l => e (l + 1)) ns ps
  | [], _ | .plain :: _, [] | .direct _ :: _, [] | .inst _ :: _, [] => γ

/-- The extension by the recursive results at the grades `es`, in order, is the extension by the
variables of the telescope of their parameters at these grades. -/
theorem _root_.Sic.Grading.GradeVector.extendResults_resultGrades {Γ : Scope} :
    (γ : GradeVector Γ.length) → (ns : List (Nest Name)) → (ps : List Parameter) →
    (es : List Grade) →
    γ.extendResults (Telescope.resultGrades ns es) ns ps =
      γ.extendGrades (fun l => es.getD l Grade.zero) (Telescope.nestResultParams ns ps)
  | γ, .plain :: ns, _ :: ps, es => extendResults_resultGrades γ ns ps es
  | γ, .direct _ :: ns, _ :: ps, e :: es | γ, .inst _ :: ns, _ :: ps, e :: es =>
    extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ e) ns ps es
  | γ, .direct _ :: ns, _ :: ps, [] | γ, .inst _ :: ns, _ :: ps, [] => by
    have h := extendResults_resultGrades (Γ := .var :: Γ) (γ ∙ Grade.zero) ns ps []
    rw [funext (Telescope.resultGrades_nil ns)] at h
    exact h
  | _, [], _, _ | _, .plain :: _, [], _ | _, .direct _ :: _, [], _
  | _, .inst _ :: _, [], _ => rfl

-- ADE: none.
/-- `e_{l₁} + … + e_{l_b}`: the sum of the grades `e l` of the recursive results of the fields whose
nestings `ns` have a position, at their positions `l`, the first field at `0`. -/
def Telescope.resultSum (e : Nat → Grade) : List (Nest Name) → Grade
  | [] => Grade.zero
  | .plain :: ns => Telescope.resultSum (fun l => e (l + 1)) ns
  | _ :: ns => e 0 + Telescope.resultSum (fun l => e (l + 1)) ns

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
      {qs : List Quality} {ls : List (Level k)} {ms : List (Lifting.Result k)} {ps : List Grade}
      {as : InstanceArgs k Γ decl.scope} {S : List Nat} {as' : InstanceArgs k Γ Δ'}
      {ns : List Name}
      {body : Instance (decl.sorts + 1) (decl.liftingGrades S) →
        Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
      {gs : DestructorBranches k Γ}
      (h : sig.HasCodataType D decl T) (hn : ∀ E, n ≠ .direct E)
      (hq : qs.length = decl.sorts) (hl : ls.length = decl.levels) (hp : ps.length = decl.grades)
      (has : InstanceArgs.Lifts sig v ρ n.args as S ms as') (hS : S ≠ [])
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
        (.corec v.recursion (Lifting.name D S) (qs ++ [v.quality]) (ls ++ ms.map (·.level))
          (v.grades ps ms) (.snoc (e := .var) as' t) .nil
          (.cons 0 .nil [] .nil) gs)

/-- The types of the entries of the telescope `Θ` at the arguments `t̄`, in order: the type of each
entry, at the arguments of the entries before it. -/
def Telescope.typesAt {Γ : Scope} :
    {ps : List Parameter} → Telescope k Γ ps → Args k Γ ps → Terms k Γ
  | [], .nil, .nil => .nil
  | _ :: _, .cons _ _ A Θ, .cons t ts =>
    .cons A (Telescope.typesAt (Θ.subst₀ (Subst₀.single t)) ts)

/-- The types of the entries of a telescope at arguments have a type at each position before the
number of its entries, and none from it on: `Terms.get` gives a term exactly below the length of
the terms. -/
theorem Telescope.get_typesAt_isSome {Γ : Scope} : {ps : List Parameter} →
    (Θ : Telescope k Γ ps) → (ts : Args k Γ ps) → (l : Nat) →
      ((Θ.typesAt ts).get l).isSome ↔ l < ps.length
  | [], .nil, .nil, _ => by simp [Telescope.typesAt, Terms.get]
  | _ :: _, .cons _ _ _ _, .cons _ _, 0 => by simp [Telescope.typesAt, Terms.get]
  | _ :: _, .cons _ _ _ Θ, .cons t ts, l + 1 => by
    simp only [Telescope.typesAt, Terms.get, List.length_cons, Nat.add_lt_add_iff_right]
    exact Telescope.get_typesAt_isSome (Θ.subst₀ (Subst₀.single t)) ts l

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
