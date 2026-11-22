module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Ownership
public import Sic.Grading.GradeSet
import Sic.Core.Ownership.Signature
import Sic.Core.RunTime.Ownership.Nested
import Sic.Core.Shape.Results.Fields
import Sic.Core.Syntax.Signature

/-!
# Ownership of the Erasure

The preservation of the ownership by the erasure of annex 19 of RFC 36: the erasure at run time of
a term checked in the mode `11ᵐ` has, in the ownership of the target language, the run-time
multiplicity of its ownership, given the run-time multiplicities of the ownerships of its variables
and of its constants.
The erasure keeps the positions that the mode `11ᵐ` checks in the mode `11ᵐ` again, and their
requirements, and replaces the others with `↯`, which has every ownership; the run-time
multiplicity keeps the product and the meet of the grades, so that the coefficients that the
erasure stores give the run-time multiplicities of the ownerships of the variables of the
branches, and the value of the ownership of the result of a destructor, which reads only the
ownerships of the arguments checked in the mode of the observation, is kept.
A recursor whose block has nested fields gives each nested result the ownership `1` of a new value,
and checks its branches a second time, at the requirement `ς` of the lifted destructors and the
ownership `χ`, as the target does; the shape of each nested result has these ownerships, and, when
the recursor runs a recursion through it, meets the requirements of the recursions and keeps the
ownership of the term, since the premise `hused` of the rule of the recursor makes the field used
at run time, so that the requirement of the recursion reads its pairs.
A block without nested field checks its branches a second time as the first.
ADE have no such property: their erasure keeps no ownership.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

/-! ## Values of the Ownerships of Results -/

/-- The value at run time of the ownership of a result, read at ownerships at run time that agree
with the run-time multiplicities of `os` on the arguments that have a factor, is the run-time
multiplicity of its value at `os`. -/
theorem ResultOwnership.value_map_run : {n : Nat} → (ψ : ResultOwnership Grade n) →
    (os : List Grade) → (os' : List Multiplicity) → os'.length = os.length →
    (∀ i : Fin n, (ψ.coefficient i).isSome → os'[(i : Nat)]? = os[(i : Nat)]?.map Grade.run) →
    (ψ.map Grade.run).value os' = (ψ.value os).map Grade.run
  | 0, ψ, _, _, _, _ => by cases ψ; rfl
  | _ + 1, ψ, [], [], _, _ => by cases ψ; rfl
  | _ + 1, _, [], _ :: _, hl, _ => nomatch hl
  | _ + 1, _, _ :: _, [], hl, _ => nomatch hl
  | n + 1, ψ, o :: os, o' :: os', hl, h => by
    have ih := ResultOwnership.value_map_run ψ.tail os os' (Nat.succ.inj hl)
      fun i hi => by simpa using h i.succ hi
    simp only [ResultOwnership.value]
    have et : (ψ.map Grade.run).tail = ψ.tail.map Grade.run := rfl
    rw [et, ih]
    have e0 : ((ψ.map Grade.run).coefficient 0).map (o' * ·) =
        ((ψ.coefficient 0).map (o * ·)).map Grade.run := by
      cases hc : ψ.coefficient 0 with
      | none => simp [ResultOwnership.map, hc]
      | some χ =>
        have ho : o' = o.run := by simpa using h 0 (by simp [hc])
        simp [ResultOwnership.map, hc, ho, (Grade.run_op _ _).2.1]
    rw [e0]
    cases (ψ.coefficient 0).map (o * ·) <;> cases ψ.tail.value os <;>
      simp [Option.merge, (Grade.run_op _ _).2.2.1]

/-! ## Extensions of the Ownerships of the Variables -/

-- ADE: none.
/-- The ownerships `φ` of the variables of the scope `Γ`, extended by the ownership `v l` of the new
variable of index `l` of `n` new variables, the first one at `0`. -/
def Ownership.extendWith {Γ : Scope} (φ : Var Γ .var → Grade) (v : Nat → Grade) :
    (n : Nat) → Var (Γ.extend n) .var → Grade
  | 0 => φ
  | n + 1 => Ownership.extendWith (Γ := .var :: Γ) (fun | .zero => v 0 | .succ x => φ x)
      (fun l => v (l + 1)) n

/-- The ownerships at run time `φ'` of the positions of a scope of first-order variables are the
run-time multiplicities of the ownerships `φ` of its variables. -/
def Ownership.RunAgree {Γ : Scope} (φ' : MultiplicityVector Γ.length)
    (φ : Var Γ .var → Grade) : Prop :=
  ∀ x : Var Γ .var, φ' x.toFin = (φ x).run

/-- A vector of ownerships at run time that gives each of `n` new variables the run-time
multiplicity of its ownership, the first one at the deepest index, and each old variable its own,
agrees with the ownerships extended alike. -/
theorem Ownership.RunAgree.extendWith {Γ : Scope} {φ : Var Γ .var → Grade}
    {φ' : MultiplicityVector Γ.length} (hφ : Ownership.RunAgree φ' φ) :
    (n : Nat) → (v : Nat → Grade) → (ψ' : MultiplicityVector (Γ.extend n).length) →
    (∀ i : Fin (Γ.extend n).length, (h : (i : Nat) < n) → ψ' i = (v (n - 1 - i)).run) →
    (∀ i : Fin (Γ.extend n).length, (h : n ≤ (i : Nat)) →
      ψ' i = φ' ⟨i - n, by have := Scope.length_extend Γ n; omega⟩) →
    Ownership.RunAgree ψ' (Ownership.extendWith φ v n)
  | 0, v, ψ', _, hold => fun x => by
    rw [hold x.toFin (Nat.zero_le _)]
    exact hφ x
  | n + 1, v, ψ', hnew, hold => by
    have hl₁ := Scope.length_extend Γ (n + 1)
    have hl₂ := Scope.length_extend (.var :: Γ) n
    let φ₁ : MultiplicityVector (Scope.Entry.var :: Γ).length := fun i =>
      if h : (i : Nat) = 0 then (v 0).run else
        φ' ⟨i - 1, by have := i.2; simp only [List.length_cons] at this; omega⟩
    have h₁ : Ownership.RunAgree (Γ := .var :: Γ) φ₁
        (fun | .zero => v 0 | .succ x => φ x) := fun x => by
      cases x with
      | zero => simp [φ₁, Var.toFin]
      | succ x =>
        simp only [φ₁, Var.toFin, Fin.val_succ]
        rw [dite_eq_right_of_eq_false (by simp), ← hφ x]
        congr 1
    refine Ownership.RunAgree.extendWith h₁ n (fun l => v (l + 1)) ψ'
      (fun i h => by rw [hnew i (by omega)]; congr 2; omega) (fun i h => ?_)
    by_cases he : (i : Nat) = n
    · rw [hnew i (by omega)]
      have : (⟨i - n, by have := Scope.length_extend (.var :: Γ) n; omega⟩ :
          Fin (Scope.Entry.var :: Γ).length) = 0 := Fin.ext (by simp; omega)
      rw [this]
      simp only [φ₁, Fin.val_zero, ↓reduceDIte]
      congr 2
      omega
    · rw [hold i (by omega)]
      simp only [φ₁]
      rw [dite_eq_right_of_eq_false (by simp; omega)]
      congr 1

/-- The ownerships extended by the variables of a telescope, each at the requirement of its entry
times a grade, are extended by their values in order. -/
theorem Ownership.extendFields_eq {Γ : Scope} (φ : Var Γ .var → Grade) (o g : Grade) :
    (ps : List Parameter) → Ownership.extendFields φ o g ps = Ownership.extendWith φ
      (fun l => ((ps[l]?).map fun p => (o * p.requirement) * (g * p.usage)).getD .zero) ps.length
  | [] => rfl
  | p :: ps => by
    rw [Ownership.extendFields, Ownership.extendFields_eq _ o g ps]
    simp only [List.length_cons, Ownership.extendWith, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rfl

/-- The ownerships extended by `n` recursive results, each at its ownership times its grade, are
extended by their values in order. -/
theorem Ownership.extendResults_eq {Γ : Scope} (φ : Var Γ .var → Grade) :
    (os es : List Grade) → (n : Nat) → Ownership.extendResults φ os es n =
      Ownership.extendWith φ (fun l => os.getD l .unrestrictedUnrestricted * es.getD l .zero) n
  | _, _, 0 => rfl
  | os, es, n + 1 => by
    rw [Ownership.extendResults, Ownership.extendResults_eq _ os.tail es.tail n,
      Ownership.extendWith]
    cases os <;> cases es <;> rfl

-- ADE: none.
/-- The ownership of the value of the `j`-th recursive result of the fields whose nestings are `ns`,
in a branch of a recursor of the ownership `p`, has the run-time multiplicity of the ownership that
the erasure gives the variable of the `j`-th recursive result of these fields from the position `o`
in a branch of the ownership `run(p)`, when `f` gives each recursive field a type of the block and
`s` each nested field a shape: `p` for the recursor on a recursive field, and `1` for the
corecursor of a nested field, a new value. -/
theorem Telescope.resultOwnerships_getD {p d : Grade} {f : Nat → Option Name}
    {s : Nat → Option Shape} :
    (ns : List (Nest Name)) → (ps : List Parameter) → ns.length = ps.length → (o : Nat) →
    (∀ i D, ns[i]? = some (.direct D) → (f (o + i)).isSome) →
    (∀ i ms, ns[i]? = some (.inst ms) → f (o + i) = none ∧ (s (o + i)).isSome) →
    ∀ j, j < (Telescope.nestResultParams ns ps).length →
      ((Telescope.resultOwnerships p ns).getD j d).run =
        ((((Telescope.nestPositions ns o).map fun l =>
          RecursiveResult.ofField (f l) (s l) l)[j]?).getD .erased).ownership p.run
  | [], [], _, _, _, _, _, h => nomatch h
  | _ :: _, [], hl, _, _, _, _, _ => nomatch hl
  | .plain :: ns, _ :: ps, hl, o, hf, hs, j, h => by
    rw [Telescope.nestPositions_plain]
    exact Telescope.resultOwnerships_getD ns ps (Nat.succ.inj hl) (o + 1)
      (fun i D h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D h)
      (fun i ms h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hs (i + 1) ms h) j h
  | .direct D :: ns, _ :: ps, hl, o, hf, hs, j, h => by
    rw [Telescope.nestPositions_cons rfl, List.map_cons]
    cases j with
    | zero =>
      obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.1 (hf 0 D rfl)
      rw [Nat.add_zero] at hD'
      simp only [List.getElem?_cons_zero, Option.getD_some, RecursiveResult.ofField, hD']
      rfl
    | succ j =>
      exact Telescope.resultOwnerships_getD ns ps (Nat.succ.inj hl) (o + 1)
        (fun i D h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D h)
        (fun i ms h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hs (i + 1) ms h) j
        (Nat.lt_of_succ_lt_succ h)
  | .inst ms :: ns, _ :: ps, hl, o, hf, hs, j, h => by
    rw [Telescope.nestPositions_cons rfl, List.map_cons]
    cases j with
    | zero =>
      obtain ⟨hn, hσ⟩ := hs 0 ms rfl
      obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hσ
      rw [Nat.add_zero] at hn hσ
      simp only [List.getElem?_cons_zero, Option.getD_some, RecursiveResult.ofField, hn, hσ]
      rfl
    | succ j =>
      exact Telescope.resultOwnerships_getD ns ps (Nat.succ.inj hl) (o + 1)
        (fun i D h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hf (i + 1) D h)
        (fun i ms h => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hs (i + 1) ms h) j
        (Nat.lt_of_succ_lt_succ h)

/-- The ownerships extended by the variables of the arguments of a telescope, each at its ownership
times a grade, are extended by their values in order. -/
theorem Ownership.extendArgs_eq {Γ : Scope} (φ : Var Γ .var → Grade) (g : Grade) :
    (ps : List Parameter) → (os : List Grade) → Ownership.extendArgs φ g ps os =
      Ownership.extendWith φ (fun l => ((ps[l]?).map fun p =>
        os.getD l .unrestrictedUnrestricted * (g * p.usage)).getD .zero) ps.length
  | [], _ => rfl
  | p :: ps, os => by
    rw [Ownership.extendArgs, Ownership.extendArgs_eq _ g ps os.tail]
    simp only [List.length_cons, Ownership.extendWith, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    cases os <;> rfl

/-- The ownerships at run time extended by the binders of a branch of the target language agree,
transported to the scope of the branch, with the ownerships extended by the variables of the branch,
when the new ones agree. -/
theorem Ownership.RunAgree.extendBinders {Γ : Scope} {φ : Var Γ .var → Grade}
    {φ' : MultiplicityVector Γ.length} (hφ : Ownership.RunAgree φ' φ) {a b : Nat}
    (v₁ v₂ : Nat → Grade) (w₁ : Fin a → Multiplicity) (w₂ : Fin b → Multiplicity)
    (h₁ : ∀ l, w₁ l = (v₁ l).run) (h₂ : ∀ l, w₂ l = (v₂ l).run) :
    Ownership.RunAgree
      (fun i => φ'.extendBinders w₁ w₂ (i.cast (Scope.length_extend_extend Γ a b)))
      (Ownership.extendWith (Ownership.extendWith φ v₁ a) v₂ b) := by
  have ha := Scope.length_extend Γ a
  have hb := Scope.length_extend (Γ.extend a) b
  refine Ownership.RunAgree.extendWith
    (φ' := fun i => if h : (i : Nat) < a then (v₁ (a - 1 - i)).run else
      φ' ⟨i - a, by omega⟩)
    (Ownership.RunAgree.extendWith hφ a v₁ _ (fun i h => by simp [h])
      (fun i h => by simp [show ¬(i : Nat) < a by omega])) b v₂ _
    (fun i h => ?_) (fun i h => ?_)
  · simp only [MultiplicityVector.extendBinders, Fin.val_cast, h, ↓reduceDIte, h₂]
  · simp only [MultiplicityVector.extendBinders, Fin.val_cast, show ¬(i : Nat) < b by omega,
      ↓reduceDIte]
    by_cases h' : (i : Nat) - b < a
    · simp only [show (i : Nat) < a + b by omega, ↓reduceDIte, h', h₁]
    · simp only [show ¬(i : Nat) < a + b by omega, ↓reduceDIte, h']
      congr 1
      exact Fin.ext (by simp only; omega)

/-! ## Transports -/

/-- A term of the target language transported along an equality of sizes keeps its ownership, given
the ownerships of the variables transported back. -/
theorem Target.Ownership.cast {Ω : Name → Multiplicity} {n n' : Nat} (h : n = n')
    {φ : MultiplicityVector n'} {o : Multiplicity} {M : Target n}
    (hM : Target.Ownership Ω (fun i => φ (i.cast h)) o M) : Target.Ownership Ω φ o (h ▸ M) := by
  subst h
  exact hM

/-! ## Erasure -/

/-- The erasure of the branches of a recursor whose term has the ownership `o` has the ownership `o'`
when the recursive results of each branch are those of `ws` and the erasure of each branch has it,
given the ownership `o` times the coefficient of each variable of a field and the ownership of each
recursive result times its multiplicity, `o'` for a result of the recursor and `1` for a nested
result, has the ownership `χ` with the scope at `ς · φ'` and the results of the recursor at `χ`, and
the shape of each nested result has the ownerships `ς` and `χ`, and, when the multiplicity of the
recursor times its factor is not `0`, meets the requirements of the recursions at `o`, and the
variable of its field, seen at `ς`, keeps `o`. -/
theorem Branches.erase_ownership {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {Ω : Name → Multiplicity} {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder) (r : Grade)
    (φ' : MultiplicityVector Γ.length) (o o' ς χ : Multiplicity) :
    (us : Branches k Γ) → (ws : List (List RecursiveResult)) → (fs : List (List Parameter)) →
    (∀ i a b (gs : _root_.Vector Grade b) (u : Term k ((Γ.extend a).extend b)),
      us.get i = some ⟨a, b, u⟩ → us.grades i = gs.toList →
      Target.Ownership Ω (φ'.extendBinders
          (fun l => o * r.fieldCoefficient ((fs.drop i).headD [])[(l : Nat)]?)
          (fun (j : Fin b) => (if gs[j] ∈ S then RecursiveResult.erased
            else (((ws.drop i).headD [])[(j : Nat)]?).getD .erased).ownership o' * gs[j].run)) o'
        (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b)) ∧
      Target.Ownership Ω (MultiplicityVector.extendBinders (ς ·ᶜ φ')
          (fun l => o * r.fieldCoefficient ((fs.drop i).headD [])[(l : Nat)]?)
          (fun (j : Fin b) => (if gs[j] ∈ S then RecursiveResult.erased
            else (((ws.drop i).headD [])[(j : Nat)]?).getD .erased).ownership χ * gs[j].run)) χ
        (Scope.length_extend_extend Γ a b ▸ u.erase sig S ((hΓ.extend a).extend b)) ∧
      ∀ (j : Fin b) (l : Fin a) (σ : Shape), gs[j] ∉ S →
        ((ws.drop i).headD [])[(j : Nat)]? = some (.nested l σ) →
        σ.Uniform ς χ ∧ (r.run * σ.factor ≠ .zero → σ.Requires o ς ∧
          o ≤ ς * (o * r.fieldCoefficient ((fs.drop i).headD [])[(l : Nat)]?))) →
    TargetBranches.Ownership Ω φ' r.run o o' ς χ (us.erase sig S hΓ r ws fs)
  | .nil, _, _, _ => .nil
  | .cons a b gs u us, ws, fs, h => by
    obtain ⟨hu, hu', hks⟩ := h 0 a b gs u rfl rfl
    simp only [List.drop_zero] at hu hu' hks
    have ih := Branches.erase_ownership hΓ r φ' o o' ς χ us ws.tail fs.tail
      fun i a' b' gs' u' hg hgs => by
        have e₁ : ws.drop (i + 1) = ws.tail.drop i := by cases ws <;> simp
        have e₂ : fs.drop (i + 1) = fs.tail.drop i := by cases fs <;> simp
        have := h (i + 1) a' b' gs' u' hg hgs
        rwa [e₁, e₂] at this
    refine .cons hu hu' (fun j l σ hj => ?_) ih
    change (if gs[j] ∈ S then RecursiveResult.erased else _) = _ at hj
    split at hj
    · cases hj
    · rename_i hS
      refine hks j l σ hS ?_
      cases hw : (ws.headD [])[(j : Nat)]? with
      | none => rw [hw] at hj; cases hj
      | some w => rw [hw] at hj; cases hj; rfl

/-- A grade with a use at run time, times a recursor whose multiplicity times a factor is not `0`,
in the mode `11ᵐ`, times this factor, is not `0`: the multiplicities have no divisors of `0`. -/
theorem _root_.Sic.Grading.Grade.oneOne_mul_run_ne_zero :
    ∀ (r e : Grade) (c : Multiplicity), r.run * c ≠ .zero → e.run ≠ .zero →
      (Mode.oneOne.grade * r * e).run * c ≠ .zero := by
  decide

/-- The grade of the mode `11ᵐ` is `1`. -/
theorem Mode.oneOne_grade : Mode.oneOne.grade = Grade.one := rfl

/-- The coefficient of the variable of a field, times the ownership of the term, is the run-time
multiplicity of the ownership of the variable in the mode `11ᵐ`, the term of a recursor of a grade
without use at run time having the ownership `1`. -/
theorem Multiplicity.mul_fieldCoefficient :
    ∀ o q c u : Multiplicity, o * (q * (c * u)) = o * q * (Multiplicity.one * c * u) := by
  decide

/-- The variable of a field of the term of a recursor of a grade without use at run time has the
ownership `0` at run time, whatever the ownership of the term and the requirement of the recursion,
`ω` at run time. -/
theorem Multiplicity.mul_fieldCoefficient_zero :
    ∀ o r q u : Multiplicity, Multiplicity.one * .omega * (q * (.zero * u)) =
      o * r * q * (Multiplicity.one * .zero * u) := by
  decide

/-- The erasure of the branches of a corecursor has its ownership when each branch, without
non-uniform parameters and with a grade, has, for all the ownerships of its arguments that satisfy
their requirements, the ownership of the result of its destructor at them, or `1` when it resumes the
corecursor, given the requirement of its destructor on the observed value times that of each entry of
the state and times the ownership of each variable of the scope, and when the ownership of the result
of the destructor of each branch that resumes the corecursor is a constant. -/
theorem DestructorBranches.erase_ownership {sig : Signature} {S : Set Grade} [DecidablePred (· ∈ S)]
    {Ω : Name → Multiplicity} {k : Nat} {Γ : Scope} (hΓ : Γ.FirstOrder)
    (φ' : MultiplicityVector Γ.length) :
    (vs : DestructorBranches k Γ) → (ps : List Grade) → (ks : List Resumption) →
    (pss : List (List Parameter × Σ ps : List Parameter, ResultOwnership Grade ps.length × Grade)) →
    (∀ i, i < vs.length → ∃ (b c : Nat) (v : Term k ((Γ.extend b).extend c)) (p : Grade),
      vs.get i = some ⟨0, b, c, v⟩ ∧ ps[i]? = some p ∧
      (∀ (os : Fin c → Multiplicity) (w : Multiplicity),
        (∀ l : Fin c, ((((pss.drop i).headD ([], ResultOwnership.noArguments)).2.1[(l : Nat)]?).map
          (·.requirement.run)).getD .omega ≤ os l) →
        ((ks.drop i).headD .none = .none ∧
            (((((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.1.toArity c).map
              Grade.run).value (List.ofFn os) = some w) ∨
          (ks.drop i).headD .none ≠ .none ∧ w = .one) →
        Target.Ownership Ω (MultiplicityVector.extendBinders
              (((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.2.run ·ᶜ φ')
            (fun (l : Fin b) =>
              ((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.2.run *
              ((((pss.drop i).headD ([], ResultOwnership.noArguments)).1[(l : Nat)]?).map
                (·.requirement.run)).getD .omega *
              ((((pss.drop i).headD ([], ResultOwnership.noArguments)).1[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)
            (fun (l : Fin c) => os l *
              ((((pss.drop i).headD ([], ResultOwnership.noArguments)).2.1[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)) w
          (if p ∈ S then .erased else
            Scope.length_extend_extend Γ b c ▸ v.erase sig S ((hΓ.extend b).extend c))) ∧
      ((ks.drop i).headD .none ≠ .none → ∃ χ,
        ((((pss.drop i).headD ([], ResultOwnership.noArguments)).2.2.1.toArity c).map
          Grade.run) = ⟨some χ, fun _ => none⟩)) →
    TargetCorecBranches.Ownership Ω φ' (vs.erase sig S hΓ ps ks pss)
  | .nil, _, _, _, _ => .nil
  | .cons n b c v vs, ps, ks, pss, h => by
    obtain ⟨b', c', v', p, hg, hp, hP⟩ := h 0 (Nat.zero_lt_succ _)
    simp only [DestructorBranches.get, Option.some.injEq] at hg
    have hn : n = 0 := by
      have := congrArg Sigma.fst hg
      simp only at this
      omega
    subst hn
    cases hg
    cases ps with
    | nil => nomatch hp
    | cons p' ps =>
      cases hp
      simp only [List.drop_zero] at hP
      refine .cons (fun os w hr hk => hP.1 os w hr hk) hP.2
        (DestructorBranches.erase_ownership hΓ φ' vs ps ks.tail pss.tail fun i hi => ?_)
      obtain ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, hP₁⟩ := h (i + 1) (Nat.succ_lt_succ hi)
      have e₁ : ks.drop (i + 1) = ks.tail.drop i := by cases ks <;> simp
      have e₂ : pss.drop (i + 1) = pss.tail.drop i := by cases pss <;> simp
      rw [e₁, e₂] at hP₁
      exact ⟨b₁, c₁, v₁, p₁, hg₁, hp₁, hP₁⟩

/-- A multiplicity above the run-time multiplicity of a grade is the run-time multiplicity of a grade
above it. -/
theorem Grade.exists_run_above :
    ∀ (r : Grade) (o : Multiplicity), r.run ≤ o → ∃ g : Grade, g.run = o ∧ r ≤ g := by
  decide

/-- Ownerships at run time above the run-time multiplicities of the requirements of the entries of a
telescope are those of ownerships that satisfy these requirements, in every mode. -/
theorem Parameter.exists_allow (m : Mode) : (ps : List Parameter) → (os : List Multiplicity) →
    os.length = ps.length →
    (∀ (i : Nat) (q : Parameter) (o : Multiplicity), ps[i]? = some q → os[i]? = some o →
      q.requirement.run ≤ o) →
    ∃ gs : List Grade, Parameter.Allow m ps gs ∧ gs.map Grade.run = os
  | [], [], _, _ => ⟨[], trivial, rfl⟩
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | q :: ps, o :: os, hl, h => by
    obtain ⟨g, hg, hr⟩ : ∃ g : Grade, g.run = o ∧ q.requirement ≤ g :=
      Grade.exists_run_above _ _ (h 0 q o rfl rfl)
    obtain ⟨gs, ha, hm⟩ := Parameter.exists_allow m ps os (Nat.succ.inj hl)
      fun i q' o' hq ho => h (i + 1) q' o' hq ho
    exact ⟨g :: gs, ⟨fun _ => hr, ha⟩, by simp [hg, hm]⟩

/-- The variable of an entry of the state of a corecursor has the run-time multiplicity of its
ownership in a branch checked in the mode `11ᵐ`. -/
theorem Multiplicity.mul_stateCoefficient :
    ∀ x q c u : Multiplicity, x * q * (Multiplicity.one * c * u) =
      x * q * (Multiplicity.one * (c * u)) := by
  decide

/-- Parameters rebuilt from their grades and their requirements are themselves. -/
theorem Parameter.map_eta (ps : List Parameter) :
    ps.map (fun q => (⟨id q.usage, q.requirement⟩ : Parameter)) = ps := by
  induction ps <;> simp_all

/-- `11ᵐ` checks in `11ᵐ` each argument whose grade has a use at run time. -/
theorem Mode.oneOne_odot_of_not_erased {m : Mode} (hm : m = .oneOne) (u : Grade)
    (hu : id u ∉ Mode.oneOne.erased) : m ⊙ u = .oneOne :=
  hm ▸ (Mode.erasesUncounted .oneOne).mode _ hu

/-- A grade that the mode `11ᵐ` checks in the mode `11ᵐ` has a use at run time. -/
theorem Mode.not_erased_of_odot {m : Mode} {u : Grade} (hm : m = .oneOne) (h : m ⊙ u = m) :
    u ∉ Mode.oneOne.erased :=
  fun hS => hS (hm ▸ h)

mutual

-- ADE: none.
/--
The erasure at run time of a term checked in the mode `11ᵐ` has, in the ownership of the target
language, the run-time multiplicity of its ownership, given the run-time multiplicities `φ'` of the
ownerships `φ` of its variables and those `Ω` of the ownerships of the constants, in a signature
whose names are distinct, so that the ownership and the erasure read the parameters of the fields,
of the arguments and of the branches in the same declaration, and whose entries have their
ownerships, so that the result of each recursive destructor has a constant ownership; the mode is a premise `m = 11ᵐ`, so
that the positions of the term, which the ownership checks in the mode `m ⊙ p`, are checked by the
same theorem.
RFC: `\mathsf{erase}_{◀}`
-/
theorem Ownership.erase_ownership {sig : Signature} (hd : sig.Distinct)
    (hs : OwnershipSig sig)
    {Ω : Name → Multiplicity}
    (hΩ : ∀ f j k' g m p A, sig.HasConstant f j k' g m p A → Ω f = p.run) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {φ : Var Γ .var → Grade} {φ' : MultiplicityVector Γ.length}
    (hφ : Ownership.RunAgree φ' φ) {m : Mode} {p : Grade} {t : Term k Γ} (hm : m = .oneOne) :
    Ownership sig φ m p t → Target.Ownership Ω φ' p.run (t.erase sig Mode.oneOne.erased hΓ)
  | .var (x := y) => by
    simp only [Term.erase]
    rw [← hφ y]
    exact .var _
  | .secondOrder (X := X) .. => nomatch hΓ _ X.mem
  | .const h => by
    simp only [Term.erase]
    rw [← hΩ _ _ _ _ _ _ _ h]
    exact .const _ _ _
  | .sort => .erased _
  | .inst => .erased _
  | .ctor (con := con) h hc hq hp hts => by
    obtain ⟨i, hi⟩ := Signature.constructorCase_of_mem h.1 h.2.1 hc
    rw [h.2.2] at hi
    simp only [Term.erase, hi, hd.fieldParams h hc hq hp, Option.getD_some]
    obtain ⟨_, hos, -⟩ := OwnershipArgs.erase_ownership_map hd hs hΩ hΓ hφ id
      (Mode.oneOne_odot_of_not_erased hm) hts
    rw [Parameter.map_eta] at hos
    exact .ctor hos
  | .recursor (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (ς := ς) (χ := χ) (κ := κ)
      (us := us) (o := o) (p := p) h hq hp ht hns hul hus hu hu' hmeets hused => by
    -- The branches, whose variables have the run-time multiplicities of their ownerships.
    have hbr : ∀ o',
        (r ∉ Mode.oneOne.erased →
          o' = o.run * (sig.recursionRequirement D qs ps ⟨κ.quality, r, ς⟩ χ).run) →
        (r ∈ Mode.oneOne.erased → o' = .one * .omega) →
        ∃ ς' χ', TargetBranches.Ownership Ω φ' r.run o' p.run ς' χ'
          (us.erase sig Mode.oneOne.erased hΓ r (sig.recursiveResults D qs ps ⟨κ.quality, r, ς⟩ χ)
            ((sig.caseFieldParams D qs ps).getD [])) := by
      intro o' ho₁ ho₂
      rw [hd.recursionRequirement_eq h hq hp] at ho₁
      rw [hd.recursiveResults h hq hp, hd.caseFieldParams h hq hp, Option.getD_some]
      rw [hm] at hns hmeets hused
      -- The case of each branch.
      have hcase : ∀ i a b (u : Term k ((Γ.extend a).extend b)), us.get i = some ⟨a, b, u⟩ →
          ∃ j T' con u', decl.cases[i]? = some (j, T', con) ∧
          us.get i = some ⟨(con.params (.ofLists qs ps hq hp)).length,
            (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length, u'⟩ ∧
          ((decl.cases.map fun x => x.2.2.params (.ofLists qs ps hq hp)).drop i).headD [] =
            con.params (.ofLists qs ps hq hp) ∧
          ((decl.recursiveResults sig ⟨κ.quality, r, ς⟩ qs ps χ (.ofLists qs ps hq hp)).drop
            i).headD [] =
            con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ
              (.ofLists qs ps hq hp) := by
        intro i a b u hget
        have hi : i < decl.cases.length := hul ▸ Branches.lt_length_of_get hget
        obtain ⟨⟨j, T', con⟩, hc⟩ : ∃ c, decl.cases[i]? = some c :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨u', hu'⟩ := hus i j T' con hc
        exact ⟨j, T', con, u', hc, hu',
          List.headD_drop (by simp [hc]),
          List.headD_drop (by simp [TypeDeclaration.recursiveResults, hc])⟩
      -- The run-time multiplicities of the ownerships of the variables of a branch, at the
      -- ownerships `φ₀` of the scope and `c` of the results of the recursor.
      have hagree : ∀ i j T' con (gs' : _root_.Vector Grade
            (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length)
          (φ₀ : Var Γ .var → Grade) (φ₀' : MultiplicityVector Γ.length) (c : Grade),
          decl.cases[i]? = some (j, T', con) → us.grades i = gs'.toList →
          Ownership.RunAgree φ₀' φ₀ →
          Ownership.RunAgree
            (fun x => φ₀'.extendBinders
              (fun l => o' * r.fieldCoefficient (con.params (.ofLists qs ps hq hp))[(l : Nat)]?)
              (fun j => (if gs'[j] ∈ Mode.oneOne.erased then RecursiveResult.erased
                else ((con.recursiveResults sig ⟨κ.quality, r, ς⟩ decl.names qs ps χ
                  (.ofLists qs ps hq hp))[(j : Nat)]?).getD .erased).ownership c.run *
                  gs'[j].run)
              (x.cast (Scope.length_extend_extend Γ _ _)))
            (Ownership.extendResults (Ownership.extendFields φ₀
              (o * decl.recursionRequirement sig ⟨κ.quality, r, ς⟩ m χ qs ps
                (.ofLists qs ps hq hp))
              (m.grade * r) (con.params (.ofLists qs ps hq hp)))
              (Telescope.resultOwnerships c ((con.fields (.ofLists qs ps hq hp)).nest decl.names))
              (us.grades i) (con.nestResultParams (.ofLists qs ps hq hp) decl.names).length) := by
        intro i j T' con gs' φ₀ φ₀' c hc hgs' hφ₀
        rw [Ownership.extendResults_eq, Ownership.extendFields_eq]
        refine Ownership.RunAgree.extendBinders hφ₀ _ _ _ _ (fun l => ?_) (fun l => ?_)
        · -- The variable of a field.
          simp only [List.getElem?_eq_getElem l.2, Option.map_some, Option.getD_some,
            Grade.fieldCoefficient, (Grade.run_op _ _).2.1, hm, Mode.oneOne_grade]
          by_cases hr : r ∈ Mode.oneOne.erased
          · rw [ho₂ hr, (Mode.erased_values.1 r).1 hr]
            exact Multiplicity.mul_fieldCoefficient_zero _ _ _ _
          · rw [ho₁ hr]
            exact Multiplicity.mul_fieldCoefficient _ _ _ _
        · -- The variable of a recursive result: of the ownership `c` for a result of the
          -- recursor, and `1` for a nested result, a new value.
          rw [hgs', (Grade.run_op _ _).2.1, List.getD_eq_getElem?_getD (l := gs'.toList),
            List.getElem?_eq_getElem (l := gs'.toList) (i := l)
              (by rw [_root_.Vector.length_toList]; exact l.2),
            Option.getD_some, _root_.Vector.getElem_toList]
          split
          · rename_i hS
            have hz : gs'[l].run = .zero := (Mode.erased_values.1 _).1 hS
            show _ * gs'[l].run = _ * gs'[l].run
            rw [hz]
            exact (Multiplicity.modality.semiring.mul_zero _).trans
              (Multiplicity.modality.semiring.mul_zero _).symm
          · congr 1
            rw [Constructor.recursiveResults_eq_map]
            refine (Telescope.resultOwnerships_getD (p := c) (d := .unrestrictedUnrestricted)
              (f := (con.fields (.ofLists qs ps hq hp)).recursionAt decl.names)
              (s := fun l => (con.nestedShapes sig ⟨κ.quality, r, ς⟩ .oneOne Grade.run decl.names
                qs ps χ (.ofLists qs ps hq hp))[l]?.join) _ _
              (Telescope.length_nest decl.names (con.fields (.ofLists qs ps hq hp))) 0
              (fun i' D hD => ?_) (fun i' ms hms => ⟨?_, ?_⟩) l l.2).symm
            · rw [Nat.zero_add, Telescope.recursionAt, Telescope.recursion_eq_map_nest,
                List.getElem?_map, hD]
              rfl
            · rw [Nat.zero_add, Telescope.recursionAt, Telescope.recursion_eq_map_nest,
                List.getElem?_map, hms]
              rfl
            · obtain ⟨σ, hσ⟩ := hns i j T' con hc Grade.run List.mem_cons_self i' ms hms
              rw [Nat.zero_add, hσ]
              rfl
      rcases decl.hasNestedField_or_not (.ofLists qs ps hq hp) with hN | hN
      · -- A block with a nested field: the second check, at `ς · φ` and the ownership `χ`.
        refine ⟨ς.run, χ.run, Branches.erase_ownership hΓ r φ' o' p.run ς.run χ.run us _ _
          fun i a b gs' u hget hgs' => ?_⟩
        obtain ⟨j, T', con, u', hc, hu'', hfs, hws⟩ := hcase i a b u hget
        cases Option.some.inj (hget.symm.trans hu'')
        rw [hfs, hws]
        refine ⟨Target.Ownership.cast _ (Ownership.erase_ownership hd hs hΩ
            ((hΓ.extend _).extend _) (hagree i j T' con gs' φ φ' p hc hgs' hφ) hm
            (hu i j T' con u' hc hget)),
          Target.Ownership.cast _ (Ownership.erase_ownership hd hs hΩ ((hΓ.extend _).extend _)
            (hagree i j T' con gs' (fun x => ς * φ x) (ς.run ·ᶜ φ') χ hc hgs'
              (fun x => by
                show ς.run * φ' x.toFin = _
                rw [hφ x, (Grade.run_op _ _).2.1])) hm
            (hu' hN i j T' con u' hc hget)), fun j' l σ hS hj => ?_⟩
        obtain ⟨-, hσ⟩ := Constructor.inst_of_recursiveResults_eq_nested hj
        refine ⟨Constructor.nestedShapes_uniform hσ, fun hg => ?_⟩
        -- The guard: the recursor runs a recursion through the shape, so that the branch uses the
        -- result, and so the field, at run time.
        have hr : r ∉ Mode.oneOne.erased := fun hr => by
          rw [(Mode.erased_values.1 r).1 hr] at hg
          exact hg rfl
        obtain ⟨p', hp'⟩ : ∃ p', (con.params (.ofLists qs ps hq hp))[(l : Nat)]? = some p' :=
          ⟨_, List.getElem?_eq_getElem l.2⟩
        have hidx : (Telescope.nestPositions ((con.fields (.ofLists qs ps hq hp)).nest decl.names)
            0)[(j' : Nat)]? = some (0 + (l : Nat)) := by
          rw [Constructor.getElem?_recursiveResults] at hj
          obtain ⟨l', hl', he⟩ := Option.map_eq_some_iff.1 hj
          obtain ⟨hll, -⟩ := RecursiveResult.ofField_eq_nested.1 he
          rw [Nat.zero_add, hll]
          exact hl'
        have he := Telescope.resultGrades_of_nestPositions _ (us.grades i) 0 j' l hidx
        rw [hgs', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp),
          Option.getD_some, _root_.Vector.getElem_toList] at he
        have hc' := hused i j T' con hc l σ p' hσ hp'
          (by
            rw [hgs', he]
            exact Grade.oneOne_mul_run_ne_zero r gs'[j'] σ.factor hg
              (fun h0 => hS ((Mode.erased_values.1 _).2 h0)))
        rw [ho₁ hr, hp', ← (Grade.run_op _ _).2.1]
        exact ⟨Ownership.nestedField_requires hc hσ hp' hc' o
            (hmeets i j T' con hc Grade.run List.mem_cons_self l σ hσ),
          Ownership.nestedField_keeps hc hσ hp' hc' o⟩
      · -- A block without nested field: the second check is the first, at `1 · φ` and `p`.
        refine ⟨.one, p.run, Branches.erase_ownership hΓ r φ' o' p.run .one p.run us _ _
          fun i a b gs' u hget hgs' => ?_⟩
        obtain ⟨j, T', con, u', hc, hu'', hfs, hws⟩ := hcase i a b u hget
        cases Option.some.inj (hget.symm.trans hu'')
        rw [hfs, hws]
        have hN₀ := Target.Ownership.cast _ (Ownership.erase_ownership hd hs hΩ
          ((hΓ.extend _).extend _) (hagree i j T' con gs' φ φ' p hc hgs' hφ) hm
          (hu i j T' con u' hc hget))
        refine ⟨hN₀, ?_, fun j' l σ _ hj => ?_⟩
        · rw [(MultiplicityVector.module Multiplicity.modality).one_smul]
          exact hN₀
        · obtain ⟨⟨ms, hms⟩, -⟩ := Constructor.inst_of_recursiveResults_eq_nested hj
          exact absurd ⟨i, j, T', con, hc, ms, List.mem_of_getElem? hms⟩ hN
    simp only [Term.erase]
    by_cases hr : r ∈ Mode.oneOne.erased
    · simp only [hr, ↓reduceIte]
      obtain ⟨_, _, hNs⟩ := hbr _ (fun h' => absurd hr h') fun _ => rfl
      exact .recursor (sig.skeleton _ _ _).ownership hNs
    · simp only [hr, ↓reduceIte]
      have hm' : m ⊙ r = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hr
      obtain ⟨_, _, hNs⟩ := hbr _ (fun _ => rfl) fun h' => absurd h' hr
      exact .recursor (Ownership.erase_ownership hd hs hΩ hΓ hφ hm' ht) hNs
  | .obs (ψ := ψ) (os := os) h hq hp hpos ht hbs hv hf hς => by
    obtain ⟨i, hi⟩ := Signature.destructorCase_of_mem h.1 h.2.1 hpos.mem
    rw [h.2.2] at hi
    simp only [Term.erase, hi]
    generalize hA : sig.argumentParams _ _ _ _ = A
    rw [hd.argumentParams h hq hp hpos] at hA
    subst hA
    simp only [Option.getD_some]
    obtain ⟨os', hos, hl, ha⟩ := OwnershipArgs.erase_ownership_map hd hs hΩ hΓ hφ id
      (Mode.oneOne_odot_of_not_erased hm) hbs
    rw [Parameter.map_eta] at hos
    rw [(Grade.run_op _ _).2.1]
    refine .obs (Ownership.erase_ownership hd hs hΩ hΓ hφ hm ht) hos ?_ (Grade.run_le hς)
    rw [ResultOwnership.value_map_run ψ os os' hl fun i hi => ha i _
      (List.getElem?_eq_getElem i.2) (Mode.not_erased_of_odot hm (hf i hi)), hv]
    rfl
  | .corec (D := D) (decl := decl) (qs := qs) (ps := ps) (r := r) (Ss := Ss) (gs := vs)
      h hq hp hh hS hss _ hSs hgl hgs hgo hgr => by
    simp only [Term.erase, hd.position h hh, Option.bind_some, hS, Option.elim]
    obtain ⟨_, hos, -⟩ := OwnershipArgs.erase_ownership_map hd hs hΩ hΓ hφ (r * ·)
      (fun u hu => by rw [hm]; exact Mode.oneOne_odot_mul _ _ hu) hss
    refine .corec hos (DestructorBranches.erase_ownership hΓ φ' vs _ _ _ fun i hi => ?_)
    -- The branch of the destructor of the case `i`.
    obtain ⟨j, T', d, ps'', S', p, q, ς, ps₁, Ξ, Θ, B, ψ, g, hc, hSj, ⟨hpos⟩, hg, hpg, hargs,
      hres⟩ := hd.corecCase h hq hp hSs hgl hgs hi
    have hT' := (TypeDeclaration.mem_casesFrom (List.mem_of_getElem? hc)).1
    refine ⟨ps''.length, ps₁.length, g, p, hg, hpg, ?_⟩
    rw [List.headD_drop_map hargs, List.headD_drop_map hres]
    simp only [hSj]
    refine ⟨?_, fun hk => ?_⟩
    rotate_left
    · -- A branch that resumes the corecursor: its destructor is recursive, of a constant result.
      have hbn : B.blockName decl.names ≠ none := fun hbn => hk (by
        simp [hbn, Resumption.ofArity])
      obtain ⟨χ, hχ⟩ := hs.recursiveResult h.1 _ hT' hpos hbn
      refine ⟨χ.run, ?_⟩
      rw [ResultOwnership.toArity_self, hχ]
      rfl
    intro os w hreq hk
    rw [ResultOwnership.toArity_self] at hk
    by_cases hpS : p ∈ Mode.oneOne.erased
    · simp only [hpS, ↓reduceIte]
      exact .erased w
    simp only [hpS, ↓reduceIte]
    have hm' : m ⊙ p = .oneOne := hm ▸ (Mode.erasesUncounted .oneOne).mode _ hpS
    have hgp := Mode.grade_odot_of_not_erased p hpS
    -- Ownerships of the arguments that satisfy their requirements.
    obtain ⟨gs, hal, hgs⟩ := Parameter.exists_allow (m ⊙ p) ps₁ (List.ofFn os)
      (by simp) fun l q' o hq' ho => by
        obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.1 ho
        have := hreq ⟨l, by simpa using hl⟩
        simpa [hq'] using this
    have hgl' : gs.length = ps₁.length := by
      have := congrArg List.length hgs
      simpa using this
    -- The ownerships of the variables of the branch.
    have hag : ∀ (v : Nat → Grade), (∀ l, v l = ((ps₁[l]?).map fun q' =>
          gs.getD l .unrestrictedUnrestricted * ((m ⊙ p).grade * q'.usage)).getD
            .zero) →
        Ownership.RunAgree
          (fun x => MultiplicityVector.extendBinders (ς.run ·ᶜ φ')
            (fun (l : Fin ps''.length) => ς.run *
              (((ps''.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(l : Nat)]?).map
                (·.requirement.run)).getD .omega *
              (((ps''.map fun p => (⟨r * p.usage, p.requirement⟩ : Parameter))[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega)
            (fun (l : Fin ps₁.length) => os l *
              (((ps₁[(l : Nat)]?).map
                fun q => ((Mode.oneOne ⊙ p).grade * q.usage).run).getD .omega))
            (x.cast (Scope.length_extend_extend Γ _ _)))
          (Ownership.extendArgs (Ownership.extendFields (fun x => ς * φ x) ς
            ((m ⊙ p).grade * r) ps'') (m ⊙ p).grade ps₁ gs) := by
      intro v hv
      rw [Ownership.extendArgs_eq, Ownership.extendFields_eq, hm]
      refine Ownership.RunAgree.extendBinders (fun x => by
        show ς.run * φ' x.toFin = _
        rw [hφ x, (Grade.run_op _ _).2.1]) _ _ _ _ (fun l => ?_) (fun l => ?_)
      · simp only [List.getElem?_map, List.getElem?_eq_getElem l.2, Option.map_some,
          Option.getD_some, hgp, (Grade.run_op _ _).2.1]
        exact (Multiplicity.mul_stateCoefficient _ _ _ _).symm
      · simp only [List.getElem?_eq_getElem l.2, Option.map_some, Option.getD_some,
          (Grade.run_op _ _).2.1]
        congr 1
        have e : (gs.map Grade.run)[(l : Nat)]? = (List.ofFn os)[(l : Nat)]? := by rw [hgs]
        simp [List.getElem?_eq_getElem (show (l : Nat) < gs.length by omega)] at e
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact e.symm
    cases hbn : B.blockName decl.names with
    | none =>
      -- The result of the destructor, at the ownerships of the arguments.
      have hk0 : Resumption.ofArity (decide (r ∈ Mode.oneOne.erased))
          (((B.blockName decl.names).bind decl.names.idxOf?).bind Ss.arity) = .none := by
        simp [hbn, Resumption.ofArity]
      rcases hk with ⟨-, hw⟩ | ⟨hne, -⟩
      · rw [ResultOwnership.value_map_run ψ gs (List.ofFn os) (by simp [hgl'])
          (fun l _ => by
            have := congrArg (·[(l : Nat)]?) hgs
            simpa using this.symm)] at hw
        obtain ⟨val, hval, rfl⟩ := Option.map_eq_some_iff.1 hw
        exact Target.Ownership.cast _ (Ownership.erase_ownership hd hs hΩ ((hΓ.extend _).extend _)
          (hag _ fun _ => rfl) hm'
          (hgo i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g hc hSj hpos hg hbn gs val hal hval))
      · exact absurd hk0 hne
    | some D' =>
      -- The branch resumes the corecursor: a new value.
      have hk0 : Resumption.ofArity (decide (r ∈ Mode.oneOne.erased))
          (((B.blockName decl.names).bind decl.names.idxOf?).bind Ss.arity) ≠ .none := by
        obtain ⟨T₃, hT₃, rfl⟩ := TypeDeclaration.mem_names_of_codataTypes hT'
          (Term.blockName_mem hbn)
        obtain ⟨j₃, hj₃⟩ := List.mem_iff_getElem?.1 hT₃
        obtain ⟨ps₃, S₃, hS₃⟩ := hSs j₃ T₃ hj₃
        have harity : ((B.blockName decl.names).bind decl.names.idxOf?).bind Ss.arity =
            some ps₃.length := by
          simp only [hbn, Option.bind_some, TypeDeclaration.idxOf?_codataTypes (hd.nodup h.1) hj₃,
            States.arity, hS₃]
          rfl
        rw [harity]
        simp only [Resumption.ofArity]
        split <;> simp
      rcases hk with ⟨h0, -⟩ | ⟨-, rfl⟩
      · exact absurd h0 hk0
      · exact Target.Ownership.cast _ (Ownership.erase_ownership hd hs hΩ ((hΓ.extend _).extend _)
          (hag _ fun _ => rfl) hm'
          (hgr i j T' d ps'' S' p q ς ps₁ Ξ Θ B ψ g D' hc hSj hpos hg hbn gs hal))
  | .sub h hle => .sub (Ownership.erase_ownership hd hs hΩ hΓ hφ hm h) (Grade.run_le hle)

-- ADE: none.
/-- The erasure at run time of the arguments of a telescope checked in a mode `m'`, each at the
parameter of its entry whose grade is mapped by `f`, satisfies the requirements of their positions,
at ownerships that are the run-time multiplicities of theirs at each kept position, when `m'` checks
in the mode `11ᵐ` each argument whose mapped grade has a use at run time: the arguments of a
constructor or of an observation, `f` the identity, and the state of a corecursor, `f` the product
by its grade. -/
theorem OwnershipArgs.erase_ownership_map {sig : Signature} (hd : sig.Distinct)
    (hs : OwnershipSig sig)
    {Ω : Name → Multiplicity}
    (hΩ : ∀ f j k' g m p A, sig.HasConstant f j k' g m p A → Ω f = p.run) {k : Nat} {Γ : Scope}
    (hΓ : Γ.FirstOrder) {φ : Var Γ .var → Grade} {φ' : MultiplicityVector Γ.length}
    (hφ : Ownership.RunAgree φ' φ) {m' : Mode} (f : Grade → Grade)
    (hm' : ∀ u, f u ∉ Mode.oneOne.erased → m' ⊙ u = .oneOne) {ps : List Parameter}
    {ts : Args k Γ ps} {os : List Grade} :
    OwnershipArgs sig φ m' ts os → ∃ os' : List Multiplicity,
      Targets.Ownership Ω φ' os' (ts.terms.erase sig Mode.oneOne.erased hΓ
        (ps.map fun q => ⟨f q.usage, q.requirement⟩)) ∧
      os'.length = os.length ∧
      ∀ (i : Nat) (q : Parameter), ps[i]? = some q → f q.usage ∉ Mode.oneOne.erased →
        os'[i]? = os[i]?.map Grade.run
  | .nil => ⟨[], .nil, rfl, fun _ _ h => nomatch h⟩
  | .cons (p := q) (o := o) ht hr hts => by
    obtain ⟨os', h, hl, ha⟩ := OwnershipArgs.erase_ownership_map hd hs hΩ hΓ hφ f hm' hts
    simp only [Args.terms, List.map_cons, Terms.erase]
    by_cases hq : f q.usage ∈ Mode.oneOne.erased
    · simp only [hq, ↓reduceIte]
      refine ⟨q.requirement.run :: os', .cons (.erased _)
        (Multiplicity.modality.meet.meet_idem _).symm h, by simp [hl], fun i q' hi hk => ?_⟩
      cases i with
      | zero => cases hi; exact absurd hq hk
      | succ i => simpa using ha i q' (by simpa using hi) hk
    · simp only [hq, ↓reduceIte]
      have hmq := hm' _ hq
      refine ⟨o.run :: os', .cons (Ownership.erase_ownership hd hs hΩ hΓ hφ hmq ht)
        (Grade.run_le (hr (by rw [hmq]; decide))) h, by simp [hl], fun i q' hi hk => ?_⟩
      cases i with
      | zero => rfl
      | succ i => simpa using ha i q' (by simpa using hi) hk

end

end Sic.Core
