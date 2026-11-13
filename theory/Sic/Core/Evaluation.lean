module

public import Sic.Core.Erasure

/-!
# Evaluation

The evaluation of annex 17 of RFC 36, which runs the target language of the erasure by the calling
convention of Sic: `P; H; E ⊢ M ⇓ a; H'` evaluates the term `M` of the target language, in the
environment `E` of the addresses of its variables and the heap `H`, to the address `a` of its value
in the heap `H'`, the constants being those of the program `P`, the erasure of a signature.

The convention is the call by value, everywhere: the fields of a constructor, the arguments of an
observation, the entries of the state of a corecursor and the recursive results of a branch of a
recursor are evaluated before they are bound, so that a variable is bound to the address of a value,
and an access to a variable reads it, without computing anything.
The values are `↯`, the constructors applied to the addresses of their fields, and the closures of
the corecursors, which hold their environment, their branches and the addresses of their state: a
corecursor computes nothing until it is observed, and each observation runs the branch of its
destructor again, without keeping its result, so that the laziness is explicit, a closure that the
program builds, and the sharing too, a variable that it binds.
A constant is unfolded at each of its uses, as the rule `(δ_⟶)` of the reduction unfolds it, rather
than evaluated once: the program has no state of its own.

The evaluation is big-step: the core is total, so that a run of a closed term of the core never
diverges, and the guarantees on the uses at run time and on the ownership count the uses of a whole
run, which the heap at its end gives, rather than at an intermediate step.
The heap is a list of values, the address of a value being its position, and each allocation puts
the new value at its end.

The branch of a destructor that is recursive gives a position, of the type of positions of the
prelude, whose constructors `next` and `done` are the cases `0` and `1` of its block: the evaluation
resumes it, as the rule `(β_⟶)` of the reduction does, into a new closure of the same branches from
the state that `next` packs, the entries of the state being the first fields of the nested pairs of
the prelude, each the case `0` of its block, or into the term already built that `done` holds.

[Eriksson, Abel and Danielsson](https://doi.org/10.1145/3828677) run a machine with a heap, an
environment and a stack, by the call by name, to prove the resource correctness of their usage;
the evaluation here is by value, without a stack, and counts nothing yet.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- A value at run time: `↯`, the constructor of the case `i` of its block applied to the addresses
of its fields, or the closure of a corecursor, with the addresses `E` of the `n` variables of its
scope, its branches `P̄` and the addresses of its state; the cases and the addresses are counted
from `0`, while the RFC counts them from `1`.
RFC: `\mathsf{syntax}_V` -/
inductive Value where
  /-- `↯`. -/
  | erased
  /-- `cᵢ(ℓ̄)`. -/
  | ctor (i : Nat) (as : List Nat)
  /-- `⟨E; P̄; ℓ̄⟩`. -/
  | corec (n : Nat) (E : List Nat) (Ps : TargetCorecBranches n) (as : List Nat)

/-- `H`: the heap, the value at each address, the first one at `0`. -/
abbrev Heap : Type := List Value

/-- A program of the target language: the body of each constant at each instance of its qualities
and of its grades, a closed term, when the program defines it. -/
abbrev Program : Type := Name → List Quality → List Grade → Option (Target 0)

/-- The empty scope has no second-order variable. -/
theorem Scope.FirstOrder.nil : Scope.FirstOrder [] := fun _ h => nomatch h

-- ADE: none.
/-- The body of the constant `f` at the instance of the qualities `qs` and of the grades `ps`, erased
by `S`, when the entry defines it. -/
def Entry.compile (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] (f : Name)
    (qs : List Quality) (ps : List Grade) : Entry → Option (Target 0)
  | .constantDefinition d =>
    if d.name = f then
      if hq : qs.length = d.sorts then
        if hp : ps.length = d.grades then
          some ((d.body (.ofLists qs ps hq hp)).erase sig S Scope.FirstOrder.nil)
        else none
      else none
    else none
  | _ => none

-- ADE: none.
/-- `⌊Σ⌋_S`: the program of the signature `sig`, erased by the set of grades `S`, which gives the
constant `f.{s̄; p̄}` the erasure of the body of `f` at this instance, in the last entry of `sig`
that defines it.
RFC: `\mathsf{erase}_\Sigma` -/
def Signature.compile (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] : Program :=
  fun f qs ps => sig.findSome? (Entry.compile sig S f qs ps)

/-- The branch at a position of the branches of a recursor of the target language. -/
def TargetBranches.get {n : Nat} : TargetBranches n → Nat →
    Option (Σ a b, (Fin a → Multiplicity) × (Fin b → Multiplicity) × (Fin b → Option Nat) ×
      Target (n + (a + b)))
  | .nil, _ => none
  | .cons a b πs πs' ks N _, 0 => some ⟨a, b, πs, πs', ks, N⟩
  | .cons _ _ _ _ _ _ Ns, i + 1 => Ns.get i

/-- The branch at a position of the branches of a corecursor of the target language. -/
def TargetCorecBranches.get {n : Nat} : TargetCorecBranches n → Nat →
    Option (Resumption × Σ b c, (Fin b → Multiplicity) × (Fin c → Multiplicity) ×
      Target (n + (b + c)))
  | .nil, _ => none
  | .cons o b c πs πs' N _, 0 => some (o, ⟨b, c, πs, πs', N⟩)
  | .cons _ _ _ _ _ _ Ns, i + 1 => Ns.get i

-- ADE: none.
/-- `H ⊢ unpack_k(x) = ℓ̄`: the addresses of the `k` entries that the value at the address `x`
packs, the first fields of `k` nested pairs. -/
inductive Unpack : Heap → Nat → Nat → List Nat → Prop where
  /-- No entry.
  RFC: `\mathsf{unpack}_\Downarrow.0` -/
  | zero {H : Heap} {x : Nat} : Unpack H 0 x []
  /-- A pair of an entry and of the others.
  RFC: `\mathsf{unpack}_\Downarrow.{,}` -/
  | pair {H : Heap} {k x y z : Nat} {ss : List Nat} (h : H[x]? = some (.ctor 0 [y, z]))
      (hs : Unpack H k z ss) : Unpack H (k + 1) x (y :: ss)

-- ADE: none.
/-- `H ⊢ ⟨E; P̄⟩ ↻_k w ⇓ v; H'`: the value at the address `w` that the branch of a destructor gives,
resumed: itself when the branch resumes no state, a new closure of the same branches from the state
of `k` entries that `next` packs, or from `k` erased entries, which stand at the address of the new
state without reading it, or the term already built that `done` holds. -/
inductive EvalResume : Heap → (n : Nat) → List Nat → TargetCorecBranches n → Resumption → Nat →
    Nat → Heap → Prop where
  /-- The branch resumes no state.
  RFC: `\mathsf{resume}_\Downarrow.\bot` -/
  | none {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {w : Nat} :
      EvalResume H n E Ps .none w w H
  /-- `next(x)`: a new closure from the state that `x` packs.
  RFC: `\mathsf{resume}_\Downarrow.\mathsf{next}` -/
  | next {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {k w x : Nat}
      {ss : List Nat} (h : H[w]? = some (.ctor 0 [x])) (hs : Unpack H k x ss) :
      EvalResume H n E Ps (.unpack k) w H.length (H ++ [.corec n E Ps ss])
  /-- `next(x)`, for an erased state: a new closure whose `k` entries stand at the address `x`,
  which is not read.
  RFC: `\mathsf{resume}_\Downarrow.\text{↯}` -/
  | erased {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {k w x : Nat}
      (h : H[w]? = some (.ctor 0 [x])) :
      EvalResume H n E Ps (.erased k) w H.length (H ++ [.corec n E Ps (List.replicate k x)])
  /-- `done(x)`: the term already built `x`.
  RFC: `\mathsf{resume}_\Downarrow.\mathsf{done}` -/
  | done {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {o : Resumption}
      {w x : Nat} (ho : o ≠ .none) (h : H[w]? = some (.ctor 1 [x])) : EvalResume H n E Ps o w x H

mutual

-- ADE: none.
/-- `𝒫; H; E ⊢ M ⇓ a; H'`: the term `M` of the target language evaluates, in the environment `E`
of the addresses of its variables, the last one first, and the heap `H`, to the address `a` of its
value in the heap `H'`. -/
inductive Eval (P : Program) : {n : Nat} → Heap → List Nat → Target n → Nat → Heap → Prop where
  /-- A variable is the address that the environment gives it.
  RFC: `\mathsf{eval}_x` -/
  | var {n : Nat} {H : Heap} {E : List Nat} {x : Fin n} {a : Nat} (h : E[(x : Nat)]? = some a) :
      Eval P H E (.var x) a H
  /-- A constant evaluates its body in the program, a closed term.
  RFC: `\mathsf{eval}_f` -/
  | const {n : Nat} {H H' : Heap} {E : List Nat} {f : Name} {qs : List Quality} {ps : List Grade}
      {M : Target 0} {a : Nat} (h : P f qs ps = some M) (hM : Eval P H [] M a H') :
      Eval P (n := n) H E (.const f qs ps) a H'
  /-- `↯` allocates itself.
  RFC: `\mathsf{eval}_{\text{↯}}` -/
  | erased {n : Nat} {H : Heap} {E : List Nat} :
      Eval P (n := n) H E .erased H.length (H ++ [.erased])
  /-- A constructor evaluates its fields, in order, and allocates itself with their addresses.
  RFC: `\mathsf{eval}_c` -/
  | ctor {n : Nat} {H H' : Heap} {E : List Nat} {i : Nat} {Ms : Targets n} {as : List Nat}
      (hs : EvalAll P H E Ms as H') : Eval P H E (.ctor i Ms) H'.length (H' ++ [.ctor i as])
  /-- A recursor evaluates its term, then eliminates its value.
  RFC: `\mathsf{eval}_{\mathsf{rec}}` -/
  | recursor {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {M : Target n} {Ns : TargetBranches n}
      {a b : Nat} (h : Eval P H₁ E M a H₂) (hr : EvalRec P H₂ E Ns a b H₃) :
      Eval P H₁ E (.recursor M Ns) b H₃
  /-- An observation evaluates its term, then its arguments, in order, then observes the value of
  its term.
  RFC: `\mathsf{eval}_d` -/
  | obs {n : Nat} {H₁ H₂ H₃ H₄ : Heap} {E : List Nat} {M : Target n} {i : Nat} {Ms : Targets n}
      {a b : Nat} {bs : List Nat} (h : Eval P H₁ E M a H₂) (hs : EvalAll P H₂ E Ms bs H₃)
      (ho : EvalObs P H₃ a i bs b H₄) : Eval P H₁ E (.obs M i Ms) b H₄
  /-- A corecursor evaluates its state, in order, and allocates its closure.
  RFC: `\mathsf{eval}_{\mathsf{corec}}` -/
  | corec {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n} {Ps : TargetCorecBranches n}
      {as : List Nat} (hs : EvalAll P H E Ms as H') :
      Eval P H E (.corec Ms Ps) H'.length (H' ++ [.corec n E Ps as])

-- ADE: none.
/-- `𝒫; H; E ⊢ M̄ ⇓ ā; H'`: the terms evaluate, the first one first, to the addresses `ā`. -/
inductive EvalAll (P : Program) : {n : Nat} → Heap → List Nat → Targets n → List Nat → Heap →
    Prop where
  /-- No term.
  RFC: `\mathsf{eval}_{\bar M}.\varepsilon` -/
  | nil {n : Nat} {H : Heap} {E : List Nat} : EvalAll P (n := n) H E .nil [] H
  /-- The first term, then the others.
  RFC: `\mathsf{eval}_{\bar M}.{,}` -/
  | cons {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {M : Target n} {Ms : Targets n} {a : Nat}
      {as : List Nat} (h : Eval P H₁ E M a H₂) (hs : EvalAll P H₂ E Ms as H₃) :
      EvalAll P H₁ E (.cons M Ms) (a :: as) H₃

-- ADE: none.
/-- `𝒫; H; E ⊢ rec a with N̄ ⇓ b; H'`: the recursor with the branches `N̄`, in the environment `E`,
eliminates the value at the address `a`, a constructor: the branch of its case evaluates, with its
fields and its recursive results, each the recursor on its field, or `↯` when it is erased. -/
inductive EvalRec (P : Program) : {n : Nat} → Heap → List Nat → TargetBranches n → Nat → Nat →
    Heap → Prop where
  /-- RFC: `\iota_\Downarrow` -/
  | iota {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {Ns : TargetBranches n} {a v : Nat} {i : Nat}
      {as : List Nat} {a' b : Nat} {πs : Fin a' → Multiplicity} {πs' : Fin b → Multiplicity}
      {ks : Fin b → Option Nat} {N : Target (n + (a' + b))} {rs : List Nat}
      (h : H₁[a]? = some (.ctor i as)) (hN : Ns.get i = some ⟨a', b, πs, πs', ks, N⟩)
      (ha : as.length = a') (hr : EvalResults P H₁ E Ns as (List.ofFn ks) rs H₂)
      (hv : Eval P H₂ (rs.reverse ++ as.reverse ++ E) N v H₃) : EvalRec P H₁ E Ns a v H₃

-- ADE: none.
/-- `𝒫; H; E ⊢ rec ā with N̄ ← k̄ ⇓ b̄; H'`: the recursive results of a branch, in order, each the
recursor on the field at its position in `ā`, or `↯` when it is erased. -/
inductive EvalResults (P : Program) : {n : Nat} → Heap → List Nat → TargetBranches n →
    List Nat → List (Option Nat) → List Nat → Heap → Prop where
  /-- No result.
  RFC: `\mathsf{results}_\Downarrow.\varepsilon` -/
  | nil {n : Nat} {H : Heap} {E : List Nat} {Ns : TargetBranches n} {as : List Nat} :
      EvalResults P H E Ns as [] [] H
  /-- An erased result, `↯`, then the others.
  RFC: `\mathsf{results}_\Downarrow.\text{↯}` -/
  | erased {n : Nat} {H₁ H₂ : Heap} {E : List Nat} {Ns : TargetBranches n} {as : List Nat}
      {ks : List (Option Nat)} {rs : List Nat}
      (hs : EvalResults P (H₁ ++ [.erased]) E Ns as ks rs H₂) :
      EvalResults P H₁ E Ns as (none :: ks) (H₁.length :: rs) H₂
  /-- The recursor on the field at the position `j`, then the others.
  RFC: `\mathsf{results}_\Downarrow.\mathsf{rec}` -/
  | recursor {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {Ns : TargetBranches n} {as : List Nat}
      {j a r : Nat} {ks : List (Option Nat)} {rs : List Nat} (hj : as[j]? = some a)
      (h : EvalRec P H₁ E Ns a r H₂) (hs : EvalResults P H₂ E Ns as ks rs H₃) :
      EvalResults P H₁ E Ns as (some j :: ks) (r :: rs) H₃

-- ADE: none.
/-- `𝒫; H ⊢ a.dᵢ(b̄) ⇓ c; H'`: the observation by the destructor of the case `i`, applied to the
arguments at the addresses `b̄`, of the value at the address `a`, a closure: the branch of the case
evaluates in the environment of the closure, with its state and the arguments, and its value is
resumed when the branch resumes a state. -/
inductive EvalObs (P : Program) : Heap → Nat → Nat → List Nat → Nat → Heap → Prop where
  /-- RFC: `\beta_\Downarrow` -/
  | beta {H₁ H₂ H₃ : Heap} {a i : Nat} {bs : List Nat} {v w : Nat} {n : Nat} {E : List Nat}
      {Ps : TargetCorecBranches n} {ss : List Nat} {o : Resumption} {b c : Nat}
      {πs : Fin b → Multiplicity} {πs' : Fin c → Multiplicity} {N : Target (n + (b + c))}
      (h : H₁[a]? = some (.corec n E Ps ss)) (hP : Ps.get i = some (o, ⟨b, c, πs, πs', N⟩)) (hb : ss.length = b) (hc : bs.length = c)
      (hw : Eval P H₁ (bs.reverse ++ ss.reverse ++ E) N w H₂)
      (hr : EvalResume H₂ n E Ps o w v H₃) : EvalObs P H₁ a i bs v H₃

end

/-! ## Determinism -/

/-- The unpacking of a value is unique. -/
theorem Unpack.det {H : Heap} {k x : Nat} {ss₁ ss₂ : List Nat} :
    Unpack H k x ss₁ → Unpack H k x ss₂ → ss₁ = ss₂
  | .zero, .zero => rfl
  | .pair h hs, .pair h' hs' => by
    rw [h] at h'
    cases h'
    rw [Unpack.det hs hs']

/-- The resumption of a value is unique. -/
theorem EvalResume.det {H H₁ H₂ : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
    {o : Resumption} {w v₁ v₂ : Nat} :
    EvalResume H n E Ps o w v₁ H₁ → EvalResume H n E Ps o w v₂ H₂ → v₁ = v₂ ∧ H₁ = H₂
  | .none, .none => ⟨rfl, rfl⟩
  | .none, .done ho _ | .done ho _, .none => (ho rfl).elim
  | .next h hs, .next h' hs' => by
    rw [h] at h'
    cases h'
    cases Unpack.det hs hs'
    exact ⟨rfl, rfl⟩
  | .erased h, .erased h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl⟩
  | .next h _, .done _ h' | .done _ h, .next h' _ | .erased h, .done _ h'
  | .done _ h, .erased h' => by
    rw [h] at h'
    cases h'
  | .done _ h, .done _ h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl⟩

mutual

-- ADE: none.
/-- The evaluation is deterministic: a term evaluates to one address, in one heap.
RFC: `\mathsf{det}_\Downarrow` -/
theorem Eval.det {P : Program} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat} {M : Target n}
    {a₁ a₂ : Nat} (h₁ : Eval P H E M a₁ H₁) (h₂ : Eval P H E M a₂ H₂) :
    a₁ = a₂ ∧ H₁ = H₂ :=
  match h₁, h₂ with
  | .var h, .var h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl⟩
  | .const h hM, .const h' hM' => by
    rw [h] at h'
    cases h'
    exact Eval.det hM hM'
  | .erased, .erased => ⟨rfl, rfl⟩
  | .ctor hs, .ctor hs' => by
    obtain ⟨rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl⟩
  | .recursor h hr, .recursor h' hr' => by
    obtain ⟨rfl, rfl⟩ := Eval.det h h'
    exact EvalRec.det hr hr'
  | .obs h hs ho, .obs h' hs' ho' => by
    obtain ⟨rfl, rfl⟩ := Eval.det h h'
    obtain ⟨rfl, rfl⟩ := EvalAll.det hs hs'
    exact EvalObs.det ho ho'
  | .corec hs, .corec hs' => by
    obtain ⟨rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The evaluation of terms is deterministic. -/
theorem EvalAll.det {P : Program} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat} {Ms : Targets n}
    {as₁ as₂ : List Nat} (h₁ : EvalAll P H E Ms as₁ H₁) (h₂ : EvalAll P H E Ms as₂ H₂) :
    as₁ = as₂ ∧ H₁ = H₂ :=
  match h₁, h₂ with
  | .nil, .nil => ⟨rfl, rfl⟩
  | .cons h hs, .cons h' hs' => by
    obtain ⟨rfl, rfl⟩ := Eval.det h h'
    obtain ⟨rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The elimination of a value by a recursor is deterministic. -/
theorem EvalRec.det {P : Program} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {Ns : TargetBranches n} {a v₁ v₂ : Nat}
    (h₁ : EvalRec P H E Ns a v₁ H₁) (h₂ : EvalRec P H E Ns a v₂ H₂) : v₁ = v₂ ∧ H₁ = H₂ :=
  match h₁, h₂ with
  | .iota h hN _ hr hv, .iota h' hN' _ hr' hv' => by
    rw [h] at h'
    cases h'
    rw [hN] at hN'
    cases hN'
    obtain ⟨rfl, rfl⟩ := EvalResults.det hr hr'
    exact Eval.det hv hv'
termination_by structural h₁

-- ADE: none.
/-- The evaluation of the recursive results of a branch is deterministic. -/
theorem EvalResults.det {P : Program} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {Ns : TargetBranches n} {as : List Nat} {ks : List (Option Nat)} {rs₁ rs₂ : List Nat}
    (h₁ : EvalResults P H E Ns as ks rs₁ H₁) (h₂ : EvalResults P H E Ns as ks rs₂ H₂) :
    rs₁ = rs₂ ∧ H₁ = H₂ :=
  match h₁, h₂ with
  | .nil, .nil => ⟨rfl, rfl⟩
  | .erased hs, .erased hs' => by
    obtain ⟨rfl, rfl⟩ := EvalResults.det hs hs'
    exact ⟨rfl, rfl⟩
  | .recursor hj h hs, .recursor hj' h' hs' => by
    rw [hj] at hj'
    cases hj'
    obtain ⟨rfl, rfl⟩ := EvalRec.det h h'
    obtain ⟨rfl, rfl⟩ := EvalResults.det hs hs'
    exact ⟨rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The observation of a value is deterministic. -/
theorem EvalObs.det {P : Program} {H H₁ H₂ : Heap} {a i : Nat} {bs : List Nat} {v₁ v₂ : Nat}
    (h₁ : EvalObs P H a i bs v₁ H₁) (h₂ : EvalObs P H a i bs v₂ H₂) : v₁ = v₂ ∧ H₁ = H₂ :=
  match h₁, h₂ with
  | .beta h hP _ _ hw hr, .beta h' hP' _ _ hw' hr' => by
    rw [h] at h'
    cases h'
    rw [hP] at hP'
    cases hP'
    obtain ⟨rfl, rfl⟩ := Eval.det hw hw'
    exact EvalResume.det hr hr'
termination_by structural h₁

end

end Sic.Core
