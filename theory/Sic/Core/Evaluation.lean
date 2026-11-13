module

public import Sic.Core.Erasure

/-!
# Evaluation

The evaluation of annex 17 of RFC 36, which runs the target language of the erasure by the calling
convention of Sic: `P; H; E ⊢ M ⇓ a; H'; R` evaluates the term `M` of the target language, in the
environment `E` of the addresses of the cells of its variables and the heap `H`, to the address `a`
of its value in the heap `H'`, reading the cells `R`, the constants being those of the program `P`,
the erasure of a signature.

The convention is the call by value, everywhere: the fields of a constructor, the arguments of an
observation, the entries of the state of a corecursor and the recursive results of a branch of a
recursor are evaluated before they are bound, so that a variable is bound to the address of a value,
and an access to a variable reads it, without computing anything.
Each binding allocates a cell for each of its variables, `bind_π(ℓ)`, which holds the address `ℓ` of
its value and the multiplicity `π` of its binder, and an access to the variable reads its cell, which
the evaluation records, so that the cells read by a run count the uses at run time of each binding,
while the heap stays immutable.
The evaluation runs at a weight, the multiplicity of the uses of the value that it computes: a
position evaluates its term once, and its value is then used as many times as the multiplicity of
the position, so that the term of a position runs at the weight times this multiplicity, and each
cell that the run allocates has the multiplicity of its binder times the weight: a variable bound
while a value is computed, which a closure of the value captures, is read once for each use of the
value, which shares a single cell.
A value stores each address that it holds, a field of a constructor, an entry of the state of a
closure, at the multiplicity of its position, and an observation passes its arguments at theirs:
these multiplicities bound the uses of a value through the position, which a closure observed again
would otherwise exceed.
A value also stores with each address the requirement at run time of its position on the ownership
of the value, and an observation passes the requirements of its arguments and the ownership at run
time of the result of its destructor.
The recursor and the observation check that the binders of the branch they run are within these
multiplicities, the recursor of the multiplicity `ρ` reading each field `ρ` times its multiplicity,
that the ownerships that the branch gives its variables are within those that the requirements
allow, and that the ownership of the result is the one that the observation expects, and the
evaluation is stuck otherwise.
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
the evaluation here is by value, without a stack, and records the reads of the cells instead of
updating the grades of the heap; their machine likewise eliminates a pair only by a continuation of
the same grade, `prodʷₕ` in `Graded/Heap/Reduction.agda`, as the recursor and the observation check
the multiplicities here, and allocates its heap entries at the grade of the binder times the
multiplicity of the stack, `∣ S ∣≡ q`, as the weight multiplies the multiplicities of the cells
here.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- A value at run time: `↯`, the constructor of the case `i` of its block applied to the addresses
of its fields, each at the multiplicity and the requirement of its field, the closure of a
corecursor, with the addresses `E` of the cells of the `n` variables of its scope, its branches `P̄`
and the addresses of its state, each at the multiplicity and the requirement of its entry, or the
cell of a variable; the multiplicities bound the uses of the values through these positions, and the
requirements their ownerships at run time; the cases and the addresses are counted from `0`, while
the RFC counts them from `1`.
RFC: `\mathsf{syntax}_V` -/
inductive Value where
  /-- `↯`. -/
  | erased
  /-- `cᵢ(ℓ̄ ▶ π̄ ◀ ϱ̄)`. -/
  | ctor (i : Nat) (πs ϱs : List Multiplicity) (as : List Nat)
  /-- `⟨E; P̄; ℓ̄ ▶ π̄ ◀ ϱ̄⟩`. -/
  | corec (n : Nat) (E : List Nat) (Ps : TargetCorecBranches n) (πs ϱs : List Multiplicity)
      (as : List Nat)
  /-- `bind_π(ℓ)`: the cell of a variable bound to the address `ℓ` by a binder of multiplicity
  `π`. -/
  | cell (π : Multiplicity) (a : Nat)

/-- `H`: the heap, the value at each address, the first one at `0`. -/
abbrev Heap : Type := List Value

-- ADE: none.
/-- `(H, bind_π̄(ℓ̄))`: the heap `H` followed by a cell for each address of `ℓ̄`, of the multiplicity
at its position in `π̄`, which a binder allocates for its variables, at the addresses from `|H|`.
RFC: `\mathsf{bind}_H` -/
def Heap.bind (H : Heap) (πs : List Multiplicity) (as : List Nat) : Heap :=
  H ++ List.zipWith Value.cell πs as

-- ADE: none.
/-- `H ⊢ E ↦ ℓ̄`: the addresses `E` are cells of the heap `H` that bind the addresses `ℓ̄`, one by
one.
RFC: `\mapsto_H` -/
def Heap.Binds (H : Heap) : List Nat → List Nat → Prop
  | [], [] => True
  | c :: E, a :: as => (∃ π, H[c]? = some (.cell π a)) ∧ Heap.Binds H E as
  | _, _ => False

/-- A program of the target language: the body of each constant at each instance of its qualities
and of its grades, a closed term, when the program defines it. -/
abbrev Program : Type := Name → List Quality → List Grade → Option (Target 0)

/-- The empty scope has no second-order variable. -/
theorem Scope.FirstOrder.nil : Scope.FirstOrder [] := fun _ h => nomatch h

-- ADE: none.
/-- The body of the constant `f` at the instance of the qualities `qs` and of the grades `ps`, erased
by `S`, when the entry defines it in the mode `11ᵐ`, the only constants that a term of this mode
refers to. -/
def Entry.compile (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] (f : Name)
    (qs : List Quality) (ps : List Grade) : Entry → Option (Target 0)
  | .constantDefinition d =>
    if d.name = f ∧ d.mode = .oneOne then
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
that defines it in the mode `11ᵐ`.
RFC: `\mathsf{erase}_\Sigma` -/
def Signature.compile (sig : Signature) (S : Set Grade) [DecidablePred (· ∈ S)] : Program :=
  fun f qs ps => sig.findSome? (Entry.compile sig S f qs ps)

/-- The branch at a position of the branches of a recursor of the target language. -/
def TargetBranches.get {n : Nat} : TargetBranches n → Nat →
    Option (Σ a b, (Fin a → Multiplicity) × (Fin a → Multiplicity) × (Fin b → Multiplicity) ×
      (Fin b → Option Nat) × Target (n + (a + b)))
  | .nil, _ => none
  | .cons a b πs κs πs' ks N _, 0 => some ⟨a, b, πs, κs, πs', ks, N⟩
  | .cons _ _ _ _ _ _ _ Ns, i + 1 => Ns.get i

/-- The branch at a position of the branches of a corecursor of the target language. -/
def TargetCorecBranches.get {n : Nat} : TargetCorecBranches n → Nat →
    Option (Resumption × Σ b c, (Fin b → Multiplicity) × (Fin b → Multiplicity) ×
      (Fin c → Multiplicity) × (Fin c → Multiplicity) × ResultOwnership Multiplicity c ×
      Target (n + (b + c)))
  | .nil, _ => none
  | .cons o b c πs ϱs πs' ϱs' ψ N _, 0 => some (o, ⟨b, c, πs, ϱs, πs', ϱs', ψ, N⟩)
  | .cons _ _ _ _ _ _ _ _ _ Ns, i + 1 => Ns.get i

-- ADE: none.
/-- `H ⊢ unpack_k(x) = ℓ̄ ▶ π̄ ◀ ϱ̄`: the addresses of the `k` entries that the value at the address
`x` packs, the first fields of `k` nested pairs, at the multiplicities and the requirements at which
the pairs store them, each times those of the second fields that hold its pair, the pairs ending
with a constructor without field. -/
inductive Unpack : Heap → Nat → Nat → List Multiplicity → List Multiplicity → List Nat → Prop where
  /-- No entry: the end of the pairs, a constructor without field, the unit of the prelude, whose
  value is never read, so that it must hold nothing; the evaluation is stuck otherwise.
  RFC: `\mathsf{unpack}_\Downarrow.0` -/
  | zero {H : Heap} {x i : Nat} (h : H[x]? = some (.ctor i [] [] [])) : Unpack H 0 x [] [] []
  /-- A pair of an entry and of the others.
  RFC: `\mathsf{unpack}_\Downarrow.{,}` -/
  | pair {H : Heap} {k x y z : Nat} {π π' ϱ ϱ' : Multiplicity} {πs ϱs : List Multiplicity}
      {ss : List Nat} (h : H[x]? = some (.ctor 0 [π, π'] [ϱ, ϱ'] [y, z]))
      (hs : Unpack H k z πs ϱs ss) :
      Unpack H (k + 1) x (π :: πs.map (π' * ·)) (ϱ :: ϱs.map (ϱ' * ·)) (y :: ss)

-- ADE: none.
/-- `H ⊢ ⟨E; P̄⟩ ↻_k w ◀ ψ ⇓ v; H'`: the value at the address `w` that the branch of a destructor of
the ownership at run time `ψ` of its result gives, resumed: itself when the branch resumes no
state, a new closure of the same branches from the state of `k` entries that `next` packs, each at
the multiplicity and the requirement at which the pack stores it, times those of the field of
`next`, or from `k` erased entries, which stand at the address of the new state without reading it,
at the multiplicity and the requirement `0`, or the term already built that `done` holds. -/
inductive EvalResume : Heap → (n : Nat) → List Nat → TargetCorecBranches n → Resumption →
    {c : Nat} → ResultOwnership Multiplicity c → Nat → Nat → Heap → Prop where
  /-- The branch resumes no state.
  RFC: `\mathsf{resume}_\Downarrow.\bot` -/
  | none {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {c : Nat}
      {ψ : ResultOwnership Multiplicity c} {w : Nat} : EvalResume H n E Ps .none ψ w w H
  /-- `next(x)`: a new closure from the state that `x` packs.
  RFC: `\mathsf{resume}_\Downarrow.\mathsf{next}` -/
  | next {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {c : Nat}
      {ψ : ResultOwnership Multiplicity c} {π ϱ : Multiplicity} {πs ϱs : List Multiplicity}
      {k w x : Nat} {ss : List Nat} (h : H[w]? = some (.ctor 0 [π] [ϱ] [x]))
      (hs : Unpack H k x πs ϱs ss) :
      EvalResume H n E Ps (.unpack k) ψ w H.length
        (H ++ [.corec n E Ps (πs.map (π * ·)) (ϱs.map (ϱ * ·)) ss])
  /-- `next(x)`, for an erased state: a new closure whose `k` entries stand at the address `x`,
  which is not read, at the multiplicity `0`, the multiplicity of the field of `next`, so that the
  state is never used, and at the requirement `0`; the evaluation is stuck otherwise.
  RFC: `\mathsf{resume}_\Downarrow.\text{↯}` -/
  | erased {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {c : Nat}
      {ψ : ResultOwnership Multiplicity c} {ϱ : Multiplicity} {k w x : Nat}
      (h : H[w]? = some (.ctor 0 [.zero] [ϱ] [x])) :
      EvalResume H n E Ps (.erased k) ψ w H.length
        (H ++ [.corec n E Ps (List.replicate k .zero) (List.replicate k .zero)
          (List.replicate k x)])
  /-- `done(x)`: the term already built `x`, whose field has a multiplicity other than `0`, so that
  the value that it gives is one that it may use, and a requirement that gives it at least the
  constant of the ownership of the result, `ω` when it has none, which the observation gives it; the
  evaluation is stuck otherwise.
  RFC: `\mathsf{resume}_\Downarrow.\mathsf{done}` -/
  | done {H : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n} {c : Nat}
      {ψ : ResultOwnership Multiplicity c} {π ϱ : Multiplicity} {o : Resumption} {w x : Nat}
      (ho : o ≠ .none) (h : H[w]? = some (.ctor 1 [π] [ϱ] [x])) (hπ : π ≠ .zero)
      (hϱ : ψ.constant.getD .omega ≤ ϱ) : EvalResume H n E Ps o ψ w x H

-- ADE: none.
/-- `recursions_{k̄,π̄'}(l)`: the multiplicity of the recursions that a branch of a recursor runs on
its field at the position `l`, the multiplicity in `π̄'` of the binder of each recursive result
whose field in `k̄` is `l`: the recursion runs once, but its result is read as its binder allows,
each read using the value that the recursion builds from the field.
RFC: `\mathsf{recursions}_{\bar k, \bar\pi', l}` -/
def recursionsAt : List (Option Nat) → List Multiplicity → Nat → Multiplicity
  | k :: ks, π :: πs, l => (if k = some l then π else .zero) + recursionsAt ks πs l
  | _, _, _ => .zero

mutual

-- ADE: `∣ S ∣≡ q`, in `Graded/Heap/Reduction.agda`, for the weight.
/-- `𝒫; ϖ; H; E ⊢ M ⇓ a; H'; R`: the term `M` of the target language evaluates, at the weight `ϖ`,
in the environment `E` of the addresses of the cells of its variables, the last one first, and the
heap `H`, to the address `a` of its value in the heap `H'`, reading the cells `R`, in order, one for
each access to a variable; the weight is the multiplicity of the uses of the value, so that each
cell that the run allocates has the multiplicity of its binder times the weight. -/
inductive Eval (P : Program) : {n : Nat} → Multiplicity → Heap → List Nat → Target n → Nat → Heap →
    List Nat → Prop where
  /-- A variable reads its cell, which gives the address of its value.
  RFC: `\mathsf{eval}_x` -/
  | var {ϖ : Multiplicity} {n : Nat} {H : Heap} {E : List Nat} {x : Fin n} {c : Nat}
      {π : Multiplicity} {a : Nat} (h : E[(x : Nat)]? = some c) (hc : H[c]? = some (.cell π a)) :
      Eval P ϖ H E (.var x) a H [c]
  /-- A constant evaluates its body in the program, a closed term.
  RFC: `\mathsf{eval}_f` -/
  | const {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {f : Name}
      {qs : List Quality} {ps : List Grade} {M : Target 0} {a : Nat} {R : List Nat}
      (h : P f qs ps = some M) (hM : Eval P ϖ H [] M a H' R) :
      Eval P (n := n) ϖ H E (.const f qs ps) a H' R
  /-- `↯` allocates itself.
  RFC: `\mathsf{eval}_{\text{↯}}` -/
  | erased {ϖ : Multiplicity} {n : Nat} {H : Heap} {E : List Nat} :
      Eval P (n := n) ϖ H E .erased H.length (H ++ [.erased]) []
  /-- A constructor evaluates its fields, in order, each at the weight times its multiplicity, and
  allocates itself with their addresses, at their multiplicities.
  RFC: `\mathsf{eval}_c` -/
  | ctor {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {i : Nat} {Ms : Targets n}
      {as : List Nat} {R : List Nat} (hs : EvalAll P ϖ H E Ms as H' R) :
      Eval P ϖ H E (.ctor i Ms) H'.length
        (H' ++ [.ctor i Ms.multiplicities Ms.requirements as]) R
  /-- A recursor evaluates its term, at the weight times its multiplicity, then eliminates its
  value.
  RFC: `\mathsf{eval}_{\mathsf{rec}}` -/
  | recursor {ϖ : Multiplicity} {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {ρ : Multiplicity}
      {M : Target n} {Ns : TargetBranches n} {a b : Nat} {R₁ R₂ : List Nat}
      (h : Eval P (ϖ * ρ) H₁ E M a H₂ R₁) (hr : EvalRec P ϖ H₂ E ρ Ns a b H₃ R₂) :
      Eval P ϖ H₁ E (.recursor ρ M Ns) b H₃ (R₁ ++ R₂)
  /-- An observation evaluates its term, then its arguments, in order, each at the weight times
  its multiplicity, then observes the value of its term, with the multiplicities and the
  requirements of the arguments and the ownership of the result.
  RFC: `\mathsf{eval}_d` -/
  | obs {ϖ : Multiplicity} {n : Nat} {H₁ H₂ H₃ H₄ : Heap} {E : List Nat} {M : Target n} {i c : Nat}
      {ψ : ResultOwnership Multiplicity c} {Ms : Targets n} {a b : Nat} {bs : List Nat}
      {R₁ R₂ R₃ : List Nat} (h : Eval P ϖ H₁ E M a H₂ R₁) (hs : EvalAll P ϖ H₂ E Ms bs H₃ R₂)
      (ho : EvalObs P ϖ H₃ a i ψ Ms.multiplicities Ms.requirements bs b H₄ R₃) :
      Eval P ϖ H₁ E (.obs M i ψ Ms) b H₄ (R₁ ++ (R₂ ++ R₃))
  /-- A corecursor evaluates its state, in order, each entry at the weight times its multiplicity,
  and allocates its closure, with the multiplicities of the entries.
  RFC: `\mathsf{eval}_{\mathsf{corec}}` -/
  | corec {ϖ : Multiplicity} {n : Nat} {H H' : Heap} {E : List Nat} {Ms : Targets n}
      {Ps : TargetCorecBranches n} {as : List Nat} {R : List Nat}
      (hs : EvalAll P ϖ H E Ms as H' R) :
      Eval P ϖ H E (.corec Ms Ps) H'.length
        (H' ++ [.corec n E Ps Ms.multiplicities Ms.requirements as]) R

-- ADE: none.
/-- `𝒫; ϖ; H; E ⊢ M̄ ⇓ ā; H'; R`: the terms evaluate, the first one first, to the addresses `ā`,
each at the weight `ϖ` times its multiplicity. -/
inductive EvalAll (P : Program) : {n : Nat} → Multiplicity → Heap → List Nat → Targets n →
    List Nat → Heap → List Nat → Prop where
  /-- No term.
  RFC: `\mathsf{eval}_{\bar M}.\varepsilon` -/
  | nil {ϖ : Multiplicity} {n : Nat} {H : Heap} {E : List Nat} :
      EvalAll P (n := n) ϖ H E .nil [] H []
  /-- The first term, then the others.
  RFC: `\mathsf{eval}_{\bar M}.{,}` -/
  | cons {ϖ : Multiplicity} {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {M : Target n}
      {Ms : Targets n} {a : Nat} {as : List Nat} {R₁ R₂ : List Nat} {π ϱ : Multiplicity}
      (h : Eval P (ϖ * π) H₁ E M a H₂ R₁) (hs : EvalAll P ϖ H₂ E Ms as H₃ R₂) :
      EvalAll P ϖ H₁ E (.cons π ϱ M Ms) (a :: as) H₃ (R₁ ++ R₂)

-- ADE: none.
/-- `𝒫; ϖ; H; E ⊢ rec_ρ a with N̄ ⇓ b; H'; R`: the recursor of the multiplicity `ρ` with the
branches `N̄`, in the environment `E`, at the weight `ϖ`, eliminates the value at the address `a`, a
constructor: the branch of its case evaluates, with cells for its fields and its recursive results,
each the recursor on its field, at the weight times the multiplicity of its binder, or `↯` when it
is erased, at the multiplicities of its binders times the weight; the uses that the branch makes of
each field, by its cell and by the recursions on it, must be within the uses that the constructor
allows, `ρ` times the multiplicity of the field, and the coefficient of the ownership that the branch
gives the variable of each field within the requirement of the field times these uses, and the
evaluation is stuck otherwise. -/
inductive EvalRec (P : Program) : {n : Nat} → Multiplicity → Heap → List Nat → Multiplicity →
    TargetBranches n → Nat → Nat → Heap → List Nat → Prop where
  /-- RFC: `\iota_\Downarrow` -/
  | iota {ϖ : Multiplicity} {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {ρ : Multiplicity}
      {Ns : TargetBranches n} {a v : Nat} {i : Nat} {πs₀ ϱs₀ : List Multiplicity} {as : List Nat}
      {a' b : Nat} {πs κs : Fin a' → Multiplicity} {πs' : Fin b → Multiplicity}
      {ks : Fin b → Option Nat} {N : Target (n + (a' + b))} {rs : List Nat} {R₁ R₂ : List Nat}
      (h : H₁[a]? = some (.ctor i πs₀ ϱs₀ as)) (hN : Ns.get i = some ⟨a', b, πs, κs, πs', ks, N⟩)
      (ha : as.length = a')
      (hπ : ∀ l : Fin a', ∃ π₀, πs₀[(l : Nat)]? = some π₀ ∧
        ρ * π₀ ≤ πs l + ρ * recursionsAt (List.ofFn ks) (List.ofFn πs') l)
      (hκ : ∀ l : Fin a', ∃ π₀ ϱ₀, πs₀[(l : Nat)]? = some π₀ ∧ ϱs₀[(l : Nat)]? = some ϱ₀ ∧
        κs l ≤ ϱ₀ * (ρ * π₀))
      (hr : EvalResults P ϖ H₁ E ρ Ns as (List.ofFn ks) (List.ofFn πs') rs H₂ R₁)
      (hv : Eval P ϖ (H₂.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (as ++ rs))
        ((List.range' H₂.length (as ++ rs).length).reverse ++ E) N v H₃ R₂) :
      EvalRec P ϖ H₁ E ρ Ns a v H₃ (R₁ ++ R₂)

-- ADE: none.
/-- `𝒫; ϖ; H; E ⊢ rec_ρ ā with N̄ ← k̄ ▶ π̄' ⇓ b̄; H'; R`: the recursive results of a branch, in
order, each the recursor on the field at its position in `ā`, at the weight `ϖ` times the
multiplicity of its binder in `π̄'`, or `↯` when it is erased. -/
inductive EvalResults (P : Program) : {n : Nat} → Multiplicity → Heap → List Nat → Multiplicity →
    TargetBranches n → List Nat → List (Option Nat) → List Multiplicity → List Nat → Heap →
    List Nat → Prop where
  /-- No result.
  RFC: `\mathsf{results}_\Downarrow.\varepsilon` -/
  | nil {ϖ : Multiplicity} {n : Nat} {H : Heap} {E : List Nat} {ρ : Multiplicity}
      {Ns : TargetBranches n} {as : List Nat} : EvalResults P ϖ H E ρ Ns as [] [] [] H []
  /-- An erased result, `↯`, then the others.
  RFC: `\mathsf{results}_\Downarrow.\text{↯}` -/
  | erased {ϖ : Multiplicity} {n : Nat} {H₁ H₂ : Heap} {E : List Nat} {ρ : Multiplicity}
      {Ns : TargetBranches n} {as : List Nat} {ks : List (Option Nat)} {π : Multiplicity}
      {πs : List Multiplicity} {rs : List Nat} {R : List Nat}
      (hs : EvalResults P ϖ (H₁ ++ [.erased]) E ρ Ns as ks πs rs H₂ R) :
      EvalResults P ϖ H₁ E ρ Ns as (none :: ks) (π :: πs) (H₁.length :: rs) H₂ R
  /-- The recursor on the field at the position `j`, then the others.
  RFC: `\mathsf{results}_\Downarrow.\mathsf{rec}` -/
  | recursor {ϖ : Multiplicity} {n : Nat} {H₁ H₂ H₃ : Heap} {E : List Nat} {ρ : Multiplicity}
      {Ns : TargetBranches n} {as : List Nat} {j a r : Nat} {ks : List (Option Nat)}
      {π : Multiplicity} {πs : List Multiplicity} {rs : List Nat} {R₁ R₂ : List Nat}
      (hj : as[j]? = some a) (h : EvalRec P (ϖ * π) H₁ E ρ Ns a r H₂ R₁)
      (hs : EvalResults P ϖ H₂ E ρ Ns as ks πs rs H₃ R₂) :
      EvalResults P ϖ H₁ E ρ Ns as (some j :: ks) (π :: πs) (r :: rs) H₃ (R₁ ++ R₂)

-- ADE: none.
/-- `𝒫; ϖ; H ⊢ a.dᵢ(b̄ ▶ π̄ ◀ ϱ̄) ◀ ψ ⇓ c; H'; R`: the observation by the destructor of the case `i`,
of the ownership at run time `ψ` of its result, at the weight `ϖ`, applied to the arguments at the
addresses `b̄`, at the multiplicities `π̄` and the requirements `ϱ̄`, of the value at the address `a`,
a closure: the branch of the case evaluates in the environment of the closure, with cells for its
state and the arguments, at the multiplicities of its binders times the weight, and its value is
resumed when the branch resumes a state; the uses that the branch makes of each entry of the state
and of each argument, by its cell, must be within the uses that the closure or the observation
allows, the ownership that it gives each entry of the state within the requirement of the entry,
the requirement that it assumes of each argument within the one that the observation passes, and
the ownership of its result the one that the observation expects, and the evaluation is stuck
otherwise. -/
inductive EvalObs (P : Program) : Multiplicity → Heap → Nat → Nat → {c : Nat} →
    ResultOwnership Multiplicity c → List Multiplicity → List Multiplicity → List Nat → Nat → Heap →
    List Nat → Prop where
  /-- RFC: `\beta_\Downarrow` -/
  | beta {ϖ : Multiplicity} {H₁ H₂ H₃ : Heap} {a i c₀ : Nat}
      {ψ₀ : ResultOwnership Multiplicity c₀} {πs₁ ϱs₁ πs₂ ϱs₂ : List Multiplicity}
      {bs : List Nat} {v w : Nat} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
      {ss : List Nat} {o : Resumption} {b c : Nat} {πs ϱs : Fin b → Multiplicity}
      {πs' ϱs' : Fin c → Multiplicity} {ψ : ResultOwnership Multiplicity c}
      {N : Target (n + (b + c))} {R : List Nat}
      (h : H₁[a]? = some (.corec n E Ps πs₁ ϱs₁ ss))
      (hP : Ps.get i = some (o, ⟨b, c, πs, ϱs, πs', ϱs', ψ, N⟩)) (hb : ss.length = b)
      (hc : bs.length = c)
      (hπ₁ : ∀ j : Fin b, ∃ π₁, πs₁[(j : Nat)]? = some π₁ ∧ π₁ ≤ πs j)
      (hπ₂ : ∀ j : Fin c, ∃ π₂, πs₂[(j : Nat)]? = some π₂ ∧ π₂ ≤ πs' j)
      (hϱ₁ : ∀ j : Fin b, ∃ ϱ₁, ϱs₁[(j : Nat)]? = some ϱ₁ ∧ ϱs j * πs j ≤ ϱ₁ * πs j)
      (hϱ₂ : ∀ j : Fin c, ∃ ϱ₂, ϱs₂[(j : Nat)]? = some ϱ₂ ∧ ϱs' j ≤ ϱ₂)
      (hψ : (⟨c₀, ψ₀⟩ : Σ c, ResultOwnership Multiplicity c) = ⟨c, ψ⟩)
      (hw : Eval P ϖ (H₁.bind ((List.ofFn πs ++ List.ofFn πs').map (ϖ * ·)) (ss ++ bs))
        ((List.range' H₁.length (ss ++ bs).length).reverse ++ E) N w H₂ R)
      (hr : EvalResume H₂ n E Ps o ψ w v H₃) : EvalObs P ϖ H₁ a i ψ₀ πs₂ ϱs₂ bs v H₃ R

end

/-! ## Determinism -/

/-- The unpacking of a value is unique. -/
theorem Unpack.det {H : Heap} {k x : Nat} {πs₁ πs₂ ϱs₁ ϱs₂ : List Multiplicity}
    {ss₁ ss₂ : List Nat} :
    Unpack H k x πs₁ ϱs₁ ss₁ → Unpack H k x πs₂ ϱs₂ ss₂ → πs₁ = πs₂ ∧ ϱs₁ = ϱs₂ ∧ ss₁ = ss₂
  | .zero _, .zero _ => ⟨rfl, rfl, rfl⟩
  | .pair h hs, .pair h' hs' => by
    rw [h] at h'
    cases h'
    obtain ⟨rfl, rfl, rfl⟩ := Unpack.det hs hs'
    exact ⟨rfl, rfl, rfl⟩

/-- The resumption of a value is unique. -/
theorem EvalResume.det {H H₁ H₂ : Heap} {n : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
    {o : Resumption} {c : Nat} {ψ : ResultOwnership Multiplicity c} {w v₁ v₂ : Nat} :
    EvalResume H n E Ps o ψ w v₁ H₁ → EvalResume H n E Ps o ψ w v₂ H₂ → v₁ = v₂ ∧ H₁ = H₂
  | .none, .none => ⟨rfl, rfl⟩
  | .none, .done ho _ _ _ | .done ho _ _ _, .none => (ho rfl).elim
  | .next h hs, .next h' hs' => by
    rw [h] at h'
    cases h'
    obtain ⟨rfl, rfl, rfl⟩ := Unpack.det hs hs'
    exact ⟨rfl, rfl⟩
  | .erased h, .erased h' => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl⟩
  | .next h _, .done _ h' _ _ | .done _ h _ _, .next h' _ | .erased h, .done _ h' _ _
  | .done _ h _ _, .erased h' => by
    rw [h] at h'
    cases h'
  | .done _ h _ _, .done _ h' _ _ => by
    rw [h] at h'
    cases h'
    exact ⟨rfl, rfl⟩

mutual

-- ADE: none.
/-- The evaluation is deterministic: a term evaluates to one address, in one heap, reading the same
cells.
RFC: `\mathsf{det}_\Downarrow` -/
theorem Eval.det {P : Program} {ϖ : Multiplicity} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {M : Target n} {a₁ a₂ : Nat} {R₁ R₂ : List Nat} (h₁ : Eval P ϖ H E M a₁ H₁ R₁)
    (h₂ : Eval P ϖ H E M a₂ H₂ R₂) :
    a₁ = a₂ ∧ H₁ = H₂ ∧ R₁ = R₂ :=
  match h₁, h₂ with
  | .var h hc, .var h' hc' => by
    rw [h] at h'
    cases h'
    rw [hc] at hc'
    cases hc'
    exact ⟨rfl, rfl, rfl⟩
  | .const h hM, .const h' hM' => by
    rw [h] at h'
    cases h'
    exact Eval.det hM hM'
  | .erased, .erased => ⟨rfl, rfl, rfl⟩
  | .ctor hs, .ctor hs' => by
    obtain ⟨rfl, rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl, rfl⟩
  | .recursor h hr, .recursor h' hr' => by
    obtain ⟨rfl, rfl, rfl⟩ := Eval.det h h'
    obtain ⟨rfl, rfl, rfl⟩ := EvalRec.det hr hr'
    exact ⟨rfl, rfl, rfl⟩
  | .obs h hs ho, .obs h' hs' ho' => by
    obtain ⟨rfl, rfl, rfl⟩ := Eval.det h h'
    obtain ⟨rfl, rfl, rfl⟩ := EvalAll.det hs hs'
    obtain ⟨rfl, rfl, rfl⟩ := EvalObs.det ho ho'
    exact ⟨rfl, rfl, rfl⟩
  | .corec hs, .corec hs' => by
    obtain ⟨rfl, rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The evaluation of terms is deterministic. -/
theorem EvalAll.det {P : Program} {ϖ : Multiplicity} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {Ms : Targets n} {as₁ as₂ : List Nat} {R₁ R₂ : List Nat} (h₁ : EvalAll P ϖ H E Ms as₁ H₁ R₁)
    (h₂ : EvalAll P ϖ H E Ms as₂ H₂ R₂) : as₁ = as₂ ∧ H₁ = H₂ ∧ R₁ = R₂ :=
  match h₁, h₂ with
  | .nil, .nil => ⟨rfl, rfl, rfl⟩
  | .cons h hs, .cons h' hs' => by
    obtain ⟨rfl, rfl, rfl⟩ := Eval.det h h'
    obtain ⟨rfl, rfl, rfl⟩ := EvalAll.det hs hs'
    exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The elimination of a value by a recursor is deterministic. -/
theorem EvalRec.det {P : Program} {ϖ : Multiplicity} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {ρ : Multiplicity} {Ns : TargetBranches n} {a v₁ v₂ : Nat} {R₁ R₂ : List Nat}
    (h₁ : EvalRec P ϖ H E ρ Ns a v₁ H₁ R₁) (h₂ : EvalRec P ϖ H E ρ Ns a v₂ H₂ R₂) :
    v₁ = v₂ ∧ H₁ = H₂ ∧ R₁ = R₂ :=
  match h₁, h₂ with
  | .iota h hN _ _ _ hr hv, .iota h' hN' _ _ _ hr' hv' => by
    rw [h] at h'
    cases h'
    rw [hN] at hN'
    cases hN'
    obtain ⟨rfl, rfl, rfl⟩ := EvalResults.det hr hr'
    obtain ⟨rfl, rfl, rfl⟩ := Eval.det hv hv'
    exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The evaluation of the recursive results of a branch is deterministic. -/
theorem EvalResults.det {P : Program} {ϖ : Multiplicity} {n : Nat} {H H₁ H₂ : Heap} {E : List Nat}
    {ρ : Multiplicity} {Ns : TargetBranches n} {as : List Nat} {ks : List (Option Nat)}
    {πs' : List Multiplicity} {rs₁ rs₂ : List Nat} {R₁ R₂ : List Nat}
    (h₁ : EvalResults P ϖ H E ρ Ns as ks πs' rs₁ H₁ R₁)
    (h₂ : EvalResults P ϖ H E ρ Ns as ks πs' rs₂ H₂ R₂) : rs₁ = rs₂ ∧ H₁ = H₂ ∧ R₁ = R₂ :=
  match h₁, h₂ with
  | .nil, .nil => ⟨rfl, rfl, rfl⟩
  | .erased hs, .erased hs' => by
    obtain ⟨rfl, rfl, rfl⟩ := EvalResults.det hs hs'
    exact ⟨rfl, rfl, rfl⟩
  | .recursor hj h hs, .recursor hj' h' hs' => by
    rw [hj] at hj'
    cases hj'
    obtain ⟨rfl, rfl, rfl⟩ := EvalRec.det h h'
    obtain ⟨rfl, rfl, rfl⟩ := EvalResults.det hs hs'
    exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

-- ADE: none.
/-- The observation of a value is deterministic. -/
theorem EvalObs.det {P : Program} {ϖ : Multiplicity} {H H₁ H₂ : Heap} {a i c : Nat}
    {ψ : ResultOwnership Multiplicity c} {πs ϱs : List Multiplicity} {bs : List Nat}
    {v₁ v₂ : Nat} {R₁ R₂ : List Nat} (h₁ : EvalObs P ϖ H a i ψ πs ϱs bs v₁ H₁ R₁)
    (h₂ : EvalObs P ϖ H a i ψ πs ϱs bs v₂ H₂ R₂) : v₁ = v₂ ∧ H₁ = H₂ ∧ R₁ = R₂ :=
  match h₁, h₂ with
  | .beta h hP _ _ _ _ _ _ _ hw hr, .beta h' hP' _ _ _ _ _ _ _ hw' hr' => by
    rw [h] at h'
    cases h'
    rw [hP] at hP'
    cases hP'
    obtain ⟨rfl, rfl, rfl⟩ := Eval.det hw hw'
    obtain ⟨rfl, rfl⟩ := EvalResume.det hr hr'
    exact ⟨rfl, rfl, rfl⟩
termination_by structural h₁

end

end Sic.Core
