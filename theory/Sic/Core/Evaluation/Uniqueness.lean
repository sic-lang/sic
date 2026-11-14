module

public import Sic.Core.Erasure.Ownership
public import Sic.Core.Evaluation.Paths

/-!
# Uniqueness

The claims of the uniqueness at run time of annex 17 of RFC 36: a value owned alone claims the
addresses that it holds alone, `H; g ⊢ ℓ ⊳ b`, itself, the fields and the entries of the state that
it stores at the requirement `1` and at a multiplicity other than `0`, the cells of the variables of
its scope that its closure owns alone and reads, as the annotation `g` of the heap gives the
ownership and the usage of its scope, and what the value bound by each cell that it claims claims.
The uniqueness at run time compares the claims of the values owned alone with the references that
the reaches of `Sic/Core/Evaluation/Paths.lean` count: an address claimed is referred to at most
once.
A claim follows a reference that the reach of the value counts, so that what a value claims is in
its reach: the claims of a closure read the usage of its scope in the annotation, which its reach
reads too.

The annotation is valid for a heap, `⊢_Ω H ◀ g`, when the branches of each closure have their
ownership under the ownership of its scope, and their usage under the usage of its scope, which the
evaluation gives each closure that it builds, from the corecursor that builds it; the program has
its ownership, `⊢ 𝒫 ◀ Ω`, when each of its bodies has the ownership that `Ω` gives its constant.

ADE have no ownership, and no uniqueness at run time.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading Sic.Math

-- ADE: none.
/-- `H; g ⊢ ℓ ⊳ b`: the value at the address `ℓ` of the heap `H`, annotated by `g`, claims the
address `b`, which it holds alone when it is owned alone. -/
inductive Heap.Claims (H : Heap) (g : Heap.Annotation) : Nat → Nat → Prop where
  /-- A value claims itself.
  RFC: `\mathsf{claim}.\mathsf{self}` -/
  | self (ℓ : Nat) : Heap.Claims H g ℓ ℓ
  /-- A constructor claims what each field that it stores at the requirement `1` and at a
  multiplicity other than `0` claims.
  RFC: `\mathsf{claim}.c` -/
  | ctor {ℓ i k a b : Nat} {πs ϱs : List Multiplicity} {as : List Nat} {π : Multiplicity}
      (h : H[ℓ]? = some (.ctor i πs ϱs as)) (ha : as[k]? = some a) (hπ : πs[k]? = some π)
      (hπ₀ : π ≠ .zero) (hϱ : ϱs[k]? = some .one) (hb : Heap.Claims H g a b) :
      Heap.Claims H g ℓ b
  /-- A closure claims what each entry of its state that it stores at the requirement `1` and at a
  multiplicity other than `0` claims.
  RFC: `\mathsf{claim}.\mathsf{state}` -/
  | state {ℓ n k a b : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
      {πs ϱs : List Multiplicity} {as : List Nat} {π : Multiplicity}
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (ha : as[k]? = some a) (hπ : πs[k]? = some π)
      (hπ₀ : π ≠ .zero) (hϱ : ϱs[k]? = some .one) (hb : Heap.Claims H g a b) :
      Heap.Claims H g ℓ b
  /-- A closure claims what the cell of each variable of its scope that it owns alone and reads,
  as the annotation gives the ownership and the usage of its scope, claims.
  RFC: `\mathsf{claim}.\mathsf{scope}` -/
  | scope {ℓ n c b : Nat} {E : List Nat} {Ps : TargetCorecBranches n}
      {πs ϱs : List Multiplicity} {as : List Nat} (x : Fin n)
      (h : H[ℓ]? = some (.corec n E Ps πs ϱs as)) (hc : E[(x : Nat)]? = some c)
      (hδ : g.usage ℓ n x ≠ .zero) (hφ : g.ownership ℓ n x = .one) (hb : Heap.Claims H g c b) :
      Heap.Claims H g ℓ b
  /-- A cell claims what the value that it binds claims.
  RFC: `\mathsf{claim}.\mathsf{bind}` -/
  | cell {c a b : Nat} {π : Multiplicity} (h : H[c]? = some (.cell π a))
      (hb : Heap.Claims H g a b) : Heap.Claims H g c b

-- ADE: none.
/-- `H; g ⊢ E ⊳_{φ;ν} b`: a term that owns the variables of the environment `E` as `φ` gives and
reads them as `ν` allows claims the address `b`, which the cell of a variable that it owns alone and
reads claims.
RFC: `\mathsf{claim}_E` -/
def Heap.EnvClaims (H : Heap) (g : Heap.Annotation) {n : Nat} (E : List Nat)
    (φ ν : MultiplicityVector n) (b : Nat) : Prop :=
  ∃ (x : Fin n) (c : Nat), E[(x : Nat)]? = some c ∧ φ x = .one ∧ ν x ≠ .zero ∧
    Heap.Claims H g c b

-- ADE: none.
/-- `⊢_Ω H ◀ g`: the annotation `g` is valid for the heap `H`: the branches of each closure have
their ownership under the ownership of its scope, given the ownership `Ω` of each constant, and
their usage under the usage of its scope.
RFC: `\mathsf{valid}_g` -/
def Heap.Annotation.Valid (Ω : Name → Multiplicity) (H : Heap) (g : Heap.Annotation) : Prop :=
  ∀ ℓ n E Ps πs ϱs as, H[ℓ]? = some (.corec n E Ps πs ϱs as) →
    TargetCorecBranches.Ownership Ω (g.ownership ℓ n) Ps ∧ TargetCorecBranches.Usage (g.usage ℓ n) Ps

-- ADE: none.
/-- `⊢ 𝒫 ◀ Ω`: each body of the program, a closed term, has the ownership that `Ω` gives its
constant.
RFC: `\mathsf{own}_{\mathcal{P}}` -/
def Program.Ownership (P : Program) (Ω : Name → Multiplicity) : Prop :=
  ∀ f qs ps M, P f qs ps = some M → Target.Ownership Ω (𝟘ᵛ : MultiplicityVector 0) (Ω f) M

end Sic.Core
