import Lean.Elab.Command
import Sic

/-!
Fails if a declaration of the formalization depends on an axiom other than those of the type theory
of Lean that the proofs need, so that what is proved holds without hidden hypotheses: no `sorry`, no
trust in the compiler, as `native_decide` asks, and no `Classical.choice`, so that the proofs stay
constructive, as the metatheory of a type system, whose proofs compute, should be.
-/

open Lean Elab Command

/-- The axioms that the formalization may use. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#check_axioms" : command => do
  let env ← getEnv
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`Sic).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    for axiom_ in ← liftCoreM (collectAxioms name) do
      unless allowedAxioms.contains axiom_ do
        logError m!"{name} depends on the axiom {axiom_}"

#check_axioms
