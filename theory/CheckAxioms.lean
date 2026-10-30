import Lean.CoreM
import Lean.Util.CollectAxioms
import Lean.Util.Path

/-!
Fails if a declaration of the formalization depends on an axiom other than those of the type theory
of Lean that the proofs need, so that what is proved holds without hidden hypotheses: no `sorry`, no
trust in the compiler, as `native_decide` asks, and no `Classical.choice`, so that the proofs stay
constructive, as the metatheory of a type system, whose proofs compute, should be.

Run with the directories of the libraries as arguments, `Sic/` and `SicTest/`, it imports every module
found there, as Lake builds them.
-/

open Lean

/-- The axioms that the formalization may use. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

/-- Logs every declaration of the libraries `roots` that depends on an axiom outside `allowedAxioms`,
and tells whether there is one. -/
def checkAxioms (roots : List Name) : CoreM Bool := do
  let env ← getEnv
  let mut failed := false
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless roots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!) do continue
    for axiom_ in ← collectAxioms name do
      unless allowedAxioms.contains axiom_ do
        IO.eprintln s!"{name} depends on the axiom {axiom_}"
        failed := true
  return failed

def main : List String → IO UInt32
  | [] => do
    IO.eprintln "usage: lean --run CheckAxioms.lean <directory of a library>…"
    return 2
  | dirs => do
    initSearchPath (← findSysroot)
    let modules ← IO.mkRef #[]
    -- The root of the modules of a directory is its name, as `Sic` for `theory/Sic`.
    let roots := dirs.map fun dir => Name.mkSimple (System.FilePath.mk dir).fileName.get!
    for (dir, root) in dirs.zip roots do
      forEachModuleInDir dir fun module => modules.modify (·.push { module := root ++ module })
    let env ← importModules (← modules.get) {}
    let (failed, _) ←
      (checkAxioms roots).toIO { fileName := "<CheckAxioms>", fileMap := default } { env }
    return if failed then 1 else 0
