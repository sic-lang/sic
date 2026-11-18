import Lean.CoreM
import Lean.Util.CollectAxioms
import Lean.Util.Path

/-!
Fails if a declaration of the formalization depends on an axiom other than those of the type theory
of Lean that the proofs need, so that what is proved holds without hidden hypotheses: no `sorry`, no
trust in the compiler, as `native_decide` asks, and no `Classical.choice`, so that the proofs stay
constructive, as the metatheory of a type system, whose proofs compute, should be.

Run with the directory of the library as argument, `Sic/`, it imports every module
found there, as Lake builds them.
-/

open Lean

/-- The axioms that the formalization may use. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

/-- The axioms that the declarations `names` depend on, in a single walk of the constants that they
use, each visited once: `collectAxioms` walks again, for each declaration, every constant that it
uses, which makes the check of a library quadratic in its size. -/
def reachableAxioms (env : Environment) (names : Array Name) : NameSet := Id.run do
  -- The bodies of the private declarations are those of the module that declares them.
  let env := env.setExporting false
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut todo := names
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some (.axiomInfo v) =>
      axioms := axioms.insert c
      todo := todo ++ v.type.getUsedConstants
    | some (.inductInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.ctors.toArray
    | some info =>
      todo := todo ++ info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    | none => pure ()
  return axioms

/-- Logs every declaration of the libraries `roots` that depends on an axiom outside `allowedAxioms`,
and tells whether there is one: one walk finds the axioms of all the declarations, and only when one
of them is not allowed are the declarations walked one by one, to name those that depend on it. -/
def checkAxioms (roots : List Name) : CoreM Bool := do
  let env ← getEnv
  let names := env.constants.map₁.toArray.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    if roots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!) then some name else none
  if (reachableAxioms env names).toList.all allowedAxioms.contains then
    return false
  for name in names do
    for axiom_ in ← collectAxioms name do
      unless allowedAxioms.contains axiom_ do
        IO.eprintln s!"{name} depends on the axiom {axiom_}"
  return true

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
