import Lean.CoreM
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

/-- The declarations among `names` that depend on an axiom outside `allowedAxioms`, by axiom. A
single walk visits once each constant that `names` use, and records who uses it; the declarations
that depend on a forbidden axiom are then those reached from it through the users. A declaration
that depends only on allowed axioms is never in the map, which is empty when the check passes. -/
def forbiddenAxioms (env : Environment) (names : Array Name) : NameMap NameSet := Id.run do
  -- The bodies of the private declarations are those of the module that declares them.
  let env := env.setExporting false
  let mut visited : NameSet := {}
  let mut users : NameMap (Array Name) := {}
  let mut forbidden : Array Name := #[]
  let mut todo := names
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if visited.contains c then continue
    visited := visited.insert c
    -- The constants that `c` uses: those that `collectAxioms` follows.
    let used := match env.find? c with
      | some (.axiomInfo v) => v.type.getUsedConstants
      | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
      | some info => info.type.getUsedConstants ++
          ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      | none => #[]
    if let some (.axiomInfo _) := env.find? c then
      unless allowedAxioms.contains c do forbidden := forbidden.push c
    for d in used do
      users := users.insert d (((users.find? d).getD #[]).push c)
    todo := todo ++ used
  let roots : NameSet := names.foldl (·.insert ·) {}
  let mut result : NameMap NameSet := {}
  for axiom_ in forbidden do
    let mut reached : NameSet := {}
    let mut declarations : NameSet := {}
    let mut pending := #[axiom_]
    while !pending.isEmpty do
      let c := pending.back!
      pending := pending.pop
      if reached.contains c then continue
      reached := reached.insert c
      if roots.contains c then declarations := declarations.insert c
      pending := pending ++ (users.find? c).getD #[]
    result := result.insert axiom_ declarations
  return result

/-- Logs every declaration of the libraries `roots` that depends on an axiom outside `allowedAxioms`,
and tells whether there is one. -/
def checkAxioms (roots : List Name) : CoreM Bool := do
  let env ← getEnv
  let names := env.constants.map₁.toArray.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    if roots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!) then some name else none
  let forbidden := forbiddenAxioms env names
  for (axiom_, declarations) in forbidden do
    for name in declarations do
      IO.eprintln s!"{name} depends on the axiom {axiom_}"
  return !forbidden.isEmpty

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
