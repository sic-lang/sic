import Lake.Toml
import Lean.Util.Path

/-!
Checks the imports of the modules of a library against the rules of `imports.toml`, and writes the
page of the graph of their imports.

A rule names modules and the modules they must not import, each with the modules below it, such as
`Sic.Core.Usage.Renaming` below `Sic.Core.Usage`, and fails if one of them imports one of the others,
directly or through other modules, which it shows by the path of the imports from the one to the
other; a rule or a group that names no module fails too, so that renaming a module cannot leave a
rule behind.
The imports are those of the modules as Lake builds them, so that the check reads the graph that
Lean uses, not a parse of the sources.

The page draws the direct imports of the library as a Mermaid flowchart, an arrow from each module
to each module it imports, each group of `imports.toml` as a subgraph; every module belongs to
exactly one group.

Run with the file of the rules, the file of the page and the directory of the library, `Sic/`,
whose modules it imports, as Lake builds them.
-/

open Lean Lake Toml

/-- A group of modules, drawn as a subgraph of the page. -/
structure Group where
  /-- The title of the subgraph. -/
  name : String
  /-- The modules of the group, each with the modules below it. -/
  modules : Array Name

/-- A rule: no module of `modules` imports a module of `forbidden`, directly or not. -/
structure Rule where
  /-- Why the rule holds, which the page and the failures give. -/
  reason : String
  /-- The modules that the rule constrains, each with the modules below it. -/
  modules : Array Name
  /-- The modules they must not import, each with the modules below it. -/
  forbidden : Array Name

/-- The groups and the rules of `imports.toml`. -/
structure Rules where
  /-- The groups, in the order of the file. -/
  groups : Array Group
  /-- The rules, in the order of the file. -/
  rules : Array Rule

instance : DecodeToml Group where
  decode v := do
    let t ← v.decodeTable
    return { name := ← t.decode `name, modules := ← t.decode `modules }

instance : DecodeToml Rule where
  decode v := do
    let t ← v.decodeTable
    return {
      reason := ← t.decode `reason
      modules := ← t.decode `modules
      forbidden := ← t.decode `forbidden }

/-- Reads the groups and the rules of a TOML file. -/
def readRules (file : System.FilePath) : IO Rules := do
  let ictx := Parser.mkInputContext (← IO.FS.readFile file) file.toString
  let table ← match ← (loadToml ictx).toBaseIO with
    | .ok table => pure table
    | .error log => throw <| IO.userError s!"{file}: {← log.toList.mapM (·.toString)}"
  let decode : EDecodeM Rules := do
    return { groups := ← table.decode `group, rules := ← table.decode `rule }
  match decode #[] with
  | .ok rules _ => return rules
  | .error _ errors => throw <| IO.userError s!"{file}: {errors.toList.map (·.msg)}"

/-- Whether the module is `name` or below it. -/
def Lean.Name.covers (name module : Name) : Bool := name.isPrefixOf module

/-- The path of the imports from `start` to a module that `target` holds, through the modules of
`graph`, if there is one: a breadth-first search, which gives a shortest path. -/
def pathTo (graph : Std.HashMap Name (Array Name)) (start : Name) (target : Name → Bool) :
    Option (List Name) := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  let mut queue := #[start]
  let mut index := 0
  while h : index < queue.size do
    let module := queue[index]
    index := index + 1
    for imported in graph.getD module #[] do
      if imported == start || parent.contains imported then continue
      parent := parent.insert imported module
      if target imported then
        let mut path := [imported]
        let mut current := imported
        while current != start do
          current := parent.getD current start
          path := current :: path
        return some path
      queue := queue.push imported
  return none

/-- The failures of the rules on the graph of the modules: for each module of a rule, the path to
a module it must not import, if any. -/
def checkRules (rules : Rules) (modules : Array Name) (graph : Std.HashMap Name (Array Name)) :
    Array String := Id.run do
  let mut failures := #[]
  for group in rules.groups do
    for name in group.modules do
      unless modules.any name.covers do
        failures := failures.push s!"the group {group.name} names {name}, which is no module"
  for module in modules do
    match (rules.groups.filter fun group => group.modules.any (·.covers module)).toList with
    | [_] => pure ()
    | [] => failures := failures.push s!"{module} belongs to no group"
    | groups =>
      failures := failures.push s!"{module} belongs to several groups: {groups.map (·.name)}"
  for rule in rules.rules do
    for name in rule.modules ++ rule.forbidden do
      unless modules.any name.covers do
        failures := failures.push s!"a rule names {name}, which is no module: {rule.reason}"
    for module in modules do
      unless rule.modules.any (·.covers module) do continue
      if let some path := pathTo graph module fun m => rule.forbidden.any (·.covers m) then
        failures := failures.push
          s!"{" → ".intercalate (path.map toString)}, which the rule forbids: {rule.reason}"
  return failures

/-- The page of the graph: the direct imports as a Mermaid flowchart, a subgraph for each group,
then the rules. -/
def page (rules : Rules) (modules : Array Name) (graph : Std.HashMap Name (Array Name)) : String :=
  Id.run do
  let id (module : Name) : String := s!"n{modules.idxOf module}"
  let mut lines := #[
    "# Imports",
    "",
    "The modules of `Sic/` import each other as the graph below shows, an arrow going from a module to each module it imports, and the boxes grouping the modules by subject.",
    "",
    "```mermaid",
    "flowchart TD"]
  for (group, index) in rules.groups.zipIdx do
    lines := lines.push s!"  subgraph g{index} [\"{group.name}\"]"
    for module in modules do
      if group.modules.any (·.covers module) then
        lines := lines.push s!"    {id module}[\"{module}\"]"
    lines := lines.push "  end"
  for module in modules do
    for imported in graph.getD module #[] do
      lines := lines.push s!"  {id module} --> {id imported}"
  lines := lines ++ #[
    "```",
    "",
    "The check `imports` fails if a module imports, directly or through other modules, a module that a rule forbids it, each module standing for the modules below it:",
    ""]
  for rule in rules.rules do
    let names (ms : Array Name) := ", ".intercalate (ms.toList.map fun m => s!"`{m}`")
    lines := lines.push s!"- No module of {names rule.modules} imports a module of {names rule.forbidden}: {rule.reason}."
  return "\n".intercalate lines.toList ++ "\n"

def main : List String → IO UInt32
  | [rulesFile, pageFile, dir] => do
    initSearchPath (← findSysroot)
    let rules ← readRules rulesFile
    -- The root of the modules of the directory is its name, as `Sic` for `theory/Sic`.
    let root := Name.mkSimple (System.FilePath.mk dir).fileName.get!
    let found ← IO.mkRef #[]
    forEachModuleInDir dir fun module => found.modify (·.push { module := root ++ module })
    let env ← importModules (← found.get) {}
    -- The modules of the library, sorted, and the modules of the library that each one imports.
    let modules := (env.header.moduleNames.filter root.isPrefixOf).qsort Name.lt
    let mut graph : Std.HashMap Name (Array Name) := {}
    for (module, data) in env.header.moduleNames.zip env.header.moduleData do
      if root.isPrefixOf module then
        let imports := (data.imports.map (·.module)).filter root.isPrefixOf
        graph := graph.insert module (imports.qsort Name.lt)
    IO.FS.writeFile pageFile (page rules modules graph)
    let failures := checkRules rules modules graph
    for failure in failures do IO.eprintln failure
    return if failures.isEmpty then 0 else 1
  | _ => do
    IO.eprintln "usage: lean --run Imports.lean <rules> <page> <directory of a library>"
    return 2
