import Lake.Toml
import Lean.Util.Path

/-!
Checks the imports of the modules of a library against the rules of `imports.toml`, and writes the
page of the graph of their imports.

A rule names modules, each with the modules below it, such as `Sic.Core.Usage.Renaming` below
`Sic.Core.Usage`, and either the modules they must not import or the only modules they may import,
and fails if one of them imports a module that it forbids or does not allow, directly or through
other modules, which it shows by the path of the imports from the one to the other; a rule or a
group that names no module fails too, so that renaming a module cannot leave a rule behind.
The imports are those of the modules as Lake builds them, so that the check reads the graph that
Lean uses, not a parse of the sources.

The page draws the direct imports of the library as Mermaid flowcharts, an arrow going up from each
module or group to each one it imports, so that the foundations are at the top: one flowchart of
the groups of `imports.toml`, then one for the modules of each group, with a node for each other
group that they import; every module belongs to exactly one group.

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

/-- The imports that a rule constrains, by the modules it names, each with the modules below it. -/
inductive Imports where
  /-- The modules must not import these modules. -/
  | forbidden (names : Array Name)
  /-- The modules import only these modules. -/
  | allowed (names : Array Name)

/-- The modules that the imports name. -/
def Imports.names : Imports → Array Name
  | .forbidden names | .allowed names => names

/-- Whether the imports exclude the module: a module that they forbid, or that they do not allow. -/
def Imports.excludes : Imports → Name → Bool
  | .forbidden names, module => names.any (·.isPrefixOf module)
  | .allowed names, module => !names.any (·.isPrefixOf module)

/-- A rule: no module of `modules` imports, directly or not, a module that `imports` excludes. -/
structure Rule where
  /-- Why the rule holds, which the page and the failures give. -/
  reason : String
  /-- The modules that the rule constrains, each with the modules below it. -/
  modules : Array Name
  /-- The imports that the rule forbids or allows them. -/
  imports : Imports

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
    let imports ← match ← t.decode? `forbidden, ← t.decode? `allowed with
      | some names, none => pure (Imports.forbidden names)
      | none, some names => pure (Imports.allowed names)
      | _, _ => throwDecodeErrorAt v.ref "a rule needs exactly one of the keys forbidden and allowed"
    return { reason := ← t.decode `reason, modules := ← t.decode `modules, imports }

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
    for name in rule.modules ++ rule.imports.names do
      unless modules.any name.covers do
        failures := failures.push s!"a rule names {name}, which is no module: {rule.reason}"
    for module in modules do
      unless rule.modules.any (·.covers module) do continue
      if let some path := pathTo graph module rule.imports.excludes then
        failures := failures.push
          s!"{" → ".intercalate (path.map toString)}, which the rule excludes: {rule.reason}"
  return failures

/-- The page of the graphs: the direct imports between the groups as a Mermaid flowchart, then those
of the modules of each group, then the rules. -/
def page (rules : Rules) (modules : Array Name) (graph : Std.HashMap Name (Array Name)) : String :=
  Id.run do
  -- The index of the group of a module, which `checkRules` requires to be unique.
  let groupOf (module : Name) : Nat :=
    rules.groups.findIdx (·.modules.any (·.covers module))
  let id (module : Name) : String := s!"n{modules.idxOf module}"
  -- The start of a flowchart, drawn at its own size rather than shrunk to the width of the page,
  -- which would shrink its text with it.
  let flowchart := #[
    "```mermaid",
    "---",
    "config:",
    "  flowchart:",
    "    useMaxWidth: false",
    "---",
    "flowchart BT"]
  let mut lines := #[
    "# Imports",
    "",
    "The modules of `Sic/` are grouped by subject, and import each other as the graphs of this page show, an arrow going up from a module or a group to each one it imports, so that the foundations are at the top.",
    "",
    "## Groups",
    "",
    "The groups import each other as the graph below shows, a group importing another when one of its modules imports a module of the other.",
    ""] ++ flowchart
  for (group, index) in rules.groups.zipIdx do
    lines := lines.push s!"  g{index}[\"{group.name}\"]"
  for index in [0:rules.groups.size] do
    let imported := modules.filter (groupOf · == index) |>.flatMap (graph.getD · #[])
      |>.map groupOf |>.filter (· != index)
    for target in [0:rules.groups.size] do
      if imported.contains target then
        lines := lines.push s!"  g{index} --> g{target}"
  lines := lines ++ #[
    "```",
    "",
    "## Modules",
    "",
    "The modules of each group import each other, and the modules of the other groups, as the graph of its section shows, a rounded box standing for the modules of another group.",
    ""]
  for (group, index) in rules.groups.zipIdx do
    let members := modules.filter (groupOf · == index)
    let others := members.flatMap (graph.getD · #[]) |>.map groupOf |>.filter (· != index)
    lines := lines ++ #[
      s!"### {group.name}",
      "",
      s!"The modules of the group {group.name} import the modules below.",
      ""] ++ flowchart
    for module in members do
      lines := lines.push s!"  {id module}[\"{module}\"]"
    for (other, otherIndex) in rules.groups.zipIdx do
      if others.contains otherIndex then
        lines := lines.push s!"  g{otherIndex}([\"{other.name}\"])"
    for module in members do
      let imports := graph.getD module #[]
      for imported in imports do
        if groupOf imported == index then
          lines := lines.push s!"  {id module} --> {id imported}"
      for otherIndex in [0:rules.groups.size] do
        if otherIndex != index && imports.any (groupOf · == otherIndex) then
          lines := lines.push s!"  {id module} --> g{otherIndex}"
    lines := lines ++ #["```", ""]
  lines := lines ++ #[
    "## Rules",
    "",
    "The check `imports` fails if a module imports, directly or through other modules, a module that a rule forbids it or does not allow it, each module standing for the modules below it:",
    ""]
  for rule in rules.rules do
    let names (ms : Array Name) := ", ".intercalate (ms.toList.map fun m => s!"`{m}`")
    lines := lines.push <| match rule.imports with
      | .forbidden ms =>
        s!"- No module of {names rule.modules} imports a module of {names ms}: {rule.reason}."
      | .allowed ms =>
        s!"- The modules of {names rule.modules} import only modules of {names ms}: {rule.reason}."
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
