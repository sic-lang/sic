import Lean.CoreM
import Lean.Util.Path
import Rfc

/-!
Writes the pages of the correspondence between the RFCs and the formalization: for each file of the
RFCs that names definitions, formulas or rules, a page that lists each name, with a link to its
section in the RFC and links to the declarations whose attribute `rfc` gives it, and fails if such an
attribute gives a name that no RFC has, so that renaming a formula in an RFC cannot leave the pages
behind.

Run with the directory of the RFCs, the URL of their files, the directory of the pages and the
directories of the libraries, `Sic/`, whose modules it imports, as Lake builds them; it prints the
entries of the pages for the summary of the book.
A name ends its line, which may break the formula after it: in the last column of a formula,
`&&(…)`, or after the fraction of a rule, `\;(…)`, as the check `names` of the RFCs requires.
-/

open Lean

/-- A name of an RFC, with the file and the anchor of the section where it appears. -/
structure RfcName where
  /-- The name, as the RFC writes it in LaTeX inside its parentheses, `\mathsf{op}_p`. -/
  name : String
  /-- The path of the file, from the directory of the RFCs. -/
  file : String
  /-- The anchor of the section, as GitHub makes it from the heading. -/
  anchor : String
  /-- The heading of the section. -/
  section_ : String
  deriving Inhabited

/-- The name that ends the line, after `&&(` or `\;(` and before `)`, if there is one. -/
def nameOfLine (line : String) : Option String := Id.run do
  let mut rest := line.trimAsciiEnd.toString
  for suffix in ["\\\\[1em]", "\\\\"] do
    if rest.endsWith suffix then
      rest := (rest.dropEnd suffix.length).trimAsciiEnd.toString
      break
  unless rest.endsWith ")" do return none
  for marker in ["&&(", "\\;("] do
    let parts := rest.splitOn marker
    if parts.length > 1 then
      let name := (parts.getLast!.dropEnd 1).toString
      if name.all (· != '(') && name.all (· != ')') then return some name
  return none

/-- The anchor that GitHub gives a heading: lower case, a hyphen for each space, and only the
letters, the digits, the hyphens and the underscores. -/
def anchorOf (heading : String) : String :=
  String.map (fun c => if c == ' ' then '-' else c)
    (String.ofList (heading.toLower.toList.filter fun c => c.isAlphanum || c == ' ' || c == '-' || c == '_'))

/-- The title and the names of the file `file` of the directory `dir`. -/
def readNames (dir : System.FilePath) (file : String) : IO (String × Array RfcName) := do
  let mut title := file
  let mut heading := ""
  let mut inCode := false
  let mut names := #[]
  for line in (← IO.FS.lines (dir / file)) do
    if line.startsWith "```" then
      inCode := !inCode
    else if !inCode && line.startsWith "#" then
      let text := (line.dropWhile (· == '#')).trimAsciiStart.toString
      if line.startsWith "# " then title := text
      heading := text
    else if inCode then
      if let some name := nameOfLine line then
        names := names.push { name, file, anchor := anchorOf heading, section_ := heading }
  return (title, names)

/-- The Markdown files of the RFCs, `text/*.md` and `text/*/*.md`, in the order of their paths. -/
def rfcFiles (dir : System.FilePath) : IO (Array String) := do
  let files ← (dir / "text").walkDir
  let files := files.filterMap fun path =>
    if path.extension == some "md" then
      (path.toString.drop (dir.toString.length + 1)).toString
    else none
  return files.qsort (· < ·)

/-- The declarations of the libraries `roots` that formalize each name, with their modules. -/
def declarationsOf (roots : List Name) : CoreM (Std.HashMap String (Array (Name × Name))) := do
  let env ← getEnv
  let mut result := {}
  for (decl, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let module := env.header.moduleNames[idx.toNat]!
    unless roots.any (·.isPrefixOf module) do continue
    let some names := Rfc.rfcAttr.getParam? env decl | continue
    for name in names do
      result := result.insert name ((result.getD name #[]).push (decl, module))
  return result

/-- The link to the documentation of a declaration, from a page one directory below the book. -/
def declarationLink (decl module : Name) : String :=
  let path := "/".intercalate (module.components.map (·.toString))
  s!"[`{decl}`](../theory/{path}.html#{decl})"

/-- The page of the names of one file of an RFC. -/
def page (url title : String) (names : Array RfcName)
    (decls : Std.HashMap String (Array (Name × Name))) : String := Id.run do
  let mut out := s!"# {title}\n\n"
  out := out ++ s!"Each name of [{title}]({url}/{names[0]!.file}) is formalized by the declarations of its row.\n\n"
  out := out ++ "| Name | Section | Formalization |\n| --- | --- | --- |\n"
  for n in names do
    let formalization := match decls.get? n.name with
      | some ds => ", ".intercalate (ds.toList.map fun (d, m) => declarationLink d m)
      | none => "Not yet"
    out := out ++ s!"| $({n.name})$ | [{n.section_}]({url}/{n.file}#{n.anchor}) | {formalization} |\n"
  return out

def main : List String → IO UInt32
  | rfcs :: url :: out :: dirs@(_ :: _) => do
    initSearchPath (← findSysroot)
    let modules ← IO.mkRef #[`Rfc]
    -- The root of the modules of a directory is its name, as `Sic` for `theory/Sic`.
    let roots := dirs.map fun dir => Name.mkSimple (System.FilePath.mk dir).fileName.get!
    for (dir, root) in dirs.zip roots do
      forEachModuleInDir dir fun module => modules.modify (·.push (root ++ module))
    let env ← importModules ((← modules.get).map ({ module := · })) {}
    let (decls, _) ←
      (declarationsOf roots).toIO { fileName := "<Correspondence>", fileMap := default } { env }
    let mut known : Std.HashSet String := {}
    IO.FS.createDirAll out
    for file in ← rfcFiles rfcs do
      let (title, names) ← readNames rfcs file
      if names.isEmpty then continue
      known := names.foldl (·.insert ·.name) known
      let target := System.FilePath.mk out / (file.drop "text/".length).toString
      if let some parent := target.parent then IO.FS.createDirAll parent
      IO.FS.writeFile target (page url title names decls)
      IO.println s!"- [{title}]({(file.drop "text/".length).toString})"
    let unknown := decls.toList.filter (!known.contains ·.1)
    for (name, ds) in unknown do
      for (d, _) in ds do
        IO.eprintln s!"{d} formalizes {name}, which no RFC names"
    return if unknown.isEmpty then 0 else 1
  | _ => do
    IO.eprintln "usage: lean --run Correspondence.lean <RFCs> <URL of their files> <pages> <directory of a library>…"
    return 2
