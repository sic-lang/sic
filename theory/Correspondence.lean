import Lean.CoreM
import Lean.DeclarationRange
import Lean.DocString
import Lean.Parser.Command
import Lean.Util.Path

/-!
Writes the pages of the correspondence between the RFCs and the formalization: for each file of the
RFCs that names definitions, formulas or rules, a page that gives each name with its formula, as the
RFC writes it, and the source of the declarations whose doc strings give it, as their files write
it, so that a reader compares them on one page; it fails if a doc string gives a name that no RFC
has, so that renaming a formula in an RFC cannot leave the pages behind.

Run with the directory of the RFCs, the URL of their files, the directory of the pages and the
directories of the libraries, `Sic/`, whose modules it imports, as Lake builds them; it prints the
entries of the pages for the summary of the book.
A name ends its line, which may break the formula after it: in the last column of a formula,
`&&(…)`, or after the fraction of a rule, `\;(…)`, as the check `names` of the RFCs requires.
The formula of a name is the part of its block of math between the separators `\\[1em]` that holds
the line of the name, inside the environment of the block.
A doc string gives the names on a line that starts with `RFC:`, each in a code span, written exactly
as the RFC writes it inside its parentheses, such as ``RFC: `\mathsf{op}_p`, `\mathsf{order}_p` ``.
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
  /-- The formula or the rule of the name, as LaTeX for a block of math. -/
  formula : String
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

/-- The names of a block of math, each with its formula: the part of the block between the
separators `\\[1em]` that holds the line of the name, inside the environment of the block, such as
`\begin{aligned}`, if it has one; it fails if a part holds several names. -/
def namesOfMath (block : Array String) : Except String (Array (String × String)) := do
  let (start, body, stop) :=
    if block.size ≥ 2 && block[0]!.trimAsciiStart.startsWith "\\begin{" then
      (#[block[0]!], block.extract 1 (block.size - 1), #[block.back!])
    else (#[], block, #[])
  let separator := "\\\\[1em]"
  let mut parts : Array (Array String) := #[]
  let mut part := #[]
  for line in body do
    let line := line.trimAsciiEnd.toString
    if line.endsWith separator then
      parts := parts.push (part.push (line.dropEnd separator.length).trimAsciiEnd.toString)
      part := #[]
    else
      part := part.push line
  unless part.isEmpty do parts := parts.push part
  let mut names := #[]
  for lines in parts do
    match lines.filterMap nameOfLine with
    | #[name] => names := names.push (name, "\n".intercalate (start ++ lines ++ stop).toList)
    | #[] => pure ()
    | several => throw s!"one formula has several names: {", ".intercalate several.toList}"
  return names

/-- The title and the names of the file `file` of the directory `dir`. -/
def readNames (dir : System.FilePath) (file : String) : IO (String × Array RfcName) := do
  let mut title := file
  let mut heading := ""
  -- The lines of the current block of code, and whether it is a block of math.
  let mut block : Option (Array String) := none
  let mut isMath := false
  let mut names := #[]
  for line in (← IO.FS.lines (dir / file)) do
    if line.startsWith "```" then
      match block with
      | some lines =>
        if isMath then
          match namesOfMath lines with
          | .ok found =>
            for (name, formula) in found do
              names := names.push
                { name, file, anchor := anchorOf heading, section_ := heading, formula }
          | .error message => throw <| IO.userError s!"{file}, {heading}: {message}"
        block := none
      | none =>
        block := some #[]
        isMath := line == "```math"
    else if let some lines := block then
      block := some (lines.push line)
    else if line.startsWith "#" then
      let text := (line.dropWhile (· == '#')).trimAsciiStart.toString
      if line.startsWith "# " then title := text
      heading := text
  return (title, names)

/-- The Markdown files of the RFCs, `text/*.md` and `text/*/*.md`, in the order of their paths. -/
def rfcFiles (dir : System.FilePath) : IO (Array String) := do
  let files ← (dir / "text").walkDir
  let files := files.filterMap fun path =>
    if path.extension == some "md" then
      (path.toString.drop (dir.toString.length + 1)).toString
    else none
  return files.qsort (· < ·)

/-- A declaration that formalizes names of the RFCs, with its source. -/
structure Formalization where
  /-- The name of the declaration. -/
  name : Name
  /-- The module of the declaration. -/
  module : Name
  /-- The source of the declaration, as its file writes it. -/
  source : String

/-- The source of the declaration `decl` in the file `file`, as the file writes it: the lines of its
range, and for a theorem only the statement, which ends with the signature that the parser of Lean
reads in these lines, so that the page shows no proof; a field of a record has no proof. -/
def sourceOf (decl : Name) (file : System.FilePath) : CoreM String := do
  let some ranges ← findDeclarationRanges? decl
    | throwError "{decl} has no position in {file}"
  let lines ← IO.FS.lines file
  let text := "\n".intercalate
    (lines.extract (ranges.range.pos.line - 1) ranges.range.endPos.line).toList
  unless (← getConstInfo decl).isTheorem do return text
  -- A field of a record is a statement without proof, which no command parses alone.
  if (← getEnv).isProjectionFn decl then return text
  let stx ← match Parser.runParserCategory (← getEnv) `command text file.toString with
    | .ok stx => pure stx
    | .error message => throwError "the statement of {decl} does not parse: {message}"
  let some signature := stx.find? (·.isOfKind ``Parser.Command.declSig)
    | throwError "{decl} has no signature"
  let some stop := signature.getTailPos?
    | throwError "the signature of {decl} has no position"
  return (String.Pos.Raw.extract text 0 stop).trimAsciiEnd.toString

/-- The names of the RFCs that a doc string gives: the code spans of its lines that start with
`RFC:`. -/
def namesOfDoc (doc : String) : Array String := Id.run do
  let mut names := #[]
  for line in doc.splitOn "\n" do
    let line := line.trimAscii.toString
    unless line.startsWith "RFC:" do continue
    -- The parts between backticks are the odd ones.
    let parts := line.splitOn "`"
    for i in [0:parts.length] do
      if i % 2 == 1 then names := names.push parts[i]!
  return names

/-- The declarations of the libraries in `dirs`, from their roots, that formalize each name. -/
def declarationsOf (dirs : List (Name × System.FilePath)) :
    CoreM (Std.HashMap String (Array Formalization)) := do
  let env ← getEnv
  let mut result := {}
  for (decl, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let module := env.header.moduleNames[idx.toNat]!
    let some (root, dir) := dirs.find? (·.1.isPrefixOf module) | continue
    let some doc ← findDocString? env decl | continue
    let names := namesOfDoc doc
    if names.isEmpty then continue
    let path := (module.components.drop root.components.length).map (·.toString)
    let file := (path.foldl (· / ·) dir).addExtension "lean"
    let declaration := { name := decl, module, source := ← sourceOf decl file }
    for name in names do
      result := result.insert name ((result.getD name #[]).push declaration)
  return result

/-- The link to the documentation of a declaration, from a page one directory below the book. -/
def declarationLink (decl : Formalization) : String :=
  let path := "/".intercalate (decl.module.components.map (·.toString))
  s!"[`{decl.name}`](../theory/{path}.html#{decl.name})"

/-- The page of the names of one file of an RFC: for each name, its formula, then the source of
each declaration that formalizes it. -/
def page (url title : String) (names : Array RfcName)
    (decls : Std.HashMap String (Array Formalization)) : String := Id.run do
  let mut out := s!"# {title}\n\n"
  out := out ++ s!"Each name of [{title}]({url}/{names[0]!.file}) is given with its formula, then with the source of the declarations that formalize it.\n"
  for n in names do
    out := out ++ s!"\n## $({n.name})$\n\n"
    out := out ++ s!"In [{n.section_}]({url}/{n.file}#{n.anchor}):\n\n$$\n{n.formula}\n$$\n"
    match decls.get? n.name with
      | some ds =>
        for d in ds do
          out := out ++ s!"\n{declarationLink d}:\n\n```lean\n{d.source}\n```\n"
      | none => out := out ++ "\nNot yet formalized.\n"
  return out

/-- Unsafe, since the parser of the statements needs the notations of the imported modules, which
only their environment extensions hold, and loading these runs the initializers of the modules. -/
unsafe def main : List String → IO UInt32
  | rfcs :: url :: out :: dirs@(_ :: _) => do
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let modules ← IO.mkRef #[]
    -- The root of the modules of a directory is its name, as `Sic` for `theory/Sic`.
    let roots := dirs.map fun dir => Name.mkSimple (System.FilePath.mk dir).fileName.get!
    for (dir, root) in dirs.zip roots do
      forEachModuleInDir dir fun module => modules.modify (·.push (root ++ module))
    let env ← importModules ((← modules.get).map ({ module := · })) {} (loadExts := true)
    let (decls, _) ←
      (declarationsOf (roots.zip (dirs.map System.FilePath.mk))).toIO { fileName := "<Correspondence>", fileMap := default } { env }
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
      for d in ds do
        IO.eprintln s!"{d.name} formalizes {name}, which no RFC names"
    return if unknown.isEmpty then 0 else 1
  | _ => do
    IO.eprintln "usage: lean --run Correspondence.lean <RFCs> <URL of their files> <pages> <directory of a library>…"
    return 2
