import Lean
import Lean.Elab.Import
import Lean.Util.Path
import Std

open Lean
open Lean.Elab

structure Config where
  rootDir : System.FilePath := "."
  outFile : System.FilePath := "import_graph.json"
  maxDepth : Nat := 4
  deriving Inhabited

def parseArgs (args : List String) : IO Config := do
  let rec go (cfg : Config) (args : List String) : IO Config := do
    match args with
    | [] => return cfg
    | "--root" :: value :: rest =>
        go { cfg with rootDir := value } rest
    | "--out" :: value :: rest =>
        go { cfg with outFile := value } rest
    | "--max-depth" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with maxDepth := n } rest
        | none => throw <| IO.userError s!"Invalid --max-depth value: {value}"
    | flag :: _ =>
        throw <| IO.userError s!"Unknown argument: {flag}"
  go {} args

def getLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mathlibDir := root / "Mathlib"
  if !(← mathlibDir.isDir) then
    throw <| IO.userError s!"Expected Mathlib directory at {mathlibDir}"
  let files ← mathlibDir.walkDir
  let leanFiles := files.filter (·.extension == some "lean")
  return leanFiles.qsort (fun a b => a.toString < b.toString)

def relativeToRoot (root : System.FilePath) (path : System.FilePath) : IO System.FilePath := do
  let root ← IO.FS.realPath root
  let path ← IO.FS.realPath path
  let mut rootStr := root.normalize.toString
  let pathStr := path.normalize.toString
  if !rootStr.endsWith System.FilePath.pathSeparator.toString then
    rootStr := rootStr ++ System.FilePath.pathSeparator.toString
  if !rootStr.isPrefixOf pathStr then
    throw <| IO.userError s!"File '{pathStr}' is not under root '{rootStr}'"
  let rel := (pathStr.drop rootStr.length).toString
  return System.FilePath.mk rel

def dropExtension (path : System.FilePath) : System.FilePath :=
  match path.extension with
  | none => path
  | some ext =>
      let pathStr := path.toString
      let suffix := "." ++ ext
      if pathStr.endsWith suffix then
        System.FilePath.mk ((pathStr.dropEnd suffix.length).toString)
      else
        path

def moduleNameFromPath (path : System.FilePath) : Name :=
  path.components.foldl (fun acc comp => Name.mkStr acc comp) Name.anonymous

def moduleNameToPath (mod : Name) : System.FilePath :=
  let path := mod.components.foldl (fun acc comp => acc / comp) (System.FilePath.mk "")
  path.withExtension "lean"

def sortNames (names : Array Name) : Array Name :=
  names.qsort (fun a b => a.toString < b.toString)

def nameArrayToJson (names : Array Name) : Json :=
  Json.arr <| names.map (fun name => toJson name.toString)

def levelsToJson (levels : Array (Array Name)) : Json :=
  Json.arr <| levels.map nameArrayToJson

def bfsLevels (adj : Name → Array Name) (start : Name) (maxDepth : Nat) : Array (Array Name) := Id.run do
  let mut visited : Std.HashSet Name := {}
  visited := visited.insert start
  let mut current : Array Name := #[start]
  let mut levels : Array (Array Name) := #[]
  for _ in [:maxDepth] do
    let mut next : Array Name := #[]
    for node in current do
      for nbr in adj node do
        if !visited.contains nbr then
          visited := visited.insert nbr
          next := next.push nbr
    levels := levels.push (sortNames next)
    current := next
  return levels

structure NodeData where
  module : Name
  path : System.FilePath
  imports : Array Name
  importsInRoot : Array Name
  importersInRoot : Array Name
  importsByDepth : Array (Array Name)
  importersByDepth : Array (Array Name)

def nodeToJson (node : NodeData) : Json :=
  Json.mkObj [
    ("module", toJson node.module.toString),
    ("path", toJson node.path.toString),
    ("imports", nameArrayToJson node.imports),
    ("imports_in_root", nameArrayToJson node.importsInRoot),
    ("importers_in_root", nameArrayToJson node.importersInRoot),
    ("imports_by_depth", levelsToJson node.importsByDepth),
    ("importers_by_depth", levelsToJson node.importersByDepth)
  ]

def pushMapArray (map : Std.HashMap Name (Array Name)) (key : Name) (value : Name) :
    Std.HashMap Name (Array Name) :=
  let current := map.findD key #[]
  map.insert key (current.push value)

def parseImportsForFile (file : System.FilePath) : IO (Array Name) := do
  let contents ← IO.FS.readFile file
  let (imports, _, messages) ← parseImports contents (some file.toString)
  if messages.hasErrors then
    for msg in messages.toArray do
      let rendered ← msg.toString
      IO.eprintln s!"[import_graph] {rendered}"
  return imports.map (·.module)

unsafe def main (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  let files ← getLeanFiles cfg.rootDir
  let mut moduleToPath : Std.HashMap Name System.FilePath := {}
  let mut fileEntries : Array (System.FilePath × Name) := #[]
  for file in files do
    let relativePath ← relativeToRoot cfg.rootDir file
    let moduleName := moduleNameFromPath (dropExtension relativePath)
    moduleToPath := moduleToPath.insert moduleName relativePath
    fileEntries := fileEntries.push (file, moduleName)

  let mut nodesRaw : Array (Name × System.FilePath × Array Name × Array Name) := #[]
  for (file, moduleName) in fileEntries do
    let imports ← parseImportsForFile file
    let importsSorted := sortNames imports
    let importsInRoot := importsSorted.filter (fun name => moduleToPath.contains name)
    let relativePath := moduleToPath.findD moduleName (moduleNameToPath moduleName)
    nodesRaw := nodesRaw.push (moduleName, relativePath, importsSorted, importsInRoot)

  let mut importsMap : Std.HashMap Name (Array Name) := {}
  let mut importersMap : Std.HashMap Name (Array Name) := {}
  for (moduleName, _path, _imports, importsInRoot) in nodesRaw do
    importsMap := importsMap.insert moduleName importsInRoot
    for imp in importsInRoot do
      importersMap := pushMapArray importersMap imp moduleName

  let mut nodes : Array NodeData := #[]
  for (moduleName, relativePath, imports, importsInRoot) in nodesRaw do
    let importersInRoot := sortNames (importersMap.findD moduleName #[])
    let importsByDepth := bfsLevels (fun name => importsMap.findD name #[]) moduleName cfg.maxDepth
    let importersByDepth := bfsLevels (fun name => importersMap.findD name #[]) moduleName cfg.maxDepth
    nodes := nodes.push {
      module := moduleName
      path := relativePath
      imports := imports
      importsInRoot := importsInRoot
      importersInRoot := importersInRoot
      importsByDepth := importsByDepth
      importersByDepth := importersByDepth
    }

  let parent := cfg.outFile.parent.getD "."
  IO.FS.createDirAll parent
  let output :=
    Json.mkObj [
      ("root", toJson cfg.rootDir.toString),
      ("max_depth", toJson cfg.maxDepth),
      ("nodes", Json.arr <| nodes.map nodeToJson)
    ]
  IO.FS.writeFile cfg.outFile (Json.compress output)
