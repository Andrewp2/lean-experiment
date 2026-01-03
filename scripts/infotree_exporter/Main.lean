import Lean
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Server.FileWorker.SetupFile
import Lean.Setup
import Lean.Util.Path

open Lean
open Lean.Elab
open Lean.Language

structure InfoTreeCounts where
  treesTotal : Nat := 0
  contextNodes : Nat := 0
  holes : Nat := 0
  infoItemsTotal : Nat := 0
  tacticInfos : Nat := 0
  termInfos : Nat := 0
  partialTermInfos : Nat := 0
  commandInfos : Nat := 0
  macroExpansionInfos : Nat := 0
  optionInfos : Nat := 0
  errorNameInfos : Nat := 0
  fieldInfos : Nat := 0
  completionInfos : Nat := 0
  userWidgetInfos : Nat := 0
  customInfos : Nat := 0
  fvarAliasInfos : Nat := 0
  fieldRedeclInfos : Nat := 0
  delabTermInfos : Nat := 0
  choiceInfos : Nat := 0
  docInfos : Nat := 0
  docElabInfos : Nat := 0
  deriving Inhabited

def InfoTreeCounts.bump (f : InfoTreeCounts → Nat) (set : InfoTreeCounts → Nat → InfoTreeCounts) :
    InfoTreeCounts → InfoTreeCounts := fun c => set c (f c + 1)

def InfoTreeCounts.incTrees : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.treesTotal (fun c v => { c with treesTotal := v })

def InfoTreeCounts.incContext : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.contextNodes (fun c v => { c with contextNodes := v })

def InfoTreeCounts.incHoles : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.holes (fun c v => { c with holes := v })

def InfoTreeCounts.incInfoItems : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.infoItemsTotal (fun c v => { c with infoItemsTotal := v })

def InfoTreeCounts.incTactic : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.tacticInfos (fun c v => { c with tacticInfos := v })

def InfoTreeCounts.incTerm : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.termInfos (fun c v => { c with termInfos := v })

def InfoTreeCounts.incPartialTerm : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.partialTermInfos (fun c v => { c with partialTermInfos := v })

def InfoTreeCounts.incCommand : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.commandInfos (fun c v => { c with commandInfos := v })

def InfoTreeCounts.incMacro : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.macroExpansionInfos (fun c v => { c with macroExpansionInfos := v })

def InfoTreeCounts.incOption : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.optionInfos (fun c v => { c with optionInfos := v })

def InfoTreeCounts.incErrorName : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.errorNameInfos (fun c v => { c with errorNameInfos := v })

def InfoTreeCounts.incField : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.fieldInfos (fun c v => { c with fieldInfos := v })

def InfoTreeCounts.incCompletion : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.completionInfos (fun c v => { c with completionInfos := v })

def InfoTreeCounts.incUserWidget : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.userWidgetInfos (fun c v => { c with userWidgetInfos := v })

def InfoTreeCounts.incCustom : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.customInfos (fun c v => { c with customInfos := v })

def InfoTreeCounts.incFVarAlias : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.fvarAliasInfos (fun c v => { c with fvarAliasInfos := v })

def InfoTreeCounts.incFieldRedecl : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.fieldRedeclInfos (fun c v => { c with fieldRedeclInfos := v })

def InfoTreeCounts.incDelab : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.delabTermInfos (fun c v => { c with delabTermInfos := v })

def InfoTreeCounts.incChoice : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.choiceInfos (fun c v => { c with choiceInfos := v })

def InfoTreeCounts.incDoc : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.docInfos (fun c v => { c with docInfos := v })

def InfoTreeCounts.incDocElab : InfoTreeCounts → InfoTreeCounts :=
  InfoTreeCounts.bump InfoTreeCounts.docElabInfos (fun c v => { c with docElabInfos := v })

def InfoTreeCounts.add (a b : InfoTreeCounts) : InfoTreeCounts :=
  { treesTotal := a.treesTotal + b.treesTotal
    contextNodes := a.contextNodes + b.contextNodes
    holes := a.holes + b.holes
    infoItemsTotal := a.infoItemsTotal + b.infoItemsTotal
    tacticInfos := a.tacticInfos + b.tacticInfos
    termInfos := a.termInfos + b.termInfos
    partialTermInfos := a.partialTermInfos + b.partialTermInfos
    commandInfos := a.commandInfos + b.commandInfos
    macroExpansionInfos := a.macroExpansionInfos + b.macroExpansionInfos
    optionInfos := a.optionInfos + b.optionInfos
    errorNameInfos := a.errorNameInfos + b.errorNameInfos
    fieldInfos := a.fieldInfos + b.fieldInfos
    completionInfos := a.completionInfos + b.completionInfos
    userWidgetInfos := a.userWidgetInfos + b.userWidgetInfos
    customInfos := a.customInfos + b.customInfos
    fvarAliasInfos := a.fvarAliasInfos + b.fvarAliasInfos
    fieldRedeclInfos := a.fieldRedeclInfos + b.fieldRedeclInfos
    delabTermInfos := a.delabTermInfos + b.delabTermInfos
    choiceInfos := a.choiceInfos + b.choiceInfos
    docInfos := a.docInfos + b.docInfos
    docElabInfos := a.docElabInfos + b.docElabInfos }

def countInfo (info : Info) (counts : InfoTreeCounts) : InfoTreeCounts :=
  match info with
  | .ofTacticInfo _ => counts.incInfoItems.incTactic
  | .ofTermInfo _ => counts.incInfoItems.incTerm
  | .ofPartialTermInfo _ => counts.incInfoItems.incPartialTerm
  | .ofCommandInfo _ => counts.incInfoItems.incCommand
  | .ofMacroExpansionInfo _ => counts.incInfoItems.incMacro
  | .ofOptionInfo _ => counts.incInfoItems.incOption
  | .ofErrorNameInfo _ => counts.incInfoItems.incErrorName
  | .ofFieldInfo _ => counts.incInfoItems.incField
  | .ofCompletionInfo _ => counts.incInfoItems.incCompletion
  | .ofUserWidgetInfo _ => counts.incInfoItems.incUserWidget
  | .ofCustomInfo _ => counts.incInfoItems.incCustom
  | .ofFVarAliasInfo _ => counts.incInfoItems.incFVarAlias
  | .ofFieldRedeclInfo _ => counts.incInfoItems.incFieldRedecl
  | .ofDelabTermInfo _ => counts.incInfoItems.incDelab
  | .ofChoiceInfo _ => counts.incInfoItems.incChoice
  | .ofDocInfo _ => counts.incInfoItems.incDoc
  | .ofDocElabInfo _ => counts.incInfoItems.incDocElab

partial def countTree (tree : InfoTree) (counts : InfoTreeCounts) : InfoTreeCounts :=
  match tree with
  | .context _ child =>
      countTree child (counts.incTrees.incContext)
  | .hole _ =>
      counts.incTrees.incHoles
  | .node info children =>
      let counts := countInfo info (counts.incTrees)
      children.foldl (fun acc child => countTree child acc) counts

def countTrees (trees : Array InfoTree) : InfoTreeCounts :=
  trees.foldl (fun acc tree => countTree tree acc) {}

def InfoTreeCounts.toMetricsJson (c : InfoTreeCounts) : Json :=
  let termInfoItems := c.termInfos + c.partialTermInfos + c.delabTermInfos
  let tacticSteps := c.tacticInfos
  Json.mkObj [
    ("infotree_nodes_total", toJson c.treesTotal),
    ("infotree_context_nodes", toJson c.contextNodes),
    ("infotree_holes", toJson c.holes),
    ("infotree_info_items_total", toJson c.infoItemsTotal),
    ("infotree_tactic_state_items", toJson c.tacticInfos),
    ("infotree_term_info_items", toJson termInfoItems),
    ("infotree_diagnostic_items", toJson c.errorNameInfos),
    ("infotree_widget_items", toJson c.userWidgetInfos),
    ("infotree_commands_count", toJson c.commandInfos),
    ("infotree_tactic_steps", toJson tacticSteps)
  ]

structure Config where
  rootDir : System.FilePath := "."
  outDir : System.FilePath := "infotree_out"
  limit : Option Nat := none
  start : Nat := 0
  verbose : Bool := false
  errorLimit : Nat := 3
  maxSeconds : Option Nat := none
  maxRssMb : Option Nat := none
  singleFile : Option System.FilePath := none
  rssLogMb : Option Nat := none
  memDebug : Bool := false
  continueFlag : Bool := false
  deriving Inhabited

def parseArgs (args : List String) : IO Config := do
  let rec go (cfg : Config) (args : List String) : IO Config := do
    match args with
    | [] => return cfg
    | "--root" :: value :: rest =>
        go { cfg with rootDir := value } rest
    | "--out" :: value :: rest =>
        go { cfg with outDir := value } rest
    | "--limit" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with limit := some n } rest
        | none => throw <| IO.userError s!"Invalid --limit value: {value}"
    | "--start" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with start := n } rest
        | none => throw <| IO.userError s!"Invalid --start value: {value}"
    | "--verbose" :: rest =>
        go { cfg with verbose := true } rest
    | "--error-limit" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with errorLimit := n } rest
        | none => throw <| IO.userError s!"Invalid --error-limit value: {value}"
    | "--max-seconds" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with maxSeconds := some n } rest
        | none => throw <| IO.userError s!"Invalid --max-seconds value: {value}"
    | "--max-rss-mb" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with maxRssMb := some n } rest
        | none => throw <| IO.userError s!"Invalid --max-rss-mb value: {value}"
    | "--single" :: value :: rest =>
        go { cfg with singleFile := some value } rest
    | "--rss-log-mb" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with rssLogMb := some n } rest
        | none => throw <| IO.userError s!"Invalid --rss-log-mb value: {value}"
    | "--mem-debug" :: rest =>
        go { cfg with memDebug := true } rest
    | "--continue" :: rest =>
        go { cfg with continueFlag := true } rest
    | flag :: _ =>
        throw <| IO.userError s!"Unknown argument: {flag}"
  go {} args

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

def getLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mathlibDir := root / "Mathlib"
  if !(← mathlibDir.isDir) then
    throw <| IO.userError s!"Expected Mathlib directory at {mathlibDir}"
  let files ← mathlibDir.walkDir
  return files.filter (·.extension == some "lean")

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

def fileSetupKindLabel : Lean.Server.FileWorker.FileSetupResultKind → String
  | .success => "success"
  | .noLakefile => "noLakefile"
  | .importsOutOfDate => "importsOutOfDate"
  | .error _ => "error"

def listDropRight (xs : List α) (n : Nat) : List α :=
  xs.take (xs.length - n)

def basePathFromModuleArtifact (mod : Name) (file : System.FilePath) : System.FilePath :=
  let isAbs := file.isAbsolute
  let comps := file.components.dropLast
  let modDepth := mod.components.length
  let dropCount := if modDepth == 0 then 0 else modDepth - 1
  let baseComps := listDropRight comps dropCount |>.filter (· != "") |>.map System.FilePath.mk
  let init :=
    if isAbs then
      System.FilePath.mk System.FilePath.pathSeparator.toString
    else
      System.FilePath.mk ""
  List.foldl (fun acc comp => acc / comp) init baseComps

def searchPathsFromImportArts (arts : NameMap ImportArtifacts) : Array System.FilePath :=
  let entries := Std.TreeMap.toList arts
  entries.foldl (init := #[]) fun acc entry =>
    let mod := entry.fst
    let art := entry.snd
    let file? := art.olean? <|> art.ir?
    match file? with
    | none => acc
    | some file =>
        let base := basePathFromModuleArtifact mod file
        if acc.any (fun p => p == base) then acc else acc.push base

def mergeSearchPath (paths : Array System.FilePath) : IO Unit := do
  let mut current ← Lean.searchPathRef.get
  for path in paths do
    if !(current.any (fun p => p == path)) then
      current := current ++ [path]
  Lean.searchPathRef.set current

@[extern "lean_mi_collect"]
opaque miCollect (force : Bool) : IO Unit

@[extern "lean_mi_stats_print"]
opaque miStatsPrint : IO Unit

def forceGC : IO Unit := do
  -- Force mimalloc to run a full collection.
  miCollect true

def logMiStats : IO Unit := do
  -- Print allocator stats to stderr.
  miStatsPrint

def readRssKb : IO (Option Nat) := do
  try
    let content ← IO.FS.readFile "/proc/self/status"
    for line in content.splitOn "\n" do
      if line.startsWith "VmRSS:" then
        let rest := (line.drop 6).trimAscii.toString
        let parts := rest.splitOn " "
        let first? := parts.find? (fun part => !part.isEmpty)
        match first? with
        | some value =>
            match value.toNat? with
            | some kb => return some kb
            | none => return none
        | none => return none
    return none
  catch _ =>
    return none

def readSmapsRollupSummary : IO (Array String) := do
  try
    let content ← IO.FS.readFile "/proc/self/smaps_rollup"
    let keys := #[
      "Rss:", "Pss:", "Shared_Clean:", "Shared_Dirty:",
      "Private_Clean:", "Private_Dirty:", "Swap:"
    ]
    let mut lines : Array String := #[]
    for line in content.splitOn "\n" do
      if keys.any (fun key => line.startsWith key) then
        lines := lines.push line
    return lines
  catch _ =>
    return #[]

def readSmapsTop (maxEntries : Nat) : IO (Array (Nat × String)) := do
  try
    let content ← IO.FS.readFile "/proc/self/smaps"
    let mut entries : Array (Nat × String) := #[]
    let mut currentName := ""
    let mut currentRss := 0
    let mut hasCurrent := false
    for line in content.splitOn "\n" do
      let parts := (line.splitOn " ").filter (· != "")
      if parts.length >= 5 && parts[0]!.contains "-" && parts[1]!.length == 4 then
        if hasCurrent then
          let name := if currentName.isEmpty then "[anon]" else currentName
          entries := entries.push (currentRss, name)
        let name :=
          if parts.length > 5 then
            String.intercalate " " (parts.drop 5)
          else
            ""
        currentName := name
        currentRss := 0
        hasCurrent := true
      else if line.startsWith "Rss:" then
        let rest := (line.drop 4).trimAscii.toString
        let rssParts := rest.splitOn " "
        let first? := rssParts.find? (fun part => !part.isEmpty)
        match first? with
        | some value =>
            if let some kb := value.toNat? then
              currentRss := kb
        | none => pure ()
    if hasCurrent then
      let name := if currentName.isEmpty then "[anon]" else currentName
      entries := entries.push (currentRss, name)
    let sorted := entries.qsort (fun a b => a.fst > b.fst)
    return sorted.take maxEntries
  catch _ =>
    return #[]

def logMemDebug (stage : String) : IO Unit := do
  if let some rssKb ← readRssKb then
    let rssMb := rssKb / 1024
    IO.println s!"[infotree_export] mem-debug {stage}: rss {rssMb}MB"
  else
    IO.println s!"[infotree_export] mem-debug {stage}: rss unavailable"
  let smapsLines ← readSmapsRollupSummary
  if !smapsLines.isEmpty then
    IO.println "[infotree_export] smaps_rollup:"
    for line in smapsLines do
      IO.println s!"  {line}"
  let top := (← readSmapsTop 5)
  if !top.isEmpty then
    IO.println "[infotree_export] smaps_top:"
    for (rssKb, name) in top do
      IO.println s!"  {rssKb} kB  {name}"

def buildContinuationArgs (cfg : Config) (start : Nat) (remaining : Option Nat) : Array String :=
  Id.run do
    let mut args := #[
      "--root", cfg.rootDir.toString,
      "--out", cfg.outDir.toString,
      "--start", toString start
    ]
    if let some lim := remaining then
      args := args ++ #["--limit", toString lim]
    if cfg.verbose then
      args := args.push "--verbose"
    if cfg.errorLimit != 3 then
      args := args ++ #["--error-limit", toString cfg.errorLimit]
    if let some maxSeconds := cfg.maxSeconds then
      args := args ++ #["--max-seconds", toString maxSeconds]
    if let some maxRssMb := cfg.maxRssMb then
      args := args ++ #["--max-rss-mb", toString maxRssMb]
    if let some rssLogMb := cfg.rssLogMb then
      args := args ++ #["--rss-log-mb", toString rssLogMb]
    if cfg.memDebug then
      args := args.push "--mem-debug"
    if cfg.continueFlag then
      args := args.push "--continue"
    return args

def buildSingleFileArgs (cfg : Config) (file : System.FilePath) : Array String :=
  Id.run do
    let mut args := #[
      "--root", cfg.rootDir.toString,
      "--out", cfg.outDir.toString,
      "--single", file.toString
    ]
    if cfg.verbose then
      args := args.push "--verbose"
    if cfg.errorLimit != 3 then
      args := args ++ #["--error-limit", toString cfg.errorLimit]
    if let some rssLogMb := cfg.rssLogMb then
      args := args ++ #["--rss-log-mb", toString rssLogMb]
    if cfg.memDebug then
      args := args.push "--mem-debug"
    if cfg.continueFlag then
      args := args.push "--continue"
    return args

structure SetupCache where
  setup : ModuleSetup
  searchPaths : Array System.FilePath

initialize setupCacheRef : IO.Ref (Option SetupCache) ← IO.mkRef none

def resetSetupCache : IO Unit := do
  setupCacheRef.set none

unsafe def getSetupCache (doc : Lean.Server.DocumentMeta) (stx : Elab.HeaderSyntax) (verbose : Bool) :
    IO SetupCache := do
  if let some cache ← setupCacheRef.get then
    return cache
  let header := stx.toModuleHeader
  let fileSetupResult ← Lean.Server.FileWorker.setupFile doc header (fun _ => pure ())
  if verbose then
    IO.eprintln s!"[infotree_export] setup-file kind: {fileSetupKindLabel fileSetupResult.kind}"
    IO.eprintln s!"[infotree_export] importArts count: {fileSetupResult.setup.importArts.size}"
    let plausible : Name := `Plausible
    IO.eprintln s!"[infotree_export] importArts has Plausible: {fileSetupResult.setup.importArts.contains plausible}"
  match fileSetupResult.kind with
  | .importsOutOfDate =>
      throw <| IO.userError "Imports are out of date and must be rebuilt"
  | .error msg =>
      throw <| IO.userError msg
  | _ => pure ()
  let setup := fileSetupResult.setup
  let searchPaths := searchPathsFromImportArts setup.importArts
  mergeSearchPath searchPaths
  let cache := { setup, searchPaths }
  setupCacheRef.set (some cache)
  return cache

unsafe def runFrontendForTrees (doc : Lean.Server.DocumentMeta) (verbose : Bool) (errorLimit : Nat)
    (memDebug : Bool) :
    IO (InfoTreeCounts × Nat × Array Message) := do
  let inputCtx := doc.mkInputContext
  let cmdlineOpts := Lean.internal.cmdlineSnapshots.setIfNotSet {} true
  let ctx : ProcessingContext := { inputCtx with }
  let setupFn (stx : Elab.HeaderSyntax) :
      ProcessingT IO (Except Lean.Language.Lean.HeaderProcessedSnapshot
        Lean.Language.Lean.SetupImportsResult) := do
    let cache ← liftM <| getSetupCache doc stx verbose
    let header := stx.toModuleHeader
    let mergedOpts := cmdlineOpts.mergeBy (fun _ _ fileOpt => fileOpt) cache.setup.options.toOptions
    let mergedOpts := Elab.async.set mergedOpts false
    return .ok {
      trustLevel := 0
      package? := cache.setup.package?
      mainModuleName := doc.mod
      isModule := strictOr cache.setup.isModule header.isModule
      imports := header.imports
      plugins := cache.setup.plugins
      importArts := cache.setup.importArts
      opts := mergedOpts
    }
  let snap ← Lean.Language.Lean.process setupFn none ctx
  if memDebug then
    logMemDebug "after_process"
  let snaps := Language.toSnapshotTree snap
  if memDebug then
    logMemDebug "after_to_snapshot_tree"
  let _ ← snaps.runAndReport cmdlineOpts false {}
  if memDebug then
    logMemDebug "after_runAndReport"
  let (counts, errorCount, errorMessages) ←
    snaps.foldM (init := ({}, 0, #[])) fun (counts, errorCount, errorMessages) snapshot => do
      let mut counts := counts
      let mut errorCount := errorCount
      let mut errorMessages := errorMessages
      for msg in snapshot.diagnostics.msgLog.toArray do
        if msg.severity == MessageSeverity.error then
          errorCount := errorCount + 1
          if errorMessages.size < errorLimit then
            errorMessages := errorMessages.push msg
      match snapshot.infoTree? with
      | some tree => counts := countTree tree counts
      | none => pure ()
      return (counts, errorCount, errorMessages)
  if memDebug then
    logMemDebug "after_fold"
  Runtime.forget snaps
  if memDebug then
    logMemDebug "after_forget"
  return (counts, errorCount, errorMessages)

unsafe def exportFile (cfg : Config) (file : System.FilePath) (index : Nat) (total : Nat) : IO Unit := do
  let relativePath ← relativeToRoot cfg.rootDir file
  let outputPath := cfg.outDir / relativePath |>.withExtension "json"
  if cfg.continueFlag then
    if (← outputPath.pathExists) then
      if cfg.verbose then
        IO.println s!"[{index + 1}/{total}] {relativePath} (skip)"
      return ()
  if cfg.verbose then
    IO.println s!"[{index + 1}/{total}] {relativePath}"
  let input ← IO.FS.readFile file
  let moduleName := moduleNameFromPath (dropExtension relativePath)
  let doc : Lean.Server.DocumentMeta := {
    uri := System.Uri.pathToUri file
    mod := moduleName
    version := 0
    text := input.toFileMap
    dependencyBuildMode := .never
  }
  let (counts, errorCount, errors) ←
    runFrontendForTrees doc cfg.verbose cfg.errorLimit cfg.memDebug
  if errorCount > 0 then
    IO.eprintln s!"[infotree_export] errors while processing {relativePath}"
    for msg in errors do
      let msg ← msg.toString
      IO.eprintln msg
  let outputDir := outputPath.parent.getD cfg.outDir
  IO.FS.createDirAll outputDir
  let payload := Json.mkObj [("metrics", counts.toMetricsJson)]
  IO.FS.writeFile outputPath (Json.compress payload)
  if let some thresholdMb := cfg.rssLogMb then
    if let some rssKb ← readRssKb then
      let rssMb := rssKb / 1024
      if rssMb >= thresholdMb then
        IO.println s!"[infotree_export] rss {rssMb}MB after {relativePath}"
        let smapsLines ← readSmapsRollupSummary
        if !smapsLines.isEmpty then
          IO.println "[infotree_export] smaps_rollup:"
          for line in smapsLines do
            IO.println s!"  {line}"
        logMiStats
  IO.println s!"[infotree_export] done {relativePath}"

def runSingleFileWithTimeout (cfg : Config) (file : System.FilePath) (maxSeconds : Nat) : IO Bool := do
  let exeDir ← IO.appDir
  let exePath := exeDir / "infotree_export"
  let child ← IO.Process.spawn {
    cmd := exePath.toString
    args := buildSingleFileArgs cfg file
    cwd := some cfg.rootDir
    stdout := .inherit
    stderr := .inherit
  }
  let totalTicks : Nat := maxSeconds * 10
  let rec waitLoop (remainingTicks : Nat) : IO Bool := do
    if let some _exitCode ← IO.Process.Child.tryWait child then
      return true
    match remainingTicks with
    | 0 =>
        IO.Process.Child.kill child
        return false
    | Nat.succ rest =>
        IO.sleep 100
        waitLoop rest
  waitLoop totalTicks

def maybeCollectAfterFile (cfg : Config) : IO Unit := do
  if let some thresholdMb := cfg.maxRssMb then
    if let some rssKb ← readRssKb then
      let rssMb := rssKb / 1024
      if rssMb >= thresholdMb then
        forceGC
        resetSetupCache

unsafe def main (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  IO.Process.setCurrentDir cfg.rootDir
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  if let some file := cfg.singleFile then
    if let some maxSeconds := cfg.maxSeconds then
      let ok ← runSingleFileWithTimeout cfg file maxSeconds
      if !ok then
        IO.eprintln s!"[infotree_export] timeout after {maxSeconds}s: {file}"
      maybeCollectAfterFile cfg
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir file
        logMemDebug s!"after_gc {relativePath}"
    else
      Lean.withImporting do
        exportFile cfg file 0 1
      maybeCollectAfterFile cfg
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir file
        logMemDebug s!"after_gc {relativePath}"
    return ()
  let files ← getLeanFiles cfg.rootDir
  if cfg.start >= files.size then
    throw <| IO.userError s!"Start index {cfg.start} is out of range for {files.size} files"
  let endIdx :=
    match cfg.limit with
    | some n => min files.size (cfg.start + n)
    | none => files.size
  let slice := files.extract cfg.start endIdx
  if cfg.verbose then
    IO.println s!"Exporting infotree metrics for {slice.size} files..."
  for h : i in [0:slice.size] do
    if let some maxRssMb := cfg.maxRssMb then
      if let some rssKb ← readRssKb then
        let rssMb := rssKb / 1024
        if rssMb >= maxRssMb then
          let nextStart := cfg.start + i
          let remaining :=
            match cfg.limit with
            | some lim => some (lim - i)
            | none => none
          IO.eprintln s!"[infotree_export] restarting after rss {rssMb}MB"
          let exeDir ← IO.appDir
          let exePath := exeDir / "infotree_export"
          let child ← IO.Process.spawn {
            cmd := exePath.toString
            args := (buildContinuationArgs cfg nextStart remaining)
            cwd := some cfg.rootDir
            stdout := .inherit
            stderr := .inherit
          }
          let _ ← child.wait
          return ()
    if let some maxSeconds := cfg.maxSeconds then
      let ok ← runSingleFileWithTimeout cfg (slice[i]) maxSeconds
      if !ok then
        IO.eprintln s!"[infotree_export] timeout after {maxSeconds}s: {slice[i]}"
      maybeCollectAfterFile cfg
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir (slice[i])
        logMemDebug s!"after_gc {relativePath}"
    else
      Lean.withImporting do
        exportFile cfg (slice[i]) i slice.size
      maybeCollectAfterFile cfg
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir (slice[i])
        logMemDebug s!"after_gc {relativePath}"
    if let some maxRssMb := cfg.maxRssMb then
      if let some rssKb ← readRssKb then
        let rssMb := rssKb / 1024
        if rssMb >= maxRssMb && i + 1 < slice.size then
          IO.eprintln s!"[infotree_export] restarting after rss {rssMb}MB"
          let nextStart := cfg.start + i + 1
          let remaining :=
            match cfg.limit with
            | some lim =>
                if lim <= i + 1 then
                  some 0
                else
                  some (lim - (i + 1))
            | none => none
          let exeDir ← IO.appDir
          let exePath := exeDir / "infotree_export"
          let child ← IO.Process.spawn {
            cmd := exePath.toString
            args := (buildContinuationArgs cfg nextStart remaining)
            cwd := some cfg.rootDir
            stdout := .inherit
            stderr := .inherit
          }
          let _ ← child.wait
          return ()
