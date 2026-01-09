import Lean
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Server.FileWorker.SetupFile
import Lean.Setup
import Lean.Util.Path

open Lean
open Lean.Elab
open Lean.Language
open Lean.Language.Lean

def jsonArray (items : Array Json) : Json :=
  Json.arr items

def optionToJson (to : α → Json) (value : Option α) : Json :=
  match value with
  | some v => to v
  | none => Json.null

def nameToJson (name : Name) : Json :=
  toJson name.toString

def rangeToJson (range : Syntax.Range) : Json :=
  Json.mkObj [
    ("start", toJson range.start.byteIdx),
    ("stop", toJson range.stop.byteIdx)
  ]

def syntaxToJson (stx : Syntax) : Json :=
  let range := optionToJson rangeToJson (stx.getRange?)
  Json.mkObj [
    ("kind", toJson stx.getKind.toString),
    ("range", range)
  ]

def exprToJson (expr : Expr) : Json :=
  toJson (toString expr)

def expectedTypeToJson (maxExpectedExprNodes? : Option Nat) (expr : Expr) : Json :=
  match maxExpectedExprNodes? with
  | some maxNodes =>
      let size := expr.sizeWithoutSharing
      if size > maxNodes then
        toJson s!"<expectedType truncated size={size}>"
      else
        exprToJson expr
  | none =>
      exprToJson expr

def lctxSizeToJson (lctx : LocalContext) : Json :=
  toJson lctx.decls.size

def mvarIdsToJson (mvars : List MVarId) : Json :=
  jsonArray <| mvars.toArray.map (fun mvar => toJson mvar.name.toString)

def fvarIdToJson (fvar : FVarId) : Json :=
  toJson fvar.name.toString

def partialContextToJson (ctx : PartialContextInfo) : Json :=
  match ctx with
  | .commandCtx info =>
      Json.mkObj [
        ("kind", toJson "commandCtx"),
        ("currNamespace", nameToJson info.currNamespace),
        ("openDecls", jsonArray <| info.openDecls.toArray.map (fun decl => toJson (toString decl)))
      ]
  | .parentDeclCtx parentDecl =>
      Json.mkObj [
        ("kind", toJson "parentDeclCtx"),
        ("parentDecl", nameToJson parentDecl)
      ]
  | .autoImplicitCtx autoImplicits =>
      Json.mkObj [
        ("kind", toJson "autoImplicitCtx"),
        ("autoImplicits", jsonArray <| autoImplicits.map exprToJson)
      ]

structure StringMetrics where
  exprBytes : Nat := 0
  exprMax : Nat := 0
  exprCount : Nat := 0
  expectedBytes : Nat := 0
  expectedMax : Nat := 0
  expectedCount : Nat := 0
  expectedSkipped : Nat := 0
  expectedSkippedMax : Nat := 0
  docBytes : Nat := 0
  docMax : Nat := 0
  docCount : Nat := 0
  deriving Inhabited

def StringMetrics.recordExpr (stats : StringMetrics) (value : String) : StringMetrics :=
  let size := value.length
  { stats with
    exprBytes := stats.exprBytes + size
    exprMax := max stats.exprMax size
    exprCount := stats.exprCount + 1 }

def StringMetrics.recordExpected (stats : StringMetrics) (value : String) : StringMetrics :=
  let size := value.length
  { stats with
    expectedBytes := stats.expectedBytes + size
    expectedMax := max stats.expectedMax size
    expectedCount := stats.expectedCount + 1 }

def StringMetrics.recordDoc (stats : StringMetrics) (value : String) : StringMetrics :=
  let size := value.length
  { stats with
    docBytes := stats.docBytes + size
    docMax := max stats.docMax size
    docCount := stats.docCount + 1 }

def recordExpr (ref : IO.Ref StringMetrics) (expr : Expr) : IO Unit := do
  let rendered := toString expr
  ref.modify (·.recordExpr rendered)

def recordExpected (ref : IO.Ref StringMetrics) (expr : Expr)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  if let some maxNodes := maxExpectedExprNodes? then
    let size := expr.sizeWithoutSharing
    if size > maxNodes then
      ref.modify fun stats => {
        stats with
        expectedSkipped := stats.expectedSkipped + 1
        expectedSkippedMax := max stats.expectedSkippedMax size
      }
    else
      let rendered := toString expr
      ref.modify (·.recordExpected rendered)
  else
    let rendered := toString expr
    ref.modify (·.recordExpected rendered)

def recordDocString (ref : IO.Ref StringMetrics) (value : String) : IO Unit := do
  ref.modify (·.recordDoc value)

def recordTermInfo (ref : IO.Ref StringMetrics) (info : TermInfo)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  recordExpr ref info.expr
  match info.expectedType? with
  | some expr => recordExpected ref expr maxExpectedExprNodes?
  | none => pure ()

def recordPartialTermInfo (ref : IO.Ref StringMetrics) (info : PartialTermInfo)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  match info.expectedType? with
  | some expr => recordExpected ref expr maxExpectedExprNodes?
  | none => pure ()

def recordFieldInfo (ref : IO.Ref StringMetrics) (info : FieldInfo) : IO Unit := do
  recordExpr ref info.val

def recordDelabTermInfo (ref : IO.Ref StringMetrics) (info : DelabTermInfo)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  recordExpr ref info.expr
  match info.expectedType? with
  | some expr => recordExpected ref expr maxExpectedExprNodes?
  | none => pure ()
  match info.docString? with
  | some doc => recordDocString ref doc
  | none => pure ()

def recordCompletionInfo (ref : IO.Ref StringMetrics) (info : CompletionInfo)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  match info with
  | .dot termInfo expectedType? =>
      recordTermInfo ref termInfo maxExpectedExprNodes?
      match expectedType? with
      | some expr => recordExpected ref expr maxExpectedExprNodes?
      | none => pure ()
  | .id _ _ _ _ expectedType? =>
      match expectedType? with
      | some expr => recordExpected ref expr maxExpectedExprNodes?
      | none => pure ()
  | .dotId _ _ _ expectedType? =>
      match expectedType? with
      | some expr => recordExpected ref expr maxExpectedExprNodes?
      | none => pure ()
  | .fieldId _ _ _ _ =>
      pure ()
  | .namespaceId _ =>
      pure ()
  | .option _ =>
      pure ()
  | .errorName _ _ =>
      pure ()
  | .endSection _ _ _ _ =>
      pure ()
  | .tactic _ =>
      pure ()

def recordPartialContext (ref : IO.Ref StringMetrics) (ctx : PartialContextInfo) : IO Unit := do
  match ctx with
  | .commandCtx _ => pure ()
  | .parentDeclCtx _ => pure ()
  | .autoImplicitCtx autoImplicits =>
      for expr in autoImplicits do
        recordExpr ref expr

def recordInfoMetrics (ref : IO.Ref StringMetrics) (info : Info)
    (maxExpectedExprNodes? : Option Nat) : IO Unit := do
  match info with
  | .ofTacticInfo _ => pure ()
  | .ofTermInfo i => recordTermInfo ref i maxExpectedExprNodes?
  | .ofPartialTermInfo i => recordPartialTermInfo ref i maxExpectedExprNodes?
  | .ofCommandInfo _ => pure ()
  | .ofMacroExpansionInfo _ => pure ()
  | .ofOptionInfo _ => pure ()
  | .ofErrorNameInfo _ => pure ()
  | .ofFieldInfo i => recordFieldInfo ref i
  | .ofCompletionInfo i => recordCompletionInfo ref i maxExpectedExprNodes?
  | .ofUserWidgetInfo _ => pure ()
  | .ofCustomInfo _ => pure ()
  | .ofFVarAliasInfo _ => pure ()
  | .ofFieldRedeclInfo _ => pure ()
  | .ofDelabTermInfo i => recordDelabTermInfo ref i maxExpectedExprNodes?
  | .ofChoiceInfo _ => pure ()
  | .ofDocInfo _ => pure ()
  | .ofDocElabInfo _ => pure ()

def writeStringMetricsCsv (csvPath : System.FilePath) (relativePath : System.FilePath)
    (metrics : StringMetrics) (stage : String) (nodes : Nat) : IO Unit := do
  let parent := csvPath.parent.getD "."
  IO.FS.createDirAll parent
  let header :=
    "path,stage,nodes,expr_bytes,expr_max,expr_count,expected_bytes,expected_max,expected_count,expected_skipped,expected_skipped_max,doc_bytes,doc_max,doc_count\n"
  let fileExists ← csvPath.pathExists
  IO.FS.withFile csvPath .append fun handle => do
    if !fileExists then
      handle.putStr header
    let row :=
      s!"{relativePath},{stage},{nodes}," ++
      s!"{metrics.exprBytes},{metrics.exprMax},{metrics.exprCount}," ++
      s!"{metrics.expectedBytes},{metrics.expectedMax},{metrics.expectedCount}," ++
      s!"{metrics.expectedSkipped},{metrics.expectedSkippedMax}," ++
      s!"{metrics.docBytes},{metrics.docMax},{metrics.docCount}\n"
    handle.putStr row

partial def startMetricsHeartbeat (csvPath : System.FilePath) (relativePath : System.FilePath)
    (metricsRef : IO.Ref StringMetrics) (countRef : IO.Ref Nat) : IO (IO.Ref Bool) := do
  let runningRef ← IO.mkRef true
  let rec loop : IO Unit := do
    if !(← runningRef.get) then
      return ()
    let metrics ← metricsRef.get
    let count ← countRef.get
    writeStringMetricsCsv csvPath relativePath metrics "heartbeat" count
    IO.sleep 1000
    loop
  let _ ← IO.asTask loop
  return runningRef

def termInfoToJson (maxExpectedExprNodes? : Option Nat) (info : TermInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "term"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx),
    ("lctxSize", lctxSizeToJson info.lctx),
    ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) info.expectedType?),
    ("expr", exprToJson info.expr),
    ("isBinder", toJson info.isBinder),
    ("isDisplayableTerm", toJson info.isDisplayableTerm)
  ]

def partialTermInfoToJson (maxExpectedExprNodes? : Option Nat) (info : PartialTermInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "partialTerm"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx),
    ("lctxSize", lctxSizeToJson info.lctx),
    ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) info.expectedType?)
  ]

def commandInfoToJson (info : CommandInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "command"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx)
  ]

def tacticInfoToJson (info : TacticInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "tactic"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx),
    ("goalsBefore", mvarIdsToJson info.goalsBefore),
    ("goalsAfter", mvarIdsToJson info.goalsAfter)
  ]

def macroExpansionInfoToJson (info : MacroExpansionInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "macroExpansion"),
    ("stx", syntaxToJson info.stx),
    ("output", syntaxToJson info.output),
    ("lctxSize", lctxSizeToJson info.lctx)
  ]

def optionInfoToJson (info : OptionInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "option"),
    ("stx", syntaxToJson info.stx),
    ("optionName", nameToJson info.optionName),
    ("declName", nameToJson info.declName)
  ]

def errorNameInfoToJson (info : ErrorNameInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "errorName"),
    ("stx", syntaxToJson info.stx),
    ("errorName", nameToJson info.errorName)
  ]

def fieldInfoToJson (info : FieldInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "field"),
    ("projName", nameToJson info.projName),
    ("fieldName", nameToJson info.fieldName),
    ("lctxSize", lctxSizeToJson info.lctx),
    ("val", exprToJson info.val),
    ("stx", syntaxToJson info.stx)
  ]

def completionInfoToJson (maxExpectedExprNodes? : Option Nat) (info : CompletionInfo) : Json :=
  match info with
  | .dot termInfo expectedType? =>
      Json.mkObj [
        ("kind", toJson "completion.dot"),
        ("termInfo", termInfoToJson maxExpectedExprNodes? termInfo),
        ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) expectedType?)
      ]
  | .id stx id danglingDot lctx expectedType? =>
      Json.mkObj [
        ("kind", toJson "completion.id"),
        ("stx", syntaxToJson stx),
        ("id", nameToJson id),
        ("danglingDot", toJson danglingDot),
        ("lctxSize", lctxSizeToJson lctx),
        ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) expectedType?)
      ]
  | .dotId stx id lctx expectedType? =>
      Json.mkObj [
        ("kind", toJson "completion.dotId"),
        ("stx", syntaxToJson stx),
        ("id", nameToJson id),
        ("lctxSize", lctxSizeToJson lctx),
        ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) expectedType?)
      ]
  | .fieldId stx id lctx structName =>
      Json.mkObj [
        ("kind", toJson "completion.fieldId"),
        ("stx", syntaxToJson stx),
        ("id", optionToJson nameToJson id),
        ("lctxSize", lctxSizeToJson lctx),
        ("structName", nameToJson structName)
      ]
  | .namespaceId stx =>
      Json.mkObj [
        ("kind", toJson "completion.namespaceId"),
        ("stx", syntaxToJson stx)
      ]
  | .option stx =>
      Json.mkObj [
        ("kind", toJson "completion.option"),
        ("stx", syntaxToJson stx)
      ]
  | .errorName stx partialId =>
      Json.mkObj [
        ("kind", toJson "completion.errorName"),
        ("stx", syntaxToJson stx),
        ("partialId", syntaxToJson partialId)
      ]
  | .endSection stx id? danglingDot scopeNames =>
      Json.mkObj [
        ("kind", toJson "completion.endSection"),
        ("stx", syntaxToJson stx),
        ("id", optionToJson nameToJson id?),
        ("danglingDot", toJson danglingDot),
        ("scopeNames", jsonArray <| scopeNames.toArray.map toJson)
      ]
  | .tactic stx =>
      Json.mkObj [
        ("kind", toJson "completion.tactic"),
        ("stx", syntaxToJson stx)
      ]

def userWidgetInfoToJson (info : UserWidgetInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "userWidget"),
    ("stx", syntaxToJson info.stx),
    ("widgetId", nameToJson info.id),
    ("javascriptHash", toJson info.javascriptHash)
  ]

def customInfoToJson (info : CustomInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "custom"),
    ("stx", syntaxToJson info.stx)
  ]

def fvarAliasInfoToJson (info : FVarAliasInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "fvarAlias"),
    ("userName", nameToJson info.userName),
    ("id", fvarIdToJson info.id),
    ("baseId", fvarIdToJson info.baseId)
  ]

def fieldRedeclInfoToJson (info : FieldRedeclInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "fieldRedecl"),
    ("stx", syntaxToJson info.stx)
  ]

def delabTermInfoToJson (maxExpectedExprNodes? : Option Nat) (info : DelabTermInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "delabTerm"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx),
    ("lctxSize", lctxSizeToJson info.lctx),
    ("expectedType", optionToJson (expectedTypeToJson maxExpectedExprNodes?) info.expectedType?),
    ("expr", exprToJson info.expr),
    ("isBinder", toJson info.isBinder),
    ("isDisplayableTerm", toJson info.isDisplayableTerm),
    ("explicit", toJson info.explicit),
    ("docString", optionToJson toJson info.docString?),
    ("location", optionToJson (fun loc => toJson (reprStr loc)) info.location?)
  ]

def choiceInfoToJson (info : ChoiceInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "choice"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx)
  ]

def docInfoToJson (info : DocInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "doc"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx)
  ]

def docElabInfoToJson (info : DocElabInfo) : Json :=
  Json.mkObj [
    ("kind", toJson "docElab"),
    ("elaborator", nameToJson info.elaborator),
    ("stx", syntaxToJson info.stx),
    ("name", nameToJson info.name),
    ("docKind", toJson (reprStr info.kind))
  ]

def infoToJson (maxExpectedExprNodes? : Option Nat) (info : Info) : Json :=
  match info with
  | .ofTacticInfo i => tacticInfoToJson i
  | .ofTermInfo i => termInfoToJson maxExpectedExprNodes? i
  | .ofPartialTermInfo i => partialTermInfoToJson maxExpectedExprNodes? i
  | .ofCommandInfo i => commandInfoToJson i
  | .ofMacroExpansionInfo i => macroExpansionInfoToJson i
  | .ofOptionInfo i => optionInfoToJson i
  | .ofErrorNameInfo i => errorNameInfoToJson i
  | .ofFieldInfo i => fieldInfoToJson i
  | .ofCompletionInfo i => completionInfoToJson maxExpectedExprNodes? i
  | .ofUserWidgetInfo i => userWidgetInfoToJson i
  | .ofCustomInfo i => customInfoToJson i
  | .ofFVarAliasInfo i => fvarAliasInfoToJson i
  | .ofFieldRedeclInfo i => fieldRedeclInfoToJson i
  | .ofDelabTermInfo i => delabTermInfoToJson maxExpectedExprNodes? i
  | .ofChoiceInfo i => choiceInfoToJson i
  | .ofDocInfo i => docInfoToJson i
  | .ofDocElabInfo i => docElabInfoToJson i

partial def infoTreeToJson (maxExpectedExprNodes? : Option Nat) (tree : InfoTree) : Json :=
  match tree with
  | .context ctx child =>
      Json.mkObj [
        ("kind", toJson "context"),
        ("context", partialContextToJson ctx),
        ("child", infoTreeToJson maxExpectedExprNodes? child)
      ]
  | .hole mvarId =>
      Json.mkObj [
        ("kind", toJson "hole"),
        ("mvarId", toJson mvarId.name.toString)
      ]
  | .node info children =>
      Json.mkObj [
        ("kind", toJson "node"),
        ("info", infoToJson maxExpectedExprNodes? info),
        ("children", jsonArray <| children.toArray.map (infoTreeToJson maxExpectedExprNodes?))
      ]

partial def writeInfoTreeJsonLimited (handle : IO.FS.Handle) (tree : InfoTree)
    (countRef : IO.Ref Nat) (truncatedRef : IO.Ref Bool) (maxNodes? : Option Nat)
    (maxExpectedExprNodes? : Option Nat) (metricsRef? : Option (IO.Ref StringMetrics)) : IO Unit := do
  if let some maxNodes := maxNodes? then
    let count ← countRef.get
    if count >= maxNodes then
      truncatedRef.set true
      handle.putStr "{\"kind\":\"truncated\"}"
      return ()
  let count ← countRef.get
  countRef.set (count + 1)
  match tree with
  | .context ctx child =>
      handle.putStr "{\"kind\":\"context\",\"context\":"
      handle.putStr (Json.compress (partialContextToJson ctx))
      handle.putStr ",\"child\":"
      if let some metricsRef := metricsRef? then
        recordPartialContext metricsRef ctx
      writeInfoTreeJsonLimited handle child countRef truncatedRef maxNodes? maxExpectedExprNodes? metricsRef?
      handle.putStr "}"
  | .hole mvarId =>
      handle.putStr "{\"kind\":\"hole\",\"mvarId\":"
      handle.putStr (Json.compress (toJson mvarId.name.toString))
      handle.putStr "}"
  | .node info children =>
      if let some metricsRef := metricsRef? then
        recordInfoMetrics metricsRef info maxExpectedExprNodes?
      handle.putStr "{\"kind\":\"node\",\"info\":"
      handle.putStr (Json.compress (infoToJson maxExpectedExprNodes? info))
      handle.putStr ",\"children\":["
      let arr := children.toArray
      for i in [:arr.size] do
        if i > 0 then
          handle.putStr ","
        writeInfoTreeJsonLimited handle (arr[i]!) countRef truncatedRef maxNodes? maxExpectedExprNodes? metricsRef?
      handle.putStr "]}"

structure Config where
  rootDir : System.FilePath := "."
  outDir : System.FilePath := "infotree_out"
  limit : Option Nat := none
  start : Nat := 0
  verbose : Bool := false
  errorLimit : Nat := 3
  maxSeconds : Option Nat := none
  maxInfotreeNodes : Option Nat := none
  singleFile : Option System.FilePath := none
  rssLogMb : Option Nat := none
  memDebug : Bool := false
  continueFlag : Bool := false
  gzip : Bool := false
  skipOnError : Bool := false
  stringMetrics : Bool := false
  stringMetricsCsv : Option System.FilePath := none
  maxExpectedExprNodes : Option Nat := none
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
    | "--max-infotree-nodes" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with maxInfotreeNodes := some n } rest
        | none => throw <| IO.userError s!"Invalid --max-infotree-nodes value: {value}"
    | "--gzip" :: rest =>
        go { cfg with gzip := true } rest
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
    | "--skip-on-error" :: rest =>
        go { cfg with skipOnError := true } rest
    | "--string-metrics" :: rest =>
        go { cfg with stringMetrics := true } rest
    | "--string-metrics-csv" :: value :: rest =>
        go { cfg with stringMetrics := true, stringMetricsCsv := some value } rest
    | "--max-expected-expr-nodes" :: value :: rest =>
        match value.toNat? with
        | some n => go { cfg with maxExpectedExprNodes := some n } rest
        | none => throw <| IO.userError s!"Invalid --max-expected-expr-nodes value: {value}"
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
  let leanFiles := files.filter (·.extension == some "lean")
  return leanFiles.qsort (fun a b => a.toString < b.toString)

def getLakePackagePaths (root : System.FilePath) : IO (Array System.FilePath) := do
  let pkgsDir := root / ".lake" / "packages"
  if !(← pkgsDir.isDir) then
    return #[]
  let entries ← pkgsDir.readDir
  let mut paths : Array System.FilePath := #[]
  for entry in entries do
    if (← entry.path.isDir) then
      let pkgLean := entry.path / ".lake" / "build" / "lib" / "lean"
      if (← pkgLean.isDir) then
        paths := paths.push pkgLean
  return paths

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

@[extern "lean_mi_stats_print"]
opaque miStatsPrint : IO Unit

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
    if let some rssLogMb := cfg.rssLogMb then
      args := args ++ #["--rss-log-mb", toString rssLogMb]
    if cfg.memDebug then
      args := args.push "--mem-debug"
    if cfg.continueFlag then
      args := args.push "--continue"
    if cfg.skipOnError then
      args := args.push "--skip-on-error"
    if cfg.stringMetrics then
      args := args.push "--string-metrics"
    if let some csv := cfg.stringMetricsCsv then
      args := args ++ #["--string-metrics-csv", csv.toString]
    if let some maxNodes := cfg.maxExpectedExprNodes then
      args := args ++ #["--max-expected-expr-nodes", toString maxNodes]
    if cfg.gzip then
      args := args.push "--gzip"
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
    if cfg.skipOnError then
      args := args.push "--skip-on-error"
    if cfg.stringMetrics then
      args := args.push "--string-metrics"
    if let some csv := cfg.stringMetricsCsv then
      args := args ++ #["--string-metrics-csv", csv.toString]
    if let some maxNodes := cfg.maxExpectedExprNodes then
      args := args ++ #["--max-expected-expr-nodes", toString maxNodes]
    if cfg.gzip then
      args := args.push "--gzip"
    return args

structure SetupCache where
  setup : ModuleSetup
  searchPaths : Array System.FilePath
  importsKey : Array Name

initialize setupCacheRef : IO.Ref (Option SetupCache) ← IO.mkRef none

def importsKeyFromHeader (stx : Elab.HeaderSyntax) : Array Name :=
  stx.toModuleHeader.imports.map (fun imp => imp.module)

unsafe def getSetupCache (doc : Lean.Server.DocumentMeta) (stx : Elab.HeaderSyntax) (verbose : Bool) :
    IO SetupCache := do
  let importsKey := importsKeyFromHeader stx
  if let some cache ← setupCacheRef.get then
    if cache.importsKey == importsKey then
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
  let cache := { setup, searchPaths, importsKey }
  setupCacheRef.set (some cache)
  return cache

unsafe def runFrontendForTrees (doc : Lean.Server.DocumentMeta) (verbose : Bool) (errorLimit : Nat)
    (memDebug : Bool) (emitTree? : Option (InfoTree → IO Unit)) :
    IO (Nat × Array Message) := do
  let _ := verbose
  let inputCtx := doc.mkInputContext
  let cmdlineOpts := ({} : Options)
  let cmdlineOpts := cmdlineOpts.setBool `pp.unicode.fun true
  let cmdlineOpts := cmdlineOpts.setBool `autoImplicit false
  let cmdlineOpts := cmdlineOpts.setBool `experimental.module true
  let cmdlineOpts := cmdlineOpts.setBool `backward.privateInPublic true
  let cmdlineOpts := cmdlineOpts.setBool `backward.privateInPublic.warn false
  let cmdlineOpts := cmdlineOpts.setBool `backward.proofsInPublic true
  let cmdlineOpts := cmdlineOpts.setNat `maxSynthPendingDepth 3
  let ctx : ProcessingContext := { inputCtx with }
  let setupFn (stx : Elab.HeaderSyntax) :
      ProcessingT IO (Except Lean.Language.Lean.HeaderProcessedSnapshot
        Lean.Language.Lean.SetupImportsResult) := do
    let header := stx.toModuleHeader
    let mergedOpts := Elab.async.setIfNotSet cmdlineOpts true
    let mergedOpts := Elab.inServer.set mergedOpts false
    let mergedOpts ← liftM <| Lean.Language.Lean.reparseOptions mergedOpts
    return .ok {
      trustLevel := 0
      package? := none
      mainModuleName := doc.mod
      isModule := header.isModule
      imports := header.imports
      plugins := #[]
      importArts := {}
      opts := mergedOpts
    }
  let snap ← Lean.Language.Lean.process setupFn none ctx
  if memDebug then
    logMemDebug "after_process"
  let errorCountRef ← IO.mkRef 0
  let errorMessagesRef ← IO.mkRef (#[] : Array Message)
  let processDiagnostics : Snapshot.Diagnostics → IO Unit := fun diagnostics => do
    for msg in diagnostics.msgLog.toArray do
      if msg.severity == MessageSeverity.error then
        errorCountRef.modify (· + 1)
        let errors ← errorMessagesRef.get
        if errors.size < errorLimit then
          errorMessagesRef.set (errors.push msg)
  let processInfoTree : Option InfoTree → IO Unit := fun tree? => do
    match tree? with
    | some tree =>
        if let some emitTree := emitTree? then
          emitTree tree
    | none => pure ()

  match snap.result? with
  | none => pure ()
  | some headerParsed =>
      let headerProcessed := headerParsed.processedSnap.task.get
      let headerMeta := headerProcessed.metaSnap.task.get
      processDiagnostics headerMeta.diagnostics
      processInfoTree headerMeta.infoTree?
      if let some headerState := headerProcessed.result? then
        let rec loop (next? : Option (SnapshotTask CommandParsedSnapshot)) : IO Unit := do
          match next? with
          | some next =>
              let cmdParsed := next.task.get
              processDiagnostics cmdParsed.diagnostics
              let infoSnap : SnapshotLeaf := cmdParsed.elabSnap.infoTreeSnap.task.get
              processDiagnostics infoSnap.diagnostics
              processInfoTree infoSnap.infoTree?
              loop cmdParsed.nextCmdSnap?
          | none => pure ()
        loop (some headerState.firstCmdSnap)
  if memDebug then
    logMemDebug "after_command_loop"
  let errorCount ← errorCountRef.get
  let errorMessages ← errorMessagesRef.get
  return (errorCount, errorMessages)

def outputJsonPaths (cfg : Config) (relativePath : System.FilePath) :
    System.FilePath × System.FilePath := Id.run do
  let basePath := cfg.outDir / relativePath
  let jsonPath := basePath.withExtension "json"
  let finalPath := if cfg.gzip then basePath.withExtension "json.gz" else jsonPath
  return (jsonPath, finalPath)

unsafe def exportFile (cfg : Config) (file : System.FilePath) (index : Nat) (total : Nat) : IO Unit := do
  let relativePath ← relativeToRoot cfg.rootDir file
  let (jsonPath, finalPath) := outputJsonPaths cfg relativePath
  if cfg.continueFlag then
    if (← finalPath.pathExists) then
      if cfg.verbose then
        IO.println s!"[{index + 1}/{total}] {relativePath} (skip)"
      return ()
  if cfg.verbose then
    IO.println s!"[{index + 1}/{total}] {relativePath}"
  IO.println s!"[infotree_export] start {relativePath}"
  let input ← IO.FS.readFile file
  let moduleName := moduleNameFromPath (dropExtension relativePath)
  let doc : Lean.Server.DocumentMeta := {
    uri := System.Uri.pathToUri file
    mod := moduleName
    version := 0
    text := input.toFileMap
    dependencyBuildMode := .never
  }
  let outputDir := finalPath.parent.getD cfg.outDir
  IO.FS.createDirAll outputDir
  let metricsRef? ←
    if cfg.stringMetrics then
      some <$> IO.mkRef ({} : StringMetrics)
    else
      pure none
  let logEvery := 1000
  let lastLoggedRef ← IO.mkRef 0
  let countRef ← IO.mkRef 0
  let heartbeatRef? ←
    if let some csvPath := cfg.stringMetricsCsv then
      if let some metricsRef := metricsRef? then
        let metrics ← metricsRef.get
        writeStringMetricsCsv csvPath relativePath metrics "start" 0
        some <$> startMetricsHeartbeat csvPath relativePath metricsRef countRef
      else
        pure none
    else
      pure none
  let resultAndWrote ←
    IO.FS.withFile jsonPath .write fun handle => do
      handle.putStr "{\"infotrees\":["
      let firstRef ← IO.mkRef true
      let truncatedRef ← IO.mkRef false
      let emitTree := fun tree => do
        let truncated ← truncatedRef.get
        if truncated then
          return ()
        let first ← firstRef.get
        if first then
          firstRef.set false
        else
          handle.putStr ","
        writeInfoTreeJsonLimited handle tree countRef truncatedRef cfg.maxInfotreeNodes cfg.maxExpectedExprNodes metricsRef?
        if let some csvPath := cfg.stringMetricsCsv then
          if let some metricsRef := metricsRef? then
            let count ← countRef.get
            let lastLogged ← lastLoggedRef.get
            if count == 1 || count - lastLogged >= logEvery then
              let metrics ← metricsRef.get
              writeStringMetricsCsv csvPath relativePath metrics "progress" count
              lastLoggedRef.set count
      let result ←
        runFrontendForTrees doc cfg.verbose cfg.errorLimit cfg.memDebug (some emitTree)
      let truncated ← truncatedRef.get
      let count ← countRef.get
      handle.putStr "]"
      handle.putStr ",\"truncated\":"
      handle.putStr (Json.compress (toJson truncated))
      handle.putStr ",\"truncated_at\":"
      handle.putStr (toString count)
      handle.putStr "}"
      handle.flush
      pure (result, true)
  let (result, wroteOutput) := resultAndWrote
  let (errorCount, errors) := result
  if let some heartbeatRef := heartbeatRef? then
    heartbeatRef.set false
  if let some metricsRef := metricsRef? then
    let metrics ← metricsRef.get
    IO.eprintln s!"[infotree_export] string-metrics {relativePath} expr_bytes={metrics.exprBytes} expr_max={metrics.exprMax} expr_count={metrics.exprCount} expected_bytes={metrics.expectedBytes} expected_max={metrics.expectedMax} expected_count={metrics.expectedCount} expected_skipped={metrics.expectedSkipped} expected_skipped_max={metrics.expectedSkippedMax} doc_bytes={metrics.docBytes} doc_max={metrics.docMax} doc_count={metrics.docCount}"
    if let some csvPath := cfg.stringMetricsCsv then
      let count ← countRef.get
      writeStringMetricsCsv csvPath relativePath metrics "done" count

  if errorCount > 0 then
    IO.eprintln s!"[infotree_export] errors while processing {relativePath}"
    for msg in errors do
      let msg ← msg.toString
      IO.eprintln msg
    if cfg.skipOnError then
      IO.eprintln s!"[infotree_export] skipping output for {relativePath}"
      if wroteOutput then
        IO.FS.removeFile jsonPath
      return ()

  if cfg.gzip then
    let child ← IO.Process.spawn {
      cmd := "gzip"
      args := #["-f", jsonPath.toString]
      stdout := .inherit
      stderr := .inherit
    }
    let _ ← child.wait
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

unsafe def main (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  IO.Process.setCurrentDir cfg.rootDir
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let lakeLib := cfg.rootDir / ".lake" / "build" / "lib" / "lean"
  let pkgPaths ← getLakePackagePaths cfg.rootDir
  mergeSearchPath (#[lakeLib, cfg.rootDir] ++ pkgPaths)
  if let some file := cfg.singleFile then
    if let some maxSeconds := cfg.maxSeconds then
      let ok ← runSingleFileWithTimeout cfg file maxSeconds
      if !ok then
        IO.eprintln s!"[infotree_export] timeout after {maxSeconds}s: {file}"
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir file
        logMemDebug s!"after_gc {relativePath}"
    else
      Lean.withImporting do
        exportFile cfg file 0 1
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
    IO.println s!"Exporting infotrees for {slice.size} files..."
  for h : i in [0:slice.size] do
    if let some maxSeconds := cfg.maxSeconds then
      let ok ← runSingleFileWithTimeout cfg (slice[i]) maxSeconds
      if !ok then
        IO.eprintln s!"[infotree_export] timeout after {maxSeconds}s: {slice[i]}"
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir (slice[i])
        logMemDebug s!"after_gc {relativePath}"
    else
      Lean.withImporting do
        exportFile cfg (slice[i]) i slice.size
      if cfg.memDebug then
        let relativePath ← relativeToRoot cfg.rootDir (slice[i])
        logMemDebug s!"after_gc {relativePath}"
