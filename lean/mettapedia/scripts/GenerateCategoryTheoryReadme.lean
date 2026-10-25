import Lean
import Mettapedia.CategoryTheory.FuzzyFrame
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mettapedia.DocText.CategoryTheoryReadmeCompositional

/-! Source-token inventory and bounded README regeneration. Counts are diagnostics,
not kernel qualification. The lexer consumes comments and literals using Lean's
own routines; unknown notation punctuation is only a separator for this census. -/

open Lean Parser
open Mettapedia.DocText.CategoryTheoryReadmeCompositional

namespace CategoryTheoryInventory

def markers : Array String := #["sorry", "admit", "aby", "theorem_wanted", "native_decide", "axiom"]
def startMarker := "<!-- category-theory-source-inventory:start -->"
def endMarker := "<!-- category-theory-source-inventory:end -->"

/-- Documentation comments are tokens in Lean's parser, so skip their bodies explicitly. -/
partial def space : ParserFn := fun c s =>
  let s := whitespace c s
  let i := s.pos
  if c.get i == '/' && c.get (c.next i) == '-' &&
      (c.get (c.next (c.next i)) == '-' || c.get (c.next (c.next i)) == '!') then
    andthenFn (finishCommentBlock (pushMissingOnError := false) 1) space c (s.setPos (c.next (c.next i)))
  else s

partial def tokens : ParserFn := fun c s =>
  let s := space c s
  if s.hasError || c.atEnd s.pos then s
  else
    let next := tokenFn [] c s
    if next.hasError then
      let current := c.get s.pos
      if next.pos == s.pos && !isIdFirst current && current != '"' && current != '\'' then
        tokens c (s.setPos (c.next s.pos))
      else next
    else tokens c next

def scanText (env : Environment) (text : String) : Except String (Array Nat) := Id.run do
  let context := mkInputContext text "source"
  let state := tokens.run context {env, options := {}} (getTokenTable env) (mkParserState context.inputString)
  if state.hasError || state.pos != context.endPos then
    return .error (state.toErrorMsg context)
  let mut counts := Array.replicate markers.size 0
  for stx in state.stxStack.extract 0 state.stxStack.size do
    let word := match stx with
      | .atom _ value => value
      | .ident _ raw _ _ => raw.toString
      | _ => ""
    if let some index := markers.toList.idxOf? word then
      counts := counts.modify index (· + 1)
  return .ok counts

partial def sourceFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for entry in ← dir.readDir do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type == .dir && !(["Archive", "MessyWIP", ".lake", ".git"].contains entry.fileName) then
      found := found ++ (← sourceFiles entry.path)
    else if metadata.type == .file && entry.path.extension == some "lean" then
      found := found.push entry.path
  return found.qsort (fun a b => a.toString < b.toString)

def countsJson (counts : Array Nat) : Json :=
  Json.mkObj ((markers.toList.zip counts.toList).map fun (name, count) => (name, toJson count))

def inventory (env : Environment) : IO Json := do
  let paths ← sourceFiles "Mettapedia/CategoryTheory"
  let mut totals := Array.replicate markers.size 0
  let mut positive := #[]
  for path in paths do
    let text ← IO.FS.readFile path
    let counts ← match scanText env text with
      | .ok counts => pure counts
      | .error message => throw (IO.userError s!"Cannot scan {path}: {message}")
    totals := totals.zipWith (· + ·) counts
    if counts.any (· != 0) then
      positive := positive.push (Json.mkObj [("file", toJson path.toString), ("tokens", countsJson counts)])
  return Json.mkObj [("scope", toJson "Mettapedia/CategoryTheory"), ("file_count", toJson paths.size),
    ("token_counts", countsJson totals), ("files_with_tokens", toJson positive)]

/-- Change only the marked region; first insertion retains the authored section. -/
def updateReadme (text block : String) : Except String String :=
  let marked := startMarker ++ "\n" ++ block.trimAsciiEnd.toString ++ "\n" ++ endMarker
  match text.splitOn startMarker with
  | [before, rest] =>
      match rest.splitOn endMarker with
      | [_, after] => .ok (before ++ marked ++ after)
      | _ => .error "Expected exactly one inventory end marker"
  | [_] =>
      if (text.splitOn endMarker).length != 1 then .error "Inventory end marker has no start marker"
      else match text.splitOn "\n## Dependency flow" with
      | [before, after] =>
          if (before.splitOn "\n## Formalization status\n").length != 2 then
            .error "Expected the authored formalization-status section"
          else .ok (before ++ marked ++ "\n\n## Dependency flow" ++ after)
      | _ => .error "Expected exactly one dependency-flow heading"
  | _ => .error "Expected at most one inventory start marker"

def selfTest (env : Environment) : IO Unit := do
  let samples : Array (String × Option (Array Nat)) := #[
    ("/- sorry /- admit -/ -/ /-- native_decide -/ /-! axiom -/", some #[0, 0, 0, 0, 0, 0]),
    ("#check \"sorry\\\"admit\"\n#check r###\"native_decide\"###", some #[0, 0, 0, 0, 0, 0]),
    ("def «sorry» := 'a'", some #[0, 0, 0, 0, 0, 0]),
    ("-- sorry\r\nadmit", some #[0, 1, 0, 0, 0, 0]),
    ("example : False := by sorry", some #[1, 0, 0, 0, 0, 0]),
    ("admit aby theorem_wanted native_decide axiom", some #[0, 1, 1, 1, 1, 1]),
    ("∑' x, x ⟶ y", some #[0, 0, 0, 0, 0, 0]),
    ("/- unterminated", none), ("\"unterminated", none)]
  for (text, expected) in samples do
    unless (scanText env text).toOption == expected do
      throw (IO.userError s!"Lexer control failed: {repr text}")
  let authored := "before\n## Formalization status\nkept\n\n## Dependency flow\nafter"
  let .ok inserted := updateReadme authored "first"
    | throw (IO.userError "First inventory insertion failed")
  let .ok replaced := updateReadme inserted "second"
    | throw (IO.userError "Inventory replacement failed")
  unless replaced == authored.replace "\n## Dependency flow"
      (startMarker ++ "\nsecond\n" ++ endMarker ++ "\n\n## Dependency flow") do
    throw (IO.userError "Inventory replacement changed authored content")
  for malformed in [startMarker, endMarker, inserted ++ startMarker, inserted ++ endMarker] do
    unless (updateReadme malformed "replacement").toOption.isNone do
      throw (IO.userError "Malformed inventory markers were accepted")
  IO.println s!"Controls passed: {samples.size} lexer cases, insertion, replacement, four malformed regions"

unsafe def loadEnvironment : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules #[{module := `Lean}, {module := `Mettapedia.CategoryTheory.FuzzyFrame},
    {module := `Mathlib.Topology.Algebra.InfiniteSum.Defs}] {} (loadExts := true)

unsafe def run (args : List String) : IO UInt32 := do
  unless args == [] || args == ["--check"] || args == ["--write"] || args == ["--self-test"] do
    throw (IO.userError "Usage: GenerateCategoryTheoryReadme.lean [--check|--write|--self-test]")
  let env ← loadEnvironment
  if args == ["--self-test"] then
    selfTest env
    return 0
  unless ← ("lean-toolchain" : System.FilePath).pathExists do
    throw (IO.userError "Run from the MeTTapedia Lean project root")
  let path : System.FilePath := "Mettapedia/CategoryTheory/README.md"
  let original ← IO.FS.readFile path
  let report ← inventory env
  let updated ← match updateReadme original (sourceInventoryMarkdown report) with
    | .ok updated => pure updated
    | .error message => throw (IO.userError message)
  if updated == original then
    IO.println "Source inventory is current"
    return 0
  if args == ["--write"] then
    unless (← IO.FS.readFile path) == original do
      throw (IO.userError "README changed during inventory; rerun without overwriting the concurrent edit")
    IO.FS.writeFile path updated
    IO.println s!"Updated source inventory in {path}"
    return 0
  IO.eprintln "Source inventory is stale; run with --write to update its marked block"
  return 1

end CategoryTheoryInventory

unsafe def main (args : List String) : IO UInt32 := do
  try CategoryTheoryInventory.run args
  catch error => IO.eprintln error.toString; pure 1
