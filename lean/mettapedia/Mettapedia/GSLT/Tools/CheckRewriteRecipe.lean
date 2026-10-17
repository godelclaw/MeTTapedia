import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionControls

/-!
# Executable authored rewrite-recipe checker

The client accepts the exact structural request formats for one rewrite,
literal composed traces, equation-respecting semantic traces and shared DAGs. Every
request carries its authored declarations and permissions. The reference
checker compiles that header and validates the supplied choices and joins.

The text alphabet is `0`, `1`, `e`, `a`, `p`, without whitespace. It serializes
structured language data; it is not a parser for authored `.module` text.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.CheckRewriteRecipe

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.Binding.WireCodec
open Binary


private inductive Packet where
  | atomic (request : GeneralRewriteRecipeWire.Request)
  | trace (request : GeneralRewriteRecipeCompositionWire.TraceRequest)
  | semantic (request : GeneralRewriteRecipeCompositionWire.SemanticRequest)
  | graph (request : GeneralRewriteRecipeCompositionWire.DAGRequest)

private def Packet.encode : Packet → List Alphabet
  | .atomic request => GeneralRewriteRecipeWire.encodeRequest request
  | .trace request => GeneralRewriteRecipeCompositionWire.encodeTraceRequest request
  | .semantic request => GeneralRewriteRecipeCompositionWire.encodeSemanticRequest request
  | .graph request => GeneralRewriteRecipeCompositionWire.encodeDAGRequest request

private def acceptedWord (word : List Alphabet) : Bool :=
  GeneralRewriteRecipeWire.checkWord word ||
    GeneralRewriteRecipeCompositionWire.checkTraceWord word ||
    GeneralRewriteRecipeCompositionWire.checkSemanticWord word ||
    GeneralRewriteRecipeCompositionWire.checkDAGWord word

private def packets : Option (List (String × Packet × Bool)) := do
  let base ← GeneralRewriteRecipeControls.fixture
  let reversed ← GeneralRewriteRecipeControls.reverseFixture
  let direct ← GeneralRewriteRecipeControls.directFixture
  let nested ← GeneralRewriteRecipeControls.Arithmetic.nestedRequest?
  let binder ← GeneralRewriteRecipeControls.Arithmetic.binderRequest?
  let bagFirst ← GeneralRewriteRecipeControls.Arithmetic.bagRequest? 0
  let bagSecond ← GeneralRewriteRecipeControls.Arithmetic.bagRequest? 1
  let leftFirst ← GeneralRewriteRecipeControls.Arithmetic.parallelTrace? true
  let rightFirst ← GeneralRewriteRecipeControls.Arithmetic.parallelTrace? false
  let shared ← GeneralRewriteRecipeCompositionControls.DAG.sharedFixture
  let conversion ← GeneralRewriteRecipeCompositionControls.DAG.conversionFixture
  let equationOnly ← GeneralRewriteRecipeCompositionControls.Composed.equationOnly
  let appended ← GeneralRewriteRecipeCompositionControls.Composed.appendFixture
  let arithmeticHeader : GeneralRewriteRecipeCompositionWire.Header :=
    ⟨GeneralRewriteRecipeControls.Arithmetic.snapshot, GeneralRewriteRecipeControls.Arithmetic.permissions, [], GeneralRewriteRecipeControls.Arithmetic.nat,
      GeneralRewriteRecipeControls.Arithmetic.pairSource, GeneralRewriteRecipeControls.Arithmetic.pairTarget⟩
  let trace : GeneralRewriteRecipeCompositionWire.TraceRequest := ⟨arithmeticHeader, leftFirst⟩
  let semantic : GeneralRewriteRecipeCompositionWire.SemanticRequest :=
    ⟨GeneralRewriteRecipeCompositionWire.Header.ofAtomic base,
      ⟨base.source, base.target, [], [⟨base.target, base.step⟩], []⟩⟩
  let damagedJoin := leftFirst.mapIdx fun index link =>
    if index = 0 then {link with next := GeneralRewriteRecipeControls.Arithmetic.rightMiddle} else link
  pure [
    ("atomic-equations-before-and-after", .atomic base, true),
    ("atomic-reverse-equation", .atomic reversed, true),
    ("atomic-equation-loop", .atomic (GeneralRewriteRecipeControls.loopRequest base), true),
    ("atomic-direct", .atomic direct, true),
    ("atomic-inside-constructor", .atomic nested, true),
    ("atomic-inside-binder", .atomic binder, true),
    ("atomic-equal-bag-first-choice", .atomic bagFirst, true),
    ("atomic-equal-bag-second-choice", .atomic bagSecond, true),
    ("atomic-wrong-target", .atomic {base with target := GeneralRewriteRecipeControls.a}, false),
    ("atomic-forged-rule", .atomic (GeneralRewriteRecipeControls.mapFiring base fun firing =>
      {firing with job := {firing.job with ordinal := 99}}), false),
    ("atomic-extra-match-choice", .atomic (GeneralRewriteRecipeControls.mapFiring base fun firing =>
      {firing with matcherTrace := [{path := [], selected := 0}]}), false),
    ("atomic-missing-post-equation", .atomic {base with step := {base.step with after := []}}, false),
    ("trace-left-then-right", .trace trace, true),
    ("trace-right-then-left", .trace ⟨arithmeticHeader, rightFirst⟩, true),
    ("trace-forged-join", .trace ⟨arithmeticHeader, damagedJoin⟩, false),
    ("trace-wrong-target", .trace {trace with header := {arithmeticHeader with target := GeneralRewriteRecipeControls.Arithmetic.zero}}, false),
    ("trace-missing-step", .trace {trace with trace := leftFirst.take 1}, false),
    ("semantic-equation-backed-path", .semantic semantic, true),
    ("semantic-wrong-target", .semantic {semantic with header := {semantic.header with target := GeneralRewriteRecipeControls.a}}, false),
    ("semantic-equation-only", .semantic equationOnly, true),
    ("semantic-appended-history", .semantic appended, true),
    ("literal-empty-cannot-substitute-equivalence", .trace ⟨equationOnly.header, []⟩, false),
    ("dag-five-nodes-eight-uses", .graph shared, true),
    ("dag-earlier-root-two-uses", .graph {shared with graph := {shared.graph with root := 2}}, true),
    ("dag-equation-detour", .graph conversion, true),
    ("dag-invalid-unused-reference", .graph {shared with graph := {shared.graph with nodes :=
      shared.graph.nodes ++ [.trans shared.header.source shared.header.source shared.header.target 99 99]}}, false),
    ("dag-self-reference", .graph ⟨shared.header,
      ⟨[.trans shared.header.source shared.header.source shared.header.target 0 0], 0⟩⟩, false),
    ("dag-missing-root", .graph {shared with graph := {shared.graph with root := 99}}, false),
    ("dag-forged-goal", .graph {shared with header := {shared.header with target := GeneralRewriteRecipeControls.d}}, false),
    ("dag-revoked-rule", .graph {shared with header := {shared.header with permissions :=
      {shared.header.permissions with ruleIndices := some []}}}, false),
    ("dag-revoked-equation", .graph {conversion with header := {conversion.header with permissions :=
      {conversion.header.permissions with equationIndices := some []}}}, false)]

private def require (name : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("failed: " ++ name))

private def runControls : IO UInt32 := do
  let some checks := GeneralRewriteRecipeCompositionControls.checks? |
    throw (IO.userError "authored composition control construction failed")
  for (name, passed) in checks do require name passed
  let some cases := packets | throw (IO.userError "authored control construction failed")
  let mut count := checks.length
  for (name, packet, expected) in cases do
    let word := packet.encode
    require (name ++ " exact checker") (acceptedWord word == expected)
    require (name ++ " text roundtrip") (Text.parse (Text.render word) == some word)
    require (name ++ " trailing refusal") (!acceptedWord (word ++ [0]))
    require (name ++ " truncation refusal") (!acceptedWord (word.take (word.length - 1)))
    count := count + 4
  IO.println s!"{count}/{count} authored rewrite-recipe controls passed"
  return 0

private def exportControls (directory : System.FilePath) : IO UInt32 := do
  let some cases := packets | throw (IO.userError "authored control construction failed")
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected\texit"]
  for (name, packet, expected) in cases do
    let file := name ++ ".rewrite-proof"
    IO.FS.writeFile (directory / file) (Text.render packet.encode)
    rows := rows ++ [file ++ (if expected then "\taccepted\t0" else "\trefused\t1")]
  let some (_, sample, _) := cases.head? | throw (IO.userError "no control request")
  for (name, word) in [("trailing", sample.encode ++ [0]),
      ("truncated", sample.encode.take (sample.encode.length - 1)), ("empty", [])] do
    let file := name ++ ".rewrite-proof"
    IO.FS.writeFile (directory / file) (Text.render word)
    rows := rows ++ [file ++ "\trefused\t1"]
  IO.FS.writeFile (directory / "invalid-alphabet.rewrite-proof") "?"
  rows := rows ++ ["invalid-alphabet.rewrite-proof\tinvalid\t2"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {rows.length - 1} requests"
  return 0

private def checkFile (path : System.FilePath) : IO UInt32 := do
  let input ← IO.FS.readFile path
  match Text.parse input with
  | none => IO.println "invalid request alphabet"; return 2
  | some word =>
      if acceptedWord word then IO.println "accepted"; return 0
      else IO.println "refused"; return 1

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["controls"] => runControls
  | ["export-controls", directory] => exportControls directory
  | ["check", file] => checkFile file
  | _ =>
      IO.println "gsltRewriteCheck controls | export-controls <directory> | check <request-file>"
      return 2

end Mettapedia.GSLT.Tools.CheckRewriteRecipe

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.CheckRewriteRecipe.run arguments
