import Mettapedia.GSLT.LanguageDef.GSLTILNativeKernelWire

/-!
# Executable native GSLT-ML command-journal client

Requests use the exact finite alphabet `0`, `1`, `e`, `a`, `p`, without
whitespace. The catalog profile checks derivations relative to the complete
submitted finite catalog. The Tick profile checks the fixed unbounded native
fibre. The format is structural command/evidence data, not `.module` text.

The client invokes the source-native reference checker directly. Its primitive
request/lookup bounds are separate from compiler correctness and physical
running-time claims. It neither searches for missing proofs nor interprets
unknown command frames in another language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel.Client

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

private def atom (name : String) : Pattern := .apply name []
private def a := atom "a"
private def b := atom "b"
private def c := atom "c"
private def finish := atom "finished"
private def stage := atom "A"
private def targetStage := atom "B"
private def kind := atom "forward"
private def route := atom "copy"

private def firstRow : FibreRow := ⟨atom "local-rule", stage, a, b⟩
private def laterRow : FibreRow := ⟨atom "later-rule", stage, b, c⟩
private def firstTransport : TransportRow :=
  ⟨atom "transport-0", kind, route, stage, targetStage, b, finish⟩
private def laterTransport : TransportRow :=
  ⟨atom "transport-1", kind, route, stage, targetStage, c, finish⟩

private def catalog : Catalog :=
  ⟨[firstRow, firstRow, laterRow], [firstTransport, laterTransport]⟩
private def pending : Command := .via kind route stage targetStage a
private def returned : Command := .at targetStage finish

private def complete : List (Entry Nat Nat) := [.underneath b 0, .transport finish 0]
private def longer : List (Entry Nat Nat) :=
  [.underneath b 1, .underneath c 2, .transport finish 1]

private def authoredProgram : Syntax.Program :=
  ⟨[⟨atom "authored-row", stage, a, b⟩], [], []⟩
private def rawSubstitution := Pattern.subst (.bvar 0) a
private def rawCatalog : Catalog :=
  ⟨[⟨atom "raw-syntax", stage, rawSubstitution, b⟩], []⟩

private def controls : List (String × Wire.Packet × Bool) :=
  [ ("catalog-two-rules", .catalog catalog pending returned complete, true)
  , ("catalog-three-rules", .catalog catalog pending returned longer, true)
  , ("first-equal-row-occurrence", .catalog catalog (.at stage a) (.at stage b) [.fibre b 0], true)
  , ("second-equal-row-occurrence", .catalog catalog (.at stage a) (.at stage b) [.fibre b 1], true)
  , ("empty-journal-reflexivity", .catalog catalog pending pending [], true)
  , ("empty-journal-cannot-advance", .catalog catalog pending returned [], false)
  , ("missing-inference", .catalog catalog pending returned [.underneath b 0], false)
  , ("extra-inference", .catalog catalog pending returned (complete ++ [.fibre finish 0]), false)
  , ("wrong-final-command", .catalog catalog pending (.at stage finish) complete, false)
  , ("wrong-intermediate-state", .catalog catalog pending returned [.underneath c 0, .transport finish 1], false)
  , ("unknown-fibre-ordinal", .catalog catalog (.at stage a) (.at stage b) [.fibre b 99], false)
  , ("unknown-transport-ordinal", .catalog catalog pending returned [.underneath b 0, .transport finish 99], false)
  , ("wrong-command-role", .catalog catalog (.at stage a) (.at stage b) [.underneath b 0], false)
  , ("transport-cannot-run-at-returned-state", .catalog catalog (.at stage b) returned [.transport finish 0], false)
  , ("wrong-source-stage", .catalog catalog (.at targetStage a) (.at targetStage b) [.fibre b 0], false)
  , ("wrong-route-kind", .catalog catalog (.via (atom "exact") route stage targetStage b)
      returned [.transport finish 0], false)
  , ("wrong-route-identity", .catalog catalog (.via kind (atom "other") stage targetStage b)
      returned [.transport finish 0], false)
  , ("wrong-transport-target-stage", .catalog catalog (.via kind route stage stage b)
      (.at stage finish) [.transport finish 0], false)
  , ("unbounded-fibre", .tick (.at Tick.stage (Tick.states 32))
      (.at Tick.stage (Tick.states 33)) [.fibre (Tick.states 33) ()], true)
  , ("reduce-then-transport", .tick
      (.via Tick.forward Tick.identityRoute Tick.stage Tick.stage a)
      (.at Tick.stage (Tick.tick a)) (Tick.underneathThenTransport a), true)
  , ("transport-then-reduce", .tick
      (.via Tick.forward Tick.identityRoute Tick.stage Tick.stage a)
      (.at Tick.stage (Tick.tick a)) (Tick.transportThenFibre a), true)
  , ("unbounded-fibre-does-not-skip", .tick (.at Tick.stage a)
      (.at Tick.stage (Tick.tick (Tick.tick a))) [.fibre (Tick.tick (Tick.tick a)) ()], false)
  , ("unbounded-unknown-stage", .tick (.at stage a)
      (.at stage (Tick.tick a)) [.fibre (Tick.tick a) ()], false)
  , ("authored-in-lowers-to-native-at", .catalog authoredProgram.toCatalog
      (.at stage a) (.at stage b) [.fibre b 0], true)
  , ("raw-substitution-remains-data", .catalog rawCatalog
      (.at stage rawSubstitution) (.at stage b) [.fibre b 0], true)
  , ("implicit-normalization-not-admitted", .catalog rawCatalog
      (.at stage a) (.at stage b) [.fibre b 0], false)
  ]

private def payloads : List Pattern :=
  [ .bvar 37, .fvar "$literal?"
  , .apply "λ🙂" [.fvar "x", .fvar "x"]
  , .lambda (some "named") (.bvar 0)
  , .multiLambda 2 ["left", "right"] (.bvar 1)
  , .subst (.bvar 0) (.fvar "replacement")
  , .collection .vec [a, b, a] (some "tail")
  , .collection .hashBag [b, a, a] none
  , .collection .hashSet [a, a, b] (some "rest") ]

private def require (name : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("failed: " ++ name))

private def runControls : IO UInt32 := do
  let mut assertions := 0
  for (name, packet, expected) in controls do
    let word := Wire.encode packet
    require (name ++ " source-check") (packet.check == expected)
    require (name ++ " canonical-wire") ((Wire.checkWord word).isSome == expected)
    require (name ++ " complete-packet")
      ((Wire.packetCodec.get (Wire.packetCodec.put packet)).map Wire.packetCodec.put ==
        some (Wire.packetCodec.put packet))
    require (name ++ " text") (Text.parse (Text.render word) == some word)
    require (name ++ " truncated") ((Wire.checkWord (word.take (word.length - 1))).isNone)
    require (name ++ " trailing") ((Wire.checkWord (word ++ [0])).isNone)
    assertions := assertions + 6
  for payload in payloads do
    let payloadCatalog : Catalog := ⟨[⟨atom "payload-rule", stage, payload, payload⟩], []⟩
    let packet : Wire.Packet := .catalog payloadCatalog (.at stage payload) (.at stage payload) [.fibre payload 0]
    let word := Wire.encode packet
    require "all original Pattern fields remain data" ((Wire.checkWord word).isSome)
    require "all original Pattern fields roundtrip"
      ((Wire.packetCodec.get (Wire.packetCodec.put packet)).map Wire.packetCodec.put ==
        some (Wire.packetCodec.put packet))
    assertions := assertions + 2
  let packet : Wire.Packet := .catalog catalog pending returned complete
  let word := Wire.encode packet
  let changedCatalog : Catalog := { catalog with fibreRows :=
    { firstRow with occurrence := atom "different-authority" } :: catalog.fibreRows.tail }
  require "installed header accepts exact original" ((Wire.checkAgainst catalog word).isSome)
  require "changed original occurrence header refuses" ((Wire.checkAgainst changedCatalog word).isNone)
  require "duplicate row ordinals remain distinct native articles"
    (Wire.encode (.catalog catalog (.at stage a) (.at stage b) [.fibre b 0]) !=
      Wire.encode (.catalog catalog (.at stage a) (.at stage b) [.fibre b 1]))
  require "malformed command frame" ((Wire.commandCodec.get (.pair (.atom 0) (.atom 0))).isNone)
  require "unknown command tag" ((Wire.commandCodec.get (.pair (.atom 99) (.atom 0))).isNone)
  require "unknown evidence tag" (((Wire.entryCodec Codec.nat Codec.nat).get
    (.pair (.atom 99) (.atom 0))).isNone)
  let unknownVersion := match Wire.packetCodec.put packet with
    | .pair _ fields => .pair (Codec.string.put "GSLT.NativeCommand.v2") fields
    | other => other
  let unknownProfile := .pair (Codec.string.put Wire.packetTag) (.pair (.atom 99) (.atom 0))
  require "unknown version" ((Wire.checkWord (Binary.writeData unknownVersion [])).isNone)
  require "unknown profile" ((Wire.checkWord (Binary.writeData unknownProfile [])).isNone)
  require "unknown alphabet" ((Text.parse "?").isNone)
  require "whitespace is not a symbol" ((Text.parse " ").isNone)
  let counted := replayWithRequests (catalogChecking catalog) pending complete
  require "instrumented replay is the original replay" (counted.1 == replay (catalogChecking catalog) pending complete)
  require "each accepted occurrence requested exactly once" (counted.2 == complete.length)
  require "out-of-range lookup stops at actual catalog boundary"
    ((lookupWithVisits catalog.fibreRows 1000000).2 == catalog.fibreRows.length)
  assertions := assertions + 13
  IO.println s!"native GSLT-ML command evidence: {assertions} controls PASS"
  return 0

private def exportControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, packet, expected) in controls do
    let file := name ++ ".gslt-proof"
    IO.FS.writeFile (directory / file) (Text.render (Wire.encode packet))
    rows := rows ++ [file ++ "\t" ++ if expected then "accepted" else "refused"]
  let original := Text.render (Wire.encode (.catalog catalog pending returned complete))
  let malformed : List (String × String × String) :=
    [("truncated", String.ofList (original.toList.take (original.length - 1)), "refused"),
     ("trailing", original ++ "0", "refused"),
     ("invalid-alphabet", "?", "invalid")]
  for (name, input, expected) in malformed do
    let file := name ++ ".gslt-proof"
    IO.FS.writeFile (directory / file) input
    rows := rows ++ [file ++ "\t" ++ expected]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {controls.length + malformed.length} requests"
  return 0

private def checkFile (path : System.FilePath) : IO UInt32 := do
  let input ← IO.FS.readFile path
  match Text.parse input with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match Wire.checkWord word with
      | none => IO.println "refused"; return 1
      | some packet =>
          match packet with
          | .catalog _ first last journal =>
              IO.println s!"accepted catalog command path: {journal.length} steps"
              IO.println s!"from {repr first.toPattern} to {repr last.toPattern}"
          | .tick first last journal =>
              IO.println s!"accepted unbounded Tick command path: {journal.length} steps"
              IO.println s!"from {repr first.toPattern} to {repr last.toPattern}"
          return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["controls"] => runControls
  | ["export-controls", directory] => exportControls directory
  | ["check", file] => checkFile file
  | _ =>
      IO.println "gsltNativeCheck controls | export-controls <directory> | check <request-file>"
      return 2

end Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel.Client

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel.Client.run arguments
