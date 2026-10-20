import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecutionControls
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-! Generate source-bound append queries; independently check entire returned
arrays, observation bags, retained cursors and verdicts. The target executes
both append and native checking. No Lean search result is replayed as a query. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Bridges.MeTTaIL
open Bridges.NativeTypes IndexedAppend IndexedAppend.Controls SpatialRuntime
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.GSLT.LanguageDef IndexedInductive

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "observation fixture has no exact source rendering")

private def expected (test : Fixture) : Atom :=
  .expression [.symbol "InductiveAppendObservation", .grounded (.string test.label),
    IndexedAppendExecution.observation (test.left ++ test.right) test.result]

private def rounds (budget : Nat) : List Nat :=
  List.replicate (budget / 32) 32 ++ [budget % 32]

private theorem rounds_sum (budget : Nat) : (rounds budget).sum = budget := by
  simp only [rounds, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil, Nat.add_zero,
    smul_eq_mul]
  omega

private theorem fixture_result (test : Fixture) :
    IndexedAppendExecution.result (BagModel.sizeExactly test.count)
      (Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend.sizeExactly_admitted test.count)
      test.left test.right (rounds test.first ++ rounds test.more) = test.result := by
  simp only [IndexedAppendExecution.result, List.sum_append, rounds_sum, Fixture.result,
    session, Execution.Session.resume_add]

private def generate (directory : System.FilePath) (submitted : Option String := none) : IO Unit := do
  let controls := checks ++ IndexedAppendExecution.Controls.checks
  for (label, passed) in controls do
    unless passed do throw (IO.userError s!"shared checker control failed: {label}")
  let some program := Bridges.IndexedInductiveAppend.emit? AppendSource.IndexedNatVecAppend.module
    | throw (IO.userError "authored append specialization refused")
  if let some actual := submitted then
    unless actual == program do throw (IO.userError "submitted emission differs from the proved library")
  let program := submitted.getD program
  let assembled := program ++ "\n" ++ SpatialRuntime.source.text ++ "\n" ++ IndexedAppendExecution.source.text
  let .ok parsed := SpaceSemantics.readProgram assembled
    | throw (IO.userError "composed library did not parse")
  unless reprStr parsed == reprStr IndexedAppendExecution.library.runtime do
    throw (IO.userError "composed source differs from the proved runtime")
  let mut queries := ""
  for test in fixtures do
    let code := IndexedAppendExecution.checkCall (BagModel.sizeExactly test.count)
      test.left test.right (rounds test.first ++ rounds test.more)
    queries := queries ++ "!(let $packet " ++ (← render code) ++
      s!" (println! (InductiveAppendObservation {reprStr test.label} $packet)))\n"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "append-observations.metta")
    (assembled ++ "\n" ++ queries)
  IO.println s!"{controls.length} shared and composed controls; generated {fixtures.length} observation queries"

private def check (text : String) : IO Unit := do
  let mut seen : List String := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "(InductiveAppendObservation" then
      let .ok [packet] := SpaceSemantics.readSource line
        | throw (IO.userError "malformed observation packet")
      let .expression (.symbol "InductiveAppendObservation" :: .grounded (.string label) :: _) := packet
        | throw (IO.userError "wrong observation envelope")
      if seen.contains label then throw (IO.userError s!"duplicate observation: {label}")
      let some test := fixtures.find? (·.label == label)
        | throw (IO.userError s!"unexpected observation: {label}")
      unless packet == expected test do
        throw (IO.userError s!"incorrect array, bag, cursor or verdict: {label}")
      seen := label :: seen
    else if line != "" && line != "()" && line != "[()]" && line != "[]" &&
        line != "true" && line != "True" then
      throw (IO.userError s!"unexpected observation output: {line}")
  unless seen.length == fixtures.length do
    throw (IO.userError s!"missing observations: {seen.length}/{fixtures.length}")
  IO.println s!"{fixtures.length}/{fixtures.length} complete observation packets accepted"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["emit", directory] => generate directory
  | ["emit-library", library, directory] => generate directory (some (← IO.FS.readFile library))
  | ["check", path] => check (← IO.FS.readFile path)
  | _ => throw (IO.userError "usage: qualify_inductive_append_observations.lean emit DIRECTORY | emit-library LIBRARY DIRECTORY | check OUTPUT")
