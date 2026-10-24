import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedContainerTraversal
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Bridges.IndexedContainerTraversal Controls

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "traversal control has no faithful source spelling")

private def firstFuel (items : List Atom) : Nat → Nat → Nat → Nat
  | _, low, 0 => low
  | 0, low, _ => low
  | steps + 1, low, width + 1 =>
      let middle := low + (width + 1) / 2
      if (answers? middle items).isSome then
        firstFuel items steps low ((width + 1) / 2)
      else
        firstFuel items steps (middle + 1) (low + width - middle)

private def generate (directory : System.FilePath) : IO Unit := do
  unless modelChecks do throw (IO.userError "the Lean execution controls failed")
  let mut commands := ""
  let mut expected := ""
  let mut costs : Array Lean.Json := #[]
  for fixture in fixtures do
    commands := commands ++ "!(let $packet (collapse " ++ (← render (call fixture.items)) ++
      ") (println! (TraversalPacket " ++ reprStr fixture.label ++ " $packet)))\n"
    expected := expected ++ (← render (.expression [.symbol "TraversalPacket",
      .grounded (.string fixture.label), .expression [listAtom (fixture.items.map visit)]])) ++ "\n"
    let fuel := firstFuel fixture.items 16 0 4000
    unless answers? fuel fixture.items == some [listAtom (fixture.items.map visit)] do
      throw (IO.userError "measured evaluator completion differs from the exact result")
    unless fuel == 0 || (answers? (fuel - 1) fixture.items).isNone do
      throw (IO.userError "measured fuel is not minimal")
    costs := costs.push (Lean.Json.mkObj [
      ("case", .str fixture.label), ("positions", Lean.toJson fixture.items.length),
      ("source_machine_steps", Lean.toJson fuel)])
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "traversal.metta") (source.text ++ "\n" ++ commands)
  IO.FS.writeFile (directory / "source-costs.json") ((Lean.Json.arr costs).pretty ++ "\n")
  IO.FS.writeFile (directory / "expected-packets.out") expected
  IO.println s!"Emitted {fixtures.length} traversal controls from the proved source"

private def check (path : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile path
  let mut seen : List String := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "(TraversalPacket" then
      let .ok [.expression [.symbol "TraversalPacket", .grounded (.string label),
          .expression answers]] := SpaceSemantics.readSource line
        | throw (IO.userError "malformed traversal packet")
      if seen.contains label then throw (IO.userError "duplicate traversal packet")
      let some fixture := fixtures.find? (·.label == label)
        | throw (IO.userError "unknown traversal packet")
      unless answers == [listAtom (fixture.items.map visit)] do
        throw (IO.userError s!"wrong ordered traversal result: {label}")
      seen := label :: seen
    else if line != "" && line != "()" && line != "[()]" && line != "[]" &&
        line != "true" && line != "True" then
      throw (IO.userError s!"unexpected traversal output: {line}")
  unless seen.length == fixtures.length do throw (IO.userError "missing traversal packet")
  IO.println s!"Accepted {seen.length} exact ordered traversal packets"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["emit", directory] => generate directory
  | ["check", path] => check path
  | _ => throw (IO.userError "usage: qualify_inductive_traversal.lean emit DIRECTORY | check OUTPUT")
